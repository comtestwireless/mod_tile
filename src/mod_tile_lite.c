/*
 * Copyright (c) 2007 - 2020 by mod_tile contributors (see AUTHORS file)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; If not, see http://www.gnu.org/licenses/.
 */

#include <apr.h>
#include <apr_strings.h>
#include <apr_thread_proc.h>	/* for RLIMIT stuff */
#include <apr_optional.h>
#include <apr_buckets.h>
#include <apr_lib.h>

#define APR_WANT_STRFUNC
#define APR_WANT_MEMFUNC
#include <apr_want.h>

#include <util_filter.h>
#include <ap_config.h>
#include <httpd.h>
#include <http_config.h>
#include <http_request.h>
#include <http_core.h>
#include <http_protocol.h>
#include <http_main.h>
#include <http_log.h>
#include <util_script.h>
#include <ap_mpm.h>
#include <mod_core.h>
#include <mod_cgi.h>
#include <util_md5.h>

module AP_MODULE_DECLARE_DATA tile_lite_module;

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/time.h>
#include <unistd.h>
#include <errno.h>
#include <limits.h>
#include <time.h>
#include <inttypes.h>

#include "store_file.h"
#include "sys_utils.h"

#ifdef APLOG_USE_MODULE
 APLOG_USE_MODULE(tile_lite);
# define APACHE24 1
#endif

#ifndef APACHE24
# error This module supports only Apache 2.4
#endif

#if defined(__FreeBSD__) && !defined(s6_addr32)
# define s6_addr32 __u6_addr.__u6_addr32
#endif

#define MAX_AGE (3600 * 24 * 7)
#define XMLCONFIG_MAX 41 // FIXME da rimuovere
#define PARAM_REG_PATTERN "([0-9]+)/([0-9]+)/([0-9]+).([a-zA-Z0-9_-]+)$"
#define PARAM_REG_MATCH 5
static ap_regex_t* extract_params;

int foreground = 0; // Really the kind of C hacks I hate.

enum tileState { tileMissing, tileCurrent };

typedef struct tile_server_conf {
	int cache_duration_max;
	int cache_duration_minimum;
	int cache_duration_low_zoom;
	int cache_level_low_zoom;
	int cache_duration_medium_zoom;
	int cache_level_medium_zoom;
	char tile_dir[PATH_MAX];
	int mincachetime[MAX_ZOOM + 1];

	char mapname[XMLCONFIG_MAX];
	char fileExtension[PATH_MAX];
	char mimeType[PATH_MAX];
	int minzoom;
	int maxzoom;
} tile_server_conf;

typedef struct tile_request_data {
	int x;
	int y;
	int z;
	char mapname[XMLCONFIG_MAX];
	char mimetype[XMLCONFIG_MAX];
	struct storage_backend store;
} tile_request_data;


static int error_message(request_rec *r, const char *format, ...)
__attribute__((format(printf, 2, 3)));

static int error_message(request_rec *r, const char *format, ...)
{
	va_list ap;
	char *msg;
	va_start(ap, format);

	msg = malloc(1000 * sizeof(char));

	if (msg) {
		vsnprintf(msg, 1000, format, ap);
		//ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, "%s", msg);
		ap_log_rerror(APLOG_MARK, APLOG_INFO, 0, r, "%s", msg);
		r->content_type = "text/plain";

		if (!r->header_only) {
			ap_rputs(msg, r);
		}

		free(msg);
	}

	va_end(ap);
	return OK;
}

static enum tileState tile_state(request_rec *r)
{
	ap_conf_vector_t *sconf = r->per_dir_config;
	tile_server_conf *scfg = ap_get_module_config(sconf, &tile_lite_module);

	struct stat_info stat;
	struct tile_request_data * rdata = (struct tile_request_data *)ap_get_module_config(r->request_config, &tile_lite_module);

	stat = rdata->store.tile_stat(&rdata->store, rdata->mapname, "", rdata->x, rdata->y, rdata->z);

	ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_state: determined state of %s %i %i %i on store %pp: Tile size: %li, expired: %i created: %li",
			  rdata->mapname, rdata->x, rdata->y, rdata->z, &rdata->store, stat.size, stat.expired, stat.mtime);

	r->finfo.mtime = stat.mtime * 1000000;
	r->finfo.atime = stat.atime * 1000000;
	r->finfo.ctime = stat.ctime * 1000000;

	if (stat.size < 0) {
		return tileMissing;
	}

	return tileCurrent;
}

static void add_expiry(request_rec *r)
{
	apr_time_t holdoff;
	apr_table_t *t = r->headers_out;
	apr_finfo_t *finfo = &r->finfo;
	char *timestr;

	apr_table_mergen(t, "Cache-Control",
			 apr_psprintf(r->pool, "max-age=%" APR_TIME_T_FMT,
					  (apr_time_t)MAX_AGE));
	timestr = apr_palloc(r->pool, APR_RFC822_DATE_LEN);
	apr_rfc822_date(timestr, (apr_time_from_sec(MAX_AGE) + r->request_time));
	apr_table_setn(t, "Expires", timestr);
}

static int tile_storage_hook(request_rec *r)
{
	double avg;
	int renderPrio = 0;
	enum tileState state;
	ap_conf_vector_t *sconf;
	tile_server_conf *scfg;
	struct tile_request_data * rdata;

	if (!r->handler) {
		return DECLINED;
	}

	ap_log_rerror(APLOG_MARK, APLOG_INFO, 0, r, "tile_storage_hook: handler(%s), uri(%s)",
			  r->handler, r->uri);

	if (strcmp(r->handler, "tile_serve")) {
		return DECLINED;
	}

	rdata = (struct tile_request_data *)ap_get_module_config(r->request_config, &tile_lite_module);

	state = tile_state(r);

	if (state == tileCurrent)
	{
		return OK;
	}
	else
	{
		return HTTP_NOT_FOUND;
	}
}

static int tile_handler_serve(request_rec *r)
{
	const int tile_max = MAX_SIZE;
	char err_msg[PATH_MAX];
	char id[PATH_MAX];
	char *buf;
	int len;
	int compressed;
	apr_status_t errstatus;
	struct timeval start, end;
	char *md5;
	struct tile_request_data * rdata;

	ap_conf_vector_t *sconf = r->per_dir_config;
	tile_server_conf *scfg = ap_get_module_config(sconf, &tile_lite_module);

	if (strcmp(r->handler, "tile_serve")) {
		return DECLINED;
	}

	rdata = (struct tile_request_data *)ap_get_module_config(r->request_config, &tile_lite_module);

	ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_handler_serve: xml(%s) z(%d) x(%d) y(%d)", rdata->mapname, rdata->z, rdata->x, rdata->y);

	gettimeofday(&start, NULL);

	// FIXME: It is a waste to do the malloc + read if we are fulfilling a HEAD or returning a 304.
	buf = malloc(tile_max);

	if (!buf) {
		return HTTP_INTERNAL_SERVER_ERROR;
	}

	err_msg[0] = 0;

	len = rdata->store.tile_read(&rdata->store, rdata->mapname, "", rdata->x, rdata->y, rdata->z, buf, tile_max, &compressed, err_msg);
	ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,
			  "Read tile of length %i from %s: %s", len, rdata->store.tile_storage_id(&rdata->store, rdata->mapname, "", rdata->x, rdata->y, rdata->z, id), err_msg);

	if (len > 0) {
		if (compressed) {
			const char* accept_encoding = apr_table_get(r->headers_in, "Accept-Encoding");

			if (accept_encoding && strstr(accept_encoding, "gzip")) {
				r->content_encoding = "gzip";
			} else {
				ap_log_rerror(APLOG_MARK, APLOG_WARNING, 0, r,
						  "Tile data is compressed, but user agent doesn't support Content-Encoding and we don't know how to decompress it server side");
				//TODO: decompress the output stream before sending it to client
			}
		}

		// Use MD5 hash as only cache attribute.
		// If a tile is re-rendered and produces the same output
		// then we can continue to use the previous cached copy
		md5 = ap_md5_binary(r->pool, (unsigned char *)buf, len);
		apr_table_setn(r->headers_out, "ETag", apr_psprintf(r->pool, "\"%s\"", md5));
		ap_set_content_type(r, scfg->mimeType);
		ap_set_content_length(r, len);
		add_expiry(r);

		gettimeofday(&end, NULL);

		if ((errstatus = ap_meets_conditions(r)) != OK) {
			free(buf);

			return errstatus;
		} else {
			ap_rwrite(buf, len, r);
			free(buf);

			return OK;
		}
	}

	free(buf);
	ap_log_rerror(APLOG_MARK, APLOG_WARNING, 0, r, "Failed to read tile from disk: %s", err_msg);

	return HTTP_NOT_FOUND;
}

static int tile_translate(request_rec *r)
{
	int i, n, limit, oob;
	const char *extension;
	ap_regmatch_t re_result[PARAM_REG_MATCH];

	ap_conf_vector_t *sconf = r->per_dir_config;
	tile_server_conf *scfg = ap_get_module_config(sconf, &tile_lite_module);

	if (strlen(scfg->tile_dir) == 0 || strlen(scfg->mapname) == 0)
	{
		return DECLINED;
	}

	ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: uri(%s)", r->uri);

	struct tile_request_data * rdata = (struct tile_request_data *) apr_pcalloc(r->pool, sizeof(struct tile_request_data));

	if (ap_regexec(extract_params, r->uri, PARAM_REG_MATCH, re_result, 0) == 0) {
		rdata->z = atoi(r->uri + re_result[1].rm_so);
		rdata->x = atoi(r->uri + re_result[2].rm_so);
		rdata->y = atoi(r->uri + re_result[3].rm_so);
		extension = r->uri + re_result[4].rm_so;
	}
	else {
		ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: Invalid URL for tilelayer %s without options", scfg->mapname);
		return DECLINED;
	}

	if (strcmp(extension, scfg->fileExtension) != 0) {
		ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: Invalid file extension (%s) for tilelayer %s, required %s",
					extension, scfg->mapname, scfg->fileExtension);
		return DECLINED;
	}

	oob = (rdata->z < scfg->minzoom || rdata->z > scfg->maxzoom);

	if (!oob) {
		// valid x/y for tiles are 0 ... 2^zoom-1
		limit = (1 << rdata->z);
		oob = (rdata->x < 0 || rdata->x > (limit - 1) || rdata->y < 0 || rdata->y > (limit - 1));
		ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: request for %s was %i %i %i", scfg->mapname, rdata->x, rdata->y, limit);
	}

	if (oob) {
		ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: request for %s was outside of allowed bounds", scfg->mapname);
		sleep(CLIENT_PENALTY);
		return HTTP_NOT_FOUND;
	}

	strcpy(rdata->mapname, scfg->mapname);
	strcpy(rdata->mimetype, scfg->mimeType);

	init_storage_file_s(&rdata->store, scfg->tile_dir);

	ap_set_module_config(r->request_config, &tile_lite_module, rdata);

	r->filename = NULL;
	r->handler = "tile_serve";

	ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r, "tile_translate: op(%s) xml(%s) mime(%s) z(%d) x(%d) y(%d)",
				r->handler, rdata->mapname, scfg->mimeType, rdata->z, rdata->x, rdata->y);

	return OK;
}

static void register_hooks(apr_pool_t *p)
{
	ap_hook_handler(tile_handler_serve, NULL, NULL, APR_HOOK_MIDDLE);
	ap_hook_translate_name(tile_translate, NULL, NULL, APR_HOOK_MIDDLE);
	ap_hook_map_to_storage(tile_storage_hook, NULL, NULL, APR_HOOK_FIRST);

	extract_params = ap_pregcomp(p, PARAM_REG_PATTERN, AP_REG_EXTENDED);
	ap_assert(extract_params != NULL);
}

static const char *mod_tile_tile_dir_config(cmd_parms *cmd, void *mconfig, const char *tile_dir_string)
{
	if (mconfig) {
		tile_server_conf* scfg = (tile_server_conf*)mconfig;
		strncpy(scfg->tile_dir, tile_dir_string, PATH_MAX - 1);
	}

	return NULL;
}

static const char *mod_tile_cache_duration_max_config(cmd_parms *cmd, void *mconfig, const char *cache_duration_string)
{
	if (mconfig) {
		int cache_duration;
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		if (sscanf(cache_duration_string, "%d", &cache_duration) != 1) {
			return "ModTileCacheDurationMax needs integer argument";
		}

		scfg->cache_duration_max = cache_duration;
	}

	return NULL;
}

static const char *mod_tile_cache_duration_minimum_config(cmd_parms *cmd, void *mconfig, const char *cache_duration_string)
{
	if (mconfig) {
		int cache_duration;
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		if (sscanf(cache_duration_string, "%d", &cache_duration) != 1) {
			return "ModTileCacheDurationMinimum needs integer argument";
		}

		scfg->cache_duration_minimum = cache_duration;
	}

	return NULL;
}

static const char *mod_tile_cache_duration_low_config(cmd_parms *cmd, void *mconfig, const char *zoom_level_string, const char *cache_duration_string)
{
	if (mconfig) {
		int zoom_level;
		int cache_duration;
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		if (sscanf(zoom_level_string, "%d", &zoom_level) != 1) {
			return "ModTileCacheDurationLowZoom needs integer argument";
		}

		if (sscanf(cache_duration_string, "%d", &cache_duration) != 1) {
			return "ModTileCacheDurationLowZoom needs integer argument";
		}

		scfg->cache_level_low_zoom = zoom_level;
		scfg->cache_duration_low_zoom = cache_duration;
	}

	return NULL;
}

static const char *mod_tile_cache_duration_medium_config(cmd_parms *cmd, void *mconfig, const char *zoom_level_string, const char *cache_duration_string)
{
	if (mconfig) {
		int zoom_level;
		int cache_duration;
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		if (sscanf(zoom_level_string, "%d", &zoom_level) != 1) {
			return "ModTileCacheDurationMediumZoom needs integer argument";
		}

		if (sscanf(cache_duration_string, "%d", &cache_duration) != 1) {
			return "ModTileCacheDurationMediumZoom needs integer argument";
		}

		scfg->cache_level_medium_zoom = zoom_level;
		scfg->cache_duration_medium_zoom = cache_duration;
	}

	return NULL;
}

static const char *mod_tile_zoom_level_config(cmd_parms *cmd, void *mconfig, const char *zoom_min, const char *zoom_max)
{
	if (mconfig) {
		int minzoom, maxzoom;

		if (sscanf(zoom_min, "%d", &minzoom) != 1) {
			return "ModTileZoomRange needs integer argument";
		}

		if (minzoom < 0) {
			return "ModTileZoomRange min zoom must be positive";
		}

		if (sscanf(zoom_max, "%d", &maxzoom) != 1) {
			return "ModTileZoomRange needs integer argument";
		}

		if (maxzoom < minzoom) {
			return "ModTileZoomRange max zoom must be greater than min zoom";   
		}

		tile_server_conf *scfg = (tile_server_conf*)mconfig;

		scfg->minzoom = minzoom;
		scfg->maxzoom = maxzoom;
	}

	return NULL;
}

static const char *mod_tile_file_type_config(cmd_parms *cmd, void *mconfig, const char *extension, const char* mime)
{
	if (mconfig) {
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		strncpy(scfg->fileExtension, extension, PATH_MAX - 1);
		strncpy(scfg->mimeType, mime, PATH_MAX - 1);
	}

	return NULL;
}

static const char *mod_tile_map_name_config(cmd_parms *cmd, void *mconfig, const char *name)
{
	ap_log_perror(APLOG_MARK, APLOG_NOTICE, 0, cmd->pool, "%s: %pp %s", __func__, mconfig, name);
	
	if (mconfig) {
		tile_server_conf* scfg = (tile_server_conf*)mconfig;

		strncpy(scfg->mapname, name, XMLCONFIG_MAX - 1);
	}
	
	return NULL;
}

static void *create_tile_config(apr_pool_t *p, char *dir) // Potrei usare "dir" per evitare la regex
{
	tile_server_conf * scfg = (tile_server_conf *) apr_pcalloc(p, sizeof(tile_server_conf));

	scfg->cache_duration_max = 7 * 24 * 60 * 60;
	scfg->cache_duration_minimum = 3 * 60 * 60;
	scfg->cache_duration_low_zoom = 6 * 24 * 60 * 60;
	scfg->cache_duration_medium_zoom = 1 * 24 * 60 * 60;

	strcpy(scfg->fileExtension, "png");
	strcpy(scfg->mimeType, "image/png");
	scfg->maxzoom = MAX_ZOOM;

	return scfg;
}

static void *merge_tile_config(apr_pool_t *p, void *basev, void *overridesv)
{
	int i;
	tile_server_conf * scfg = (tile_server_conf *) apr_pcalloc(p, sizeof(tile_server_conf));
	tile_server_conf * scfg_base = (tile_server_conf *) basev;
	tile_server_conf * scfg_over = (tile_server_conf *) overridesv;

	scfg->cache_duration_max = scfg_over->cache_duration_max == 0 
		? scfg_base->cache_duration_max 
		: scfg_over->cache_duration_max;
	scfg->cache_duration_minimum = scfg_over->cache_duration_minimum == 0 
		? scfg_base->cache_duration_minimum 
		: scfg_over->cache_duration_minimum;
	scfg->cache_duration_low_zoom = scfg_over->cache_duration_low_zoom == 0 
		? scfg_base->cache_duration_low_zoom 
		: scfg_over->cache_duration_low_zoom;
	scfg->cache_duration_medium_zoom = scfg_over->cache_duration_medium_zoom == 0 
		? scfg_base->cache_duration_medium_zoom 
		: scfg_over->cache_duration_medium_zoom;
	scfg->cache_level_low_zoom = scfg_over->cache_level_low_zoom == 0 
		? scfg_base->cache_level_low_zoom 
		: scfg_over->cache_level_low_zoom;
	scfg->cache_level_medium_zoom = scfg_over->cache_level_medium_zoom == 0 
		? scfg_base->cache_level_medium_zoom 
		: scfg_over->cache_level_medium_zoom;

	strcpy(scfg->tile_dir, strlen(scfg_over->tile_dir) ? scfg_over->tile_dir : scfg_base->tile_dir);

	//Construct a table of minimum cache times per zoom level
	for (i = 0; i <= MAX_ZOOM; i++) {
		if (i <= scfg->cache_level_low_zoom) {
			scfg->mincachetime[i] = scfg->cache_duration_low_zoom;
		} else if (i <= scfg->cache_level_medium_zoom) {
			scfg->mincachetime[i] = scfg->cache_duration_medium_zoom;
		} else {
			scfg->mincachetime[i] = scfg->cache_duration_minimum;
		}
	}

	strcpy(scfg->mapname, strlen(scfg_over->mapname) ? scfg_over->mapname : scfg_base->mapname);
	strcpy(scfg->fileExtension, strlen(scfg_over->fileExtension) ? scfg_over->fileExtension : scfg_base->fileExtension);
	strcpy(scfg->mimeType, strlen(scfg_over->mimeType) ? scfg_over->mimeType : scfg_base->mimeType);
	
	scfg->minzoom = scfg_over->minzoom ? scfg_over->minzoom : scfg_base->minzoom;
	scfg->maxzoom = scfg_over->maxzoom ? scfg_over->maxzoom : scfg_base->maxzoom;

	return scfg;
}

static const command_rec tile_cmds[] = {
	AP_INIT_TAKE1(
		"ModTileLiteTileDir",				/* directive name */
		mod_tile_tile_dir_config,		/* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set name of tile cache directory"  /* directive description */
	),
	AP_INIT_TAKE1(
		"ModTileLiteEnableMap",				/* directive name */
		mod_tile_map_name_config,		/* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set name of the map"  /* directive description */
	),
	AP_INIT_TAKE1(
		"ModTileLiteCacheDurationMax",				/* directive name */
		mod_tile_cache_duration_max_config,		/* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set the maximum cache expiry in seconds"  /* directive description */
	),
	AP_INIT_TAKE1(
		"ModTileLiteCacheDurationMinimum",		  /* directive name */
		mod_tile_cache_duration_minimum_config, /* config action routine */
		NULL,								   /* argument to include in call */
		ACCESS_CONF | RSRC_CONF,							 /* where available */
		"Set the minimum cache expiry"		  /* directive description */
	),
	AP_INIT_TAKE2(
		"ModTileLiteCacheDurationLowZoom",	   /* directive name */
		mod_tile_cache_duration_low_config,				 /* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set the minimum cache duration and zoom level for low zoom tiles"  /* directive description */
	),
	AP_INIT_TAKE2(
		"ModTileLiteCacheDurationMediumZoom", /* directive name */
		mod_tile_cache_duration_medium_config,				 /* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set the minimum cache duration and zoom level for medium zoom tiles"  /* directive description */
	),
	AP_INIT_TAKE2(
		"ModTileLiteZoomRange",				/* directive name */
		mod_tile_zoom_level_config,		/* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Sets the minimum and maximum zoom levels (default '0 20')"  /* directive description */
	),
	AP_INIT_TAKE2(
		"ModTileLiteFileType",				/* directive name */
		mod_tile_file_type_config,		/* config action routine */
		NULL,							/* argument to include in call */
		ACCESS_CONF | RSRC_CONF,					  /* where available */
		"Set extension and mime type for the tiles (default 'png image/png')"  /* directive description */
	),
	{ NULL }
};

module AP_MODULE_DECLARE_DATA tile_lite_module = {
	STANDARD20_MODULE_STUFF,
	create_tile_config,								/* dir config creater */
	merge_tile_config,								/* dir merger --- default is to override */
	NULL,				  /* server config */
	NULL,				   /* merge server config */
	tile_cmds,						   /* command apr_table_t */
	register_hooks					   /* register hooks */
};
