// based on http://c.learncodethehardway.org/book/ex20.html

#ifndef __dbg_h__
#define __dbg_h__

#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <time.h>

static char time_buf[BUFSIZ];

char* get_time() {
  time_t t = time(NULL);
  struct tm tm = *localtime(&t);

  snprintf(time_buf, BUFSIZ, "%d-%0.2d-%0.2d %0.2d:%0.2d:%0.2d", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec);
  return time_buf;
}

#define clean_errno() (errno == 0 ? "None" : strerror(errno))

#ifdef NDEBUG
#define debug(M, ...)
#else
#define debug(M, ...) fprintf(stderr, "[DEBUG] (%s:%s:%d: errno: %s) " M "\n", get_time(), __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__)
#endif

#ifdef CONTROLFLOW
#define log_control(M, ...) log_info(M, ##__VA_ARGS__)
#else
#define log_control(M, ...)
#endif


#define log_err(M, ...) fprintf(stderr, "[ERROR] (%s:%s:%d: errno: %s) " M "\n", get_time(), __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__)

#define log_warn(M, ...) fprintf(stderr, "[WARN] (%s:%s:%d: errno: %s) " M "\n", get_time(), __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__)

#define log_info(M, ...) fprintf(stderr, "[INFO] (%s:%s:%d) " M "\n", get_time(), __FILE__, __LINE__, ##__VA_ARGS__)

#define check(A, M, ...) if(!(A)) { log_err(M, ##__VA_ARGS__); errno=0; goto error; }

#define sentinel(M, ...)  { log_err(M, ##__VA_ARGS__); errno=0; goto error; }

#define check_mem(A) check((A), "Out of memory.")

#define check_debug(A, M, ...) if(!(A)) { debug(M, ##__VA_ARGS__); errno=0; goto error; }

#endif
