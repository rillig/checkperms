/*-
 * Copyright (c) Roland Illig <roland.illig@gmx.de>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#if defined(__GNUC__)
#  define PRINTF_STYLE(fmt, args) __attribute__((format(__printf__, fmt, args)))
#else
#  define PRINTF_STYLE(fmt, args) /* nothing */
#endif

typedef struct {
	char *data;
	size_t length;
	size_t capacity;
} Str;

static void str_append(Str *str, char ch)
{
	if (str->length + 1 + 1 > str->capacity) {
		str->capacity = str->capacity != 0 ? 2 * str->capacity : 4096;
		str->data = realloc(str->data, str->capacity);
		if (str->data == NULL) {
			perror("str_append");
			exit(EXIT_FAILURE);
		}
	}

	assert(str->length < str->capacity);
	str->data[str->length++] = ch;
	assert(str->length < str->capacity);
	str->data[str->length] = '\0';
}

static int fix_flag = 0;
static int noaction_flag = 0;
static int quiet_flag = 0;
static int content_flag = 0;
static int error_flag = 0;

static const char *const rwx[] = {
	"---", "--x", "-w-", "-wx",
	"r--", "r-x", "rw-", "rwx"
};

static const char options[] = "cefnq";


/* The number of errors and warnings that have occurred so far. */
static int errors = 0;
static int warnings = 0;

static void
usage(void)
{

	fprintf(stderr, "usage: checkperms [-%s]\n", options);
	exit(EXIT_FAILURE);
}

/* Reads a line and returns it without the trailing '\n' character. It
 * checks for embedded NUL characters and terminates the process in this
 * case.
 */
static int
read_line(Str *line)
{
	int c;

	line->length = 0;
	for (;;) {
		c = fgetc(stdin);
		if (c == EOF)
			return 0;
		if (c == '\n')
			break;
		if (c == '\0') {
			fprintf(stderr, "<stdin>: error: NUL character in input.\n");
			exit(EXIT_FAILURE);
		}
		str_append(line, (char)c);
	}

	return 1;
}

static void PRINTF_STYLE(1, 2)
error(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	fprintf(stdout, "error: ");
	vfprintf(stdout, fmt, args);
	fprintf(stdout, "\n");
	va_end(args);
	errors++;
}

static void PRINTF_STYLE(1, 2)
warning(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	fprintf(stdout, "warning: ");
	vfprintf(stdout, fmt, args);
	fprintf(stdout, "\n");
	va_end(args);
	warnings++;
}

static void PRINTF_STYLE(1, 2)
note(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	fprintf(stdout, "note: ");
	vfprintf(stdout, fmt, args);
	fprintf(stdout, "\n");
	va_end(args);
}

static void
wont_fix_this_warning(void)
{

	if (fix_flag >= 2 || noaction_flag >= 2)
		note("won't fix this.");
}

static int
should_clear_x_bit(const char *fname, mode_t perms)
{
	unsigned char buf[4];	/* the first four bytes of the file */
	unsigned long magic;	/* the same, packed into one machine word */
	size_t len;		/* length of the filename */
	int f;			/* the file to be checked */

	/* Only check executable files. */
	if ((perms & 000111) == 000000)
		return 0;

	if ((f = open(fname, O_RDONLY)) == -1) {

		if ((perms & 006000) == 0) {
			/* Only emit a warning if the file doesn't have
			 * the set-uid or set-gid bit set, in which case
			 * the read bit may be cleared intentionally.
			 */
			warning("%s: could not be read.", fname);
		}
		return 0;
	}

	if (read(f, buf, sizeof(buf)) != 4) {
		warning("%s: too small to be a valid executable file.", fname);
		(void)close(f);
		return 1;
	}
	magic = (((unsigned long)buf[0]) << 24)
		| (((unsigned long)buf[1]) << 16)
	      | (((unsigned long)buf[2]) <<  8)
	      | (((unsigned long)buf[3]) <<  0);

	(void)close(f);

	/* ELF binaries */
	if (memcmp(buf, "\177ELF", 4) == 0)
		return 0;

	/* #!-style Scripts */
	if (buf[0] == '#' && buf[1] == '!') {
		if (buf[2] == '/')
			return 0;
		if (buf[2] == ' ' && buf[3] == '/')
			return 0;

		warning("%s: #! without a following slash.", fname);
	}

	/* Microsoft Windows binaries */
	if (memcmp(buf, "MZ", 2) == 0)
		return 0;

	/* AIX binaries */
	if (magic == 0x01df0004U)
		return 0;
	/* AIX libraries */
	if (memcmp(buf, "<big", 4) == 0)
		return 0;

	/* ppc Mac OS X binaries */
	if (magic == 0xfeedfaceU)
		return 0;
	/* ppc64 Mac OS X binaries */
	if (magic == 0xfeedfacfU)
		return 0;
	/* i386 Mac OS X binaries */
	if (magic == 0xcefaedfeU)
		return 0;
	/* x86_64 Mac OS X binaries */
	if (magic == 0xcffaedfeU)
		return 0;
	/* Universal Mac OS X binaries (yes, they look like Java class files) */
	if (magic == 0xcafebabeU)
		return 0;

	/* Microsoft Windows, MS-DOS, Mono */
	if (memcmp(buf, "MZ", 2) == 0)
		return 0;

	/* As a special case, libtool libraries may have the executable bit,
	 * although they probably don't need it.
	 */
	len = strlen(fname);
	if (len >= 3 && strcmp(fname + len - 3, ".la") == 0) {
		/* The first line looks like one of the following.
		 * # libIex.la - a libtool library file
		 * # pango-arabic-fc.la - a libtool library file
		 */
		if (memcmp(buf, "# ", 2) == 0)
			return 0;
	}

	warning("%s: executable bit is set on non-executable file.", fname);
	return 1;
}

static void
check_perms(const char *fname)
{
	struct stat st;
	unsigned int m;		/* mode without the file type */
	unsigned int u;		/* permissions of the user */
	unsigned int g;		/* permissions of the group */
	unsigned int o;		/* permissions of all others */
	mode_t unfixed;		/* the original permissions */
	mode_t err_fixed;	/* permissions after all errors have been fixed */
	mode_t warn_fixed;	/* permissions after all errors and warnings have been fixed */
	mode_t fixed;		/* either err_fixed or warn_fixed, depending
				 * on the number of -f options */

	/* Make sure that the following bit manipulations work
	 * as expected.
	 */
	assert(S_ISUID == 0004000);
	assert(S_ISGID == 0002000);
	assert(S_ISVTX == 0001000);
	assert(S_IRUSR == 0000400);
	assert(S_IWUSR == 0000200);
	assert(S_IXUSR == 0000100);
	assert(S_IRGRP == 0000040);
	assert(S_IWGRP == 0000020);
	assert(S_IXGRP == 0000010);
	assert(S_IROTH == 0000004);
	assert(S_IWOTH == 0000002);
	assert(S_IXOTH == 0000001);

	if (lstat(fname, &st) == -1) {
		error("%s: %s", fname, strerror(errno));
		return;
	}

	/* Some shortcuts to keep the following code short. */
	m = unfixed = err_fixed = warn_fixed = st.st_mode & 007777;
	u = (m & 000700) >> 6;
	g = (m & 000070) >> 3;
	o = (m & 000007) >> 0;

	if (S_ISREG(st.st_mode)) {

		if (content_flag && should_clear_x_bit(fname, m)) {
			m &= ~000111;
			warn_fixed &= ~000111;
		}

		if (g & ~u) {
			warning("%s: group permissions (%s) are higher than owner permissions (%s).",
				fname, rwx[g], rwx[u]);
			wont_fix_this_warning();
			m |= g << 6;
		}

		if (o & ~g) {
			warning("%s: other permissions (%s) are higher than group permissions (%s).",
				fname, rwx[o], rwx[g]);
			wont_fix_this_warning();
			m |= o << 3;
		}

		if ((m & 006000) && (m & 000222)) {
			warning("%s: set-uid or set-gid files should not be writable by anyone.", fname);
			warn_fixed &= ~000222;
		}

		/* It doesn't matter whether the owner can write to a file or not. */
		m &= ~000200;

		if (m & 000020) {
			if (m & 006000) {
				error("%s: group-writable set-uid/set-gid file.", fname);
				err_fixed &= ~000020;
			} else {
				warning("%s: group-writable file.", fname);
			}
			warn_fixed &= ~000020;
			m &= ~000020;
		}

		if (m & 000002) {
			if (m & 006000) {
				error("%s: world-writable set-uid/set-gid file.", fname);
			} else {
				error("%s: world-writable file.", fname);
			}
			m &= ~000002;
			err_fixed &= ~000002;
			warn_fixed &= ~000002;
		}

		/* The executable bits are not needed anymore. */
		m &= ~000111;

		/* Neither are the set-uid and set-gid bits. */
		m &= ~006000;

		if (m == 000444 || m == 000440 || m == 000400 || m == 000000) {
			/* Fine. */

		} else {
			warning("%s: unchecked mode %04o/%04o for file.",
				fname, (unsigned int)unfixed, m);
		}

	} else if (S_ISDIR(st.st_mode)) {
		if ((u & 6) && !(u & 1)) {
			error("%s: inconsistent owner permissions (%s) for directory.", fname, rwx[u]);
			err_fixed |= 000100;
			warn_fixed |= 000100;
		}

		if ((g & 6) && !(g & 1)) {
			error("%s: inconsistent group permissions (%s) for directory.", fname, rwx[g]);
			err_fixed |= 000010;
			warn_fixed |= 000010;
		}

		if ((o & 6) && !(o & 1)) {
			error("%s: inconsistent other permissions (%s) for directory.", fname, rwx[o]);
			err_fixed |= 000001;
			warn_fixed |= 000001;
		}

		if (g & ~u) {
			warning("%s: group permissions (%s) are higher than owner permissions (%s).",
				fname, rwx[g], rwx[u]);
			wont_fix_this_warning();
			m |= g << 6;
		}

		if (o & ~g) {
			warning("%s: other permissions (%s) are higher than group permissions (%s).",
				fname, rwx[o], rwx[g]);
			wont_fix_this_warning();
			m |= o << 3;
		}

		/* The executable bits are not needed anymore. */
		m &= ~000111;

		/* It does not matter whether the owner can write to a directory or not. */
		m &= ~000200;

		if (!(m & 001000) && (m & 000020)) {
			warning("%s: group-writable directory.", fname);
			warn_fixed &= ~000020;
		}
		m &= ~000020;

		if (!(m & 001000) && (m & 000002)) {
			error("%s: world-writable directory.", fname);
			err_fixed &= ~000002;
			warn_fixed &= ~000002;
		}
		m &= ~000002;

		/* The sticky attribute is not needed anymore. */
		m &= ~001000;

		/* The inherit attribute is not needed anymore. */
		m &= ~002000;

		if (m == 000444 || m == 000440 || m == 000400 || m == 000000) {
			/* Fine. */

		} else {
			warning("%s: unchecked mode %04o/%04o for directory.",
				fname, (unsigned int)unfixed, m);
		}

#if defined(S_ISLNK)
	} else if (S_ISLNK(st.st_mode)) {
		/* Fine. */
#endif

#if defined(S_ISSOCK)
	} else if (S_ISSOCK(st.st_mode)) {
		/* Fine. */
#endif

	} else if (S_ISCHR(st.st_mode) || S_ISBLK(st.st_mode)) {
		/* Fine. */

	} else if (S_ISFIFO(st.st_mode)) {
		/* Fine. */

	} else {
		warning("%s: unchecked file type.", fname);
	}

	fixed = (fix_flag >= 2 || noaction_flag >= 2) ? warn_fixed : err_fixed;

	if ((fix_flag || noaction_flag) && fixed != unfixed) {
		if (noaction_flag) {
			note("%s: would fix permissions from %04o to %04o.",
			     fname, (unsigned int)unfixed, (unsigned int)fixed);

		} else if (chmod(fname, fixed) == -1) {
			error("%s: Cannot fix permissions: %s.", fname, strerror(errno));

		} else {
			note("%s: fixed permissions from %04o to %04o.",
			     fname, (unsigned int)unfixed, (unsigned int)fixed);
		}
	}
}

int
main(int argc, char **argv)
{
	Str line;
	int c;

	while ((c = getopt(argc, argv, options)) != -1) {
		switch (c) {
		case 'c':
			content_flag = 1;
			break;
		case 'e':
			error_flag = 1;
			break;
		case 'f':
			fix_flag++;
			break;
		case 'n':
			noaction_flag++;
			break;
		case 'q':
			quiet_flag = 1;
			break;
		default:
			usage();
			/* NOTREACHED */
		}
	}
	if (optind != argc)
		usage();

	while (read_line(&line))
		check_perms(line.data);

	if (!quiet_flag && (errors != 0 || warnings != 0))
		printf("%d errors and %d warnings.\n", errors, warnings);
	if (error_flag && warnings != 0)
		return EXIT_FAILURE;
	if (errors != 0)
		return EXIT_FAILURE;
	return EXIT_SUCCESS;
}
