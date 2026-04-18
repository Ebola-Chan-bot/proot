#include <stdio.h>     /* rename(2), */
#include <stdlib.h>    /* atoi */
#include <stdbool.h>   /* bool, true, false */
#include <unistd.h>    /* symlink(2), symlinkat(2), readlink(2), lstat(2), unlink(2), unlinkat(2)*/
#include <string.h>    /* str*, strrchr, strcat, strcpy, strncpy, strncmp */
#include <sys/types.h> /* lstat(2), */
#include <sys/stat.h>  /* lstat(2), */
#include <errno.h>     /* E*, */
#include <limits.h>    /* PATH_MAX, */
#include <ctype.h>     /* isdigit, */
#include <fcntl.h>     /* 仅调试用：AT_FDCWD, AT_EMPTY_PATH, AT_SYMLINK_FOLLOW, open */

#include "cli/note.h"
#include "extension/extension.h"
#include "tracee/tracee.h"
#include "tracee/mem.h"
#include "tracee/statx.h"
#include "syscall/syscall.h"
#include "syscall/sysnum.h"
#include "path/path.h"
#include "path/f2fs-bug.h"
#include "arch.h"
#include "attribute.h"

#ifdef USERLAND
#define PREFIX ".proot.l2s."
#endif 
#ifndef USERLAND
#define PREFIX ".l2s."
#endif 
#define DELETED_SUFFIX " (deleted)"

static int decrement_link_count(Tracee *tracee, Reg sysarg);

/**
 * Copy the contents of the @symlink into @value (nul terminated).
 * This function returns -errno if an error occured, otherwise 0.
 */
static int my_readlink(const char symlink[PATH_MAX], char value[PATH_MAX])
{
	ssize_t size;

	size = readlink(symlink, value, PATH_MAX);
	if (size < 0)
		return size;
	if (size >= PATH_MAX)
		return -ENAMETOOLONG;
	value[size] = '\0';

	return 0;
}

/**
 * Move the path pointed to by @tracee's @sysarg to a new location,
 * symlink the original path to this new one, make @tracee's @sysarg
 * point to the new location.  This function returns -errno if an
 * error occured, otherwise 0.
 */
static int move_and_symlink_path(Tracee *tracee, Reg sysarg, Reg link_target_sysarg)
{
	char original[PATH_MAX];
	char intermediate[PATH_MAX];
	char new_intermediate[PATH_MAX];
	char final[PATH_MAX];
	char new_final[PATH_MAX];
	char * name;
	const char * l2s_directory;
	struct stat statl;
	ssize_t size;
	int status;
	int link_count;
	int first_link = 1;
	int intermediate_suffix = 1;

	/* Note: this path was already canonicalized.  */
	size = read_string(tracee, original, peek_reg(tracee, CURRENT, sysarg), PATH_MAX);
	if (size < 0)
		return size;
	if (size >= PATH_MAX)
		return -ENAMETOOLONG;

	/* Sanity check: directories can't be linked.  */
	status = lstat(original, &statl);
	if (status < 0)
		return errno > 0 ? -errno : -ENOENT;
	if (S_ISDIR(statl.st_mode))
		return -EPERM;

	/* Check if it is a symbolic link.  */
	if (S_ISLNK(statl.st_mode)) {
		/* get name */
		size = my_readlink(original, intermediate);
		if (size < 0)
			return size;

		name = strrchr(intermediate, '/');
		if (name == NULL)
			name = intermediate;
		else
			name++;

		if (strncmp(name, PREFIX, strlen(PREFIX)) == 0)
			first_link = 0;
	} else {
		/* compute new name */
		name = strrchr(original,'/');
		if (name == NULL)
			name = original;
		else
			name++;

		l2s_directory = getenv("PROOT_L2S_DIR");
		if (l2s_directory != NULL && l2s_directory[0]) {
			if (strlen(PREFIX) + strlen(l2s_directory) + (strlen(original) - strlen(name)) + 6 >= PATH_MAX)
				return -ENAMETOOLONG;

			strcpy(intermediate, l2s_directory);
			if (l2s_directory[strlen(l2s_directory) - 1] != '/') {
				strcat(intermediate, "/");
			}
		} else {
			if (strlen(PREFIX) + strlen(original) + 5 >= PATH_MAX)
				return -ENAMETOOLONG;

			strncpy(intermediate, original, strlen(original) - strlen(name));
			intermediate[strlen(original) - strlen(name)] = '\0';
		}
		strcat(intermediate, PREFIX);
		strcat(intermediate, name);
	}

	if (first_link) {
		/*Move the original content to the new path. */
		do {
			sprintf(new_intermediate, "%s%04d", intermediate, intermediate_suffix);
			intermediate_suffix++;
		} while ((access(new_intermediate,F_OK) != -1) && (intermediate_suffix < 1000));
		strcpy(intermediate, new_intermediate);

		strcpy(final, intermediate);
		strcat(final, ".0002");
		status = rename(original, final);
		if (status < 0)
			return status;
		status = notify_extensions(tracee, LINK2SYMLINK_RENAME, (intptr_t) original, (intptr_t) final);
		if (status < 0)
			return status;

		/* Symlink the intermediate to the final file.  */
		status = symlink(final, intermediate);
		if (status < 0)
			return status;

		/* Symlink the original path to the intermediate one.  */
		status = symlink(intermediate, original);
		if (status < 0)
			return status;
	} else {
		/*Move the original content to new location, by incrementing count at end of path. */
		size = my_readlink(intermediate, final);
		if (size < 0)
			return size;

		link_count = atoi(final + strlen(final) - 4);
		link_count++;

		strncpy(new_final, final, strlen(final) - 4);
		sprintf(new_final + strlen(final) - 4, "%04d", link_count);

		status = rename(final, new_final);
		if (status < 0)
			return status;
		status = notify_extensions(tracee, LINK2SYMLINK_RENAME, (intptr_t) final, (intptr_t) new_final);
		if (status < 0)
			return status;
		strcpy(final, new_final);
		/* Symlink the intermediate to the final file.  */
		status = unlink(intermediate);
		if (status < 0)
			return status;
		status = symlink(final, intermediate);
		if (status < 0)
			return status;
	}

	/* Perform symlink() operation within PRoot.  */
	status = read_path(tracee, final, peek_reg(tracee, CURRENT, link_target_sysarg));
	if (status >= 0) {
		status = symlink(intermediate, final);
		if (status < 0) status = -errno;
	}
	if (status < 0) {
		status = -errno;
		decrement_link_count(tracee, sysarg);
		return status;
	}
	poke_reg(tracee, SYSARG_RESULT, 0);
	set_sysnum(tracee, PR_void);

	return 0;
}


/* If path points a file that is a symlink to a file that begins
 *   with PREFIX, let the file be deleted, but also delete the
 *   symlink that was created and decremnt the count that is tacked
 *   to end of original file.
 */
static int decrement_link_count(Tracee *tracee, Reg sysarg)
{
	char original[PATH_MAX];
	char intermediate[PATH_MAX];
	char final[PATH_MAX];
	char new_final[PATH_MAX];
	char * name;
	struct stat statl;
	ssize_t size;
	int status;
	int link_count;

	/* Note: this path was already canonicalized.  */
	size = read_string(tracee, original, peek_reg(tracee, CURRENT, sysarg), PATH_MAX);
	if (size < 0)
		return size;
	if (size >= PATH_MAX)
		return -ENAMETOOLONG;

	/* Check if it is a converted link already.  */
	status = lstat(original, &statl);
	if (status < 0)
		return 0;

	if (!S_ISLNK(statl.st_mode))
		return 0;

	size = my_readlink(original, intermediate);
	if (size < 0)
		return size;

	name = strrchr(intermediate, '/');
	if (name == NULL)
		name = intermediate;
	else
		name++;

	/* Check if an l2s file is pointed to */
	if (strncmp(name, PREFIX, strlen(PREFIX)) != 0)
		return 0;

	/* Read intermediate link - if this fails then
	 * this link2symlink is broken and we silently
	 * skip as we were removing it anyway.  */
	size = my_readlink(intermediate, final);
	if (size < 0) {
		VERBOSE(tracee, 1, "Skiping deref of broken link2symlink \"%s\" -> \"%s\"", original, intermediate);
		return 0;
	}

	link_count = atoi(final + strlen(final) - 4);
	link_count--;

	/* Check if it is or is not the last link to delete */
	if (link_count > 0) {
		strncpy(new_final, final, strlen(final) - 4);
		sprintf(new_final + strlen(final) - 4, "%04d", link_count);

		status = rename(final, new_final);
		if (status < 0)
			return status;
		status = notify_extensions(tracee, LINK2SYMLINK_RENAME, (intptr_t) final, (intptr_t) new_final);
		if (status < 0)
			return status;

		strcpy(final, new_final);

		/* Symlink the intermediate to the final file.  */
		status = unlink(intermediate);
		if (status < 0)
			return status;

		status = symlink(final, intermediate);
		if (status < 0)
			return status;
	} else {
		/* If it is the last, delete the intermediate and final */
		status = unlink(intermediate);
		if (status < 0)
			return status;
		status = unlink(final);
		if (status < 0)
			return status;
		status = notify_extensions(tracee, LINK2SYMLINK_UNLINK, (intptr_t) final, 0);
		if (status < 0)
			return status;
		}

	return 0;
}

/**
 * sizeof(struct stat) cut to contain only fields that are at same addresses
 * regardless of whenever tracee is 32-bit or 64-bit.
 *
 * This allows modification of following fields:
 * - st_dev
 * - st_mode
 * - st_nlink
 * - st_uid
 * - st_gid
 * - st_rdev
 * - st_size
 * - st_blksize
 * - st_blocks
 */
#define SIZEOF_RELEVANT_STRUCT_STAT 72

/**
 * Make it so fake hard links look like real hard link with respect to number of links and inode
 * This function returns -errno if an error occured, otherwise 0.
 */
static int handle_sysexit_end(Tracee *tracee)
{
	word_t sysnum;

	sysnum = get_sysnum(tracee, ORIGINAL);

	#ifdef USERLAND
		if ((get_sysnum(tracee, CURRENT) == PR_fstat) || (get_sysnum(tracee, CURRENT) == PR_fstat64))
			return 0;

		if (((sysnum == PR_fstat) || (sysnum == PR_fstat64)) && (get_sysnum(tracee, CURRENT) == PR_readlinkat))
			return 0;
	#endif

	switch (sysnum) {

	case PR_fstatat64:                 //int fstatat(int dirfd, const char *pathname, struct stat *buf, int flags);
	case PR_newfstatat:                //int fstatat(int dirfd, const char *pathname, struct stat *buf, int flags);
	case PR_stat64:                    //int stat(const char *path, struct stat *buf);
	case PR_lstat64:                   //int lstat(const char *path, struct stat *buf);
	case PR_fstat64:                   //int fstat(int fd, struct stat *buf);
	case PR_stat:                      //int stat(const char *path, struct stat *buf);
	case PR_lstat:                     //int lstat(const char *path, struct stat *buf);
	case PR_fstat: {                   //int fstat(int fd, struct stat *buf);
		word_t result;
		Reg sysarg_stat;
		Reg sysarg_path;
		int status;
		struct stat statl = {};
		ssize_t size;
		char original[PATH_MAX];
		char intermediate[PATH_MAX];
		char final[PATH_MAX];
		char * name;
		struct stat finalStat;

		/* Override only if it succeed.  */
		result = peek_reg(tracee, CURRENT, SYSARG_RESULT);
		if (result != 0)
			return 0;

		if (sysnum == PR_fstat64 || sysnum == PR_fstat) {
			#ifndef USERLAND
				status = readlink_proc_pid_fd(tracee->pid, peek_reg(tracee, MODIFIED, SYSARG_1), original);
				if (status < 0) {
					VERBOSE(tracee, 3, "link2symlink: readlink_proc_pid_fd failed, status=%d", status);
					return 0; // Don't alter syscall result
				}
				if (strlen(original) > strlen(DELETED_SUFFIX) &&
						strcmp(original + strlen(original) - strlen(DELETED_SUFFIX), DELETED_SUFFIX) == 0)
					original[strlen(original) - strlen(DELETED_SUFFIX)] = '\0';
			#endif
			#ifdef USERLAND
				size = read_string(tracee, original, peek_reg(tracee, CURRENT, SYSARG_2), PATH_MAX);
				if (size < 0)
					return size;
				if (size >= PATH_MAX)
					return -ENAMETOOLONG;
			#endif
		} else {
			if (sysnum == PR_fstatat64 || sysnum == PR_newfstatat)
				sysarg_path = SYSARG_2;
			else
				sysarg_path = SYSARG_1;
			size = read_string(tracee, original, peek_reg(tracee, MODIFIED, sysarg_path), PATH_MAX);
			if (size < 0)
				return size;
			if (size >= PATH_MAX)
				return -ENAMETOOLONG;
		}

		name = strrchr(original, '/');
		if (name == NULL)
			name = original;
		else
			name++;

		/* Check if it is a link */
		status = lstat(original, &statl);

		if (strncmp(name, PREFIX, strlen(PREFIX)) == 0) {
			if (S_ISLNK(statl.st_mode)) {
				strcpy(intermediate,original);
				goto intermediate_proc;
			} else {
				strcpy(final,original);
				goto final_proc;
			}
		}

		if (!S_ISLNK(statl.st_mode))
			return 0;

		size = my_readlink(original, intermediate);
		if (size < 0)
			return size;

		name = strrchr(intermediate, '/');
		if (name == NULL)
			name = intermediate;
		else
			name++;

		if (strncmp(name, PREFIX, strlen(PREFIX)) != 0)
			return 0;

		intermediate_proc: size = my_readlink(intermediate, final);
		if (size < 0)
			return size;

		final_proc: status = lstat(final,&finalStat);
		if (status < 0)
			return status;

		finalStat.st_nlink = atoi(final + strlen(final) - 4);

		/* Get the address of the 'stat' structure.  */
		if (sysnum == PR_fstatat64 || sysnum == PR_newfstatat)
			sysarg_stat = SYSARG_3;
		else
			sysarg_stat = SYSARG_2;

		#ifdef USERLAND
			/* Overwrite the stat struct with the correct number of "links". */
			read_data(tracee, &statl, peek_reg(tracee, ORIGINAL, sysarg_stat), sizeof(statl));
			finalStat.st_mode = statl.st_mode;
			finalStat.st_uid = statl.st_uid;
			finalStat.st_gid = statl.st_gid;
		#endif
		status = write_data(tracee, peek_reg(tracee, ORIGINAL,  sysarg_stat), &finalStat,
			is_32on64_mode(tracee) ? SIZEOF_RELEVANT_STRUCT_STAT : sizeof(finalStat));
		if (status < 0)
			return status;

		return 0;
	}

	default:
		return 0;
	}
}

static void link2symlink_handle_statx(struct statx_syscall_state *state)
{
	if (!(state->statx_buf.stx_mask & STATX_NLINK))
		return;

	const char *path_ending = strrchr(state->host_path, '/');
	if (NULL == path_ending)
		return;

	size_t ending_len = strlen(path_ending);
	if (ending_len < strlen(PREFIX) + 6) /* 6 = strlen("/") + strlen(".0002") */
		return;

	if (0 != strncmp(path_ending + 1, PREFIX, strlen(PREFIX)))
		return;

	if (path_ending[ending_len - 5] != '.')
		return;

	for (size_t i = 1; i <= 4; i++) {
		if (!isdigit(path_ending[ending_len - i]))
			return;
	}

	state->statx_buf.stx_nlink = atoi(&path_ending[ending_len - 4]);
}

/**
 * When @translated_path is a faked hard-link, replace it with the
 * point it (internally) points to.
 */
static void translated_path(Tracee *tracee, char translated_path[PATH_MAX])
{
	char path2[PATH_MAX];
	char path[PATH_MAX];
	char *component;
	int status;

	/* Don't translate l2s symlinks if call is (un)link */
	Sysnum sysnum = get_sysnum(tracee, ORIGINAL);
	if (   sysnum == PR_unlink
	    || sysnum == PR_unlinkat
	    || sysnum == PR_link
	    || sysnum == PR_linkat
	    || sysnum == PR_rename
	    || sysnum == PR_renameat
	    || sysnum == PR_renameat2) {
		return;
	}

	if (should_skip_file_access_due_to_f2fs_bug(tracee, translated_path))
		return;

	status = my_readlink(translated_path, path);
	if (status < 0)
		return;

	component = strrchr(path, '/');
	if (component == NULL)
		return;
	component++;

	if (strncmp(component, PREFIX, strlen(PREFIX)) != 0)
		return;

	status = my_readlink(path, path2);
	if (status < 0)
		return;

#if 0 /* Sanity check. */
	component = strrchr(path, '/');
	if (component == NULL)
		return;
	component++;

	if (strncmp(component, PREFIX, strlen(PREFIX)) != 0)
		return;
#endif

	strcpy(translated_path, path2);
	return;
}

/**
 * Handler for linkat(..., "/proc/X/fd/Y", ..., AT_SYMLINK_FOLLOW)
 *
 * Returns:
 *    1 if operation was handled successfully
 *      (Syscall should be marked as successful without further actions)
 *    0 if this wasn't linkat from /proc//fd
 *      (Caller should proceed with usual link2symlink)
 *   <0 if operation failed
 *      (Syscall should be marked as failed without further actions)
 */
static int handle_linkat_from_proc_fd(Tracee *tracee) {
	/* 仅调试用：一次性 dump 环境指纹 + sysctl + 自包含 O_TMPFILE linkat 对照实验。
	 * 背景：tracee linkat 得 EPERM(-1)，proot-direct linkat 得 EACCES(-13)，
	 *       两个 errno 不同 → 不同内核拒绝路径；但 proot-direct 可能只是
	 *       跨进程 procfs magic-link 访问被拦，并不能代表"O_TMPFILE linkat
	 *       本身是否被允许"。本轮新增 proot 自己 open O_TMPFILE 并 linkat 的
	 *       完全自包含测试（无 tracee、无跨 PID procfs、无 ptrace），以彻底
	 *       隔离 O_TMPFILE linkat 能力这一变量；同时 dump 内核版本、SELinux
	 *       安全域、CapEff，为下一步判断是 Android kernel patch 还是 sepolicy
	 *       问题提供决定性证据。 */
	static int __ph_dumped = 0; /* 仅调试用 */
	if (!__ph_dumped) { /* 仅调试用 */
		__ph_dumped = 1; /* 仅调试用 */
		/* 仅调试用 (1)：sysctl fs.protected_hardlinks */
		int __f = open("/proc/sys/fs/protected_hardlinks", O_RDONLY); /* 仅调试用 */
		if (__f >= 0) { /* 仅调试用 */
			char __b[16] = {0}; /* 仅调试用 */
			ssize_t __n = read(__f, __b, sizeof(__b) - 1); /* 仅调试用 */
			close(__f); /* 仅调试用 */
			fprintf(stderr, "proot-diag: sysctl fs.protected_hardlinks='%.*s' (read_rc=%zd)\n", (int) __n, __b, __n); /* 仅调试用 */
		} else { /* 仅调试用 */
			fprintf(stderr, "proot-diag: sysctl fs.protected_hardlinks open failed errno=%d\n", errno); /* 仅调试用 */
		} /* 仅调试用 */

		/* 仅调试用 (2)：SELinux 安全域（看是不是 untrusted_app:s0:c...） */
		int __cf = open("/proc/self/attr/current", O_RDONLY); /* 仅调试用 */
		if (__cf >= 0) { /* 仅调试用 */
			char __cb[256] = {0}; /* 仅调试用 */
			ssize_t __cn = read(__cf, __cb, sizeof(__cb) - 1); /* 仅调试用 */
			close(__cf); /* 仅调试用 */
			for (ssize_t __i = 0; __i < __cn; ++__i) if (__cb[__i] == '\n' || __cb[__i] == '\0') { __cb[__i] = 0; break; } /* 仅调试用 */
			fprintf(stderr, "proot-diag: selinux_context='%s' (read_rc=%zd)\n", __cb, __cn); /* 仅调试用 */
		} else { /* 仅调试用 */
			fprintf(stderr, "proot-diag: selinux context open failed errno=%d\n", errno); /* 仅调试用 */
		} /* 仅调试用 */

		/* 仅调试用 (3)：capabilities + Uid/Gid 行（看 CapEff 是否全 0） */
		int __sf = open("/proc/self/status", O_RDONLY); /* 仅调试用 */
		if (__sf >= 0) { /* 仅调试用 */
			char __sb[4096] = {0}; /* 仅调试用 */
			ssize_t __sn = read(__sf, __sb, sizeof(__sb) - 1); /* 仅调试用 */
			close(__sf); /* 仅调试用 */
			char *__p = __sb, *__end = __sb + __sn; /* 仅调试用 */
			while (__p < __end) { /* 仅调试用 */
				char *__nl = memchr(__p, '\n', (size_t)(__end - __p)); /* 仅调试用 */
				size_t __llen = __nl ? (size_t)(__nl - __p) : (size_t)(__end - __p); /* 仅调试用 */
				if (__llen > 3 && (memcmp(__p, "Uid:", 4) == 0 || memcmp(__p, "Gid:", 4) == 0 || /* 仅调试用 */
					memcmp(__p, "Cap", 3) == 0 || memcmp(__p, "Sec", 3) == 0 || /* 仅调试用 */
					memcmp(__p, "Gro", 3) == 0 || memcmp(__p, "NoN", 3) == 0)) { /* 仅调试用 */
					fprintf(stderr, "proot-diag: status %.*s\n", (int) __llen, __p); /* 仅调试用 */
				} /* 仅调试用 */
				if (!__nl) break; /* 仅调试用 */
				__p = __nl + 1; /* 仅调试用 */
			} /* 仅调试用 */
		} /* 仅调试用 */

		/* 仅调试用 (4)：内核版本（HarmonyOS 指纹） */
		int __vf = open("/proc/version", O_RDONLY); /* 仅调试用 */
		if (__vf >= 0) { /* 仅调试用 */
			char __vb[512] = {0}; /* 仅调试用 */
			ssize_t __vn = read(__vf, __vb, sizeof(__vb) - 1); /* 仅调试用 */
			close(__vf); /* 仅调试用 */
			for (ssize_t __i = 0; __i < __vn; ++__i) if (__vb[__i] == '\n') { __vb[__i] = 0; break; } /* 仅调试用 */
			fprintf(stderr, "proot-diag: kernel_version='%s'\n", __vb); /* 仅调试用 */
		} /* 仅调试用 */

		/* 仅调试用 (5)：完全自包含 O_TMPFILE + linkat 对照实验。
		 * proot 自己在 alpine/tmp（已 bind，tmpfs）和 alpine/etc/apk 各 open 一个
		 * O_TMPFILE，然后 linkat 到同目录下的普通路径。如果**也**失败，说明与
		 * tracee/ptrace/apk 无关，就是本内核+本 fs+本 uid 下 O_TMPFILE linkat
		 * 不被允许；如果**成功**，说明失败只在 tracee 的 ptrace/seccomp 路径上，
		 * 需进一步检查 ptrace-context 的差异。 */
		const char *__dirs[] = { /* 仅调试用 */
			"/data/data/com.foxdebug.acode/files/alpine/etc/apk", /* 仅调试用 */
			"/data/data/com.foxdebug.acode/files/alpine/lib/apk/db", /* 仅调试用 */
			"/data/data/com.foxdebug.acode/files/alpine/tmp", /* 仅调试用 */
			"/data/data/com.foxdebug.acode/files/tmp" /* 仅调试用 */
		}; /* 仅调试用 */
		for (size_t __di = 0; __di < sizeof(__dirs)/sizeof(__dirs[0]); ++__di) { /* 仅调试用 */
			const char *__dir = __dirs[__di]; /* 仅调试用 */
			/* 5a: proot-self O_TMPFILE */
			int __tfd = open(__dir, O_TMPFILE | O_RDWR, 0644); /* 仅调试用 */
			int __terr = errno; /* 仅调试用 */
			fprintf(stderr, "proot-diag: self O_TMPFILE dir='%s' fd=%d errno=%d(%s)\n", /* 仅调试用 */
				__dir, __tfd, __tfd < 0 ? __terr : 0, __tfd < 0 ? strerror(__terr) : ""); /* 仅调试用 */
			if (__tfd < 0) continue; /* 仅调试用 */
			if (write(__tfd, "x", 1) != 1) { /* 仅调试用 */
				fprintf(stderr, "proot-diag: self O_TMPFILE write failed errno=%d\n", errno); /* 仅调试用 */
			} /* 仅调试用 */
			/* 5b: linkat via /proc/self/fd magic link (tracee 走的路径) */
			char __src[64], __dst[256]; /* 仅调试用 */
			snprintf(__src, sizeof(__src), "/proc/self/fd/%d", __tfd); /* 仅调试用 */
			snprintf(__dst, sizeof(__dst), "%s/.proot_diag_self_tmpfile_%d", __dir, (int) getpid()); /* 仅调试用 */
			unlink(__dst); /* 仅调试用 */
			int __lr = linkat(AT_FDCWD, __src, AT_FDCWD, __dst, AT_SYMLINK_FOLLOW); /* 仅调试用 */
			int __le = errno; /* 仅调试用 */
			fprintf(stderr, "proot-diag: self linkat(magic,AT_SYMLINK_FOLLOW) dir='%s' rc=%d errno=%d(%s) dst='%s'\n", /* 仅调试用 */
				__dir, __lr, __le, strerror(__le), __dst); /* 仅调试用 */
			if (__lr == 0) unlink(__dst); /* 仅调试用 */
			/* 5c: linkat via AT_EMPTY_PATH 直接用 fd（不经 /proc） */
			int __lr2 = linkat(__tfd, "", AT_FDCWD, __dst, AT_EMPTY_PATH); /* 仅调试用 */
			int __le2 = errno; /* 仅调试用 */
			fprintf(stderr, "proot-diag: self linkat(fd,AT_EMPTY_PATH) dir='%s' rc=%d errno=%d(%s)\n", /* 仅调试用 */
				__dir, __lr2, __le2, strerror(__le2)); /* 仅调试用 */
			if (__lr2 == 0) unlink(__dst); /* 仅调试用 */
			close(__tfd); /* 仅调试用 */

			/* 5d: 对照：同目录 open 一个**普通文件**（非 O_TMPFILE），关闭后
			 * 用 /proc/self/fd 的 magic link 再试一次（**hold 着 fd 让 magic
			 * link 有效**），对比 O_TMPFILE 是否被特殊对待 */
			char __regsrc[256]; /* 仅调试用 */
			snprintf(__regsrc, sizeof(__regsrc), "%s/.proot_diag_reg_%d", __dir, (int) getpid()); /* 仅调试用 */
			int __rfd = open(__regsrc, O_RDWR | O_CREAT, 0644); /* 仅调试用 */
			if (__rfd >= 0) { /* 仅调试用 */
				char __rsrc[64], __rdst[256]; /* 仅调试用 */
				snprintf(__rsrc, sizeof(__rsrc), "/proc/self/fd/%d", __rfd); /* 仅调试用 */
				snprintf(__rdst, sizeof(__rdst), "%s/.proot_diag_reg_link_%d", __dir, (int) getpid()); /* 仅调试用 */
				unlink(__rdst); /* 仅调试用 */
				int __rr = linkat(AT_FDCWD, __rsrc, AT_FDCWD, __rdst, AT_SYMLINK_FOLLOW); /* 仅调试用 */
				int __rer = errno; /* 仅调试用 */
				fprintf(stderr, "proot-diag: self linkat(REGULAR magic) dir='%s' rc=%d errno=%d(%s)\n", /* 仅调试用 */
					__dir, __rr, __rer, strerror(__rer)); /* 仅调试用 */
				if (__rr == 0) unlink(__rdst); /* 仅调试用 */
				close(__rfd); /* 仅调试用 */
				unlink(__regsrc); /* 仅调试用 */
			} /* 仅调试用 */

			/* 仅调试用 5e：经典 link(real_path, new_path) —— 不经 /proc fd，
			 * 验证"所有硬链接被禁"还是只禁 magic-link 源。 */
			char __cla[256], __clb[256]; /* 仅调试用 */
			snprintf(__cla, sizeof(__cla), "%s/.proot_diag_classic_a_%d", __dir, (int) getpid()); /* 仅调试用 */
			snprintf(__clb, sizeof(__clb), "%s/.proot_diag_classic_b_%d", __dir, (int) getpid()); /* 仅调试用 */
			unlink(__cla); unlink(__clb); /* 仅调试用 */
			int __caf = open(__cla, O_RDWR | O_CREAT, 0644); /* 仅调试用 */
			if (__caf >= 0) { /* 仅调试用 */
				close(__caf); /* 仅调试用 */
				int __clr = link(__cla, __clb); /* 仅调试用 */
				int __cle = errno; /* 仅调试用 */
				fprintf(stderr, "proot-diag: self link(classic) dir='%s' rc=%d errno=%d(%s)\n", /* 仅调试用 */
					__dir, __clr, __cle, strerror(__cle)); /* 仅调试用 */
				if (__clr == 0) unlink(__clb); /* 仅调试用 */
				unlink(__cla); /* 仅调试用 */
			} /* 仅调试用 */

			/* 仅调试用 5f：symlink —— 验证软链接是否也被禁。 */
			char __syl[256]; /* 仅调试用 */
			snprintf(__syl, sizeof(__syl), "%s/.proot_diag_symlink_%d", __dir, (int) getpid()); /* 仅调试用 */
			unlink(__syl); /* 仅调试用 */
			int __sylr = symlink("/dev/null", __syl); /* 仅调试用 */
			int __syle = errno; /* 仅调试用 */
			fprintf(stderr, "proot-diag: self symlink dir='%s' rc=%d errno=%d(%s)\n", /* 仅调试用 */
				__dir, __sylr, __syle, strerror(__syle)); /* 仅调试用 */
			if (__sylr == 0) unlink(__syl); /* 仅调试用 */
		} /* 仅调试用 */
	} /* 仅调试用 */

	/* Read source path, return if it doesn't belong to /proc  */
	char proc_path[128];
	ssize_t size = read_string(tracee, proc_path, peek_reg(tracee, CURRENT, SYSARG_2), sizeof(proc_path));
	if (size <= 0 || size >= (ssize_t) sizeof(proc_path)) {
		fprintf(stderr, "proot-diag: l2s linkat early-return size=%zd (read_string)\n", size); /* 仅调试用 */
		return 0;
	}
	if (compare_paths(proc_path, "/proc") != PATH2_IS_PREFIX) {
		fprintf(stderr, "proot-diag: l2s linkat early-return not /proc prefix path='%s'\n", proc_path); /* 仅调试用 */
		return 0;
	}

	/* Ensure provided path is symlink to " (deleted)" file.
	 *
	 * 仅调试用：正在追查 Alpine apk linkat EPERM/EACCES 的内核根因。
	 * O_TMPFILE 场景（target 形如 "/<dir>/#<inum>"）之前做过"l2s 接管"修复，
	 * 但未严格验证 errno 归因（怀疑主因不是 fs.protected_hardlinks，
	 * 可能是 SELinux / Android LSM）。本次回退接管，只保留识别+日志，
	 * 放行真实 linkat，靠 syscall.c 的 SYSCALL_EXIT 日志抓取确切返回码。 */
	char target_path[PATH_MAX] = {};
	int status = readlink(proc_path, target_path, sizeof(target_path));
	if (status < 10 || status >= (ssize_t) sizeof(target_path)) {
		fprintf(stderr, "proot-diag: l2s linkat early-return readlink rc=%d errno=%d proc_path='%s'\n", status, errno, proc_path); /* 仅调试用 */
		return 0;
	}
	bool is_deleted = (0 == memcmp(&target_path[status - 10], DELETED_SUFFIX, 10));
	/* 仅调试用：识别 O_TMPFILE 形如 "/<dir>/#<inum>" 以便日志标记，
	 * 但**不**在此接管——放行给真实 linkat 跑完，由 syscall.c exit 日志抓错误码。
	 * 目的：确认 Alpine apk 的 linkat EPERM/EACCES 到底来自内核哪一层
	 * （protected_hardlinks / SELinux / 其他 LSM），之前的 O_TMPFILE
	 * 接管修复虽能 work，但根因归因未严格验证。 */
	bool is_o_tmpfile = false;
	{
		const char *slash = strrchr(target_path, '/');
		if (slash != NULL && slash[1] == '#') {
			const char *p = slash + 2;
			while (*p != '\0' && isdigit((unsigned char) *p))
				p++;
			if (*p == '\0' && p > slash + 2)
				is_o_tmpfile = true;
		}
	}
	if (is_o_tmpfile) {
		/* 仅调试用：dump 真实 inode 元数据 + 父目录属性 + proot 自己复现 linkat
		 * 确认 EPERM 来源。前一次诊断发现 i_uid==fsuid==10164 理论上应通过
		 * may_linkat 的 inode_owner_or_capable 放行，但实际 EPERM。
		 * 本轮进一步排查：
		 *   (a) 父目录 mode/owner/sticky/immutable：排除 vfs_link 里 check_sticky
		 *       或 HAS_UNMAPPED_ID / IS_APPEND / IS_IMMUTABLE 的拦截；
		 *   (b) proot 自己以 AT_SYMLINK_FOLLOW 调一次 linkat 到 /data/.../tmp/
		 *       （tracee target 父目录之外），排除"目标目录特殊"因素；
		 *   (c) proot 自己 linkat 到 tracee 原目标路径，如果**也**是 EPERM，
		 *       说明错误与 tracee 上下文无关（纯内核 policy）。 */
		struct stat __s = {}; /* 仅调试用 */
		int __rc = stat(proc_path, &__s); /* 仅调试用 */
		fprintf(stderr, "proot-diag: l2s O_TMPFILE inode stat rc=%d errno=%d uid=%u gid=%u mode=0%o nlink=%u size=%lld proc_path='%s' target='%.*s' my_fsuid=%u my_fsgid=%u\n", /* 仅调试用 */
			__rc, __rc == 0 ? 0 : errno, /* 仅调试用 */
			(unsigned) __s.st_uid, (unsigned) __s.st_gid, /* 仅调试用 */
			(unsigned) __s.st_mode, (unsigned) __s.st_nlink, /* 仅调试用 */
			(long long) __s.st_size, /* 仅调试用 */
			proc_path, (int) status, target_path, /* 仅调试用 */
			(unsigned) getuid(), (unsigned) getgid()); /* 仅调试用 */

		/* 仅调试用 (a)：stat 匿名 inode 的父目录（target 形如 "/<dir>/#<inum>"） */
		char __parent[PATH_MAX]; /* 仅调试用 */
		size_t __tlen = (size_t) status; /* 仅调试用 */
		const char *__slash = NULL; /* 仅调试用 */
		for (const char *__p = target_path + __tlen - 1; __p > target_path; --__p) { /* 仅调试用 */
			if (*__p == '/') { __slash = __p; break; } /* 仅调试用 */
		} /* 仅调试用 */
		if (__slash != NULL && __slash > target_path) { /* 仅调试用 */
			size_t __plen = (size_t)(__slash - target_path); /* 仅调试用 */
			if (__plen < sizeof(__parent)) { /* 仅调试用 */
				memcpy(__parent, target_path, __plen); /* 仅调试用 */
				__parent[__plen] = '\0'; /* 仅调试用 */
				struct stat __ps = {}; /* 仅调试用 */
				int __prc = stat(__parent, &__ps); /* 仅调试用 */
				fprintf(stderr, "proot-diag: l2s O_TMPFILE parent stat rc=%d errno=%d parent='%s' uid=%u gid=%u mode=0%o nlink=%u\n", /* 仅调试用 */
					__prc, __prc == 0 ? 0 : errno, __parent, /* 仅调试用 */
					(unsigned) __ps.st_uid, (unsigned) __ps.st_gid, /* 仅调试用 */
					(unsigned) __ps.st_mode, (unsigned) __ps.st_nlink); /* 仅调试用 */
			} /* 仅调试用 */
		} /* 仅调试用 */

		/* 仅调试用 (b)：proot 自己试着把同一个 fd linkat 到 proot 可写的临时路径，
		 * 完全避开 tracee 的目标父目录。若仍 EPERM，确认与目标目录无关。 */
		static int __self_test_counter = 0; /* 仅调试用 */
		if (__self_test_counter < 3) { /* 仅调试用：限 3 次避免刷屏 */
			__self_test_counter++; /* 仅调试用 */
			char __my_tmp[128]; /* 仅调试用 */
			snprintf(__my_tmp, sizeof(__my_tmp), "/data/data/com.foxdebug.acode/files/tmp/proot_diag_linkat_%d_%d", /* 仅调试用 */
				(int) getpid(), __self_test_counter); /* 仅调试用 */
			unlink(__my_tmp); /* 仅调试用：保险起见 */
			int __lrc = linkat(AT_FDCWD, proc_path, AT_FDCWD, __my_tmp, AT_SYMLINK_FOLLOW); /* 仅调试用 */
			int __lerr = errno; /* 仅调试用 */
			fprintf(stderr, "proot-diag: l2s SELF-TEST linkat rc=%d errno=%d(%s) src='%s' dst='%s'\n", /* 仅调试用 */
				__lrc, __lerr, strerror(__lerr), proc_path, __my_tmp); /* 仅调试用 */
			if (__lrc == 0) unlink(__my_tmp); /* 仅调试用：清理 */

			/* 仅调试用：额外测一次 AT_EMPTY_PATH（需要 fd 源 而非 /proc magic link）
			 * 我们 open 源 fd 自己来测 —— 如果 /proc magic link 走禁止路径，
			 * 改用 open(proc_path) 得到的普通 fd 行为应一致（都指向同一 inode）。 */
			int __src_fd = open(proc_path, O_RDONLY); /* 仅调试用 */
			if (__src_fd >= 0) { /* 仅调试用 */
				char __my_tmp2[128]; /* 仅调试用 */
				snprintf(__my_tmp2, sizeof(__my_tmp2), "/data/data/com.foxdebug.acode/files/tmp/proot_diag_emptylink_%d_%d", /* 仅调试用 */
					(int) getpid(), __self_test_counter); /* 仅调试用 */
				unlink(__my_tmp2); /* 仅调试用 */
				int __lrc2 = linkat(__src_fd, "", AT_FDCWD, __my_tmp2, AT_EMPTY_PATH); /* 仅调试用 */
				int __lerr2 = errno; /* 仅调试用 */
				fprintf(stderr, "proot-diag: l2s SELF-TEST linkat(AT_EMPTY_PATH) rc=%d errno=%d(%s) src_fd=%d dst='%s'\n", /* 仅调试用 */
					__lrc2, __lerr2, strerror(__lerr2), __src_fd, __my_tmp2); /* 仅调试用 */
				if (__lrc2 == 0) unlink(__my_tmp2); /* 仅调试用 */
				close(__src_fd); /* 仅调试用 */
			} else { /* 仅调试用 */
				fprintf(stderr, "proot-diag: l2s SELF-TEST open src failed errno=%d\n", errno); /* 仅调试用 */
			} /* 仅调试用 */
		} /* 仅调试用 */
	}
	if (!is_deleted) {
		fprintf(stderr, "proot-diag: l2s linkat early-return target not deleted, proc_path='%s' target='%.*s' (tail10='%.10s') is_o_tmpfile=%d\n", proc_path, (int)status, target_path, &target_path[status - 10], is_o_tmpfile); /* 仅调试用 */
		return 0;
	}

	/* Read stats of source file, ensure it is regular file  */
	struct stat stats = {};
	if (0 != stat(proc_path, &stats)) {
		fprintf(stderr, "proot-diag: l2s linkat early-return stat failed errno=%d proc_path='%s'\n", errno, proc_path); /* 仅调试用 */
		return 0;
	}
	if (!S_ISREG(stats.st_mode)) {
		fprintf(stderr, "proot-diag: l2s linkat early-return not regular mode=0%o proc_path='%s'\n", (unsigned)stats.st_mode, proc_path); /* 仅调试用 */
		return 0;
	}

	/* Read path of target file (already translated by proot)  */
	size = read_string(tracee, target_path, peek_reg(tracee, CURRENT, SYSARG_4), PATH_MAX);
	if (size < 0 || size >= (ssize_t) sizeof(target_path)) {
		fprintf(stderr, "proot-diag: l2s linkat early-return target read_string size=%zd\n", size); /* 仅调试用 */
		return 0;
	}

	/* Open source file for reading  */
	int source_fd = open(proc_path, O_RDONLY);
	if (source_fd < 0) {
		fprintf(stderr, "proot-diag: l2s linkat early-return open src failed errno=%d proc_path='%s'\n", errno, proc_path); /* 仅调试用 */
		return 0;
	}

	/* Point of no return, below we no longer are allowed to "return 0",
	 * any errors will be propagated to caller
	 *
	 * Delete target file (we'll be replacing it).
	 * Ignore result of unlink, file could or could not exist,
	 * we'll report failure of open though  */
	unlink(target_path);

	/* Open target file for writing  */
	int target_fd = open(target_path, O_WRONLY|O_CREAT|O_EXCL, stats.st_mode & 0777);
	if (target_fd < 0) {
		status = -errno;
		if (status >= 0)
			status = -EPERM;
		close(source_fd);
		return status;
	}

	/* Copy contents of file  */
	char buf[4096];
	int nread;
	while (0 != (nread = read(source_fd, buf, sizeof(buf)))) {
		if (nread < 0) {
			status = -errno;
			if (status >= 0)
				status = -EPERM;
			close(source_fd);
			close(target_fd);
			return status;
		}
		int pos = 0;
		while (pos < nread) {
			int nwrite = write(target_fd, buf + pos, nread - pos);
			if (nwrite <= 0) {
				status = -errno;
				if (status >= 0)
					status = -EPERM;
				close(source_fd);
				close(target_fd);
				return status;
			}
			pos += nwrite;
		}
	}

	/* Copy successful, nothing more to be done for this syscall  */
	close(source_fd);
	close(target_fd);
	return 1;
}

/**
 * Handler for this @extension.  It is triggered each time an @event
 * occurred.  See ExtensionEvent for the meaning of @data1 and @data2.
 */
int link2symlink_callback(Extension *extension, ExtensionEvent event,
			intptr_t data1, intptr_t data2 UNUSED)
{
	int status;

	switch (event) {
	case INITIALIZATION: {
		/* List of syscalls handled by this extensions.  */
		static FilteredSysnum filtered_sysnums[] = {
			{ PR_link,		FILTER_SYSEXIT },
			{ PR_linkat,		FILTER_SYSEXIT },
			{ PR_unlink,		FILTER_SYSEXIT },
			{ PR_unlinkat,		FILTER_SYSEXIT },
			{ PR_fstat,		FILTER_SYSEXIT },
			{ PR_fstat64,		FILTER_SYSEXIT },
			{ PR_fstatat64,		FILTER_SYSEXIT },
			{ PR_lstat,		FILTER_SYSEXIT },
			{ PR_lstat64,		FILTER_SYSEXIT },
			{ PR_newfstatat,	FILTER_SYSEXIT },
			{ PR_stat,		FILTER_SYSEXIT },
			{ PR_stat64,		FILTER_SYSEXIT },
			{ PR_rename,		FILTER_SYSEXIT },
			{ PR_renameat,		FILTER_SYSEXIT },
			{ PR_renameat2,		FILTER_SYSEXIT },
			FILTERED_SYSNUM_END,
		};
		extension->filtered_sysnums = filtered_sysnums;
		return 0;
	}

	case SYSCALL_ENTER_END: {
		Tracee *tracee = TRACEE(extension);

		switch (get_sysnum(tracee, ORIGINAL)) {
		case PR_rename:
			/*int rename(const char *oldpath, const char *newpath);
			 *If newpath is a psuedo hard link decrement the link count.
			 */

			status = decrement_link_count(tracee, SYSARG_2);
			if (status < 0)
				return status;

			break;

		case PR_renameat:
		case PR_renameat2:
			/*int renameat(int olddirfd, const char *oldpath, int newdirfd, const char *newpath);
			 *If newpath is a psuedo hard link decrement the link count.
			 */

			status = decrement_link_count(tracee, SYSARG_4);
			if (status < 0)
				return status;

			break;

		case PR_unlink:
			/* If path points a file that is an symlink to a file that begins
			 *   with PREFIX, let the file be deleted, but also decrement the
			 *   hard link count, if it is greater than 1, otherwise delete
			 *   the original file and intermediate file too.
			 */

			status = decrement_link_count(tracee, SYSARG_1);
			if (status < 0)
				return status;

			break;

		case PR_unlinkat:
			/* If this is request to delete directory, don't handle it here.
			 * directories cannot be hard links.  */
			if ((peek_reg(tracee, CURRENT, SYSARG_3) & AT_REMOVEDIR) != 0)
			{
				return 0;
			}

			/* If path points a file that is a symlink to a file that begins
			 *   with PREFIX, let the file be deleted, but also delete the
			 *   symlink that was created and decremnt the count that is tacked
			 *   to end of original file.
			 */

			status = decrement_link_count(tracee, SYSARG_2);
			if (status < 0)
				return status;

			break;

		case PR_link:
			/* Convert:
			 *
			 *     int link(const char *oldpath, const char *newpath);
			 *
			 * into:
			 *
			 *     int symlink(const char *oldpath, const char *newpath);
			 */

			status = move_and_symlink_path(tracee, SYSARG_1, SYSARG_2);
			if (status < 0)
				return status;

			break;

		case PR_linkat:
			/*
			 * Handle linkat(..., "/proc/X/fd/Y", ..., AT_SYMLINK_FOLLOW)
			 */
			if (peek_reg(tracee, CURRENT, SYSARG_5) & AT_SYMLINK_FOLLOW) {
				status = handle_linkat_from_proc_fd(tracee);
				if (status < 0)
					return status;
				if (status == 1) {
					set_sysnum(tracee, PR_void);
					poke_reg(tracee, SYSARG_RESULT, 0);
					return 0;
				}
			}

			/* Convert:
			 *
			 *     int linkat(int olddirfd, const char *oldpath,
			 *                int newdirfd, const char *newpath, int flags);
			 *
			 * into:
			 *
			 *     int symlink(const char *oldpath, const char *newpath);
			 *
			 * Note: PRoot has already canonicalized
			 * linkat() paths this way:
			 *
			 *   olddirfd + oldpath -> oldpath
			 *   newdirfd + newpath -> newpath
			 */

			status = move_and_symlink_path(tracee, SYSARG_2, SYSARG_4);
			if (status < 0)
				return status;

			break;

		default:
			break;
		}
		return 0;
	}

	case SYSCALL_EXIT_END: {
		return handle_sysexit_end(TRACEE(extension));
	}

	case TRANSLATED_PATH:
		translated_path(TRACEE(extension), (char *) data1);
		return 0;

	case STATX_SYSCALL:
		link2symlink_handle_statx((struct statx_syscall_state *) data1);
		return 0;

	default:
		return 0;
	}
}
