/* -*- c-set-style: "K&R"; c-basic-offset: 8 -*-
 *
 * This file is part of PRoot.
 *
 * Copyright (C) 2015 STMicroelectronics
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */

#include <stdbool.h>     /* bool, true, false,  */

#define NO_LIBC_HEADER
#include "loader/script.h"
#include "compat.h"
#include "arch.h"

#if defined(ARCH_X86_64)
#    include "loader/assembly-x86_64.h"
#elif defined(ARCH_ARM_EABI)
#    include "loader/assembly-arm.h"
#elif defined(ARCH_X86)
#    include "loader/assembly-x86.h"
#elif defined(ARCH_ARM64)
#    include "loader/assembly-arm64.h"
#else
#    error "Unsupported architecture"
#endif

#if !defined(MMAP_OFFSET_SHIFT)
#    define MMAP_OFFSET_SHIFT 0
#endif

/* _STR / _XSTR: stringify macro for embedding __LINE__ in static strings. */ /* 仅调试用 */
#define _STR(x) #x /* 仅调试用 */
#define _XSTR(x) _STR(x) /* 仅调试用 */

/* Write a diagnostic message to stderr (fd 2) before exiting 182.
 * This distinguishes loader FATAL() from signal-54-killed processes,
 * since both produce $?=182 in the parent shell. */
#define FATAL() do {						\
		static const char _fatal_msg[] =		\
			"[loader:FATAL,line=" _XSTR(__LINE__) "]\n"; /* 仅调试用 */ \
		SYSCALL(WRITE, 3, 2,				\
			(word_t)_fatal_msg,			\
			sizeof(_fatal_msg) - 1);		/* 仅调试用 */ \
		SYSCALL(EXIT, 1, 182);				\
		__builtin_unreachable();			\
	} while (0)

#define unlikely(expr) __builtin_expect(!!(expr), 0)

/* Write a word_t value as 16-char hex string to stderr. No libc needed. */ /* 仅调试用 */
static inline void _write_hex(word_t v) /* 仅调试用 */
{ /* 仅调试用 */
	char buf[16]; /* 仅调试用 */
	int i; /* 仅调试用 */
	for (i = 15; i >= 0; i--) { /* 仅调试用 */
		int n = v & 0xf; /* 仅调试用 */
		buf[i] = n < 10 ? '0' + n : 'a' + n - 10; /* 仅调试用 */
		v >>= 4; /* 仅调试用 */
	} /* 仅调试用 */
	SYSCALL(WRITE, 3, 2, (word_t)buf, 16); /* 仅调试用 */
} /* 仅调试用 */

/**
 * Clear the memory from @start (inclusive) to @end (exclusive).
 */
static inline void clear(word_t start, word_t end)
{
	byte_t *start_misaligned;
	byte_t *end_misaligned;

	word_t *start_aligned;
	word_t *end_aligned;

	/* Compute the number of mis-aligned bytes.  */
	word_t start_bytes = start % sizeof(word_t);
	word_t end_bytes   = end % sizeof(word_t);

	/* Compute aligned addresses.  */
	start_aligned = (word_t *) (start_bytes ? start + sizeof(word_t) - start_bytes : start);
	end_aligned   = (word_t *) (end - end_bytes);

	/* Clear leading mis-aligned bytes.  */
	start_misaligned = (byte_t *) start;
	while (start_misaligned < (byte_t *) start_aligned)
		*start_misaligned++ = 0;

	/* Clear aligned bytes.  */
	while (start_aligned < end_aligned)
		*start_aligned++ = 0;

	/* Clear trailing mis-aligned bytes.  */
	end_misaligned = (byte_t *) end_aligned;
	while (end_misaligned < (byte_t *) end)
		*end_misaligned++ = 0;
}

/**
 * Return the address of the last path component of @string_.  Note
 * that @string_ is not modified.
 */
static inline word_t basename(word_t string_)
{
	byte_t *string = (byte_t *) string_;
	byte_t *cursor;

	for (cursor = string; *cursor != 0; cursor++)
		;

	for (; *cursor != (byte_t) '/' && cursor > string; cursor--)
		;

	if (cursor != string)
		cursor++;

	return (word_t) cursor;
}

/**
 * Interpret the load script pointed to by @cursor.
 */
void _start(void *cursor)
{
	bool traced = false;
	bool reset_at_base = true;
	word_t at_base = 0;

	word_t fd = -1;
	word_t status;

	while(1) {
		LoadStatement *stmt = cursor;

		switch (stmt->action) {
		case LOAD_ACTION_OPEN_NEXT:
			status = SYSCALL(CLOSE, 1, fd);
			if (unlikely((int) status < 0))
				FATAL();
			/* Fall through.  */

		case LOAD_ACTION_OPEN:
#if defined(OPEN)
			fd = SYSCALL(OPEN, 3, stmt->open.string_address, O_RDONLY, 0);
#else
			fd = SYSCALL(OPENAT, 4, AT_FDCWD, stmt->open.string_address, O_RDONLY, 0);
#endif
			if (unlikely((int) fd < 0))
				FATAL();

			reset_at_base = true;

			cursor += LOAD_STATEMENT_SIZE(*stmt, open);
			break;

		case LOAD_ACTION_MMAP_FILE:
			status = SYSCALL(MMAP, 6, stmt->mmap.addr, stmt->mmap.length,
					stmt->mmap.prot, MAP_PRIVATE | MAP_FIXED, fd,
					stmt->mmap.offset >> MMAP_OFFSET_SHIFT);
			if (unlikely(status != stmt->mmap.addr)) {
				/* mmap returned unexpected addr; dump exp/got/len/fd for diagnosis */ /* 仅调试用 */
				static const char _h1[] = "[loader:mmap-fail,exp="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_h1, sizeof(_h1) - 1); /* 仅调试用 */
				_write_hex(stmt->mmap.addr); /* 仅调试用 */
				static const char _h2[] = ",got="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_h2, sizeof(_h2) - 1); /* 仅调试用 */
				_write_hex(status); /* 仅调试用 */
				static const char _h3[] = ",len="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_h3, sizeof(_h3) - 1); /* 仅调试用 */
				_write_hex(stmt->mmap.length); /* 仅调试用 */
				static const char _h4[] = ",fd="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_h4, sizeof(_h4) - 1); /* 仅调试用 */
				_write_hex(fd); /* 仅调试用 */
				static const char _h5[] = "]\n"; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_h5, sizeof(_h5) - 1); /* 仅调试用 */

				/* Probe MAP_FIXED at multiple addresses to find the kernel's
				 * accepted/rejected boundary. Previous round confirmed:
				 * - 0x3000000000 persistently -EFAULT (not transient)
				 * - Same mmap without MAP_FIXED succeeds (fd/prot OK)
				 * - /proc/PID/maps shows 0x3000000000 is unoccupied
				 * - vdso/kshare at ~0x2fa1c3XXXX, only ~1.5GB below target
				 * Hypothesis: Huawei kernel restricts MAP_FIXED near vdso.
				 * Test addresses: 0x21-0x50 (×2^32) to map the boundary. */ /* 仅调试用 */
				{ /* 仅调试用 */
					/* Test addresses from 0x2100000000 to 0x5000000000 */ /* 仅调试用 */
					static const word_t test_addrs[] = { /* 仅调试用 */
						0x2100000000UL, /* 132 GB — just above loader */ /* 仅调试用 */
						0x2800000000UL, /* 160 GB — midpoint */ /* 仅调试用 */
						0x2e00000000UL, /* 184 GB — below vdso */ /* 仅调试用 */
						0x2f00000000UL, /* 188 GB — closer to vdso */ /* 仅调试用 */
						0x2f80000000UL, /* 190 GB — very near vdso */ /* 仅调试用 */
						0x3000000000UL, /* 192 GB — EXEC_PIC_ADDRESS (known fail) */ /* 仅调试用 */
						0x3100000000UL, /* 196 GB — above target */ /* 仅调试用 */
						0x4000000000UL, /* 256 GB — well above */ /* 仅调试用 */
						0x5000000000UL, /* 320 GB — much higher */ /* 仅调试用 */
					}; /* 仅调试用 */
					word_t page_sz = 0x1000; /* 仅调试用 */
					int ti; /* 仅调试用 */
					for (ti = 0; ti < 9; ti++) { /* 仅调试用 */
						word_t taddr = test_addrs[ti]; /* 仅调试用 */
						word_t tret = SYSCALL(MMAP, 6, taddr, page_sz, /* 仅调试用 */
								0x3 /* PROT_READ|PROT_WRITE */, /* 仅调试用 */
								MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, /* 仅调试用 */
								-1, 0); /* 仅调试用 */
						static const char _t1[] = "[loader:addr-probe,addr="; /* 仅调试用 */
						SYSCALL(WRITE, 3, 2, (word_t)_t1, sizeof(_t1) - 1); /* 仅调试用 */
						_write_hex(taddr); /* 仅调试用 */
						static const char _t2[] = ",got="; /* 仅调试用 */
						SYSCALL(WRITE, 3, 2, (word_t)_t2, sizeof(_t2) - 1); /* 仅调试用 */
						_write_hex(tret); /* 仅调试用 */
						static const char _t3[] = "]\n"; /* 仅调试用 */
						SYSCALL(WRITE, 3, 2, (word_t)_t3, sizeof(_t3) - 1); /* 仅调试用 */
						/* Unmap if successful to keep address space clean */ /* 仅调试用 */
						if (tret == taddr) /* 仅调试用 */
							SYSCALL(MUNMAP, 3, tret, page_sz, 0); /* 仅调试用 */
					} /* 仅调试用 */
				} /* 仅调试用 */

				FATAL();
			}

			if (stmt->mmap.clear_length != 0)
				clear(stmt->mmap.addr + stmt->mmap.length - stmt->mmap.clear_length,
					stmt->mmap.addr + stmt->mmap.length);

			if (reset_at_base) {
				at_base = stmt->mmap.addr;
				reset_at_base = false;
			}

			cursor += LOAD_STATEMENT_SIZE(*stmt, mmap);
			break;

		case LOAD_ACTION_MMAP_ANON:
			status = SYSCALL(MMAP, 6, stmt->mmap.addr, stmt->mmap.length,
					stmt->mmap.prot, MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, -1, 0);
			if (unlikely(status != stmt->mmap.addr)) {
				/* anon mmap returned unexpected addr */ /* 仅调试用 */
				static const char _a1[] = "[loader:mmap-anon-fail,exp="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_a1, sizeof(_a1) - 1); /* 仅调试用 */
				_write_hex(stmt->mmap.addr); /* 仅调试用 */
				static const char _a2[] = ",got="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_a2, sizeof(_a2) - 1); /* 仅调试用 */
				_write_hex(status); /* 仅调试用 */
				static const char _a3[] = ",len="; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_a3, sizeof(_a3) - 1); /* 仅调试用 */
				_write_hex(stmt->mmap.length); /* 仅调试用 */
				static const char _a4[] = "]\n"; /* 仅调试用 */
				SYSCALL(WRITE, 3, 2, (word_t)_a4, sizeof(_a4) - 1); /* 仅调试用 */
				FATAL();
			}

			cursor += LOAD_STATEMENT_SIZE(*stmt, mmap);
			break;

		case LOAD_ACTION_MAKE_STACK_EXEC:
			SYSCALL(MPROTECT, 3,
				stmt->make_stack_exec.start, 1,
				PROT_READ | PROT_WRITE | PROT_EXEC | PROT_GROWSDOWN);

			cursor += LOAD_STATEMENT_SIZE(*stmt, make_stack_exec);
			break;

		case LOAD_ACTION_START_TRACED:
			traced = true;
			/* Fall through.  */

		case LOAD_ACTION_START: {
			word_t *cursor2 = (word_t *) stmt->start.stack_pointer;
			const word_t argc = cursor2[0];
			const word_t at_execfn = cursor2[1];
			word_t name;

			status = SYSCALL(CLOSE, 1, fd);
			if (unlikely((int) status < 0))
				FATAL();

			/* Right after execve, the stack content is as follow:
			 *
			 *   +------+--------+--------+--------+
			 *   | argc | argv[] | envp[] | auxv[] |
			 *   +------+--------+--------+--------+
			 */

			/* Skip argv[].  */
			cursor2 += argc + 1;

			/* Skip envp[].  */
			do cursor2++; while (cursor2[0] != 0);
			cursor2++;

			/* Adjust auxv[].  */
			do {
				switch (cursor2[0]) {
				case AT_PHDR:
					cursor2[1] = stmt->start.at_phdr;
					break;

				case AT_PHENT:
					cursor2[1] = stmt->start.at_phent;
					break;

				case AT_PHNUM:
					cursor2[1] = stmt->start.at_phnum;
					break;

				case AT_ENTRY:
					cursor2[1] = stmt->start.at_entry;
					break;

				case AT_BASE:
					cursor2[1] = at_base;
					break;

				case AT_EXECFN:
					/* stmt->start.at_execfn can't be used for now since it is
					 * currently stored in a location that will be scratched
					 * by the process (below the final stack pointer).  */
					cursor2[1] = at_execfn;
					break;

				default:
					break;
				}
				cursor2 += 2;
			} while (cursor2[0] != AT_NULL);

			/* Note that only 2 arguments are actually necessary... */
			name = basename(stmt->start.at_execfn);
			SYSCALL(PRCTL, 3, PR_SET_NAME, name, 0);

			if (unlikely(traced))
				SYSCALL(EXECVE, 6, 1,
					stmt->start.stack_pointer,
					stmt->start.entry_point, 2, 3, 4);
			else
				BRANCH(stmt->start.stack_pointer, stmt->start.entry_point);
			FATAL();
		}

		default:
			FATAL();
		}
	}

	FATAL();
}
