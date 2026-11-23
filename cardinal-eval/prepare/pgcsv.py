#!/usr/bin/env python3
"""Rewrites PostgreSQL CSV (`COPY ... CSV ESCAPE '\\'`) as RFC 4180 CSV.

In PostgreSQL's CSV, the escape character only escapes, inside a quoted
field, the quote and itself; anywhere else a backslash is a backslash. DuckDB
applies an escape outside quotes too, so a field ending in a backslash
breaks its row. This keeps every field as it was (quoted or not: an empty
unquoted field is NULL, a quoted one an empty string) and writes an inner
quote as two.

    pgcsv.py <in.csv> <out.csv>
"""

import sys


def convert(src, dst):
    quoted = False
    with open(src, encoding="utf-8", errors="surrogateescape", newline="") as i, \
         open(dst, "w", encoding="utf-8", errors="surrogateescape", newline="") as o:
        for line in i:
            # Most lines: no backslash and no quoted field open across lines.
            if not quoted and "\\" not in line and line.count('"') % 2 == 0:
                o.write(line)
                continue
            out = []
            j, n = 0, len(line)
            while j < n:
                c = line[j]
                if quoted:
                    if c == "\\" and j + 1 < n and line[j + 1] in '"\\':
                        out.append('""' if line[j + 1] == '"' else "\\")
                        j += 2
                        continue
                    if c == '"':
                        quoted = False
                    out.append(c)
                else:
                    if c == '"':
                        quoted = True
                    out.append(c)
                j += 1
            o.write("".join(out))


if __name__ == "__main__":
    convert(sys.argv[1], sys.argv[2])
