#!/usr/bin/env python3
"""Generate a fixture whose Int63 payload straddles the reader buffer edge."""

import struct
import sys


WORD = struct.Struct("<Q")
LENGTH = 131_073
DEFAULT = 424_242


def write_word(stream, value):
    stream.write(WORD.pack(value))


def main():
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} OUTPUT")

    with open(sys.argv[1], "wb") as stream:
        write_word(stream, 0x05)  # Array
        write_word(stream, 0x06)  # Record
        write_word(stream, 5)
        stream.write(b"point")   # Deliberately not 8-byte aligned.
        write_word(stream, 1)
        write_word(stream, 0x00)  # The record's sole Int63 field.

        write_word(stream, LENGTH)
        write_word(stream, DEFAULT)
        for value in range(LENGTH):
            write_word(stream, value)


if __name__ == "__main__":
    main()
