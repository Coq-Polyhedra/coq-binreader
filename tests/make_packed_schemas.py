#!/usr/bin/env python3
"""Generate small, independent fixtures for every packed decoder schema."""

import pathlib
import struct
import sys


WORD = struct.Struct("<Q")


def word(value):
    return WORD.pack(value)


def bign(*limbs):
    return word(len(limbs)) + b"".join(word(limb) for limb in limbs)


def bigz(sign, *limbs):
    return word(sign) + bign(*limbs)


def write(directory, name, data):
    (directory / name).write_bytes(data)


def main():
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} OUTPUT_DIRECTORY")

    output = pathlib.Path(sys.argv[1])
    output.mkdir(parents=True, exist_ok=True)

    write(output, "packed-int.bin",
          word(0x00) + word(0x0102030405060708))
    write(output, "packed-n.bin",
          word(0x01) + bign(7, 11, 13, 0))
    write(output, "packed-z.bin",
          word(0x02) + bigz(2, 9))
    write(output, "packed-q.bin",
          word(0x03) + bigz(0, 5) + bign())
    write(output, "packed-pair.bin",
          word(0x04) + word(0x00) + word(0x01)
          + word(17) + bign(19, 23))
    write(output, "packed-array.bin",
          word(0x05) + word(0x00)
          + word(2) + word(42) + word(3) + word(4))
    write(output, "packed-empty-array.bin",
          word(0x05) + word(0x00) + word(0) + word(42))
    boundary_counts = [63, 64, 65, 127, 128, 129]
    write(output, "packed-n-boundaries.bin",
          word(0x05) + word(0x01)
          + word(len(boundary_counts)) + bign()
          + b"".join(bign(*range(1, count + 1))
                     for count in boundary_counts))

    name = b"M.point"
    record_descriptor = (
        word(0x06) + word(len(name)) + name + word(2)
        + word(0x00) + word(0x02)
    )
    write(output, "packed-record.bin",
          record_descriptor + word(12) + bigz(0, 9))
    empty_name = b"M.empty"
    write(output, "packed-empty-record.bin",
          word(0x06) + word(len(empty_name)) + empty_name + word(0))

    write(output, "packed-array-too-large.bin",
          word(0x05) + word(0x00) + word(4_194_304) + word(0))
    write(output, "packed-array-truncated-max.bin",
          word(0x05) + word(0x00) + word(4_194_303) + word(0))
    write(output, "packed-bign-huge-count.bin",
          word(0x01) + word((1 << 63) - 1))


if __name__ == "__main__":
    main()
