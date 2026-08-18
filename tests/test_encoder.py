#!/usr/bin/env python3
"""Focused regressions for the standalone binary encoder."""

import importlib.util
import io
import struct
import sys


def load_encoder(path):
    spec = importlib.util.spec_from_file_location("binreader_encoder", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def decode_limbs(data):
    words = [value[0] for value in struct.iter_unpack("<Q", data)]
    count, *limbs = words
    assert count == len(limbs)
    return sum(limb << (63 * index) for index, limb in enumerate(limbs))


def main():
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} ENCODER")

    encoder = load_encoder(sys.argv[1])

    # Float log2 used to round these boundary values incorrectly.
    values = [
        0,
        1,
        (1 << 63) - 1,
        1 << 63,
        (1 << 126) - 1,
        1 << 126,
    ]
    for value in values:
        stream = io.BytesIO()
        encoder.D_BigN.INSTANCE.pickle(value, stream)
        assert decode_limbs(stream.getvalue()) == value

    assert encoder.descriptor_of_string("([[I]],Z,N)") is not None
    for invalid in ["Ix", "Qgarbage", "(I,N))", "[I]trailing"]:
        try:
            encoder.descriptor_of_string(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted trailing descriptor text: {invalid}")

    print("ok")


if __name__ == "__main__":
    main()
