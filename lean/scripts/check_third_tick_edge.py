"""Check how far an authentic western initial row forces sampled black hits.

The initial row is white strictly west of zero and black at zero. Split on
initial eastern bits until a sampled hit is forced at the chosen column.
The coverage proof and the sharpness witnesses replay with the Python
standard library.
"""


def step(row):
    return (row << 1) ^ (row | (row >> 1))


def trace(row, place, horizon):
    bits = []
    for _ in range(horizon + 1):
        bits.append((row >> place) & 1)
        row = step(row)
    return bits


def forces_hit(distance, start, horizon, bits, east):
    mask = (1 << (2*horizon + 1)) - 1
    target = 1 << horizon
    seed_bit = horizon - distance
    black = (1 << seed_bit) | (east << (seed_bit + 1))
    white = ((1 << (seed_bit + 1 + bits)) - 1) ^ black
    for age in range(horizon + 1):
        if age >= start and (age - start) % 3 == 0 and black & target:
            return True
        # Sites in neither mask are unknown. OR is definitely white only
        # when both inputs are white. XOR is definite only on definite inputs.
        or_black = black | (black >> 1)
        or_white = white & (white >> 1)
        new_black = ((black << 1) & or_white) | ((white << 1) & or_black)
        new_white = ((white << 1) & or_white) | ((black << 1) & or_black)
        black, white = new_black & mask, new_white & mask
    return False


def origin_test():
    # (distance from leftmost black, earliest sampled age, sharp last age,
    # a right half avoiding every earlier eligible tick). Low bit is site +1.
    cases = [
        (-1, 6, 30, 0xce59c), (-1, 7, 10, 3), (-1, 8, 29, 0x3a4f),
        (0, 0, 0, 0), (0, 1, 1, 0), (0, 2, 29, 0xf9cf),
        (1, 0, 9, 0x8), (1, 1, 28, 0x16100e), (1, 2, 20, 0x1ec),
        (2, 0, 27, 0x124e65), (2, 1, 31, 0xfe8e97), (2, 2, 17, 0x127c),
        (3, 0, 30, 0xb7690), (3, 1, 16, 0x3c0), (3, 2, 26, 0x1095a2),
    ]
    for distance, start, horizon, witness in cases:
        todo = [(0, 0)]
        leaves = max_depth = 0
        while todo:
            bits, east = todo.pop()
            if forces_hit(distance, start, horizon, bits, east):
                leaves += 1
                max_depth = max(max_depth, bits)
            else:
                if bits >= horizon + distance:
                    raise AssertionError("a complete cone escapes the deadline")
                todo.extend([(bits + 1, east), (bits + 1, east | (1 << bits))])
        seed_bit = horizon - distance
        row = (1 << seed_bit) | (witness << (seed_bit + 1))
        readings = trace(row, horizon, horizon)
        if any(readings[start:horizon:3]) or not readings[horizon]:
            raise AssertionError("the sharpness witness does not attain the deadline")
        print(f"Distance {distance}, start {start}: sharp deadline {horizon}, {leaves} leaves, depth {max_depth}.")


if __name__ == "__main__":
    origin_test()
