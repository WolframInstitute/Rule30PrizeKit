"""Finite phase test for an eastern window driven by 001 or 011.

Bit zero of a state is site +1. Its phase gives the current center color.
At every step the cell beyond the eastern edge may be chosen afresh.
All initial states are included. Run with Python 3, without dependencies.
"""


def parent_colors(width):
    """All possible past center colors given the observed next eastern word."""
    mask = (1 << width) - 1
    colors = bytearray(1 << width)
    for parent in range(1 << (width + 2)):
        image = (parent ^ ((parent >> 1) | (parent >> 2))) & mask
        colors[image] |= 1 << (parent & 1)
    assert all(colors)
    return colors


def children(width, drive):
    size = 1 << width
    mask = size - 1
    edges = []
    for phase, center in enumerate(drive):
        offset = ((phase + 1) % 3) * size
        for x in range(size):
            left = (x << 1) | center
            east = x >> 1
            y0 = (left ^ (x | east)) & mask
            y1 = (left ^ (x | east | (size >> 1))) & mask
            edges.append((offset + y0, offset + y1))
    return edges


def max_avoidance(width, drive):
    """Numbers of rows in longest walks without a readout of a given phase."""
    size = 1 << width
    colors = parent_colors(width)
    edges = children(width, drive)
    limits = []
    for ph in range(3):
        # Each row at phase ph+1 observes the preceding center at phase ph.
        allowed = bytearray(i // size != (ph + 1) % 3 or colors[i % size] == 3
                            for i in range(3 * size))
        # A determinate word on a real edge must return the driving color.
        for i in range(ph * size, (ph + 1) * size):
            for child in edges[i]:
                assert colors[child % size] & (1 << drive[ph])
        live = allowed
        rows = 0
        while any(live):
            rows += 1
            following = bytearray(ok and (live[a] or live[b])
                                  for ok, (a, b) in zip(allowed, edges))
            if following == live:
                raise ValueError(f"unbounded avoidance for {drive}, phase {ph}")
            live = following
        limits.append(rows)
    return tuple(limits)


if __name__ == "__main__":
    for clock, expected in [((0, 0, 1), (14, 13, 19)), ((0, 1, 1), (14, 17, 17))]:
        lengths = max_avoidance(15, clock)
        assert lengths == expected
        print(f"{clock}: longest readout-free blocks by prior phase = {lengths} rows")
