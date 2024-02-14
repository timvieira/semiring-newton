from leftcorner import Real, CFG
from leftcorner.misc import assert_equal_chart, colors
from newton import newton


def test_treesum1():

    cfg = CFG.from_string("""

    0.25: S → S S
    0.75: S → a

    """, Real)

    want = cfg.agenda()
    have = newton(cfg)

    assert_equal_chart(have, want, verbose=True)


def test_treesum2():

    cfg = CFG.from_string("""

    0.15: S → a S b S c
    0.15: S → a S b
    0.7: S → d

    """, Real)

    want = cfg.agenda()
    have = newton(cfg)

    assert_equal_chart(have, want, verbose=True)


def test_geom():

    cfg = CFG.from_string("""

    0.5: S → S :
    1: S → a

    """, Real)

    want = cfg.agenda()
    have = newton(cfg)

    assert_equal_chart(have, want, verbose=True)


def test_misc():

    cfg = CFG.from_string("""

    1: S → XY Z

    7: XY → X Y

    2: X → x
    0.5: Y → Y y
    3: Y → y
    4: Z → z

    """, Real)

    want = cfg.agenda()
    have = newton(cfg)

    assert_equal_chart(have, want, verbose=True)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
