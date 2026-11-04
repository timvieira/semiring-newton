from leftcorner import CFG, Real, MaxTimes
from leftcorner.misc import assert_equal_chart

from newton import solve
from newton.hybrid import sccs


GRAMMARS = {
    'treesum1': """
    0.25: S → S S
    0.75: S → a
    """,
    'treesum2': """
    0.15: S → a S b S c
    0.15: S → a S b
    0.7: S → d
    """,
    'geom': """
    0.5: S → S :
    1: S → a
    """,
    'misc': """
    1: S → XY Z
    7: XY → X Y
    2: X → x
    0.5: Y → Y y
    3: Y → y
    4: Z → z
    """,
    'pp': """
    1: S → NP VP
    0.4: NP → NP PP
    0.6: NP → n
    0.7: VP → v NP
    0.3: VP → VP PP
    1.0: PP → p NP
    0.5: VP → V
    0.5: V → V v
    0.5: V → v
    """,
}


def test_matches_agenda():
    for name, g in GRAMMARS.items():
        for R in [Real, MaxTimes]:
            cfg = CFG.from_string(g, R)
            assert_equal_chart(solve(cfg), cfg.agenda(), verbose=False), (name, R)


def test_scc_order_and_methods():
    cfg = CFG.from_string(GRAMMARS['pp'], Real)
    trace = []
    solve(cfg, trace=trace)
    assert [(sorted(s), m) for s, m in trace] == [
        (['NP', 'PP'], 'newton'),      # NP → NP PP, PP → p NP: nonlinear
        (['V'], 'solve_linear'),
        (['VP'], 'solve_linear'),      # VP → VP PP is linear once PP is solved
        (['S'], 'solve_linear'),       # acyclic
    ]


def test_sccs_are_topologically_ordered():
    for g in GRAMMARS.values():
        cfg = CFG.from_string(g, Real)
        order = sccs(cfg)
        position = {X: i for i, scc in enumerate(order) for X in scc}
        for r in cfg:
            for y in r.body:
                if cfg.is_nonterminal(y):
                    assert position[y] <= position[r.head]


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
