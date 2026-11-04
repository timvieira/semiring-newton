"""
Tests for the claims made in the blog post (content/semiring-newton.md).

If one of these fails, the post is wrong until proven otherwise.
"""
import inspect
import re
from pathlib import Path

from leftcorner import CFG, Real, MaxTimes

from newton import newton
from newton.newton import _newton, linearize


POST = Path(__file__).resolve().parent.parent / 'content' / 'semiring-newton.md'


def newton_iterates(cfg, T):
    "Value of chart' (all derivations of dimension <= t) for t = 0..T."
    out = []
    for t, (_, _, next_chart) in enumerate(_newton(cfg)):
        out.append(next_chart)
        if t == T:
            return out


def critical():
    return CFG.from_string("""
    0.5: S → S S
    0.5: S → a
    """, Real)


def test_critical_newton_one_bit_per_iteration():
    # Newton's error after iteration t is exactly 2^-(t+1).
    for t, chart in enumerate(newton_iterates(critical(), 39)):
        assert abs((1 - chart['S'].score) - 2.0**-(t+1)) < 1e-15


def test_critical_fixpoint_iteration_is_slow():
    # Fixpoint iteration's error after n iterations is about 2/n.
    cfg = critical()
    V = cfg.R.chart()
    errs = {}
    for n in range(1, 100_001):
        V = cfg._bottom_up_step(V)
        errs[n] = 1 - V['S'].score
    assert round(errs[10], 2) == 0.14
    assert round(errs[100], 3) == 0.019
    assert abs(errs[1000] - 2e-3) < 5e-5
    assert abs(errs[100_000] - 2e-5) < 5e-7


def test_subcritical_quadratic():
    cfg = CFG.from_string("""
    0.25: S → S S
    0.75: S → a
    """, Real)
    errs = [1 - c['S'].score for c in newton_iterates(cfg, 4)]
    want = [0.25, 0.025, 3e-4, 5e-8, 1e-15]
    for e, w in zip(errs, want):
        assert 0.5 * w <= e <= 2 * w, (e, w)


def test_matches_textbook_newton():
    # Over the reals, iteration t equals step t+1 of Newton's method on
    # g(x) = 1/2 x^2 - x + 1/2 = 0 started from x = 0.
    x = 0.0
    for chart in newton_iterates(critical(), 20):
        x = x - (0.5*x*x - x + 0.5) / (x - 1)
        assert abs(chart['S'].score - x) < 1e-12


def test_linear_grammar_is_dimension_zero():
    # Linear grammars are solved exactly by the initialization.
    cfg = CFG.from_string("""
    0.5: S → S a
    1: S → b
    """, Real)
    [chart] = newton_iterates(cfg, 0)
    assert abs(chart['S'].score - 2) < 1e-12


def test_viterbi_example():
    cfg = CFG.from_string("""
    1.0: S → NP VP
    0.4: NP → NP PP
    0.6: NP → n
    0.7: VP → v NP
    0.3: VP → VP PP
    1.0: PP → p NP
    """, MaxTimes)
    have = newton(cfg)
    assert abs(have['S'].score - 0.252) < 1e-12
    assert abs(have['NP'].score - 0.6) < 1e-12
    assert abs(have['VP'].score - 0.42) < 1e-12
    assert abs(have['PP'].score - 0.6) < 1e-12
    # exact after initialization plus one iteration
    iterates = newton_iterates(cfg, 1)
    assert iterates[0].metric(have) != 0
    assert iterates[1].metric(have) == 0


def test_catalan_example():
    # X = X X + c: the least solution is the smaller root, (1 - sqrt(1 - 4c)) / 2,
    # and its series is c + c^2 + 2c^3 + 5c^4 + 14c^5 + 42c^6 + ...
    c = 0.2
    cfg = CFG.from_string(f"""
    1: X → X X
    {c}: X → a
    """, Real, start='X')
    assert abs(newton(cfg)['X'].score - (1 - (1 - 4*c)**0.5) / 2) < 1e-10
    x = [0]*8            # truncated power series in c, by fixpoint iteration
    for _ in range(8):
        sq = [sum(x[i]*x[n-i] for i in range(n+1)) for n in range(8)]
        x = [sq[n] + (n == 1) for n in range(8)]
    assert x[1:7] == [1, 1, 2, 5, 14, 42]


def test_post_code_matches_source():
    post = POST.read_text()
    blocks = re.findall(r'```python\n(.*?)```', post, re.DOTALL)
    for fn in [_newton, linearize]:
        assert inspect.getsource(fn) in blocks, fn.__name__


def test_figures_are_up_to_date(tmp_path, monkeypatch):
    # The committed SVGs must match what content/make_figures.py draws.
    import importlib.util
    path = POST.parent / 'make_figures.py'
    spec = importlib.util.spec_from_file_location('make_figures', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    monkeypatch.setattr(mod, 'OUT', tmp_path)
    mod.dimension_figure()
    mod.newton_step_figure()
    mod.convergence_figure()
    mod.height_dimension_figure()
    for name in ['dimension.svg', 'newton-step.svg', 'convergence.svg', 'height-dimension.svg']:
        assert (tmp_path / name).read_text() == (POST.parent / 'images' / name).read_text(), name
