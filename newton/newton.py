from leftcorner import CFG
from leftcorner.misc import colors
from itertools import combinations
from newton.chart import Chart
from functools import cached_property


def newton(self, T=None, verbosity=0, tol=1e-12):
    """
    Newton algorithm for solving fixpoint systems of equations over a
    commutative semiring.
    """
    for t, (chart, change, next_chart) in enumerate(_newton(self)):
        if verbosity > 1:
            print(colors.light.yellow % f'iter {t}:')
            print('chart:', chart)
            print('change:', change)
            print('next_chart:', next_chart)

        err = chart.metric(next_chart)
        if verbosity > 0:
            print(t, 'err=', err)
        if err <= tol:          # fixpoint test
            if verbosity > 0: print(colors.light.yellow % 'converged')
            return next_chart
        if T is not None and t == T:      # no more iterations
            if verbosity > 0: print(colors.light.yellow % 'stopped early')
            return next_chart


def _newton(self):
    # initial chart is empty, except for terminals
    chart = Chart(self.R, {x: self.R.one for x in self.V})
    # initialize with dim<=1 derivations
    change = linearize(self, chart, chart, chart, init=True)
    while True:
        next_chart = chart + change.sol
        yield (chart, change, next_chart)
        change = linearize(self, chart, change.sol, next_chart)
        chart = next_chart


class Change:
    def __init__(self, cfg, A, b):
        self.cfg = cfg
        self.A = A
        self.b = b
    @cached_property
    def K(self):
        return self.cfg._lehmann(self.cfg.N, self.A)
    @cached_property
    def sol(self):
        K = self.K
        sol = Chart(self.cfg.R)
        for i in self.cfg.N:
            for j in self.cfg.N:
                sol[i] += K[i,j] * self.b[j]
        return sol


def linearize(self, chart, change, next_chart, init=False):
    # Matrix and vector for linearized grammar
    A = Chart(self.R)
    b = Chart(self.R)

    # recursive cases
    for r in self:
        ys = r.body
        for k in range(len(ys)):
            if self.is_terminal(ys[k]): continue
            A[r.head, ys[k]] += (
                r.w
                * next_chart.product(ys[:k])
                * next_chart.product(ys[k+1:])
            )

    # base cases for initialization
    if init:
        for r in self:
            if all(map(self.is_terminal, r.body)):
                b[r.head] += r.w

    # base cases for iterates
    else:
        for r in self:
            ys = r.body
            for i,j in combinations(range(len(ys)), 2):
                b[r.head] += (
                    r.w *
                    next_chart.product(ys[:i]) *
                    change[ys[i]] *
                    chart.product(ys[i+1:j]) *
                    change[ys[j]] *
                    chart.product(ys[j+1:])
                )

    return Change(self, A, b)
