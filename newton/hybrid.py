"""
Hybrid solver: break a grammar into strongly connected components (SCCs),
solve them in topological order, and solve each one with the best applicable
method (Section "Hybrid Algorithm" in chapter 5 of Tim Vieira's dissertation).

Assumes a commutative semiring (as does the rest of this package): solved
nonterminals from earlier components are folded into the rule weights.
"""
from leftcorner import CFG

from newton.chart import Chart
from newton.newton import newton


def solve(cfg, tol=1e-12, trace=None):
    """
    Solve `cfg` by SCC decomposition.  Returns a chart with the value of every
    nonterminal (and terminals, which have value one).  If `trace` is a list,
    each component and the method used to solve it are appended to it.
    """
    R = cfg.R
    chart = Chart(R, {a: R.one for a in cfg.V})
    for scc in sccs(cfg):
        sub = restrict(cfg, scc, chart)
        method, sol = best_solve(sub, tol)
        if trace is not None:
            trace.append((scc, method))
        for X in scc:
            chart[X] = sol[X]
    return chart


def sccs(cfg):
    """
    Strongly connected components of the dependency graph X → Y (Y is a
    nonterminal in the body of a rule for X), in topological order:
    each component comes after the components it depends on.  Tarjan's
    algorithm emits components in exactly this order.
    """
    succ = {}
    for r in cfg:
        succ.setdefault(r.head, set()).update(y for y in r.body if cfg.is_nonterminal(y))
    nodes = list(dict.fromkeys([*succ, *(y for ys in succ.values() for y in ys)]))

    index, low, on_stack, stack, out = {}, {}, set(), [], []
    for root in nodes:
        if root in index: continue
        work = [(root, iter(sorted(succ.get(root, ()))))]   # iterative DFS
        index[root] = low[root] = len(index)
        stack.append(root); on_stack.add(root)
        while work:
            v, children = work[-1]
            for w in children:
                if w not in index:
                    index[w] = low[w] = len(index)
                    stack.append(w); on_stack.add(w)
                    work.append((w, iter(sorted(succ.get(w, ())))))
                    break
                elif w in on_stack:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    scc = []
                    while True:
                        w = stack.pop(); on_stack.discard(w)
                        scc.append(w)
                        if w == v: break
                    out.append(frozenset(scc))
    return out


def restrict(cfg, scc, chart):
    """
    The subgrammar for the nonterminals in `scc`: their rules, with every
    symbol outside the component (terminals and already-solved nonterminals)
    folded into the rule's weight.
    """
    sub = CFG(R=cfg.R, S=next(iter(scc)), V=set())
    sub.N |= scc
    for r in cfg:
        if r.head not in scc: continue
        w = r.w
        for y in r.body:
            if y not in scc:
                w = w * chart[y]
        sub.add(w, r.head, *[y for y in r.body if y in scc])
    return sub


def best_solve(sub, tol):
    """
    Solve a subgrammar with the best method available, following the ranking:
    solve_linear (exact), then newton (fast), then agenda (most general).
    An acyclic component is a special case of a linear one.
    """
    if all(len(r.body) <= 1 for r in sub):
        return 'solve_linear', solve_linear(sub)
    try:
        return 'newton', newton(sub, tol=tol)
    except (ZeroDivisionError, OverflowError):
        return 'agenda', sub.agenda(tol=tol)


def solve_linear(sub):
    """
    Solve a (right-)linear grammar, x = b ⊕ A x, by the matrix star:
    x = A⋆ b, computed with Lehmann's algorithm.
    """
    R = sub.R
    A, b = R.chart(), R.chart()
    for r in sub:
        if len(r.body) == 0:
            b[r.head] += r.w
        else:
            [Y] = r.body
            A[r.head, Y] += r.w
    N = sorted(sub.N)
    K = sub._lehmann(N, A)
    sol = Chart(R)
    for X in N:
        for Y in N:
            sol[X] += K[X, Y] * b[Y]
    return sol
