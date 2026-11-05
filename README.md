Solve fixpoint systems of equations over commutative semirings.

## Newton's Method

<img src="docs/images/newton-convergence.png" align="right" width="200">

This package implements a solver based on Newton's method for solving fixpoint systems of equations, suitably generalized beyond real numbers to operate over semirings! The papers below are excellent examples of why Newton's method is awesome for solving the kinds of cyclical systems of equations that we encounter in probabilistic inference problems and other domains. Our implementation assumes that the semiring is commutative.

`newton(cfg)` runs Newton's method; `solve(cfg)` is a hybrid solver that splits the grammar into strongly connected components and solves each one, in topological order, with the best applicable method (exact linear solver, then Newton, then fixpoint iteration).

### References

* Details and discussion of semiring Newton's algorithm are in chapter 5 of [Tim Vieira's dissertation](https://timvieira.github.io/doc/2023-timv-dissertation.pdf)

* [An Extension of Newton's Method to ω-Continuous Semirings](https://link.springer.com/chapter/10.1007/978-3-540-73208-2_17). Javier Esparza, Stefan Kiefer, Michael Luttenberger

* [Recursive Markov chains, stochastic grammars, and monotone systems of nonlinear equations](https://dl.acm.org/doi/10.1145/1462153.1462154). Kousha Etessami, Mihalis Yannakakis

* [Computing partition functions of PCFGs](https://mjn.host.cs.st-andrews.ac.uk/publications/2008d.pdf). Mark-Jan Nederhof, Giorgio Satta

* [Exact Recursive Probabilistic Programming](https://arxiv.org/abs/2210.01206). David Chiang, Colin McDonald, Chung-chieh Shan


## Blog posts (draft series)

`content/` holds a draft series, adapted from chapter 5 of the dissertation (with background from the dissertation and from the left-corner paper, arXiv 2311.16258), served by GitHub Pages from `docs/`:

- Background: `semirings-a-powerful-abstraction-for-dynamic-programming.md`
- Background: `weighted-context-free-grammars.md` (figures: `content/wcfg_figures.py`)
1. `weighted-grammars-as-algebraic-systems.md`: the problem, and why fixpoint iteration can be slow
2. `solving-linear-grammars-exactly.md`: the right-linear solver (matrix star)
3. `newtons-method-for-weighted-grammars.md`: Newton's method, the hybrid SCC solver, and code
- Sequel: `from-weighted-grammars-to-dyna-programs.md` (embeds cells from `content/dyna-tutorial.ipynb`, a copy of dyna-pi's `docs/Demo.ipynb`)

Build them with the `blog` CLI from [timvieira/blog](https://github.com/timvieira/blog) (`blog build` or `blog dev`; output goes to `docs/`).  `content/make_figures.py` draws the series figures, and `tests/test_post.py` checks the claims the posts make.
