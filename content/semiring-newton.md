title: Newton's Method for Weighted Grammars
date: 2026-11-04
tags: semirings, grammars, parsing, algorithms, dynamic-programming
status: draft

<macros>
\newcommand{\Chart}{\mathsf{chart}}
\newcommand{\Change}{\mathsf{change}}
\newcommand{\NextChart}{\mathsf{chart}'}
\newcommand{\NextChange}{\mathsf{change}'}
\newcommand{\Dim}[1]{\mathrm{dim}(#1)}
\newcommand{\semione}{\mathbb{1}}
\newcommand{\semizero}{\mathbb{0}}
</macros>

A weighted context-free grammar (WCFG) assigns a semiring value to each nonterminal: the total weight $\beta(X)$ of all derivations rooted at $X$,

$$
\beta(X) = \bigoplus_{t \in \mathcal{D}(X)} w(t),
$$

where the weight $w(t)$ of a derivation $t$ is the $\otimes$-product of the weights of the rules it uses.  When the grammar is recursive, $\mathcal{D}(X)$ is infinite, and $\beta$ is the least solution to the system of fixpoint equations

$$
\beta(X) = \bigoplus_{(X \to Y_1 \cdots Y_K) \in \mathcal{R}} w(X \to Y_1 \cdots Y_K) \otimes \beta(Y_1) \otimes \cdots \otimes \beta(Y_K),
$$

with $\beta(a) = \semione$ for each terminal $a$.  Depending on the semiring, $\beta$ is the partition function of a PCFG (real semiring), the weight of the best derivation (max-times), whether $X$ derives anything at all (boolean), and so on.

The standard approach is **fixpoint iteration**: start every nonterminal at $\semizero$ and apply the equations above as an update until nothing changes.  On iteration $t$, fixpoint iteration's estimate equals the total weight of all derivations of height $\le t$.<footnote>We start with every nonterminal at $\semizero$.  From there, we build height $\le 1$ derivations from rules whose right-hand sides contain only terminals.  Each application of the update combines the values of height $\le t$ derivations by applying the rules of the grammar to derive the values of all height $\le t\!+\!1$ derivations.</footnote>  It converges in the limit, but it can be very slow.

This post describes a much faster method: **Newton's method, generalized to semirings**.  The idea is due to [Esparza, Kiefer, and Luttenberger (2007)](https://doi.org/10.1007/978-3-540-73208-2_17); the presentation below is adapted from chapter 5 of [my dissertation](https://timvieira.github.io/doc/2023-timv-dissertation.pdf), specialized here from Dyna programs to grammars.  The [code](https://github.com/timvieira/semiring-newton) works for any commutative semiring.


## Fixpoint iteration can be exponentially slow

What is interesting about Newton's method relative to fixpoint iteration is that it can sum infinitely many derivations in a single iteration.  More specifically, each iteration sums the set of derivations by increasing **dimension** (defined below) rather than by height, as in fixpoint iteration.<footnote>We use Newton's method to sum over semiring-weighted derivations; thus, our presentation will differ from that of [Esparza et al. (2007)](https://doi.org/10.1007/978-3-540-73208-2_17), which takes Newton's method as their starting point.  Newton's method for solving a fixpoint equation $\boldsymbol{x} = \boldsymbol{f}(\boldsymbol{x})$ *over the reals*, where $\boldsymbol{x} \in \mathbb{R}^D$ and $\boldsymbol{f}: \mathbb{R}^D \to \mathbb{R}^D$, is an iterative scheme with the update rule $\boldsymbol{x}^{(t+1)} \gets \boldsymbol{x}^{(t)} + (\boldsymbol{I}-\boldsymbol{J}^{(t)})^{-1} (\boldsymbol{f}(\boldsymbol{x}^{(t)}) - \boldsymbol{x}^{(t)})$, where $\boldsymbol{J}^{(t)}$ is the Jacobian matrix of $\boldsymbol{f}$ evaluated at $\boldsymbol{x}^{(t)}$.  Generalizing to the semiring setting requires retrofitting Newton's method to accommodate semirings that do not have subtraction, division, or differentiation.  For our purposes, such retrofitting would be a distraction; we refer the reader to [Esparza et al. (2007)](https://doi.org/10.1007/978-3-540-73208-2_17), [Reps et al. (2017)](https://doi.org/10.1145/3024084), and [Luttenberger (2009)](https://d-nb.info/100090086X/34), which discuss the connection.  We found the presentation in [Schlund (2016)](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf) the clearest.</footnote>

[Etessami and Yannakakis (2009)](https://doi.org/10.1145/1462153.1462154) showed that fixpoint iteration can converge exponentially slower than Newton's method.  Consider the following grammar, based on their Theorem 3.2:

```text
0.5: S → S S
0.5: S → a
```

Its fixpoint equation is $x = \frac{1}{2} + \frac{1}{2} x^2$, which has a single solution, $\beta(\mathrm{S}) = 1$.<footnote>$\frac{1}{2} x^2 - x + \frac{1}{2} = 0$, which, by the quadratic formula with $a = \frac{1}{2}$, $b = -1$, $c = \frac{1}{2}$, has the solution set $\{1\}$.</footnote>  Fixpoint iteration requires roughly $2^k$ iterations to gain $k$ bits of precision, whereas Newton's method gains one bit of precision per iteration.  Here is what that looks like in practice, where the error is $1 - \text{estimate}$:

| method | iterations | error |
|:-------|-----------:|------:|
| fixpoint iteration | 10 | $1.4 \times 10^{-1}$ |
| fixpoint iteration | 1,000 | $2.0 \times 10^{-3}$ |
| fixpoint iteration | 100,000 | $2.0 \times 10^{-5}$ |
| Newton | 10 | $4.9 \times 10^{-4}$ |
| Newton | 39 | $9.1 \times 10^{-13}$ |

Fixpoint iteration's error after $n$ iterations is about $2/n$; Newton's error after initialization plus $n$ iterations is exactly $2^{-(n+1)}$.  This grammar is a worst case for Newton's method (it is *critical*: the expected size of a tree is infinite).  On a subcritical grammar like `0.25: S → S S`, `0.75: S → a`, Newton's method converges *quadratically*: the errors on successive iterations are $0.25$, $0.025$, $3 \times 10^{-4}$, $5 \times 10^{-8}$, $10^{-15}$.


## The dimension of a derivation

**Definition.** The **dimension** $\Dim{t}$ of a derivation $t$ is defined inductively.  Suppose $t$ is rooted at a rule $X \to Y_1 \cdots Y_K$, and let $t_1, \ldots, t_m$ be the subderivations of the *nonterminal* children (terminal children are ignored).

* If $m = 0$: $\Dim{t} \overset{\text{def}}{=} 0$.
* If $m \ge 1$: let $d = \max(\Dim{t_1}, \ldots, \Dim{t_m})$.  If the argmax is unique (i.e., no ties for the max), $\Dim{t} \overset{\text{def}}{=} d$.  Otherwise, $\Dim{t} \overset{\text{def}}{=} d+1$.

In words: a node's dimension goes up only where two children of maximal dimension meet; a chain of nodes with a single maximal child keeps the same dimension.<footnote>This is a variant of the Horton–Strahler number of a tree.  See [Esparza, Luttenberger, and Schlund (2014)](https://archive.model.in.tum.de/um/bibdb/esparza/lata2014.pdf) for a history of Strahler numbers and their connection to Newton's method.</footnote>

The dimension of a derivation is always $\le$ its height, but it is often $\ll$.  The set of derivations with dimension $d$ can be infinite.  In contrast, the set of derivations with fixed height is finite.  For example, every derivation of a linear grammar (at most one nonterminal per right-hand side), such as the geometric series `0.5: S → S a`, `1: S → b`, has dimension $0$.  What is remarkable about the set of derivations with dimension $= d\!+\!1$ is that there is an efficient *linear* structure relating it to the sets of derivations with dimensions $\le d$, $= d$, and $< d$.  This allows us to grow the set of derivations we have summed over much more quickly using a linear solver.


## The algorithm

Newton's method tracks two charts, much like semi-naive forward chaining: $\Chart$ holds the total weight of the dimension $< d$ derivations of each nonterminal, and $\Change$ holds the total weight of the dimension $= d$ derivations.  Their sum $\NextChart = \Chart \oplus \Change$ holds the dimension $\le d$ derivations.  To efficiently determine the values of all $= d\!+\!1$ derivations, Newton's method solves a **linearized grammar** for $\NextChange$:

**Initialization.**  $\Chart \gets \semizero$, and $\Change$ is the solution of the linear grammar made up of the rules with at most one nonterminal on the right-hand side.  These are exactly the dimension-$0$ derivations.

**Iteration.**  Given $\Chart$ (dimension $\lt d$) and $\Change$ (dimension $=d$), let $\NextChart = \Chart \oplus \Change$, and solve the following equations for $\NextChange$.  For each rule $X \to Y_1 \cdots Y_K$ with weight $w$:

* *Base case:* combine at least two derivations of dimension $=d$.  For each pair of positions $i < j$,
$$
\begin{aligned} \NextChange[X] \mathrel{\oplus}= w &\otimes \NextChart[Y_{\lt i}] \otimes \Change[Y_i] \\ &\otimes \Chart[Y_{i+1:j}] \otimes \Change[Y_j] \otimes \Chart[Y_{\gt j}] \end{aligned}
$$
Here $i$ and $j$ are the last two children of dimension $=d$, so every derivation is counted once.

* *Recursive case:* derive $=d\!+\!1$ derivations by combining one $=d\!+\!1$ derivation with $\le d$ derivations.  For each position $k$ where $Y_k$ is a nonterminal,
$$
\NextChange[X] \mathrel{\oplus}= w \otimes \NextChart[Y_{\lt k}] \otimes \NextChange[Y_k] \otimes \NextChart[Y_{\gt k}]
$$

Here $\Chart[Y_{i:j}]$ is shorthand for the product $\Chart[Y_i] \otimes \cdots \otimes \Chart[Y_{j-1}]$, and terminals always have value $\semione$ in $\Chart$ and $\NextChart$ and $\semizero$ in $\Change$.  Then set $\Chart \gets \NextChart$, $\Change \gets \NextChange$, and repeat until $\Chart$ stops changing.

**Why it works.**  On iteration $d$, $\Chart$ is the total weight of derivations of dimension $< d$, and $\Change$ is the total weight of derivations of dimension $= d$.  To see why, we argue that $\NextChange$ is precisely the sum of dimension $=d\!+\!1$ derivations.  According to the definition, to create a dimension $\ge d\!+\!1$ derivation, we need to combine at least two $=d$ derivations.  That is why the base case combines two $=d$ derivations (with $< d$ derivations to their right and $\le d$ derivations to their left); this creates a subderivation with dimension equal to $d\!+\!1$.  Now, because all subderivations that can combine along the spine (the path up to the root) of the new derivation have dimension $\le d$, the new derivation has dimension $d\!+\!1$; this is the recursive case.  To ensure that the enumeration of $= d\!+\!1$ derivations is exhaustive, the linearized grammar includes every rule that can combine the $\le d$ subderivations and the base case of at least two $= d$ subderivations.  The linearized grammar is a compact encoding of the value of this potentially infinite set of $=d\!+\!1$ derivations.  Finally, $\NextChart$ is the sum of $\Chart$ and $\Change$, so at iteration $d$, $\Chart$ is the total value of all derivations of dimension $< d$.

Notice that the recursive case contains a single unknown, $\NextChange[Y_k]$, and everything else is a constant from earlier iterations.  So each iteration of Newton's method solves a *linear* system, and every derivation of the original grammar is summed on the iteration equal to its dimension.  Over the reals, this is ordinary Newton's method: the coefficient of $\NextChange[Y_k]$ in the recursive case is the partial derivative $\partial f_X / \partial x_{Y_k}$ evaluated at $\NextChart$, and the base case equals $\boldsymbol{f}(\NextChart) \ominus \NextChart$.<footnote>The base case collects the derivations whose children all have dimension $\le d$ but which themselves have dimension $d\!+\!1$, which is exactly the part of $\boldsymbol{f}(\NextChart)$ not already in $\NextChart$.  The [tests](https://github.com/timvieira/semiring-newton/blob/master/tests/test_post.py) check that the iterates match textbook Newton's method on $x - f(x) = 0$ started from $x = 0$.</footnote>


## Solving the linear subproblems

The linearized grammar has the form $\boldsymbol{x} = \boldsymbol{b} \oplus \boldsymbol{A}\, \boldsymbol{x}$ where $\boldsymbol{A} \in \mathbb{K}^{N \times N}$ and $\boldsymbol{b} \in \mathbb{K}^{N}$, provided that we can move each unknown to the right-hand end of its rule.  This is where we need **commutativity**: in the recursive case, the unknown $\NextChange[Y_k]$ sits between the constants $\NextChart[Y_{\lt k}]$ and $\NextChart[Y_{\gt k}]$, and we can only rewrite it as $\boldsymbol{A}_{X, Y_k} \otimes \NextChange[Y_k]$ with $\boldsymbol{A}_{X, Y_k} = w \otimes \NextChart[Y_{\lt k}] \otimes \NextChart[Y_{\gt k}]$ if we are allowed to permute the product.

The solution of a right-linear system is given by the matrix star operation $\boldsymbol{x} = \boldsymbol{A}^* \, \boldsymbol{b}$, where $\boldsymbol{A}^* \overset{\text{def}}{=} \bigoplus_{i=0}^\infty \boldsymbol{A}^i$.  A useful perspective on the matrix star is that it computes the total weight of paths in a weighted directed graph: if $\boldsymbol{A}$ is the weighted adjacency matrix of a graph, then $\boldsymbol{A}_{ik}$ is the total weight of all paths of length $1$ from $i$ to $k$, $(\boldsymbol{A}\, \boldsymbol{A})_{ik}$ is the total weight of the paths of length $2$, and so on.  Paths may be regarded as a restricted family of right-recursive derivations; here they are the spines of the dimension $d\!+\!1$ derivations.  We compute $\boldsymbol{A}^*$ with [Lehmann's (1977)](https://doi.org/10.1016/0304-3975(77)90056-1) algorithm, which runs in $\mathcal{O}(|N|^3)$ time.  Special cases of this algorithm for specific applications are well known, e.g.,

* matrix inversion (Gauss–Jordan elimination)<footnote>[Althoen and McLaughlin (1987)](http://www.jstor.org/stable/2322413) provide an interesting historical overview of the Gauss–Jordan elimination algorithm.</footnote>
* all-pairs shortest path ([Floyd, 1962](https://doi.org/10.1145/367766.368168); [Warshall, 1962](https://doi.org/10.1145/321105.321107); [Roy, 1959](https://gallica.bnf.fr/ark:/12148/bpt6k3201c/f222.image))
* finite-state automaton to regular expression conversion ([Kleene, 1956](https://apps.dtic.mil/sti/pdfs/ADA596138.pdf))
* transitive closure ([Warshall, 1962](https://doi.org/10.1145/321105.321107))

These problems were unified into what are often called **algebraic path problems** ([Lehmann, 1977](https://doi.org/10.1016/0304-3975(77)90056-1); [Tarjan, 1981](https://doi.org/10.1145/322261.322272)).  Unifying these problems was just the (closed) semiring abstraction at work again!  A choice of semiring, with the same underlying algorithm that sums over all paths in a graph, solves all the above problems and many others.

**Without commutativity.**  Unfortunately, not all semirings are commutative, so permuting the right-hand side is not always allowed.  In general, each Newton step produces a *linear* grammar, not a right-linear one, and linear grammars are strictly more expressive.  The following grammar over the semiring of formal languages is linear but not right-linear:

```text
S → a S b
S → ε
```

Its solution is $\beta(\mathrm{S}) = \{ a^n b^n \mid n \in \mathbb{N} \}$, which is not a regular language; thus, it cannot be expressed as a finite expression involving $\otimes$, $\oplus$, and $(\cdot)^*$.  Unlike the commutative examples, we cannot transform this grammar into a right-linear one, so the right-linear solver cannot solve it; we would need a general linear solver.  Other tractable cases are discussed in the literature (e.g., [Esparza et al., 2007](https://doi.org/10.1007/978-3-540-73208-2_17); [Schlund, 2016](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf); [Reps et al., 2017](https://doi.org/10.1145/3024084)).  We note that fixpoint iteration is always available for (approximately) solving the linear subproblems; however, fixpoint iteration may not converge quickly (or at all).


## Code

The [implementation](https://github.com/timvieira/semiring-newton/blob/master/newton/newton.py) takes a grammar from the [`leftcorner`](https://github.com/rycolab/left-corner) package, which provides a WCFG class, several semirings, and Lehmann's algorithm (`cfg._lehmann`).  The main loop mirrors the description above:

```python
def _newton(self):
    # initial chart is empty, except for terminals
    chart = Chart(self.R, {x: self.R.one for x in self.V})
    # initialize with dimension-0 derivations
    change = linearize(self, chart, chart, chart, init=True)
    while True:
        next_chart = chart + change.sol
        yield (chart, change, next_chart)
        change = linearize(self, chart, change.sol, next_chart)
        chart = next_chart
```

The linearization builds the matrix $\boldsymbol{A}$ and vector $\boldsymbol{b}$.  The line `A[r.head, ys[k]] += ...` is where commutativity is used: the constant to the right of the unknown is folded into its coefficient.

```python
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
```

During initialization, $\NextChart$ is zero on every nonterminal, so the matrix $\boldsymbol{A}$ only picks up rules with a single nonterminal, which matches the initialization above.  `Change.sol` computes $\boldsymbol{A}^* \boldsymbol{b}$.

Using it:

```python
from leftcorner import CFG, Real, MaxTimes
from newton import newton

cfg = CFG.from_string("""
0.5: S → S S
0.5: S → a
""", Real)

newton(cfg)            # {'a': 1, 'S': 0.9999999999990905}  (39 iterations)
cfg.naive_bottom_up()  # fixpoint iteration: needs ~2^k iterations for k bits
```

The same code runs in any commutative semiring.  Here is a small grammar with prepositional-phrase attachment in the max-times (Viterbi) semiring:

```python
cfg = CFG.from_string("""
1.0: S → NP VP
0.4: NP → NP PP
0.6: NP → n
0.7: VP → v NP
0.3: VP → VP PP
1.0: PP → p NP
""", MaxTimes)

newton(cfg)   # S: 0.252, NP: 0.6, VP: 0.42, PP: 0.6  (exact after one iteration)
```

In commutative *idempotent* semirings like max-times, Newton's method reaches the exact solution after at most $|N|$ iterations ([Esparza, Kiefer, and Luttenberger, 2010](https://doi.org/10.1145/1857914.1857917)).


## Notes

* **Strongly connected components.**  As noted in other work on Newton's method (e.g., [Schlund, 2016](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf)), decomposing the grammar into strongly connected components and solving them bottom-up can speed the algorithm up considerably, both for the Newton iterations and for the $\mathcal{O}(|N|^3)$ linear solver.  The implementation does not do this yet.
* **Speed–accuracy tradeoff.**  Each Newton iteration costs a call to the linear solver, so it is much more expensive than a fixpoint iteration.  Often fixpoint iteration can reach a tolerable level of accuracy faster than the exact linear solver.<footnote>The convergence rate of fixpoint iteration depends on the properties of the $\boldsymbol{A}$ matrix.  In the case of the real semiring, we can bound the number of iterations to reach a given error tolerance in terms of the spectral radius of $\boldsymbol{A}$.</footnote>


## References

* Javier Esparza, Stefan Kiefer, and Michael Luttenberger. [An Extension of Newton's Method to ω-Continuous Semirings](https://doi.org/10.1007/978-3-540-73208-2_17). DLT 2007.
* Javier Esparza, Stefan Kiefer, and Michael Luttenberger. [Newtonian Program Analysis](https://doi.org/10.1145/1857914.1857917). JACM 2010.
* Kousha Etessami and Mihalis Yannakakis. [Recursive Markov Chains, Stochastic Grammars, and Monotone Systems of Nonlinear Equations](https://doi.org/10.1145/1462153.1462154). JACM 2009.
* Michael Luttenberger. [Solving Polynomial Systems on Semirings: A Generalization of Newton's Method](https://d-nb.info/100090086X/34). PhD thesis, 2009.
* Maximilian Schlund. [Algebraic Systems of Fixpoint Equations over Semirings: Theory and Applications](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf). PhD thesis, 2016.
* Thomas Reps, Emma Turetsky, and Prathmesh Prabhu. [Newtonian Program Analysis via Tensor Product](https://doi.org/10.1145/3024084). TOPLAS 2017.
* Daniel J. Lehmann. [Algebraic Structures for Transitive Closure](https://doi.org/10.1016/0304-3975(77)90056-1). Theoretical Computer Science, 1977.
* Robert E. Tarjan. [A Unified Approach to Path Problems](https://doi.org/10.1145/322261.322272). JACM 1981.
* Mark-Jan Nederhof and Giorgio Satta. [Computing Partition Functions of PCFGs](https://mjn.host.cs.st-andrews.ac.uk/publications/2008d.pdf). Research on Language and Computation, 2008.
* Tim Vieira. [Automating the Analysis and Improvement of Dynamic Programming Algorithms with Applications to Natural Language Processing](https://timvieira.github.io/doc/2023-timv-dissertation.pdf). PhD thesis, 2023.
