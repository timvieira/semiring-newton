title: Weighted Grammars as Algebraic Systems
date: 2026-11-05
tags: semirings, grammars, parsing, algorithms, dynamic-programming
status: draft


<macros>
\renewcommand{\otimes}{\mathbin{\circ}}
\newcommand{\Chart}{{\color{#4617ac}{\mathfrak{m}}}}
\newcommand{\Change}{{\color{#CC6677}{\mathfrak{d}}}}
\newcommand{\NextChart}{{\color{#882255}{\mathfrak{m}'}}}
\newcommand{\NextChange}{{\color{#b53389}{\mathfrak{d}'}}}
\newcommand{\Notation}{\color{#332288}}
\newcommand{\DimName}{{\color{#332288}{\mathsf{dim}}}}
\newcommand{\Dim}[1]{\DimName(#1)}
\newcommand{\HeightName}{{\color{#332288}{\mathsf{height}}}}
\newcommand{\Newton}{{\color{#332288}{\mathsf{newton}}}}
\newcommand{\NewtonStep}{{\color{#332288}{\mathsf{newton\_step}}}}
\newcommand{\NewtonInit}{{\color{#332288}{\mathsf{newton\_init}}}}
\newcommand{\SolveName}{{\color{#332288}{\mathsf{solve}}}}
\newcommand{\BestSolve}{{\color{#332288}{\mathsf{best\_solve}}}}
\newcommand{\SccName}{{\color{#332288}{\mathsf{scc}}}}
\newcommand{\SolveLinearName}{{\color{#332288}{\mathsf{solve\_linear}}}}
\newcommand{\solveLinear}[1]{\SolveLinearName(#1)}
\newcommand{\semione}{{\color{magenta}{\underline{1}}}}
\newcommand{\semizero}{{\color{magenta}{\underline{0}}}}
\newcommand{\llbracket}{[\![}
\newcommand{\rrbracket}{]\!]}
\newcommand{\sem}[1]{{\color{magenta}{\llbracket}}#1{\color{magenta}{\rrbracket}}}
\newcommand{\deriv}{\boldsymbol{\delta}}
\newcommand{\w}{{\color{magenta}{w}}}
\newcommand{\val}{{\color{magenta}{v}}}
\newcommand{\AddRule}{\textbf{add } }
\newcommand{\Values}{{\color{magenta}{\mathbb{V}}}}
\newcommand{\Series}{\Values\langle\!\langle \Sigma^* \rangle\!\rangle}
\newcommand{\KleeneStar}{{\color{#332288}{\star}}}
\newcommand{\kleene}[1]{#1^{\KleeneStar}}
\newcommand{\dotimes}{\mathbin{\color[rgb]{0,0,.5}{\circ}}}
\newcommand{\doplus}{\mathbin{\color[rgb]{0,0,.5}{\oplus}}}
\newcommand{\dopluseq}{\mathrel{\color[rgb]{0,0,.5}{\oplus\mkern-2mu\texttt{=}}}}
\newcommand{\dotimesdots}{\dotimes{\color[rgb]{0,0,.5}{\cdots}}\dotimes}
\newcommand{\NewGrammar}{\{\,\}}
\newcommand{\dLT}{{\color{#4617ac}{\lt\!d}}}
\newcommand{\dEQ}{{\color{#CC6677}{=\!d}}}
\newcommand{\dLE}{{\color{#882255}{\le\!d}}}
\newcommand{\dPP}{{\color{#b53389}{=\!d\!+\!1}}}
\newcommand{\cPP}{\color{#b53389}}
\newcommand{\Comment}{\color{grey}{\triangleright}\ \color{grey}}
</macros>

<style>
.theorem { border-left: 3px solid #c9c2b8; padding: 0.6em 1em; margin: 1.2em 0; background: #fbf8f3; }
.theorem > :first-child { margin-top: 0; }
.theorem > :last-child { margin-bottom: 0; }
.pseudocode mjx-container[display="true"] { text-align: left !important; margin-left: 0.5em !important; font-size: 90% !important; overflow-x: auto; overflow-y: hidden; }
</style>

<div style="background: #fff3cd; border-left: 4px solid #ffc107; padding: 12px 16px; margin-bottom: 1.5em; border-radius: 4px; font-size: 0.95em;"><p style="margin: 0;"><strong>Draft</strong> — This article is a work in progress. Content may change.</p></div>

<div class="theorem" markdown="1">
**Solving weighted grammars** is a three-part series adapted from chapter 5 of [my dissertation](https://timvieira.github.io/doc/2023-timv-dissertation.pdf).  This is part 1.

1. **Weighted Grammars as Algebraic Systems**: the problem, and why fixpoint iteration can be slow
2. [Solving Linear Grammars Exactly](../solving-linear-grammars-exactly/): an exact solver for (right-)linear grammars via the matrix star
3. [Newton's Method for Weighted Grammars](../newtons-method-for-weighted-grammars/): Newton's method, a hybrid solver that splits the grammar into strongly connected components, and code

Background: [semirings](/blog/semirings-a-powerful-abstraction-for-dynamic-programming/).  Proofs, side examples, and background are tucked into collapsible blocks (▸) for readers who want more depth.
</div>

A weighted context-free grammar $\mathcal{G}$ over a semiring $\Values$ has nonterminals $\mathcal{N}$, terminals $\Sigma$, and a set of rules $X \xrightarrow{\w} Y_1 \cdots Y_K$, each of which rewrites a nonterminal $X \in \mathcal{N}$ into a sequence of symbols $Y_1 \cdots Y_K \in (\mathcal{N} \cup \Sigma)^*$ with a weight $\w \in \Values$.  The grammar assigns a value $\sem{X} \in \Values$ to each nonterminal $X$: the total weight of all derivations $\deriv$ rooted at $X$,

$$
\sem{X} = \bigoplus_{\deriv \in \mathcal{D}(X)} \w(\deriv),
$$

where the weight $\w(\deriv)$ of a derivation is the $\otimes$-product of the weights of the rules it uses.  When the grammar is recursive, $\mathcal{D}(X)$ is infinite, and $\sem{\cdot}$ is the least solution to the system of fixpoint equations

$$
\sem{X} = \bigoplus_{(X \xrightarrow{\w} Y_1 \cdots Y_K) \in \mathcal{G}} \w \otimes \sem{Y_1} \otimes \cdots \otimes \sem{Y_K},
$$

with $\sem{a} = \semione$ for each terminal $a \in \Sigma$.  Note that $\sem{X}$ ignores *which strings* the derivations yield: it sums the weights of all derivations, whatever their yield.  This total weight (sometimes called the treesum or, for a PCFG, the partition function) is the quantity the algorithms in this series compute.

## Grammars are algebraic systems

The fixpoint equations of a grammar are an instance of a classical object: an **algebraic system** of equations over a semiring (Chomsky and Schützenberger, 1963; [Esparza et al., 2007](https://doi.org/10.1007/978-3-540-73208-2_17); [Schlund, 2016](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf)).  Fix a semiring $\mathbb{S}$ and a vector of $\mathbb{S}$-valued variables $\boldsymbol{x} = (x_1, \ldots, x_n)$.  A *monomial* is a finite product of constants from $\mathbb{S}$ and variables, such as $c \otimes x_1 \otimes x_2$; a *polynomial* is a finite sum of monomials; and an algebraic system is a system of equations

$$
\boldsymbol{x} = \boldsymbol{f}(\boldsymbol{x}),
$$

where each component $f_i$ is a polynomial.  To turn a grammar into an algebraic system, we treat the value $\sem{X}$ of each nonterminal $X$ as an unknown.  (The nonterminal $X$ is a symbol; $\sem{X}$ stands for its semiring value.)  The grammar problem and the algebraic problem are essentially the same problem, but we have to be careful about *which* semiring $\mathbb{S}$ the system lives in, because there are two natural choices.  They differ in what happens to the terminals:

* **Weights only, $\mathbb{S} = \Values$.**  Each terminal is replaced by $\semione$, so it drops out of the monomial.  The least solution is the total weight $\sem{X}$ defined above.
* **Weighted languages, $\mathbb{S} = \Series$.**  Here $\Series$ is the semiring of *weighted languages* (formal power series), i.e., functions $L : \Sigma^* \to \Values$, with $\oplus$ taken pointwise and $\otimes$ given by concatenation, $(L \otimes L')(s) = \bigoplus_{s = u\,v} L(u) \otimes L'(v)$.  A rule weight $\w$ becomes the series that gives the empty string weight $\w$, and a terminal $a$ becomes the series that gives the one-symbol string $a$ weight $\semione$.  The least solution $L_X$ assigns each string $s$ the total weight of the derivations of $X$ that yield $s$.

| grammar | system over $\Values$ (weights only) | system over $\Series$ (weighted languages) |
|:--------|:-------------------------------------|:-------------------------------------------|
| nonterminal $X$ | variable $\sem{X}$ | variable $L_X$ |
| terminal $a$ | $\semione$ (drops out) | the series $a$ (string $a$ with weight $\semione$) |
| rule $X \xrightarrow{\w} Y_1 \cdots Y_K$ | monomial $\w \otimes \sem{Y_1} \otimes \cdots \otimes \sem{Y_K}$ in $f_X$, where $\sem{a} = \semione$ for a terminal | monomial $\w\, \hat{Y}_1 \cdots \hat{Y}_K$ in $f_X$, in order, where $\hat{Y} = L_Y$ for a nonterminal and $\hat{a} = a$ for a terminal |
| derivation $\deriv$ with yield $s$ | the term $\w(\deriv)$ | the term $\w(\deriv)\, s$ |
| least solution | $\sem{X} \in \Values$ | $L_X \in \Series$ |

The two are related by forgetting the strings: $\sem{X} = \bigoplus_{s \in \Sigma^*} L_X(s)$, i.e., the image of $L_X$ under the homomorphism that sends every terminal to $\semione$.  When $\Values$ is the boolean semiring, a weighted language is just a formal language, $L_X$ is the language generated by $X$, and the least-solution characterization is the observation of Chomsky and Schützenberger.

This distinction matters for the algorithms below.  Even when $\Values$ is commutative, $\Series$ is *not* (concatenation does not commute: $a\,b \ne b\,a$).  The algorithms in this series assume a commutative semiring, so they solve the weights-only system for $\sem{\cdot}$; they do not compute the weighted language $L_X$ ([part 2](../solving-linear-grammars-exactly/) has a non-commutative example that the right-linear solver cannot handle).

The fixpoint equations are *underspecified*: they provide necessary, but not sufficient, conditions for a solution to equal the potentially infinite sum over derivations.

<details class="derivation" markdown="1">
<summary>Example: a grammar whose equations have two solutions</summary>

<div class="theorem" markdown="1">
**Example.** The following grammar encodes the Catalan series: $\sem{X} = c + c^2 + 2\,c^3 + 5\,c^4 + 14\,c^5 + 42\,c^6 + \cdots$.

$$
\begin{aligned} X &\xrightarrow{1} X\,X \\ X &\xrightarrow{c} a \end{aligned}
$$

Its algebraic system is $\sem{X} = \sem{X} \otimes \sem{X} \oplus c$.  Over the real semiring, the system admits *two* solutions: rearranging gives $\sem{X}^2 - \sem{X} + c = 0$, so $\sem{X} \in \frac{1 \pm \sqrt{1 - 4\,c}}{2}$ by the quadratic formula.  Assuming $0 \le c \le \frac{1}{4}$, the smaller solution $\frac{1 - \sqrt{1 - 4\,c}}{2}$ corresponds to the sum over derivations.  The larger solution $\frac{1 + \sqrt{1 - 4\,c}}{2}$ is a fixpoint, but it is not equal to the sum over derivations.
</div>

</details>

The sum over derivations is the *least* solution.  In $\omega$-continuous semirings (where all the infinite sums we need are well-defined), Kleene's fixed-point theorem says that the least solution is the limit of the sequence $\boldsymbol{0}, \boldsymbol{f}(\boldsymbol{0}), \boldsymbol{f}(\boldsymbol{f}(\boldsymbol{0})), \ldots$.  Computing that sequence is **fixpoint iteration**, which initializes every variable to $\semizero$ and repeatedly applies the equations above as an update until it converges.  Newton's method, too, is most naturally stated on the algebraic system: it is Newton's method for solving $\boldsymbol{x} = \boldsymbol{f}(\boldsymbol{x})$, retrofitted to semirings.  We stay with the grammar view below because it lets us talk about derivations directly.

<div class="theorem" markdown="1">
**Proposition.** The estimate at time $t$ given by fixpoint iteration equals the total value of all derivations of height $\le t$.
</div>

<details class="derivation" markdown="1">
<summary>Proof (sketch)</summary>

We start with every nonterminal at $\semizero$.  From there, we build height $\le 1$ derivations from the rules whose right-hand sides contain only terminals.  From there, each application of the update combines the values of height $\le t$ derivations by applying the rules of the grammar to derive the values of all height $\le t\!+\!1$ derivations.<footnote>This is a form of dynamic programming: the estimate at time $t$ is a memo table for a version of the computation, which makes the height $t$ an argument to break cycles.</footnote> $\square$

</details>

Assuming the sum is convergent, fixpoint iteration will diligently compute it (up to each height) until every height has been covered; thus, it converges in the limit to $\sem{\cdot}$.

## Fixpoint iteration can be slow

[Etessami and Yannakakis (2009)](https://doi.org/10.1145/1462153.1462154) showed that fixpoint iteration could converge exponentially slower than Newton's method.

<div class="theorem" markdown="1">
**Example.** Consider the following grammar based on [Etessami and Yannakakis (2009, Theorem 3.2)](https://doi.org/10.1145/1462153.1462154).  This grammar has a single fixpoint $\sem{\mathrm{S}} = 1$.<footnote>$\frac{1}{2} x^2 - x + \frac{1}{2} = 0$, which, by the quadratic formula ($a\,x^2+b\,x+c=0 \iff x=\frac{-b\pm\sqrt{b^2-4\,a\,c}}{2a}$ with $a \mapsto \frac{1}{2}$, $b \mapsto -1$, $c \mapsto \frac{1}{2}$), has solutions $\{1\}$.</footnote>

$$
\begin{aligned} S &\xrightarrow{0.5} S\,S \\ S &\xrightarrow{0.5} a \end{aligned}
$$

Etessami and Yannakakis show that fixpoint iteration is exponentially slower than Newton's method in this example.  Specifically, fixpoint iteration requires roughly $2^k$ iterations to gain $k$ bits of precision, whereas Newton's method gains one bit of precision per iteration.  The plot below shows this using the code from [part 3](../newtons-method-for-weighted-grammars/): the error of fixpoint iteration after $n$ iterations is about $2/n$, whereas the error of $\Newton$ after $n$ iterations is $2^{-n}$.
</div>

<figure>
<img src="../images/convergence.svg" alt="Log-log plot of error versus iterations on the grammar 0.5: S → S S, 0.5: S → a. Fixpoint iteration's error falls slowly, like 2/n, reaching about 2e-5 after 100,000 iterations; Newton's error falls like 2^-n, reaching about 1e-12 after 40 iterations." style="width:100%">
</figure>

## What comes next

Fixpoint iteration sums derivations by height, one level at a time.  The rest of the series builds faster solvers.  [Part 2](../solving-linear-grammars-exactly/) solves *linear* grammars exactly, in closed form, with the matrix star operation.  [Part 3](../newtons-method-for-weighted-grammars/) uses that solver inside Newton's method, which sums derivations by *dimension* instead of height and gains one bit of precision per iteration on the example above, and then combines everything into a hybrid solver.

## References

* Javier Esparza, Stefan Kiefer, and Michael Luttenberger. [An Extension of Newton's Method to ω-Continuous Semirings](https://doi.org/10.1007/978-3-540-73208-2_17). DLT 2007.
* Kousha Etessami and Mihalis Yannakakis. [Recursive Markov Chains, Stochastic Grammars, and Monotone Systems of Nonlinear Equations](https://doi.org/10.1145/1462153.1462154). JACM 2009.
* Maximilian Schlund. [Algebraic Systems of Fixpoint Equations over Semirings: Theory and Applications](https://mediatum.ub.tum.de/doc/1273784/1273784.pdf). PhD thesis, 2016.
* Noam Chomsky and Marcel-Paul Schützenberger. The Algebraic Theory of Context-Free Languages. In *Computer Programming and Formal Systems*, North-Holland, 1963.
* Tim Vieira. [Automating the Analysis and Improvement of Dynamic Programming Algorithms with Applications to Natural Language Processing](https://timvieira.github.io/doc/2023-timv-dissertation.pdf). PhD thesis, 2023.
