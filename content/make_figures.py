"""
Draw the post's derivation diagrams as SVG (adapted from the TikZ figures in
chapter 5 of the dissertation).  Run from the repo root:

    python content/make_figures.py

Writes content/images/dimension.svg, newton-step.svg, and convergence.svg.
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent / 'images'

# Colors from the dissertation (config/common.sty)
CHART = '#4617ac'        # dimension < d
CHANGE = '#CC6677'       # dimension = d
NEXT_CHART = '#882255'   # dimension <= d
NEXT_CHANGE = '#b53389'  # dimension = d+1
INK = '#333'
GRAY = '#888'
SPINE = '#fff3b0'        # TikZ yellow!30


def tint(color, p=0.5):
    "TikZ `color!50`: mix with white."
    c = color.lstrip('#')
    rgb = [int(c[i:i+2], 16) for i in (0, 2, 4)]
    return '#' + ''.join(f'{round(v*p + 255*(1-p)):02x}' for v in rgb)


KIND = {
    'LT': (CHART, '&lt;<tspan font-style="italic">d</tspan>'),
    'EQ': (CHANGE, '=<tspan font-style="italic">d</tspan>'),
    'LE': (NEXT_CHART, '≤<tspan font-style="italic">d</tspan>'),
}


class SVG:
    def __init__(self, w, h):
        self.w, self.h, self.parts = w, h, []

    def add(self, s):
        self.parts.append(s)

    def line(self, x1, y1, x2, y2, color=INK, width=1.2):
        self.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                 f'stroke="{color}" stroke-width="{width}"/>')

    def text(self, x, y, s, size=16, color=INK, anchor='middle', italic=False, extra=''):
        style = ' font-style="italic"' if italic else ''
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" fill="{color}" '
                 f'text-anchor="{anchor}"{style}{extra}>{s}</text>')

    def triangle(self, x, y, kind, w=34, h=30):
        "Subtree triangle with its apex at (x, y)."
        color, label = KIND[kind]
        self.add(f'<polygon points="{x:.1f},{y:.1f} {x-w/2:.1f},{y+h:.1f} {x+w/2:.1f},{y+h:.1f}" '
                 f'fill="{tint(color)}" stroke="{INK}" stroke-width="0.8"/>')
        self.text(x, y + h - 6, label, size=10)

    def dot(self, x, y, r=4.5):
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{INK}"/>')

    def dots(self, x, y, vertical=False, r=1.3, step=5):
        "Three small dots centered at (x, y), like TikZ's \\cdots node."
        for k in (-1, 0, 1):
            dx, dy = (0, k*step) if vertical else (k*step, 0)
            self.dot(x + dx, y + dy, r=r)

    def save(self, path, title):
        svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.w} {self.h}" '
               f'font-family="Georgia, \'Times New Roman\', serif" role="img">\n'
               f'<title>{title}</title>\n' + '\n'.join(self.parts) + '\n</svg>\n')
        path.write_text(svg)


def sub(name, i):
    return f'<tspan font-style="italic">{name}</tspan><tspan font-size="70%" baseline-shift="sub">{i}</tspan>'


def dimension_figure():
    """
    dim( X over terminals ) = 0
    dim( X → ≤d … =d <d … =d <d … ) = d+1
    dim( X → <d … =d <d … )         = d
    """
    W, rowh = 640, 150
    svg = SVG(W, 3*rowh - 10)
    gap = 64

    def tree(y0, children, x0, dots_after):
        """children: list of (label_html, kind).  As in the TikZ original,
        dots sit midway between the labels of neighboring children i, i+1
        for i in dots_after.  Returns the right edge."""
        xs = [x0 + gap*i for i in range(len(children))]
        mid = (xs[0] + xs[-1]) / 2
        svg.text(mid, y0, '<tspan font-style="italic">X</tspan>', size=17)
        for x, (label, kind) in zip(xs, children):
            svg.line(mid, y0 + 6, x, y0 + 38, width=0.9)
            svg.text(x, y0 + 54, label, size=15)
            svg.triangle(x, y0 + 62, kind)
        for i in dots_after:
            svg.dots((xs[i] + xs[i+1]) / 2, y0 + 49)
        return xs[-1]

    def bracket(x, y, h, right=False):
        "Tall parentheses around a tree, drawn as arcs."
        s = 1 if right else -1
        svg.add(f'<path d="M {x:.1f} {y:.1f} Q {x + s*12:.1f} {y + h/2:.1f} {x:.1f} {y + h:.1f}" '
                f'fill="none" stroke="{INK}" stroke-width="1.2"/>')

    # Row 1: a rule with no nonterminal children.
    y = 30
    svg.text(40, y + 52, 'dim', size=17, anchor='start')
    bracket(84, y - 14, 100)
    svg.text(130, y, '<tspan font-style="italic">X</tspan>', size=17)
    for x, a in [(106, 'a'), (154, 'b')]:
        svg.line(130, y + 6, x, y + 38, width=0.9)
        svg.text(x, y + 54, a, size=15, italic=True)
    svg.dots(130, y + 49)
    bracket(178, y - 14, 100, right=True)
    svg.text(196, y + 52, '= 0', size=17, anchor='start')
    svg.text(280, y + 52, '(no nonterminal children)', size=13, color=GRAY, anchor='start')

    # Row 2: two maximal children → d+1
    y = 30 + rowh
    kids = [(sub('Y', 1), 'LE'), (sub('Y', 'i−1'), 'LE'), (sub('Y', 'i'), 'EQ'), (sub('Y', 'i+1'), 'LT'),
            (sub('Y', 'j−1'), 'LT'), (sub('Y', 'j'), 'EQ'), (sub('Y', 'j+1'), 'LT'), (sub('Y', 'K'), 'LT')]
    svg.text(4, y + 52, 'dim', size=17, anchor='start')
    bracket(48, y - 14, 112)
    right = tree(y, kids, 76, dots_after=[0, 3, 6])
    bracket(right + 24, y - 14, 112, right=True)
    svg.text(right + 42, y + 52,
             f'= <tspan fill="{NEXT_CHANGE}"><tspan font-style="italic">d</tspan>+1</tspan>',
             size=17, anchor='start')

    # Row 3: a unique maximal child → d
    y = 30 + 2*rowh
    kids = [(sub('Y', 1), 'LT'), (sub('Y', 'k−1'), 'LT'), (sub('Y', 'k'), 'EQ'),
            (sub('Y', 'k+1'), 'LT'), (sub('Y', 'K'), 'LT')]
    svg.text(4, y + 52, 'dim', size=17, anchor='start')
    bracket(48, y - 14, 112)
    right = tree(y, kids, 76, dots_after=[0, 3])
    bracket(right + 24, y - 14, 112, right=True)
    svg.text(right + 42, y + 52,
             f'= <tspan fill="{CHANGE}" font-style="italic">d</tspan>', size=17, anchor='start')

    svg.save(OUT / 'dimension.svg', 'The dimension of a derivation')


def newton_step_figure():
    """
    A dimension d+1 derivation: a spine of rules (shaded) whose side subtrees
    have dimension ≤ d, ending in a rule that combines two =d subtrees.
    """
    W, H = 640, 330
    svg = SVG(W, H)
    sib = 38

    m1 = (250, 22)
    m2 = (250, 102)
    m3 = (250, 182)
    m4 = (250, 252)

    # shaded spine (drawn first so it sits behind)
    svg.add(f'<path d="M {m1[0]-16} {m1[1]-14} C {m1[0]-30} {m2[1]}, {m4[0]-40} {m3[1]}, {m4[0]-18} {m4[1]+12} '
            f'L {m4[0]+18} {m4[1]+12} C {m4[0]+40} {m3[1]}, {m1[0]+30} {m2[1]}, {m1[0]+16} {m1[1]-14} Z" '
            f'fill="{SPINE}" stroke="{INK}" stroke-width="0.8" stroke-dasharray="2 3"/>')

    def side(head, offsets, kind, dy=34):
        for dx in offsets:
            x = head[0] + dx
            svg.line(head[0], head[1], x, head[1] + dy, width=0.9)
            svg.triangle(x, head[1] + dy, kind, w=28, h=26)

    # levels 1–3: ≤d subtrees on either side of the spine
    for head in (m1, m2, m3):
        side(head, [-3*sib, -2*sib], 'LE')
        side(head, [2*sib, 3*sib], 'LE')
        # dots in the gap between neighboring subtrees, clear of the edges
        svg.dots(head[0] - 2.5*sib, head[1] + 34 + 10)
        svg.dots(head[0] + 2.5*sib, head[1] + 34 + 10)

    # spine edges with dots (unbounded depth)
    # (TikZ: a yellow-filled \\cdots node laid along the edge, breaking the line)
    for a, b in [(m1, m2), (m2, m3)]:
        svg.line(*a, *b)
        cy = (a[1] + b[1]) / 2
        svg.add(f'<rect x="{a[0]-5}" y="{cy-11}" width="10" height="22" fill="{SPINE}"/>')
        svg.dots(a[0], cy, vertical=True, r=1.6, step=6)
    svg.line(*m3, *m4)

    # base case: two =d subtrees, ≤d to the left of the first, <d elsewhere
    kids = ['LE', 'LE', 'EQ', 'LT', 'LT', 'EQ', 'LT', 'LT']
    xs = [m4[0] + sib*(i - 3.5) for i in range(len(kids))]
    for x, k in zip(xs, kids):
        svg.line(m4[0], m4[1], x, m4[1] + 34, width=0.9)
        svg.triangle(x, m4[1] + 34, k, w=28, h=26)
    for i in (0, 3, 6):
        svg.dots((xs[i] + xs[i+1]) / 2, m4[1] + 34 + 10)

    for head in (m1, m2, m3, m4):
        svg.dot(*head)

    # annotation
    ax, ay = 420, 40
    lines = ['These are the unknowns that we are',
             'solving for in <tspan fill="%s">𝔡′</tspan>; the other' % NEXT_CHANGE,
             'subtrees are <tspan font-style="italic">constants</tspan> from previous',
             'iterations (<tspan fill="%s">𝔪</tspan>, <tspan fill="%s">𝔡</tspan>, <tspan fill="%s">𝔪′</tspan>).'
             % (CHART, CHANGE, NEXT_CHART)]
    for i, s in enumerate(lines):
        svg.text(ax, ay + 16*i, s, size=12, color=GRAY, anchor='start')
    svg.add(f'<path d="M {ax-6} {ay+4} Q {ax-60} {ay-20} {m1[0]+20} {m1[1]-4}" fill="none" '
            f'stroke="{GRAY}" stroke-width="1" marker-end="url(#arrow)"/>')
    svg.parts.insert(0, f'<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" '
                        f'markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="{GRAY}"/>'
                        f'</marker></defs>')

    svg.save(OUT / 'newton-step.svg', 'How Newton builds dimension d+1 derivations')


def convergence_figure():
    """
    Error vs. iterations for fixpoint iteration and Newton's method on the
    Etessami–Yannakakis grammar (0.5: S → S S, 0.5: S → a), log–log axes.
    The data comes from running the code.
    """
    import math
    from leftcorner import CFG, Real
    from newton.newton import _newton

    cfg = CFG.from_string("""
    0.5: S → S S
    0.5: S → a
    """, Real)

    # Newton: iterate t (t = 0 is the initialization), plotted at t+1 solves
    newton_pts = []
    for t, (_, _, nc) in enumerate(_newton(cfg)):
        newton_pts.append((t + 1, 1 - nc['S'].score))
        if t == 39: break

    # Fixpoint iteration: sample at log-spaced iteration counts
    keep = sorted({int(round(10**(k/10))) for k in range(0, 51)})
    V, fix_pts = cfg.R.chart(), []
    for n in range(1, keep[-1] + 1):
        V = cfg._bottom_up_step(V)
        if n in keep:
            fix_pts.append((n, 1 - V['S'].score))

    W, H = 640, 380
    L, R, T, B = 74, 24, 18, 58
    svg = SVG(W, H)
    x0, x1, y0, y1 = 0, 5, -13, 0      # log10 ranges
    X = lambda n: L + (math.log10(n) - x0) / (x1 - x0) * (W - L - R)
    Y = lambda e: T + (y1 - math.log10(e)) / (y1 - y0) * (H - T - B)
    GRID, AXIS, MUTED = '#e4e0da', '#999', '#666'

    for k in range(x0, x1 + 1):
        svg.line(X(10**k), T, X(10**k), H - B, color=GRID, width=1)
        svg.text(X(10**k), H - B + 18, f'10<tspan font-size="70%" baseline-shift="super">{k}</tspan>', size=12, color=MUTED)
    for k in range(y0, y1 + 1, 2):
        svg.line(L, Y(10**k), W - R, Y(10**k), color=GRID, width=1)
        svg.text(L - 8, Y(10**k) + 4, f'10<tspan font-size="70%" baseline-shift="super">{k}</tspan>', size=12, color=MUTED, anchor='end')
    svg.line(L, H - B, W - R, H - B, color=AXIS, width=1)
    svg.line(L, T, L, H - B, color=AXIS, width=1)
    svg.text((L + W - R) / 2, H - 14, 'iterations', size=13, color=MUTED)
    svg.add(f'<text x="18" y="{(T + H - B) / 2:.1f}" font-size="13" fill="{MUTED}" text-anchor="middle" '
            f'transform="rotate(-90 18 {(T + H - B) / 2:.1f})">error</text>')

    FIX, NEWTON = '#377eb8', NEXT_CHANGE
    def path(pts, color, dash=''):
        d = ' '.join(f'{"M" if i == 0 else "L"} {X(n):.1f} {Y(e):.1f}' for i, (n, e) in enumerate(pts))
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        svg.add(f'<path d="{d}" fill="none" stroke="{color}" stroke-width="2" stroke-linejoin="round"{extra}/>')
    path(fix_pts, FIX, dash='6 4')
    path(newton_pts, NEWTON)
    # annotations (ink, not series color); the legend names the lines
    svg.text(X(1e4), Y(2e-4) - 14, 'error ≈ 2/<tspan font-style="italic">n</tspan>', size=12, color=MUTED)
    n, e = newton_pts[-1]
    svg.text(X(n) + 10, Y(e) + 4, 'error = 2<tspan font-size="70%" baseline-shift="super">−<tspan font-style="italic">n</tspan></tspan>', size=12, color=MUTED, anchor='start')

    # legend
    lx, ly = W - R - 170, T + 16
    svg.add(f'<line x1="{lx}" y1="{ly}" x2="{lx + 26}" y2="{ly}" stroke="{NEWTON}" stroke-width="2"/>')
    svg.text(lx + 34, ly + 4, 'Newton', size=12, anchor='start')
    svg.add(f'<line x1="{lx}" y1="{ly + 20}" x2="{lx + 26}" y2="{ly + 20}" stroke="{FIX}" stroke-width="2" stroke-dasharray="6 4"/>')
    svg.text(lx + 34, ly + 24, 'fixpoint iteration', size=12, anchor='start')

    svg.save(OUT / 'convergence.svg', 'Error vs. iterations: fixpoint iteration and Newton')


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    dimension_figure()
    newton_step_figure()
    convergence_figure()
