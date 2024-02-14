from collections import defaultdict
from leftcorner.misc import format_table


class Chart:
    def __init__(self, semiring, vals=()):
        self.semiring = semiring
        self._vals = semiring.chart()
        self._vals.update(vals)
    def keys(self):
        return self._vals.keys()
    def items(self):
        return self._vals.items()
    def __iter__(self):
        return iter(self._vals)
    def __getitem__(self, k):
        return self._vals[k]
    def __setitem__(self, k, v):
        self._vals[k] = v
        return self
    def spawn(self):
        return Chart(self.semiring)
    def __add__(self, other):
        new = self.spawn()
        for k, v in self.items():
            new[k] += v
        for k, v in other.items():
            new[k] += v
        return new
    def product(self, ks):
        v = self.semiring.one
        for k in ks:
            v *= self._vals[k]
        return v
    def copy(self):
        return self.spawn() + self
    def metric(self, other):
        assert isinstance(other, Chart)
        err = 0
        for x in self._vals.keys() | other._vals.keys():
            err = max(err, self[x].metric(other[x]))
        return err
    def _repr_html_(self):
        return ('<div style="font-family: Monospace;">'
                + format_table(self.items(), headings=['key', 'value'])
                + '</div>')
    def __repr__(self):
        return repr({k: v for k,v in self.items() if v != self.semiring.zero})
