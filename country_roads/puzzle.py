from collections import defaultdict
import z3


def dict_invert(d):
    result = defaultdict(set)
    for k, v in d.items():
        result[v].add(k)
    return dict(result)


class Puzzle:
    def __init__(self, *grid, **regions):
        self.cells = set()

        # We'll want these later
        self.vars = {}
        self.solver = z3.Solver()
        self.model = None

        self.cells = {(i, j) for (j, line) in enumerate(grid) for (i, _) in enumerate(line)}

        # Work out the regions
        self.cell_region = {(i, j): grid[j][i] for (i, j) in self.cells}

        # "a" -> {(0, 0), (1, 0), ...}, "b" -> {...} ...etc
        self.regions = dict_invert(self.cell_region)
        self.region_constraints = regions

        self.dimensions = (max(x for (x, y) in self.cells) + 1,
                           max(y for (x, y) in self.cells) + 1)

    def __getitem__(self, item):
        """Something to handle variables simply"""
        if item not in self.vars:
            self.vars[item] = z3.Bool(str(item))
        return self.vars[item]

    def add(self, *constraints):
        """Add arbitrary constraints to the puzzle"""
        for c in constraints:
            self.solver.add(c)

    def solve(self):
        """Callable from a while loop"""
        if self.model is not None:
            self._reject()
        sat = self.solver.check()
        if sat != z3.sat:
            return False
        self.model = self.solver.model()
        return True

    def _reject(self):
        # Reject the solution which has this precise arrangement of variables
        r = z3.And(*(self[var] == self.model.eval(self[var]) for var in self.vars))
        n = z3.Not(r)
        self.add(n)

    def visited(self, cell):
        """Does a loop pass through this cell?"""
        if cell in self.vars:
            return self.model.eval(self[cell])
        return False

    def connected(self, cell1, cell2):
        """Is this cell connected to another in the given direction?"""
        border = tuple(sorted((cell1, cell2)))
        if border in self.vars:
            return self.model.eval(self[border])
        return False
