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

        # Set up the variables for constraint satisfaction
        for (x, y) in self.cells:
            # Is this cell part of the loop?
            _ = self[(x, y)]

            # Is this cell connected to its neighbours?
            if (conn := self.connection((x, y), (x + 1, y))) is not None:
                _ = self[conn]

            if (conn := self.connection((x, y), (x, y + 1))) is not None:
                _ = self[conn]

    def _name(self, item):
        (a, b) = item
        if isinstance(a, tuple) and isinstance(b, tuple):
            (a1, a2) = a
            (b1, b2) = b
            return "B_{}_{}__{}_{}".format(a1, a2, b1, b2)
        elif isinstance(a, int) and isinstance(b, int):
            return "C_{}_{}".format(a, b)
        else:
            return "unknown"

    def __getitem__(self, item):
        """Something to handle variables simply"""
        if item not in self.vars:
            # Construct a variable name for this
            self.vars[item] = z3.Bool(self._name(item))
        return self.vars[item]

    def add(self, *constraints):
        """Add arbitrary constraints to the puzzle"""
        for c in constraints:
            self.solver.add(c)

    def solve(self):
        """Callable from a while loop"""
        if self.model is not None:
            self.solver.pop()
            self._reject()
        self.solver.push()
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

    def neighbours(self, cell):
        (x, y) = cell
        return self.cells.intersection({(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)})

    def borders(self, cell):
        return {self.connection(cell, cell2) for cell2 in self.neighbours(cell)}

    def visited(self, cell):
        """Does a loop pass through this cell?"""
        if cell in self.vars:
            return self.model.eval(self[cell])
        return False

    def connection(self, cell1, cell2):
        if cell1 in self.cells and cell2 in self.cells:
            return tuple(sorted((cell1, cell2)))
        return None

    def connected(self, cell1, cell2):
        """Is this cell connected to another in the given direction?"""
        border = self.connection(cell1, cell2)
        if border in self.vars:
            return self.model.eval(self[border])
        return False
