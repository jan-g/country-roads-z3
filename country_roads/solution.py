import z3


def add_constraints(puzzle):
    """Add the rules that guide us toward a single solution"""

    loop_logic(puzzle)


def loop_logic(puzzle):
    """Basic connectedness rules: iff a cell is not visited, then none of its edges are traversed
       Iff a cell is visited, then precisely two of its borders
    """
    for cell in puzzle.cells:
        borders = puzzle.borders(cell)

        off = z3.Not(puzzle[cell])
        puzzle.add(off == z3.And(*(z3.Not(puzzle[border]) for border in borders)))

        bool_to_int = z3.Function("bool_to_int", z3.BoolSort(), z3.IntSort())
        puzzle.add(bool_to_int(True) == 1)
        puzzle.add(bool_to_int(False) == 0)

        on = puzzle[cell]
        puzzle.add(on == (sum(bool_to_int(puzzle[border]) for border in borders) == 2))
