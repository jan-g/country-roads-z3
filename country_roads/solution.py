import z3


def add_constraints(puzzle):
    """Add the rules that guide us toward a single solution"""

    bool_to_int = utility_functions(puzzle)
    loop_logic(puzzle, bool_to_int)
    regions_visited_once(puzzle, bool_to_int)
    regions_have_n_visited_squares(puzzle, bool_to_int)


def utility_functions(puzzle):
    bool_to_int = z3.Function("bool_to_int", z3.BoolSort(), z3.IntSort())
    puzzle.add(bool_to_int(True) == 1)
    puzzle.add(bool_to_int(False) == 0)
    return bool_to_int


def loop_logic(puzzle, bool_to_int):
    """Basic connectedness rules:
       Iff a cell is not visited, then none of its edges are traversed
       Iff a cell is visited, then precisely two of its borders are traversed
    """
    for cell in puzzle.cells:
        borders = puzzle.borders(cell)

        off = z3.Not(puzzle[cell])
        puzzle.add(off == z3.And(*(z3.Not(puzzle[border]) for border in borders)))

        on = puzzle[cell]
        puzzle.add(on == (sum(bool_to_int(puzzle[border]) for border in borders) == 2))


def regions_visited_once(puzzle, bool_to_int):
    """The loop visits each region precisely once"""
    for region in puzzle.regions:
        cells = puzzle.regions[region]

        # Find all neighbouring cells
        borders = {puzzle.connection(cell, other)
                   for cell in cells
                   for other in puzzle.neighbours(cell)
                   if other not in cells}

        # For a region to be visited once only, that means the loop crosses its border precisely twice
        puzzle.add(sum(bool_to_int(puzzle[border]) for border in borders) == 2)


def regions_have_n_visited_squares(puzzle, bool_to_int):
    """Some regions must have a fixed number of visited squares"""
    for region, visited in puzzle.region_constraints.items():
        cells = puzzle.regions[region]

        puzzle.add(visited == sum(bool_to_int(puzzle[cell]) for cell in cells))
