import z3


def add_constraints(puzzle):
    """Add the rules that guide us toward a single solution"""

    bool_to_int = utility_functions(puzzle)
    loop_logic(puzzle, bool_to_int)
    regions_visited_once(puzzle, bool_to_int)
    regions_have_n_visited_squares(puzzle, bool_to_int)
    neighbouring_unvisited_squares_constrained(puzzle)
    loop_is_closed(puzzle)


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


def neighbouring_unvisited_squares_constrained(puzzle):
    """No two neighbouring cells in different regions are both unvisited"""
    for cell in puzzle.cells:
        for other in puzzle.neighbours(cell):
            if puzzle.cell_region[cell] != puzzle.cell_region[other]:
                puzzle.add(z3.Or(puzzle[cell], puzzle[other]))


def loop_is_closed(puzzle):
    """The loop is simply closed

        This is implemented in two stages:
        - firstly, we define what it means for two regions to be "connected": they border each other and the loop
          crosses between them;
        - then, we define the transitive reflexive closure of this connected relationship.

        We demand that all regions are transitively connected to one (chosen arbitrarily).
    """

    regions = list(puzzle.regions.keys())

    # Begin by declaring a Region type
    Region = z3.Datatype("Region")
    for r in regions:
        Region.declare("R_{}".format(r))
    Region = Region.create()

    region_atom = {r: getattr(Region, "R_{}".format(r)) for r in regions}
    print(region_atom)

    # "Is connected to" relationship between Regions
    connected = z3.Function("connected", Region, Region, z3.BoolSort())

    # For each pair of regions: define their connectedness if they border each other
    for region1, cells1 in puzzle.regions.items():
        for region2, cells2 in puzzle.regions.items():
            if region1 == region2:
                # We consider regions to be self-connected
                puzzle.add(connected(region_atom[region1], region_atom[region2]))
                continue

            borders = {puzzle.connection(c1, c2) for c1 in cells1 for c2 in cells2 if c1 in puzzle.neighbours(c2)}
            # They are actually connected if the loop transits over any of those border connections
            puzzle.add(
                connected(region_atom[region1], region_atom[region2]) == z3.Or(*(puzzle[conn] for conn in borders)))

    # Transitive closure of "is connected to"
    # (At the moment, this does not appear to be working correctly.)
    path_connected = z3.TransitiveClosure(connected)

    # All regions are connected to the first
    for r in regions:
        puzzle.add(path_connected(region_atom[regions[0]], region_atom[r]))

    # Spit this out for debugging
    puzzle.extras = (Region, region_atom, connected, path_connected)
