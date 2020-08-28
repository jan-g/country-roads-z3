import random
from graphics import GraphWin, Point, Line, Rectangle, Circle, Text, color_rgb


def plot(puzzle):
    w, h = puzzle.dimensions
    scale = 100

    win = GraphWin(width=w * scale, height=h * scale)

    colours = {}

    for (x, y) in puzzle.cells:
        r = Rectangle(Point(x * scale, y * scale), Point((x + 1) * scale, (y + 1) * scale))
        # Get the region
        region = puzzle.cell_region[(x, y)]
        if region not in colours:
            colours[region] = color_rgb(random.randrange(120, 200),
                                        random.randrange(120, 200),
                                        random.randrange(120, 200))
        r.setFill(colours[region])
        r.draw(win)

        # Is this cell visited?
        if puzzle.visited((x, y)):
            c = Circle(Point((x + 0.5) * scale, (y + 0.5) * scale), scale / 10)
            c.setFill("black")
            c.draw(win)

    for r, c in puzzle.region_constraints.items():
        # Leftmost of the uppermost cells
        (x, y) = min(puzzle.regions[r], key=lambda cell: (cell[1], cell[0]))
        t = Text(Point((x + 0.1) * scale, (y + 0.1) * scale), str(c))
        t.draw(win)

    for (x, y) in puzzle.cells:
        if puzzle.connected((x, y), (x + 1, y)):
            l = Line(Point((x + 0.5) * scale, (y + 0.5) * scale),
                     Point((x + 1.5) * scale, (y + 0.5) * scale))
            l.setWidth(scale / 20)
            l.draw(win)

        if puzzle.connected((x, y), (x, y + 1)):
            l = Line(Point((x + 0.5) * scale, (y + 0.5) * scale),
                     Point((x + 0.5) * scale, (y + 1.5) * scale))
            l.setWidth(scale / 20)
            l.draw(win)

    win.getKey()
