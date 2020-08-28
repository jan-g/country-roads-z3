from country_roads.puzzle import Puzzle
from country_roads.display import plot
from country_roads.solution import add_constraints


def main():
    p = Puzzle(
        "aabbcc",
        "addbcc",
        "eddffg",
        "edhffg",
        "iihfjj",
        "iihhjj",
        c=1,
        d=3,
        i=2,
    )
    add_constraints(p)
    while p.solve():
        plot(p)


if __name__ == "__main__":
    main()
