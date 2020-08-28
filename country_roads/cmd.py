from country_roads.puzzle import Puzzle
from country_roads.display import plot

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
    while p.solve():
        plot(p)


if __name__ == "__main__":
    main()
