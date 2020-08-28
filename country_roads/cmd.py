from country_roads.puzzle import Puzzle
from country_roads.display import plot
from country_roads.solution import add_constraints


def main():
    p = harder_puzzle()
    add_constraints(p)
    while p.solve():
        plot(p, scale=80)


def test_puzzle():
    return Puzzle(
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


def harder_puzzle():
    return Puzzle(
        "abbbddefff",
        "abcciihggf",
        "aacciihgff",
        "lllllijggk",
        "mmmliijjkk",
        "nnnppjjqqk",
        "nonpppqqkk",
        "rrrtttvvww",
        "srstttvwwx",
        "ssstuuxxxx",
        c=2,
        i=5,
        p=3,
        v=1,
    )


if __name__ == "__main__":
    main()
