import sys
from itertools import combinations

def generate_partial_matchings(n, k):
    vertices = list(range(n))
    all_edges = [tuple(sorted((a, b))) for a, b in combinations(vertices, 2)]
    matchings = set()

    for edge_comb in combinations(all_edges, k):
        used_vertices = set()
        valid = True
        for a, b in edge_comb:
            if a in used_vertices or b in used_vertices:
                valid = False
                break
            used_vertices.update((a, b))
        if valid and len(used_vertices) == 2 * k:
            matchings.add(tuple(sorted(edge_comb)))
    
    return sorted(matchings)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: python3 {sys.argv[0]} n k")
        sys.exit(1)

    n = int(sys.argv[1])
    k = int(sys.argv[2])

    matchings = generate_partial_matchings(n, k)
    print(f"Generated {len(matchings)} matchings.")

    filename = f"matchings_{n}v_{k}e.txt"
    with open(filename, "w") as f:
        for m in matchings:
            f.write(str(list(m)) + "\n")

    print(f"Matchings saved to {filename}")
