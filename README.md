# A lower bound for Moser's worm problem with rotations and translations

Checker, check logs, search programs and two formal proofs in Lean 4 for the paper
*A lower bound for Moser's worm problem with rotations and translations* by Tejasvi Singh Tomar
(Zenodo, [doi:10.5281/zenodo.23585569](https://doi.org/10.5281/zenodo.23585569)). The certificate (9.9 GB in nineteen archives), the data of the
formal proofs (7.3 GB in seven archives for `lean/`, 8.5 GB in two archives for `lean_k/`) and this repository are
archived in the supplement record [doi:10.5281/zenodo.23585570](https://doi.org/10.5281/zenodo.23585570).

## Theorem

Let Ω be a convex set in the plane that contains, for each of the five arcs L, T, U, C, S below, a copy obtained by a
rotation and a translation. Then area(Ω) ≥ 0.2414.

Consequently M⁺ ≥ 0.2414, where M⁺ is the least area of a convex set that contains a rotated and translated copy of
every planar arc of length 1. This is constant 13a of the repository of optimization constants
(github.com/teorth/optimizationproblems), which defines it with "a rigid motion (translation + rotation; no
reflections)". The previous lower bound, 0.239, was proved by Keller (arXiv:2609.21968) for the version with
reflections and carries over to this one. The bound above is not claimed for the version with reflections.

`lean/` contains a formal proof of this bound in Lean 4 (see below).

The arcs are polygonal; each starts at the given point and has the given link lengths and directions:

| arc | start | lengths | directions (degrees) |
|---|---|---|---|
| L | (-1/2, 0) | 1 | 0 |
| T | (-1/4, 0) | 1/2, 1/2 | 60, -60 |
| U | (0, 0) | 1/3, 1/3, 1/3 | 0, 84, 168 |
| C | (0, 0) | 3/20, 7/10, 3/20 | 0, -70, 0 |
| S | (0, 0) | 41/250, 84/125, 41/250 | 0, 75, 0 |

C and S are zigzags that turn in opposite directions, and no rotation maps the turning pattern of one to that of the
other.

## Proof outline

1. **Placements.** Fix L. A placement, a point p of R¹², gives T, U, C and S an angle and a translation each. Let A(p)
   be the area of the convex hull of the placed arcs. A convex set as in the theorem contains such a hull, so it is
   enough to show A > 0.2414 everywhere.
2. **A bounded box.** By the symmetries of the hulls (T: rotation by 2π/3; C, S: half-turn), a global half-turn and
   Keller's chord bound, every placement with A < 0.2414 has a copy with the same hull area in the box D of the paper
   (angles in [0, π/3], [0, 2π], [0, π], [0, π]; translations with |t_x| ≤ 0.6149… and |t_y| ≤ 0.4828).
3. **Bounds on a box.** On a box of placements, the signed area F of a polygon through chosen vertices of the placed
   arcs is a lower bound for A if the vertices stay in angular order around a point (fan), if there are at most four
   of them, or if the list splits along a chord into such pieces (Keller's chord decomposition). F is bounded below on
   the box by a second-order Taylor bound with a certified eigenvalue bound, and several such bounds can be combined
   convexly.
4. **Branch and bound.** A root box X that contains D is cut into 1,048,576 cells, distributed over 16,384 parts. In
   each cell a binary tree of boxes ends in leaves at which a recorded structure, or a recorded convex combination of
   structures, proves A > 0.2414. The certificate has 866,777,204 nodes and 433,912,890 leaves, and 70,576,243 leaves
   use a combination.

## Checking the certificate

Download the nineteen archives `cert_w2414a_K.tar` (K = 0, ..., 18) from the supplement record and extract them into one
directory CERT. Archive K holds a contiguous range of parts, three files per part (`partNNNN.json`, the header;
`partNNNN.npy`, the tree codes; `partNNNN.leaves.jsonl.gz`, the leaf records), and a list `MANIFEST_K.txt` of their
SHA-256 hashes. The ranges are filled in order of the parts up to about 0.6 GB, so the largest parts, 276 and 1333,
have an archive each:

| K | parts | K | parts |
|---|---|---|---|
| 0 | 0-275 | 10 | 3383-3411 |
| 1 | 276 | 11 | 3412-3448 |
| 2 | 277-339 | 12 | 3449-5427 |
| 3 | 340-372 | 13 | 5428-7542 |
| 4 | 373-1332 | 14 | 7543-9586 |
| 5 | 1333 | 15 | 9587-12621 |
| 6 | 1334-1398 | 16 | 12622-13682 |
| 7 | 1399-2387 | 17 | 13683-14677 |
| 8 | 2388-2389 | 18 | 14678-16383 |
| 9 | 2390-3382 |  |  |

Then:

    for K in $(seq 0 18); do tar -xf cert_w2414a_$K.tar -C CERT; done
    cd CERT && for K in $(seq 0 18); do sha256sum -c --quiet MANIFEST_$K.txt; done

Together the archives hold the 49,152 files of the parts. The directory of the certificate on our servers listed 29
further files in its list of SHA-256 hashes:

- its summary, which is `checker/logs/SUMMARY.json` here;
- copies of the nineteen programs that ran. The twelve programs of the search and the check are in `search/` and
  `checker/`, and `PROVENANCE.md` gives the hashes of the versions that ran. The other seven distributed the work over
  the servers, started and stopped the worker processes, ran a pilot and the control runs, and froze the directory;
- the logs of our check runs, one file per server, whose passing lines are in `checker/logs/check_lines.jsonl.gz`, and
  the plan that assigned the check jobs to the servers;
- the plan and the log of the search runs, the results of control runs of the checker, and our notes on the certificate.

The files of the last two items and the seven programs are not published: they name our servers and directories, and
neither checking the certificate nor running the search needs them.

The checker needs Python 3 with numpy and python-flint, which contains Arb. Our check runs used Python 3.12 and
python-flint 0.9.0, and the repeated check described below used Python 3.13. The checker relies on assert statements and
refuses to run under `python -O`.

    WCHECK_DISTRIBUTED=1 python3 -I checker/wcheck.py CERT 0 1 2      # check parts 0, 1 and 2
    python3 -I checker/wcheck_v2.py CERT 276 --leaves 0:500000       # check a range of leaves of one part

Each run prints one line of JSON per part. Without `WCHECK_DISTRIBUTED=1`, `wcheck.py` first checks that all 16,384
parts are present in CERT. `wcheck_v2.py` differs from `wcheck.py` only in the routine that checks a part and in its
command line: it decodes the whole tree of the part, checks the leaves whose index lies in the given range, and only
reads the records of the other leaves. After all parts are checked,

    python3 -I checker/wcheck_presence_v2.py CERT LOG [LOG ...]

verifies that all parts are present, that their headers agree, and that the passing lines of the logs, for the files
whose SHA-256 hashes they record, cover all leaves of every part. On our runs it prints the content of
`checker/logs/SUMMARY.json`:

    {"nparts": 16384, "all_ok": true, "leaves": 433912890, "min_margin": 9.60748147894597e-08, "bad": [], "nbad": 0,
     "check_lines": 19772, "tau": 0.2414, "family": "polished1"}

`checker/logs/check_lines.jsonl.gz` contains the 19,772 passing lines of our runs for the certificate's files; after
decompression it can be passed to `wcheck_presence_v2.py` as LOG. The repeated check of all leaves took 208 CPU-hours
in 16,940 runs. Here and below, a CPU-hour is an hour of one hardware thread (virtual CPU) of a cloud server;
`lean/README.md` and `lean_k/README.md` call it a thread-hour and a core-hour. Most parts are small; the largest,
part 276, has 38.6 million leaves and is best checked in ranges. Our check runs took about 12 minutes of wall-clock
time on the cloud servers that ran the search (1,536 virtual CPUs), and they accepted all parts on the first run.

    python3 -I checker/check_headers.py CERT

compares the headers with the paper, which the checker and the presence program do not do. It verifies that the arcs
in every header are exactly those of the table above, with the angle periods 2π/3, 2π, π and π of T, U, C and S, and
that the vertex numbering lists every vertex once. It also verifies that all headers carry the same grid, root box,
target and number of parts, and that each header carries the index of its file. Finally, it computes the cell
endpoints in double precision as the checker computes them and verifies that they start and end at the corners of the
root box, increase, and equal the exact rational values, so that the cells tile the root box and are equal. On the
certificate it prints

    {"ok": true, "headers": 16384, "grid": [4, 2, 2, 16, 2, 2, 8, 2, 2, 8, 2, 2], "cells": 1048576, "nparts": 16384,
     "tau": 0.2414, "errors": []}

What the checker verifies (Section 4 of the paper): the arcs in the headers (lengths at most 1, the segment, the
two-link arc, the parallelogram hulls of C and S); that the root box contains D; the structure of every tree, with
every split at the double-precision midpoint of the box and every leaf box exactly c ± h; at every leaf, in ball
arithmetic at 100 bits, the validity of every structure of positive weight on the whole box, its Taylor bound, and
that the combination of these bounds exceeds 0.2414. Two steps leave ball arithmetic. The checker rounds the lower
bound Λ for the second-order term of the Taylor bound to double precision, from up to three candidates; Section 4.3
of the paper shows that this changes the accepted bounds by less than 10⁻¹⁴, against a smallest margin of 9.607·10⁻⁸.
And a fallback for square roots of balls that contain 0 works in double precision; it returns an enclosure for every
such ball that occurs. The certificate is not trusted: a leaf passes only if these inequalities prove A > 0.2414 on it.

Before release, we audited the certificate and the checker separately from the work that produced them. We rederived the
lemmas on which the checker rests, reviewed the checker, the presence program and `check_headers.py` against them,
checked all leaves again with the same results, and decoded the trees of all parts with a separate program. A further
implementation of the leaf bound, which shares no code with the checker, accepted all 500 leaves on which it
was run, among them 100 of those with the smallest margins (Section 4.7 of the paper). The formal proof described below
also verifies the whole certificate, converted into another format, with a checker written in Lean that bounds the hull
area on the leaves differently.

`checker/wcheck_selftest.py CERT PART` runs the checker on one part and on modified copies of its leaf records and
header, which must be rejected (repeated vertex, clockwise fan, fan centre outside, five-point small list, negative
weight, target 10, coincident vertices, exchanged chord sides). `checker/testcert/` holds four parts of a test
certificate for the same arcs, with target 0.24 and the root box cut into 65,536 parts:

    python3 -I checker/wcheck_selftest.py checker/testcert 5613      # and 49490; both print ALL PASS

None of these modifications reaches the test of the angle sum of a fan. `checker/negtest_winding.py CERT [PART ...]`
reorders every fan of odd length at least 5 in star order, which winds twice around the centre of the fan, and checks
that the checker rejects every reordering whose determinants are all positive at the centre of the leaf box, so that
only the angle sum can reject it, while it accepts the original fans. It finds 2 such reorderings in
`checker/testcert` and 66 in parts 0 to 9 of the certificate, and the checker rejects all of them.

`checker/negtest_leaf.py CERT [TAU ...]` finds the leaf whose box contains the placement with the smallest hull area
found (`data/opt_point.json`); this is leaf 9,704,165 of part 1335. It checks that its box is exactly c ± h and runs the
leaf routine of the checker with the target of the header and with the given targets. With `0.2415 0.2421` the leaf
passes 0.2414, with a margin of 4.3·10⁻⁵, and fails the other two. A whole part with a target above 0.241400003 in its
header already fails at the root-box test, because the box D grows with the target.

Comments and docstrings in the checker use the numbering of the lemmas in our working notes: W1 is Proposition 2.4
of the paper (the box D), W3 the fan lemma (Lemma 3.2), W4 the small lists (Lemma 3.1), W5 the chord decomposition
(Lemma 3.4, with Keller's fan from a vertex (Lemma 3.3) for its pieces), W6 the Taylor bound with the variation
bounds (Lemmas 3.7 and 3.8), and W7 (also called Lemma K) the combination bound (Lemma 3.10). In the code, `q2` is
the number Λ₂ of Lemma 3.7, the other entries of the list `qs` are Λ₁ and Λ₃, `q` is Λ, and `e2` is ε.

All lines of the check logs were produced by the version of `wcheck_v2.py` whose SHA-256 hash begins with 9374fec5,
and the presence program that ran has hash beginning with 9e7cbbd3; `wcheck.py` (hash beginning with 520e291e) is the
version from which `wcheck_v2.py` was made. The released `wcheck.py` and `wcheck_v2.py` differ from these versions only
in docstrings and in one comment; `PROVENANCE.md` lists every released file with the hash of the version that ran and
the changes.

## Formal proof in Lean 4 (`lean/`)

`lean/` proves, in Lean 4, the bound M⁺ ≥ 0.2414 of the theorem above, from the certificate of the nineteen archives
converted into text. The theorems are in `lean/WormN/Final.lean`:

- `Worm.worm_lower_2414 : WormLowerAt (2414 / 10000)`: every convex set that covers every unit arc has Lebesgue measure
  at least 0.2414;
- `Worm.optimalAreaM_lower_2414 : OptimalAreaLowerAt (2414 / 10000)`: the infimum of these measures, in [0, ∞], is at
  least 0.2414.

In the statement (`lean/Worm13a/Statement.lean` and `lean/Worm13a/StatementAt.lean`, which depend only on Mathlib),
the plane is ℂ, a unit arc is a map γ : ℝ → ℂ that is continuous on [0, 1] and has total variation 1 on [0, 1], and a
set K covers γ if it contains e^{iθ}·γ([0, 1]) + t for some real θ and complex t. These definitions follow Keller's Lean
development, except that there a set covers γ if it contains the image of γ([0, 1]) under some isometry of the plane,
so that the copies may also be reflected.

The proof formalizes the reduction of Section 2 of the paper and Lemmas 3.1-3.4 for the structures of the certificate.
In place of the Python checker it uses a checker written in Lean (`lean/WormCore/`), whose soundness it proves
(`lean/WormSound/`). The Lean checker tests validity as the Python checker does, except that it certifies the winding of
a fan differently. On the leaves it uses its own bound: an exact quadratic model of the signed area in the translations
and in the cosines and sines of the angle offsets, bounded on the box by a Gershgorin-type estimate. Section 5 of the
paper describes both. The data (`lean/data/`, from the archives of the supplement record) consist of 11,072 chunks and
skeletons for the 16,384 parts. One module for each chunk proves, with `native_decide`, that the checker accepts the
chunk. Eleven leaves that the Lean bound could not close are each split once in the data; all halves pass.

Trusted base: the Lean kernel, the Lean compiler and the compiled checker; the last two because `native_decide`
evaluates the chunk checks by compiled code. `#print axioms Worm.worm_lower_2414` lists `propext`, `Classical.choice`,
`Quot.sound` and 11,074 auxiliary axioms `..._native.native_decide.ax_1_1`, one for each evaluated check (11,072 chunks,
the cover of all units and the skeleton walks). Each states that its evaluation returned true, and
`lean/tools/check_native.lean` checks that the type of each is the statement of its own theorem. The theorem
`wormLowerAt_2414_of_certificate`, which derives the bound from these checks, uses only the three standard axioms. The
data need not be trusted.

To check the proof, download the archives `worm_data_2414_meta.tar.zst` and `worm_data_2414_chunks1.tar.zst` to
`worm_data_2414_chunks6.tar.zst` from the supplement record, extract them in `lean/` and follow `lean/README.md`
(toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3`). Compiling the chunk modules took about 680 CPU-hours
on our servers, with at most 0.6 GB of memory per module; the final module needs about 4.7 GB.

We also checked the formal proof on another machine: we compared the types of the two theorems with the statement
file and listed their axioms, replayed in the Lean kernel all 11,537 modules of the formal proof outside Mathlib and
the libraries that Mathlib uses, and compared the chunk texts in the compiled modules with the data files. Compiling
222 chunk modules, chosen at random, again with a separately built checker gave identical files.

`lean/MoserWorm/` holds 15 files of Ethan Keller's Lean development `moser-worm-improved-bounds` (Apache-2.0, commit
9a339413), of which the proof imports eight. One of the others was adapted to the newer toolchain and carries a notice.
The licence, the upstream citation file and checksums are in `lean/third_party/moser-worm-improved-bounds/`; see
`lean/PROVENANCE.md`.

## The bound 0.241 checked by the Lean kernel alone (`lean_k/`)

`lean_k/` and the generated modules of the supplement record prove the weaker bound M⁺ ≥ 0.241 without code generated
by Lean's compiler. The theorems are in the generated module `WormKD/Final.lean`:

- `WormKD.worm_lower_K : WormLowerAt (2410 / 10000)`, with `WormLowerAt` of the statement above;
- `WormKD.optimalAreaM_lower_K : OptimalAreaLowerAt (2410 / 10000)`.

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`: the trusted base is Lean's kernel, including
the kernel's built-in arithmetic on natural numbers. The proof uses the reduction, the soundness proof of the checker
and the assembly of `lean/`, in their versions for τ = 0.241; `lean_k/` holds its own copy of these files, so that it
builds on its own.

Its data come from the certificate for τ = 0.241 that the first run of the search produced (see Search programs below),
with 264,084,910 leaves. It was converted like the data of `lean/`, and five leaves were split once. Then, going up the
tree of each unit, a subtree with at most 256 leaves became one leaf whenever `WormCore.leafOK` accepted its box with
one of at most 32 records taken from its leaves. This left 127,841,892 leaves. The compiled checker accepted the merged
certificate before the kernel checks were run; the proof does not depend on that run.

For the kernel, the leaf test `WormK4.leafOKRK4` evaluates the same interval arithmetic with its sums arranged
differently, and `WormK4.leafOKRK4_eq` proves that it equals the recursive leaf test of the checker on boxes with 12
coordinates. The leaves are grouped into 16,374,312 pieces of at most 64 leaves, in 140,827 modules. The box, the codes
and the record indices of a piece are natural-number literals, which decoders written in Lean expand in the kernel, so
the encoding need not be trusted. Each piece has one theorem, proved with `decide +kernel`. Above the pieces, 7,750
unit-group modules, 16,384 part modules, 256 block modules and 4 group modules join them up to `WormKD.Final`.

The generated modules are archived in the supplement record, and `lean_k/tools/gen_kd4.py`, run with `SUBMAX=64 SALT=1`,
writes the same files from the merged certificate and the skeletons archived with it. `lean_k/README.md` gives the
commands. Checking all 165,297 modules took about 18,300 CPU-hours on cloud servers. A module of pieces needs at most
3.6 GB of memory, the other generated modules at most 55.3 GB, and the final module about 77 GB.

A separate check compared the types of the two theorems with the statement file and scanned every generated module
for axioms. It also replayed a sample of 138 modules in the Lean kernel and compiled the 137 generated ones among them
again, which gave identical files.

A kernel-only proof of the weaker bound 0.24, with its two archives, is in the supplement records
[doi:10.5281/zenodo.23557869](https://doi.org/10.5281/zenodo.23557869) and
[doi:10.5281/zenodo.23574657](https://doi.org/10.5281/zenodo.23574657).

## Search programs

`search/` holds the programs that produced the certificate, which was made in two runs. A first run at τ = 0.241 made a
tree for every part, with the search program in two versions, `wtask_5acd5ac0.py` (335 parts) and `wtask_ab6507da.py`
(16,049 parts). A second run, with `wtask_812be2a4.py`, replayed these trees on the root box for τ = 0.2414 and searched
each of their leaves again at τ = 0.2414. Every part header cites this version and, in its field `refined_from`, the
SHA-256 hash of the tree codes of the first run; the certificate of the first run is archived in the supplement record
[doi:10.5281/zenodo.23557869](https://doi.org/10.5281/zenodo.23557869), with the data of a proof of the bound 0.241 by
compiled code. The file names carry the first eight hex digits of the SHA-256 hash of the version that ran. To run the
search, copy the files to the plain names (`wtask.py`, `wsearch.py`, `wbnb.py`, `wchord.py`, `wfam.py`, `lbsearch.py`,
`worm.py`, `fammin.py`, `run5b.py`, `fitscale.py`, `assemble.py`). They need Python 3 with numpy, scipy, numba and
highspy.

- `wfam.py`: the exact data of the arc family `polished1`, in the two versions that the part headers of the two runs cite (17da1a7b for
  1,299 parts of the first run, 261fc37d for the other parts of the first run and for all parts of the second). The
  second also contains a family for the version with reflections, which the certificate does not use; the data of
  `polished1` are the same in both.
- `wsearch.py FAMILY TAU PART NPARTS SPLIT0 OUTDIR [MAXSMALL]`: the depth-first branch and bound in double precision,
  which writes the three files of a part. `wbnb.py`, `wchord.py` and `lbsearch.py` form the candidate structures and
  evaluate their bounds; `worm.py`, `fammin.py`, `run5b.py` and `fitscale.py` are numerical helpers for the family.
- `wtask.py`: a pool of workers that runs the same search on the boxes of a part in time-limited tasks and assembles the
  trees of the part from them. The three versions run the same search. The second can also start single cells from a
  list, which we used to spread the largest parts over many machines, and the third can also continue the search from
  the leaves of a tree replayed on a new root box.
- `assemble.py`: joins the trees of the 64 cells of a part, searched separately, in cell order. In the first run the
  cells of 4,513 parts were searched separately and joined either by this program or by the same concatenation in
  `wtask.py`; in the second run 150 parts were refined cell by cell and joined in `wtask.py`.

A box that the search cannot close is split in the coordinate with the largest contribution to the loss in the
bound (in the widest coordinate if no candidate structure is valid), or in the coordinate in which the vertices move
most when the largest contribution is below 10⁻⁵ or the contributions explain less than half of the gap to the hull
area at the centre; a coordinate whose half-width is below 10⁻¹² is never split. Any split is valid for the checker.

`search/CHANGES.md` lists the files in which lines with absolute paths on our machines, or comments that named
internal notes, were changed for this release, with the SHA-256 hashes before and after. The job-distribution scripts
are not included. The search is not part of the proof.

## Data

`data/opt_point.json`: the placement with the smallest hull area found by local minimization from 300 starting points
(hull area 0.24205381484 in double precision). So, numerically, these five arcs cannot give a bound above about 0.24205.

## License and citation

The programs and the Lean files are licensed under Apache-2.0 (`LICENSE`); the files in `lean/MoserWorm/` are Ethan
Keller's, under the Apache License 2.0 in `lean/third_party/moser-worm-improved-bounds/LICENSE`. The certificate, the
data of the formal proof and the paper are licensed under CC-BY-4.0. Please cite the paper; see `CITATION.cff`.
