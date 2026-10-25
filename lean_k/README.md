# Kernel-only proof of the bound 0.2414

This directory is the hand-written part of a Lean proof, checked by the Lean kernel alone, of the theorem
`WormKD.worm_lower_K : WormLowerAt (2414 / 10000)` (with `WormKD.optimalAreaM_lower_K : OptimalAreaLowerAt (2414 / 10000)`):
every convex set that contains a rotated and translated copy of every unit arc has area at least 0.2414
(`Worm13a/StatementAt.lean`). No step uses `native_decide`; the two theorems depend on `propext`, `Classical.choice` and
`Quot.sound` only.

The statement, the certificate checker and its soundness proof are those of the Lean proof tree of the bound 0.2414
(only the modules this proof uses; two files differ from that tree in comments only). That tree proves the same theorems
with `native_decide` for the certificate checks; this proof checks every leaf of the certificate in the kernel instead.

## Contents

- `Worm13a/`, `WormCore/`, `WormSound/`, `MoserWorm/`: the statement, the certificate checker and its soundness proof.
  `MoserWorm/` holds 8 of the 15 files listed in `PROVENANCE.md` (licence in `third_party/`).
- `WormKC/`: the kernel layer. `Walk.lean` (the unit walk with the leaf test as a parameter, and the top walk over
  pieces), `Pack.lean` (decoders of the packed data: codes, records, dyadic boxes, skeletons), `Lit.lean` (literal
  elaborators), `Cov.lean` (box covers and their assembly into `WormLowerAt τ` through the checker's soundness proof),
  `BridgeK.lean` (a piece checked with the kernel leaf test covers its box), `Salt.lean` (tagged box literals).
- `WormK/`, `WormKProof/`: the kernel form of the leaf test (`WormK4.leafOKRK4`) and the proof that it equals the
  checker's leaf test on boxes with 12 coordinates (`WormK4.leafOKRK4_eq`, by way of `WormK3`).
- `WormKTools/MergeOut.lean`: the merge pass (`lake build wormk_mergeout`).
- `tools/gen_kd5b.py` (writes the generated modules `WormKD/`), `tools/build_dag.py` (builds them, one `lean` process per
  module), `tools/StatementCheckK2414.lean` (checks the two statements and their axioms).

## Supplement archives

Each archive is split into parts of at most 2 GB. Every part is a complete tar file (zstd) holding a share of the
members; extract all parts of an archive into the same directory.

- `worm_k2414_sources_part*.tar.zst`: the whole project, i.e. this directory plus the 261,772 generated modules `WormKD/`.
- `worm_k2414_merged_certificate_part*.tar.zst`: the merged certificate (`merged/`, 11,072 chunks, `MANIFEST.tsv`,
  `TOOL.txt`) and the inputs of the generator besides it (`snap/WormCore/Family.lean`, `snap/data/skel/`,
  `snap/data/manifest.json`).

## Building and checking the proof

Extract the parts of `worm_k2414_sources` into an empty directory and, in that directory:

    lake exe cache get                                         # Mathlib oleans
    lake build WormKC.BridgeK WormKC.Salt WormKC.Lit WormK.Walk4
    LEAN_NUM_THREADS=1 python3 tools/build_dag.py . WormKD --jobs <threads> --mem-gb 240
    lake env lean tools/StatementCheckK2414.lean

`build_dag.py` builds the generated modules in dependency order with plain `lean -o <olean> -i <ilean> <file>` (no
options), at most `<threads>` at a time, each under an address-space cap of `--mem-gb` GB (the default 16 GB is too
small). The 231,440 hole modules took 28,547 core-hours in total, about 2.5 GB each; the 30,332 other generated modules
took 484 core-hours. The two largest parts, `WormKD.Part.P00276` and `WormKD.Part.P01333`, need about 198 GB and
15 minutes each (build them one at a time on a machine with at least 256 GB); every other part, block and group stays
under 94 GB, and `WormKD.Final` needs 123 GB. The last command prints `true` for both statement checks and the three
axioms.

## Regenerating the generated modules

`tools/gen_kd5b.py` writes the same `WormKD/` files from the merged certificate. Extract its parts, then with
`SNAP=snap` and `MERGED=merged`:

    python3 tools/gen_kd5b.py skel SNAP OUT
    SUBMAX=64 SALT=1 HOLE_IMPORT=WormK.Walk4 python3 tools/gen_kd5b.py range SNAP MERGED OUT k 20 64 900 "(WormK4.leafOKRK4 famW maxsmallW tauHiW)" K
    TAU=2414 python3 tools/gen_kd5b.py root OUT

where the `range` command runs for k = 0, ..., 255. `OUT/WormKD` then equals the `WormKD/` of the sources archive.

The merged certificate itself comes from the certificate of the Lean proof tree of the bound 0.2414 (its data archive)
by `wormk_mergeout DATADIR 32 256 OUTDIR CHUNK` for each chunk. In post-order over each unit's tree, a node with at most
256 original leaves below it is tested with up to 32 records from its subtree (children first); if the checker's leaf
test passes on the node's box with one of them, the subtree becomes one leaf with that record. 433,912,901 leaves become
196,725,046, with the unit counts unchanged. The merged chunks pass the checker's native chunk check; the kernel checks
every leaf again in any case.
