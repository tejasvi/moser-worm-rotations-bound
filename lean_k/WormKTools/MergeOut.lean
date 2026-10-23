import WormCore.Family

/-! Write the merged certificate of a chunk (same text format as the input chunk).

Post-order over each unit's tree. A node with at most `maxSub` original leaves below it is tested with up to `K`
candidate records from its subtree (children's candidates first, in order); if `leafOK` passes on the node's box
with one of them, the subtree becomes one leaf with that record (code `L`, or `K` for a Lemma K record). The leaf test
is the unchanged `leafOK`, so the merged chunk must pass `chunkCheck` like the original (re-checked natively
before use).

usage: wormk_mergeout DATADIR K MAXSUB OUTDIR CHUNKFILE...   (writes OUTDIR/<name>, prints one stats line each) -/

open WormCore MoserWorm

def pad5 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (5 - s.length) '0') ++ s

structure MRes where
  collapsed : Bool
  codes : Array Char          -- merged codes of the subtree
  toks : Array String         -- merged record tokens of the subtree
  cands : List (Rec × String) -- candidate records (at most K)
  orig : Nat                  -- original leaf count
  restC : List Char
  restR : List (Rec × String)

partial def mwalk (F : Fam) (K maxSub : Nat) (lo hi : Array Int) (cs : List Char) (recs : List (Rec × String))
    (tests : IO.Ref Nat) : IO (Option MRes) := do
  match cs with
  | [] => return none
  | c :: cs' =>
    if c = 'L' ∨ c = 'K' then
      match recs with
      | (r, t) :: rs => return some ⟨true, #[c], #[t], [(r, t)], 1, cs', rs⟩
      | [] => return none
    else match codeDim c with
      | some k => match halves lo hi k with
        | some ((l1, h1), (l2, h2)) =>
          match ← mwalk F K maxSub l1 h1 cs' recs tests with
          | none => return none
          | some a =>
            match ← mwalk F K maxSub l2 h2 a.restC a.restR tests with
            | none => return none
            | some b =>
              let cands := (a.cands ++ b.cands).take K
              let orig := a.orig + b.orig
              let mut found : Option (Rec × String) := none
              if orig ≤ maxSub then
                for rt in cands do
                  if found.isNone then
                    tests.modify (· + 1)
                    if leafOK F maxsmallW tauHiW lo hi rt.1 then found := some rt
              match found with
              | some (r, t) =>
                return some ⟨true, #[if t.any (· = ',') then 'K' else 'L'], #[t], [(r, t)], orig, b.restC, b.restR⟩
              | none =>
                return some ⟨false, (#[c] ++ a.codes) ++ b.codes, a.toks ++ b.toks, cands, orig, b.restC, b.restR⟩
        | none => return none
      | none => return none

def main (args : List String) : IO Unit := do
  let dir := args[0]!
  let K := args[1]!.toNat!
  let maxSub := args[2]!.toNat!
  let outDir := args[3]!
  let F := mkFam famArcs famGid
  for cf in args.drop 4 do
    let t0 ← IO.monoMsNow
    let txt ← IO.FS.readFile cf
    let toks := (txt.splitOn " ").toArray
    let n := (String.ofList (toks[0]!.toList.drop 1)).toNat!
    let table := ((toks.extract 1 (n + 1)).map parseSt).map fun o => o.getD default
    let mut out : Array String := toks.extract 0 (n + 1)
    let mut i := n + 1
    let mut before := 0
    let mut after := 0
    let mut bad := 0
    let tests ← IO.mkRef 0
    while i < toks.size do
      let t := toks[i]!
      let pu := (String.ofList (t.toList.drop 1)).splitOn "."
      let p := pu[0]!.toNat!
      let u := pu[1]!.toNat!
      let cs := String.ofList (toks[i + 1]!.toList.drop 1)
      let skelTxt ← IO.FS.readFile s!"{dir}/skel/s{pad5 p}.txt"
      let skel := String.ofList (skelTxt.toList.filter (fun c => c ≠ (Char.ofNat 10)))
      let nl := cs.foldl (fun a c => if c = 'L' ∨ c = 'K' then a + 1 else a) 0
      let rtoks := (toks.extract (i + 2) (i + 2 + nl)).toList
      let recs := rtoks.filterMap fun tk => (parseRec table tk).map (·, tk)
      match unitBoxes rootW p skel with
      | none => bad := bad + 1
      | some boxes =>
        match ← mwalk F K maxSub boxes[u]!.1 boxes[u]!.2 cs.toList recs tests with
        | some m =>
          if m.restC.isEmpty && m.restR.isEmpty && recs.length == nl then
            out := (out.push t).push ("C" ++ String.ofList m.codes.toList) ++ m.toks
            before := before + nl
            after := after + m.toks.size
          else bad := bad + 1
        | none => bad := bad + 1
      i := i + 2 + nl
    let name := (cf.splitOn "/").getLast!
    IO.FS.writeFile s!"{outDir}/{name}" (" ".intercalate out.toList)
    let t1 ← IO.monoMsNow
    IO.println s!"{name} leaves {before} merged {after} ratio {(Float.ofNat after) / (Float.ofNat (max before 1))} tests {← tests.get} bad {bad} ms {t1 - t0}"
