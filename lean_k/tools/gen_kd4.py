#!/usr/bin/env python3
"""K data generator (production layout, plain Lean files).

  gen_kd4.py skel  SNAPDIR OUTDIR
      -> OUTDIR/WormKD/Skel.lean   (packed skeletons of all parts in a Braun tree; skelOf)
  gen_kd4.py part  SNAPDIR MERGEDDIR OUTDIR P MAXLEAVES PIECES_PER_HOLE LEAFT HT
      -> OUTDIR/WormKD/H/P<p>_<j>.lean (hole modules) and OUTDIR/WormKD/Part/P<p>.lean (part aggregator)
  LEAFT: Lean term of the leaf test; HT: proof that it equals leafOKR famW maxsmallW tauHiW (e.g. "rfl").
All data is packed into Nat literals (see WormKC/Pack.lean); the decoders there are untrusted."""
import sys, os, re
sys.set_int_max_str_digits(0)

def load_root(SNAP):
    fam = open(os.path.join(SNAP, "WormCore/Family.lean")).read()
    def arr(name):
        m = re.search(name + r" := #\[([^\]]*)\]", fam)
        return [int(x.strip().strip("()")) for x in m.group(1).split(",")]
    return arr("lo"), arr("hi"), arr("split0"), int(re.search(r"nparts := (\d+)", fam).group(1))

class Geo:
    def __init__(self, SNAP):
        self.SNAP = SNAP
        self.LO, self.HI, self.SPLIT0, self.NPARTS = load_root(SNAP)
        global ROOT
        ROOT = (self.LO, self.HI)
        self.D = len(self.LO); self.NCELLS = 1
        for s in self.SPLIT0: self.NCELLS *= s
    def stride(self, j):
        r = 1
        for s in self.SPLIT0[j + 1:]: r *= s
        return r
    def cell_box(self, c):
        lo, hi = [], []
        for j in range(self.D):
            w = (self.HI[j] - self.LO[j]) // self.SPLIT0[j]; i = (c // self.stride(j)) % self.SPLIT0[j]
            lo.append(self.LO[j] + w * i); hi.append(self.LO[j] + w * (i + 1))
        return lo, hi
    def skel(self, p):
        return open(os.path.join(self.SNAP, "data/skel/s%05d.txt" % p)).read().strip()
    def unit_boxes(self, p):
        st = [self.cell_box(p + self.NPARTS * k) for k in range(self.NCELLS // self.NPARTS)]; acc = []
        for ch in self.skel(p):
            box = st.pop(0)
            if ch == 'U': acc.append(box)
            else:
                a, b = halves(box[0], box[1], code_dim(ch)); st[0:0] = [a, b]
        assert not st
        return acc

def code_dim(ch):
    if '0' <= ch <= '9': return ord(ch) - 48
    return {'a': 10, 'b': 11}.get(ch)
def halves(lo, hi, k):
    s = lo[k] + hi[k]; assert s % 2 == 0
    h1 = list(hi); h1[k] = s // 2; l2 = list(lo); l2[k] = s // 2
    return (lo, h1), (l2, hi)

class Bits:
    def __init__(self): self.v = 0; self.pos = 0
    def put(self, x, k):
        assert 0 <= x < (1 << k), (x, k); self.v |= x << self.pos; self.pos += k
    def put_int(self, x, k):
        self.put(0 if x >= 0 else 1, 1); self.put(abs(x), k)

ROOT = None
def pack_box(box):
    """dyadic (depth, index) per coordinate, 6-bit depth then `depth`-bit index (WormKC.Pack.decodeBox)"""
    lo0, hi0 = ROOT
    b = Bits()
    for i in range(12):
        W = hi0[i] - lo0[i]; w = box[1][i] - box[0][i]
        d = 0
        while (W >> d) > w: d += 1
        assert W % (1 << d) == 0 and (W >> d) == w, ("not dyadic", i, d)
        k = (box[0][i] - lo0[i]) // w
        assert lo0[i] + k * w == box[0][i] and 0 <= k < (1 << d)
        b.put(d, 6); b.put(k, d)
    return b.v

SYM = {c: i + 1 for i, c in enumerate("0123456789abLKP")}
def pack_codes(cs):
    n = 0
    for i, c in enumerate(cs): n += SYM[c] << (4 * i)
    return n
SKSYM = {c: i + 1 for i, c in enumerate("0123456789abU")}
def pack_skel(cs):
    n = 0
    for i, c in enumerate(cs): n += SKSYM[c] << (4 * i)
    return n
def pack_idx(ix):
    n = 0
    for i, v in enumerate(ix):
        assert 0 <= v < 65536; n += v << (16 * i)
    return n

def put_ct(b, t, i=0):
    c = t[i]
    if c == 's': b.put(0, 2); return i + 1
    if c == 'f': b.put(1, 2); b.put(int(t[i + 1], 36), 5); return i + 2
    if c == 'c':
        b.put(2, 2); b.put(int(t[i + 1], 36), 5); b.put(int(t[i + 2], 36), 5)
        j = put_ct(b, t, i + 3); return put_ct(b, t, j)
    raise ValueError(t)
def put_st(b, tok):
    kind = {'s': 0, 'f': 1, 'c': 2}[tok[0]]
    body = tok[1:].split('|')
    ids = [ord(c) - 97 for c in body[0]]
    b.put(kind, 2); b.put(len(ids), 5)
    for g in ids: b.put(g, 5)
    if kind == 1: b.put_int(int(body[1]), 62); b.put_int(int(body[2]), 62)
    elif kind == 2:
        j = put_ct(b, body[1]); assert j == len(body[1])
DFX = 72057594037927936
def pack_rec(tok, table):
    b = Bits()
    if ',' in tok:
        items = [it.split(',') for it in tok.split(';')]
        b.put(len(items), 4)
        for a, w in items: put_st(b, table[int(a, 36)]); b.put_int(int(w), 62)
    else:
        b.put(1, 4); put_st(b, table[int(tok, 36)]); b.put_int(DFX, 62)
    return b.v

def braun(vals):
    if not vals: return "K.BTree.leaf"
    return "(K.BTree.node %s %s %s)" % (vals[0], braun(vals[1::2]), braun(vals[2::2]))

HDR = ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "set_option Elab.async false", ""]

def gen_skel(SNAP, OUT):
    g = Geo(SNAP)
    vals = ["%d" % pack_skel(g.skel(p)) for p in range(g.NPARTS)]
    os.makedirs(os.path.join(OUT, "WormKD"), exist_ok=True)
    L = ["import WormKC.Lit", "", "/-! Packed skeletons of all %d parts (generated). -/" % g.NPARTS, ""] + HDR + [
         "namespace WormKD", "open WormCore", "",
         "noncomputable def skelTab : K.BTree Nat := nat_btree% \"" + " ".join(vals) + "\"", "",
         "/-- The skeleton of part `p`. -/",
         "noncomputable def skelOf (p : Nat) : String := String.ofList (K.decodeSkel 4096 ((skelTab.get p).getD 0))", "",
         "end WormKD", ""]
    open(os.path.join(OUT, "WormKD/Skel.lean"), "w").write("\n".join(L))

def read_units(MERGED, p):
    """all units of part p, from the merged chunks that contain them (scan; fine for tests)"""
    out = {}
    for f in sorted(os.listdir(MERGED)):
        toks = open(os.path.join(MERGED, f)).read().split(' ')
        n = int(toks[0][1:]); table = toks[1:n + 1]; i = n + 1
        while i < len(toks):
            pp, u = map(int, toks[i][1:].split('.')); codes = toks[i + 1][1:]
            nl = sum(1 for c in codes if c in 'LK')
            if pp == p: out[u] = (codes, toks[i + 2:i + 2 + nl], table)
            i += 2 + nl
    return out

def slices(xs, k=64):
    return [xs[i:i + k] for i in range(0, len(xs), k)] or [[]]

def rnest(xs):
    """right-nested appends with explicit parentheses (`++` is left-associative in Lean)"""
    if len(xs) == 1: return xs[0]
    return "(%s ++ %s)" % (xs[0], rnest(xs[1:]))

def forall_chain(names):
    proof = "List.forall_mem_nil _"
    for nm in reversed(names): proof = "List.forall_mem_cons.mpr ⟨%s, %s⟩" % (nm, proof)
    return proof

def gen_part(SNAP, MERGED, OUT, p, MAXL, PPH, LEAFT, HT):
    g = Geo(SNAP)
    ubs = g.unit_boxes(p)
    units = read_units(MERGED, p)
    assert sorted(units) == list(range(len(ubs))), ("missing units", p, len(units), len(ubs))
    # cut every unit into pieces
    allpieces = []   # (unit, box, codes, rtoks, table)
    tops = []        # per unit: top codes, list of piece ids
    for u in range(len(ubs)):
        codes, rtoks, table = units[u]
        def subtree_end(j):
            if codes[j] in 'LK': return j + 1, 1
            a, na = subtree_end(j + 1); b, nb = subtree_end(a); return b, na + nb
        rpos = [0]; top = []; ids = []
        def cut(j, box):
            e, nlv = subtree_end(j)
            if nlv <= MAXL:
                ids.append(len(allpieces)); allpieces.append((u, box, codes[j:e], rtoks[rpos[0]:rpos[0] + nlv], table))
                rpos[0] += nlv; top.append('P'); return e
            c = codes[j]; top.append(c); a, b = halves(box[0], box[1], code_dim(c))
            return cut(cut(j + 1, a), b)
        sys.setrecursionlimit(100000)
        assert cut(0, ubs[u]) == len(codes) and rpos[0] == len(rtoks)
        tops.append((''.join(top), ids))
    # hole modules
    holes = slices(list(range(len(allpieces))), PPH)
    os.makedirs(os.path.join(OUT, "WormKD/H"), exist_ok=True); os.makedirs(os.path.join(OUT, "WormKD/Part"), exist_ok=True)
    hname = {}
    for j, hp in enumerate(holes):
        mod = "P%05d_%03d" % (p, j)
        ridx = {}; rvals = []
        lines = ["import WormKC.Lit", "", "/-! Part %d, hole module %d: %d pieces (generated). -/" % (p, j, len(hp)), ""] + HDR + [
                 "namespace WormKD.H.%s" % mod, "open WormCore", ""]
        body = []
        for k in hp:
            u, box, pc, rt, table = allpieces[k]
            ix = []
            for t in rt:
                key = (id(table), t)
                if key not in ridx: ridx[key] = len(rvals); rvals.append("%d" % pack_rec(t, table))
                ix.append(ridx[key])
            body.append("theorem pc%d : K.pieceOKK %s tab (nat_lit%% \"%d\") (nat_lit%% \"%d\") %d (nat_lit%% \"%d\") = true := by\n  decide +kernel" % (
                k, LEAFT, pack_box(box), pack_codes(pc), len(rt), pack_idx(ix)))
            hname[k] = (mod, pack_box(box))
        lines += ["noncomputable def tab : K.BTree Nat := nat_btree% \"" + " ".join(rvals) + "\"", ""] + body + ["", "end WormKD.H.%s" % mod, ""]
        open(os.path.join(OUT, "WormKD/H/%s.lean" % mod), "w").write("\n".join(lines))
    # part aggregator
    L = ["import WormKC.Cov", "import WormKC.Lit", "import WormKD.Skel"] + ["import WormKD.H.P%05d_%03d" % (p, j) for j in range(len(holes))] + [
         "", "/-! Part %d: %d units, %d pieces (generated). -/" % (p, len(ubs), len(allpieces)), ""] + HDR + [
         "namespace WormKD.Part.P%05d" % p, "open WormCore WormCore.Sound WormCore.SoundK", ""]
    for k in range(len(allpieces)):
        mod, nb = hname[k]
        L.append("theorem cv%d : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_pieceOKK _ %s _ _ _ _ _ WormKD.H.%s.pc%d" % (k, nb, HT, mod, k))
    L.append("")
    for u, (top, ids) in enumerate(tops):
        rev = list(reversed(ids))
        sl = slices(rev)
        lists = ["[%s]" % ", ".join("K.decodeBox (nat_lit%% \"%d\")" % hname[k][1] for k in s) for s in sl]
        for si, s in enumerate(sl):
            L.append("theorem u%d_s%d : ∀ b ∈ %s, Cov b := %s" % (u, si, lists[si], forall_chain(["cv%d" % k for k in s])))
        outl = rnest(lists)
        proof = "u%d_s%d" % (u, len(sl) - 1)
        for si in reversed(range(len(sl) - 1)): proof = "List.forall_mem_append.mpr ⟨u%d_s%d, %s⟩" % (u, si, proof)
        L.append("theorem u%d : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_topOKK _ (nat_lit%% \"%d\") (%s) (by decide +kernel) (%s)" % (
            u, pack_box(ubs[u]), pack_codes(top), outl, proof))
    L.append("")
    usl = slices(list(range(len(ubs))))
    ulists = ["[%s]" % ", ".join("K.decodeBox (nat_lit%% \"%d\")" % pack_box(ubs[u]) for u in s) for s in usl]
    for si, s in enumerate(usl):
        L.append("theorem units_s%d : ∀ b ∈ %s, Cov b := %s" % (si, ulists[si], forall_chain(["u%d" % u for u in s])))
    proof = "units_s%d" % (len(usl) - 1)
    for si in reversed(range(len(usl) - 1)): proof = "List.forall_mem_append.mpr ⟨units_s%d, %s⟩" % (si, proof)
    L.append("theorem part : PartOK WormKD.skelOf %d := partOK_of WormKD.skelOf %d _ rfl (%s) (by decide +kernel) (%s)" % (
        p, p, rnest(ulists), proof))
    L += ["", "end WormKD.Part.P%05d" % p, ""]
    open(os.path.join(OUT, "WormKD/Part/P%05d.lean" % p), "w").write("\n".join(L))
    print("part %d: units %d pieces %d holes %d leaves %d" % (p, len(ubs), len(allpieces), len(holes),
          sum(len(x[3]) for x in allpieces)))

if __name__ == "__main__":
    if sys.argv[1] == "skel": gen_skel(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "part":
        gen_part(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]), sys.argv[8], sys.argv[9])

FINAL = {
    "": ["/-- **Theorem, kernel-only.** Every convex set that contains a rotated and translated copy of every",
         "unit arc has area at least `0.24`. -/",
         "theorem worm_lower_K : WormLowerM := wormLowerM_of_parts skelOf allParts",
         "",
         "/-- **Theorem, kernel-only**, for the least area. -/",
         "theorem optimalAreaM_lower_K : OptimalAreaLowerM := WormCore.Sound.optimalAreaLowerM_of worm_lower_K"],
    "2410": ["/-- **Theorem, kernel-only.** Every convex set that contains a rotated and translated copy of every",
             "unit arc has area at least `0.241`. -/",
             "theorem worm_lower_K : WormLowerAt (2410 / 10000) :=",
             "  wormLowerAt_of_parts (2410 / 10000) (by norm_num) WormCore.Sound.tau_2410_le WormCore.Sound.root_box_at",
             "    skelOf allParts",
             "",
             "/-- **Theorem, kernel-only**, for the least area. -/",
             "theorem optimalAreaM_lower_K : OptimalAreaLowerAt (2410 / 10000) := WormCore.Sound.optimalAreaLowerAt_of worm_lower_K"],
}

def gen_root(OUT, nparts=16384, bs=64):
    """Blocks of 64 parts, groups of 64 blocks, and the final theorem (plain files)."""
    os.makedirs(os.path.join(OUT, "WormKD/Root"), exist_ok=True)
    nb = nparts // bs
    for j in range(nb):
        L = ["import WormKC.Cov", "import WormKD.Skel"] + ["import WormKD.Part.P%05d" % (bs * j + i) for i in range(bs)] + [
             "", "/-! Parts %d..%d (generated). -/" % (bs * j, bs * j + bs - 1), ""] + HDR + [
             "namespace WormKD.Root", "open WormCore WormCore.SoundK", "",
             "theorem blk%03d : ∀ i < %d, PartOK WormKD.skelOf (%d * %d + i) := fun i hi =>" % (j, bs, bs, j),
             "  match i, hi with"]
        for i in range(bs):
            L.append("  | %d, _ => WormKD.Part.P%05d.part" % (i, bs * j + i))
        L += ["  | _ + %d, h => absurd h (by omega)" % bs, "", "end WormKD.Root", ""]
        open(os.path.join(OUT, "WormKD/Root/B%03d.lean" % j), "w").write("\n".join(L))
    ng = nb // bs
    for gi in range(ng):
        L = ["import WormKC.Cov", "import WormKD.Skel"] + ["import WormKD.Root.B%03d" % (bs * gi + j) for j in range(bs)] + [
             "", "/-! Blocks %d..%d (generated). -/" % (bs * gi, bs * gi + bs - 1), ""] + HDR + [
             "namespace WormKD.Root", "open WormCore WormCore.SoundK", "",
             "theorem grp%d : ∀ j < %d, ∀ i < %d, PartOK WormKD.skelOf (%d * (%d * %d + j) + i) := fun j hj =>" % (gi, bs, bs, bs, bs, gi),
             "  match j, hj with"]
        for j in range(bs):
            L.append("  | %d, _ => blk%03d" % (j, bs * gi + j))
        L += ["  | _ + %d, h => absurd h (by omega)" % bs, "", "end WormKD.Root", ""]
        open(os.path.join(OUT, "WormKD/Root/G%d.lean" % gi), "w").write("\n".join(L))
    L = ["import WormKC.Cov", "import WormKD.Skel"] + ["import WormKD.Root.G%d" % gi for gi in range(ng)] + [
         "", "/-! The kernel-only worm bound (generated). -/", ""] + HDR + [
         "namespace WormKD", "open WormCore WormCore.SoundK Worm", "",
         "theorem allParts : ∀ p < rootW.nparts, PartOK skelOf p := by",
         "  have hQ : ∀ j < %d * %d, ∀ i < %d, PartOK skelOf (%d * j + i) :=" % (bs, ng, bs, bs),
         "    forall_lt_of_blocks (P := fun j => ∀ i < %d, PartOK skelOf (%d * j + i)) %d %d (fun g hg =>" % (bs, bs, ng, bs),
         "      match g, hg with"]
    for gi in range(ng):
        L.append("      | %d, _ => Root.grp%d" % (gi, gi))
    L += ["      | _ + %d, h => absurd h (by omega))" % ng,
          "  have h := forall_lt_of_blocks (P := PartOK skelOf) (%d * %d) %d hQ" % (bs, ng, bs),
          "  intro p hp",
          "  have hn : rootW.nparts = %d := rfl" % nparts,
          "  exact h p (by omega)",
          "",
          ] + FINAL[TAU] + ["", "end WormKD", ""]
    open(os.path.join(OUT, "WormKD/Final.lean"), "w").write("\n".join(L))
    A = ["import WormKD.Final", "", "#print axioms WormKD.worm_lower_K", "#print axioms WormKD.optimalAreaM_lower_K", ""]
    open(os.path.join(OUT, "AXIOMS_K.lean"), "w").write("\n".join(A))

# per-kind kernel cost estimate (s/leaf, measured for the kernel leaf test); Lemma K records: 0.95 x sum of parts
KIND_COST = {('s', 3): 0.31, ('s', 4): 0.31, ('f', 4): 0.34, ('f', 5): 0.43, ('f', 6): 0.55, ('f', 7): 0.82,
             ('f', 8): 0.91, ('f', 9): 1.03, ('f', 10): 1.17, ('c', 4): 0.39, ('c', 5): 0.39, ('c', 6): 0.51,
             ('c', 7): 0.73, ('c', 8): 0.86, ('c', 9): 1.00, ('c', 10): 1.00}
def st_cost(tok):
    k = tok[0]; m = len(tok[1:].split('|')[0])
    return KIND_COST.get((k, m), 1.2 if m > 10 else 0.5)
def rec_cost(tok, table):
    if ',' in tok:
        return 0.95 * sum(st_cost(table[int(it.split(',')[0], 36)]) for it in tok.split(';'))
    return st_cost(table[int(tok, 36)])

def gen_holes_chunk(SNAP, CF, OUT, CAP, MAXL, MODCAP, LEAFT, tag):
    """timing mode: every unit of one (merged) chunk cut into pieces of at most CAP estimated kernel-seconds and
    MAXL leaves, grouped into hole modules of at most MODCAP estimated seconds (no part aggregators)."""
    g = Geo(SNAP)
    toks = open(CF).read().split(' ')
    n = int(toks[0][1:]); table = toks[1:n + 1]; i = n + 1
    pieces = []
    ubcache = {}
    sys.setrecursionlimit(100000)
    while i < len(toks):
        p, u = map(int, toks[i][1:].split('.')); codes = toks[i + 1][1:]
        nl = sum(1 for c in codes if c in 'LK'); rtoks = toks[i + 2:i + 2 + nl]; i += 2 + nl
        if p not in ubcache: ubcache[p] = g.unit_boxes(p)
        box0 = ubcache[p][u]
        costs = [rec_cost(t, table) for t in rtoks]
        # subtree (end, leaves, cost) by recursion
        rpos = [0]
        def sub(j):
            if codes[j] in 'LK': return j + 1, 1, costs[rpos_at[j]]
            a, na, ca = sub(j + 1); b, nb, cb = sub(a); return b, na + nb, ca + cb
        # map leaf code positions to record indices
        rpos_at = {}; r = 0
        for j, c in enumerate(codes):
            if c in 'LK': rpos_at[j] = r; r += 1
        def cut(j, box):
            e, nlv, cst = sub(j)
            if nlv <= MAXL and cst <= CAP:
                r0 = rpos_at[min(k for k in range(j, e) if codes[k] in 'LK')]
                pieces.append((box, codes[j:e], rtoks[r0:r0 + nlv], cst)); return e
            c = codes[j]
            if c in 'LK':   # single heavy leaf
                pieces.append((box, c, [rtoks[rpos_at[j]]], cst)); return j + 1
            a, b = halves(box[0], box[1], code_dim(c))
            return cut(cut(j + 1, a), b)
        assert cut(0, box0) == len(codes)
    # group into modules by estimated cost
    os.makedirs(os.path.join(OUT, "WormKD/T"), exist_ok=True)
    mods = []; cur = []; cc = 0.0
    for pc in pieces:
        if cur and cc + pc[3] > MODCAP: mods.append(cur); cur = []; cc = 0.0
        cur.append(pc); cc += pc[3]
    if cur: mods.append(cur)
    names = []
    for mi, mp in enumerate(mods):
        name = "%s_%04d" % (tag, mi)
        ridx = {}; rvals = []; body = []
        for k, (box, pc, rt, cst) in enumerate(mp):
            ix = []
            for t in rt:
                if t not in ridx: ridx[t] = len(rvals); rvals.append("%d" % pack_rec(t, table))
                ix.append(ridx[t])
            body.append("theorem pc%d : K.pieceOKK %s tab (nat_lit%% \"%d\") (nat_lit%% \"%d\") %d (nat_lit%% \"%d\") = true := by\n  decide +kernel" % (
                k, LEAFT, pack_box(box), pack_codes(pc), len(rt), pack_idx(ix)))
        lines = ["import WormKC.Lit", "import WormK.Walk3", "", "/-! timing module %s: %d pieces, %d leaves, est %.0f s -/" % (
                 name, len(mp), sum(len(x[2]) for x in mp), sum(x[3] for x in mp)), ""] + HDR + [
                 "namespace WormKD.T.%s" % name, "open WormCore", "",
                 "noncomputable def tab : K.BTree Nat := nat_btree% \"" + " ".join(rvals) + "\"", ""] + body + ["", "end WormKD.T.%s" % name, ""]
        open(os.path.join(OUT, "WormKD/T/%s.lean" % name), "w").write("\n".join(lines))
        names.append((name, len(mp), sum(len(x[2]) for x in mp), sum(x[3] for x in mp)))
    with open(os.path.join(OUT, "WormKD/T/%s.index.tsv" % tag), "w") as f:
        for nm in names: f.write("%s\t%d\t%d\t%.1f\n" % nm)
    print("%s: pieces %d modules %d leaves %d est %.0f s" % (tag, len(pieces), len(mods), sum(x[2] for x in names), sum(x[3] for x in names)))

if __name__ == "__main__" and sys.argv[1] == "holes":
    gen_holes_chunk(sys.argv[2], sys.argv[3], sys.argv[4], float(sys.argv[5]), int(sys.argv[6]), float(sys.argv[7]), sys.argv[8], sys.argv[9])

def cut_unit(codes, rtoks, table, box, CAP, MAXL):
    """Cut a unit's tree into pieces of at most CAP estimated kernel-seconds and MAXL leaves.
    Returns (top codes with 'P' at piece roots, [(box, piece codes, piece record tokens, est cost)])."""
    costs = [rec_cost(t, table) for t in rtoks]
    leafpos = {}; r = 0
    for j, c in enumerate(codes):
        if c in 'LK': leafpos[j] = r; r += 1
    # iterative subtree sizes: end index, leaf count, cost, first leaf record index, for every node
    n = len(codes); end = [0] * n; nl = [0] * n; cst = [0.0] * n
    stack = []
    for j in range(n - 1, -1, -1):
        if codes[j] in 'LK':
            end[j] = j + 1; nl[j] = 1; cst[j] = costs[leafpos[j]]; stack.append(j)
        else:
            a = stack.pop(); b = stack.pop()   # a = left child (starts at j+1), b = right child
            end[j] = end[b]; nl[j] = nl[a] + nl[b]; cst[j] = cst[a] + cst[b]; stack.append(j)
    assert len(stack) == 1 and stack[0] == 0
    top = []; pieces = []
    work = [(0, box)]
    while work:
        j, bx = work.pop()
        if nl[j] <= MAXL and (cst[j] <= CAP or codes[j] in 'LK'):
            r0 = leafpos[min(k for k in range(j, end[j]) if codes[k] in 'LK')] if codes[j] not in 'LK' else leafpos[j]
            pieces.append((bx, codes[j:end[j]], rtoks[r0:r0 + nl[j]], cst[j])); top.append('P'); continue
        c = codes[j]; top.append(c)
        a, b = halves(bx[0], bx[1], code_dim(c))
        left = j + 1; right = end[left]
        work.append((right, b)); work.append((left, a))   # left processed first (preorder)
    return ''.join(top), pieces

SUBMAX = int(os.environ.get("SUBMAX", "0"))
HOLE_IMPORT = os.environ.get("HOLE_IMPORT", "WormK.Walk3")   # module of the leaf test named in LEAFT
TAU = os.environ.get("TAU", "")                               # "" = the 0.24 statement; "2410" = WormLowerAt (2410/10000)
SALT = os.environ.get("SALT", "0") == "1"

def box_lit(b, t):
    """a box of a top-walk list; with SALT it carries the tag t (distinct within one list, < 65536) in its low 16 bits,
    so the literals of one declaration hash apart (see WormKC/Salt.lean)"""
    if SALT:
        assert 0 < t < 65536
        return "K.decodeBoxS (nat_lit%% \"%d\")" % (b * 65536 + t)
    return "K.decodeBox (nat_lit%% \"%d\")" % b

def cut_top(top, box, submax):
    """Cut a unit's top codes (split codes, 'P' at piece roots) at the highest nodes with at most `submax` pieces.
    Returns (upper codes with 'P' at sub-unit roots, [(box, sub-unit codes, first piece ordinal, piece count)] in preorder)."""
    n = len(top); end = [0] * n; npc = [0] * n; st = []
    for j in range(n - 1, -1, -1):
        if top[j] == 'P':
            end[j] = j + 1; npc[j] = 1; st.append(j)
        else:
            a = st.pop(); b = st.pop()
            end[j] = end[b]; npc[j] = npc[a] + npc[b]; st.append(j)
    assert len(st) == 1 and st[0] == 0
    pre = [0] * (n + 1)
    for j, c in enumerate(top): pre[j + 1] = pre[j] + (c == 'P')
    upper = []; subs = []
    work = [(0, box)]
    while work:
        j, bx = work.pop()
        if npc[j] <= submax:
            subs.append((bx, top[j:end[j]], pre[j], npc[j])); upper.append('P'); continue
        c = top[j]; upper.append(c)
        a, b = halves(bx[0], bx[1], code_dim(c))
        left = j + 1; right = end[left]
        work.append((right, b)); work.append((left, a))
    return ''.join(upper), subs

def gen_part_units(g, OUT, p, units, CAP, MAXL, MODCAP, LEAFT, HT):
    """units: {u: (codes, rtoks, table)}; writes hole modules H/P<p>_<j>.lean and Part/P<p>.lean"""
    ubs = g.unit_boxes(p)
    assert sorted(units) == list(range(len(ubs))), ("units", p, len(units), len(ubs))
    allp = []; tops = []
    for u in range(len(ubs)):
        codes, rtoks, table = units[u]
        top, pcs = cut_unit(codes, rtoks, table, ubs[u], CAP, MAXL)
        ids = []
        for pc in pcs: ids.append(len(allp)); allp.append((u,) + pc + (table,))
        tops.append((top, ids))
    # hole modules by estimated cost
    mods = []; cur = []; cc = 0.0
    for k, pc in enumerate(allp):
        if cur and cc + pc[4] > MODCAP: mods.append(cur); cur = []; cc = 0.0
        cur.append(k); cc += pc[4]
    if cur: mods.append(cur)
    os.makedirs(os.path.join(OUT, "WormKD/H"), exist_ok=True); os.makedirs(os.path.join(OUT, "WormKD/Part"), exist_ok=True)
    hname = {}; written = []
    for j, mk in enumerate(mods):
        mod = "P%05d_%03d" % (p, j)
        ridx = {}; rvals = []; body = []
        for k in mk:
            u, box, pc, rt, cst, table = allp[k]
            ix = []
            for t in rt:
                key = (id(table), t)
                if key not in ridx: ridx[key] = len(rvals); rvals.append("%d" % pack_rec(t, table))
                ix.append(ridx[key])
            nb = pack_box(box)
            body.append("theorem pc%d : K.pieceOKK %s tab (nat_lit%% \"%d\") (nat_lit%% \"%d\") %d (nat_lit%% \"%d\") = true := by\n  decide +kernel" % (
                k, LEAFT, nb, pack_codes(pc), len(rt), pack_idx(ix)))
            hname[k] = (mod, nb)
        est = sum(allp[k][4] for k in mk); nlv = sum(len(allp[k][3]) for k in mk)
        lines = ["import WormKC.Lit", "import " + HOLE_IMPORT, "", "/-! Part %d, hole module %d: %d pieces, %d leaves, est %.0f s (generated). -/" % (
                 p, j, len(mk), nlv, est), ""] + HDR + ["namespace WormKD.H.%s" % mod, "open WormCore", "",
                 "noncomputable def tab : K.BTree Nat := nat_btree% \"" + " ".join(rvals) + "\"", ""] + body + ["", "end WormKD.H.%s" % mod, ""]
        write_if_changed(os.path.join(OUT, "WormKD/H/%s.lean" % mod), "\n".join(lines))
        written.append((mod, len(mk), nlv, est))
    covimp = "import WormKC.BridgeK" if HT == "K" else "import WormKC.Cov"
    def cv_line(k, prefix):
        mod, nb = hname[k]
        if HT == "K":
            return "theorem %scv%d : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_pieceOKK_K _ _ _ _ _ WormKD.H.%s.pc%d" % (prefix, k, nb, mod, k)
        return "theorem %scv%d : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_pieceOKK _ %s _ _ _ _ _ WormKD.H.%s.pc%d" % (prefix, k, nb, HT, mod, k)
    def cover_lines(name, boxp, codes, items):
        """items: [(fact name, packed box)] in preorder -> sub-lemmas name_s<i> and `theorem name : Cov (decodeBox boxp)`"""
        out = []
        rev = list(reversed(items)); sl = slices(rev)
        lists = ["[%s]" % ", ".join(box_lit(b, 64 * si + i + 1) for i, (_, b) in enumerate(s_)) for si, s_ in enumerate(sl)]
        for si, s_ in enumerate(sl):
            out.append("theorem %s_s%d : ∀ b ∈ %s, Cov b := %s" % (name, si, lists[si], forall_chain([f for f, _ in s_])))
        proof = "%s_s%d" % (name, len(sl) - 1)
        for si in reversed(range(len(sl) - 1)): proof = "List.forall_mem_append.mpr ⟨%s_s%d, %s⟩" % (name, si, proof)
        out.append("theorem %s : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_topOKK _ (nat_lit%% \"%d\") (%s) (by decide +kernel) (%s)" % (
            name, boxp, pack_codes(codes), rnest(lists), proof))
        return out
    def unit_lines(u, top, ids, unit_name):
        items = [("cv%d" % k, hname[k][1]) for k in ids]
        if SUBMAX and len(ids) > SUBMAX:
            # big unit: one top walk per sub-unit of at most SUBMAX pieces, then a walk over the sub-unit boxes
            # (kernel cost of one walk grows faster than linearly in its box count)
            upper, subs = cut_top(top, ubs[u], SUBMAX)
            out = []; sitems = []
            for j, (bx, sc, p0, cnt) in enumerate(subs):
                if cnt == 1: sitems.append(items[p0]); continue
                nm = "%s_t%d" % (unit_name, j); bp = pack_box(bx)
                out += cover_lines(nm, bp, sc, items[p0:p0 + cnt]); sitems.append((nm, bp))
            return out + cover_lines(unit_name, pack_box(ubs[u]), upper, sitems)
        return cover_lines(unit_name, pack_box(ubs[u]), top, items)
    split = len(allp) > int(os.environ.get("SPLIT_PIECES", "2000"))
    unit_ref = {}
    if split:
        os.makedirs(os.path.join(OUT, "WormKD/PU"), exist_ok=True)
        # group consecutive units into unit modules of at most ~2,000 pieces (a bigger unit gets its own module)
        groups = []; cur = []; cn = 0
        for u, (top, ids) in enumerate(tops):
            if cur and cn + len(ids) > 2000: groups.append(cur); cur = []; cn = 0
            cur.append(u); cn += len(ids)
        if cur: groups.append(cur)
        gmods = []
        for gi, us in enumerate(groups):
            umod = "P%05d_G%04d" % (p, gi); gmods.append(umod)
            ids_all = [k for u in us for k in tops[u][1]]
            hmods = sorted(set(hname[k][0] for k in ids_all))
            U = [covimp, "import WormKC.Lit"] + (["import WormKC.Salt"] if SALT else []) + ["import WormKD.H.%s" % m for m in hmods] + [
                 "", "/-! Part %d, units %d..%d: %d pieces (generated). -/" % (p, us[0], us[-1], len(ids_all)), ""] + HDR + [
                 "namespace WormKD.PU.%s" % umod, "open WormCore WormCore.Sound WormCore.SoundK", ""]
            U += [cv_line(k, "") for k in ids_all] + [""]
            for u in us:
                U += unit_lines(u, tops[u][0], tops[u][1], "u%d" % u)
                unit_ref[u] = "WormKD.PU.%s.u%d" % (umod, u)
            U += ["", "end WormKD.PU.%s" % umod, ""]
            write_if_changed(os.path.join(OUT, "WormKD/PU/%s.lean" % umod), "\n".join(U))
        L = [covimp, "import WormKC.Lit"] + (["import WormKC.Salt"] if SALT else []) + ["import WormKD.Skel"] + ["import WormKD.PU.%s" % m for m in gmods] + [
             "", "/-! Part %d: %d units, %d pieces, unit covers in WormKD.PU (generated). -/" % (p, len(ubs), len(allp)), ""] + HDR + [
             "namespace WormKD.Part.P%05d" % p, "open WormCore WormCore.Sound WormCore.SoundK", ""]
    else:
        L = [covimp, "import WormKC.Lit"] + (["import WormKC.Salt"] if SALT else []) + ["import WormKD.Skel"] + ["import WormKD.H.P%05d_%03d" % (p, j) for j in range(len(mods))] + [
             "", "/-! Part %d: %d units, %d pieces (generated). -/" % (p, len(ubs), len(allp)), ""] + HDR + [
             "namespace WormKD.Part.P%05d" % p, "open WormCore WormCore.Sound WormCore.SoundK", ""]
        L += [cv_line(k, "") for k in range(len(allp))] + [""]
        for u, (top, ids) in enumerate(tops):
            L += unit_lines(u, top, ids, "u%d" % u)
            unit_ref[u] = "u%d" % u
    L.append("")
    usl = slices(list(range(len(ubs))))
    ulists = ["[%s]" % ", ".join(box_lit(pack_box(ubs[u]), 64 * si + i + 1) for i, u in enumerate(s_)) for si, s_ in enumerate(usl)]
    for si, s_ in enumerate(usl):
        L.append("theorem units_s%d : ∀ b ∈ %s, Cov b := %s" % (si, ulists[si], forall_chain([unit_ref[u] for u in s_])))
    proof = "units_s%d" % (len(usl) - 1)
    for si in reversed(range(len(usl) - 1)): proof = "List.forall_mem_append.mpr ⟨units_s%d, %s⟩" % (si, proof)
    L.append("theorem part : PartOK WormKD.skelOf %d := partOK_of WormKD.skelOf %d _ rfl (%s) (by decide +kernel) (%s)" % (
        p, p, rnest(ulists), proof))
    L += ["", "end WormKD.Part.P%05d" % p, ""]
    write_if_changed(os.path.join(OUT, "WormKD/Part/P%05d.lean" % p), "\n".join(L))
    return written, len(allp), sum(len(x[3]) for x in allp)

def write_if_changed(path, text):
    try:
        if open(path).read() == text: return False
    except FileNotFoundError:
        pass
    open(path, "w").write(text); return True

def gen_range(SNAP, MERGED, OUT, k, CAP, MAXL, MODCAP, LEAFT, HT):
    """parts 64k..64k+63 from the merged chunks that hold them (via data/manifest.json)"""
    import json
    g = Geo(SNAP)
    man = json.load(open(os.path.join(SNAP, "data/manifest.json")))
    lo, hi = 64 * k, 64 * k + 64
    names = [c["name"] for c in man["chunks"] if any(lo <= pu[0] < hi for pu in c["units"])]
    units = {}
    for nm in names:
        toks = open(os.path.join(MERGED, nm + ".txt")).read().split(' ')
        n = int(toks[0][1:]); table = toks[1:n + 1]; i = n + 1
        while i < len(toks):
            pp, u = map(int, toks[i][1:].split('.')); codes = toks[i + 1][1:]
            nlv = sum(1 for c in codes if c in 'LK')
            if lo <= pp < hi: units.setdefault(pp, {})[u] = (codes, toks[i + 2:i + 2 + nlv], table)
            i += 2 + nlv
    idx = []
    for p in range(lo, hi):
        written, npc, nlv = gen_part_units(g, OUT, p, units.get(p, {}), CAP, MAXL, MODCAP, LEAFT, HT)
        idx += ["%s\t%d\t%d\t%.1f" % w for w in written]
    os.makedirs(os.path.join(OUT, "index"), exist_ok=True)
    open(os.path.join(OUT, "index/range_%03d.tsv" % k), "w").write("\n".join(idx) + "\n")
    print("range %d: chunks %d hole modules %d" % (k, len(names), len(idx)))

if __name__ == "__main__" and sys.argv[1] == "range":
    gen_range(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7]), float(sys.argv[8]), sys.argv[9], sys.argv[10])

if __name__ == "__main__" and sys.argv[1] == "part1":
    # part1 SNAP MERGEDDIR OUT P CAP MAXL MODCAP LEAFT HT
    g = Geo(sys.argv[2]); p = int(sys.argv[5])
    units = read_units(sys.argv[3], p)
    w, npc, nl = gen_part_units(g, sys.argv[4], p, units, float(sys.argv[6]), int(sys.argv[7]), float(sys.argv[8]), sys.argv[9], sys.argv[10])
    print("part %d: hole modules %d pieces %d leaves %d" % (p, len(w), npc, nl))

if __name__ == "__main__" and sys.argv[1] == "unit1":
    # unit1 SNAP CHUNKFILE UNITINDEX OUT CAP MAXL MODCAP  -> hole module(s) + a unit cover test (the proof's leaf test)
    g = Geo(sys.argv[2]); CF = sys.argv[3]; UI = int(sys.argv[4]); OUT = sys.argv[5]
    CAP, MAXL, MODCAP = float(sys.argv[6]), int(sys.argv[7]), float(sys.argv[8])
    toks = open(CF).read().split(' '); n = int(toks[0][1:]); table = toks[1:n + 1]; i = n + 1; k = 0
    while True:
        p, u = map(int, toks[i][1:].split('.')); codes = toks[i + 1][1:]; nl = sum(1 for c in codes if c in 'LK')
        if k == UI: rtoks = toks[i + 2:i + 2 + nl]; break
        i += 2 + nl; k += 1
    box = g.unit_boxes(p)[u]
    top, pcs = cut_unit(codes, rtoks, table, box, CAP, MAXL)
    os.makedirs(os.path.join(OUT, "WormKD/U"), exist_ok=True)
    ridx = {}; rvals = []; body = []
    for j, (bx, pc, rt, cst) in enumerate(pcs):
        ix = []
        for t in rt:
            if t not in ridx: ridx[t] = len(rvals); rvals.append("%d" % pack_rec(t, table))
            ix.append(ridx[t])
        body.append("theorem pc%d : K.pieceOKK (WormK3.leafOKRK famW maxsmallW tauHiW) tab (nat_lit%% \"%d\") (nat_lit%% \"%d\") %d (nat_lit%% \"%d\") = true := by\n  decide +kernel" % (
            j, pack_box(bx), pack_codes(pc), len(rt), pack_idx(ix)))
    H = ["import WormKC.Lit", "import WormK.Walk3", ""] + HDR + ["namespace WormKD.U.H", "open WormCore", "",
         "noncomputable def tab : K.BTree Nat := nat_btree% \"" + " ".join(rvals) + "\"", ""] + body + ["", "end WormKD.U.H", ""]
    open(os.path.join(OUT, "WormKD/U/H.lean"), "w").write("\n".join(H))
    ids = list(range(len(pcs))); rev = list(reversed(ids)); sl = slices(rev)
    lists = ["[%s]" % ", ".join("K.decodeBox (nat_lit%% \"%d\")" % pack_box(pcs[k][0]) for k in s) for s in sl]
    L = ["import WormKC.BridgeK", "import WormKC.Lit", "import WormKD.U.H", ""] + HDR + ["namespace WormKD.U.T",
         "open WormCore WormCore.Sound WormCore.SoundK", ""]
    for k in ids:
        L.append("theorem cv%d : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_pieceOKK_K _ _ _ _ _ WormKD.U.H.pc%d" % (k, pack_box(pcs[k][0]), k))
    for si, s in enumerate(sl):
        L.append("theorem s%d : ∀ b ∈ %s, Cov b := %s" % (si, lists[si], forall_chain(["cv%d" % k for k in s])))
    proof = "s%d" % (len(sl) - 1)
    for si in reversed(range(len(sl) - 1)): proof = "List.forall_mem_append.mpr ⟨s%d, %s⟩" % (si, proof)
    L.append("theorem unit_cov : Cov (K.decodeBox (nat_lit%% \"%d\")) := cov_of_topOKK _ (nat_lit%% \"%d\") (%s) (by decide +kernel) (%s)" % (
        pack_box(box), pack_codes(top), rnest(lists), proof))
    L += ["", "#print axioms unit_cov", "", "end WormKD.U.T", ""]
    open(os.path.join(OUT, "WormKD/U/T.lean"), "w").write("\n".join(L))
    print("unit %d.%d: leaves %d pieces %d slices %d" % (p, u, len(rtoks), len(pcs), len(sl)))

if __name__ == "__main__" and sys.argv[1] == "root":
    gen_root(sys.argv[2])
