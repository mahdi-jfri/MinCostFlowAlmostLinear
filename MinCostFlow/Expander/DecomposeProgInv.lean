module

public import MinCostFlow.Expander.DecomposeProgHelpers
public import MinCostFlow.Spanner.ToolContracts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic Word RAM `DecomposeImpl` (Theorem 8.5, Theorem B.1, Algorithm 5)

Assembles `decomposeStepBody`, `decomposeLevelLoop`, `decomposeEntry`, and `decomposeProcs`,
proves multi-level loop preservation into `decompProp_of_multiLevel`, and constructs the
deterministic `decomposeImpl : Cited.ExpanderDecomposition → Spanner.DecomposeImpl` meeting
`Spanner.decomposeHeapContract` with `c_ℓ = 1`, `φ_lb m = 1 / maxPhiDenOf K_nat thr m`, and
`decFactor = subpolyB1 C₀_cost`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section

/-! ## 1. Expression Helpers, Partition Lemmas, and Sparse Fast Path -/

lemma dp_ev_eq_of {w : ℕ} {st : State} {e : Expr} {x y : ℕ}
    (h1 : Expr.eval w st e = some x) (h2 : x = y) : Expr.eval w st e = some y :=
  h2 ▸ h1

lemma dp_ev_const {w : ℕ} {st : State} {k : ℕ} (hk : k < 2 ^ w) :
    Expr.eval w st (.const k) = some k := by simp [Expr.eval, hk]

lemma dp_ev_reg {w : ℕ} {st : State} {r v : ℕ} (hv : st.regs r = v) :
    Expr.eval w st (.reg r) = some v := by simp [Expr.eval, hv]

lemma dp_ev_add {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x + y < 2 ^ w) :
    Expr.eval w st (.bin .add a b) = some (x + y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma dp_ev_sub {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x - y < 2 ^ w) :
    Expr.eval w st (.bin .sub a b) = some (x - y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma dp_ev_mul {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x * y < 2 ^ w) :
    Expr.eval w st (.bin .mul a b) = some (x * y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma dp_ev_div {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x / y < 2 ^ w) :
    Expr.eval w st (.bin .div a b) = some (x / y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma dp_ev_lt {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (h1w : 1 < 2 ^ w) :
    Expr.eval w st (.bin .lt a b) = some (if x < y then 1 else 0) := by
  have hlt : (if x < y then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  simp [Expr.eval, BinOp.eval, ha, hb, hlt]

lemma dp_ev_load {w : ℕ} {st : State} {a : Expr} {x v : ℕ}
    (ha : Expr.eval w st a = some x) (hv : st.mem x = v) :
    Expr.eval w st a.load = some v := by
  simp [Expr.eval, ha, hv]

lemma edges_map_filter {α : Type*} (f : ℕ → α) (d : α) (idx : List ℕ)
    (len : ℕ) (hlen : idx.length = len) (p : ℕ → Bool) :
    List.map (fun t => (List.map f idx).getD t d) (List.filter p (List.range len)) =
      List.map f (List.map (fun t => idx.getD t 0) (List.filter p (List.range len))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have htr : t ∈ List.range len := (List.mem_filter.mp ht).1
  have htl : t < idx.length := hlen ▸ List.mem_range.mp htr
  simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem htl]

lemma mem_kept_rem_partition {idx : List ℕ} {len : ℕ} (hlen : idx.length = len)
    (hnodup : idx.Nodup) (p : ℕ → Bool) :
    let rem := List.map (fun t => idx.getD t 0) (List.filter (fun t => !p t) (List.range len))
    let kept := List.map (fun t => idx.getD t 0) (List.filter (fun t => p t) (List.range len))
    (∀ a ∈ rem, a ∈ idx ∧ a ∉ kept) ∧
    (∀ a ∈ kept, a ∈ idx ∧ a ∉ rem) ∧
    (∀ a ∈ idx, a ∈ rem ∨ a ∈ kept) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
    have ht' := List.mem_filter.mp ht
    have htl : t < idx.length := hlen ▸ List.mem_range.mp ht'.1
    have ha_idx : idx.getD t 0 ∈ idx := by
      simp [List.getD, List.getElem?_eq_getElem htl]
    refine ⟨ha_idx, ?_⟩
    intro hk
    rcases List.mem_map.mp hk with ⟨s, hs, hseq⟩
    have hs' := List.mem_filter.mp hs
    have hsl : s < idx.length := hlen ▸ List.mem_range.mp hs'.1
    have heq : idx[s] = idx[t] := by
      simpa [List.getD, List.getElem?_eq_getElem hsl, List.getElem?_eq_getElem htl] using hseq
    have hst : s = t := (List.Nodup.getElem_inj_iff hnodup).mp heq
    subst hst
    rcases ht' with ⟨_, hnt⟩
    rcases hs' with ⟨_, hps⟩
    simp_all
  · intro a ha
    rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
    have ht' := List.mem_filter.mp ht
    have htl : t < idx.length := hlen ▸ List.mem_range.mp ht'.1
    have ha_idx : idx.getD t 0 ∈ idx := by
      simp [List.getD, List.getElem?_eq_getElem htl]
    refine ⟨ha_idx, ?_⟩
    intro hr
    rcases List.mem_map.mp hr with ⟨s, hs, hseq⟩
    have hs' := List.mem_filter.mp hs
    have hsl : s < idx.length := hlen ▸ List.mem_range.mp hs'.1
    have heq : idx[s] = idx[t] := by
      simpa [List.getD, List.getElem?_eq_getElem hsl, List.getElem?_eq_getElem htl] using hseq
    have hst : s = t := (List.Nodup.getElem_inj_iff hnodup).mp heq
    subst hst
    rcases ht' with ⟨_, hpt⟩
    rcases hs' with ⟨_, hns⟩
    simp_all
  · intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨t, htl, rfl⟩
    have htr : t ∈ List.range len := List.mem_range.mpr (hlen ▸ htl)
    have hget : idx.getD t 0 = idx[t] := by
      simp [List.getD, List.getElem?_eq_getElem htl]
    by_cases hpt : p t = true
    · exact Or.inr (List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨htr, hpt⟩, hget⟩)
    · refine Or.inl (List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨htr, ?_⟩, hget⟩)
      simp [hpt]

lemma decomposeProp_zero_of_le (G : Cited.Graph) (hmn : G.m ≤ G.n) :
    Spanner.DecomposeProp 1 G (Spanner.mkDecomposeOutput 0 (List.replicate G.m 0) []) 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Spanner.mkDecomposeOutput, Nat.cast_zero, one_mul]; positivity
  · intro j hj
    simp [Spanner.mkDecomposeOutput, List.getD, List.getElem?_replicate, hj]
  · intro i hi
    simp only [Spanner.mkDecomposeOutput] at hi
    obtain rfl : i = 0 := by omega
    simp only [Cited.Graph.m, Spanner.DecomposeOutput.graphAt, List.length_map,
      Spanner.DecomposeOutput.edgesAt, pow_zero, one_mul]
    have hm' : (List.range G.m).length ≤ G.n := by simpa [List.length_range] using hmn
    exact le_trans (List.length_filter_le _ _) hm'
  · intro i hi0 hi0'
    simp only [Spanner.mkDecomposeOutput] at hi0'
    omega

lemma one_le_n_of_lt {G : Cited.Graph} (hV : G.IsValid) (hlt : G.n < G.m) : 1 ≤ G.n := by
  by_contra hn
  have h0 : G.n = 0 := by omega
  have hne : G.edges ≠ [] := by
    intro he
    have hm0 : G.m = 0 := by simp [Cited.Graph.m, he]
    omega
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil G.edges hne
  have := (hV e he).1
  omega

/-! ## 2. Procedures, Program Assembly, and Determinism -/

@[expose] def decomposeStepBody (b_lvl : ℕ) : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.reg rLvl))) (.load (.reg rStatePtr))
    , .call rRet b_lvl
        [ .reg rCurG, .reg rCurIdx, .reg rNextG, .reg rNextIdx
        , .reg rLvlArr, .reg rTw, .reg rBuf, .reg rWork, .reg rKept
        , .reg rStatePtr, .reg rLvl, .reg rD, .reg rDphi, .reg rM ]
    , .store (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.reg rLvl)) (.const 1)))
        (.load (.reg rStatePtr))
    , .assign rTmp1 (.reg rCurG)
    , .assign rCurG (.reg rNextG)
    , .assign rNextG (.reg rTmp1)
    , .assign rTmp1 (.reg rCurIdx)
    , .assign rCurIdx (.reg rNextIdx)
    , .assign rNextIdx (.reg rTmp1)
    , .assign rLvl (.bin .sub (.reg rLvl) (.const 1))
    , .assign rD (.bin .div (.reg rD) (.const 2)) ]

lemma decomposeStepBody_noRand (b_lvl : ℕ) : (decomposeStepBody b_lvl).NoRand := by
  simp [decomposeStepBody, seqStmts, Stmt.NoRand]

@[expose] def decomposeLevelLoop (b_lvl : ℕ) : Stmt :=
  .loop (.bin .lt (.const 0) (.reg rLvl)) (decomposeStepBody b_lvl)

lemma decomposeLevelLoop_noRand (b_lvl : ℕ) : (decomposeLevelLoop b_lvl).NoRand := by
  simp [decomposeLevelLoop, Stmt.NoRand, decomposeStepBody_noRand]

@[expose] def decomposeEntry (K_nat thr b_lvl : ℕ) : Stmt :=
  seqStmts
    [ .assign rN (.load (.reg rGAddr))
    , .assign rM (.load (.bin .add (.reg rGAddr) (.const 1)))
    , .cond (.bin .lt (.reg rN) (.reg rM))
        (seqStmts
          [ computePhiDenStmt K_nat thr rM rDphi rTmp1 rTmp2 rTmp3 rTmp4 rTmp5
          , computeEllStmt
          , computeLayoutStmt
          , initMemoryStmt
          , decomposeLevelLoop b_lvl
          , packOutputStmt ])
        sparseFastPathStmt ]

lemma decomposeEntry_noRand (K_nat thr b_lvl : ℕ) : (decomposeEntry K_nat thr b_lvl).NoRand := by
  simp [decomposeEntry, seqStmts, Stmt.NoRand, computePhiDenStmt_noRand,
    computeEllStmt_noRand, computeLayoutStmt_noRand, initMemoryStmt_noRand,
    decomposeLevelLoop_noRand, packOutputStmt_noRand, sparseFastPathStmt_noRand]

@[expose] def decomposeProcs (K_nat thr : ℕ) (P : Program) (c b : ℕ) : List Stmt :=
  [ decomposeEntry K_nat thr (b + 11)
  , buildCsrProc
  , bfsLabelsProc
  , siftDownProc
  , heapSortProc (b + 3)
  , dedupProc
  , binSearchProc
  , groupVertsProc (b + 4) (b + 5) (b + 6)
  , groupEdgesProc
  , pruneWrapProc
  , partPruneProc (b + 1) (b + 9)
  , levelProc (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr ] ++
  runner (stripRandProg P) c (b + 12)

lemma decomposeProcs_length_pos (K_nat thr : ℕ) (P : Program) (c b : ℕ) :
    0 < (decomposeProcs K_nat thr P c b).length := by
  simp [decomposeProcs]

lemma decomposeProcs_noRand (K_nat thr : ℕ) (P : Program) (c b : ℕ) :
    ∀ s ∈ decomposeProcs K_nat thr P c b, s.NoRand := by
  intro s hs
  simp only [decomposeProcs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hs
  · exact decomposeEntry_noRand K_nat thr (b + 11)
  · exact buildCsrProc_noRand
  · exact bfsLabelsProc_noRand
  · exact siftDownProc_noRand
  · exact heapSortProc_noRand (b + 3)
  · exact dedupProc_noRand
  · exact binSearchProc_noRand
  · exact groupVertsProc_noRand (b + 4) (b + 5) (b + 6)
  · exact groupEdgesProc_noRand
  · exact pruneWrapProc_noRand
  · exact partPruneProc_noRand (b + 1) (b + 9)
  · exact levelProc_noRand (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr
  · exact runner_noRand (stripRandProg_isDeterministic P) c (b + 12) s hs

lemma hasAt_singleton_of_getElem {p : Program} {b : ℕ} {s : Stmt}
    (h : p.procs[b]? = some s) : p.HasAt b [s] := by
  intro i hi
  obtain rfl : i = 0 := by simp at hi; omega
  simpa using h

structure DecompProgContracts (K_nat thr : ℕ) (P : Program) (c w b : ℕ) (p : Program) : Prop where
  hEntry : p.procs[b]? = some (decomposeEntry K_nat thr (b + 11))
  hCsr : MeetsContract w p (b + 1) (buildCsrContract w)
  hBfs : MeetsContract w p (b + 2) (bfsLabelsContract w)
  hGv : MeetsContract w p (b + 7) (groupVertsContract w)
  hGe : MeetsContract w p (b + 8) (groupEdgesContract w)
  hPrune : p.procs[b + 9]? = some pruneWrapProc
  hPart : p.procs[b + 10]? = some (partPruneProc (b + 1) (b + 9))
  hLvl : p.procs[b + 11]? = some (levelProc (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr)
  hRun : p.HasAt (b + 12) (runner (stripRandProg P) c (b + 12))

lemma mkDecompProgContracts (K_nat thr : ℕ) (P : Program) (c w b : ℕ) (p : Program)
    (hHas : p.HasAt b (decomposeProcs K_nat thr P c b)) :
    DecompProgContracts K_nat thr P c w b p := by
  have hget : ∀ {i : ℕ} (hi : i < 12),
      p.procs[b + i]? = some ((decomposeProcs K_nat thr P c b)[i]'(by simp [decomposeProcs]; omega)) :=
    fun {i} hi => hHas.get (by simp [decomposeProcs]; omega)
  have h0 : p.procs[b]? = some (decomposeEntry K_nat thr (b + 11)) := by
    simpa [decomposeProcs] using hget (i := 0) (by omega)
  have h1 : p.procs[b + 1]? = some buildCsrProc := by
    simpa [decomposeProcs] using hget (i := 1) (by omega)
  have h2 : p.procs[b + 2]? = some bfsLabelsProc := by
    simpa [decomposeProcs] using hget (i := 2) (by omega)
  have h3 : p.procs[b + 3]? = some siftDownProc := by
    simpa [decomposeProcs] using hget (i := 3) (by omega)
  have h4 : p.procs[b + 4]? = some (heapSortProc (b + 3)) := by
    simpa [decomposeProcs] using hget (i := 4) (by omega)
  have h5 : p.procs[b + 5]? = some dedupProc := by
    simpa [decomposeProcs] using hget (i := 5) (by omega)
  have h6 : p.procs[b + 6]? = some binSearchProc := by
    simpa [decomposeProcs] using hget (i := 6) (by omega)
  have h7 : p.procs[b + 7]? = some (groupVertsProc (b + 4) (b + 5) (b + 6)) := by
    simpa [decomposeProcs] using hget (i := 7) (by omega)
  have h8 : p.procs[b + 8]? = some groupEdgesProc := by
    simpa [decomposeProcs] using hget (i := 8) (by omega)
  have h9 : p.procs[b + 9]? = some pruneWrapProc := by
    simpa [decomposeProcs] using hget (i := 9) (by omega)
  have h10 : p.procs[b + 10]? = some (partPruneProc (b + 1) (b + 9)) := by
    simpa [decomposeProcs] using hget (i := 10) (by omega)
  have h11 : p.procs[b + 11]? =
      some (levelProc (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr) := by
    simpa [decomposeProcs] using hget (i := 11) (by omega)
  have hCsr : MeetsContract w p (b + 1) (buildCsrContract w) :=
    buildCsr_spec (hasAt_singleton_of_getElem h1)
  have hBfs : MeetsContract w p (b + 2) (bfsLabelsContract w) :=
    bfsLabels_spec w p (b + 2) (hasAt_singleton_of_getElem h2)
  have hSort : MeetsContract w p (b + 4) (heapSortContract w) :=
    heapSort_spec (hasAt_singleton_of_getElem h3) (hasAt_singleton_of_getElem h4)
  have hDedup : MeetsContract w p (b + 5) (dedupContract w) :=
    dedup_spec (hasAt_singleton_of_getElem h5)
  have hBs : MeetsContract w p (b + 6) (binSearchContract w) :=
    binSearch_spec (hasAt_singleton_of_getElem h6)
  have hGv : MeetsContract w p (b + 7) (groupVertsContract w) :=
    groupVerts_spec h7 hSort hDedup hBs
  have hGe : MeetsContract w p (b + 8) (groupEdgesContract w) :=
    groupEdges_spec h8
  have hRun : p.HasAt (b + 12) (runner (stripRandProg P) c (b + 12)) := by
    intro j hj
    have hj' : 12 + j < (decomposeProcs K_nat thr P c b).length := by
      simp [decomposeProcs]; omega
    have h := hHas.get hj'
    have hlen : ([decomposeEntry K_nat thr (b + 11), buildCsrProc, bfsLabelsProc, siftDownProc,
        heapSortProc (b + 3), dedupProc, binSearchProc,
        groupVertsProc (b + 4) (b + 5) (b + 6), groupEdgesProc, pruneWrapProc,
        partPruneProc (b + 1) (b + 9),
        levelProc (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr] : List _).length = 12 := by simp
    have hget' : (decomposeProcs K_nat thr P c b)[12 + j]'hj' =
        (runner (stripRandProg P) c (b + 12))[j]'hj := by
      simp only [decomposeProcs]
      rw [List.getElem_append_right (by rw [hlen]; omega)]
      simp only [hlen, Nat.add_sub_cancel_left]
    rw [hget'] at h
    simpa [Nat.add_assoc] using h
  exact ⟨h0, hCsr, hBfs, hGv, hGe, h9, h10, h11, hRun⟩

/-! ## 3. Multi-Level Loop Invariant and Preservation -/

@[expose] def curAddrs (L : DecompLayout) (done : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if done % 2 = 0 then (L.g0Addr, L.idx0Addr, L.g1Addr, L.idx1Addr)
  else (L.g1Addr, L.idx1Addr, L.g0Addr, L.idx0Addr)

lemma curAddrs_flip (L : DecompLayout) {k ℓ : ℕ} (hk : k + 1 ≤ ℓ) :
    let ca := curAddrs L (ℓ - (k + 1))
    let cb := curAddrs L (ℓ - k)
    cb = (ca.2.2.1, ca.2.2.2, ca.1, ca.2.1) := by
  have heq : ℓ - k = ℓ - (k + 1) + 1 := by omega
  dsimp only [curAddrs]
  rw [heq]
  by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp, Nat.add_mod]; omega

structure DecompLayoutBounds (L : DecompLayout) (h n m D_phi : ℕ) : Prop where
  hsp : L.statePtr = h + 4 + 5 * m
  hbnd : L.boundsAddr = L.statePtr + 3
  hlvl : L.lvlArrAddr = L.boundsAddr + 2 * m + 6
  hg0 : L.g0Addr = L.lvlArrAddr + m
  hi0 : L.idx0Addr = L.g0Addr + 2 + 2 * m
  hg1 : L.g1Addr = L.idx0Addr + m
  hi1 : L.idx1Addr = L.g1Addr + 2 + 2 * m
  htw : L.twAddr = L.idx1Addr + m
  hbuf : L.bufAddr = L.twAddr + 6 + 8 * n + 18 * m
  hwork : L.workAddr = L.bufAddr + groupBufSize n m
  hkept : L.keptVertAddr = L.workAddr + partWorkSize n m (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m + 1) + 1) + 2)
  har : L.arena₀ = L.keptVertAddr + n
  hzc : L.zeroCursor₀ = L.arena₀ + 4 * m

lemma mkDecompLayout_bounds (h n m D_phi : ℕ) :
    DecompLayoutBounds (mkDecompLayout h n m D_phi) h n m D_phi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma bounds_idx_ne {base a b : ℕ} (h : a < b) :
    base + 2 * b ≠ base + 2 * a ∧
    base + 2 * b ≠ base + 2 * a + 1 ∧
    base + 2 * b + 1 ≠ base + 2 * a ∧
    base + 2 * b + 1 ≠ base + 2 * a + 1 := by omega

lemma bnd_lt_lvl {b lvlAddr m x : ℕ} (hl : lvlAddr = b + 2 * m + 6) (hx : x ≤ m) :
    b + 2 * x + 1 < lvlAddr := by omega

lemma decompLayout_h_le {L : DecompLayout} {h n m D_phi : ℕ}
    (hb : DecompLayoutBounds L h n m D_phi) :
    h ≤ L.statePtr ∧ h ≤ L.boundsAddr ∧ h ≤ L.lvlArrAddr ∧
    h ≤ L.twAddr ∧ h ≤ L.keptVertAddr ∧ h ≤ L.zeroCursor₀ := by
  have := hb.hsp; have := hb.hbnd; have := hb.hlvl; have := hb.hg0; have := hb.hi0
  have := hb.hg1; have := hb.hi1; have := hb.htw; have := hb.hbuf; have := hb.hwork
  have := hb.hkept; have := hb.har; have := hb.hzc
  omega

lemma not_mem_interval_of_lt {a h lo hi : ℕ} (ha : a < h) (hle : h ≤ lo) :
    ¬(lo ≤ a ∧ a < hi) :=
  fun ⟨hge, _⟩ => absurd hge (not_le_of_gt (lt_of_lt_of_le ha hle))

lemma decompLayout_lvl_le_ar {L : DecompLayout} {h n m D_phi : ℕ}
    (hb : DecompLayoutBounds L h n m D_phi) :
    L.lvlArrAddr ≤ L.arena₀ := by
  have h1 := hb.hg0; have h2 := hb.hi0; have h3 := hb.hg1; have h4 := hb.hi1
  have h5 := hb.htw; have h6 := hb.hbuf; have h7 := hb.hwork; have h8 := hb.hkept; have h9 := hb.har
  omega

lemma hrecs_shift {G : Cited.Graph} {D_phi k j : ℕ} {rec : DecompLevelRec}
    (h : let lvl := k + 1 + j + 1;
      rec.lvl = lvl ∧
      (∀ comp ∈ rec.rawComps,
          comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
      List.map (fun c => c.2.toFinset) rec.rawComps = rec.validRs ∧
      rec.keptIdx.Pairwise (· < ·) ∧
      (∀ a ∈ rec.keptIdx, a < G.m) ∧
      rec.Gi.n = G.n ∧
      rec.Gi.edges = List.map (fun t => G.edges.getD t (0, 0)) rec.keptIdx ∧
      rec.Gi.m ≤ 2 ^ lvl * G.n ∧
      rec.validRs.Pairwise Disjoint ∧
      (∀ R ∈ rec.validRs,
          R ⊆ G.verts ∧ 2 ≤ R.card ∧
          rec.Gi.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          (∀ x ∈ R, 1 / (3 * (D_phi : ℝ)) * 2 ^ lvl ≤ ↑(rec.Gi.degIn R x)) ∧
          ∀ e ∈ rec.Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
      ∀ e ∈ rec.Gi.edges, ∃ R ∈ rec.validRs, e.1 ∈ R ∧ e.2 ∈ R) :
    let lvl := k + (j + 1) + 1;
    rec.lvl = lvl ∧
    (∀ comp ∈ rec.rawComps,
        comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
    List.map (fun c => c.2.toFinset) rec.rawComps = rec.validRs ∧
    rec.keptIdx.Pairwise (· < ·) ∧
    (∀ a ∈ rec.keptIdx, a < G.m) ∧
    rec.Gi.n = G.n ∧
    rec.Gi.edges = List.map (fun t => G.edges.getD t (0, 0)) rec.keptIdx ∧
    rec.Gi.m ≤ 2 ^ lvl * G.n ∧
    rec.validRs.Pairwise Disjoint ∧
    (∀ R ∈ rec.validRs,
        R ⊆ G.verts ∧ 2 ≤ R.card ∧
        rec.Gi.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
        (∀ x ∈ R, 1 / (3 * (D_phi : ℝ)) * 2 ^ lvl ≤ ↑(rec.Gi.degIn R x)) ∧
        ∀ e ∈ rec.Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
    ∀ e ∈ rec.Gi.edges, ∃ R ∈ rec.validRs, e.1 ∈ R ∧ e.2 ∈ R := by
  have hkeq : k + (j + 1) + 1 = k + 1 + j + 1 := by
    rw [Nat.add_assoc k 1 j, Nat.add_comm 1 j]
  dsimp only at h ⊢
  rwa [hkeq]

lemma hbounds_head {L : DecompLayout} {k arena arena₁ : ℕ} {rawComps : List (ℕ × List ℕ)}
    {st4 st_lvl : State}
    (harena_ge1 : arena ≤ arena₁) (harena_ge : L.arena₀ ≤ arena)
    (harena_eq : arena₁ = arena + (List.flatMap compRecord rawComps).length)
    (ha0 : st4.mem (L.boundsAddr + 2 * (k + 1)) = arena)
    (ha1 : st4.mem (L.boundsAddr + 2 * (k + 1) + 1) = arena₁)
    (hlist : ∀ q < (List.flatMap compRecord rawComps).length,
      st4.mem (arena + q) = st_lvl.mem (arena + q))
    (hlist_ar : ListAt st_lvl.mem arena (List.flatMap compRecord rawComps)) :
    let lvl := k + 0 + 1
    let a0 := st4.mem (L.boundsAddr + 2 * lvl)
    let a1 := st4.mem (L.boundsAddr + 2 * lvl + 1)
    L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena₁ ∧
      a1 - a0 = (List.flatMap compRecord rawComps).length ∧
      ListAt st4.mem a0 (List.flatMap compRecord rawComps) := by
  dsimp only
  rw [Nat.add_zero, ha0, ha1]
  refine ⟨harena_ge, harena_ge1, le_rfl, by omega, ?_⟩
  intro q hq
  rw [hlist q hq]
  exact hlist_ar q hq

lemma hbounds_tail {L : DecompLayout} {k j arena arena₁ : ℕ} {rawComps : List (ℕ × List ℕ)}
    {st st4 : State}
    (harena_ge1 : arena ≤ arena₁)
    (hb_rec :
      let lvl := k + 1 + j + 1
      let a0 := st.mem (L.boundsAddr + 2 * lvl)
      let a1 := st.mem (L.boundsAddr + 2 * lvl + 1)
      L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena ∧
        a1 - a0 = (List.flatMap compRecord rawComps).length ∧
        ListAt st.mem a0 (List.flatMap compRecord rawComps))
    (ha0 : st4.mem (L.boundsAddr + 2 * (k + (j + 1) + 1)) = st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)))
    (ha1 : st4.mem (L.boundsAddr + 2 * (k + (j + 1) + 1) + 1) =
        st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1) + 1))
    (hlist : ∀ q < (List.flatMap compRecord rawComps).length,
      st4.mem (st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q) =
        st.mem (st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q)) :
    let lvl := k + (j + 1) + 1
    let a0 := st4.mem (L.boundsAddr + 2 * lvl)
    let a1 := st4.mem (L.boundsAddr + 2 * lvl + 1)
    L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena₁ ∧
      a1 - a0 = (List.flatMap compRecord rawComps).length ∧
      ListAt st4.mem a0 (List.flatMap compRecord rawComps) := by
  dsimp only at hb_rec ⊢
  rw [ha0, ha1]
  refine ⟨hb_rec.1, hb_rec.2.1, le_trans hb_rec.2.2.1 harena_ge1, hb_rec.2.2.2.1, ?_⟩
  intro q hq
  rw [hlist q hq]
  exact hb_rec.2.2.2.2 q hq

lemma idx_succ_le_ell {k j ℓ len : ℕ}
    (hk : k + 1 ≤ ℓ) (hl : len = ℓ - (k + 1)) (hj : j < len) :
    k + (j + 1) + 1 ≤ ℓ := by omega

lemma k1_lt_kj1 (k j : ℕ) : k + 1 < k + (j + 1) + 1 := by omega

lemma decomposeStep_hlvl
    {G : Cited.Graph} {k : ℕ} {L : DecompLayout}
    {recs : List DecompLevelRec} {rec_new : DecompLevelRec}
    {remIdx remIdx' keptIdx : List ℕ} {st st4 : State}
    (hrec_k : rec_new.keptIdx = keptIdx)
    (hmem_eq : ∀ a < G.m, st4.mem (L.lvlArrAddr + a) =
      if a ∈ keptIdx then k + 1 else st.mem (L.lvlArrAddr + a))
    (hrem_part : (∀ a ∈ remIdx', a ∈ remIdx ∧ a ∉ keptIdx) ∧
      (∀ a ∈ keptIdx, a ∈ remIdx ∧ a ∉ remIdx') ∧
      (∀ a ∈ remIdx, a ∈ remIdx' ∨ a ∈ keptIdx))
    (hinv_hlvl : ∀ a < G.m,
      (st.mem (L.lvlArrAddr + a) = 0 ↔ a ∈ remIdx) ∧
      (∀ (t : ℕ) (ht : t < recs.length), st.mem (L.lvlArrAddr + a) = (k + 1) + t + 1 ↔ a ∈ recs[t].keptIdx) ∧
      (st.mem (L.lvlArrAddr + a) = 0 ∨ ∃ t, ∃ (_ : t < recs.length), st.mem (L.lvlArrAddr + a) = (k + 1) + t + 1)) :
    ∀ a < G.m,
      (st4.mem (L.lvlArrAddr + a) = 0 ↔ a ∈ remIdx') ∧
      (∀ (t : ℕ) (ht : t < (rec_new :: recs).length),
        st4.mem (L.lvlArrAddr + a) = k + t + 1 ↔ a ∈ (rec_new :: recs)[t].keptIdx) ∧
      (st4.mem (L.lvlArrAddr + a) = 0 ∨
        ∃ t, ∃ (_ : t < (rec_new :: recs).length), st4.mem (L.lvlArrAddr + a) = k + t + 1) := by
  intro a ha
  rw [hmem_eq a ha]
  have hinv_a := hinv_hlvl a ha
  by_cases hka : a ∈ keptIdx
  · have ha_rem_orig : a ∈ remIdx := (hrem_part.2.1 a hka).1
    have ha_nrem' : a ∉ remIdx' := (hrem_part.2.1 a hka).2
    have ha_nkept_old : ∀ j (hj : j < recs.length), a ∉ recs[j].keptIdx := by
      intro j hj hkj
      have hmem0 : st.mem (L.lvlArrAddr + a) = 0 := hinv_a.1.mpr ha_rem_orig
      have hmemj : st.mem (L.lvlArrAddr + a) = (k + 1) + j + 1 := (hinv_a.2.1 j hj).mpr hkj
      omega
    refine ⟨⟨fun h0 => by simp [hka] at h0, fun hr => False.elim (ha_nrem' hr)⟩,
      ?_, Or.inr ⟨0, by simp, by simp [hka]⟩⟩
    intro i hi
    rcases i with _ | j
    · simp [hka, hrec_k]
    · simp only [List.getElem_cons_succ, List.length_cons, hka, ite_true] at hi ⊢
      constructor
      · intro heq; omega
      · intro hkj; exact False.elim (ha_nkept_old j (by omega) hkj)
  · have ha_nrem_new : a ∈ remIdx' ↔ a ∈ remIdx := by
      constructor
      · intro hr; exact (hrem_part.1 a hr).1
      · intro hr; exact (hrem_part.2.2 a hr).resolve_right hka
    refine ⟨?_, ?_, ?_⟩
    · simp only [hka, ite_false, ha_nrem_new]; exact hinv_a.1
    · intro i hi
      rcases i with _ | j
      · simp only [Nat.add_zero, List.getElem_cons_zero, hka, ite_false, hrec_k]
        constructor
        · intro h0
          rcases hinv_a.2.2 with hzero_st | ⟨j, hj, hmem_j⟩
          · omega
          · omega
        · intro hk_mem; exact False.elim hk_mem
      · simp only [List.getElem_cons_succ, hka, ite_false]
        have heq : (k + 1) + j + 1 = k + (j + 1) + 1 := by omega
        rw [← heq]
        exact hinv_a.2.1 j (by simp at hi; omega)
    · simp only [hka, ite_false]
      rcases hinv_a.2.2 with hzero_st | ⟨j, hj, hmem_j⟩
      · exact Or.inl hzero_st
      · have heq : (k + 1) + j + 1 = k + (j + 1) + 1 := by omega
        exact Or.inr ⟨j + 1, by simp; omega, by rw [← heq]; exact hmem_j⟩

lemma decomposeStep_hbounds
    {L : DecompLayout} {k ℓ m_G arena arena₁ : ℕ}
    {recs : List DecompLevelRec} {rec_new : DecompLevelRec}
    {rawComps_lvl : List (ℕ × List ℕ)} {st st1 st_lvl st4 : State}
    (hrec_rc : rec_new.rawComps = rawComps_lvl)
    (hk_le : k + 1 ≤ ℓ) (hlen : recs.length = ℓ - (k + 1)) (hlvl_le_m : ℓ ≤ m_G)
    (hL_lvl : L.lvlArrAddr = L.boundsAddr + 2 * m_G + 6)
    (hbnd_le : L.boundsAddr + 2 * (k + 1) + 1 < L.lvlArrAddr)
    (hL_lvl_ar : L.lvlArrAddr ≤ L.arena₀)
    (harena_ge : L.arena₀ ≤ arena) (harena_ge1 : arena ≤ arena₁)
    (harena_eq : arena₁ = arena + (List.flatMap compRecord rawComps_lvl).length)
    (hlist_ar : ListAt st_lvl.mem arena (List.flatMap compRecord rawComps_lvl))
    (hinv_hbounds : ∀ (j : ℕ) (hj : j < recs.length),
      let lvl := k + 1 + j + 1
      let a0 := st.mem (L.boundsAddr + 2 * lvl)
      let a1 := st.mem (L.boundsAddr + 2 * lvl + 1)
      L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena ∧
        a1 - a0 = (List.flatMap compRecord recs[j].rawComps).length ∧
        ListAt st.mem a0 (List.flatMap compRecord recs[j].rawComps))
    (hst4_mem_ne : ∀ a, a ≠ L.boundsAddr + 2 * (k + 1) + 1 → st4.mem a = st_lvl.mem a)
    (hst4_mem_bnd1 : st4.mem (L.boundsAddr + 2 * (k + 1) + 1) = arena₁)
    (hfr_bnd : ∀ a, L.boundsAddr ≤ a → a < L.lvlArrAddr → st_lvl.mem a = st1.mem a)
    (hfr_ar : ∀ a, L.arena₀ ≤ a → a < arena → st_lvl.mem a = st1.mem a)
    (hst1_mem_ne : ∀ a, a ≠ L.boundsAddr + 2 * (k + 1) → st1.mem a = st.mem a)
    (hst1_mem_bnd0 : st1.mem (L.boundsAddr + 2 * (k + 1)) = arena) :
    ∀ (i : ℕ) (hi : i < (rec_new :: recs).length),
      let lvl := k + i + 1
      let a0 := st4.mem (L.boundsAddr + 2 * lvl)
      let a1 := st4.mem (L.boundsAddr + 2 * lvl + 1)
      L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena₁ ∧
        a1 - a0 = (List.flatMap compRecord (rec_new :: recs)[i].rawComps).length ∧
        ListAt st4.mem a0 (List.flatMap compRecord (rec_new :: recs)[i].rawComps) := by
  have hbnd1_lt_arena₀ : L.boundsAddr + 2 * (k + 1) + 1 < L.arena₀ :=
    lt_of_lt_of_le hbnd_le hL_lvl_ar
  have hbnd1_lt_arena : L.boundsAddr + 2 * (k + 1) + 1 < arena :=
    lt_of_lt_of_le hbnd1_lt_arena₀ harena_ge
  have ha0_head : st4.mem (L.boundsAddr + 2 * (k + 1)) = arena := by
    rw [hst4_mem_ne _ (Nat.ne_of_lt (Nat.lt_succ_self _)),
        hfr_bnd _ (Nat.le_add_right _ _) (Nat.lt_of_succ_lt hbnd_le), hst1_mem_bnd0]
  have hlist_head : ∀ q < (List.flatMap compRecord rawComps_lvl).length,
      st4.mem (arena + q) = st_lvl.mem (arena + q) := fun q _ =>
    hst4_mem_ne _ (Nat.ne_of_gt (lt_of_lt_of_le hbnd1_lt_arena (Nat.le_add_right _ _)))
  intro i hi
  rcases i with _ | j
  · simp only [List.getElem_cons_zero, hrec_rc]
    exact hbounds_head (L := L) harena_ge1 harena_ge harena_eq ha0_head hst4_mem_bnd1
      hlist_head hlist_ar
  · have hj : j < recs.length := by simp at hi; omega
    have hb_rec := hinv_hbounds j hj
    simp only [List.getElem_cons_succ]
    have hk_sum : k + (j + 1) + 1 ≤ ℓ := idx_succ_le_ell hk_le hlen hj
    have hlt_lvl : L.boundsAddr + 2 * (k + (j + 1) + 1) + 1 < L.lvlArrAddr :=
      bnd_lt_lvl hL_lvl (le_trans hk_sum hlvl_le_m)
    have hlt_k : k + 1 < k + (j + 1) + 1 := k1_lt_kj1 k j
    have hnes := bounds_idx_ne (base := L.boundsAddr) hlt_k
    have hidx_eq : (k + 1) + j + 1 = k + (j + 1) + 1 := by omega
    have hbnd_le_a : L.boundsAddr ≤ L.boundsAddr + 2 * (k + (j + 1) + 1) :=
      Nat.le_add_right _ _
    have ha0_lt_lvl : L.boundsAddr + 2 * (k + (j + 1) + 1) < L.lvlArrAddr :=
      Nat.lt_of_succ_lt hlt_lvl
    have hbnd_le_a1 : L.boundsAddr ≤ L.boundsAddr + 2 * (k + (j + 1) + 1) + 1 :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have ha1_lt_lvl : L.boundsAddr + 2 * (k + (j + 1) + 1) + 1 < L.lvlArrAddr := hlt_lvl
    have ha0_eq : st4.mem (L.boundsAddr + 2 * (k + (j + 1) + 1)) =
        st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) := by
      rw [hidx_eq, hst4_mem_ne _ hnes.2.1, hfr_bnd _ hbnd_le_a ha0_lt_lvl, hst1_mem_ne _ hnes.1]
    have ha1_eq : st4.mem (L.boundsAddr + 2 * (k + (j + 1) + 1) + 1) =
        st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1) + 1) := by
      rw [hidx_eq, hst4_mem_ne _ hnes.2.2.2, hfr_bnd _ hbnd_le_a1 ha1_lt_lvl, hst1_mem_ne _ hnes.2.2.1]
    have hlist_q : ∀ q < (List.flatMap compRecord recs[j].rawComps).length,
        st4.mem (st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q) =
          st.mem (st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q) := by
      intro q hq
      dsimp only at hb_rec
      have hq_ar : L.arena₀ ≤ st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q ∧
          st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q < arena := by
        have h1 := hb_rec.1; have h2 := hb_rec.2.1; have h3 := hb_rec.2.2.1; have h4 := hb_rec.2.2.2.1
        omega
      have hne3 : st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q ≠ L.boundsAddr + 2 * (k + 1) + 1 :=
        Nat.ne_of_gt (lt_of_lt_of_le hbnd1_lt_arena₀ hq_ar.1)
      have hne1 : st.mem (L.boundsAddr + 2 * ((k + 1) + j + 1)) + q ≠ L.boundsAddr + 2 * (k + 1) :=
        Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_of_succ_lt hbnd1_lt_arena₀) hq_ar.1)
      rw [hst4_mem_ne _ hne3, hfr_ar _ hq_ar.1 hq_ar.2, hst1_mem_ne _ hne1]
    exact hbounds_tail (L := L) harena_ge1 hb_rec ha0_eq ha1_eq hlist_q

lemma dr_dphi {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rDphi = D_phi :=
  hr.2.2.2.2.2.1
lemma dr_m {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rM = m :=
  hr.2.2.2.1
lemma dr_sp {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rStatePtr = L.statePtr :=
  hr.2.2.2.2.2.2.1
lemma dr_bnd {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rBounds = L.boundsAddr :=
  hr.2.2.2.2.2.2.2.1
lemma dr_lvlArr {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rLvlArr = L.lvlArrAddr :=
  hr.2.2.2.2.2.2.2.2.1
lemma dr_curG {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rCurG = cG :=
  hr.2.2.2.2.2.2.2.2.2.1
lemma dr_curIdx {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rCurIdx = cI :=
  hr.2.2.2.2.2.2.2.2.2.2.1
lemma dr_nextG {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rNextG = nG :=
  hr.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_nextIdx {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rNextIdx = nI :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_tw {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rTw = L.twAddr :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_buf {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rBuf = L.bufAddr :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_work {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rWork = L.workAddr :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_kept {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rKept = L.keptVertAddr :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_lvl {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rLvl = lvl :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma dr_d {gAddr h n m ℓ D_phi lvl D cG cI nG nI : ℕ} {L : DecompLayout} {st : State}
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D cG cI nG nI L st) : st.regs rD = D :=
  hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

structure DecompLoopInv (G : Cited.Graph) (gAddr h ℓ D_phi c_cited k : ℕ)
    (mem_orig : ℕ → ℕ) (recs : List DecompLevelRec) (remG : Cited.Graph) (remIdx : List ℕ)
    (arena zc : ℕ) (st : State) : Prop where
  hk : k ≤ ℓ
  hlen : recs.length = ℓ - k
  hregs : let L := mkDecompLayout h G.n G.m D_phi
          let ca := curAddrs L (ℓ - k)
          DecompRegs gAddr h G.n G.m ℓ D_phi k (2 ^ k) ca.1 ca.2.1 ca.2.2.1 ca.2.2.2 L st
  hrem_valid : remG.IsValid
  hrem_loopless : remG.IsLoopless
  hrem_n : remG.n = G.n
  hrem_m_le_pow : remG.m ≤ 2 ^ k * G.n
  hrem_m_le : remG.m ≤ G.m
  hrem_edges : remG.edges = List.map (fun j => G.edges.getD j (0, 0)) remIdx
  hidx_len : remIdx.length = remG.m
  hidx_pw : remIdx.Pairwise (· < ·)
  hidx_lt : ∀ a ∈ remIdx, a < G.m
  hcurG_at : GraphAt st.mem (curAddrs (mkDecompLayout h G.n G.m D_phi) (ℓ - k)).1 remG
  hcurIdx_at : ListAt st.mem (curAddrs (mkDecompLayout h G.n G.m D_phi) (ℓ - k)).2.1 remIdx
  hstate_ar : st.mem (mkDecompLayout h G.n G.m D_phi).statePtr = arena
  hstate_zc : st.mem ((mkDecompLayout h G.n G.m D_phi).statePtr + 1) = zc
  hstate_tot : st.mem ((mkDecompLayout h G.n G.m D_phi).statePtr + 2) =
      (recs.map (fun x => x.rawComps)).flatten.length
  hzero : ZeroFrom st.mem zc
  harena_ge : (mkDecompLayout h G.n G.m D_phi).arena₀ ≤ arena
  harena_m : arena + 4 * remG.m ≤ (mkDecompLayout h G.n G.m D_phi).zeroCursor₀
  htotal_m : (recs.map (fun x => x.rawComps)).flatten.length + remG.m ≤ G.m
  hzc_ge : (mkDecompLayout h G.n G.m D_phi).zeroCursor₀ ≤ zc
  hzc_le : zc ≤ (mkDecompLayout h G.n G.m D_phi).zeroCursor₀ +
      (ℓ - k) * (1 + (416 * (G.n + G.m + 2)) ^ c_cited)
  hrecs : ∀ (i : ℕ) (hi : i < recs.length),
      let lvl := k + i + 1
      recs[i].lvl = lvl ∧
      (∀ comp ∈ recs[i].rawComps,
          comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
      List.map (fun c => c.2.toFinset) recs[i].rawComps = recs[i].validRs ∧
      recs[i].keptIdx.Pairwise (· < ·) ∧
      (∀ a ∈ recs[i].keptIdx, a < G.m) ∧
      recs[i].Gi.n = G.n ∧
      recs[i].Gi.edges = List.map (fun j => G.edges.getD j (0, 0)) recs[i].keptIdx ∧
      recs[i].Gi.m ≤ 2 ^ lvl * G.n ∧
      recs[i].validRs.Pairwise Disjoint ∧
      (∀ R ∈ recs[i].validRs,
          R ⊆ G.verts ∧ 2 ≤ R.card ∧
          recs[i].Gi.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          (∀ x ∈ R, (1 / (3 * (D_phi : ℝ))) * 2 ^ lvl ≤ ↑(recs[i].Gi.degIn R x)) ∧
          ∀ e ∈ recs[i].Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
      ∀ e ∈ recs[i].Gi.edges, ∃ R ∈ recs[i].validRs, e.1 ∈ R ∧ e.2 ∈ R
  hbounds : ∀ (i : ℕ) (hi : i < recs.length),
      let L := mkDecompLayout h G.n G.m D_phi
      let a0 := st.mem (L.boundsAddr + 2 * (k + i + 1))
      let a1 := st.mem (L.boundsAddr + 2 * (k + i + 1) + 1)
      L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ arena ∧
      a1 - a0 = (recs[i].rawComps.flatMap compRecord).length ∧
      ListAt st.mem a0 (recs[i].rawComps.flatMap compRecord)
  hlvl : ∀ a < G.m,
      let L := mkDecompLayout h G.n G.m D_phi
      (st.mem (L.lvlArrAddr + a) = 0 ↔ a ∈ remIdx) ∧
      (∀ (i : ℕ) (hi : i < recs.length), st.mem (L.lvlArrAddr + a) = k + i + 1 ↔ a ∈ recs[i].keptIdx) ∧
      (st.mem (L.lvlArrAddr + a) = 0 ∨ ∃ i, ∃ (_ : i < recs.length), st.mem (L.lvlArrAddr + a) = k + i + 1)
  hframe : ∀ a < h, st.mem a = mem_orig a

lemma swap_regs_step {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (gAddr h n m ℓ D_phi k curGAddr curIdxAddr nextGAddr nextIdxAddr : ℕ)
    (L : DecompLayout) (st₀ : State)
    (h1w : 1 < 2 ^ w) (h2w : 2 < 2 ^ w) (hkw : k + 1 < 2 ^ w) (hDw : 2 ^ (k + 1) < 2 ^ w)
    (hregs : DecompRegs gAddr h n m ℓ D_phi (k + 1) (2 ^ (k + 1)) curGAddr curIdxAddr nextGAddr nextIdxAddr L st₀) :
    ∃ st' c,
      Runs w p ω
        (seqStmts
          [ .assign rTmp1 (.reg rCurG)
          , .assign rCurG (.reg rNextG)
          , .assign rNextG (.reg rTmp1)
          , .assign rTmp1 (.reg rCurIdx)
          , .assign rCurIdx (.reg rNextIdx)
          , .assign rNextIdx (.reg rTmp1)
          , .assign rLvl (.bin .sub (.reg rLvl) (.const 1))
          , .assign rD (.bin .div (.reg rD) (.const 2)) ])
        st₀ .normal st' c ∧
      DecompRegs gAddr h n m ℓ D_phi k (2 ^ k) nextGAddr nextIdxAddr curGAddr curIdxAddr L st' ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      c ≤ 30 := by
  have hk_sub : (k + 1) - 1 < 2 ^ w := by omega
  have hD_div_eq : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; exact Nat.mul_div_cancel _ (by omega)
  have hD_div_w : 2 ^ (k + 1) / 2 < 2 ^ w := by omega
  let st1 : State := { st₀ with regs := Function.update st₀.regs rTmp1 curGAddr }
  have hr1 : Runs w p ω (.assign rTmp1 (.reg rCurG)) st₀ .normal st1 2 := by
    apply runs_assign_iff.mpr
    refine ⟨curGAddr, dp_ev_reg (dr_curG hregs), rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs rCurG nextGAddr }
  have h1_ng : st1.regs rNextG = nextGAddr := by
    dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact dr_nextG hregs
  have hr2 : Runs w p ω (.assign rCurG (.reg rNextG)) st1 .normal st2 2 := by
    apply runs_assign_iff.mpr
    refine ⟨nextGAddr, dp_ev_reg h1_ng, rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2 with regs := Function.update st2.regs rNextG curGAddr }
  have h2_t1 : st2.regs rTmp1 = curGAddr := by
    dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr3 : Runs w p ω (.assign rNextG (.reg rTmp1)) st2 .normal st3 2 := by
    apply runs_assign_iff.mpr
    refine ⟨curGAddr, dp_ev_reg h2_t1, rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp1 curIdxAddr }
  have h3_ci : st3.regs rCurIdx = curIdxAddr := by
    dsimp [st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact dr_curIdx hregs
  have hr4 : Runs w p ω (.assign rTmp1 (.reg rCurIdx)) st3 .normal st4 2 := by
    apply runs_assign_iff.mpr
    refine ⟨curIdxAddr, dp_ev_reg h3_ci, rfl, rfl, by simp [Expr.size]⟩
  let st5 : State := { st4 with regs := Function.update st4.regs rCurIdx nextIdxAddr }
  have h4_ni : st4.regs rNextIdx = nextIdxAddr := by
    dsimp [st4, st3, st2, st1]
    repeat rw [Function.update_of_ne (by decide)]
    exact dr_nextIdx hregs
  have hr5 : Runs w p ω (.assign rCurIdx (.reg rNextIdx)) st4 .normal st5 2 := by
    apply runs_assign_iff.mpr
    refine ⟨nextIdxAddr, dp_ev_reg h4_ni, rfl, rfl, by simp [Expr.size]⟩
  let st6 : State := { st5 with regs := Function.update st5.regs rNextIdx curIdxAddr }
  have h5_t1 : st5.regs rTmp1 = curIdxAddr := by
    dsimp [st5, st4]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr6 : Runs w p ω (.assign rNextIdx (.reg rTmp1)) st5 .normal st6 2 := by
    apply runs_assign_iff.mpr
    refine ⟨curIdxAddr, dp_ev_reg h5_t1, rfl, rfl, by simp [Expr.size]⟩
  let st7 : State := { st6 with regs := Function.update st6.regs rLvl k }
  have h6_lvl : st6.regs rLvl = k + 1 := by
    dsimp [st6, st5, st4, st3, st2, st1]
    repeat rw [Function.update_of_ne (by decide)]
    exact dr_lvl hregs
  have hr7 : Runs w p ω (.assign rLvl (.bin .sub (.reg rLvl) (.const 1))) st6 .normal st7 4 := by
    apply runs_assign_iff.mpr
    refine ⟨k, dp_ev_eq_of (dp_ev_sub (dp_ev_reg h6_lvl) (dp_ev_const h1w) hk_sub) (by omega),
      rfl, rfl, by simp [Expr.size]⟩
  let st8 : State := { st7 with regs := Function.update st7.regs rD (2 ^ k) }
  have h7_d : st7.regs rD = 2 ^ (k + 1) := by
    dsimp [st7, st6, st5, st4, st3, st2, st1]
    repeat rw [Function.update_of_ne (by decide)]
    exact dr_d hregs
  have hr8 : Runs w p ω (.assign rD (.bin .div (.reg rD) (.const 2))) st7 .normal st8 4 := by
    apply runs_assign_iff.mpr
    refine ⟨2 ^ k, dp_ev_eq_of (dp_ev_div (dp_ev_reg h7_d) (dp_ev_const h2w) hD_div_w) hD_div_eq,
      rfl, rfl, by simp [Expr.size]⟩
  have hfull := runs_seq hr1 (runs_seq hr2 (runs_seq hr3 (runs_seq hr4 (runs_seq hr5 (runs_seq hr6 (runs_seq hr7 hr8))))))
  change Runs w p ω _ st₀ .normal st8 _ at hfull
  refine ⟨st8, _, hfull, ?_, rfl, rfl, by omega⟩
  rcases hregs with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp only [st8, st7, st6, st5, st4, st3, st2, st1];
     repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by decide)])) <;>
    assumption


end

end MinCostFlow.Expander
