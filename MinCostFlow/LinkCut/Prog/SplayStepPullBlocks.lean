module

public import MinCostFlow.LinkCut.Prog.SplayStepBase

namespace MinCostFlow.LinkCut.Prog

/-!
Modular building blocks and pure aggregate lemmas for `pullBody`:
- `listIntMinAgg_has_iff_ne_nil`, signed cost/availability bridge lemmas for `nodeOwnRawStep`,
- `CanonicalNumAgg`, `decodeNumAgg`, `PullPre`, and `pullPre_of_treeMemMatch`,
- `addOptPtrStmt_runs`, `combineNumAggStmt_runs`, and `pullBody_zero_triple`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-! ### Pure `IntMinAgg` and `nodeOwnRawStep` algebra -/

theorem listIntMinAgg_has_iff_ne_nil (xs : List (ℕ × ℤ)) :
    (listIntMinAgg xs).has = true ↔ xs ≠ [] := by
  induction xs with
  | nil => simp [listIntMinAgg]
  | cons p xs _ =>
      rcases p with ⟨id, v⟩
      rcases hxs : listIntMinAgg xs with ⟨hb, vb, fb, lb⟩
      cases hb
      · simp [listIntMinAgg, hxs, combineIntMinAgg]
      · simp only [listIntMinAgg, hxs, combineIntMinAgg, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
        split_ifs <;> rfl

theorem wrap_signedCost_nodeOwn_eq {h L nodesBase cap x : ℕ} {mem : ℕ → ℕ}
    (hhe1 : nodeField mem nodesBase x OFF_HASE = 1)
    (hcf_ok : NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase x OFF_COST_FWD))
    (_hcb_ok : NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase x OFF_COST_BWD))
    (hcb_eq : intVal mem (nodeField mem nodesBase x OFF_COST_BWD) h L =
      wrap h L (-intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L)) :
    ∀ s, nodeOwnRawStep mem nodesBase h L x = some s →
      wrap h L s.signedCost = intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L ∧
      wrap h L (-s.signedCost) = intVal mem (nodeField mem nodesBase x OFF_COST_BWD) h L := by
  intro s hs
  have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
  simp only [nodeOwnRawStep, hne, ↓reduceIte, Option.some.injEq] at hs
  have hcf_fit : Fits h L (intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L) :=
    intVal_fits hcf_ok.2.2.2
  rw [← hs]
  dsimp only [RawStep.signedCost]
  cases hdir : decide (nodeField mem nodesBase x OFF_DIR ≠ 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · rw [hcb_eq, wrap_neg_wrap, neg_neg, wrap_of_fits hcf_fit]
    · rw [neg_neg, wrap_of_fits (intVal_fits _hcb_ok.2.2.2)]
  · simp only [↓reduceIte, wrap_of_fits hcf_fit, hcb_eq, and_self]

theorem nodeOwn_dirAvail_eq {h L nodesBase x : ℕ} {mem : ℕ → ℕ}
    (hhe1 : nodeField mem nodesBase x OFF_HASE = 1)
    {s : RawStep} (hs : nodeOwnRawStep mem nodesBase h L x = some s) :
    s.dirAvail = intVal mem (nodeField mem nodesBase x OFF_AF_PTR) h L ∧
    s.flip.dirAvail = intVal mem (nodeField mem nodesBase x OFF_AB_PTR) h L := by
  have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
  simp only [nodeOwnRawStep, hne, ↓reduceIte, Option.some.injEq] at hs
  rw [← hs]
  simp only [RawStep.dirAvail, RawStep.flip]
  cases decide (nodeField mem nodesBase x OFF_DIR ≠ 0) <;> simp

theorem nodeOwn_eq_some_of_hase {h L nodesBase x : ℕ} {mem : ℕ → ℕ}
    (hhe1 : nodeField mem nodesBase x OFF_HASE = 1) :
    ∃ s, nodeOwnRawStep mem nodesBase h L x = some s := by
  have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
  simp [nodeOwnRawStep, hne]

theorem listRawCost_own_eq_fwd {_w h L nodesBase cap x : ℕ} {mem : ℕ → ℕ}
    (hhe : nodeField mem nodesBase x OFF_HASE ≤ 1)
    (he1 : nodeField mem nodesBase x OFF_HASE = 1 →
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_FLOW_PTR) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_AF_PTR) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_AB_PTR) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_COST_FWD) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_COST_BWD) ∧
      intVal mem (nodeField mem nodesBase x OFF_COST_BWD) h L =
        wrap h L (-intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L))
    (he0 : nodeField mem nodesBase x OFF_HASE = 0 →
      nodeField mem nodesBase x OFF_COST_FWD = 0 ∧
      nodeField mem nodesBase x OFF_COST_BWD = 0) :
    let own := ((nodeOwnRawStep mem nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList
    wrap h L (listRawCost own) =
      optIntVal mem h L (nodeField mem nodesBase x OFF_COST_FWD) ∧
    wrap h L (-(listRawCost own)) =
      optIntVal mem h L (nodeField mem nodesBase x OFF_COST_BWD) := by
  by_cases h0 : nodeField mem nodesBase x OFF_HASE = 0
  · obtain ⟨hcf0, hcb0⟩ := he0 h0
    simp [nodeOwnRawStep, h0, listRawCost, optIntVal, hcf0, hcb0, wrap_of_fits (fits_zero h L)]
  · have h1 : nodeField mem nodesBase x OFF_HASE = 1 := by omega
    rcases he1 h1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, hcb_eq⟩
    rcases nodeOwn_eq_some_of_hase (h := h) (L := L) (nodesBase := nodesBase) (x := x) (mem := mem) h1
      with ⟨s, hs⟩
    have hfits : Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd := by
      have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
      simp only [nodeOwnRawStep, hne, ↓reduceIte, Option.some.injEq] at hs
      rw [← hs]
      refine ⟨intVal_fits hf_ok.2.2.2, ?_, ?_⟩
      · cases decide (nodeField mem nodesBase x OFF_DIR ≠ 0) <;>
          simp [intVal_fits haf_ok.2.2.2, intVal_fits hab_ok.2.2.2]
      · cases decide (nodeField mem nodesBase x OFF_DIR ≠ 0) <;>
          simp [intVal_fits haf_ok.2.2.2, intVal_fits hab_ok.2.2.2]
    have hmod0 : s.addDeltaMod h L 0 = s :=
      RawStep.addDeltaMod_zero hfits.1 hfits.2.1 hfits.2.2
    have hsc := wrap_signedCost_nodeOwn_eq h1 hcf_ok hcb_ok hcb_eq s hs
    simp only [hs, Option.map_some, Option.toList_some, hmod0, listRawCost,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    simp only [optIntVal, hcf_ok.1, hcb_ok.1, ↓reduceIte]
    exact hsc

theorem listIntMinAgg_own_eq {h L nodesBase cap x : ℕ} {mem : ℕ → ℕ}
    (hhe : nodeField mem nodesBase x OFF_HASE ≤ 1)
    (he1 : nodeField mem nodesBase x OFF_HASE = 1 →
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_FLOW_PTR) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_AF_PTR) ∧
      NumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
        (nodeField mem nodesBase x OFF_AB_PTR))
    (_he0 : nodeField mem nodesBase x OFF_HASE = 0 →
      nodeField mem nodesBase x OFF_AF_PTR = 0 ∧
      nodeField mem nodesBase x OFF_AB_PTR = 0) :
    let own := ((nodeOwnRawStep mem nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList
    listIntMinAgg (own.map fun s => (s.nodeId, s.dirAvail)) =
      (if nodeField mem nodesBase x OFF_HASE = 0 then ⟨false, 0, 0, 0⟩
       else ⟨true, optIntVal mem h L (nodeField mem nodesBase x OFF_AF_PTR), x, x⟩) ∧
    listIntMinAgg (own.map fun s => (s.nodeId, s.flip.dirAvail)) =
      (if nodeField mem nodesBase x OFF_HASE = 0 then ⟨false, 0, 0, 0⟩
       else ⟨true, optIntVal mem h L (nodeField mem nodesBase x OFF_AB_PTR), x, x⟩) := by
  by_cases h0 : nodeField mem nodesBase x OFF_HASE = 0
  · simp [nodeOwnRawStep, h0, listIntMinAgg]
  · have h1 : nodeField mem nodesBase x OFF_HASE = 1 := by omega
    rcases he1 h1 with ⟨hf_ok, haf_ok, hab_ok⟩
    rcases nodeOwn_eq_some_of_hase (h := h) (L := L) (nodesBase := nodesBase) (x := x) (mem := mem) h1
      with ⟨s, hs⟩
    have hfits : Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd := by
      have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
      simp only [nodeOwnRawStep, hne, ↓reduceIte, Option.some.injEq] at hs
      rw [← hs]
      refine ⟨intVal_fits hf_ok.2.2.2, ?_, ?_⟩
      · cases decide (nodeField mem nodesBase x OFF_DIR ≠ 0) <;>
          simp [intVal_fits haf_ok.2.2.2, intVal_fits hab_ok.2.2.2]
      · cases decide (nodeField mem nodesBase x OFF_DIR ≠ 0) <;>
          simp [intVal_fits haf_ok.2.2.2, intVal_fits hab_ok.2.2.2]
    have hmod0 : s.addDeltaMod h L 0 = s :=
      RawStep.addDeltaMod_zero hfits.1 hfits.2.1 hfits.2.2
    have hnid : s.nodeId = x := by
      have hne : nodeField mem nodesBase x OFF_HASE ≠ 0 := by omega
      simp only [nodeOwnRawStep, hne, ↓reduceIte, Option.some.injEq] at hs
      rw [← hs]
    have hda := nodeOwn_dirAvail_eq h1 hs
    simp only [hs, Option.map_some, Option.toList_some, hmod0, List.map_cons, List.map_nil,
      listIntMinAgg, combineIntMinAgg, hnid, hda.1, hda.2, h0, ↓reduceIte,
      optIntVal, haf_ok.1, hab_ok.1, Bool.not_false, Bool.not_true, Bool.false_eq_true, and_self]

/-! ### `CanonicalNumAgg`, `PullPre`, and `pullPre_of_treeMemMatch` -/

def CanonicalNumAgg (mem : ℕ → ℕ) (arenaHi hp h L rH rV rF rL : ℕ) : Prop :=
  (rH = 0 → rV = 0 ∧ rF = 0 ∧ rL = 0) ∧
  (rH ≠ 0 → rH = 1 ∧ NumPtrOk mem arenaHi hp h L rV)

def decodeNumAgg (mem : ℕ → ℕ) (h L rH rV rF rL : ℕ) : IntMinAgg :=
  ⟨decide (rH ≠ 0), optIntVal mem h L rV, rF, rL⟩

theorem canonicalNumAgg_of_zero {mem : ℕ → ℕ} {arenaHi hp h L : ℕ} :
    CanonicalNumAgg mem arenaHi hp h L 0 0 0 0 :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun h0 => absurd rfl h0⟩

theorem canonicalNumAgg_of_node1 {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {par pp : ℕ} (hq : TreeMemMatch w h L mem nodesBase cap q par pp)
    (h0 : SlotZeroOk mem nodesBase) :
    CanonicalNumAgg mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase q.rootId OFF_MIN1_HAS)
      (nodeField mem nodesBase q.rootId OFF_MIN1_VAL)
      (nodeField mem nodesBase q.rootId OFF_MIN1_FIRST)
      (nodeField mem nodesBase q.rootId OFF_MIN1_LAST) := by
  cases q with
  | leaf =>
      simp only [AuxTree.rootId, nodeField, Nat.mul_zero, Nat.add_zero]
      rw [h0 OFF_MIN1_HAS (by decide), h0 OFF_MIN1_VAL (by decide),
        h0 OFF_MIN1_FIRST (by decide), h0 OFF_MIN1_LAST (by decide)]
      exact canonicalNumAgg_of_zero
  | node rid rl rr =>
      rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, hm1h, _, hm1_1, hm1_0, _⟩
      simp only [AuxTree.rootId]
      exact ⟨fun hz => let h := hm1_0 hz; ⟨h.1, h.2.1, h.2.2.1⟩,
        fun hne => have h1 : nodeField mem nodesBase rid OFF_MIN1_HAS = 1 :=
            Nat.le_antisymm hm1h (Nat.one_le_iff_ne_zero.mpr hne)
          ⟨h1, (hm1_1 h1).1⟩⟩

theorem canonicalNumAgg_of_node2 {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {par pp : ℕ} (hq : TreeMemMatch w h L mem nodesBase cap q par pp)
    (h0 : SlotZeroOk mem nodesBase) :
    CanonicalNumAgg mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase q.rootId OFF_MIN2_HAS)
      (nodeField mem nodesBase q.rootId OFF_MIN2_VAL)
      (nodeField mem nodesBase q.rootId OFF_MIN2_FIRST)
      (nodeField mem nodesBase q.rootId OFF_MIN2_LAST) := by
  cases q with
  | leaf =>
      simp only [AuxTree.rootId, nodeField, Nat.mul_zero, Nat.add_zero]
      rw [h0 OFF_MIN2_HAS (by decide), h0 OFF_MIN2_VAL (by decide),
        h0 OFF_MIN2_FIRST (by decide), h0 OFF_MIN2_LAST (by decide)]
      exact canonicalNumAgg_of_zero
  | node rid rl rr =>
      rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, hm1h, hm2h, hm1_1, hm1_0, _⟩
      simp only [AuxTree.rootId, hm2h]
      exact ⟨fun hz => let h := hm1_0 hz; ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
        fun hne => have h1 : nodeField mem nodesBase rid OFF_MIN1_HAS = 1 :=
            Nat.le_antisymm hm1h (Nat.one_le_iff_ne_zero.mpr hne)
          ⟨h1, (hm1_1 h1).2.1⟩⟩

/-- Preconditions for calling `pullBody(nodesBase, x)` on a node `x` whose lazy reversal and
tag flags are cleared and whose left/right children already match `l` and `r`. -/
structure PullPre (w h L : ℕ) (mem : ℕ → ℕ) (nodesBase cap x : ℕ)
    (l r : AuxTree) (parId pp : ℕ) : Prop where
  hx1 : 1 ≤ x
  hx2 : x ≤ cap
  hL : nodeField mem nodesBase x OFF_LEFT = l.rootId
  hR : nodeField mem nodesBase x OFF_RIGHT = r.rootId
  hP : nodeField mem nodesBase x OFF_PARENT = parId
  hPP : nodeField mem nodesBase x OFF_PPAR = pp
  hrev0 : nodeField mem nodesBase x OFF_REV = 0
  hiv : nodeField mem nodesBase x OFF_ISV ≤ 1
  hhe : nodeField mem nodesBase x OFF_HASE ≤ 1
  hsum : nodeField mem nodesBase x OFF_ISV + nodeField mem nodesBase x OFF_HASE ≤ 1
  hdir : nodeField mem nodesBase x OFF_DIR ≤ 1
  hht0 : nodeField mem nodesBase x OFF_HAS_TAG = 0
  htp0 : nodeField mem nodesBase x OFF_TAG_PTR = 0
  htn0 : nodeField mem nodesBase x OFF_TAG_NEG = 0
  heu : nodeField mem nodesBase x OFF_EU < 2 ^ w
  hev : nodeField mem nodesBase x OFF_EV < 2 ^ w
  heid : nodeField mem nodesBase x OFF_EID < 2 ^ w
  he1 : nodeField mem nodesBase x OFF_HASE = 1 →
    let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
    let hp := mem (nodesBase - 1)
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_FLOW_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_AF_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_AB_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_COST_FWD) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_COST_BWD) ∧
    intVal mem (nodeField mem nodesBase x OFF_COST_BWD) h L =
      wrap h L (-intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L)
  he0 : nodeField mem nodesBase x OFF_HASE = 0 →
    nodeField mem nodesBase x OFF_DIR = 0 ∧
    nodeField mem nodesBase x OFF_FLOW_PTR = 0 ∧
    nodeField mem nodesBase x OFF_AF_PTR = 0 ∧
    nodeField mem nodesBase x OFF_AB_PTR = 0 ∧
    nodeField mem nodesBase x OFF_COST_FWD = 0 ∧
    nodeField mem nodesBase x OFF_COST_BWD = 0
  hl : TreeMemMatch w h L mem nodesBase cap l x 0
  hr : TreeMemMatch w h L mem nodesBase cap r x 0
  hvcnt_lt : listVcnt mem nodesBase
    (l.evalInorder (revFlag mem nodesBase) false ++ [x] ++
      r.evalInorder (revFlag mem nodesBase) false) < 2 ^ w

theorem pullPre_of_treeMemMatch {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    {l r : AuxTree} {parId pp : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (ht : TreeMemMatch w h L mem nodesBase cap (.node x l r) parId pp)
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hrev : nodeField mem nodesBase x OFF_REV = 0)
    (hht : nodeField mem nodesBase x OFF_HAS_TAG = 0) :
    PullPre w h L mem nodesBase cap x l r parId pp := by
  have hvc := ht.listVcnt_lt_pow hbase hnd
  rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, _, hiv, hhe, hsum, hdir, _, _,
    heu, hev, heid, he1, he0, _, _, _, htag0, _, _, _, _, _, hl, hr⟩
  obtain ⟨htp, htn⟩ := htag0 hht
  have hrf : revFlag mem nodesBase x = false := by simp [revFlag, hrev]
  have hvc' : listVcnt mem nodesBase
      (l.evalInorder (revFlag mem nodesBase) false ++ [x] ++
        r.evalInorder (revFlag mem nodesBase) false) < 2 ^ w := by
    simpa [AuxTree.evalInorder, hrf] using hvc
  exact ⟨hx1, hx2, hL, hR, hP, hPP, hrev, hiv, hhe, hsum, hdir, hht, htp, htn,
    heu, hev, heid, he1, he0, hl, hr, hvc'⟩

/-! ### Specifications for `addOptPtrStmt`, `combineNumAggStmt`, and `pullBody_zero_triple` -/

theorem addOptPtrStmt_runs {w h L arenaHi hp p1 p2 : ℕ}
    {sp : SplayProcs} {p : Program} {p1Reg p2Reg LReg hpReg outReg : ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hnd_regs : [p1Reg, p2Reg, LReg, hpReg, outReg].Nodup)
    (st₀ : State)
    (hr_1 : st₀.regs p1Reg = p1) (hr_2 : st₀.regs p2Reg = p2)
    (hr_L : st₀.regs LReg = L) (hr_hp : st₀.regs hpReg = hp)
    (harena_pos : 1 ≤ arenaHi) (harena_hp : arenaHi ≤ hp)
    (hp1_ok : OptNumPtrOk st₀.mem arenaHi hp h L p1)
    (hp2_ok : OptNumPtrOk st₀.mem arenaHi hp h L p2)
    (hz : ZeroFrom st₀.mem hp)
    (hhp_lt : hp + L < 2 ^ w) :
    ∀ ω, ∃ st' c hp' outPtr,
      Runs w p ω (addOptPtrStmt sp p1Reg p2Reg LReg hpReg outReg) st₀ .normal st' c ∧
      st'.regs hpReg = hp' ∧
      st'.regs outReg = outPtr ∧
      (∀ r, r ≠ hpReg → r ≠ outReg → st'.regs r = st₀.regs r) ∧
      hp ≤ hp' ∧ hp' ≤ hp + L ∧
      c + (hp' - hp) ≤ 39 * L + 32 ∧
      (∀ a < hp, st'.mem a = st₀.mem a) ∧
      ZeroFrom st'.mem hp' ∧
      OptNumPtrOk st'.mem arenaHi hp' h L outPtr ∧
      optIntVal st'.mem h L outPtr =
        wrap h L (optIntVal st₀.mem h L p1 + optIntVal st₀.mem h L p2) := by
  intro ω
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd_regs
  rcases hnd_regs with ⟨⟨_, _, _, _⟩, ⟨_, _, _⟩, ⟨hLh, _⟩, hho, _⟩
  dsimp only [addOptPtrStmt]
  by_cases hp1z : p1 = 0
  · subst hp1z
    let st' : State := { mem := st₀.mem, regs := Function.update st₀.regs outReg p2, pos := st₀.pos }
    have hass : Runs w p ω (Stmt.assign outReg (.reg p2Reg)) st₀ .normal st' 2 :=
      runs_assign_iff.mpr ⟨p2, Expr.eval_reg_of_eq hr_2, rfl, rfl, rfl⟩
    refine ⟨st', 4, hp, p2,
      runs_cond_iff.mpr ⟨0, 2, by simpa using Expr.eval_reg_of_eq hr_1, by simp [hass], rfl⟩,
      ?_, ?_, ?_, le_rfl, Nat.le_add_right _ _, by omega, fun _ _ => rfl, hz, hp2_ok, ?_⟩
    · dsimp [st']; rw [Function.update_of_ne hho]; exact hr_hp
    · dsimp [st']; exact Function.update_self _ _ _
    · intro r _ hro; dsimp [st']; rw [Function.update_of_ne hro]
    · simp only [optIntVal, ↓reduceIte, zero_add]
      rcases hp2_ok with rfl | ⟨_, _, hv2⟩
      · simp [wrap_of_fits (fits_zero h L)]
      · have hp2_nz : p2 ≠ 0 := by omega
        dsimp [st']
        simp [hp2_nz, wrap_of_fits (intVal_fits hv2)]
  · rcases hp1_ok with rfl | ⟨h1lo, h1hi, h1v⟩
    · contradiction
    by_cases hp2z : p2 = 0
    · subst hp2z
      let st' : State := { mem := st₀.mem, regs := Function.update st₀.regs outReg p1, pos := st₀.pos }
      have hass : Runs w p ω (Stmt.assign outReg (.reg p1Reg)) st₀ .normal st' 2 :=
        runs_assign_iff.mpr ⟨p1, Expr.eval_reg_of_eq hr_1, rfl, rfl, rfl⟩
      refine ⟨st', 6, hp, p1, ?_, ?_, ?_, ?_, le_rfl, Nat.le_add_right _ _, by omega,
        fun _ _ => rfl, hz, Or.inr ⟨h1lo, h1hi, h1v⟩, ?_⟩
      · refine runs_cond_iff.mpr ⟨p1, 4, Expr.eval_reg_of_eq hr_1, ?_, rfl⟩
        simp only [hp1z, ↓reduceIte]
        exact runs_cond_iff.mpr ⟨0, 2, by simpa using Expr.eval_reg_of_eq hr_2, by simp [hass], rfl⟩
      · dsimp [st']; rw [Function.update_of_ne hho]; exact hr_hp
      · dsimp [st']; exact Function.update_self _ _ _
      · intro r _ hro; dsimp [st']; rw [Function.update_of_ne hro]
      · simp only [optIntVal, hp1z, ↓reduceIte, add_zero]
        exact (wrap_of_fits (intVal_fits h1v)).symm
    · rcases hp2_ok with rfl | ⟨h2lo, h2hi, h2v⟩
      · contradiction
      have hargs : evalArgs w st₀ [.reg p1Reg, .reg p2Reg, .reg LReg, .reg hpReg] =
          some [p1, p2, L, hp] := by
        simp [evalArgs, Expr.eval, hr_1, hr_2, hr_L, hr_hp]
      have hwords : ∀ a ∈ ([p1, p2, L, hp] : List ℕ), a < 2 ^ w := by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega
      have hpre_add : (addContract w h).pre [p1, p2, L, hp] st₀.mem :=
        ⟨p1, p2, L, hp, rfl, ⟨⟨p1, p2, L, 0, hp, rfl, h1hi, h2hi, Nat.zero_le 1, h1v, h2v⟩,
          hz, by change hp + L < 2 ^ w; exact hhp_lt⟩⟩
      rcases hp_ok.add_ok [p1, p2, L, hp] st₀.mem st₀.pos ω hwords hpre_add with
        ⟨body, hproc, o, st1, c_add, hr_add, hpost_add, hc_add⟩
      rcases hpost_add with ⟨ho_eq, _, _, hpres1, hz1, hl1⟩
      change o.value = hp + L at ho_eq
      change ∀ a < hp, st1.mem a = st₀.mem a at hpres1
      change ZeroFrom st1.mem o.value at hz1
      change ListAt st1.mem hp
        (digits h L (unsignedVal st₀.mem p1 h L + unsignedVal st₀.mem p2 h L + 0)) at hl1
      change c_add ≤ 38 * L + 15 at hc_add
      have hval1 := addCarry_value hl1
      let st_call : State := { st1 with regs := Function.update st₀.regs hpReg (hp + L) }
      have hcall : Runs w p ω
          (Stmt.call hpReg sp.numAdd [.reg p1Reg, .reg p2Reg, .reg LReg, .reg hpReg])
          st₀ .normal st_call (4 + c_add + 1) := by
        dsimp only [st_call]; rw [← ho_eq]
        exact runs_call_iff.mpr ⟨[p1, p2, L, hp], body, o, st1, c_add, hargs, hproc, hr_add, rfl, rfl, rfl⟩
      have hr_hp1 : st_call.regs hpReg = hp + L := Function.update_self _ _ _
      have hr_L1 : st_call.regs LReg = L := by
        dsimp [st_call]; rw [Function.update_of_ne hLh, hr_L]
      have hsub_ev : (Expr.bin .sub (.reg hpReg) (.reg LReg)).eval w st_call = some hp := by
        have h1 := Expr.eval_sub (Expr.eval_reg_of_eq hr_hp1) (Expr.eval_reg_of_eq hr_L1) hhp_lt
        simpa [show hp + L - L = hp by omega] using h1
      let st' : State := { mem := st_call.mem, regs := Function.update st_call.regs outReg hp, pos := st_call.pos }
      have hass : Runs w p ω (Stmt.assign outReg (.bin .sub (.reg hpReg) (.reg LReg)))
          st_call .normal st' 4 :=
        runs_assign_iff.mpr ⟨hp, hsub_ev, rfl, rfl, rfl⟩
      have hseq : Runs w p ω
          (Stmt.call hpReg sp.numAdd [.reg p1Reg, .reg p2Reg, .reg LReg, .reg hpReg] ;;
           Stmt.assign outReg (.bin .sub (.reg hpReg) (.reg LReg)))
          st₀ .normal st' ((4 + c_add + 1) + 4 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st_call, _, _, hcall, hass, rfl⟩)
      have hcond2 : Runs w p ω
          (Stmt.cond (.reg p2Reg) _ (Stmt.assign outReg (.reg p1Reg))) st₀ .normal st'
          (1 + ((4 + c_add + 1) + 4 + 1) + 1) :=
        runs_cond_iff.mpr ⟨p2, _, Expr.eval_reg_of_eq hr_2, by simpa [hp2z] using hseq, rfl⟩
      have hcond1 : Runs w p ω (addOptPtrStmt sp p1Reg p2Reg LReg hpReg outReg) st₀ .normal st'
          (1 + (1 + ((4 + c_add + 1) + 4 + 1) + 1) + 1) :=
        runs_cond_iff.mpr ⟨p1, _, Expr.eval_reg_of_eq hr_1, by simpa [hp1z] using hcond2, rfl⟩
      refine ⟨st', _, hp + L, hp, hcond1, ?_, ?_, ?_, Nat.le_add_right _ _, le_rfl, by omega,
        hpres1, ?_, Or.inr ⟨harena_hp, le_rfl, hval1.1⟩, ?_⟩
      · dsimp [st', st_call]; rw [Function.update_of_ne hho]; exact hr_hp1
      · dsimp [st']; exact Function.update_self _ _ _
      · intro r hr1 hr2; dsimp [st', st_call]; rw [Function.update_of_ne hr2, Function.update_of_ne hr1]
      · simpa [st', st_call, ho_eq] using hz1
      · have hhp_nz : hp ≠ 0 := by omega
        simp only [optIntVal, hhp_nz, hp1z, hp2z, ↓reduceIte]
        simpa [st', st_call, Int.natCast_zero, add_zero] using hval1.2

theorem combineNumAggStmt_runs {w h L arenaHi hp : ℕ}
    {sp : SplayProcs} {p : Program}
    {rHA rVA rFA rLA rHB rVB rFB rLB LReg cmpReg : ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hhp_lt : hp < 2 ^ w)
    (hnd_regs : [rHA, rVA, rFA, rLA, rHB, rVB, rFB, rLB, LReg, cmpReg].Nodup)
    (st₀ : State)
    (hr_L : st₀.regs LReg = L)
    (hca : CanonicalNumAgg st₀.mem arenaHi hp h L
      (st₀.regs rHA) (st₀.regs rVA) (st₀.regs rFA) (st₀.regs rLA))
    (hvb_ok : st₀.regs rHB ≠ 0 →
      st₀.regs rHB = 1 ∧ NumPtrOk st₀.mem arenaHi hp h L (st₀.regs rVB)) :
    ∀ ω, ∃ st' c,
      Runs w p ω (combineNumAggStmt sp rHA rVA rFA rLA rHB rVB rFB rLB LReg cmpReg) st₀ .normal st' c ∧
      st'.mem = st₀.mem ∧
      (∀ r, r ≠ rHA → r ≠ rVA → r ≠ rFA → r ≠ rLA → r ≠ cmpReg → st'.regs r = st₀.regs r) ∧
      CanonicalNumAgg st'.mem arenaHi hp h L
        (st'.regs rHA) (st'.regs rVA) (st'.regs rFA) (st'.regs rLA) ∧
      decodeNumAgg st'.mem h L (st'.regs rHA) (st'.regs rVA) (st'.regs rFA) (st'.regs rLA) =
        combineIntMinAgg
          (decodeNumAgg st₀.mem h L (st₀.regs rHA) (st₀.regs rVA) (st₀.regs rFA) (st₀.regs rLA))
          (decodeNumAgg st₀.mem h L (st₀.regs rHB) (st₀.regs rVB) (st₀.regs rFB) (st₀.regs rLB)) ∧
      c ≤ 64 * L + 80 := by
  intro ω
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd_regs
  rcases hnd_regs with ⟨⟨hHA_VA, hHA_FA, hHA_LA, hHA_HB, hHA_VB, hHA_FB, hHA_LB, hHA_L, hHA_cmp⟩,
    ⟨hVA_FA, hVA_LA, hVA_HB, hVA_VB, hVA_FB, hVA_LB, hVA_L, hVA_cmp⟩,
    ⟨hFA_LA, hFA_HB, hFA_VB, hFA_FB, hFA_LB, hFA_L, hFA_cmp⟩,
    ⟨hLA_HB, hLA_VB, hLA_FB, hLA_LB, hLA_L, hLA_cmp⟩,
    ⟨hHB_VB, hHB_FB, hHB_LB, hHB_L, hHB_cmp⟩,
    ⟨hVB_FB, hVB_LB, hVB_L, hVB_cmp⟩,
    ⟨hFB_LB, hFB_L, hFB_cmp⟩,
    ⟨hLB_L, hLB_cmp⟩, hL_cmp, _⟩
  let A := decodeNumAgg st₀.mem h L (st₀.regs rHA) (st₀.regs rVA) (st₀.regs rFA) (st₀.regs rLA)
  let B := decodeNumAgg st₀.mem h L (st₀.regs rHB) (st₀.regs rVB) (st₀.regs rFB) (st₀.regs rLB)
  have hA_zero : st₀.regs rHA = 0 → A = ⟨false, 0, 0, 0⟩ := fun hz => by
    obtain ⟨hv, hf, hl⟩ := hca.1 hz
    simp [A, decodeNumAgg, hz, hv, hf, hl, optIntVal]
  have hw1 : (1 : ℕ) < 2 ^ w :=
    Nat.one_lt_pow (by have := hp_ok.hh; have := hp_ok.hw; omega) (by decide)
  dsimp only [combineNumAggStmt]
  by_cases hHB0 : st₀.regs rHB = 0
  · have hB_f : B.has = false := by simp [B, decodeNumAgg, hHB0]
    refine ⟨st₀, 3,
      runs_cond_iff.mpr ⟨0, 1, by simpa [hHB0] using Expr.eval_reg w rHB st₀,
        by simp [runs_nop_iff], rfl⟩,
      rfl, fun _ _ _ _ _ _ => rfl, hca, ?_, by omega⟩
    change A = combineIntMinAgg A B
    simp only [combineIntMinAgg, hB_f, Bool.not_false, ↓reduceIte]
    by_cases hHA0 : st₀.regs rHA = 0
    · rw [hA_zero hHA0]; simp
    · have hA_t : A.has = true := by simp [A, decodeNumAgg, hHA0]
      simp [hA_t]
  · obtain ⟨hHB1, hvb_ptr⟩ := hvb_ok hHB0
    have hB_t : B.has = true := by simp [B, decodeNumAgg, hHB0]
    have hB_val : B.val = intVal st₀.mem (st₀.regs rVB) h L := by
      simp [B, decodeNumAgg, optIntVal, hvb_ptr.1]
    by_cases hHA0 : st₀.regs rHA = 0
    · have hA_f : A.has = false := by simp [A, decodeNumAgg, hHA0]
      let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs rHA 1, pos := st₀.pos }
      let st2 : State := { mem := st₀.mem, regs := Function.update st1.regs rVA (st₀.regs rVB), pos := st₀.pos }
      let st3 : State := { mem := st₀.mem, regs := Function.update st2.regs rFA (st₀.regs rFB), pos := st₀.pos }
      let st4 : State := { mem := st₀.mem, regs := Function.update st3.regs rLA (st₀.regs rLB), pos := st₀.pos }
      have h1 : st1.regs rVB = st₀.regs rVB := by dsimp [st1]; rw [Function.update_of_ne (Ne.symm hHA_VB)]
      have h2 : st2.regs rFB = st₀.regs rFB := by
        dsimp [st2, st1]; rw [Function.update_of_ne (Ne.symm hVA_FB), Function.update_of_ne (Ne.symm hHA_FB)]
      have h3 : st3.regs rLB = st₀.regs rLB := by
        dsimp [st3, st2, st1]
        rw [Function.update_of_ne (Ne.symm hFA_LB), Function.update_of_ne (Ne.symm hVA_LB), Function.update_of_ne (Ne.symm hHA_LB)]
      have hbranch : Runs w p ω
          (Stmt.assign rHA (.const 1) ;; Stmt.assign rVA (.reg rVB) ;;
           Stmt.assign rFA (.reg rFB) ;; Stmt.assign rLA (.reg rLB)) st₀ .normal st4 11 :=
        runs_seq_iff.mpr (Or.inr ⟨st1, 2, 8,
          runs_assign_iff.mpr ⟨1, Expr.eval_const hw1, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st2, 2, 5,
            runs_assign_iff.mpr ⟨st₀.regs rVB, Expr.eval_reg_of_eq h1, rfl, rfl, rfl⟩,
            runs_seq_iff.mpr (Or.inr ⟨st3, 2, 2,
              runs_assign_iff.mpr ⟨st₀.regs rFB, Expr.eval_reg_of_eq h2, rfl, rfl, rfl⟩,
              runs_assign_iff.mpr ⟨st₀.regs rLB, Expr.eval_reg_of_eq h3, rfl, rfl, rfl⟩, rfl⟩), rfl⟩), rfl⟩)
      have hrHA4 : st4.regs rHA = 1 := by
        dsimp [st4, st3, st2, st1]
        rw [Function.update_of_ne hHA_LA, Function.update_of_ne hHA_FA,
          Function.update_of_ne hHA_VA, Function.update_self]
      have hrVA4 : st4.regs rVA = st₀.regs rVB := by
        dsimp [st4, st3, st2, st1]
        rw [Function.update_of_ne hVA_LA, Function.update_of_ne hVA_FA, Function.update_self]
      have hrFA4 : st4.regs rFA = st₀.regs rFB := by
        dsimp [st4, st3, st2]; rw [Function.update_of_ne hFA_LA, Function.update_self]
      have hrLA4 : st4.regs rLA = st₀.regs rLB := by dsimp [st4]; exact Function.update_self _ _ _
      refine ⟨st4, 15, ?_, rfl, ?_, ?_, ?_, by omega⟩
      · refine runs_cond_iff.mpr ⟨st₀.regs rHB, 13, Expr.eval_reg w rHB st₀, ?_, rfl⟩
        simp only [hHB0, ↓reduceIte]
        refine runs_cond_iff.mpr ⟨0, 11, by simpa [hHA0] using Expr.eval_reg w rHA st₀, ?_, rfl⟩
        simpa only [↓reduceIte] using hbranch
      · intro r hr1 hr2 hr3 hr4 _
        dsimp [st4, st3, st2, st1]
        rw [Function.update_of_ne hr4, Function.update_of_ne hr3, Function.update_of_ne hr2, Function.update_of_ne hr1]
      · exact ⟨fun h => absurd h (by rw [hrHA4]; exact Nat.one_ne_zero), fun _ => ⟨hrHA4, by rw [hrVA4]; exact hvb_ptr⟩⟩
      · change decodeNumAgg st4.mem h L (st4.regs rHA) (st4.regs rVA) (st4.regs rFA) (st4.regs rLA) =
          combineIntMinAgg A B
        have hrhs : combineIntMinAgg A B = B := by simp [combineIntMinAgg, hB_t, hA_f]
        rw [hrhs, hrHA4, hrVA4, hrFA4, hrLA4]
        simp [B, decodeNumAgg, hHB0, st4]
    · obtain ⟨hHA1, hva_ptr⟩ := hca.2 hHA0
      have hA_t : A.has = true := by simp [A, decodeNumAgg, hHA0]
      have hA_val : A.val = intVal st₀.mem (st₀.regs rVA) h L := by
        simp [A, decodeNumAgg, optIntVal, hva_ptr.1]
      have hargs_less : evalArgs w st₀ [.reg rVB, .reg rVA, .reg LReg] =
          some [st₀.regs rVB, st₀.regs rVA, L] := by
        simp [evalArgs, Expr.eval, hr_L]
      have hwords_less : ∀ a ∈ ([st₀.regs rVB, st₀.regs rVA, L] : List ℕ), a < 2 ^ w := by
        have hvb_lt : st₀.regs rVB < 2 ^ w :=
          lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ L) hvb_ptr.2.2.1) hhp_lt
        have hva_lt : st₀.regs rVA < 2 ^ w :=
          lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ L) hva_ptr.2.2.1) hhp_lt
        have hL_lt : L < 2 ^ w :=
          lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left L (st₀.regs rVB)) hvb_ptr.2.2.1) hhp_lt
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | ha | ha <;> rw [ha] <;> assumption
      have hpre_less : (lessContract w h).pre [st₀.regs rVB, st₀.regs rVA, L] st₀.mem :=
        ⟨st₀.regs rVB, st₀.regs rVA, L, rfl, lt_of_le_of_lt hvb_ptr.2.2.1 hhp_lt,
          lt_of_le_of_lt hva_ptr.2.2.1 hhp_lt, hvb_ptr.2.2.2, hva_ptr.2.2.2⟩
      rcases hp_ok.less_ok [st₀.regs rVB, st₀.regs rVA, L] st₀.mem st₀.pos ω hwords_less hpre_less with
        ⟨b_less, hp_less, o_less, st_less, c_less, hr_less, hpost_less, hc_less⟩
      rcases hpost_less with ⟨hmem_less, hv_less⟩
      change st_less.mem = st₀.mem at hmem_less
      let cmpLess := o_less.value
      change cmpLess = (if intVal st₀.mem (st₀.regs rVB) h L < intVal st₀.mem (st₀.regs rVA) h L then 1 else 0) at hv_less
      change c_less ≤ 41 * L + 51 at hc_less
      let st_c1 : State := { st_less with regs := Function.update st₀.regs cmpReg cmpLess }
      have hcall_less : Runs w p ω (Stmt.call cmpReg sp.numLess [.reg rVB, .reg rVA, .reg LReg]) st₀
          .normal st_c1 (3 + c_less + 1) :=
        runs_call_iff.mpr ⟨[st₀.regs rVB, st₀.regs rVA, L], b_less, o_less, st_less, c_less,
          hargs_less, hp_less, hr_less, rfl, rfl, rfl⟩
      have hsc1_mem : st_c1.mem = st₀.mem := hmem_less
      have hsc1_regs : ∀ r, r ≠ cmpReg → st_c1.regs r = st₀.regs r := fun _ hr => Function.update_of_ne hr _ _
      by_cases hlt : intVal st₀.mem (st₀.regs rVB) h L < intVal st₀.mem (st₀.regs rVA) h L
      · have hv1 : cmpLess = 1 := by simp [hv_less, hlt]
        let st2 : State := { mem := st₀.mem, regs := Function.update st_c1.regs rVA (st₀.regs rVB), pos := st_c1.pos }
        let st3 : State := { mem := st₀.mem, regs := Function.update st2.regs rFA (st₀.regs rFB), pos := st_c1.pos }
        let st4 : State := { mem := st₀.mem, regs := Function.update st3.regs rLA (st₀.regs rLB), pos := st_c1.pos }
        have hr1_VB : st_c1.regs rVB = st₀.regs rVB := hsc1_regs rVB hVB_cmp
        have hr2_FB : st2.regs rFB = st₀.regs rFB := by
          dsimp [st2]; rw [Function.update_of_ne (Ne.symm hVA_FB), hsc1_regs rFB hFB_cmp]
        have hr3_LB : st3.regs rLB = st₀.regs rLB := by
          dsimp [st3, st2]; rw [Function.update_of_ne (Ne.symm hFA_LB), Function.update_of_ne (Ne.symm hVA_LB), hsc1_regs rLB hLB_cmp]
        have hthen : Runs w p ω
            (Stmt.assign rVA (.reg rVB) ;; Stmt.assign rFA (.reg rFB) ;; Stmt.assign rLA (.reg rLB))
            st_c1 .normal st4 8 :=
          runs_seq_iff.mpr (Or.inr ⟨st2, 2, 5,
            runs_assign_iff.mpr ⟨st₀.regs rVB, Expr.eval_reg_of_eq hr1_VB, rfl, by simp [st2, hsc1_mem], rfl⟩,
            runs_seq_iff.mpr (Or.inr ⟨st3, 2, 2,
              runs_assign_iff.mpr ⟨st₀.regs rFB, Expr.eval_reg_of_eq hr2_FB, rfl, rfl, rfl⟩,
              runs_assign_iff.mpr ⟨st₀.regs rLB, Expr.eval_reg_of_eq hr3_LB, rfl, rfl, rfl⟩, rfl⟩), rfl⟩)
        have hrHA4 : st4.regs rHA = st₀.regs rHA := by
          dsimp [st4, st3, st2]
          rw [Function.update_of_ne hHA_LA, Function.update_of_ne hHA_FA, Function.update_of_ne hHA_VA, hsc1_regs rHA hHA_cmp]
        have hrVA4 : st4.regs rVA = st₀.regs rVB := by
          dsimp [st4, st3, st2]; rw [Function.update_of_ne hVA_LA, Function.update_of_ne hVA_FA, Function.update_self]
        have hrFA4 : st4.regs rFA = st₀.regs rFB := by
          dsimp [st4, st3]; rw [Function.update_of_ne hFA_LA, Function.update_self]
        have hrLA4 : st4.regs rLA = st₀.regs rLB := by dsimp [st4]; exact Function.update_self _ _ _
        have hsc1_cmp : st_c1.regs cmpReg = 1 := by simp [st_c1, hv1]
        refine ⟨st4, 1 + (1 + ((3 + c_less + 1) + 10 + 1) + 1) + 1, ?_, rfl, ?_, ?_, ?_, by omega⟩
        · refine runs_cond_iff.mpr ⟨st₀.regs rHB, _, Expr.eval_reg w rHB st₀, ?_, rfl⟩
          simp only [hHB0, ↓reduceIte]
          refine runs_cond_iff.mpr ⟨st₀.regs rHA, _, Expr.eval_reg w rHA st₀, ?_, rfl⟩
          simp only [hHA0, ↓reduceIte]
          refine runs_seq_iff.mpr (Or.inr ⟨st_c1, 3 + c_less + 1, 10, hcall_less, ?_, rfl⟩)
          refine runs_cond_iff.mpr ⟨1, 8, Expr.eval_reg_of_eq hsc1_cmp, ?_, rfl⟩
          simpa only [Nat.one_ne_zero, ↓reduceIte] using hthen
        · intro r hr1 hr2 hr3 hr4 hr5
          dsimp [st4, st3, st2]; rw [Function.update_of_ne hr4, Function.update_of_ne hr3,
            Function.update_of_ne hr2, hsc1_regs r hr5]
        · exact ⟨fun h => absurd h (by rw [hrHA4]; exact hHA0), fun _ => ⟨by rw [hrHA4]; exact hHA1, by rw [hrVA4]; exact hvb_ptr⟩⟩
        · have hlt' : B.val < A.val := by rw [hB_val, hA_val]; exact hlt
          change decodeNumAgg st4.mem h L (st4.regs rHA) (st4.regs rVA) (st4.regs rFA) (st4.regs rLA) =
            combineIntMinAgg A B
          have hrhs : combineIntMinAgg A B = B := by simp [combineIntMinAgg, hB_t, hA_t, hlt']
          rw [hrhs, hrHA4, hrVA4, hrFA4, hrLA4]
          simp [B, decodeNumAgg, hHB0, hHA0, st4]
      · have hv0 : cmpLess = 0 := by simp [hv_less, hlt]
        have hargs_eq : evalArgs w st_c1 [.reg rVA, .reg rVB, .reg LReg] =
            some [st₀.regs rVA, st₀.regs rVB, L] := by
          simp [evalArgs, Expr.eval, hsc1_regs rVA hVA_cmp, hsc1_regs rVB hVB_cmp, hsc1_regs LReg hL_cmp, hr_L]
        have hwords_eq : ∀ a ∈ ([st₀.regs rVA, st₀.regs rVB, L] : List ℕ), a < 2 ^ w := by
          have hva_lt : st₀.regs rVA < 2 ^ w :=
            lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ L) hva_ptr.2.2.1) hhp_lt
          have hvb_lt : st₀.regs rVB < 2 ^ w :=
            lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ L) hvb_ptr.2.2.1) hhp_lt
          have hL_lt : L < 2 ^ w :=
            lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left L (st₀.regs rVB)) hvb_ptr.2.2.1) hhp_lt
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with ha | ha | ha <;> rw [ha] <;> assumption
        have hpre_eq : (equalContract w h).pre [st₀.regs rVA, st₀.regs rVB, L] st_c1.mem := by
          rw [hsc1_mem]
          exact ⟨st₀.regs rVA, st₀.regs rVB, L, rfl, lt_of_le_of_lt hva_ptr.2.2.1 hhp_lt,
            lt_of_le_of_lt hvb_ptr.2.2.1 hhp_lt, hva_ptr.2.2.2, hvb_ptr.2.2.2⟩
        rcases hp_ok.equal_ok [st₀.regs rVA, st₀.regs rVB, L] st_c1.mem st_c1.pos ω hwords_eq hpre_eq with
          ⟨b_eq, hp_eq, o_eq, st_eq, c_eq, hr_eq, hpost_eq, hc_eq⟩
        rcases hpost_eq with ⟨hmem_eq, hv_eq⟩
        change st_eq.mem = st_c1.mem at hmem_eq
        let cmpEq := o_eq.value
        change cmpEq = (if intVal st_c1.mem (st₀.regs rVA) h L = intVal st_c1.mem (st₀.regs rVB) h L then 1 else 0) at hv_eq
        change c_eq ≤ 23 * L + 6 at hc_eq
        let st_c2 : State := { st_eq with regs := Function.update st_c1.regs cmpReg cmpEq }
        have hcall_eq : Runs w p ω (Stmt.call cmpReg sp.numEqual [.reg rVA, .reg rVB, .reg LReg]) st_c1
            .normal st_c2 (3 + c_eq + 1) :=
          runs_call_iff.mpr ⟨[st₀.regs rVA, st₀.regs rVB, L], b_eq, o_eq, st_eq, c_eq,
            hargs_eq, hp_eq, hr_eq, rfl, rfl, rfl⟩
        have hsc2_mem : st_c2.mem = st₀.mem := hmem_eq.trans hsc1_mem
        have hsc2_regs : ∀ r, r ≠ cmpReg → st_c2.regs r = st₀.regs r := fun r hr => by
          dsimp [st_c2]; rw [Function.update_of_ne hr, hsc1_regs r hr]
        by_cases heq : intVal st₀.mem (st₀.regs rVA) h L = intVal st₀.mem (st₀.regs rVB) h L
        · have hv_eq1 : cmpEq = 1 := by simp [hv_eq, hsc1_mem, heq]
          let st3 : State := { mem := st₀.mem, regs := Function.update st_c2.regs rLA (st₀.regs rLB), pos := st_c2.pos }
          have hsc2_cmp : st_c2.regs cmpReg = 1 := by simp [st_c2, hv_eq1]
          have hcond_eq : Runs w p ω (Stmt.cond (.reg cmpReg) (Stmt.assign rLA (.reg rLB)) Stmt.nop)
              st_c2 .normal st3 4 := by
            refine runs_cond_iff.mpr ⟨1, 2, Expr.eval_reg_of_eq hsc2_cmp, ?_, rfl⟩
            simp only [Nat.one_ne_zero, ↓reduceIte]
            exact runs_assign_iff.mpr ⟨st₀.regs rLB, Expr.eval_reg_of_eq (hsc2_regs rLB hLB_cmp), rfl, by simp [st3, hsc2_mem]⟩
          have hrHA3 : st3.regs rHA = st₀.regs rHA := by dsimp [st3]; rw [Function.update_of_ne hHA_LA, hsc2_regs rHA hHA_cmp]
          have hrVA3 : st3.regs rVA = st₀.regs rVA := by dsimp [st3]; rw [Function.update_of_ne hVA_LA, hsc2_regs rVA hVA_cmp]
          have hrFA3 : st3.regs rFA = st₀.regs rFA := by dsimp [st3]; rw [Function.update_of_ne hFA_LA, hsc2_regs rFA hFA_cmp]
          have hrLA3 : st3.regs rLA = st₀.regs rLB := by dsimp [st3]; exact Function.update_self _ _ _
          have hsc1_cmp0 : st_c1.regs cmpReg = 0 := by simp [st_c1, hv0]
          refine ⟨st3, 1 + (1 + ((3 + c_less + 1) + (1 + ((3 + c_eq + 1) + 4 + 1) + 1) + 1) + 1) + 1,
              ?_, rfl, ?_, ?_, ?_, by omega⟩
          · refine runs_cond_iff.mpr ⟨st₀.regs rHB, _, Expr.eval_reg w rHB st₀, ?_, rfl⟩
            simp only [hHB0, ↓reduceIte]
            refine runs_cond_iff.mpr ⟨st₀.regs rHA, _, Expr.eval_reg w rHA st₀, ?_, rfl⟩
            simp only [hHA0, ↓reduceIte]
            refine runs_seq_iff.mpr (Or.inr ⟨st_c1, 3 + c_less + 1, 1 + ((3 + c_eq + 1) + 4 + 1) + 1, hcall_less, ?_, rfl⟩)
            refine runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq hsc1_cmp0, ?_, rfl⟩
            simp only [↓reduceIte]
            exact runs_seq_iff.mpr (Or.inr ⟨st_c2, 3 + c_eq + 1, 4, hcall_eq, hcond_eq, rfl⟩)
          · intro r _ _ _ hr4 hr5; dsimp [st3]; rw [Function.update_of_ne hr4, hsc2_regs r hr5]
          · exact ⟨fun h => absurd h (by rw [hrHA3]; exact hHA0), fun _ => ⟨by rw [hrHA3]; exact hHA1, by rw [hrVA3]; exact hva_ptr⟩⟩
          · have hlt' : ¬ B.val < A.val := by rw [hB_val, hA_val]; exact hlt
            have heq' : A.val = B.val := by rw [hA_val, hB_val]; exact heq
            change decodeNumAgg st3.mem h L (st3.regs rHA) (st3.regs rVA) (st3.regs rFA) (st3.regs rLA) =
              combineIntMinAgg A B
            have hrhs : combineIntMinAgg A B = { A with last := B.last } := by
              simp [combineIntMinAgg, hB_t, hA_t, heq']
            rw [hrhs, hrHA3, hrVA3, hrFA3, hrLA3]
            simp [A, B, decodeNumAgg, hHA0, st3]
        · have hv_eq0 : cmpEq = 0 := by simp [hv_eq, hsc1_mem, heq]
          have hsc2_cmp0 : st_c2.regs cmpReg = 0 := by simp [st_c2, hv_eq0]
          have hcond_eq : Runs w p ω (Stmt.cond (.reg cmpReg) (Stmt.assign rLA (.reg rLB)) Stmt.nop)
              st_c2 .normal st_c2 3 :=
            runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq hsc2_cmp0,
              by simp [runs_nop_iff], rfl⟩
          have hrHA2 : st_c2.regs rHA = st₀.regs rHA := hsc2_regs rHA hHA_cmp
          have hrVA2 : st_c2.regs rVA = st₀.regs rVA := hsc2_regs rVA hVA_cmp
          have hrFA2 : st_c2.regs rFA = st₀.regs rFA := hsc2_regs rFA hFA_cmp
          have hrLA2 : st_c2.regs rLA = st₀.regs rLA := hsc2_regs rLA hLA_cmp
          have hsc1_cmp0 : st_c1.regs cmpReg = 0 := by simp [st_c1, hv0]
          refine ⟨st_c2, 1 + (1 + ((3 + c_less + 1) + (1 + ((3 + c_eq + 1) + 3 + 1) + 1) + 1) + 1) + 1,
              ?_, hsc2_mem, ?_, ?_, ?_, by omega⟩
          · refine runs_cond_iff.mpr ⟨st₀.regs rHB, _, Expr.eval_reg w rHB st₀, ?_, rfl⟩
            simp only [hHB0, ↓reduceIte]
            refine runs_cond_iff.mpr ⟨st₀.regs rHA, _, Expr.eval_reg w rHA st₀, ?_, rfl⟩
            simp only [hHA0, ↓reduceIte]
            refine runs_seq_iff.mpr (Or.inr ⟨st_c1, 3 + c_less + 1, 1 + ((3 + c_eq + 1) + 3 + 1) + 1, hcall_less, ?_, rfl⟩)
            refine runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq hsc1_cmp0, ?_, rfl⟩
            simp only [↓reduceIte]
            exact runs_seq_iff.mpr (Or.inr ⟨st_c2, 3 + c_eq + 1, 3, hcall_eq, hcond_eq, rfl⟩)
          · intro r _ _ _ _ hr5; exact hsc2_regs r hr5
          · refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [hrHA2] at h; rw [hrVA2, hrFA2, hrLA2]; exact hca.1 h
            · rw [hrHA2] at h; rw [hrHA2, hrVA2, hsc2_mem]; exact hca.2 h
          · have hlt' : ¬ B.val < A.val := by rw [hB_val, hA_val]; exact hlt
            have heq' : A.val ≠ B.val := by rw [hA_val, hB_val]; exact heq
            change decodeNumAgg st_c2.mem h L (st_c2.regs rHA) (st_c2.regs rVA) (st_c2.regs rFA) (st_c2.regs rLA) =
              combineIntMinAgg A B
            have hrhs : combineIntMinAgg A B = A := by simp [combineIntMinAgg, hB_t, hA_t, hlt', heq']
            rw [hrhs, hrHA2, hrVA2, hrFA2, hrLA2]
            simp [A, decodeNumAgg, hsc2_mem]

theorem pullBody_zero_triple {w L nodesBase : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos : ℕ) (hw : 0 < 2 ^ w) :
    Triple w p
      (fun st => st = startState [nodesBase, 0] mem₀ pos)
      (pullBody sp)
      (retPost fun v st' => v = 0 ∧ st'.mem = mem₀)
      (fun _ => K_PULL L) := by
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  have hcond : (Expr.reg 1).eval w (startState [nodesBase, 0] mem₀ pos) = some 0 := by
    simp [startState, Expr.eval]
  refine ⟨.returned 0, startState [nodesBase, 0] mem₀ pos, 4, ?_, ⟨rfl, rfl⟩,
    by dsimp only; unfold K_PULL; omega⟩
  refine runs_cond_iff.mpr ⟨0, 2, hcond, ?_, rfl⟩
  exact runs_ret_iff.mpr ⟨0, Expr.eval_const hw, rfl, rfl, rfl⟩

end

end MinCostFlow.LinkCut.Prog
