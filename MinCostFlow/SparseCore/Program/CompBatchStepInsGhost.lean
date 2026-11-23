module

public import MinCostFlow.SparseCore.Program.CompBatchStepInsBase
import WordRAM.Tactic

/-!
# Edge-Insertion Step: Cross-Component Helpers (`CompBatchStepInsGhost`)

Since cross-inserts are projected to insert-then-delete self-loops:
1. `compStepInsCrossPre_runs`: marks `isCross[e] := 1` and marks both endpoint components `c1`, `c2`
   touched via `compMarkTouchProc` (no ghost lists are populated).
2. `compStepInsDelPairDisp_runs`: executes
   `compStepInsDispStmt bDisp rC rA rA ;; compStepInsDelOnlyDispStmt bDisp rC` on one component `c`,
   applying `[.insert e ua ua, .delete e]` across all `k` branches. By
   `applyLSFBatch_insert_delete_selfLoop`, the `.delete e` step adds zero new roots and zero forest
   cuts, so the combined cut log equals that of `.insert e ua ua`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Pure RF preservation on `[.insert e a a, .delete e]` -/

/-- Applying `.delete e` right after `.insert e a a` leaves `R_orig`, `RF.F.E`, and `RF.R`
identical to the post-insert state `S₁ = applyLSFUpdate S (.insert e a a)`. -/
lemma applyLSFBatch_insert_delete_selfLoop_RF {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) {e a : ℕ} (he : e ∉ S.G.E) (ha : a ∈ S.G.V) :
    let S₁ := applyLSFUpdate S (.insert e a a)
    let S₂ := applyLSFBatch S [.insert e a a, .delete e]
    S₂.R_orig = S₁.R_orig ∧ S₂.RF.F.E = S₁.RF.F.E ∧ S₂.RF.R = S₁.RF.R := by
  classical
  intro S₁ S₂
  have hspec := applyLSFBatch_insert_delete_selfLoop hI he ha
  have hReq : S₂.R = S₁.R := hspec.2.2.2.2.2.2
  have hI1 : LSFInvWith thresh K_σ ℓ₀ S₁ :=
    (applyLSFBatch_inv_with [.insert e a a] hI ⟨⟨he, ha, ha⟩, trivial⟩).1
  have hI2 : LSFInvWith thresh K_σ ℓ₀ S₂ :=
    (applyLSFBatch_inv_with [.insert e a a, .delete e] hI hspec.1).1
  have hS1 := LSFInvWith.toStructInv hI1
  have hS2 := LSFInvWith.toStructInv hI2
  have hR_orig : S₂.R_orig = S₁.R_orig := by
    apply Finset.Subset.antisymm
    · intro r hr
      have hrR1 : r ∈ S₁.R := hReq ▸ Finset.mem_union_left _ hr
      have hrT0 : r ∈ S₁.T₀.V := by
        have hsub : S₂.R_orig ⊆ S₂.T₀.V := hS2.R_orig_sub
        exact hsub hr
      rcases Finset.mem_union.mp hrR1 with h1 | h2
      · exact h1
      · exact absurd h2 (Finset.disjoint_left.mp hS1.hdisj_iso hrT0)
    · exact compApplyLSFUpdate_R_orig_sub S₁ (.delete e)
  have hFE : S₂.RF.F.E = S₁.RF.F.E := by
    dsimp only [LSFState.RF, forestGivenRoots]
    change S₁.T₀.E \ deletedEdges S₁.T₀ S₁.r₀ S₂.R_orig S₁.π =
      S₁.T₀.E \ deletedEdges S₁.T₀ S₁.r₀ S₁.R_orig S₁.π
    rw [hR_orig]
  exact ⟨hR_orig, hFE, hReq⟩

/-! ## 2. Cross-insert prefix verification (`compStepInsCrossPre_runs`) -/

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compStepInsCrossPreStmt` starting from the post-prefix state `stP` when
`c1 ≠ c2`. Sets `isCross[e] := 1` and marks `c1, c2` touched while preserving registers `0..19`
and all other memory regions (including ghost tables). -/
lemma compStepInsCrossPre_runs {W : LSFWindowImpl}
    {w k b bCons bMark uPtr heap cntBase updBuf e a bVert : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (heCap : e < x.eCap)
    (c1 c2 : Fin x.numComps) (h12 : c1 ≠ c2)
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 5 < 2 ^ w)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    {stP : State}
    (hstP_regs : stP.regs 0 = b ∧ stP.regs 1 = uPtr ∧ stP.regs 2 = heap ∧ stP.regs 3 = cntBase ∧
      stP.regs 4 = updBuf ∧ stP.regs 5 = e ∧ stP.regs 6 = a ∧ stP.regs 7 = bVert ∧
      stP.regs 8 = x.vCap ∧ stP.regs 9 = x.eCap ∧ stP.regs 11 = c1.1 ∧ stP.regs 12 = c2.1 ∧
      stP.regs 16 = compTouchMarkBase b x.vCap x.eCap ∧ stP.regs 17 = heap + 1 ∧
      stP.regs 18 = compEdgefulBase b x.vCap ∧ stP.regs 19 = compEdgefulIdxBase b x.vCap)
    (hstP_mem : stP.mem = Function.update (Function.update (Function.update mem
      (compEdgeC1Base b x.vCap + e) c1.1) (compEdgeC2Base b x.vCap x.eCap + e) c2.1)
      (compIsInsBase b x.vCap x.eCap + e) 1) :
    ∃ stM2 cPre, ∃ (touched' : List ℕ),
      Runs w p ω (compStepInsCrossPreStmt bCons bMark) stP .normal stM2 cPre ∧
      cPre ≤ 160 ∧
      (∀ r < 20, stM2.regs r = stP.regs r) ∧
      touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
      touched'.length ≤ touched.length + 2 ∧
      (∀ c : Fin x.numComps, c.1 ∈ touched' ↔ c.1 ∈ touched ∨ c = c1 ∨ c = c2) ∧
      stM2.mem heap = touched'.length ∧
      ListAt stM2.mem (heap + 1) touched' ∧
      (∀ z < compEdgeC1Base b x.vCap, stM2.mem z = mem z) ∧
      (∀ f < x.eCap,
        stM2.mem (compEdgeC1Base b x.vCap + f) =
          (if f = e then c1.1 else mem (compEdgeC1Base b x.vCap + f)) ∧
        stM2.mem (compEdgeC2Base b x.vCap x.eCap + f) =
          (if f = e then c2.1 else mem (compEdgeC2Base b x.vCap x.eCap + f)) ∧
        stM2.mem (compIsCrossBase b x.vCap x.eCap + f) =
          (if f = e then 1 else mem (compIsCrossBase b x.vCap x.eCap + f)) ∧
        stM2.mem (compIsInsBase b x.vCap x.eCap + f) =
          (if f = e then 1 else mem (compIsInsBase b x.vCap x.eCap + f))) ∧
      (∀ z, compGhostBase b x.vCap x.eCap ≤ z → z < compTouchMarkBase b x.vCap x.eCap →
        stM2.mem z = mem z) ∧
      (∀ c < x.vCap, stM2.mem (compTouchMarkBase b x.vCap x.eCap + c) =
        if c ∈ touched' then 1 else 0) ∧
      (∀ z, compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ z →
        z ≠ heap → (z < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ z) →
        stM2.mem z = mem z) := by
  obtain ⟨_, _, _, _, _, _, _, hnumC, _, hTE, hhdr, _, _, _, _, _, _, _, _, _, hTM, _, _, _⟩ := hrep
  have h12_val : c1.1 ≠ c2.1 := fun h => h12 (Fin.ext h)
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hte_w ⊢; omega
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  have hw16' : 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have hb16 : b + 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have htm_w : compTouchMarkBase b x.vCap x.eCap + x.vCap < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
      compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have htm_lt_end : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ x.endAddr := by
    have : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
        compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have h_iscr_w : compIsCrossBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsCrossBase, compEdgeC2Base,
      compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
      compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hmP_fr : ∀ z, z ≠ compEdgeC1Base b x.vCap + e → z ≠ compEdgeC2Base b x.vCap x.eCap + e →
      z ≠ compIsInsBase b x.vCap x.eCap + e → stP.mem z = mem z := fun z h1 h2 h3 => by
    rw [hstP_mem, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hmP_ec1 : stP.mem (compEdgeC1Base b x.vCap + e) = c1.1 := by
    rw [hstP_mem, Function.update_of_ne (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega),
        Function.update_of_ne (by dsimp only [compEdgeC2Base]; omega), Function.update_self]
  have hmP_ec2 : stP.mem (compEdgeC2Base b x.vCap x.eCap + e) = c2.1 := by
    rw [hstP_mem, Function.update_of_ne (by dsimp only [compIsInsBase, compIsCrossBase]; omega), Function.update_self]
  have hmP_ins : stP.mem (compIsInsBase b x.vCap x.eCap + e) = 1 := by rw [hstP_mem, Function.update_self]
  let mX1 := Function.update stP.mem (compIsCrossBase b x.vCap x.eCap + e) 1
  let stX1 : State := { stP with regs := Function.update stP.regs 20 (compIsCrossBase b x.vCap x.eCap) }
  let stX2 : State := { stX1 with mem := mX1 }
  have hh_16 : mem (b + 16) = compIsCrossBase b x.vCap x.eCap := by
    simpa [compOffIsCrossPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrun_x1 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr)))) stP .normal stX1 5 := by
    rw [runs_assign_iff]; refine ⟨compIsCrossBase b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h16 : b + 16 ≠ compEdgeC1Base b x.vCap + e ∧ b + 16 ≠ compEdgeC2Base b x.vCap x.eCap + e ∧
        b + 16 ≠ compIsInsBase b x.vCap x.eCap + e := by
      dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]
      exact ⟨by omega, by omega, by omega⟩
    simp [Expr.eval, BinOp.eval, hstP_regs.1, compOffIsCrossPtr, hw16', hb16,
      hmP_fr _ h16.1 h16.2.1 h16.2.2, hh_16]
  have hrun_x2 : Runs w p ω (.store (.bin .add (.reg 20) (.reg 5)) (.const 1)) stX1 .normal stX2 5 := by
    rw [runs_store_iff]; refine ⟨compIsCrossBase b x.vCap x.eCap + e, 1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [Expr.eval, BinOp.eval, stX1, hstP_regs.2.2.2.2.2.1, h_iscr_w]
    · simp [Expr.eval, hw0]
  have hmX1_lt_ec1 : ∀ z < compEdgeC1Base b x.vCap, mX1 z = mem z := fun z hz => by
    dsimp only [mX1]
    rw [Function.update_of_ne (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega)]
    exact hmP_fr z (by omega) (by dsimp only [compEdgeC2Base]; omega)
      (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)
  have hmX1_ge_g : ∀ z, compGhostBase b x.vCap x.eCap ≤ z → mX1 z = mem z := fun z hz => by
    dsimp only [mX1]
    rw [Function.update_of_ne (by dsimp only [compGhostBase, compIsInsBase] at hz; omega)]
    exact hmP_fr z (by dsimp only [compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base] at hz; omega)
      (by dsimp only [compGhostBase, compIsInsBase, compIsCrossBase] at hz; omega)
      (by dsimp only [compGhostBase] at hz; omega)
  have hmX1_ge_tm : ∀ z, compTouchMarkBase b x.vCap x.eCap ≤ z → mX1 z = mem z := fun z hz =>
    hmX1_ge_g z (by dsimp only [compTouchMarkBase, compGhostSize] at hz; omega)
  -- `compMarkTouch` #1 on `c1`
  have hmk1_eq : mX1 (compTouchMarkBase b x.vCap x.eCap + c1.1) = if c1.1 ∈ touched then 1 else 0 :=
    (hmX1_ge_tm _ (Nat.le_add_right _ _)).trans (hTM c1.1 (by have := c1.2; omega))
  obtain ⟨oM1, stM1, cM1, hrunM1, _, hmkM1, hcntM1, hlistM1, hfrM1, hcM1⟩ :=
    compMarkTouch_call (cap := x.vCap) (L := touched) (c := c1.1) (pos := stX2.pos) (ω := ω)
      hpMark hw16 (by have := c1.2; omega) htm_w (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun i hi => ⟨by omega, by omega⟩)
      ((hmX1_ge_tm heap (by omega)).trans hcnt_touch)
      (fun i hi => (hmX1_ge_tm (heap + 1 + i) (by omega)).trans (hlist_touch i hi))
      (by rw [hmk1_eq]; split_ifs <;> simp)
  set touched1 := if mX1 (compTouchMarkBase b x.vCap x.eCap + c1.1) = 0 then touched ++ [c1.1] else touched
  have htouch1_len : touched1.length ≤ touched.length + 1 := by dsimp only [touched1]; split_ifs <;> simp
  let stX3 : State := { stX2 with regs := Function.update stX2.regs 20 oM1.value, mem := stM1.mem, pos := stM1.pos }
  have hrun_m1 : Runs w p ω (.call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 11]) stX2 .normal stX3 (cM1 + 5) := by
    rw [runs_call_iff]
    refine ⟨[compTouchMarkBase b x.vCap x.eCap, heap + 1, heap, c1.1], compMarkTouchProc,
      oM1, stM1, cM1, ?_, hpMark, hrunM1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, stX2, stX1, hstP_regs.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.2.2.1,
      hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  -- `compMarkTouch` #2 on `c2`
  have hmk2_eq : stM1.mem (compTouchMarkBase b x.vCap x.eCap + c2.1) = if c2.1 ∈ touched then 1 else 0 :=
    (hfrM1 _ (by omega) (by have := c2.2; omega) (by have := c2.2; omega)).trans
      ((hmX1_ge_tm _ (Nat.le_add_right _ _)).trans (hTM c2.1 (by have := c2.2; omega)))
  obtain ⟨oM2, stM2_inner, cM2, hrunM2, _, hmkM2, hcntM2, hlistM2, hfrM2, hcM2⟩ :=
    compMarkTouch_call (cap := x.vCap) (L := touched1) (c := c2.1) (pos := stX3.pos) (ω := ω)
      hpMark hw16 (by have := c2.2; omega) htm_w (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun i hi => ⟨by omega, by omega⟩) hcntM1 hlistM1 (by rw [hmk2_eq]; split_ifs <;> simp)
  set touched' := if stM1.mem (compTouchMarkBase b x.vCap x.eCap + c2.1) = 0 then touched1 ++ [c2.1] else touched1
  let stM2 : State := { stX3 with regs := Function.update stX3.regs 20 oM2.value, mem := stM2_inner.mem, pos := stM2_inner.pos }
  have hrun_m2 : Runs w p ω (.call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 12]) stX3 .normal stM2 (cM2 + 5) := by
    rw [runs_call_iff]
    refine ⟨[compTouchMarkBase b x.vCap x.eCap, heap + 1, heap, c2.1], compMarkTouchProc,
      oM2, stM2_inner, cM2, ?_, hpMark, hrunM2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, stX3, stX2, stX1, hstP_regs.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.2.2.2.1,
      hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hrun_all : Runs w p ω (compStepInsCrossPreStmt bCons bMark) stP .normal stM2 (cM1 + cM2 + 23) :=
    runs_seq_iff.mpr (Or.inr ⟨stX1, 5, _, hrun_x1,
      runs_seq_iff.mpr (Or.inr ⟨stX2, 5, _, hrun_x2,
        runs_seq_iff.mpr (Or.inr ⟨stX3, cM1 + 5, cM2 + 5, hrun_m1, hrun_m2, rfl⟩), rfl⟩), by omega⟩)
  have hM2_below_tm : ∀ z < compTouchMarkBase b x.vCap x.eCap, stM2.mem z = mX1 z := fun z hz =>
    (hfrM2 z (by omega) (by omega) (by omega)).trans (hfrM1 z (by omega) (by omega) (by omega))
  have htouch1_iff : ∀ c : ℕ, c ∈ touched1 ↔ c ∈ touched ∨ c = c1.1 := fun c => by
    dsimp only [touched1]; rw [hmk1_eq]
    by_cases h1 : c1.1 ∈ touched
    · simp only [h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; exact ⟨Or.inl, fun h => h.elim id (fun h' => h' ▸ h1)⟩
    · simp only [h1, ↓reduceIte, List.mem_append, List.mem_singleton]
  have htouch'_iff_nat : ∀ c : ℕ, c ∈ touched' ↔ c ∈ touched ∨ c = c1.1 ∨ c = c2.1 := fun c => by
    dsimp only [touched']; rw [hmk2_eq]
    by_cases h2 : c2.1 ∈ touched
    · simp only [h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega, htouch1_iff]
      exact ⟨fun h => h.elim Or.inl (fun h' => Or.inr (Or.inl h')),
        fun h => h.elim Or.inl (fun h' => h'.elim Or.inr (fun h'' => Or.inl (h'' ▸ h2)))⟩
    · simp only [h2, ↓reduceIte, List.mem_append, List.mem_singleton, htouch1_iff]; tauto
  have htouch1_nd : touched1.Nodup := by
    dsimp only [touched1]; rw [hmk1_eq]
    by_cases h1 : c1.1 ∈ touched
    · simp only [h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; exact htouch_nd
    · simp only [h1, ↓reduceIte]
      exact List.nodup_append.mpr ⟨htouch_nd, List.nodup_singleton _, fun z hz w hw heq => h1 (List.mem_singleton.mp hw ▸ heq ▸ hz)⟩
  have htouch'_nd : touched'.Nodup := by
    dsimp only [touched']; rw [hmk2_eq]
    by_cases h2 : c2.1 ∈ touched
    · simp only [h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; exact htouch1_nd
    · simp only [h2, ↓reduceIte]
      refine List.nodup_append.mpr ⟨htouch1_nd, List.nodup_singleton _, fun z hz w hw heq => ?_⟩
      have hzc2 : z = c2.1 := heq.trans (List.mem_singleton.mp hw)
      rcases (htouch1_iff z).mp hz with h | h
      · exact h2 (hzc2 ▸ h)
      · exact h12_val (h.symm.trans hzc2)
  have htouch'_len : touched'.length ≤ touched.length + 2 := by
    dsimp only [touched']; split_ifs
    · simp only [List.length_append, List.length_singleton]; omega
    · omega
  refine ⟨stM2, cM1 + cM2 + 23, touched', hrun_all, by omega,
    fun r hr => by simp [stM2, stX3, stX2, stX1, show r ≠ 20 by omega],
    htouch'_nd,
    fun c hc => by rcases (htouch'_iff_nat c).mp hc with h | rfl | rfl; exact htouch_lt c h; exact c1.2; exact c2.2,
    htouch'_len,
    fun c => by rw [htouch'_iff_nat c.1]; exact ⟨fun h => h.imp id (fun h' => h'.imp Fin.ext Fin.ext),
      fun h => h.imp id (fun h' => h'.imp (congrArg Fin.val) (congrArg Fin.val))⟩,
    hcntM2, hlistM2,
    fun z hz => (hM2_below_tm z (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)).trans (hmX1_lt_ec1 z hz),
    fun f hf => by
      have h1 := hM2_below_tm (compEdgeC1Base b x.vCap + f) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)
      have h2 := hM2_below_tm (compEdgeC2Base b x.vCap x.eCap + f) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega)
      have h3 := hM2_below_tm (compIsCrossBase b x.vCap x.eCap + f) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase]; omega)
      have h4 := hM2_below_tm (compIsInsBase b x.vCap x.eCap + f) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize]; omega)
      rw [h1, h2, h3, h4]
      by_cases hfe : f = e
      · subst hfe
        refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega), hmP_ec1]; simp
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsCrossBase]; omega), hmP_ec2]; simp
        · dsimp only [mX1]; rw [Function.update_self]; simp
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsInsBase]; omega), hmP_ins]; simp
      · refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega),
            hmP_fr _ (by omega) (by dsimp only [compEdgeC2Base]; omega) (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)]; simp [hfe]
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsCrossBase]; omega),
            hmP_fr _ (by dsimp only [compEdgeC2Base]; omega) (by omega) (by dsimp only [compIsInsBase, compIsCrossBase]; omega)]; simp [hfe]
        · dsimp only [mX1]; rw [Function.update_of_ne (by omega : compIsCrossBase b x.vCap x.eCap + f ≠ compIsCrossBase b x.vCap x.eCap + e),
            hmP_fr _ (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega) (by dsimp only [compIsCrossBase]; omega) (by dsimp only [compIsInsBase]; omega)]; simp [hfe]
        · dsimp only [mX1]; rw [Function.update_of_ne (by dsimp only [compIsInsBase]; omega),
            hmP_fr _ (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega) (by dsimp only [compIsInsBase, compIsCrossBase]; omega) (by omega)]; simp [hfe]
    ,
    fun z h1 h2 => (hM2_below_tm z h2).trans (hmX1_ge_g z h1),
    fun c hc => by
      by_cases hc2 : c = c2.1
      · subst hc2; rw [hmkM2, ite_eq_left ((htouch'_iff_nat c2.1).mpr (Or.inr (Or.inr rfl)))]
      · rw [hfrM2 _ (by omega) (by omega) (by omega)]
        by_cases hc1 : c = c1.1
        · subst hc1; rw [hmkM1, ite_eq_left ((htouch'_iff_nat c1.1).mpr (Or.inr (Or.inl rfl)))]
        · rw [hfrM1 _ (by omega) (by omega) (by omega), hmX1_ge_tm _ (Nat.le_add_right _ _), hTM c hc]
          have hiff : c ∈ touched' ↔ c ∈ touched := by rw [htouch'_iff_nat]; tauto
          simp [hiff],
    fun z hge hnh hnl => by
      have hne1 : z ≠ heap + 1 + touched1.length := by
        have : touched.length ≤ touched1.length := by dsimp only [touched1]; split_ifs <;> simp
        omega
      have hne0 : z ≠ heap + 1 + touched.length := by omega
      exact (hfrM2 z (by have := c2.2; omega) hnh hne1).trans
        ((hfrM1 z (by have := c1.2; omega) hnh hne0).trans (hmX1_ge_tm z (by omega)))⟩

/-! ## 3. Paired `[.insert e ua ua, .delete e]` dispatch (`compStepInsDelPairDisp_runs`) -/

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of `compStepInsDispStmt bDisp rC rA rA ;; compStepInsDelOnlyDispStmt bDisp rC`:
dispatches `.insert e ua ua` followed immediately by `.delete e` on component `c` (if edgeful; or
`.nop` twice if isolated). By `applyLSFBatch_insert_delete_selfLoop_RF`, the `.delete e` step emits
zero cuts, so the cut log matches the single `.insert e ua ua` step while the final component state
equals `applyLSFBatch Sj [.insert e ua ua, .delete e]`. -/
lemma compStepInsDelPairDisp_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bDisp cntBase updBuf rC rA e ua : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k} {cnts : Fin k → ℕ}
    {st : State} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k) (hLw : 1 ≤ x.L_w)
    (hrC_lt : rC < 20) (hrA_lt : rA < 20)
    (c : Fin x.numComps)
    (hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂)
    (hef_pos : ∀ ec : Fin x.numEdgeful, 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf (x.edgefulComp ec))).m)
    (hI_all : ∃ ℓ₀, ∀ j : Fin k, CompLSFInv W.C_lsst ℓ₀ (S j) ∧ (S j).G₀ = (S ⟨0, hk⟩).G₀ ∧
      ((S j).compSt (x.compOf c)).G = ((S ⟨0, hk⟩).compSt (x.compOf c)).G)
    (hC_mem : x.compOf c ∈ components (S ⟨0, hk⟩).G₀)
    (hr0 : st.regs 0 = b) (hr3 : st.regs 3 = cntBase) (hr4 : st.regs 4 = updBuf)
    (hr5 : st.regs 5 = e) (hr18 : st.regs 18 = compEdgefulBase b x.vCap)
    (hr19 : st.regs 19 = compEdgefulIdxBase b x.vCap)
    (hrC : st.regs rC = c.1) (hrA : st.regs rA = ua)
    (hnumC : x.numComps ≤ x.vCap)
    (hend_le : x.endAddr ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 5 < 2 ^ w)
    (hz : ZeroFrom st.mem updBuf)
    (hcnts_m : ∀ j : Fin k, st.mem (cntBase + j.1) = cnts j)
    (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hef_m : st.mem (compEdgefulBase b x.vCap + c.1) =
      if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0)
    (hef_spec : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx c = ec.1 ∧
        st.mem (compEdgefulIdxBase b x.vCap + c.1) = ec.1 ∧ x.edgefulComp ec = c ∧
        CompDispatchWinOk W k b S x ec st.mem)
    (hcap : ∀ j : Fin k,
      let Sj := (S j).compSt (x.compOf c)
      cnts j + ((applyLSFUpdate Sj (.insert e ua ua)).R_orig \ Sj.R_orig).card ≤ x.vCap)
    (hu_valid : ((S ⟨0, hk⟩).compSt (x.compOf c)).G.UpdateIsValid (.insert e ua ua))
    (heCap : e < x.eCap) (hua : ua < x.vCap) :
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (cuts : Fin k → List (ℕ × ℕ)) (winConc' : Fin x.numEdgeful → Fin k → LSFConcrete),
      Runs w p ω (compStepInsDispStmt bDisp rC rA rA ;; compStepInsDelOnlyDispStmt bDisp rC) st .normal st' cost ∧
      (∀ r < 20, st'.regs r = st.regs r) ∧
      (∀ j : Fin k,
        let Sj := (S j).compSt (x.compOf c)
        let Sj1 := applyLSFUpdate Sj (.insert e ua ua)
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        (1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m →
          CompForestCutsValid x.vCap Sj.RF (cuts j) ∧
          ((cuts j).foldl compApplyForestCut Sj.RF).F.E = Sj1.RF.F.E ∧
          ((cuts j).map Prod.fst).Nodup ∧
          ((cuts j).map Prod.fst).toFinset = Sj.RF.F.E \ Sj1.RF.F.E ∧
          ((cuts j).map Prod.snd).Nodup ∧
          ((cuts j).map Prod.snd).toFinset = Sj1.RF.R \ Sj.RF.R) ∧
        ((compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m = 0 → cuts j = [])) ∧
      (∀ (ec : Fin x.numEdgeful) (j : Fin k),
        (x.edgefulComp ec = c →
          SameStaticConcrete (x.winConc ec j) (winConc' ec j) ∧
          (LSFRep W.h).rep (x.winHandle ec j)
            (applyLSFBatch ((S j).compSt (x.compOf c)) [.insert e ua ua, .delete e])
            (winConc' ec j) st'.mem) ∧
        (x.edgefulComp ec ≠ c → winConc' ec j = x.winConc ec j)) ∧
      (∀ a,
        (∀ ec j, x.edgefulComp ec = c → ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = st.mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      (if _ : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then
        ∃ ec : Fin x.numEdgeful, x.edgefulComp ec = c ∧
          cost + 120 * (∑ j : Fin k, (cuts j).length) +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) st'.mem) ≤
            k * (lsfBatchCostFactor * (8 * x.L_w + 2) + 1700) + 600 +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) st.mem)
      else cost ≤ 40 ∧ ∀ a, st'.mem a = st.mem a) := by
  intro rootsBase fDelBase
  obtain ⟨ℓ₀, hI_all⟩ := hI_all
  obtain ⟨st1, c1, cuts, winConc1, hrun1, hregs1, hbr1, hwin1, hfr1, hz1, hcost1⟩ :=
    compStepInsDisp_runs (rC := rC) (rA := rA) (rB := rA) (cnts := cnts) (st := st) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpDisp hw16 hk hLw hrC_lt hrA_lt hrA_lt c
      hefComp_inj hef_pos hr0 hr3 hr4 hr5 hr18 hr19 hrC hrA hrA
      hnumC hend_le hcnt_buf hbuf_w hz hcnts_m hTE hef_m hef_spec hcap hu_valid heCap hua hua
  have hef_w : compEdgefulBase b x.vCap + c.1 < 2 ^ w := by
    have : compEdgefulBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase,
        compHdrSize]; have := c.2; omega
    omega
  have hefIdx_w : compEdgefulIdxBase b x.vCap + c.1 < 2 ^ w := by
    have : compEdgefulIdxBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase,
        compEdgefulBase, compVCompBase, compHdrSize]; have := c.2; omega
    omega
  have he_w : e < 2 ^ w := by
    have : x.eCap < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hst1_below_te : ∀ z < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k, st1.mem z = st.mem z := fun z hz' => by
    by_cases hp : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m
    · obtain ⟨ec, _, _, hcomp, hwin⟩ := hef_spec hp
      exact hfr1 z (fun ec' j hcomp' ha => by
        have heq : ec' = ec := hefComp_inj ec' ec (hcomp'.trans hcomp.symm)
        subst heq; exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hz' (hwin.2.2.2.2.2.2.2.2.1 j).2.2.2.2.2.1)))
        (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)
    · rw [dite_eq_right hp] at hcost1; exact hcost1.2 z
  have hef_m1 : st1.mem (compEdgefulBase b x.vCap + c.1) =
      if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0 :=
    (hst1_below_te _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase,
      compVCompBase, compHdrSize]; have := c.2; omega)).trans hef_m
  set isEf := if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0
  let st2a : State := { st1 with regs := Function.update st1.regs 23 isEf }
  have hrun2a : Runs w p ω (.assign 23 (.load (.bin .add (.reg 18) (.reg rC)))) st1 .normal st2a 5 := by
    rw [runs_assign_iff]; refine ⟨isEf, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [Expr.eval, BinOp.eval, hregs1 18 (by omega), hr18, hregs1 rC hrC_lt, hrC, hef_w, hef_m1, isEf]
  by_cases hpos : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m
  · have hisEf : isEf = 1 := ite_eq_left hpos
    obtain ⟨ec, _, hec_m, hec_comp, hwin⟩ := hef_spec hpos
    rw [dite_eq_left hpos] at hcost1
    obtain ⟨ec', hec'_comp, hcost1_le⟩ := hcost1
    have hec_eq : ec' = ec := hefComp_inj ec' ec (hec'_comp.trans hec_comp.symm)
    subst ec'
    have hst2a_r : ∀ r < 20, st2a.regs r = st.regs r := fun r hr => by
      simp [st2a, show r ≠ 23 by omega, hregs1 r hr]
    let m1 := Function.update st1.mem updBuf 1
    let m2 := Function.update m1 (updBuf + 1) 1
    let m3 := Function.update m2 (updBuf + 2) e
    have hm3_lt : ∀ a < updBuf, m3 a = st1.mem a := fun a ha => by
      simp [m3, m2, m1, Function.update_of_ne (show a ≠ updBuf + 2 by omega),
        Function.update_of_ne (show a ≠ updBuf + 1 by omega),
        Function.update_of_ne (show a ≠ updBuf by omega)]
    have hm3_ge : ∀ a ≥ updBuf + 3, m3 a = st1.mem a := fun a ha => by
      simp [m3, m2, m1, Function.update_of_ne (show a ≠ updBuf + 2 by omega),
        Function.update_of_ne (show a ≠ updBuf + 1 by omega),
        Function.update_of_ne (show a ≠ updBuf by omega)]
    let s1 : State := { st2a with mem := m1 }
    let s2 : State := { st2a with mem := m2 }
    let s3 : State := { st2a with mem := m3 }
    let s4 : State := { s3 with regs := Function.update s3.regs 24 ec.1 }
    have hs1 : Runs w p ω (.store (.reg 4) (.const 1)) st2a .normal s1 3 :=
      runs_store_iff.mpr ⟨updBuf, 1, by simp [Expr.eval, hst2a_r 4 (by omega), hr4], by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
    have hs2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.const 1)) s1 .normal s2 5 :=
      runs_store_iff.mpr ⟨updBuf + 1, 1,
        by simp [s1, Expr.eval, BinOp.eval, hst2a_r 4 (by omega), hr4, hw0, show updBuf + 1 < 2 ^ w by omega],
        by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
    have hs3 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 5)) s2 .normal s3 5 :=
      runs_store_iff.mpr ⟨updBuf + 2, e,
        by simp [s2, Expr.eval, BinOp.eval, hst2a_r 4 (by omega), hr4, hw2, show updBuf + 2 < 2 ^ w by omega],
        by simp [s2, Expr.eval, hst2a_r 5 (by omega), hr5], rfl, rfl, by simp [Expr.size]⟩
    have hs4 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 19) (.reg rC)))) s3 .normal s4 5 := by
      rw [runs_assign_iff]; refine ⟨ec.1, ?_, rfl, rfl, by simp [Expr.size]⟩
      have hlt_te : compEdgefulIdxBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compHdrSize]; have := c.2; omega
      have hlt_buf : compEdgefulIdxBase b x.vCap + c.1 < updBuf := by omega
      simp [s3, Expr.eval, BinOp.eval, hst2a_r 19 (by omega), hr19, hst2a_r rC hrC_lt, hrC,
        hefIdx_w, hm3_lt (compEdgefulIdxBase b x.vCap + c.1) hlt_buf, hst1_below_te _ hlt_te, hec_m]
    -- Build intermediate `CompLSFFamily` and `CompLSFMeta` for the `.delete e` dispatch
    let S_mid : CompLSFFamily k := fun j =>
      { (S j) with compSt := (Function.update (S j).compSt (x.compOf c)
          (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ua))) }
    let x_mid : CompLSFMeta k := { x with winConc := winConc1 }
    have hwin_mid : CompDispatchWinOk W k b S_mid x_mid ec m3 := by
      obtain ⟨_, _, hne, _, hK, hV, hH, hG, hW, hD⟩ := hwin
      refine ⟨hk, hLw, hne, hTE,
        (hm3_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffK] at hTE ⊢; omega)).trans
          ((hst1_below_te _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffK]; omega)).trans hK),
        (hm3_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffVCap] at hTE ⊢; omega)).trans
          ((hst1_below_te _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffVCap]; omega)).trans hV),
        (hm3_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffHandlesPtr] at hTE ⊢; omega)).trans
          ((hst1_below_te _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffHandlesPtr]; omega)).trans hH),
        fun j => by
          dsimp only [S_mid, x_mid]; rw [hec_comp, Function.update_self, Function.update_self]
          change ((S j).compSt (x.compOf c)).G.applyUpdate (.insert e ua ua) =
            ((S ⟨0, hk⟩).compSt (x.compOf c)).G.applyUpdate (.insert e ua ua)
          rw [← hec_comp, hG j],
        fun j => by
          obtain ⟨hslot, _, hv, he, hL, hge, hle⟩ := hW j
          obtain ⟨hss1, hrep1⟩ := (hwin1 ec j).1 hec_comp
          have hslot_lt : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) <
              compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
            have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
            have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
            dsimp only [compTablesEnd]; omega
          have hslot_buf : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < updBuf := by omega
          refine ⟨(hm3_lt (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) hslot_buf).trans
              ((hst1_below_te _ hslot_lt).trans hslot), ?_,
            hss1.1.trans hv, hss1.2.1.trans he, hss1.2.2.2.2.2.2.2.2.1.trans hL,
            hge, (hss1.endAddr (x.winHandle ec j)).symm ▸ hle⟩
          dsimp only [S_mid, x_mid]; rw [hec_comp, Function.update_self]
          exact (lsfRep_local W.h _ _ _ st1.mem m3 fun z hz =>
            (hm3_lt z (lt_of_lt_of_le (by simpa [LSFRep, hss1.endAddr] using hz.2) (le_trans hle (by omega)))).symm).1 hrep1,
        fun j₁ j₂ hne_j z h1 h2 => by
          have hss1 := ((hwin1 ec j₁).1 hec_comp).1
          have hss2 := ((hwin1 ec j₂).1 hec_comp).1
          exact hD j₁ j₂ hne_j z (by simpa [x_mid, LSFRep, hss1.endAddr] using h1)
            (by simpa [x_mid, LSFRep, hss2.endAddr] using h2)⟩
    let cnts1 : Fin k → ℕ := fun j => cnts j + (cuts j).length
    have hRF_del : ∀ j : Fin k,
        let Sj := (S j).compSt (x.compOf c)
        let Sj1 := applyLSFUpdate Sj (.insert e ua ua)
        let Sj2 := applyLSFBatch Sj [.insert e ua ua, .delete e]
        Sj2.R_orig = Sj1.R_orig ∧ Sj2.RF.F.E = Sj1.RF.F.E ∧ Sj2.RF.R = Sj1.RF.R := fun j => by
      have hCj : x.compOf c ∈ components (S j).G₀ := (hI_all j).2.1.symm ▸ hC_mem
      have hu_j : ((S j).compSt (x.compOf c)).G.UpdateIsValid (.insert e ua ua) :=
        (hI_all j).2.2.symm ▸ hu_valid
      exact applyLSFBatch_insert_delete_selfLoop_RF ((hI_all j).1.hCompLSF _ hCj).1 hu_j.1 hu_j.2.1
    have hcnts1_le : ∀ j : Fin k, cnts1 j ≤ x.vCap := fun j => by
      have hcard := List.toFinset_card_of_nodup ((hbr1 j).2.2.1 hpos).2.2.2.2.1
      rw [List.length_map, ((hbr1 j).2.2.1 hpos).2.2.2.2.2] at hcard
      have hsub : (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ua)).RF.R \
            ((S j).compSt (x.compOf c)).RF.R ⊆
          (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ua)).R_orig \
            ((S j).compSt (x.compOf c)).R_orig := fun z hz => by
        simp only [LSFState.RF, LSFState.R, applyLSFUpdate, Finset.mem_sdiff, Finset.mem_union] at hz ⊢
        exact ⟨hz.1.resolve_right (fun h => hz.2 (Or.inr h)), fun h => hz.2 (Or.inl h)⟩
      have := Finset.card_le_card hsub; have := hcap j; dsimp only [cnts1]; omega
    have hu_del_val : ((S_mid ⟨0, hwin_mid.1⟩).compSt (x_mid.compOf (x_mid.edgefulComp ec))).G.UpdateIsValid (.delete e) := by
      dsimp only [S_mid, x_mid]; rw [hec_comp, Function.update_self]
      exact Finset.mem_insert_self e _
    have hUpdAt_del : UpdateAt m3 (updBuf + 1)
        ((S_mid ⟨0, hwin_mid.1⟩).compSt (x_mid.compOf (x_mid.edgefulComp ec))).G (.delete e) 2 := by
      refine ⟨rfl, fun i hi => ?_⟩
      rcases i with _ | _ | i
      · simp [m3, m2, m1, Function.update_of_ne (show updBuf + 1 ≠ updBuf + 2 by omega)]
      · simp [m3]
      · simp at hi
    obtain ⟨stD, cD, winConc_ec2, cuts_del, hrunD, hbrD, hfrD, hzD, hcostD⟩ :=
      compDispatchOne_runs (p := p) (S := S_mid) (x := x_mid) (cnts := cnts1) (mem := m3)
        (pos := s4.pos) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hw16 ec hwin_mid
        hend_le hcnt_buf (by omega) (fun z hz' => (hm3_ge z (by omega)).trans (hz1 z (by omega)))
        (fun j => (hm3_lt _ (by have := j.2; omega)).trans (hbr1 j).1)
        (fun j => by
          dsimp only [S_mid, x_mid]; rw [hec_comp, Function.update_self]
          change cnts1 j + ((applyLSFBatch ((S j).compSt (x.compOf c)) [.insert e ua ua, .delete e]).R_orig \
            (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ua)).R_orig).card ≤ x.vCap
          rw [(hRF_del j).1, Finset.sdiff_self, Finset.card_empty, Nat.add_zero]
          exact hcnts1_le j)
        (by simp [m3, m2, m1, Function.update_of_ne (show updBuf ≠ updBuf + 2 by omega),
          Function.update_of_ne (show updBuf ≠ updBuf + 1 by omega)])
        (fun i hi => by
          rcases i with _ | _ | _ | i
          · simp [m3, m2, m1, Function.update_of_ne (show updBuf ≠ updBuf + 2 by omega),
              Function.update_of_ne (show updBuf ≠ updBuf + 1 by omega)]; omega
          · simp [m3, m2, m1, Function.update_of_ne (show updBuf + 1 ≠ updBuf + 2 by omega)]; omega
          · simp [m3]; exact he_w
          · omega)
        hUpdAt_del hu_del_val trivial trivial
    have hcuts_del_nil : ∀ j : Fin k, cuts_del j = [] := fun j => by
      have hset := (hbrD j).2.2.2.2.2.2.2.2.2
      dsimp only [S_mid, x_mid] at hset; rw [hec_comp, Function.update_self] at hset
      change ((cuts_del j).map Prod.snd).toFinset =
        (applyLSFBatch ((S j).compSt (x.compOf c)) [.insert e ua ua, .delete e]).RF.R \
          (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ua)).RF.R at hset
      rw [(hRF_del j).2.2, Finset.sdiff_self] at hset
      cases hcd : cuts_del j with
      | nil => rfl
      | cons p ps =>
        rw [hcd] at hset
        have : p.2 ∈ (∅ : Finset ℕ) := hset ▸ List.mem_toFinset.mpr (List.mem_cons_self)
        simp at this
    let s5 : State := { s4 with regs := Function.update s4.regs 20 0, mem := stD.mem, pos := stD.pos }
    have hs5 : Runs w p ω (.call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 3, .reg 3]) s4 .normal s5 (cD + 6) := by
      rw [runs_call_iff]
      refine ⟨[b, ec.1, updBuf, 3, cntBase], _, .returned 0, stD, cD, ?_, hpDisp, hrunD, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
      simp [evalArgs, Expr.eval, s4, s3, hst2a_r 0 (by omega), hr0, hst2a_r 4 (by omega), hr4,
        hst2a_r 3 (by omega), hr3, hw3]
    have hthen2 : Runs w p ω _ st2a .normal s5 (cD + 28) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, hs1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hs3,
            runs_seq_iff.mpr (Or.inr ⟨s4, 5, cD + 6, hs4, hs5, rfl⟩), rfl⟩), rfl⟩), by omega⟩)
    have hcond2 : Runs w p ω (.cond (.reg 23) _ .nop) st2a .normal s5 (cD + 30) :=
      runs_cond_iff.mpr ⟨1, cD + 28, by simp [st2a, Expr.eval, hisEf], by simpa using hthen2, by simp [Expr.size]; omega⟩
    have hrun2 : Runs w p ω (compStepInsDelOnlyDispStmt bDisp rC) st1 .normal s5 (cD + 36) :=
      runs_seq_iff.mpr (Or.inr ⟨st2a, 5, cD + 30, hrun2a, hcond2, by omega⟩)
    have hrun_pair : Runs w p ω _ st .normal s5 (c1 + cD + 37) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, cD + 36, hrun1, hrun2, by omega⟩)
    let winConc' : Fin x.numEdgeful → Fin k → LSFConcrete := fun ec' j =>
      if ec' = ec then winConc_ec2 j else x.winConc ec' j
    have hfoot_mid : ∀ j a, (LSFRep W.h).foot (x.winHandle ec j) (winConc1 ec j) a ↔
        (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a := fun j a => by
      simp [LSFRep, ((hwin1 ec j).1 hec_comp).1.endAddr]
    have hD_lt_buf : ∀ a, (∀ j : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) → a < updBuf → stD.mem a = st1.mem a := fun a hnw hnc hlt =>
      (hfrD a (fun j ha => hnw j ((hfoot_mid j a).mp ha)) hnc
        (fun j => by rw [hcuts_del_nil j]; simp; omega)
        (fun j => by rw [hcuts_del_nil j]; simp; omega)
        (Or.inl hlt)).trans (hm3_lt a hlt)
    have hphi_m3 : (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) m3) =
        ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) st1.mem :=
      Finset.sum_congr rfl fun j _ => lsfPhi_congr fun z _ hz2 => by
        have hss1 := ((hwin1 ec j).1 hec_comp).1
        have hle := (hwin.2.2.2.2.2.2.2.2.1 j).2.2.2.2.2.2
        exact hm3_lt z (lt_of_lt_of_le (hss1.endAddr _ ▸ hz2) (le_trans hle (by omega)))
    refine ⟨s5, c1 + cD + 37, cuts, winConc', hrun_pair,
      fun r hr => by simp [s5, s4, s3, show r ≠ 20 by omega, show r ≠ 24 by omega, hst2a_r r hr],
      fun j => by
        have hcd := hcuts_del_nil j
        have hcnt_j : s5.mem (cntBase + j.1) = cnts j + (cuts j).length := by
          have := (hbrD j).2.2.1; dsimp only [cnts1] at this; rw [hcd] at this; simpa [s5] using this
        have hbuf_j : ∀ i (hi : i < (cuts j).length),
            s5.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
            s5.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1 := fun i hi => by
          have h1 := (hbr1 j).2.1 i hi
          have hle_j : cnts j + i < x.vCap := by have := hcnts1_le j; dsimp only [cnts1] at this; omega
          have hjk : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at hjk
          have hr_lt : rootsBase + j.1 * x.vCap + (cnts j + i) < updBuf := by omega
          have hf_lt : fDelBase + j.1 * x.vCap + (cnts j + i) < updBuf := by omega
          have hnw_r : ∀ j0 : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec j0) (x.winConc ec j0)
              (rootsBase + j.1 * x.vCap + (cnts j + i)) := fun j0 ha =>
            absurd ha.2 (not_lt.mpr (le_trans (hwin.2.2.2.2.2.2.2.2.1 j0).2.2.2.2.2.2 (by omega)))
          have hnw_f : ∀ j0 : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec j0) (x.winConc ec j0)
              (fDelBase + j.1 * x.vCap + (cnts j + i)) := fun j0 ha =>
            absurd ha.2 (not_lt.mpr (le_trans (hwin.2.2.2.2.2.2.2.2.1 j0).2.2.2.2.2.2 (by omega)))
          exact ⟨(hD_lt_buf _ hnw_r (fun j0 => by have := j0.2; omega) hr_lt).trans h1.1,
            (hD_lt_buf _ hnw_f (fun j0 => by have := j0.2; omega) hf_lt).trans h1.2⟩
        exact ⟨hcnt_j, hbuf_j, (hbr1 j).2.2.1, (hbr1 j).2.2.2⟩,
      fun ec0 j => ⟨fun hcomp0 => by
        have heq0 : ec0 = ec := hefComp_inj ec0 ec (hcomp0.trans hec_comp.symm)
        subst ec0; simp only [winConc', ↓reduceIte]
        have hss1 := ((hwin1 ec j).1 hec_comp).1
        have hss2 := (hbrD j).1
        have hrep2 := (hbrD j).2.1
        dsimp only [S_mid, x_mid] at hss2 hrep2; rw [hec_comp, Function.update_self] at hrep2
        exact ⟨hss1.trans hss2, hrep2⟩,
        fun hne0 => by simp [winConc', show ec0 ≠ ec from fun h => hne0 (h ▸ hec_comp)]⟩,
      fun a hnw hnc hnrt hnfd hlt_buf =>
        (hD_lt_buf a (fun j => hnw ec j hec_comp) hnc hlt_buf).trans (hfr1 a hnw hnc hnrt hnfd hlt_buf),
      hzD, ?_⟩
    rw [dite_eq_left hpos]
    refine ⟨ec, hec_comp, ?_⟩
    have hphi_new : (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) s5.mem) =
        ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc_ec2 j) stD.mem :=
      Finset.sum_congr rfl fun j _ => by simp [winConc', s5]
    rw [hphi_new]; rw [hphi_m3] at hcostD
    have hcd0 : ∑ j : Fin k, (cuts_del j).length = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcuts_del_nil j]; rfl
    rw [hcd0] at hcostD
    have hmul : k * (lsfBatchCostFactor * (5 * x.L_w + 1) + 850) +
        k * (lsfBatchCostFactor * ((1 + 2) * x.L_w + 1) + 850) =
        k * (lsfBatchCostFactor * (8 * x.L_w + 2) + 1700) := by ring
    linarith
  · have hisEf : isEf = 0 := ite_eq_right hpos
    rw [dite_eq_right hpos] at hcost1
    have hcond2 : Runs w p ω (.cond (.reg 23)
        (.store (.reg 4) (.const 1) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
         .store (.bin .add (.reg 4) (.const 2)) (.reg 5) ;;
         .assign 24 (.load (.bin .add (.reg 19) (.reg rC))) ;;
         .call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 3, .reg 3]) .nop) st2a .normal st2a 3 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [st2a, Expr.eval, hisEf], by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
    have hrun2 : Runs w p ω (compStepInsDelOnlyDispStmt bDisp rC) st1 .normal st2a 9 :=
      runs_seq_iff.mpr (Or.inr ⟨st2a, 5, 3, hrun2a, hcond2, rfl⟩)
    have hrun_pair : Runs w p ω _ st .normal st2a (c1 + 10) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, 9, hrun1, hrun2, by omega⟩)
    refine ⟨st2a, c1 + 10, cuts, winConc1, hrun_pair,
      fun r hr => by simp [st2a, show r ≠ 23 by omega, hregs1 r hr],
      fun j => by simpa [st2a] using hbr1 j,
      fun ec j => ⟨fun heq => absurd (heq ▸ hef_pos ec) hpos, (hwin1 ec j).2⟩,
      fun a _ _ _ _ _ => hcost1.2 a,
      hz1, ?_⟩
    rw [dite_eq_right hpos]
    exact ⟨by omega, fun a => hcost1.2 a⟩

end

end MinCostFlow.SparseCore.Program
