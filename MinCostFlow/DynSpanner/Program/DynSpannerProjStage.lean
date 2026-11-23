module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkPtrs
public import MinCostFlow.DynSpanner.Program.DynSpannerBuildProj
import WordRAM.Tactic

/-!
# The projection stage of a step

In a step with `0 < j`, once the affected edges `E_aff` are known, Algorithm 6 (lines 70–77)
builds the graph `J` on the projected ends and the embedding `Π_{J → H_{<j} ∪ E_aff}`. The
procedure `dsProjStageStmt` does this in the state at `b`:

1. it computes the bases of the state (`dsFilterPrefixStmt`);
2. it writes the walk pointers of the affected edges at `heap` (`dsWalkPtrsStmt`);
3. it builds `J` in the scratch graph `aux` of the state, with the walk pointers of `J` in the
   table `MEmbTemp` and the walks in the heap after the pointer list (`dsBuildProjStmt`).

The input is described by `FilterCtx` with the list of affected edges as `cand` and the heap
start as `outArrPtr`, plus the facts of `ProjStageHyp`. `dsProjStage_meetsContract` proves the
contract. Most of the proof checks that the areas of the two calls are disjoint: the graphs,
`sBit` and `MEmbTemp` lie in the fixed area of the state, and the walks, the list of edges and the
heap lie after it.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The projection stage (`args = [b, j, esPtr, esLen, heap]`); returns the final heap pointer. -/
def dsProjStageStmt (bW bB : ℕ) : Stmt :=
  dsFilterPrefixStmt ;;
  .call 14 (bW + walkPtrsIdx) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .assign 15 (.bin .add (.reg 13) (.bin .mul (.const 2) (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))))) ;;
  .assign 16 (.bin .add (.reg 11) (.bin .add (.bin .mul (.const 2) (.reg 5))
    (.bin .mul (.const 2) (.reg 6)))) ;;
  .call 17 (bB + buildProjIdx)
    [.reg 13, .reg 15, .reg 11, .reg 2, .reg 3, .reg 4, .reg 16, .bin .add (.reg 4) (.reg 3)] ;;
  .ret (.reg 17)

def projStageProcs (bW bB : ℕ) : List Stmt := [dsProjStageStmt bW bB]

def projStageIdx : ℕ := 0

lemma projStageProcs_noRand (bW bB : ℕ) : ∀ s ∈ projStageProcs bW bB, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Facts beyond `FilterCtx` that the projection stage needs. The heap area starts at
`outArrPtr`: first the `|E_aff|` walk pointers, then `projHeapNeed` words for `dsBuildProjStmt`. -/
structure ProjStageHyp (c : FilterCtx) : Prop where
  aux0 : DynGraphAt c.mem0 (dsAuxPtr c.b c.vCap c.eCap) c.vCap c.eCap emptyMGraph
  hB : c.outArrPtr + c.candLen + projHeapNeed c.piLt_mid c.cand < 2 ^ c.w
  foot_fix : ∀ a, c.footPi a → c.b + dsFixedSize c.L c.vCap c.eCap ≤ a
  foot_heap : ∀ a, c.footPi a → a < c.outArrPtr ∨
    c.outArrPtr + c.candLen + projHeapNeed c.piLt_mid c.cand ≤ a
  cand_fix : c.b + dsFixedSize c.L c.vCap c.eCap ≤ c.candPtr
  cand_heap : IvlDisj c.outArrPtr (c.candLen + projHeapNeed c.piLt_mid c.cand) c.candPtr c.candLen
  walks : ∀ e ∈ c.cand, PrefixWalksValid c.G' c.S_prev c.eCap (c.G'.tail e) (c.G'.head e) (c.piLt_mid e)

/-- Contract of `dsProjStageStmt`. -/
def dsProjStageContract (c : FilterCtx) : Contract where
  pre args mem :=
    args = [c.b, c.j, c.candPtr, c.candLen, c.outArrPtr] ∧ mem = c.mem0 ∧ ProjStageHyp c
  post _ mem ret mem' :=
    DynGraphAt mem' (dsAuxPtr c.b c.vCap c.eCap) c.vCap c.eCap
      (buildProjGraph c.G' c.G' c.piLt_mid c.S_prev c.cand.toFinset) ∧
    (∀ k (hk : k < c.cand.length), mem' (c.outArrPtr + k) = c.walkPtr c.cand[k]) ∧
    (∀ e ∈ c.cand, c.outArrPtr + c.candLen ≤ mem' (dsMEmbTempBase c.b c.L c.vCap c.eCap + e) ∧
      mem' (dsMEmbTempBase c.b c.L c.vCap c.eCap + e) +
        (2 * (projWalk c.G' c.G' c.piLt_mid c.S_prev e).length + 1) ≤ ret ∧
      MWalkAt mem' (mem' (dsMEmbTempBase c.b c.L c.vCap c.eCap + e))
        (projWalk c.G' c.G' c.piLt_mid c.S_prev e)) ∧
    ret = projHeapAt c.G' c.piLt_mid c.S_prev c.cand (c.outArrPtr + c.candLen) c.cand.length ∧
    ∀ addr, (addr < c.outArrPtr ∨
        c.outArrPtr + c.candLen + projHeapNeed c.piLt_mid c.cand ≤ addr) →
      (addr < dsAuxPtr c.b c.vCap c.eCap ∨
        dsAuxPtr c.b c.vCap c.eCap + dynGraphSize c.vCap c.eCap ≤ addr) →
      (∀ e ∈ c.cand, addr ≠ dsMEmbTempBase c.b c.L c.vCap c.eCap + e) → mem' addr = mem addr
  cost _ _ := c.cand.length * (35 * c.j + 60) + buildProjCost c.piLt_mid c.cand + 400

end

/-- An interval whose every address satisfies `P` is disjoint from an area that avoids `P`. -/
private lemma ivlDisj_of_foot {P : ℕ → Prop} {lo len x lx : ℕ} (hlen : 0 < len) (hlx : 0 < lx)
    (hfoot : ∀ a, x ≤ a → a < x + lx → P a) (hout : ∀ a, P a → a < lo ∨ lo + len ≤ a) :
    IvlDisj lo len x lx := by
  unfold IvlDisj
  by_contra h
  have h1 : x < lo + len := by omega
  have h2 : lo < x + lx := by omega
  have := hout (max x lo) (hfoot _ (le_max_left _ _) (by omega))
  omega

/-- Positions of the areas of the fixed block used by the stage. -/
private lemma stage_layout (b L vCap eCap : ℕ) :
    dsAuxPtr b vCap eCap = dsGPtr b + 2 * (4 + (7 * vCap + 9 * eCap)) ∧
    dsGPtr b + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsSBitBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap = dsSBitBase b L vCap eCap + (2 * vCap + 2 * eCap) ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap ∧
    b ≤ dsGPtr b := by
  have hfa := dsFixedSize_add b L vCap eCap
  refine ⟨?_, ?_, ?_, ?_, hfa, dsGPtr_ge b⟩ <;>
  simp only [dsAuxPtr, dsHPtr, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase,
    dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase,
    dsHPrevBase, dsHNextBase, dsMinHBase, dsMEmbTempBase, dsKeptStampBase, dsEStampBase,
    dsVStampBase, dynGraphSize] <;> omega

public section

/-- `dsProjStageStmt` meets `dsProjStageContract`. -/
theorem dsProjStage_meetsContract (c : FilterCtx) {p : Program}
    {bS bW bB bOps bEdge bProj bEmb : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpProj : p.HasAt bProj (projProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpB : p.HasAt bB (buildProjProcs bOps bEdge bProj)) (hpW : p.HasAt bW walkPtrsProcs)
    (hpS : p.HasAt bS (projStageProcs bW bB)) :
    MeetsContract c.w p (bS + projStageIdx) (dsProjStageContract c) := by
  refine meetsContract_of_runs
    (hpS.get (i := projStageIdx) (by simp [projStageProcs, projStageIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem, hyp⟩
  subst hmem
  have hlay := c.lay
  have hw16 := c.hw16
  have hlen := c.hcand_len
  obtain ⟨hA0, hR, hR1, hT0, hT1, hgb⟩ := stage_layout c.b c.L c.vCap c.eCap
  have hfix_w := c.hfix_w
  have hfix_out := c.hfix_out
  have hcand_w := c.hcand_w
  have hhB := hyp.hB
  have hcf := hyp.cand_fix
  have hdgs := hlay.dgs_eq
  have hsbf := hlay.sb_le_fix
  have hj_w : c.j < 2 ^ c.w := by have := hlay.L1_w; have := c.hjL; omega
  simp only [projStageProcs, projStageIdx, List.getElem_cons_zero]
  dsimp only [dsProjStageStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le (dsFilterAffected_bases_triple c) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro st1 ⟨hm1, hf1, _⟩
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13⟩ := hf1
  -- Walk pointers.
  refine runs_seq_call_le (dsWalkPtrs_meetsContract c hpW) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨rfl, hm1⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨hwp, hfr₁⟩
  rw [hm1] at hfr₁
  -- Bases of `aux` and `MEmbTemp`.
  have haux_w : dsAuxPtr c.b c.vCap c.eCap < 2 ^ c.w := by omega
  have hT_w : dsMEmbTempBase c.b c.L c.vCap c.eCap < 2 ^ c.w := by omega
  refine runs_seq_assign_le (v := dsAuxPtr c.b c.vCap c.eCap) (by
    rw [hA0]
    exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r13]))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r5]))
              (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r6]))
              (by omega)) (by omega))
          (by omega)) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := dsMEmbTempBase c.b c.L c.vCap c.eCap) (by
    rw [hT0]
    exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r11]))
      (Expr.eval_add
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r5]))
          (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r6]))
          (by omega)) (by omega)) (by omega)) ?_
  -- Build `J` and its embedding.
  have hnB := hyp.hB
  have hch := hyp.cand_heap
  unfold IvlDisj at hch
  have hT_cand : ∀ e ∈ c.cand, e < c.eCap := fun e he => (c.hcand_sub e he).2
  have hwalk : ∀ k (hk : k < c.cand.length),
      MWalkAt mem₁ (mem₁ (c.outArrPtr + k)) (c.piLt_mid c.cand[k]) ∧
      mem₁ (c.outArrPtr + k) + (2 * (c.piLt_mid c.cand[k]).length + 1) < 2 ^ c.w ∧
      IvlDisj (c.outArrPtr + c.candLen) (projHeapNeed c.piLt_mid c.cand) (mem₁ (c.outArrPtr + k))
        (2 * (c.piLt_mid c.cand[k]).length + 1) ∧
      IvlDisj (dsAuxPtr c.b c.vCap c.eCap) (dynGraphSize c.vCap c.eCap) (mem₁ (c.outArrPtr + k))
        (2 * (c.piLt_mid c.cand[k]).length + 1) ∧
      IvlDisj (dsMEmbTempBase c.b c.L c.vCap c.eCap) c.eCap (mem₁ (c.outArrPtr + k))
        (2 * (c.piLt_mid c.cand[k]).length + 1) := by
    intro k hk
    obtain ⟨hp, hW, hfoot, hbd⟩ := hwp k hk
    rw [mWalkEncode_length] at hfoot hbd
    rw [hp]
    have hneed : 0 < projHeapNeed c.piLt_mid c.cand := by
      obtain ⟨x, xs, hx⟩ : ∃ x xs, c.cand = x :: xs := by
        cases h : c.cand with
        | nil => simp [h] at hk
        | cons x xs => exact ⟨x, xs, rfl⟩
      simp [projHeapNeed, hx]
    have hp0 := hyp.foot_fix _ (hfoot _ (Nat.le_refl _) (by omega))
    refine ⟨hW, by omega, ?_, Or.inl (by omega), Or.inl (by omega)⟩
    have := ivlDisj_of_foot (lo := c.outArrPtr) (len := c.candLen + projHeapNeed c.piLt_mid c.cand)
      (x := c.walkPtr c.cand[k]) (lx := 1 + 2 * (c.piLt_mid c.cand[k]).length) (by omega) (by omega) hfoot (fun a ha => by have := hyp.foot_heap a ha; omega)
    have h2 := IvlDisj.sub_left (x' := c.outArrPtr + c.candLen)
      (lx' := projHeapNeed c.piLt_mid c.cand) this (by omega) (by omega)
    unfold IvlDisj at h2 ⊢
    omega
  have hG₁ : DynGraphAt mem₁ (dsGPtr c.b) c.vCap c.eCap c.G' :=
    dynGraphAt_of_agree c.hDG fun addr h1 h2 => hfr₁ addr (Or.inl (by omega))
  have hJ₁ : DynGraphAt mem₁ (dsAuxPtr c.b c.vCap c.eCap) c.vCap c.eCap emptyMGraph :=
    dynGraphAt_of_agree hyp.aux0 fun addr h1 h2 => hfr₁ addr (Or.inl (by omega))
  have hes₁ : ListAt mem₁ c.candPtr c.cand :=
    c.hm_cand.congr fun k h1 h2 => hfr₁ k (by rw [hlen] at h2; omega)
  have hS₁ : ∀ v < c.vCap, mem₁ (dsSBitBase c.b c.L c.vCap c.eCap + v) =
      if v ∈ c.S_prev then 1 else 0 := fun v hv =>
    (hfr₁ _ (Or.inl (by omega))).trans (c.hsBit v hv)
  refine runs_seq_call_le (dsBuildProj_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) (G := c.G') (embLt := c.piLt_mid) (S := c.S_prev) (es := c.cand)
      hpOps hpEdge hpProj hpEmb hpB) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨dsGPtr c.b, dsAuxPtr c.b c.vCap c.eCap, dsSBitBase c.b c.L c.vCap c.eCap, c.candPtr,
      c.outArrPtr, dsMEmbTempBase c.b c.L c.vCap c.eCap, c.outArrPtr + c.candLen,
      by simp only [hlen, hA0, hT0], hw16, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), by unfold IvlDisj; omega,
      Or.inr (by omega), Or.inr (by omega),
      Or.inr (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inl (by omega), Or.inl (by omega),
      hwalk, hG₁, c.hG_val, c.hGV_cap, c.hGE_cap, hJ₁, hes₁, c.hcand_nd,
      fun e he => (c.hcand_sub e he).1, hyp.walks, hS₁⟩ ?_
  rintro r₁₇ mem₂ pos₂ ⟨_, _, _, _, _, _, _, hargs₂, hJ₂, hT₂, hret₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl, rfl, -, rfl, rfl, rfl⟩ := hargs₂
  simp only [← hA0, ← hT0] at hJ₂ hT₂ hfr₂
  refine runs_ret_le (v := r₁₇) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨hJ₂, fun k hk => ?_, hT₂, hret₂, fun addr hH hA hT => ?_⟩
    · show mem₂ _ = _
      rw [hfr₂ _ (Or.inl (by omega)) (Or.inr (by omega))
        (fun e he => by have := hT_cand e he; omega)]
      exact (hwp k hk).1
    · show mem₂ addr = _
      rw [hfr₂ addr (by omega) hA hT]
      exact hfr₁ addr (by omega)
  · simp only [dsWalkPtrsContract, dsBuildProjContract, dsProjStageContract,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
