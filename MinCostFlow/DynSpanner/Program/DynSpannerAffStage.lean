module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffStageDefs
import WordRAM.Tactic

/-!
# The affected stage: candidates, affected edges, then the projection

`dsAffStageStmt` (Algorithm 6, lines 70–77) makes three calls:
1. `dsCollectCandStmt` writes the list of candidate edges after the list of `S_{j-1}` in the heap
   and marks `S_{j-1}` in `sBit`;
2. `dsFilterAffectedStmt` writes the affected candidates right after the candidates;
3. `dsProjStageStmt` builds `J` and its embedding from the affected list, with its heap right
   after this list.
The last two calls read only words that the first call keeps (`AffMid.agree`), so their contexts
are given by `AffCtx.toFilter` (`dsAffStage_meetsContract`). The cost is stated with the model
sets `AffCtx.candSet` and `AffCtx.affSet`, which the lists enumerate without repeats.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- `args = [b, j, heapPtr]`; returns the number of affected edges. -/
def dsAffStageStmt (bAff bS : ℕ) : Stmt :=
  .call 3 (bAff + affIdxCollectCand) [.reg 0, .reg 1, .reg 2] ;;
  .assign 4 (.bin .add (.bin .add (.reg 2) (.const 2)) (.load (.reg 2))) ;;
  .assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .call 6 (bAff + affIdxFilterAffected) [.reg 0, .reg 1, .reg 4, .reg 5, .reg 3] ;;
  .call 7 (bS + projStageIdx) [.reg 0, .reg 1, .reg 3, .reg 6, .bin .add (.reg 3) (.reg 6)] ;;
  .ret (.reg 6)

def affStageProcs (bAff bS : ℕ) : List Stmt := [dsAffStageStmt bAff bS]

def affStageIdx : ℕ := 0

lemma affStageProcs_noRand (bAff bS : ℕ) : ∀ s ∈ affStageProcs bAff bS, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsAffStageStmt`. The post names the list `cand` of candidates, the list `eAff`
of affected edges, the memories `mem₁` and `mem₂` after the first two calls, and the pointer
`retP` that the projection returns. The stage returns `|eAff|`. After the first call the heap
starts with `[|S_{j-1}|, |cand|]` and the list of `S_{j-1}`. -/
noncomputable def dsAffStageContract (a : AffCtx) : Contract where
  pre args mem :=
    args = [a.b, a.j, a.heapPtr] ∧ mem = a.mem0 ∧
    a.heapPtr + 2 + a.vCap + 3 * a.eCap + a.heapNeed < 2 ^ a.w
  post _ mem ret mem' := ∃ cand eAff mem₁ mem₂ retP, ∃ _ : AffMid a a.candPtr cand mem₁,
    ∃ h₂ : AffMid a (a.candPtr + cand.length) eAff mem₂,
    (∀ e, e ∈ cand ↔ e ∈ a.candSet) ∧ (∀ e, e ∈ eAff ↔ e ∈ a.affSet) ∧
    (dsProjStageContract (a.toFilter (a.candPtr + cand.length) eAff mem₂ h₂)).post [] mem₂ retP
      mem' ∧
    ret = eAff.length ∧
    mem₁ a.heapPtr = a.sPrevList.length ∧ mem₁ (a.heapPtr + 1) = cand.length ∧
    ListAt mem₁ (a.heapPtr + 2) a.sPrevList ∧
    mem₁ (a.b + dsGenOff) = mem (a.b + dsGenOff) + 1 ∧
    (∀ e < a.eCap, mem₁ (dsEStampBase a.b a.L a.vCap a.eCap + e) ≤ mem (a.b + dsGenOff) + 1) ∧
    (∀ addr, dsCollectCandFrameCond a.L a.vCap a.eCap a.b a.heapPtr (a.candPtr + cand.length)
      addr → mem₁ addr = mem addr) ∧
    ∀ addr, (addr < a.candPtr + cand.length ∨ a.candPtr + cand.length + cand.length ≤ addr) →
      mem₂ addr = mem₁ addr
  cost _ _ :=
    100 * candRevSum a.L a.j a.revLists a.sPrevList + 100 * (a.j * a.sPrevList.length) +
      100 * a.sPrevList.length + 100 * a.j +
      100 * (∑ e ∈ a.candSet, (a.piLt_mid e).length) + 40 * (a.candSet.card * a.j) +
      160 * a.candSet.card +
      a.affSet.card * (35 * a.j + 60) +
      (∑ e ∈ a.affSet, (800 * (a.piLt_mid e).length + 2000)) + 1200

end

public section

/-- A list without repeats whose elements are those of a set sums like the set. -/
lemma list_sum_eq_finset_sum {l : List ℕ} {S : Finset ℕ} (hnd : l.Nodup)
    (hiff : ∀ e, e ∈ l ↔ e ∈ S) (f : ℕ → ℕ) : (l.map f).sum = ∑ e ∈ S, f e := by
  have hS : l.toFinset = S := by
    ext e; simp [hiff]
  rw [← hS, List.sum_toFinset f hnd]

lemma list_length_eq_card {l : List ℕ} {S : Finset ℕ} (hnd : l.Nodup)
    (hiff : ∀ e, e ∈ l ↔ e ∈ S) : l.length = S.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e; simp [hiff]

/-- The projection stage on an affected list at `ptr` has the facts of `ProjStageHyp`. -/
lemma projStageHyp_of_mid (a : AffCtx) {ptr : ℕ} {l : List ℕ} {mem : ℕ → ℕ}
    (h : AffMid a ptr l mem) : ProjStageHyp (a.toFilter ptr l mem h) := by
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10⟩ :=
    sBit_ge_layout a.b a.L a.vCap a.eCap
  have hfixH := a.hfixH
  have hp := h.hp
  exact
    { aux0 := show DynGraphAt mem (dsAuxPtr a.b a.vCap a.eCap) a.vCap a.eCap emptyMGraph from
        dynGraphAt_of_agree a.aux0 fun addr h1 h2 =>
          h.agree addr (Or.inl ⟨by omega, by omega⟩)
      hB := h.hB
      foot_fix := fun x hx => (a.hfootPi x hx).1
      foot_heap := fun x hx => by
        have := (a.hfootPi x hx).2
        left; show x < ptr + l.length
        omega
      cand_fix := by
        show a.b + dsFixedSize a.L a.vCap a.eCap ≤ ptr
        omega
      cand_heap := Or.inr (le_refl _)
      walks := fun e he => a.walks e (h.sub e he) }

/-- `dsAffStageStmt` meets `dsAffStageContract`. -/
theorem dsAffStage_meetsContract (a : AffCtx) {p : Program}
    {bAff bOps bS bW bB bEdge bProj bEmb bA : ℕ}
    (hpAff : p.HasAt bAff (affectedProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpProj : p.HasAt bProj (projProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpB : p.HasAt bB (buildProjProcs bOps bEdge bProj)) (hpW : p.HasAt bW walkPtrsProcs)
    (hpS : p.HasAt bS (projStageProcs bW bB))
    (hpA : p.HasAt bA (affStageProcs bAff bS)) :
    MeetsContract a.w p (bA + affStageIdx) (dsAffStageContract a) := by
  refine meetsContract_of_runs
    (hpA.get (i := affStageIdx) (by simp [affStageProcs, affStageIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, hmem, hheap⟩
  subst hmem
  simp only [affStageProcs, affStageIdx, List.getElem_cons_zero]
  dsimp only [dsAffStageStmt]
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10⟩ :=
    sBit_ge_layout a.b a.L a.vCap a.eCap
  have hES : dsEStampBase a.b a.L a.vCap a.eCap + a.eCap ≤ a.b + dsFixedSize a.L a.vCap a.eCap := by
    rw [← dsFixedSize_add]
    simp only [dsMEmbTempBase, dsKeptStampBase]
    omega
  have hSE : dsSBitBase a.b a.L a.vCap a.eCap ≤ dsEStampBase a.b a.L a.vCap a.eCap := by
    simp only [dsEStampBase, dsVStampBase]; omega
  have hfixH := a.hfixH
  have hw16 := a.hw16
  have hsl : a.sPrevList.length ≤ a.vCap :=
    list_length_le_of_nodup_lt a.hs_nd fun v hv => a.hS_cap v ((a.hs_iff v).mp hv)
  refine runs_start_le ?_
  -- Call 1: the candidates.
  refine runs_seq_call_le (vs := [a.b, a.j, a.heapPtr])
    (dsCollectCand_meetsContract a.w a.L a.vCap a.eCap a.b a.j a.G' a.S_prev a.sPrevList
      a.revLists a.footS a.footRev hpAff)
    (by eval_expr) hW
    ⟨a.heapPtr, rfl, a.hw16, a.h1j, a.hjL, a.hfixH, by omega, a.hmL, a.hmV, a.hmE, a.hgen1,
      a.hgenB, a.hDG, a.hG_val, a.hGE_cap, a.hfootS, a.hfootRev, a.hS_cap, a.hs_nd, a.hs_iff,
      a.hsg0, a.hsgle, a.hsll, a.hsbit0, a.hestamp, a.hdomle, a.hrev⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨heapPtr', cand, hargs₁, hnd, hr₁, hr₁le, hm0, hm1, hsL, hcL, hsBit,
    hiff, hlt, hgen, hest, hfr⟩
  simp only [List.cons.injEq, and_true, true_and] at hargs₁
  subst hargs₁
  have hcl : cand.length ≤ a.eCap := list_length_le_of_nodup_lt hnd hlt
  have hiffC : ∀ e, e ∈ cand ↔ e ∈ a.candSet := fun e => by simp [AffCtx.candSet, hiff]
  have hneedC : projHeapNeed a.piLt_mid cand = a.heapNeed :=
    list_sum_eq_finset_sum hnd hiffC _
  have hagree₁ : ∀ addr, ((addr < dsSBitBase a.b a.L a.vCap a.eCap ∧ addr ≠ a.b + dsGenOff) ∨
      (a.b + dsFixedSize a.L a.vCap a.eCap ≤ addr ∧ addr < a.heapPtr)) →
      mem₁ addr = a.mem0 addr := fun addr h => by
    refine hfr addr ⟨?_, fun v hv => ?_, fun e he => ?_, ?_⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · omega
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · left; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hmid₁ : AffMid a a.candPtr cand mem₁ :=
    { nd := hnd, sub := fun e he => ((hiff e).mp he).1, lt := hlt, at_ := hcL, sBit := hsBit
      agree := hagree₁
      hp := by simp only [AffCtx.candPtr]; omega
      hB := by rw [hneedC]; simp only [AffCtx.candPtr]; omega }
  -- The two words that locate the list of candidates.
  refine runs_seq_assign_le (v := a.candPtr)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hm0) (by omega)) ?_
  refine runs_seq_assign_le (v := cand.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hm1) ?_
  have hr₁' : r₁ = a.candPtr + cand.length := by simp only [AffCtx.candPtr]; omega
  -- Call 2: the affected edges.
  refine runs_seq_call_le (vs := [a.b, a.j, a.candPtr, cand.length, a.candPtr + cand.length])
    (dsFilterAffected_meetsContract (a.toFilter a.candPtr cand mem₁ hmid₁) hpOps hpAff)
    (by
      simp only [evalArgs, Expr.eval]
      simp [hr₁', startState])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl|rfl|rfl)
      · exact hW _ (by simp)
      · exact hW _ (by simp)
      · simp only [AffCtx.candPtr]; omega
      · omega
      · simp only [AffCtx.candPtr]; omega)
    ⟨rfl, rfl⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hv₂, hnd₂, hat₂, hfr₂, hle₂, hiff₂⟩
  dsimp only [AffCtx.toFilter] at hv₂ hnd₂ hat₂ hfr₂ hle₂ hiff₂
  obtain ⟨eAff, hv₂, hnd₂, hat₂, hle₂, hiff₂⟩ : ∃ l : List ℕ, r₂ = l.length ∧ l.Nodup ∧
      ListAt mem₂ (a.candPtr + cand.length) l ∧ l.length ≤ cand.length ∧
      ∀ e, e ∈ l ↔ e ∈ cand ∧ e ∈ affectedEdges a.G' a.H_lt a.piLt_mid a.S_prev :=
    ⟨_, hv₂, hnd₂, hat₂, hle₂, hiff₂⟩
  have hiffA : ∀ e, e ∈ eAff ↔ e ∈ a.affSet := fun e => by
    rw [hiff₂, AffCtx.affSet, Finset.mem_filter, hiffC]
  have hsubA : a.affSet ⊆ a.candSet := Finset.filter_subset _ _
  have hneedA : projHeapNeed a.piLt_mid eAff ≤ a.heapNeed := by
    rw [show projHeapNeed a.piLt_mid eAff = _ from list_sum_eq_finset_sum hnd₂ hiffA _]
    exact Finset.sum_le_sum_of_subset hsubA
  have hfr₂' : ∀ addr, addr < a.candPtr + cand.length → mem₂ addr = mem₁ addr :=
    fun addr h => hfr₂ addr (Or.inl h)
  have hmid₂ : AffMid a (a.candPtr + cand.length) eAff mem₂ :=
    { nd := hnd₂
      sub := fun e he => ((hiff e).mp ((hiff₂ e).mp he).1).1
      lt := fun e he => hlt e ((hiff₂ e).mp he).1
      at_ := hat₂
      sBit := fun v hv => by
        rw [hfr₂' (dsSBitBase a.b a.L a.vCap a.eCap + v) (by simp only [AffCtx.candPtr]; omega)]
        exact hsBit v hv
      agree := fun addr h => by
        rw [hfr₂' addr (by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [AffCtx.candPtr] <;>
          omega)]
        exact hagree₁ addr h
      hp := by simp only [AffCtx.candPtr]; omega
      hB := by
        have := hneedA
        simp only [AffCtx.candPtr]; omega }
  -- Call 3: the projection.
  refine runs_seq_call_le (vs := [a.b, a.j, a.candPtr + cand.length, eAff.length,
      a.candPtr + cand.length + eAff.length])
    (dsProjStage_meetsContract (a.toFilter (a.candPtr + cand.length) eAff mem₂ hmid₂)
      hpOps hpEdge hpProj hpEmb hpB hpW hpS)
    (by
      simp only [evalArgs, Expr.eval]
      have hb3 : a.candPtr + cand.length + eAff.length < 2 ^ a.w := by
        have := hmid₂.hB; omega
      simp [hr₁', hv₂, startState, hb3])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl|rfl|rfl)
      · exact hW _ (by simp)
      · exact hW _ (by simp)
      · simp only [AffCtx.candPtr]; omega
      · omega
      · simp only [AffCtx.candPtr]; omega)
    ⟨rfl, rfl, projStageHyp_of_mid a hmid₂⟩ ?_
  rintro r₃ mem₃ pos₃ hpost₃
  refine runs_ret_le (v := eAff.length) (Expr.eval_reg_of_eq (by simp [hv₂]))
    ⟨cand, eAff, mem₁, mem₂, r₃, hmid₁, hmid₂, hiffC, hiffA, hpost₃, rfl, hm0, hm1, hsL, hgen, hest,
      fun addr h => hfr addr (by rw [hr₁']; exact h), fun addr h => hfr₂ addr h⟩ ?_
  have hcC := list_length_eq_card hnd hiffC
  have hcA := list_length_eq_card hnd₂ hiffA
  have hsC := list_sum_eq_finset_sum hnd hiffC fun e => (a.piLt_mid e).length
  have hsA := list_sum_eq_finset_sum hnd₂ hiffA fun e => 800 * (a.piLt_mid e).length + 2000
  simp only [Expr.size, argsSize, dsAffStageContract, dsCollectCandContract,
    dsFilterAffectedContract, dsProjStageContract, buildProjCost]
  show _ ≤ _
  simp only [AffCtx.toFilter]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [hsC, hsA, hcC, hcA]
  omega

end

end MinCostFlow.DynSpanner.Program
