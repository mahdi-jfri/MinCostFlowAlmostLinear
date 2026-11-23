module

public import MinCostFlow.DynSpanner.Program.DynSpannerPhaseAux

public import MinCostFlow.DynSpanner.Program.StateLayout
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# Phase arithmetic, auxiliary graph, and bucket Word-RAM procedures (`DynSpannerPhase`)

Implements and verifies the deterministic Word-RAM procedures shared by `init` and `step` of
Algorithm 6 (`phaseProcs`, length `5`):
* `chooseLevelStmt` (`phaseIdxChooseLevel = 0`): computes `chooseLevel L q t` in `O(L + 1)` steps
  without overflowing `2 ^ w`.
* `clearAuxGraphStmt` (`phaseIdxClearAux = 1`): clears `auxPtr` back to `emptyMGraph` in
  `O(A.m + A.n + 1)` steps.
* `buildActiveOnAuxStmt` (`phaseIdxBuildActive = 2`): populates `auxPtr` with `activeSubgraph G`
  in `O(G.m + 1)` steps.
* `hBucketConsStmt` / `hBucketRemoveStmt` (`3, 4`): `O(1)` doubly-linked `hBuckets` maintenance.

The file is split in three parts: `DynSpannerPhaseDefs.lean` (programs, contracts, helpers, and
the proof for `chooseLevelStmt`), `DynSpannerPhaseAux.lean` (the proofs for the auxiliary graph),
and this file (the proofs for the buckets).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

private lemma dsDomGenBase_le_fixed (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  have h1 := dsRevGenBase_eq b L vCap eCap
  have h2 := dsRevHeadBase_eq b L vCap eCap
  have h3 := dsVStampBase_eq b L vCap eCap
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]
  omega

private def hBucketPrefixStmt (tail : Stmt) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .mul (.const 3)
      (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))))) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 4)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 4)) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .add (.reg 5) (.const 1))) ;;
  tail

private lemma hBucketPrefix_runs {w L vCap eCap b i e k T : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {tail : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (hbound : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = i) (hr2 : st.regs 2 = e)
    (hL : st.mem (b + dsLOff) = L) (hvC : st.mem (b + dsVCapOff) = vCap)
    (heC : st.mem (b + dsECapOff) = eCap)
    (htail : ∀ k₁ st₁, k₁ ≤ k + 75 →
      st₁.regs 0 = b → st₁.regs 1 = i → st₁.regs 2 = e →
      st₁.regs 3 = vCap → st₁.regs 4 = eCap → st₁.regs 5 = L →
      st₁.regs 6 = dsMinHBase b vCap eCap →
      st₁.regs 7 = dsHNextBase b vCap eCap →
      st₁.regs 8 = dsHPrevBase b vCap eCap →
      st₁.regs 9 = dsHHeadBase b vCap eCap →
      st₁.regs 10 = dsHDegDummyBase b L vCap eCap →
      st₁.mem = st.mem →
      ∃ o st' c, Runs w p ω tail st₁ o st' c ∧ Q o st' ∧ k₁ + c ≤ T) :
    ∃ o st' c, Runs w p ω (hBucketPrefixStmt tail) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hle := dsDomGenBase_le_fixed b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hmin_eq := dsMinHBase_eq b vCap eCap
  have hdg_le : 3 * dynGraphSize vCap eCap ≤ dsFixedSize L vCap eCap := by
    have : b + dsHdrSize + 3 * dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
      rw [← hmin_eq]
      have : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by omega
      exact le_trans this hle
    omega
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h1w : (1 : ℕ) < 2 ^ w := by omega
  have h3w : (3 : ℕ) < 2 ^ w := by omega
  have h4w : (4 : ℕ) < 2 ^ w := by omega
  have h6w : dsHdrSize < 2 ^ w := by simp [dsHdrSize]; omega
  have h7w : (7 : ℕ) < 2 ^ w := by omega
  have h9w : (9 : ℕ) < 2 ^ w := by omega
  have h7v_lt : 7 * vCap < 2 ^ w := by simp [dynGraphSize] at hdg_le; omega
  have h9e_lt : 9 * eCap < 2 ^ w := by simp [dynGraphSize] at hdg_le; omega
  have hdg_lt : dynGraphSize vCap eCap < 2 ^ w := by simp [dynGraphSize] at hdg_le ⊢; omega
  have h3dg_lt : 3 * dynGraphSize vCap eCap < 2 ^ w := by omega
  have hv_lt : vCap < 2 ^ w := by omega
  have he_lt : eCap < 2 ^ w := by omega
  have hdom_def : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  have hdeg_def : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hhead_def : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hprev_def : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hnext_def : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hL1_lt : L + 1 < 2 ^ w := by omega
  have hmin_lt : dsMinHBase b vCap eCap < 2 ^ w := by omega
  have hn_lt : dsMinHBase b vCap eCap + eCap < 2 ^ w := by omega
  have hp_lt : dsHNextBase b vCap eCap + eCap < 2 ^ w := by omega
  have hh_lt : dsHPrevBase b vCap eCap + eCap < 2 ^ w := by omega
  have hd_lt : dsHHeadBase b vCap eCap + (L + 1) < 2 ^ w := by omega
  have hb3_lt : b + dsVCapOff < 2 ^ w := by simp only [dsVCapOff, dsHdrSize] at hmin_eq ⊢; omega
  have hb4_lt : b + dsECapOff < 2 ^ w := by simp only [dsECapOff, dsHdrSize] at hmin_eq ⊢; omega
  have hb2_lt : b + dsLOff < 2 ^ w := by simp only [dsLOff, dsHdrSize] at hmin_eq ⊢; omega
  dsimp only [hBucketPrefixStmt]
  refine runs_seq_assign_le (v := vCap) ?_ ?_
  · exact Expr.eval_load_of_eq
      (by simp [Expr.eval, BinOp.eval, hr0, dsVCapOff, h3w, show b + 3 < 2 ^ w by simpa [dsVCapOff] using hb3_lt]) hvC
  refine runs_seq_assign_le (v := eCap) ?_ ?_
  · exact Expr.eval_load_of_eq
      (by simp [Expr.eval, BinOp.eval, hr0, dsECapOff, h4w, show b + 4 < 2 ^ w by simpa [dsECapOff] using hb4_lt]) heC
  refine runs_seq_assign_le (v := L) ?_ ?_
  · exact Expr.eval_load_of_eq
      (by simp [Expr.eval, BinOp.eval, hr0, dsLOff, show (2 : ℕ) < 2 ^ w by omega,
        show b + 2 < 2 ^ w by simpa [dsLOff] using hb2_lt]) hL
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap) ?_ ?_
  · have hb_hdr : b + dsHdrSize < 2 ^ w := by omega
    have h7v9e : 7 * vCap + 9 * eCap < 2 ^ w := by simp [dynGraphSize] at hdg_lt; omega
    have h4v : 4 + (7 * vCap + 9 * eCap) < 2 ^ w := by
      simpa [dynGraphSize, Nat.add_assoc] using hdg_lt
    have h3v : 3 * (4 + (7 * vCap + 9 * eCap)) < 2 ^ w := by
      simpa [dynGraphSize, Nat.add_assoc] using h3dg_lt
    have hmin_raw : b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) < 2 ^ w := by
      rw [hmin_eq] at hmin_lt; simpa [dynGraphSize, Nat.add_assoc] using hmin_lt
    simp [Expr.eval, BinOp.eval, hr0, h3w, h4w, h6w, h7w, h9w, h7v_lt, h9e_lt,
      h7v9e, h4v, h3v, hb_hdr, hmin_eq, dynGraphSize, Nat.add_assoc]
    omega
  refine runs_seq_assign_le (v := dsHNextBase b vCap eCap) ?_ ?_
  · simp [Expr.eval, BinOp.eval, hn_lt, dsHNextBase]
  refine runs_seq_assign_le (v := dsHPrevBase b vCap eCap) ?_ ?_
  · simp [Expr.eval, BinOp.eval, hp_lt, dsHPrevBase]
  refine runs_seq_assign_le (v := dsHHeadBase b vCap eCap) ?_ ?_
  · simp [Expr.eval, BinOp.eval, hh_lt, dsHHeadBase]
  refine runs_seq_assign_le (v := dsHDegDummyBase b L vCap eCap) ?_ ?_
  · simp [Expr.eval, BinOp.eval, h1w, hL1_lt, hd_lt, dsHDegDummyBase]
  · refine htail _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · dsimp only [Expr.size, dsVCapOff, dsECapOff, dsLOff, dsHdrSize]; omega
    · simp [hr0]
    · simp [hr1]
    · simp [hr2]
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · rfl

theorem hBucketCons_meetsContract {w L vCap eCap b : ℕ} {L_buck : List ℕ} {i e : ℕ}
    {p : Program} {bPhase bOps bEdge : ℕ}
    (hp : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bPhase + phaseIdxHBucketCons)
      (hBucketConsContract w L vCap eCap b L_buck i e) := by
  refine meetsContract_of_runs
    (hp.get (i := phaseIdxHBucketCons) (by simp [phaseProcs, phaseIdxHBucketCons]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, hbound, hiL, heCap, heNot, hL, hvC, heC, hdll, hdeg⟩
  have hle := dsDomGenBase_le_fixed b L vCap eCap
  have hdom_def : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  have hdeg_def : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hhead_def : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hprev_def : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hnext_def : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hlen_succ : L_buck.length + 1 ≤ eCap := dll_length_succ_le_cap hdll heCap heNot
  have hi_ltw : i < 2 ^ w := by omega
  have hi1_ltw : i + 1 < 2 ^ w := by omega
  have hmin_e_lt : dsMinHBase b vCap eCap + e < 2 ^ w := by omega
  have hprev_lt : dsHPrevBase b vCap eCap + eCap < 2 ^ w := by omega
  have hnext_lt : dsHNextBase b vCap eCap + eCap < 2 ^ w := by omega
  have hhead_i_lt : dsHHeadBase b vCap eCap + i < 2 ^ w := by omega
  have hdeg_i_lt : dsHDegDummyBase b L vCap eCap + i < 2 ^ w := by omega
  have he_ltw : e < 2 ^ w := by omega
  have hmin_ne_head : dsMinHBase b vCap eCap + e ≠ dsHHeadBase b vCap eCap + i := by omega
  have hmin_ne_deg : dsMinHBase b vCap eCap + e ≠ dsHDegDummyBase b L vCap eCap + i := by omega
  have hmin_ne_prev : ∀ x, dsMinHBase b vCap eCap + e ≠ dsHPrevBase b vCap eCap + x := fun x => by omega
  have hmin_ne_next : ∀ x, dsMinHBase b vCap eCap + e ≠ dsHNextBase b vCap eCap + x := fun x => by omega
  have hprefix_eq : hBucketConsStmt bOps = hBucketPrefixStmt
      (.store (.bin .add (.reg 6) (.reg 2)) (.bin .add (.reg 1) (.const 1)) ;;
       .call 11 (bOps + dgIdxDllCons)
         [.reg 8, .reg 7, .bin .add (.reg 9) (.reg 1), .bin .add (.reg 10) (.reg 1), .reg 2] ;;
       .ret (.const 0)) := rfl
  refine runs_start_le ?_
  have hget_cons : (phaseProcs bOps bEdge)[phaseIdxHBucketCons]'(by simp [phaseProcs, phaseIdxHBucketCons]) =
      hBucketConsStmt bOps := rfl
  rw [hget_cons, hprefix_eq]
  refine hBucketPrefix_runs (i := i) (e := e) hw16 hbound ?_ ?_ ?_ hL hvC heC ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  intro k₁ st hk₁ hr0 hr1 hr2 _ _ _ hr6 hr7 hr8 hr9 hr10 hmeq
  have hm_eq : st.mem = mem := hmeq
  refine runs_seq_store_le (x := dsMinHBase b vCap eCap + e) (v := i + 1) ?_ ?_ ?_
  · simp [Expr.eval, BinOp.eval, hr6, hr2, hmin_e_lt]
  · simp [Expr.eval, BinOp.eval, hr1, hi1_ltw, show (1 : ℕ) < 2 ^ w by omega]
  let mem1 := Function.update st.mem (dsMinHBase b vCap eCap + e) (i + 1)
  have hdll1 : IsDoublyLinkedList mem1 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap L_buck := by
    refine hdll.of_agree ?_ (fun x _ => ?_) (fun x _ => ?_)
    · dsimp only [mem1]; rw [Function.update_of_ne hmin_ne_head.symm, hm_eq]
    · dsimp only [mem1]; rw [Function.update_of_ne (hmin_ne_prev x).symm, hm_eq]
    · dsimp only [mem1]; rw [Function.update_of_ne (hmin_ne_next x).symm, hm_eq]
  have hdeg1 : mem1 (dsHDegDummyBase b L vCap eCap + i) = L_buck.length := by
    dsimp only [mem1]
    rw [Function.update_of_ne hmin_ne_deg.symm, hm_eq, hdeg]
  have hpre_dll : (dgDllConsContract w eCap L_buck).pre
      [dsHPrevBase b vCap eCap, dsHNextBase b vCap eCap,
        dsHHeadBase b vCap eCap + i, dsHDegDummyBase b L vCap eCap + i, e] mem1 := by
    refine ⟨dsHPrevBase b vCap eCap, dsHNextBase b vCap eCap,
      dsHHeadBase b vCap eCap + i, dsHDegDummyBase b L vCap eCap + i, e,
      rfl, hw16, hprev_lt, hnext_lt, hhead_i_lt, hdeg_i_lt, hdll1, heCap, heNot, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdeg1]
      have : eCap < 2 ^ w := by omega
      omega
    · omega
    · intro x hx; constructor <;> omega
    · intro x hx; constructor <;> omega
    · intro x y heq hx hy; omega
  refine runs_seq_call_le (r := 11) (dgDllCons_meetsContract hpOps)
    (by simp [Expr.eval, evalArgs, hr8, hr7, hr9, hr1, hr10, hr2, hhead_i_lt, hdeg_i_lt])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_dll ?_
  intro ret mem2 pos2 hpost2
  rcases hpost2 with ⟨_, _, _, _, _, hEq, _, hdll2, hdeg2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq
  rcases hEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine runs_ret_le (by eval_expr) ⟨rfl, rfl, ?_, hdll2, ?_, ?_⟩ ?_
  · dsimp only
    rw [hfr2 _ (fun x hx => (hmin_ne_prev x hx).elim)
      (fun x hx => (hmin_ne_next x hx).elim) hmin_ne_head hmin_ne_deg]
    dsimp only
    exact Function.update_self _ _ _
  · dsimp only
    rw [hdeg2]
    dsimp only
    exact congrArg (· + 1) hdeg1
  · intro addr hne_m hne_h hne_d hnotp hnotn
    dsimp only
    rw [hfr2 addr (fun x hx => hnotp x hx) (fun x hx => hnotn x hx) hne_h hne_d]
    dsimp only
    rw [Function.update_of_ne hne_m, hm_eq]
  · dsimp only [hBucketConsContract, dgDllConsContract, argsSize, Expr.size]
    omega

theorem hBucketRemove_meetsContract {w L vCap eCap b : ℕ} {L_buck : List ℕ} {i e : ℕ}
    {p : Program} {bPhase bOps bEdge : ℕ}
    (hp : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bPhase + phaseIdxHBucketRemove)
      (hBucketRemoveContract w L vCap eCap b L_buck i e) := by
  refine meetsContract_of_runs
    (hp.get (i := phaseIdxHBucketRemove) (by simp [phaseProcs, phaseIdxHBucketRemove]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, hbound, hiL, heCap, heMem, hL, hvC, heC, hdll, hdeg⟩
  have hle := dsDomGenBase_le_fixed b L vCap eCap
  have hdom_def : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  have hdeg_def : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hhead_def : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hprev_def : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hnext_def : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hi_ltw : i < 2 ^ w := by omega
  have hmin_e_lt : dsMinHBase b vCap eCap + e < 2 ^ w := by omega
  have hprev_lt : dsHPrevBase b vCap eCap + eCap < 2 ^ w := by omega
  have hnext_lt : dsHNextBase b vCap eCap + eCap < 2 ^ w := by omega
  have hhead_i_lt : dsHHeadBase b vCap eCap + i < 2 ^ w := by omega
  have hdeg_i_lt : dsHDegDummyBase b L vCap eCap + i < 2 ^ w := by omega
  have he_ltw : e < 2 ^ w := by omega
  have hmin_ne_head : dsMinHBase b vCap eCap + e ≠ dsHHeadBase b vCap eCap + i := by omega
  have hmin_ne_deg : dsMinHBase b vCap eCap + e ≠ dsHDegDummyBase b L vCap eCap + i := by omega
  have hmin_ne_prev : ∀ x, dsMinHBase b vCap eCap + e ≠ dsHPrevBase b vCap eCap + x := fun x => by omega
  have hmin_ne_next : ∀ x, dsMinHBase b vCap eCap + e ≠ dsHNextBase b vCap eCap + x := fun x => by omega
  have hprefix_eq : hBucketRemoveStmt bOps = hBucketPrefixStmt
      (.store (.bin .add (.reg 6) (.reg 2)) (.const 0) ;;
       .call 11 (bOps + dgIdxDllRemove)
         [.reg 8, .reg 7, .bin .add (.reg 9) (.reg 1), .bin .add (.reg 10) (.reg 1), .reg 2] ;;
       .ret (.const 0)) := rfl
  refine runs_start_le ?_
  have hget_rem : (phaseProcs bOps bEdge)[phaseIdxHBucketRemove]'(by simp [phaseProcs, phaseIdxHBucketRemove]) =
      hBucketRemoveStmt bOps := rfl
  rw [hget_rem, hprefix_eq]
  refine hBucketPrefix_runs (i := i) (e := e) hw16 hbound ?_ ?_ ?_ hL hvC heC ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  intro k₁ st hk₁ hr0 hr1 hr2 _ _ _ hr6 hr7 hr8 hr9 hr10 hmeq
  have hm_eq : st.mem = mem := hmeq
  refine runs_seq_store_le (x := dsMinHBase b vCap eCap + e) (v := 0) ?_ (by eval_expr) ?_
  · simp [Expr.eval, BinOp.eval, hr6, hr2, hmin_e_lt]
  let mem1 := Function.update st.mem (dsMinHBase b vCap eCap + e) 0
  have hdll1 : IsDoublyLinkedList mem1 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap L_buck := by
    refine hdll.of_agree ?_ (fun x _ => ?_) (fun x _ => ?_)
    · dsimp only [mem1]; rw [Function.update_of_ne hmin_ne_head.symm, hm_eq]
    · dsimp only [mem1]; rw [Function.update_of_ne (hmin_ne_prev x).symm, hm_eq]
    · dsimp only [mem1]; rw [Function.update_of_ne (hmin_ne_next x).symm, hm_eq]
  have hdeg1 : mem1 (dsHDegDummyBase b L vCap eCap + i) = L_buck.length := by
    dsimp only [mem1]
    rw [Function.update_of_ne hmin_ne_deg.symm, hm_eq, hdeg]
  have hlen_le : L_buck.length ≤ eCap := dll_length_le_cap hdll
  have hpre_dll : (dgDllRemoveContract w eCap L_buck).pre
      [dsHPrevBase b vCap eCap, dsHNextBase b vCap eCap,
        dsHHeadBase b vCap eCap + i, dsHDegDummyBase b L vCap eCap + i, e] mem1 := by
    refine ⟨dsHPrevBase b vCap eCap, dsHNextBase b vCap eCap,
      dsHHeadBase b vCap eCap + i, dsHDegDummyBase b L vCap eCap + i, e,
      rfl, hw16, hprev_lt, hnext_lt, hhead_i_lt, hdeg_i_lt, hdll1, heMem, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdeg1]
      have : eCap < 2 ^ w := by omega
      omega
    · omega
    · intro x hx; constructor <;> omega
    · intro x hx; constructor <;> omega
    · intro x y heq hx hy; omega
  refine runs_seq_call_le (r := 11) (dgDllRemove_meetsContract hpOps)
    (by simp [Expr.eval, evalArgs, hr8, hr7, hr9, hr1, hr10, hr2, hhead_i_lt, hdeg_i_lt])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_dll ?_
  intro ret mem2 pos2 hpost2
  rcases hpost2 with ⟨_, _, _, _, _, hEq, _, hdll2, hdeg2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq
  rcases hEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine runs_ret_le (by eval_expr) ⟨rfl, rfl, ?_, hdll2, ?_, ?_⟩ ?_
  · dsimp only
    rw [hfr2 _ (fun x hx => (hmin_ne_prev x hx).elim)
      (fun x hx => (hmin_ne_next x hx).elim) hmin_ne_head hmin_ne_deg]
    dsimp only
    exact Function.update_self _ _ _
  · dsimp only
    rw [hdeg2]
    dsimp only
    exact congrArg (· - 1) hdeg1
  · intro addr hne_m hne_h hne_d hnotp hnotn
    dsimp only
    rw [hfr2 addr (fun x hx => hnotp x hx) (fun x hx => hnotn x hx) hne_h hne_d]
    dsimp only
    rw [Function.update_of_ne hne_m, hm_eq]
  · dsimp only [hBucketRemoveContract, dgDllRemoveContract, argsSize, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program

