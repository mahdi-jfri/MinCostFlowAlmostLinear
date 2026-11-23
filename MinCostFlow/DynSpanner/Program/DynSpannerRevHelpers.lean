module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevDefs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared helpers and loop invariant for `dsInsertWalkRev` (`DynSpannerRevHelpers`)

Provides the walk-prefix lemma, disjointness layout structure `DsLayoutFacts`, register setup
`dsInsertWalkRevPrep_cont`, endpoint direction dispatch `dsInsertWalkRev_dir_triple`, and the loop
invariant `dsInsertWalkRevInv` used by `dsInsertWalkRev_step_triple` and `dsInsertWalkRev_meetsContract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

lemma walkVertices_take_succ {H : MGraph} {uStart : ℕ} {W : List (ℕ × Bool)}
    {k : ℕ} (hk : k < W.length) :
    ∀ v, v ∈ H.walkVertices uStart (W.take (k + 1)) ↔
      v ∈ H.walkVertices uStart (W.take k) ∨ v = H.dst (W[k]'hk) := by
  intro v
  rw [List.take_succ_eq_append_getElem hk]
  simp only [MGraph.walkVertices, List.map_append, List.map_cons, List.map_nil,
    List.mem_cons, List.mem_append]
  tauto

lemma dsMEmbTempBase_eq_rev (b L vCap eCap : ℕ) :
    dsMEmbTempBase b L vCap eCap =
      dsRevGenBase b L vCap eCap + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) +
        (vCap + 2 * eCap) := by
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase]
  omega

structure DsLayoutFacts (b L vCap eCap i v i' v' heapPtr : ℕ) : Prop where
  dom_lt_fix : dsDomGenBase b L vCap eCap + i < b + dsFixedSize L vCap eCap
  rg_lt_fix : dsRevGenBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap
  rh_lt_fix : dsRevHeadBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap
  vs_lt_fix : dsVStampBase b L vCap eCap + v < b + dsFixedSize L vCap eCap
  vs_ne_dom : dsVStampBase b L vCap eCap + v ≠ dsDomGenBase b L vCap eCap + i'
  vs_ne_gen : dsVStampBase b L vCap eCap + v ≠ b + dsGenOff
  vs_ne_rg : dsVStampBase b L vCap eCap + v ≠ dsRevGenBase b L vCap eCap + i' * vCap + v'
  vs_ne_rh : dsVStampBase b L vCap eCap + v ≠ dsRevHeadBase b L vCap eCap + i' * vCap + v'
  rg_ne_dom : dsRevGenBase b L vCap eCap + i * vCap + v ≠ dsDomGenBase b L vCap eCap + i'
  rh_ne_dom : dsRevHeadBase b L vCap eCap + i * vCap + v ≠ dsDomGenBase b L vCap eCap + i'
  rg_ne_gen : dsRevGenBase b L vCap eCap + i * vCap + v ≠ b + dsGenOff
  rh_ne_gen : dsRevHeadBase b L vCap eCap + i * vCap + v ≠ b + dsGenOff
  dom_ne_gen : dsDomGenBase b L vCap eCap + i ≠ b + dsGenOff
  vs_lt_hp : dsVStampBase b L vCap eCap + v < heapPtr
  rg_lt_hp : dsRevGenBase b L vCap eCap + i * vCap + v < heapPtr
  rh_lt_hp : dsRevHeadBase b L vCap eCap + i * vCap + v < heapPtr

lemma dsLayout_facts {b L vCap eCap i v i' v' heapPtr : ℕ}
    (hi : i ≤ L) (hv : v < vCap) (hi' : i' ≤ L) (hv' : v' < vCap)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) :
    DsLayoutFacts b L vCap eCap i v i' v' heapPtr := by
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq_rev b L vCap eCap
  have hml := mul_add_lt_mul_succ hi hv
  have hml' := mul_add_lt_mul_succ hi' hv'
  have hgen_lt_hdr : dsGenOff < dsHdrSize := by decide
  have hdg_le_min : b + dsHdrSize ≤ dsMinHBase b vCap eCap := by omega
  have hmin_le_dom : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by omega
  have hdom_le_rg : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsRevGenBase b L vCap eCap := by omega
  have hrg_rh : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hrh_vs : dsRevHeadBase b L vCap eCap + (L + 1) * vCap ≤ dsVStampBase b L vCap eCap := by omega
  have hvs_mem : dsVStampBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap := by
    simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma runs_of_triple_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {P : State → Prop} {Q Q' : Outcome → State → Prop} {k₀ bound b' : ℕ}
    (ht : Triple w p P s Q (fun _ => b')) {st : State} (hp : P st)
    (hq : ∀ o st', Q o st' → Q' o st') (hc : k₀ + b' ≤ bound) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q' o st' ∧ k₀ + c ≤ bound := by
  obtain ⟨o, st', c, hrun, hq0, hc0⟩ := ht st ω hp
  exact ⟨o, st', c, hrun, hq o st' hq0, le_trans (Nat.add_le_add_left hc0 k₀) hc⟩

lemma dsInsertWalkRevPrep_cont {w L vCap eCap b i e uStart wPtr hPtr heapPtr cCont cTot : ℕ}
    {p : Program} {rest : Stmt} {Q : Outcome → State → Prop}
    {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hb_ltw : b < 2 ^ w)
    (hfix_le : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_lt : heapPtr < 2 ^ w)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    (hc_tot : 120 + cCont ≤ cTot)
    (hcont : Triple w p
      (fun st1 : State =>
        st1.mem = mem ∧
        st1.regs 0 = b ∧ st1.regs 1 = i ∧ st1.regs 2 = e ∧ st1.regs 3 = uStart ∧
        st1.regs 4 = wPtr ∧ st1.regs 5 = hPtr ∧ st1.regs 6 = heapPtr ∧
        st1.regs 7 = vCap ∧ st1.regs 8 = eCap ∧ st1.regs 9 = L ∧
        st1.regs 10 = dsVStampBase b L vCap eCap)
      rest Q (fun _ => cCont)) :
    ∃ o st' c, Runs w p ω
      (.assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 9 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 10 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 7)) (.bin .mul (.const 9) (.reg 8)))) ;;
       .assign 10 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 10))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.bin .mul (.const 3) (.reg 8))
           (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.bin .add (.reg 9) (.const 1))
           (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 8))))) ;;
       .assign 10 (.bin .add (.reg 10) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7)))
           (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))) (.reg 7)))) ;;
       rest)
      (startState [b, i, e, uStart, wPtr, hPtr, heapPtr] mem pos) o st' c ∧
      Q o st' ∧ 0 + c ≤ cTot := by
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix_le hheap_lt
  rcases had with ⟨hdg_sz, hdg_lt, hmin_eq, hmin_lt, hdom_lt, _, _, hrevG_lt, hrevH_lt, hvs_fix, _, _⟩
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq_rev b L vCap eCap
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h6_lt : (6 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have h9_lt : (9 : ℕ) < 2 ^ w := by omega
  have hvCap_ltw : vCap < 2 ^ w := by omega
  have heCap_ltw : eCap < 2 ^ w := by omega
  have hL_ltw : L < 2 ^ w := by omega
  have hvs_lt : dsVStampBase b L vCap eCap < 2 ^ w := by omega
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsVCapOff, h3_lt,
      show b + 3 < 2 ^ w by omega]) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsECapOff, h4_lt,
      show b + 4 < 2 ^ w by omega]) heC) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsLOff, h2_lt,
      show b + 2 < 2 ^ w by omega]) hL) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h4_lt, h7_lt, h9_lt,
      show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 7 * vCap + 9 * eCap < 2 ^ w by omega,
      show 4 + (7 * vCap + 9 * eCap) < 2 ^ w by omega]; omega) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (by rw [← hmin_eq, show dsHdrSize = 6 from rfl]
        simp [Expr.eval, BinOp.eval, startState, h6_lt, h3_lt,
          show b + 6 < 2 ^ w by omega, show 3 * dynGraphSize vCap eCap < 2 ^ w by omega,
          show b + 6 + 3 * dynGraphSize vCap eCap < 2 ^ w by
            rw [← show dsHdrSize = 6 from rfl, hmin_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by rw [dsDomGenBase_eq]
        simp [Expr.eval, BinOp.eval, h3_lt, h2_lt, h1_lt,
          show 3 * eCap < 2 ^ w by omega, show L + 1 < 2 ^ w by omega,
          show 2 * (L + 1) < 2 ^ w by omega, show 3 * eCap + 2 * (L + 1) < 2 ^ w by omega,
          show dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) < 2 ^ w by
            rw [← dsDomGenBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsRevGenBase b L vCap eCap)
    (by rw [dsRevGenBase_eq]
        simp [Expr.eval, BinOp.eval, h1_lt, h2_lt,
          show L + 1 < 2 ^ w by omega, show (L + 1) * eCap < 2 ^ w by omega,
          show 2 * ((L + 1) * eCap) < 2 ^ w by omega,
          show (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w by omega,
          show dsDomGenBase b L vCap eCap + ((L + 1) + 2 * ((L + 1) * eCap)) < 2 ^ w by
            rw [← dsRevGenBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsRevHeadBase b L vCap eCap)
    (by rw [dsRevHeadBase_eq]
        simp [Expr.eval, BinOp.eval, h1_lt,
          show L + 1 < 2 ^ w by omega, show (L + 1) * vCap < 2 ^ w by omega,
          show dsRevGenBase b L vCap eCap + (L + 1) * vCap < 2 ^ w by
            rw [← dsRevHeadBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsVStampBase b L vCap eCap)
    (by rw [dsVStampBase_eq]
        simp [Expr.eval, BinOp.eval, h2_lt, h1_lt,
          show L + 1 < 2 ^ w by omega, show (L + 1) * vCap < 2 ^ w by omega,
          show 2 * ((L + 1) * vCap) < 2 ^ w by omega, show 2 * (L + 1) < 2 ^ w by omega,
          show 2 * (L + 1) + vCap < 2 ^ w by omega,
          show 2 * ((L + 1) * vCap) + (2 * (L + 1) + vCap) < 2 ^ w by omega,
          show dsRevHeadBase b L vCap eCap + (2 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) < 2 ^ w by
            rw [← dsVStampBase_eq]; omega]) ?_
  refine runs_of_triple_le hcont ?_ (fun _ _ h => h) (by dsimp only [Expr.size]; omega)
  exact ⟨rfl, by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp, by simp, by simp, by simp⟩

lemma dsInsertWalkRev_dir_triple {w vCap eCap b i e wPtr hPtr heapCur vStamp
    gen1 len k eStep : ℕ} {dir : Bool} {H : MGraph} {p : Program} {bOps : ℕ} {mem0 : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hw16 : 16 ≤ 2 ^ w)
    (hh_ltw : hPtr + dynGraphSize vCap eCap < 2 ^ w) (hh_ptrw : hPtr < 2 ^ w)
    (he_ltw : eStep < 2 ^ w) (heE : eStep ∈ H.E) (hH : DynGraphAt mem0 hPtr vCap eCap H) :
    Triple w p
      (fun st_c => st_c.mem = mem0 ∧
        st_c.regs 0 = b ∧ st_c.regs 1 = i ∧ st_c.regs 2 = e ∧ st_c.regs 4 = wPtr ∧
        st_c.regs 5 = hPtr ∧ st_c.regs 6 = heapCur ∧ st_c.regs 10 = vStamp ∧
        st_c.regs 11 = gen1 ∧ st_c.regs 12 = len ∧ st_c.regs 13 = k ∧
        st_c.regs 14 = (if dir then 1 else 0) ∧ st_c.regs 15 = eStep)
      (.cond (.reg 14)
        (.call 15 (bOps + dgIdxGetHead) [.reg 5, .reg 15])
        (.call 15 (bOps + dgIdxGetTail) [.reg 5, .reg 15]))
      (normalPost fun st_d => st_d.mem = mem0 ∧
        st_d.regs 0 = b ∧ st_d.regs 1 = i ∧ st_d.regs 2 = e ∧ st_d.regs 4 = wPtr ∧
        st_d.regs 5 = hPtr ∧ st_d.regs 6 = heapCur ∧ st_d.regs 10 = vStamp ∧
        st_d.regs 11 = gen1 ∧ st_d.regs 12 = len ∧ st_d.regs 13 = k ∧
        st_d.regs 15 = H.dst (eStep, dir))
      (fun _ => 60) := by
  intro st_c ω ⟨hm_c, cr0, cr1, cr2, cr4, cr5, cr6, cr10, cr11, cr12, cr13, cr14, cr15⟩
  refine runs_start_le ?_
  have hpre_c' : (dgGetTailContract w vCap eCap H).pre [hPtr, eStep] st_c.mem :=
    ⟨hPtr, eStep, rfl, hw16, hh_ltw, heE, hm_c ▸ hH⟩
  have hpre_ch' : (dgGetHeadContract w vCap eCap H).pre [hPtr, eStep] st_c.mem :=
    ⟨hPtr, eStep, rfl, hw16, hh_ltw, heE, hm_c ▸ hH⟩
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at cr14
    refine runs_cond_le (v := 0) (by simp [Expr.eval, cr14])
      (fun hne => False.elim (by omega)) (fun _ => ?_)
    refine runs_call_le (r := 15) (dgGetTail_meetsContract hpOps)
      (by simp [Expr.eval, evalArgs, cr5, cr15])
      (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> assumption)
      hpre_c' ?_
    intro ret1 mem1 pos1 ⟨_, _, hEq1, hm1, hret1⟩
    simp only [List.cons.injEq, and_true] at hEq1
    rcases hEq1 with ⟨rfl, rfl⟩
    dsimp only [normalPost]
    refine ⟨⟨hm1.trans hm_c, by simp [cr0], by simp [cr1], by simp [cr2], by simp [cr4],
      by simp [cr5], by simp [cr6], by simp [cr10], by simp [cr11], by simp [cr12],
      by simp [cr13], ?_⟩, ?_⟩
    · rw [Function.update_self, hret1]; rfl
    · dsimp only [dgGetTailContract, argsSize, Expr.size]; omega
  · simp only [↓reduceIte] at cr14
    refine runs_cond_le (v := 1) (by simp [Expr.eval, cr14])
      (fun _ => ?_) (fun hz => False.elim (by omega))
    refine runs_call_le (r := 15) (dgGetHead_meetsContract hpOps)
      (by simp [Expr.eval, evalArgs, cr5, cr15])
      (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> assumption)
      hpre_ch' ?_
    intro ret1 mem1 pos1 ⟨_, _, hEq1, hm1, hret1⟩
    simp only [List.cons.injEq, and_true] at hEq1
    rcases hEq1 with ⟨rfl, rfl⟩
    dsimp only [normalPost]
    refine ⟨⟨hm1.trans hm_c, by simp [cr0], by simp [cr1], by simp [cr2], by simp [cr4],
      by simp [cr5], by simp [cr6], by simp [cr10], by simp [cr11], by simp [cr12],
      by simp [cr13], ?_⟩, ?_⟩
    · rw [Function.update_self, hret1]; rfl
    · dsimp only [dgGetHeadContract, argsSize, Expr.size]; omega

def dsInsertWalkRevInv (L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 : ℕ)
    (H : MGraph) (W : List (ℕ × Bool)) (rev0 : ℕ → List ℕ) (foot0 : ℕ → Prop)
    (mem : ℕ → ℕ) (k : ℕ) (st : State) : Prop :=
  let vStamp := dsVStampBase b L vCap eCap
  let domVal := mem (dsDomGenBase b L vCap eCap + i)
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  ∃ heapCur : ℕ,
    heapPtr + 2 ≤ heapCur ∧ heapCur ≤ heapPtr + 2 * (k + 1) ∧
    st.regs 0 = b ∧ st.regs 1 = i ∧ st.regs 2 = e ∧ st.regs 4 = wPtr ∧ st.regs 5 = hPtr ∧
    st.regs 6 = heapCur ∧ st.regs 10 = vStamp ∧ st.regs 11 = gen0 + 1 ∧
    st.regs 12 = W.length ∧ st.regs 13 = k ∧
    st.mem (b + dsGenOff) = gen0 + 1 ∧
    (∀ v < vCap,
      if v ∈ H.walkVertices uStart (W.take k)
      then st.mem (vStamp + v) = gen0 + 1
      else st.mem (vStamp + v) ≤ gen0) ∧
    (∀ v < vCap,
      if v ∈ H.walkVertices uStart (W.take k) then
        st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) = domVal ∧
        LinkedListIn (footOf heapCur) st.mem
          (st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) (e :: rev0 v)
      else
        st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) =
          mem (dsRevGenBase b L vCap eCap + i * vCap + v) ∧
        st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v) =
          mem (dsRevHeadBase b L vCap eCap + i * vCap + v) ∧
        (if st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) = domVal
         then LinkedListIn (footOf heapCur) st.mem
                (st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) (rev0 v)
         else rev0 v = [])) ∧
    ∀ addr,
      addr ≠ b + dsGenOff →
      (∀ v < vCap, addr ≠ vStamp + v) →
      (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + i * vCap + v) →
      (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + i * vCap + v) →
      (addr < heapPtr ∨ heapCur ≤ addr) →
      st.mem addr = mem addr


end

end MinCostFlow.DynSpanner.Program
