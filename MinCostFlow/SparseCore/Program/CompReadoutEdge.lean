module

public import MinCostFlow.SparseCore.Program.CompReadout
import MinCostFlow.SparseCore.CompLSFBridge

/-!
# Readout Verification (`op 4` and `op 5`) for Per-Component Dynamic LSF (`CompReadoutEdge`)

Completes the readout proofs for `compEdgeInfoProc` (`op 4`) and `compInfoProc` (`op 5`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

public section

private lemma compInfo_exec {w b heap nC nE k vCap eCap L_w pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hb_lt : b + compHdrSize < 2 ^ w) (hb_heap : b + compHdrSize ≤ heap)
    (hheap_w : heap + 6 < 2 ^ w)
    (h_nC : mem (b + compOffNumComps) = nC) (h_nE : mem (b + compOffNumEdgeful) = nE)
    (h_k : mem (b + compOffK) = k) (h_vC : mem (b + compOffVCap) = vCap)
    (h_eC : mem (b + compOffECap) = eCap) (h_Lw : mem (b + compOffLW) = L_w) :
    ∃ st' c, Runs w p ω compInfoProc (startState [b, heap] mem pos) (.returned (heap + 6)) st' c ∧
      st'.mem heap = nC ∧ st'.mem (heap + 1) = nE ∧ st'.mem (heap + 2) = k ∧
      st'.mem (heap + 3) = vCap ∧ st'.mem (heap + 4) = eCap ∧ st'.mem (heap + 5) = L_w ∧
      (∀ a, a < heap ∨ heap + 6 ≤ a → st'.mem a = mem a) ∧ c ≤ 120 := by
  let st0 := startState [b, heap] mem pos
  have hstep : ∀ (off dst val : ℕ) (s : State),
      off < compHdrSize → dst < 6 → s.regs 0 = b → s.regs 1 = heap →
      s.mem (b + off) = val →
      Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const off))) ;;
          if dst = 0 then .store (.reg 1) (.reg 2)
          else .store (.bin .add (.reg 1) (.const dst)) (.reg 2))
        s .normal { s with regs := Function.update s.regs 2 val,
                           mem := Function.update s.mem (heap + dst) val }
        (if dst = 0 then 9 else 11) := by
    intro off dst val s hoff hdst hr0 hr1 hm
    let s1 : State := { s with regs := Function.update s.regs 2 val }
    have ha : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const off)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨val, Expr.eval_load_of_eq (by
        dsimp [compHdrSize] at hb_lt hoff
        simp [Expr.eval, BinOp.eval, hr0, show off < 2 ^ w by omega, show b + off < 2 ^ w by omega]) hm,
        rfl, rfl, by simp [Expr.size]⟩
    split_ifs with h0
    · subst h0
      have hs : Runs w p ω (.store (.reg 1) (.reg 2)) s1 .normal
          { s1 with mem := Function.update s1.mem (heap + 0) val } 3 :=
        runs_store_iff.mpr ⟨heap, val, by simp [s1, Expr.eval, hr1], by simp [s1, Expr.eval],
          rfl, by simp [s1], by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 3, ha, hs, rfl⟩)
    · have hs : Runs w p ω (.store (.bin .add (.reg 1) (.const dst)) (.reg 2)) s1 .normal
          { s1 with mem := Function.update s1.mem (heap + dst) val } 5 :=
        runs_store_iff.mpr ⟨heap + dst, val, by
          simp [s1, Expr.eval, BinOp.eval, hr1, show dst < 2 ^ w by omega, show heap + dst < 2 ^ w by omega],
          by simp [s1, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 5, ha, hs, rfl⟩)
  let s1 : State := { st0 with regs := Function.update st0.regs 2 nC, mem := Function.update mem heap nC }
  let s2 : State := { s1 with regs := Function.update s1.regs 2 nE, mem := Function.update s1.mem (heap + 1) nE }
  let s3 : State := { s2 with regs := Function.update s2.regs 2 k, mem := Function.update s2.mem (heap + 2) k }
  let s4 : State := { s3 with regs := Function.update s3.regs 2 vCap, mem := Function.update s3.mem (heap + 3) vCap }
  let s5 : State := { s4 with regs := Function.update s4.regs 2 eCap, mem := Function.update s4.mem (heap + 4) eCap }
  let s6 : State := { s5 with regs := Function.update s5.regs 2 L_w, mem := Function.update s5.mem (heap + 5) L_w }
  have hbelow : ∀ a < heap, s1.mem a = mem a ∧ s2.mem a = mem a ∧ s3.mem a = mem a ∧
      s4.mem a = mem a ∧ s5.mem a = mem a := fun a ha => by
    have e1 : s1.mem a = mem a := Function.update_of_ne (by omega) _ _
    have e2 : s2.mem a = mem a := (Function.update_of_ne (by omega) _ _).trans e1
    have e3 : s3.mem a = mem a := (Function.update_of_ne (by omega) _ _).trans e2
    have e4 : s4.mem a = mem a := (Function.update_of_ne (by omega) _ _).trans e3
    have e5 : s5.mem a = mem a := (Function.update_of_ne (by omega) _ _).trans e4
    exact ⟨e1, e2, e3, e4, e5⟩
  have h1 := hstep compOffNumComps 0 nC st0 (by decide) (by omega) (by simp [st0, startState]) (by simp [st0, startState]) h_nC
  have h2 := hstep compOffNumEdgeful 1 nE s1 (by decide) (by omega) (by simp [s1, st0, startState]) (by simp [s1, st0, startState])
    ((hbelow _ (by dsimp [compOffNumEdgeful, compHdrSize] at hb_heap ⊢; omega)).1.trans h_nE)
  have h3 := hstep compOffK 2 k s2 (by decide) (by omega) (by simp [s2, s1, st0, startState]) (by simp [s2, s1, st0, startState])
    ((hbelow _ (by dsimp [compOffK, compHdrSize] at hb_heap ⊢; omega)).2.1.trans h_k)
  have h4 := hstep compOffVCap 3 vCap s3 (by decide) (by omega) (by simp [s3, s2, s1, st0, startState]) (by simp [s3, s2, s1, st0, startState])
    ((hbelow _ (by dsimp [compOffVCap, compHdrSize] at hb_heap ⊢; omega)).2.2.1.trans h_vC)
  have h5 := hstep compOffECap 4 eCap s4 (by decide) (by omega) (by simp [s4, s3, s2, s1, st0, startState]) (by simp [s4, s3, s2, s1, st0, startState])
    ((hbelow _ (by dsimp [compOffECap, compHdrSize] at hb_heap ⊢; omega)).2.2.2.1.trans h_eC)
  have h6 := hstep compOffLW 5 L_w s5 (by decide) (by omega) (by simp [s5, s4, s3, s2, s1, st0, startState]) (by simp [s5, s4, s3, s2, s1, st0, startState])
    ((hbelow _ (by dsimp [compOffLW, compHdrSize] at hb_heap ⊢; omega)).2.2.2.2.trans h_Lw)
  have hret : Runs w p ω (.ret (.bin .add (.reg 1) (.const 6))) s6 (.returned (heap + 6)) s6 4 :=
    runs_ret_iff.mpr ⟨heap + 6, by
      simp [s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 6 < 2 ^ w by omega, hheap_w],
      rfl, rfl, by simp [Expr.size]⟩
  simp only [↓reduceIte, Nat.add_zero] at h1
  simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega,
    show (4 : ℕ) ≠ 0 by omega, show (5 : ℕ) ≠ 0 by omega, ↓reduceIte] at h2 h3 h4 h5 h6
  have hseq2 : ∀ {A B C : Stmt} {u v t : State} {o : Outcome} {c1 c2 : ℕ},
      Runs w p ω (A ;; B) u .normal v c1 → Runs w p ω C v o t c2 →
      Runs w p ω (A ;; (B ;; C)) u o t (c1 + c2 + 1) := by
    intro A B C u v t o c1 c2 hAB hC
    rcases runs_seq_iff.mp hAB with ⟨_, _, _, hno, _⟩ | ⟨m, ca, cb, hA, hB, rfl⟩
    · cases hno
    · exact runs_seq_iff.mpr (Or.inr ⟨m, ca, cb + c2 + 1, hA,
        runs_seq_iff.mpr (Or.inr ⟨v, cb, c2, hB, hC, rfl⟩), by omega⟩)
  have hrun : Runs w p ω compInfoProc st0 (.returned (heap + 6)) s6 74 := by
    unfold compInfoProc
    exact hseq2 h1 (hseq2 h2 (hseq2 h3 (hseq2 h4 (hseq2 h5 (hseq2 h6 hret)))))
  have hfr : ∀ a, a < heap ∨ heap + 6 ≤ a → s6.mem a = mem a := fun a ha => by
    dsimp only [s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨s6, 74, hrun, ?_, ?_, ?_, ?_, ?_, ?_, hfr, by omega⟩ <;>
    dsimp only [s6, s5, s4, s3, s2, s1] <;>
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])

private lemma compEdgeInfo_exec_ins {w b j e heap crPtr insPtr crV onePtr pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (_hb_lt : b + compHdrSize < 2 ^ w) (hb_heap : b + compHdrSize ≤ heap)
    (hheap_w : heap + 4 < 2 ^ w) (hcr_w : crPtr + e < 2 ^ w) (hins_w : insPtr + e < 2 ^ w)
    (h_crP : mem (b + compOffIsCrossPtr) = crPtr) (h_crV : mem (crPtr + e) = crV)
    (h_insP : mem (b + compOffIsInsPtr) = insPtr) (h_insV : mem (insPtr + e) = 1)
    (h_oneP : mem (b + compOffOneLimbPtr) = onePtr) :
    ∃ st' c, Runs w p ω compEdgeInfoProc (startState [b, j, e, heap] mem pos) (.returned (heap + 4)) st' c ∧
      st'.mem heap = crV ∧ st'.mem (heap + 1) = 1 ∧
      st'.mem (heap + 2) = onePtr ∧ st'.mem (heap + 3) = onePtr ∧
      (∀ a, a < heap ∨ heap + 4 ≤ a → st'.mem a = mem a) ∧ c ≤ 180 := by
  let st0 := startState [b, j, e, heap] mem pos
  let s1 : State := { st0 with regs := Function.update st0.regs 4 crPtr }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 crV }
  let s3 : State := { s2 with regs := Function.update s2.regs 6 insPtr }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 1 }
  let m1 := Function.update mem heap crV
  let m2 := Function.update m1 (heap + 1) 1
  let s5 : State := { s4 with mem := m1 }
  let s6 : State := { s5 with mem := m2 }
  let s7 : State := { s6 with regs := Function.update s6.regs 8 onePtr }
  let m3 := Function.update m2 (heap + 2) onePtr
  let m4 := Function.update m3 (heap + 3) onePtr
  let s8 : State := { s7 with mem := m3 }
  let s9 : State := { s8 with mem := m4 }
  have hld : ∀ (r off val : ℕ) (s : State), off < compHdrSize → s.regs 0 = b → s.mem (b + off) = val →
      Runs w p ω (.assign r (.load (.bin .add (.reg 0) (.const off)))) s .normal
        { s with regs := Function.update s.regs r val } 5 := fun r off val s hoff hr0 hm =>
    runs_assign_iff.mpr ⟨val, Expr.eval_load_of_eq (x := b + off) (by
      simp [Expr.eval, BinOp.eval, hr0, show off < 2 ^ w by omega, show b + off < 2 ^ w by omega]) hm,
      rfl, rfl, by simp [Expr.size]⟩
  have h1 := hld 4 compOffIsCrossPtr crPtr st0 (by decide) (by simp [st0, startState]) h_crP
  have h2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.reg 2)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨crV, Expr.eval_load_of_eq (by
      simp [s1, st0, startState, Expr.eval, BinOp.eval, hcr_w]) h_crV, rfl, rfl, by simp [Expr.size]⟩
  have h3 := hld 6 compOffIsInsPtr insPtr s2 (by decide) (by simp [s2, s1, st0, startState]) h_insP
  have h4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 6) (.reg 2)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (by
      simp [s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, hins_w]) h_insV, rfl, rfl, by simp [Expr.size]⟩
  have h5 : Runs w p ω (.store (.reg 3) (.reg 5)) s4 .normal s5 3 :=
    runs_store_iff.mpr ⟨heap, crV, by simp [s4, s3, s2, s1, st0, startState, Expr.eval],
      by simp [s4, s3, s2, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have h6 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 7)) s5 .normal s6 5 :=
    runs_store_iff.mpr ⟨heap + 1, 1, by
      simp [s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega],
      by simp [s5, s4, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have h7 := hld 8 compOffOneLimbPtr onePtr s6 (by decide) (by simp [s6, s5, s4, s3, s2, s1, st0, startState])
    (by have hoff : compOffOneLimbPtr < compHdrSize := by decide
        dsimp only [s6, s5, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h_oneP)
  have h8 : Runs w p ω (.store (.bin .add (.reg 3) (.const 2)) (.reg 8)) s7 .normal s8 5 :=
    runs_store_iff.mpr ⟨heap + 2, onePtr, by
      simp [s7, s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show heap + 2 < 2 ^ w by omega],
      by simp [s7, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have h9 : Runs w p ω (.store (.bin .add (.reg 3) (.const 3)) (.reg 8)) s8 .normal s9 5 :=
    runs_store_iff.mpr ⟨heap + 3, onePtr, by
      simp [s8, s7, s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show heap + 3 < 2 ^ w by omega],
      by simp [s8, s7, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.const 4))) s9 (.returned (heap + 4)) s9 4 :=
    runs_ret_iff.mpr ⟨heap + 4, by
      simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, hheap_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hbr : Runs w p ω _ s6 (.returned (heap + 4)) s9 22 :=
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, 16, h7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 5, 10, h8,
      runs_seq_iff.mpr (Or.inr ⟨s9, 5, 4, h9, hret, rfl⟩), rfl⟩), rfl⟩)
  have hfull : Runs w p ω compEdgeInfoProc st0 (.returned (heap + 4)) s9 58 := by
    unfold compEdgeInfoProc
    exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 52, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 46, h2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, 40, h3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, 34, h4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 3, 30, h5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, 24, h6,
        runs_cond_iff.mpr ⟨1, 22, by simp [s6, s5, s4, Expr.eval], by simpa using hbr, by simp [Expr.size]⟩,
        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hfr : ∀ a, a < heap ∨ heap + 4 ≤ a → s9.mem a = mem a := fun a ha => by
    dsimp only [s9, s8, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨s9, 58, hfull, ?_, ?_, ?_, ?_, hfr, by omega⟩ <;>
    dsimp only [s9, s8, m4, m3, m2, m1] <;>
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])

private lemma compEdgeInfo_exec_nonins {w b j e heap crPtr insPtr crV eC1Ptr c1 efIdxPtr ec k hdlPtr hWin L_w numB denB pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (_hb_lt : b + compHdrSize < 2 ^ w) (hb_heap : b + compHdrSize ≤ heap)
    (hheap_w : heap + 4 < 2 ^ w) (hcr_w : crPtr + e < 2 ^ w) (hins_w : insPtr + e < 2 ^ w)
    (heC1_w : eC1Ptr + e < 2 ^ w) (heC1_lt : eC1Ptr + e < heap)
    (hef_w : efIdxPtr + c1 < 2 ^ w) (hef_lt : efIdxPtr + c1 < heap)
    (hH_w : hdlPtr + (ec * k + j) < 2 ^ w) (hH_lt : hdlPtr + (ec * k + j) < heap)
    (hWin_w : hWin + lsfHdrSize < 2 ^ w) (hWin_lt : hWin + lsfHdrSize ≤ heap)
    (hnum_w : numB + e * L_w < 2 ^ w) (hden_w : denB + e * L_w < 2 ^ w)
    (h_crP : mem (b + compOffIsCrossPtr) = crPtr) (h_crV : mem (crPtr + e) = crV)
    (h_insP : mem (b + compOffIsInsPtr) = insPtr) (h_insV : mem (insPtr + e) = 0)
    (h_eC1P : mem (b + compOffEdgeC1Ptr) = eC1Ptr) (h_c1 : mem (eC1Ptr + e) = c1)
    (h_efP : mem (b + compOffEdgefulIdxPtr) = efIdxPtr) (h_ec : mem (efIdxPtr + c1) = ec)
    (h_k : mem (b + compOffK) = k) (h_hdlP : mem (b + compOffHandlesPtr) = hdlPtr)
    (h_hWin : mem (hdlPtr + (ec * k + j)) = hWin) (h_Lw : mem (b + compOffLW) = L_w)
    (h_numB : mem (hWin + lsfOffWstrNumPtr) = numB) (h_denB : mem (hWin + lsfOffWstrDenPtr) = denB) :
    ∃ st' c, Runs w p ω compEdgeInfoProc (startState [b, j, e, heap] mem pos) (.returned (heap + 4)) st' c ∧
      st'.mem heap = crV ∧ st'.mem (heap + 1) = 0 ∧
      st'.mem (heap + 2) = numB + e * L_w ∧ st'.mem (heap + 3) = denB + e * L_w ∧
      (∀ a, a < heap ∨ heap + 4 ≤ a → st'.mem a = mem a) ∧ c ≤ 180 := by
  let st0 := startState [b, j, e, heap] mem pos
  let s1 : State := { st0 with regs := Function.update st0.regs 4 crPtr }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 crV }
  let s3 : State := { s2 with regs := Function.update s2.regs 6 insPtr }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 0 }
  let m1 := Function.update mem heap crV
  let m2 := Function.update m1 (heap + 1) 0
  let s5 : State := { s4 with mem := m1 }
  let s6 : State := { s5 with mem := m2 }
  have hm2_lt : ∀ a < heap, m2 a = mem a := fun a ha => by
    dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  let r8 := Function.update s6.regs 8 eC1Ptr
  let r9 := Function.update r8 9 c1
  let r10 := Function.update r9 10 efIdxPtr
  let r11 := Function.update r10 11 ec
  let r12 := Function.update r11 12 k
  let r13 := Function.update r12 13 hdlPtr
  let r14 := Function.update r13 14 hWin
  let r15 := Function.update r14 15 L_w
  let r16 := Function.update r15 16 numB
  let r17 := Function.update r16 17 denB
  let t8 : State := { s6 with regs := r8 }
  let t9 : State := { s6 with regs := r9 }
  let t10 : State := { s6 with regs := r10 }
  let t11 : State := { s6 with regs := r11 }
  let t12 : State := { s6 with regs := r12 }
  let t13 : State := { s6 with regs := r13 }
  let t14 : State := { s6 with regs := r14 }
  let t15 : State := { s6 with regs := r15 }
  let t16 : State := { s6 with regs := r16 }
  let t17 : State := { s6 with regs := r17 }
  let m3 := Function.update m2 (heap + 2) (numB + e * L_w)
  let m4 := Function.update m3 (heap + 3) (denB + e * L_w)
  let t18 : State := { t17 with mem := m3 }
  let t19 : State := { t18 with mem := m4 }
  have hld : ∀ (r off val : ℕ) (s : State), off < compHdrSize → s.regs 0 = b → s.mem (b + off) = val →
      Runs w p ω (.assign r (.load (.bin .add (.reg 0) (.const off)))) s .normal
        { s with regs := Function.update s.regs r val } 5 := fun r off val s hoff hr0 hm =>
    runs_assign_iff.mpr ⟨val, Expr.eval_load_of_eq (x := b + off) (by
      simp [Expr.eval, BinOp.eval, hr0, show off < 2 ^ w by omega, show b + off < 2 ^ w by omega]) hm,
      rfl, rfl, by simp [Expr.size]⟩
  have hldW : ∀ (r off val : ℕ) (s : State), off < lsfHdrSize → s.regs 14 = hWin → s.mem (hWin + off) = val →
      Runs w p ω (.assign r (.load (.bin .add (.reg 14) (.const off)))) s .normal
        { s with regs := Function.update s.regs r val } 5 := fun r off val s hoff hr14 hm =>
    runs_assign_iff.mpr ⟨val, Expr.eval_load_of_eq (x := hWin + off) (by
      simp [Expr.eval, BinOp.eval, hr14, show off < 2 ^ w by omega, show hWin + off < 2 ^ w by omega]) hm,
      rfl, rfl, by simp [Expr.size]⟩
  have h1 := hld 4 compOffIsCrossPtr crPtr st0 (by decide) (by simp [st0, startState]) h_crP
  have h2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.reg 2)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨crV, Expr.eval_load_of_eq (by
      simp [s1, st0, startState, Expr.eval, BinOp.eval, hcr_w]) h_crV, rfl, rfl, by simp [Expr.size]⟩
  have h3 := hld 6 compOffIsInsPtr insPtr s2 (by decide) (by simp [s2, s1, st0, startState]) h_insP
  have h4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 6) (.reg 2)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (by
      simp [s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, hins_w]) h_insV, rfl, rfl, by simp [Expr.size]⟩
  have h5 : Runs w p ω (.store (.reg 3) (.reg 5)) s4 .normal s5 3 :=
    runs_store_iff.mpr ⟨heap, crV, by simp [s4, s3, s2, s1, st0, startState, Expr.eval],
      by simp [s4, s3, s2, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have h6 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 7)) s5 .normal s6 5 :=
    runs_store_iff.mpr ⟨heap + 1, 0, by
      simp [s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega],
      by simp [s5, s4, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have ha8 := hld 8 compOffEdgeC1Ptr eC1Ptr s6 (by decide) (by simp [s6, s5, s4, s3, s2, s1, st0, startState])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) b) hb_heap)).trans h_eC1P)
  have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 8) (.reg 2)))) t8 .normal t9 5 :=
    runs_assign_iff.mpr ⟨c1, Expr.eval_load_of_eq (by
      simp [t8, r8, s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval, heC1_w])
      ((hm2_lt _ heC1_lt).trans h_c1), rfl, rfl, by simp [Expr.size]⟩
  have ha10 := hld 10 compOffEdgefulIdxPtr efIdxPtr t9 (by decide) (by simp [t9, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) b) hb_heap)).trans h_efP)
  have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.reg 9)))) t10 .normal t11 5 :=
    runs_assign_iff.mpr ⟨ec, Expr.eval_load_of_eq (by
      simp [t10, r10, r9, r8, Expr.eval, BinOp.eval, hef_w]) ((hm2_lt _ hef_lt).trans h_ec), rfl, rfl, by simp [Expr.size]⟩
  have ha12 := hld 12 compOffK k t11 (by decide) (by simp [t11, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) b) hb_heap)).trans h_k)
  have ha13 := hld 13 compOffHandlesPtr hdlPtr t12 (by decide) (by simp [t12, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) b) hb_heap)).trans h_hdlP)
  have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 13) (.bin .add (.bin .mul (.reg 11) (.reg 12)) (.reg 1))))) t13 .normal t14 9 :=
    runs_assign_iff.mpr ⟨hWin, Expr.eval_load_of_eq (by
      simp [t13, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState, Expr.eval, BinOp.eval,
        show ec * k < 2 ^ w by omega, show ec * k + j < 2 ^ w by omega, hH_w])
      ((hm2_lt _ hH_lt).trans h_hWin), rfl, rfl, by simp [Expr.size]⟩
  have ha15 := hld 15 compOffLW L_w t14 (by decide) (by simp [t14, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) b) hb_heap)).trans h_Lw)
  have ha16 := hldW 16 lsfOffWstrNumPtr numB t15 (by decide) (by simp [t15, r15, r14])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) hWin) hWin_lt)).trans h_numB)
  have ha17 := hldW 17 lsfOffWstrDenPtr denB t16 (by decide) (by simp [t16, r16, r15, r14])
    ((hm2_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) hWin) hWin_lt)).trans h_denB)
  have hs18 : Runs w p ω (.store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 16) (.bin .mul (.reg 2) (.reg 15)))) t17 .normal t18 9 :=
    runs_store_iff.mpr ⟨heap + 2, numB + e * L_w, by
      simp [t17, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState,
        Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show heap + 2 < 2 ^ w by omega],
      by simp [t17, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState,
        Expr.eval, BinOp.eval, show e * L_w < 2 ^ w by omega, hnum_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hs19 : Runs w p ω (.store (.bin .add (.reg 3) (.const 3)) (.bin .add (.reg 17) (.bin .mul (.reg 2) (.reg 15)))) t18 .normal t19 9 :=
    runs_store_iff.mpr ⟨heap + 3, denB + e * L_w, by
      simp [t18, t17, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState,
        Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show heap + 3 < 2 ^ w by omega],
      by simp [t18, t17, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState,
        Expr.eval, BinOp.eval, show e * L_w < 2 ^ w by omega, hden_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.const 4))) t19 (.returned (heap + 4)) t19 4 :=
    runs_ret_iff.mpr ⟨heap + 4, by
      simp [t19, t18, t17, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, s6, s5, s4, s3, s2, s1, st0, startState,
        Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, hheap_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hbr : Runs w p ω _ s6 (.returned (heap + 4)) t19 88 :=
    runs_seq_iff.mpr (Or.inr ⟨t8, 5, _, ha8,
    runs_seq_iff.mpr (Or.inr ⟨t9, 5, _, ha9,
    runs_seq_iff.mpr (Or.inr ⟨t10, 5, _, ha10,
    runs_seq_iff.mpr (Or.inr ⟨t11, 5, _, ha11,
    runs_seq_iff.mpr (Or.inr ⟨t12, 5, _, ha12,
    runs_seq_iff.mpr (Or.inr ⟨t13, 5, _, ha13,
    runs_seq_iff.mpr (Or.inr ⟨t14, 9, _, ha14,
    runs_seq_iff.mpr (Or.inr ⟨t15, 5, _, ha15,
    runs_seq_iff.mpr (Or.inr ⟨t16, 5, _, ha16,
    runs_seq_iff.mpr (Or.inr ⟨t17, 5, _, ha17,
    runs_seq_iff.mpr (Or.inr ⟨t18, 9, _, hs18,
    runs_seq_iff.mpr (Or.inr ⟨t19, 9, 4, hs19, hret, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hfull : Runs w p ω compEdgeInfoProc st0 (.returned (heap + 4)) t19 124 := by
    unfold compEdgeInfoProc
    exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 118, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 112, h2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, 106, h3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, 100, h4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 3, 96, h5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, 90, h6,
        runs_cond_iff.mpr ⟨0, 88, by simp [s6, s5, s4, Expr.eval], by simpa using hbr, by simp [Expr.size]⟩,
        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hfr : ∀ a, a < heap ∨ heap + 4 ≤ a → t19.mem a = mem a := fun a ha => by
    dsimp only [t19, t18, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨t19, 124, hfull, ?_, ?_, ?_, ?_, hfr, by omega⟩ <;>
    dsimp only [t19, t18, m4, m3, m2, m1] <;>
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])

/-- Verification of `op 4` (`compEdgeInfoProc`). -/
theorem compLSFDS_op4 {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {p : Program}
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 4 S args mem)
    (_hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 4 S args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω compEdgeInfoProc (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 4 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 4 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 4 S args mem + compPhi b x mem := by
  rcases hpre with ⟨hk, b', j_idx, e, heap, rfl, hw16, hj_lt, heG⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  simp only [compLSFDS, List.getD_cons_zero, List.getD_cons_succ] at hsp ⊢
  have hheap_eq : heapArg [b, j_idx, e, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hend : x.endAddr ≤ heap := compEndAddr_le_heap hrep hdisj
  have hrep_all := hrep
  rcases hrep with ⟨hk', hxh, _, _, hxLw, hx2h, _, hnc, hne, hTE, hhdr, hBr, _, hTrack,
    hCompInfo, _, _, hEdgeC, hFlags, _, _, hOne, hWins, _⟩
  rcases hhdr with ⟨_, _, hh_k, hh_Lw, _, _, _, _, _, _, _, hh_efIdx, _, _, hh_eC1, _, hh_cr, hh_ins,
    _, _, hh_one, hh_hdl, _, _⟩
  obtain ⟨ℓ₀, hBr'⟩ := hBr
  let jF : Fin k := ⟨j_idx, hj_lt⟩
  have ⟨hInv_j, hG0_j, hG_j, _, hCr_j, hIns_j, hCG_j⟩ := hBr' jF
  have helt : e < x.eCap := hTrack.hElt e heG
  obtain ⟨hcr_m, hins_m⟩ := hFlags e helt
  set crV := if e ∈ (S ⟨0, hk⟩).crossEdges then 1 else 0
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_heap : b + compHdrSize ≤ heap := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hb_w : b + compHdrSize < 2 ^ w := by omega
  have hcr_w : compIsCrossBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
      compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
      compGhostSize, compHdrSize] at hStat ⊢; omega
  have hins_w : compIsInsBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
      compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
      compGhostSize, compHdrSize] at hStat ⊢; omega
  by_cases heIns0 : e ∈ (S ⟨0, hk⟩).insertedGlobal
  · have hins1 : mem (compIsInsBase b x.vCap x.eCap + e) = 1 := by simpa [heIns0] using hins_m
    have heIns_j : e ∈ (S jF).insertedGlobal := hIns_j.symm ▸ heIns0
    have hwstr1 : (S jF).wstrGlobal e = 1 := (hInv_j.hIns_wstr_R e heIns_j).1
    set onePtr := compOneLimbBase b x.vCap x.eCap
    have hone_end : onePtr + x.L_w ≤ x.endAddr := by
      have := compOneLimb_end_eq b x.vCap x.eCap x.L_w
      dsimp only [onePtr, compHandlesBase] at this ⊢; omega
    obtain ⟨st', c_run, hrun, h0, h1, h2, h3, hfr, hc⟩ :=
      compEdgeInfo_exec_ins hw16 hb_w hb_heap hsp hcr_w hins_w hh_cr hcr_m hh_ins hins1 hh_one
    have ⟨hV1, hI1⟩ := compOneLimb_valid_and_intVal W.hh hxLw (hxh ▸ hx2h)
      ((hfr onePtr (Or.inl (by omega))).trans hOne.1)
      (fun i hi1 hi2 => (hfr (onePtr + i) (Or.inl (by omega))).trans (hOne.2 i hi1 hi2))
    obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
    refine ⟨.returned (heap + 4), st', c_run, hrun, S, x, hrep', ?_, hresp, by omega⟩
    refine ⟨rfl, hj_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0]; simp [crV, show (S ⟨j_idx, hj_lt⟩).crossEdges = (S ⟨0, hk⟩).crossEdges from hCr_j]
    · rw [h1]; exact (ite_eq_left heIns_j).symm
    · rw [h2, hh_Lw]; exact hV1
    · rw [h3, hh_Lw]; exact hV1
    · rw [h2, hh_Lw, hI1]
    · rw [h3, hh_Lw, hI1]
    · rw [h2, h3, hh_Lw, hI1, hwstr1]; norm_num
  · have hins0 : mem (compIsInsBase b x.vCap x.eCap + e) = 0 := by simpa [heIns0] using hins_m
    have hni_j : e ∉ (S jF).insertedGlobal := fun h => heIns0 (hIns_j ▸ h)
    obtain ⟨c1, c2, hc1, hc2, _, _, hmemE, hcr_iff, _⟩ := hTrack.hEdge e heG
    have hncr0 : e ∉ (S ⟨0, hk⟩).crossEdges := fun hcr => heIns0 ((hBr' ⟨0, hk⟩).1.hCross_sub hcr)
    have hc12 : c1 = c2 := by_contra fun hne => hncr0 (hcr_iff.mpr hne)
    have heC1_0 : e ∈ ((S ⟨0, hk⟩).compSt (x.compOf c1)).G.E := (hmemE c1).mpr ⟨hc12, rfl⟩
    have hC1_mem_j : x.compOf c1 ∈ components (S jF).G₀ := hG0_j.symm ▸ hTrack.compOf_mem c1
    have heC1_j : e ∈ ((S jF).compSt (x.compOf c1)).G.E := (hCG_j c1).symm ▸ heC1_0
    have hm_ge1 : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c1)).m := by
      obtain ⟨C', hC', hm', heC', _, _⟩ := nonIns_mem_edgeful (hBr' ⟨0, hk⟩).1 heG heIns0
      obtain ⟨c', rfl⟩ := (hTrack.hBij.2 C').mp hC'
      have hc'eq : c' = c1 := ((hmemE c').mp heC').2
      exact hc'eq ▸ hm'
    obtain ⟨ec, _, hec_m, hec_eq⟩ := (hCompInfo c1).2.2.2 hm_ge1
    obtain ⟨hWin_m, hWin_rep, _, heWin, hLwWin, hWin_ge, hWin_le⟩ := hWins ec jF
    set hWin := x.winHandle ec jF
    set xWin := x.winConc ec jF
    rw [hec_eq] at hWin_rep
    have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hWin_wstr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hWin_h := hWin_rep.1
    set numBase := lsfWstrNumPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
    set denBase := lsfWstrDenPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
    have hwstr_sub := lsfWstr_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
    have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
    dsimp only [LSFConcrete.endAddr] at hWin_le
    have hwstr_eq : (S jF).wstrGlobal e = ((S jF).compSt (x.compOf c1)).wstr e := by
      obtain ⟨C', hC', heC', _, hw⟩ := hInv_j.hWstr_surv e (hG_j.symm ▸ heG) hni_j
      obtain ⟨c', rfl⟩ := (hTrack.hBij.2 C').mp (hG0_j ▸ hC')
      have hc'eq : c' = c1 := ((hmemE c').mp ((hCG_j c') ▸ heC')).2
      exact hc'eq ▸ hw
    have hidx_lt : ec.1 * k + j_idx < x.m0Total * k := by
      calc ec.1 * k + j_idx < ec.1 * k + k := Nat.add_lt_add_left hj_lt _
        _ = (ec.1 + 1) * k := by ring
        _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
    have heLw_lt : e * x.L_w + x.L_w ≤ x.eCap * x.L_w := by
      have : (e + 1) * x.L_w ≤ x.eCap * x.L_w := Nat.mul_le_mul_right _ helt
      linarith
    have hnum_end : numBase + e * x.L_w + x.L_w ≤ x.endAddr := by
      have h1 : e * x.L_w + x.L_w ≤ xWin.eCap * xWin.L_w := by rw [heWin, hLwWin]; exact heLw_lt
      omega
    have hden_end : denBase + e * x.L_w + x.L_w ≤ x.endAddr := by
      have h1 : e * x.L_w + x.L_w ≤ xWin.eCap * xWin.L_w := by rw [heWin, hLwWin]; exact heLw_lt
      omega
    have hec1_lt : compEdgeC1Base b x.vCap + e < heap := by
      dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
        compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
    have hefi_lt : compEdgefulIdxBase b x.vCap + c1.1 < heap := by
      have := lt_of_lt_of_le c1.2 hnc
      dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
        compGhostSize, compHdrSize] at hStat ⊢; omega
    have hH_lt : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j_idx) < heap := by
      dsimp only [compTablesEnd] at hTE; omega
    obtain ⟨st', c_run, hrun, h0, h1, h2, h3, hfr, hc⟩ :=
      compEdgeInfo_exec_nonins hw16 hb_w hb_heap hsp hcr_w hins_w (by omega) hec1_lt
        (by omega) hefi_lt (by omega) hH_lt (by omega) (by omega) (by omega) (by omega)
        hh_cr hcr_m hh_ins hins0 hh_eC1 ((hEdgeC e heG).1.trans hc1) hh_efIdx hec_m
        hh_k hh_hdl hWin_m hh_Lw hWin_hdr.2.2.2.2.2.2.2.2.2.1 hWin_hdr.2.2.2.2.2.2.2.2.2.2.1
    have hWstr_m' := hWin_wstr.of_agree
      (fun a ha1 ha2 => hfr a (Or.inl (by omega)))
      (fun a ha1 ha2 => hfr a (Or.inl (by omega)))
    obtain ⟨_, hVN, hVD, hIN, hID, hVal⟩ := hWstr_m'.2.2 e heC1_j
    rw [hWin_h, hLwWin] at hVN hVD hIN hID hVal
    obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
    refine ⟨.returned (heap + 4), st', c_run, hrun, S, x, hrep', ?_, hresp, by omega⟩
    refine ⟨rfl, hj_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0]; simp [crV, show (S ⟨j_idx, hj_lt⟩).crossEdges = (S ⟨0, hk⟩).crossEdges from hCr_j]
    · rw [h1]; exact (ite_eq_right hni_j).symm
    · rw [h2, hh_Lw]; exact hVN
    · rw [h3, hh_Lw]; exact hVD
    · rw [h2, hh_Lw]; exact hIN
    · rw [h3, hh_Lw]; exact hID
    · rw [h2, h3, hh_Lw, hwstr_eq]; exact hVal

/-- Verification of `op 5` (`compInfoProc`). -/
theorem compLSFDS_op5 {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {p : Program}
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 5 S args mem)
    (_hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 5 S args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω compInfoProc (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 5 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 5 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 5 S args mem + compPhi b x mem := by
  rcases hpre with ⟨b', heap, rfl, hw16, _hk_w⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  simp only [compLSFDS, List.getD_cons_zero] at hsp ⊢
  have hheap_eq : heapArg [b, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hend : x.endAddr ≤ heap := compEndAddr_le_heap hrep hdisj
  have hrep_all := hrep
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, hTE, hhdr, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases hhdr with ⟨hh_vCap, hh_eCap, hh_k, hh_Lw, _, _, _, hh_nC, hh_nE, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_heap : b + compHdrSize ≤ heap := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  obtain ⟨st', c_run, hrun, h0, h1, h2, h3, h4, h5, hfr, hc⟩ :=
    compInfo_exec hw16 (by omega) hb_heap hsp hh_nC hh_nE hh_k hh_vCap hh_eCap hh_Lw
  obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
  refine ⟨.returned (heap + 6), st', c_run, hrun, S, x, hrep', ?_, hresp, by omega⟩
  exact ⟨rfl, h0.trans hh_nC.symm, h1.trans hh_nE.symm, h2,
    h3.trans hh_vCap.symm, h4.trans hh_eCap.symm, h5.trans hh_Lw.symm⟩

end

end MinCostFlow.SparseCore.Program
