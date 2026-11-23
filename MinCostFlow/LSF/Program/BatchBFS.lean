module

public import MinCostFlow.LSF.Program.BatchBFSSteps
import Mathlib.Tactic.Linarith

/-!
# Lock-Step Dual-BFS Component Split Verification (`BatchBFS`)

Completes `clearBothVis_triple`, `bfsPostLoop_runs`, and the top-level contract theorem
`splitCompBFS_meetsContract` (`O(|E_{C_small}| + 1)` time).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Clears both `visA` and `visB` arrays and returns `0`, preserving memory outside
`[visA, visB + vCap)`, in cost `≤ 25 * (qA.length + qB.length) + 25`. -/
private lemma clearBothVis_triple {w qBufA qBufB visA visB vCap : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {qA qB : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hqA_qB : qBufA + vCap = qBufB) (hqB_vA : qBufB + vCap = visA) (hvA_vB : visA + vCap = visB)
    (hvB_ltw : visB + vCap < 2 ^ w)
    (hqA_nd : qA.Nodup) (hqA_le : qA.length ≤ vCap) (hqA_lt : ∀ v ∈ qA, v < vCap)
    (hqB_nd : qB.Nodup) (hqB_le : qB.length ≤ vCap) (hqB_lt : ∀ v ∈ qB, v < vCap)
    (hSA : SideMemAt mem0 qBufA visA vCap qA) (hSB : SideMemAt mem0 qBufB visB vCap qB) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs 18 = qBufA ∧ st.regs 19 = qBufB ∧
        st.regs 20 = visA ∧ st.regs 21 = visB ∧
        st.regs 23 = qA.length ∧ st.regs 26 = qB.length)
      (clearVisStmt 18 20 23 ;; clearVisStmt 19 21 26 ;; .ret (.const 0))
      (fun o st' => o = .returned 0 ∧
        (∀ a, ¬ (visA ≤ a ∧ a < visB + vCap) → st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (visA + v) = 0 ∧ st'.mem (visB + v) = 0))
      (fun _ => 25 * (qA.length + qB.length) + 25) := by
  intro st ω ⟨hm, h18, h19, h20, h21, h23, h26⟩
  suffices h : ∃ o st' c,
      Runs w p ω (clearVisStmt 18 20 23 ;; clearVisStmt 19 21 26 ;; .ret (.const 0)) st o st' c ∧
      (o = .returned 0 ∧
        (∀ a, ¬ (visA ≤ a ∧ a < visB + vCap) → st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (visA + v) = 0 ∧ st'.mem (visB + v) = 0)) ∧
      0 + c ≤ 25 * (qA.length + qB.length) + 25 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  have hclrA := clearVis_triple (w := w) (p := p) (qBuf := qBufA) (vis := visA) (vCap := vCap)
    (rQBuf := 18) (rVis := 20) (rQTail := 23) (mem0 := mem0) (regs_in := st.regs) (q := qA)
    hw16 (by decide) (by omega) (by omega) (Or.inl (by omega)) hqA_nd hqA_le hqA_lt hSA
  refine runs_seq_triple_le hclrA ⟨hm, rfl, h18, h20, h23⟩ ?_
  rintro st₁ ⟨hfr1, hvisA1, hreg1⟩
  have hSB1 : SideMemAt st₁.mem qBufB visB vCap qB :=
    hSB.of_agree (fun i hi => hfr1 _ (by omega)) (fun v hv => hfr1 _ (by omega)) hqB_le
  have hclrB := clearVis_triple (w := w) (p := p) (qBuf := qBufB) (vis := visB) (vCap := vCap)
    (rQBuf := 19) (rVis := 21) (rQTail := 26) (mem0 := st₁.mem) (regs_in := st₁.regs) (q := qB)
    hw16 (by decide) (by omega) (by omega) (Or.inl (by omega)) hqB_nd hqB_le hqB_lt hSB1
  refine runs_seq_triple_le hclrB
    ⟨rfl, rfl, (hreg1 19 (by decide)).trans h19, (hreg1 21 (by decide)).trans h21,
      (hreg1 26 (by decide)).trans h26⟩ ?_
  rintro st₂ ⟨hfr2, hvisB2, _⟩
  refine runs_ret_le (v := 0) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
  exact ⟨rfl, fun a ha => (hfr2 a (by omega)).trans (hfr1 a (by omega)),
    fun v hv => ⟨(hfr2 _ (by omega)).trans (hvisA1 v hv), hvisB2 v hv⟩⟩

open Classical in
/-- Post-loop stage of `splitCompBFSProc`: loads `fAnc` array pointers, runs `finishSideStmt` on
whichever side finished first, clears both `visA` and `visB`, and returns `0`. -/
private lemma bfsPostLoop_runs
    {w dgFPtr fAncPtr auxPtr vCap eCapF n0 uA uB oldCid root1 root2 newSum k qHA qHB : ℕ}
    {p : Program} {mem : ℕ → ℕ} {F : MGraph} {incL : ℕ → List ℕ}
    {qA remA qB remB : List ℕ} {st₁ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hf_ltw : fAncPtr + fAncSize vCap < 2 ^ w)
    (hf_hdr_lt_qA : fAncPtr + 6 ≤ auxQBufABase auxPtr vCap n0)
    (hcs_le_qA : fCompSizeBase fAncPtr vCap + vCap ≤ auxQBufABase auxPtr vCap n0)
    (hvB_ltw : auxVisBBase auxPtr vCap n0 + vCap < 2 ^ w)
    (h2e_v_ltw : 2 * eCapF + vCap < 2 ^ w)
    (hF : F.IsForest) (huA : uA ∈ F.V) (huB : uB ∈ F.V)
    (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V,
      mem (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem (dgIntToExtBase dgFPtr vCap + mem (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    (hcidPtr : mem (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap)
    (hcrootPtr : mem (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap)
    (hcsizePtr : mem (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap)
    (hvis0 : ∀ v < vCap, mem (auxVisABase auxPtr vCap n0 + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap n0 + v) = 0)
    (hold_lt : oldCid < vCap) (hr1_lt : root1 < vCap) (hr2_lt : root2 < vCap)
    (hold_ne_r2 : oldCid ≠ root2) (hnewSum_ltw : newSum < 2 ^ w)
    (hnewSum : newSum = (F.V.filter fun v => F.Connected v uA).card +
        (F.V.filter fun v => F.Connected v uB).card)
    (hfr1 : ∀ a, ¬ (auxQBufABase auxPtr vCap n0 ≤ a ∧ a < auxVisBBase auxPtr vCap n0 + vCap) →
      st₁.mem a = mem a)
    (hr1 : st₁.regs 1 = fAncPtr) (hr8 : st₁.regs 8 = oldCid) (hr9 : st₁.regs 9 = root1)
    (hr10 : st₁.regs 10 = root2) (hr11 : st₁.regs 11 = newSum)
    (hr18 : st₁.regs 18 = auxQBufABase auxPtr vCap n0)
    (hr19 : st₁.regs 19 = auxQBufBBase auxPtr vCap n0)
    (hr20 : st₁.regs 20 = auxVisABase auxPtr vCap n0)
    (hr21 : st₁.regs 21 = auxVisBBase auxPtr vCap n0)
    (hBA : BfsInv F (fun v => mem (dgExtToIntBase dgFPtr vCap + v)) incL uA qA qHA remA k)
    (hBB : BfsInv F (fun v => mem (dgExtToIntBase dgFPtr vCap + v)) incL uB qB qHB remB k)
    (hSA : SideMemAt st₁.mem (auxQBufABase auxPtr vCap n0) (auxVisABase auxPtr vCap n0) vCap qA)
    (hSB : SideMemAt st₁.mem (auxQBufBBase auxPtr vCap n0) (auxVisBBase auxPtr vCap n0) vCap qB)
    (hDA : DllTailAt st₁.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remA (st₁.regs 24))
    (hr22 : st₁.regs 22 = qHA) (hr23 : st₁.regs 23 = qA.length)
    (hr26 : st₁.regs 26 = qB.length)
    (hdone : (qHA = qA.length ∧ remA = []) ∨ (qHB = qB.length ∧ remB = [])) :
    ∃ o st' c,
      Runs w p ω
        (.assign 29 (.load (.bin .add (.reg 1) (.const fOffCompIdPtr))) ;;
         .assign 30 (.load (.bin .add (.reg 1) (.const fOffCompRootPtr))) ;;
         .assign 31 (.load (.bin .add (.reg 1) (.const fOffCompSizePtr))) ;;
         .cond (.bin .add (.reg 24) (.bin .sub (.reg 23) (.reg 22)))
           (finishSideStmt 19 21 26)
           (finishSideStmt 18 20 23) ;;
         clearVisStmt 18 20 23 ;;
         clearVisStmt 19 21 26 ;;
         .ret (.const 0)) st₁ o st' c ∧
      (splitCompBFSContract w F).post
        [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum]
        mem o.value st'.mem ∧
      (0 + 140 + 1 +
        (152 * (3 * (min (F.E.filter fun e => F.Connected (F.tail e) uA).card
              (F.E.filter fun e => F.Connected (F.tail e) uB).card) + 2) + 2) + 1) + c ≤
        (splitCompBFSContract w F).cost
          [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum] mem := by
  set qBufA := auxQBufABase auxPtr vCap n0
  set qBufB := auxQBufBBase auxPtr vCap n0
  set visA := auxVisABase auxPtr vCap n0
  set visB := auxVisBBase auxPtr vCap n0
  set compIdBase := fCompIdBase fAncPtr vCap
  set compRootBase := fCompRootBase fAncPtr vCap
  set compSizeBase := fCompSizeBase fAncPtr vCap
  have hqA_qB : qBufA + vCap = qBufB := rfl
  have hqB_vA : qBufB + vCap = visA := rfl
  have hvA_vB : visA + vCap = visB := rfl
  have hcid_cr : compIdBase + vCap = compRootBase := rfl
  have hcr_cs : compRootBase + vCap = compSizeBase := rfl
  have hcs_le_qB : compSizeBase + vCap ≤ qBufB := by omega
  have hcs_le_vA : compSizeBase + vCap ≤ visA := by omega
  have hcs_le_vB : compSizeBase + vCap ≤ visB := by omega
  have hvA_ltw : visA + vCap < 2 ^ w := by omega
  have hqA_le_vA : qBufA + vCap ≤ visA := by omega
  have hqB_le_vB : qBufB + vCap ≤ visB := by omega
  have hf_hdr_lt : fAncPtr + 5 < 2 ^ w := by dsimp [fAncSize] at hf_ltw; omega
  have hqA_le : qA.length ≤ vCap :=
    list_len_le_vCap hvCap hBA.hq_nd (fun v hv => (hBA.hq_sub v hv).1)
  have hqB_le : qB.length ≤ vCap :=
    list_len_le_vCap hvCap hBB.hq_nd (fun v hv => (hBB.hq_sub v hv).1)
  have hqA_lt : ∀ v ∈ qA, v < vCap := fun v hv => hvCap v (hBA.hq_sub v hv).1
  have hqB_lt : ∀ v ∈ qB, v < vCap := fun v hv => hvCap v (hBB.hq_sub v hv).1
  have hchA_le : st₁.regs 24 ≤ 2 * eCapF := by
    cases remA with
    | nil => rw [hDA]; omega
    | cons a tl => obtain ⟨h1, h2, _⟩ := hDA; omega
  set CA := F.V.filter fun v => F.Connected v uA
  set CB := F.V.filter fun v => F.Connected v uB
  set EA := F.E.filter fun e => F.Connected (F.tail e) uA
  set EB := F.E.filter fun e => F.Connected (F.tail e) uB
  set mSmall := min EA.card EB.card
  have hCA_card : CA.card = EA.card + 1 := forest_comp_card_eq_edges_succ hF huA
  have hCB_card : CB.card = EB.card + 1 := forest_comp_card_eq_edges_succ hF huB
  have hcidPtr1 : st₁.mem (fAncPtr + fOffCompIdPtr) = compIdBase :=
    (hfr1 _ (fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) fAncPtr) hf_hdr_lt_qA) h.1)).trans hcidPtr
  have hcrootPtr1 : st₁.mem (fAncPtr + fOffCompRootPtr) = compRootBase :=
    (hfr1 _ (fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) fAncPtr) hf_hdr_lt_qA) h.1)).trans hcrootPtr
  have hcsizePtr1 : st₁.mem (fAncPtr + fOffCompSizePtr) = compSizeBase :=
    (hfr1 _ (fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) fAncPtr) hf_hdr_lt_qA) h.1)).trans hcsizePtr
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := compIdBase) (by dsimp only [fOffCompIdPtr]; eval_expr) hcidPtr1) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := compRootBase) (by dsimp only [fOffCompRootPtr]; eval_expr) hcrootPtr1) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := compSizeBase) (by dsimp only [fOffCompSizePtr]; eval_expr) hcsizePtr1) ?_; dsimp only
  have hcleanup : ∀ (st₂ : State) (Csmall Cbig : Finset ℕ),
      ((Csmall = CA ∧ Cbig = CB) ∨ (Csmall = CB ∧ Cbig = CA)) →
      Csmall.card ≤ Cbig.card →
      qA.length + qB.length ≤ 4 * mSmall + 3 →
      (∀ a, ¬ (compIdBase ≤ a ∧ a < compSizeBase + vCap) → st₂.mem a = st₁.mem a) →
      (∀ v < vCap, st₂.mem (compIdBase + v) = if v ∈ Csmall then root2 else mem (compIdBase + v)) →
      (∀ c < vCap, c ≠ oldCid → c ≠ root2 →
        st₂.mem (compRootBase + c) = mem (compRootBase + c) ∧
        st₂.mem (compSizeBase + c) = mem (compSizeBase + c)) →
      st₂.mem (compSizeBase + root2) = Csmall.card →
      st₂.mem (compSizeBase + oldCid) = Cbig.card →
      ((root2 ∈ Csmall ∧ st₂.mem (compRootBase + root2) = root2 ∧
          st₂.mem (compRootBase + oldCid) = root1) ∨
       (root2 ∉ Csmall ∧ st₂.mem (compRootBase + root2) = root1 ∧
          st₂.mem (compRootBase + oldCid) = root2)) →
      st₂.regs 18 = qBufA → st₂.regs 19 = qBufB → st₂.regs 20 = visA → st₂.regs 21 = visB →
      st₂.regs 23 = qA.length → st₂.regs 26 = qB.length →
      ∀ acc : ℕ, acc ≤ 482 * mSmall + 575 →
      ∃ o st' c,
        Runs w p ω (clearVisStmt 18 20 23 ;; clearVisStmt 19 21 26 ;; .ret (.const 0)) st₂ o st' c ∧
        (splitCompBFSContract w F).post
          [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum]
          mem o.value st'.mem ∧
        acc + c ≤ (splitCompBFSContract w F).cost
          [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum] mem := by
    intro st₂ Csmall Cbig hCpair hCle hqSum_bd hfr2 hcid2 hother2 hcsR2 hcsOld hroots2
      h18_2 h19_2 h20_2 h21_2 h23_2 h26_2 acc hacc
    have hSA2 : SideMemAt st₂.mem qBufA visA vCap qA :=
      hSA.of_agree
        (fun i _ => hfr2 _ (fun h => Nat.not_lt.mpr (Nat.le_trans hcs_le_qA (Nat.le_add_right qBufA i)) h.2))
        (fun v _ => hfr2 _ (fun h => Nat.not_lt.mpr (Nat.le_trans hcs_le_vA (Nat.le_add_right visA v)) h.2))
        hqA_le
    have hSB2 : SideMemAt st₂.mem qBufB visB vCap qB :=
      hSB.of_agree
        (fun i _ => hfr2 _ (fun h => Nat.not_lt.mpr (Nat.le_trans hcs_le_qB (Nat.le_add_right qBufB i)) h.2))
        (fun v _ => hfr2 _ (fun h => Nat.not_lt.mpr (Nat.le_trans hcs_le_vB (Nat.le_add_right visB v)) h.2))
        hqB_le
    obtain ⟨o, st₄, c, hrun, ⟨rfl, hfr4, hvis4⟩, hc⟩ :=
      clearBothVis_triple hw16 hqA_qB hqB_vA hvA_vB hvB_ltw
        hBA.hq_nd hqA_le hqA_lt hBB.hq_nd hqB_le hqB_lt hSA2 hSB2
        st₂ ω ⟨rfl, h18_2, h19_2, h20_2, h21_2, h23_2, h26_2⟩
    have hmem_fAnc : ∀ a, compIdBase ≤ a → a < compSizeBase + vCap → st₄.mem a = st₂.mem a :=
      fun a _ ha2 => hfr4 a (fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le ha2 hcs_le_vA) h.1)
    have hmem_frame : ∀ a, ¬ (compIdBase ≤ a ∧ a < compSizeBase + vCap) →
        ¬ (qBufA ≤ a ∧ a < qBufB + vCap) → st₄.mem a = mem a := by
      intro a haF haQ
      by_cases haVA : visA ≤ a ∧ a < visA + vCap
      · have hidx : a = visA + (a - visA) := (Nat.add_sub_of_le haVA.1).symm
        have hlt : a - visA < vCap := Nat.sub_lt_left_of_lt_add haVA.1 (Nat.add_comm visA vCap ▸ haVA.2)
        rw [hidx, (hvis4 _ hlt).1, (hvis0 _ hlt).1]
      · by_cases haVB : visB ≤ a ∧ a < visB + vCap
        · have hidx : a = visB + (a - visB) := (Nat.add_sub_of_le haVB.1).symm
          have hlt : a - visB < vCap := Nat.sub_lt_left_of_lt_add haVB.1 (Nat.add_comm visB vCap ▸ haVB.2)
          rw [hidx, (hvis4 _ hlt).2, (hvis0 _ hlt).2]
        · have hnotVis : ¬ (visA ≤ a ∧ a < visB + vCap) := by
            rintro ⟨h1, h2⟩
            by_cases hlt : a < visA + vCap
            · exact haVA ⟨h1, hlt⟩
            · exact haVB ⟨hvA_vB ▸ Nat.not_lt.mp hlt, h2⟩
          have hnotAll : ¬ (qBufA ≤ a ∧ a < visB + vCap) := by
            rintro ⟨h1, h2⟩
            by_cases hlt : a < qBufB + vCap
            · exact haQ ⟨h1, hlt⟩
            · exact hnotVis ⟨hqB_vA ▸ Nat.not_lt.mp hlt, h2⟩
          rw [hfr4 a hnotVis, hfr2 a haF, hfr1 a hnotAll]
    have hcid_in : ∀ v < vCap, compIdBase ≤ compIdBase + v ∧ compIdBase + v < compSizeBase + vCap :=
      fun v hv => ⟨Nat.le_add_right _ _, by
        have h1 : compIdBase + v < compIdBase + vCap := Nat.add_lt_add_left hv _
        have h2 : compIdBase + vCap ≤ compSizeBase + vCap := by
          rw [hcid_cr, ← hcr_cs]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
        exact Nat.lt_of_lt_of_le h1 h2⟩
    have hcr_in : ∀ c < vCap, compIdBase ≤ compRootBase + c ∧ compRootBase + c < compSizeBase + vCap :=
      fun c hc => ⟨by rw [← hcid_cr]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _),
        by have h1 : compRootBase + c < compRootBase + vCap := Nat.add_lt_add_left hc _
           rw [hcr_cs] at h1; exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)⟩
    have hcs_in : ∀ c < vCap, compIdBase ≤ compSizeBase + c ∧ compSizeBase + c < compSizeBase + vCap :=
      fun c hc => ⟨by
          rw [← hcr_cs, ← hcid_cr]
          exact Nat.le_trans (Nat.le_add_right _ _)
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)),
        Nat.add_lt_add_left hc _⟩
    refine ⟨.returned 0, st₄, c, hrun, ?_, ?_⟩
    · refine ⟨dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum,
        rfl, rfl, hmem_frame, Csmall, Cbig, hCpair, hCle,
        fun v hv => (hmem_fAnc _ (hcid_in v hv).1 (hcid_in v hv).2).trans (hcid2 v hv),
        fun c hc hne1 hne2 =>
          ⟨(hmem_fAnc _ (hcr_in c hc).1 (hcr_in c hc).2).trans (hother2 c hc hne1 hne2).1,
           (hmem_fAnc _ (hcs_in c hc).1 (hcs_in c hc).2).trans (hother2 c hc hne1 hne2).2⟩,
        (hmem_fAnc _ (hcs_in root2 hr2_lt).1 (hcs_in root2 hr2_lt).2).trans hcsR2,
        (hmem_fAnc _ (hcs_in oldCid hold_lt).1 (hcs_in oldCid hold_lt).2).trans hcsOld, ?_⟩
      rcases hroots2 with ⟨hr2in, h1, h2⟩ | ⟨hr2out, h1, h2⟩
      · exact Or.inl ⟨hr2in,
          (hmem_fAnc _ (hcr_in root2 hr2_lt).1 (hcr_in root2 hr2_lt).2).trans h1,
          (hmem_fAnc _ (hcr_in oldCid hold_lt).1 (hcr_in oldCid hold_lt).2).trans h2⟩
      · exact Or.inr ⟨hr2out,
          (hmem_fAnc _ (hcr_in root2 hr2_lt).1 (hcr_in root2 hr2_lt).2).trans h1,
          (hmem_fAnc _ (hcr_in oldCid hold_lt).1 (hcr_in oldCid hold_lt).2).trans h2⟩
    · simp only [splitCompBFSContract, List.getD_cons_zero, List.getD_cons_succ]
      dsimp only at hc
      change acc + c ≤ 600 * mSmall + 700
      have h1 : c ≤ 25 * (4 * mSmall + 3) + 25 := le_trans hc (Nat.add_le_add_right (Nat.mul_le_mul_left 25 hqSum_bd) 25)
      exact Nat.le_trans (Nat.add_le_add hacc h1) (by
        have : 482 * mSmall + 575 + (25 * (4 * mSmall + 3) + 25) = 582 * mSmall + 675 := by ring
        rw [this]
        exact Nat.add_le_add (Nat.mul_le_mul_right mSmall (by decide)) (by decide))
  have hfAnc_mem1 : ∀ a < compSizeBase + vCap, st₁.mem a = mem a :=
    fun a ha => hfr1 a (fun h => Nat.not_le.mpr (Nat.lt_of_lt_of_le ha hcs_le_qA) h.1)
  have hcid_lt_cs : ∀ v < vCap, compIdBase + v < compSizeBase + vCap := fun v hv => by
    have h1 : compIdBase + v < compIdBase + vCap := Nat.add_lt_add_left hv _
    have h2 : compIdBase + vCap ≤ compSizeBase + vCap := by
      rw [hcid_cr, ← hcr_cs]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact Nat.lt_of_lt_of_le h1 h2
  have hcr_lt_cs : ∀ c < vCap, compRootBase + c < compSizeBase + vCap := fun c hc => by
    have h1 : compRootBase + c < compRootBase + vCap := Nat.add_lt_add_left hc _
    rw [hcr_cs] at h1; exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  have hupd3 : ∀ r, r ≠ 29 → r ≠ 30 → r ≠ 31 →
      Function.update (Function.update (Function.update st₁.regs 29 compIdBase) 30 compRootBase) 31 compSizeBase r = st₁.regs r :=
    fun r h29 h30 h31 => by rw [Function.update_of_ne h31, Function.update_of_ne h30, Function.update_of_ne h29]
  refine runs_seq_cond_le (v := st₁.regs 24 + (qA.length - qHA)) (by have := hBA.hqh_le; eval_expr) ?_ ?_
  · intro hA_ne
    have hA_notDone : ¬ (qHA = qA.length ∧ remA = []) := by
      rintro ⟨h1, h2⟩; subst h2; rw [hDA, h1] at hA_ne; omega
    have hB_done : qHB = qB.length ∧ remB = [] := hdone.resolve_left hA_notDone
    obtain ⟨hB_mem, hB_len, hk_eq⟩ :=
      hBB.done_eq hF huB hvCap heCap hExtToInt hincL hB_done.1 hB_done.2
    have hk_eq' : k = 3 * EB.card + 1 := hk_eq
    have hk_le_A : k ≤ 3 * EA.card + 1 := hBA.steps_le hF huA hvCap heCap hExtToInt hincL
    have hEB_le_EA : EB.card ≤ EA.card := by omega
    have hmSmall_eq : mSmall = EB.card := Nat.min_eq_right hEB_le_EA
    have hqB_eq : qB.length = CB.card := by rw [hB_len, hCB_card]
    have hqA_bd : qA.length ≤ 3 * mSmall + 2 := by have := hBA.hq_len_le; omega
    have hqSum_bd : qA.length + qB.length ≤ 4 * mSmall + 3 := by omega
    have hqB_iff : ∀ v, v ∈ qB ↔ v ∈ CB := fun v => by simp [CB, hB_mem]
    have hfinB := finishSide_triple (w := w) (p := p) (fAncPtr := fAncPtr) (qBuf := qBufB)
      (vis := visB) (vCap := vCap) (oldCid := oldCid) (root1 := root1) (root2 := root2)
      (newSum := newSum) (rQBuf := 19) (rVis := 21) (rQTail := 26)
      (mem0 := st₁.mem)
      (regs_in := Function.update (Function.update (Function.update st₁.regs 29 compIdBase) 30 compRootBase) 31 compSizeBase)
      (q := qB) hw16 (by decide) hcid_cr hcr_cs hcs_le_qB hqB_le_vB hvB_ltw
      hold_lt hr1_lt hr2_lt hold_ne_r2 hqB_le (by rw [hnewSum, hqB_eq]; exact Nat.le_add_left _ _) hnewSum_ltw hqB_lt hSB
    refine runs_seq_triple_le hfinB
      ⟨rfl, rfl,
        (hupd3 8 (by decide) (by decide) (by decide)).trans hr8,
        (hupd3 9 (by decide) (by decide) (by decide)).trans hr9,
        (hupd3 10 (by decide) (by decide) (by decide)).trans hr10,
        (hupd3 11 (by decide) (by decide) (by decide)).trans hr11,
        rfl, rfl, rfl,
        (hupd3 19 (by decide) (by decide) (by decide)).trans hr19,
        (hupd3 21 (by decide) (by decide) (by decide)).trans hr21,
        (hupd3 26 (by decide) (by decide) (by decide)).trans hr26⟩ ?_
    rintro st₂ ⟨hfr2, hcid2, hother2, hcsR2, hcsOld, hroots2, hreg2⟩
    exact hcleanup st₂ CB CA (Or.inr ⟨rfl, rfl⟩) (by rw [hCA_card, hCB_card]; exact Nat.add_le_add_right hEB_le_EA 1)
      hqSum_bd hfr2
      (fun v hv => by rw [hcid2 v hv, hfAnc_mem1 _ (hcid_lt_cs v hv)]; simp [hqB_iff])
      (fun c hc h1 h2 => ⟨(hother2 c hc h1 h2).1.trans (hfAnc_mem1 _ (hcr_lt_cs c hc)),
        (hother2 c hc h1 h2).2.trans (hfAnc_mem1 _ (Nat.add_lt_add_left hc _))⟩)
      (hcsR2.trans hqB_eq) (by rw [hcsOld, hnewSum, hqB_eq]; exact Nat.add_sub_cancel _ _)
      (by rcases hroots2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨(hqB_iff _).mp h1, h2, h3⟩
          · exact Or.inr ⟨fun h => h1 ((hqB_iff _).mpr h), h2, h3⟩)
      ((hreg2 18 (by decide)).trans ((hupd3 18 (by decide) (by decide) (by decide)).trans hr18))
      ((hreg2 19 (by decide)).trans ((hupd3 19 (by decide) (by decide) (by decide)).trans hr19))
      ((hreg2 20 (by decide)).trans ((hupd3 20 (by decide) (by decide) (by decide)).trans hr20))
      ((hreg2 21 (by decide)).trans ((hupd3 21 (by decide) (by decide) (by decide)).trans hr21))
      ((hreg2 23 (by decide)).trans ((hupd3 23 (by decide) (by decide) (by decide)).trans hr23))
      ((hreg2 26 (by decide)).trans ((hupd3 26 (by decide) (by decide) (by decide)).trans hr26)) _
      (by
        dsimp only [Expr.size]
        rw [hqB_eq, hCB_card, ← hmSmall_eq]
        calc _ = 481 * mSmall + 558 := by ring
          _ ≤ 482 * mSmall + 575 := Nat.add_le_add (Nat.mul_le_mul_right mSmall (by decide)) (by decide))
  · intro hA_0
    have hA_done : qHA = qA.length ∧ remA = [] := by
      have h1 : st₁.regs 24 = 0 := by omega
      have h2 : qHA = qA.length := by have := hBA.hqh_le; omega
      refine ⟨h2, ?_⟩
      cases remA with
      | nil => rfl
      | cons a tl => exfalso; exact Nat.succ_ne_zero a (hDA.1.symm.trans h1)
    obtain ⟨hA_mem, hA_len, hk_eq⟩ :=
      hBA.done_eq hF huA hvCap heCap hExtToInt hincL hA_done.1 hA_done.2
    have hk_eq' : k = 3 * EA.card + 1 := hk_eq
    have hk_le_B : k ≤ 3 * EB.card + 1 := hBB.steps_le hF huB hvCap heCap hExtToInt hincL
    have hEA_le_EB : EA.card ≤ EB.card := by omega
    have hmSmall_eq : mSmall = EA.card := Nat.min_eq_left hEA_le_EB
    have hqA_eq : qA.length = CA.card := by rw [hA_len, hCA_card]
    have hqB_bd : qB.length ≤ 3 * mSmall + 2 := by have := hBB.hq_len_le; omega
    have hqSum_bd : qA.length + qB.length ≤ 4 * mSmall + 3 := by omega
    have hqA_iff : ∀ v, v ∈ qA ↔ v ∈ CA := fun v => by simp [CA, hA_mem]
    have hfinA := finishSide_triple (w := w) (p := p) (fAncPtr := fAncPtr) (qBuf := qBufA)
      (vis := visA) (vCap := vCap) (oldCid := oldCid) (root1 := root1) (root2 := root2)
      (newSum := newSum) (rQBuf := 18) (rVis := 20) (rQTail := 23)
      (mem0 := st₁.mem)
      (regs_in := Function.update (Function.update (Function.update st₁.regs 29 compIdBase) 30 compRootBase) 31 compSizeBase)
      (q := qA) hw16 (by decide) hcid_cr hcr_cs hcs_le_qA hqA_le_vA hvA_ltw
      hold_lt hr1_lt hr2_lt hold_ne_r2 hqA_le (by rw [hnewSum, hqA_eq]; exact Nat.le_add_right _ _) hnewSum_ltw hqA_lt hSA
    refine runs_seq_triple_le hfinA
      ⟨rfl, rfl,
        (hupd3 8 (by decide) (by decide) (by decide)).trans hr8,
        (hupd3 9 (by decide) (by decide) (by decide)).trans hr9,
        (hupd3 10 (by decide) (by decide) (by decide)).trans hr10,
        (hupd3 11 (by decide) (by decide) (by decide)).trans hr11,
        rfl, rfl, rfl,
        (hupd3 18 (by decide) (by decide) (by decide)).trans hr18,
        (hupd3 20 (by decide) (by decide) (by decide)).trans hr20,
        (hupd3 23 (by decide) (by decide) (by decide)).trans hr23⟩ ?_
    rintro st₂ ⟨hfr2, hcid2, hother2, hcsR2, hcsOld, hroots2, hreg2⟩
    exact hcleanup st₂ CA CB (Or.inl ⟨rfl, rfl⟩) (by rw [hCA_card, hCB_card]; exact Nat.add_le_add_right hEA_le_EB 1)
      hqSum_bd hfr2
      (fun v hv => by rw [hcid2 v hv, hfAnc_mem1 _ (hcid_lt_cs v hv)]; simp [hqA_iff])
      (fun c hc h1 h2 => ⟨(hother2 c hc h1 h2).1.trans (hfAnc_mem1 _ (hcr_lt_cs c hc)),
        (hother2 c hc h1 h2).2.trans (hfAnc_mem1 _ (Nat.add_lt_add_left hc _))⟩)
      (hcsR2.trans hqA_eq) (by rw [hcsOld, hnewSum, hqA_eq]; exact Nat.add_sub_cancel_left _ _)
      (by rcases hroots2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨(hqA_iff _).mp h1, h2, h3⟩
          · exact Or.inr ⟨fun h => h1 ((hqA_iff _).mpr h), h2, h3⟩)
      ((hreg2 18 (by decide)).trans ((hupd3 18 (by decide) (by decide) (by decide)).trans hr18))
      ((hreg2 19 (by decide)).trans ((hupd3 19 (by decide) (by decide) (by decide)).trans hr19))
      ((hreg2 20 (by decide)).trans ((hupd3 20 (by decide) (by decide) (by decide)).trans hr20))
      ((hreg2 21 (by decide)).trans ((hupd3 21 (by decide) (by decide) (by decide)).trans hr21))
      ((hreg2 23 (by decide)).trans ((hupd3 23 (by decide) (by decide) (by decide)).trans hr23))
      ((hreg2 26 (by decide)).trans ((hupd3 26 (by decide) (by decide) (by decide)).trans hr26)) _
      (by
        dsimp only [Expr.size]
        rw [hqA_eq, hCA_card, ← hmSmall_eq]
        calc _ = 481 * mSmall + 558 := by ring
          _ ≤ 482 * mSmall + 575 := Nat.add_le_add (Nat.mul_le_mul_right mSmall (by decide)) (by decide))

/-! ## Main verification theorem -/

open Classical in
/-- `splitCompBFSProc` satisfies `splitCompBFSContract`. -/
theorem splitCompBFS_meetsContract {w : ℕ} {p : Program} {b : ℕ} {F : MGraph}
    (hp : p.procs[b]? = some splitCompBFSProc) :
    MeetsContract w p b (splitCompBFSContract w F) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum,
    rfl, hw16, hdg_le_f, hf_le_aux, haux_ltw, hF, hdgF, hcidPtr, hcrootPtr, hcsizePtr,
    hqAPtr, hqBPtr, hvAPtr, hvBPtr, hvis0, huA, huB, hnotConn, hold_lt, hr1_lt, hr2_lt,
    hold_ne_r2, hroots, hnewSum⟩
  -- Unpack `DynGraphAt mem dgFPtr vCap eCapF F`
  rcases hdgF with ⟨hFval, hvCap, heCap, _, _, _, _, _, _, hExtToInt, hIntToExt, _, _,
    hEndSlot, incL, hincL_raw⟩
  have hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hincL_raw s hs
    refine ⟨h1, h2, fun h => ?_⟩
    rw [h3 h]
    constructor
    · rintro ⟨hlt, heE, hslot⟩
      refine ⟨hlt, heE, ?_⟩
      obtain ⟨ht, hh⟩ := hEndSlot _ heE
      split_ifs at hslot ⊢
      · rwa [← ht]
      · rwa [← hh]
    · rintro ⟨hlt, heE, hslot⟩
      refine ⟨hlt, heE, ?_⟩
      obtain ⟨ht, hh⟩ := hEndSlot _ heE
      split_ifs at hslot ⊢
      · rwa [ht]
      · rwa [hh]
  -- Base addresses and layout bounds
  set extToInt := dgExtToIntBase dgFPtr vCap
  set intToExt := dgIntToExtBase dgFPtr vCap
  set incHead := dgIncHeadBase dgFPtr vCap
  set eTailSlot := dgETailSlotBase dgFPtr vCap eCapF
  set eHeadSlot := dgEHeadSlotBase dgFPtr vCap eCapF
  set heNext := dgHeNextBase dgFPtr vCap eCapF
  set qBufA := auxQBufABase auxPtr vCap n0
  set qBufB := auxQBufBBase auxPtr vCap n0
  set visA := auxVisABase auxPtr vCap n0
  set visB := auxVisBBase auxPtr vCap n0
  set compIdBase := fCompIdBase fAncPtr vCap
  set compRootBase := fCompRootBase fAncPtr vCap
  set compSizeBase := fCompSizeBase fAncPtr vCap
  have hqA_ge : auxPtr + auxHdrSize ≤ qBufA := by
    dsimp [qBufA, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase]; omega
  have hqA_qB : qBufA + vCap = qBufB := rfl
  have hqB_vA : qBufB + vCap = visA := rfl
  have hvA_vB : visA + vCap = visB := rfl
  have hvB_le : visB + vCap ≤ auxPtr + auxSize vCap n0 := by
    dsimp [visB, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
      auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
  have hcid_ge : fAncPtr + fAncHdrSize ≤ compIdBase := by
    dsimp [compIdBase, fCompIdBase, fRListBase, fIsRootBase]; omega
  have hcid_cr : compIdBase + vCap = compRootBase := rfl
  have hcr_cs : compRootBase + vCap = compSizeBase := rfl
  have hcs_le : compSizeBase + vCap = fAncPtr + fAncSize vCap := fAnc_end_eq fAncPtr vCap
  have hcs_le_qA : compSizeBase + vCap ≤ qBufA := by omega
  have hcs_le_qB : compSizeBase + vCap ≤ qBufB := by omega
  have hcs_le_vA : compSizeBase + vCap ≤ visA := by omega
  have hcs_le_vB : compSizeBase + vCap ≤ visB := by omega
  have hvB_ltw : visB + vCap < 2 ^ w := by omega
  have hvA_ltw : visA + vCap < 2 ^ w := by omega
  have hqA_le_vA : qBufA + vCap ≤ visA := by omega
  have hqB_le_vB : qBufB + vCap ≤ visB := by omega
  have hdg_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by omega
  have hf_ltw : fAncPtr + fAncSize vCap < 2 ^ w := by omega
  have huA_lt : uA < vCap := hvCap uA huA
  have huB_lt : uB < vCap := hvCap uB huB
  -- Component sizes and edge counts
  set CA := F.V.filter fun v => F.Connected v uA
  set CB := F.V.filter fun v => F.Connected v uB
  set EA := F.E.filter fun e => F.Connected (F.tail e) uA
  set EB := F.E.filter fun e => F.Connected (F.tail e) uB
  set mSmall := min EA.card EB.card
  have hCA_card : CA.card = EA.card + 1 := forest_comp_card_eq_edges_succ hF huA
  have hCB_card : CB.card = EB.card + 1 := forest_comp_card_eq_edges_succ hF huB
  have hCA_le_vCap : CA.card ≤ vCap := by
    have hsub : CA ⊆ Finset.range vCap := fun v hv =>
      Finset.mem_range.mpr (hvCap v (Finset.mem_filter.mp hv).1)
    simpa [Finset.card_range] using Finset.card_le_card hsub
  have hCB_le_vCap : CB.card ≤ vCap := by
    have hsub : CB ⊆ Finset.range vCap := fun v hv =>
      Finset.mem_range.mpr (hvCap v (Finset.mem_filter.mp hv).1)
    simpa [Finset.card_range] using Finset.card_le_card hsub
  have hnewSum_ltw : newSum < 2 ^ w := by
    have hdisj_AB : Disjoint CA CB := Finset.disjoint_left.mpr fun v hvA hvB =>
      hnotConn (connected_trans (connected_symm (Finset.mem_filter.mp hvA).2)
        (Finset.mem_filter.mp hvB).2)
    have hsub : CA ∪ CB ⊆ Finset.range vCap := fun v hv => by
      rw [Finset.mem_range]
      rcases Finset.mem_union.mp hv with h | h
      · exact hvCap v (Finset.mem_filter.mp h).1
      · exact hvCap v (Finset.mem_filter.mp h).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_AB, Finset.card_range] at hcard
    have : newSum ≤ vCap := by rw [hnewSum]; exact hcard
    omega
  -- Execute the full procedure `splitCompBFSProc`
  refine runs_start_le ?_
  dsimp only [splitCompBFSProc, startState]
  have hf_hdr_lt : fAncPtr + 5 < 2 ^ w := by dsimp [fAncSize] at hf_ltw; omega
  have hf_hdr_lt_qA : fAncPtr + 6 ≤ qBufA := by
    dsimp [fAncSize, fAncHdrSize, auxHdrSize] at hf_le_aux hqA_ge; omega
  have h2e_v_ltw : 2 * eCapF + vCap < 2 ^ w := by dsimp [dynGraphSize] at hdg_ltw; omega
  -- Stage 1: setup prefix via `bfsSetup_triple`
  refine runs_seq_triple_le
    (bfsSetup_triple (w := w) (p := p) (dgFPtr := dgFPtr) (fAncPtr := fAncPtr) (auxPtr := auxPtr)
      (vCap := vCap) (eCapF := eCapF) (n0 := n0) (uA := uA) (uB := uB) (oldCid := oldCid)
      (root1 := root1) (root2 := root2) (newSum := newSum) (mem := mem)
      hw16 hdg_ltw haux_ltw hqAPtr hqBPtr hvAPtr hvBPtr hvis0 huA_lt huB_lt)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  rintro st₀ ⟨hfr0, h0_1, h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14, h0_15, h0_16, h0_17,
    h0_18, h0_19, h0_20, h0_21, h0_28, hSA0, hSB0, h0_22, h0_23, h0_24, h0_25, h0_26, h0_27⟩
  -- Stage 2: lock-step loop via `bfsLockStep_triple`
  have hloop_step :=
    bfsLockStep_triple (w := w) (p := p) (dgFPtr := dgFPtr) (vCap := vCap)
      (eCapF := eCapF) (qBufA := qBufA) (qBufB := qBufB) (visA := visA) (visB := visB)
      (uA := uA) (uB := uB) (mem0 := mem) (regs_in := st₀.regs)
      hw16 hdg_ltw (by omega) hqA_qB hqB_vA hvA_vB (by omega) hF huA huB hvCap heCap
      hExtToInt hIntToExt hEndSlot hincL
  refine runs_seq_triple_le hloop_step
    ⟨rfl, hfr0, h0_12, h0_13, h0_14, h0_15, h0_16, h0_17, h0_18, h0_19, h0_20, h0_21,
      h0_28, hSA0, hSB0, h0_22, h0_23, h0_24, h0_25, h0_26, h0_27⟩ ?_
  -- After lock-step loop: hand off to `bfsPostLoop_runs`
  rintro st₁ ⟨hfr1, hreg1, k, qA, qHA, remA, qB, qHB, remB,
    hBA, hBB, hSA, hSB, hDA, _, hr22, hr23, _, hr26, hdone⟩
  clear hloop_step
  have hr1 : st₁.regs 1 = fAncPtr := (hreg1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_1
  have hr8 : st₁.regs 8 = oldCid := (hreg1 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_8
  have hr9 : st₁.regs 9 = root1 := (hreg1 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_9
  have hr10 : st₁.regs 10 = root2 := (hreg1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_10
  have hr11 : st₁.regs 11 = newSum := (hreg1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_11
  have hr18 : st₁.regs 18 = qBufA := (hreg1 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_18
  have hr19 : st₁.regs 19 = qBufB := (hreg1 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_19
  have hr20 : st₁.regs 20 = visA := (hreg1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_20
  have hr21 : st₁.regs 21 = visB := (hreg1 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0_21
  exact bfsPostLoop_runs hw16 hf_ltw hf_hdr_lt_qA hcs_le_qA hvB_ltw h2e_v_ltw
    hF huA huB hvCap heCap hExtToInt hincL hcidPtr hcrootPtr hcsizePtr hvis0
    hold_lt hr1_lt hr2_lt hold_ne_r2 hnewSum_ltw hnewSum hfr1
    hr1 hr8 hr9 hr10 hr11 hr18 hr19 hr20 hr21
    hBA hBB hSA hSB hDA hr22 hr23 hr26 hdone

end

end MinCostFlow.LSF.Program
