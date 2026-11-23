module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
public import MinCostFlow.SparseCore.Program.LSFWindowRepackDg
import WordRAM.Tactic

/-!
# Sparse Repack Verification for `FAncAt`

Proves `repackFAncProc_runs`, copying a guest `FAncAt` block into fresh zeroed host memory at host
vertex capacity `vCap_h` in time `≤ 70 * RF.R.card + 35 * RF.F.n + 160`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program

lemma repackFAncProc_runs {w : ℕ} {p : Program} {bCopy : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {guestBase fAncPtr_g dgFPtr_g dstFAnc vCap_g eCapF_g vCap_h : ℕ}
    {RF : RootedForest} {rList : List ℕ} {compId compRoot compSize : ℕ → ℕ}
    {activeCids : Finset ℕ}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hMemW : ∀ a, (guestBase + fAncPtr_g ≤ a ∧ a < guestBase + fAncPtr_g + fAncSize vCap_g) ∨
        (guestBase + dgFPtr_g ≤ a ∧ a < guestBase + dgFPtr_g + dynGraphSize vCap_g eCapF_g) →
      mem a < 2 ^ w)
    (hFAnc : FAncAt (fun a => mem (guestBase + a)) fAncPtr_g vCap_g RF rList compId compRoot compSize activeCids)
    (hdgF : DynGraphAt (fun a => mem (guestBase + a)) dgFPtr_g vCap_g eCapF_g RF.F)
    (hR_sub : RF.R ⊆ RF.F.V)
    (hvCap : vCap_g ≤ vCap_h)
    (hsrcF_w : guestBase + fAncPtr_g + fAncSize vCap_g < 2 ^ w)
    (hsrcDg_w : guestBase + dgFPtr_g + dynGraphSize vCap_g eCapF_g < 2 ^ w)
    (hdst_w : dstFAnc + fAncSize vCap_h < 2 ^ w)
    (hdisjF : guestBase + fAncPtr_g + fAncSize vCap_g ≤ dstFAnc ∨
              dstFAnc + fAncSize vCap_h ≤ guestBase + fAncPtr_g)
    (hdisjDg : guestBase + dgFPtr_g + dynGraphSize vCap_g eCapF_g ≤ dstFAnc ∨
               dstFAnc + fAncSize vCap_h ≤ guestBase + dgFPtr_g)
    (hzero : ∀ a, dstFAnc ≤ a → a < dstFAnc + fAncSize vCap_h → mem a = 0) :
    ∃ st' c,
      Runs w p ω (repackFAncProc bCopy)
        (startState [guestBase + fAncPtr_g, guestBase + dgFPtr_g, dstFAnc, vCap_h, guestBase] mem pos)
        (.returned 0) st' c ∧
      FAncAt st'.mem dstFAnc vCap_h RF rList compId compRoot compSize activeCids ∧
      (∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → st'.mem a = mem a) ∧
      c ≤ 70 * RF.R.card + 35 * RF.F.n + 160 := by
  suffices hmain : ∃ o st' c,
      Runs w p ω (repackFAncProc bCopy)
        (startState [guestBase + fAncPtr_g, guestBase + dgFPtr_g, dstFAnc, vCap_h, guestBase] mem pos)
        o st' c ∧
      (o = .returned 0 ∧
        FAncAt st'.mem dstFAnc vCap_h RF rList compId compRoot compSize activeCids ∧
        (∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → st'.mem a = mem a)) ∧
      c ≤ 70 * RF.R.card + 35 * RF.F.n + 160 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  classical
  dsimp only [FAncAt] at hFAnc
  rcases hFAnc with ⟨hrCnt, hIsRP, hRLP, hCIdP, hCRootP, hCSizeP, hvltF,
    hrlen, hrnd, hrmem, hrle, hrLA, hIsR, hact, hcid, hvF⟩
  have hdgF_s : DynGraphAt mem (guestBase + dgFPtr_g) vCap_g eCapF_g RF.F := dynGraphAt_shift hdgF
  rcases hdgF_s with ⟨_, _, _, hdgVCap, _, hdgN, _, _, ⟨vLF, hvLF_len, hvLF_nd, hvLF_mem, hvLF_LA, _⟩,
    _, _, _, _, _, _⟩
  have hoffs : fOffRCount = 0 ∧ fOffIsRootPtr = 1 ∧ fOffRListPtr = 2 ∧
      fOffCompIdPtr = 3 ∧ fOffCompRootPtr = 4 ∧ fOffCompSizePtr = 5 ∧ fAncHdrSize = 6 ∧
      dgVCapOff = 0 ∧ dgNOff = 2 := by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrCnt_le : RF.R.card ≤ vCap_g := by omega
  have hFn_le : RF.F.n ≤ vCap_g := by
    have hsub : RF.F.V ⊆ Finset.range vCap_g := fun v hv => Finset.mem_range.mpr (hvltF v hv)
    calc RF.F.n = RF.F.V.card := rfl
      _ ≤ (Finset.range vCap_g).card := Finset.card_le_card hsub
      _ = vCap_g := Finset.card_range vCap_g
  have hsz_g : fAncSize vCap_g = 6 + 5 * vCap_g := rfl
  have hsz_h : fAncSize vCap_h = 6 + 5 * vCap_h := rfl
  have hdg_sz : dynGraphSize vCap_g eCapF_g = 4 + 7 * vCap_g + 9 * eCapF_g := rfl
  have hdst_lt : fIsRootBase dstFAnc < 2 ^ w ∧ fRListBase dstFAnc vCap_h < 2 ^ w ∧
      fCompIdBase dstFAnc vCap_h < 2 ^ w ∧ fCompRootBase dstFAnc vCap_h < 2 ^ w ∧
      fCompSizeBase dstFAnc vCap_h < 2 ^ w := by
    dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  refine runs_start_le ?_
  unfold repackFAncProc startState
  refine runs_seq_assign_flat (v := RF.R.card) (by
    have hv : mem (guestBase + fAncPtr_g + fOffRCount) = RF.R.card := by simpa [Nat.add_assoc] using hrCnt
    eval_expr) ?_
  refine runs_seq_assign_flat (v := fIsRootBase dstFAnc) (by dsimp [fIsRootBase] at hdst_lt ⊢; eval_expr) ?_
  refine runs_seq_assign_flat (v := fRListBase dstFAnc vCap_h) (by dsimp [fRListBase] at hdst_lt ⊢; eval_expr) ?_
  refine runs_seq_assign_flat (v := fCompIdBase dstFAnc vCap_h) (by dsimp [fCompIdBase] at hdst_lt ⊢; eval_expr) ?_
  refine runs_seq_assign_flat (v := fCompRootBase dstFAnc vCap_h) (by dsimp [fCompRootBase] at hdst_lt ⊢; eval_expr) ?_
  refine runs_seq_assign_flat (v := fCompSizeBase dstFAnc vCap_h) (by dsimp [fCompSizeBase] at hdst_lt ⊢; eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffRCount) (v := RF.R.card) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffIsRootPtr) (v := fIsRootBase dstFAnc) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffRListPtr) (v := fRListBase dstFAnc vCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffCompIdPtr) (v := fCompIdBase dstFAnc vCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffCompRootPtr) (v := fCompRootBase dstFAnc vCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstFAnc + fOffCompSizePtr) (v := fCompSizeBase dstFAnc vCap_h) (by eval_expr) (by eval_expr) ?_
  set mem0 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update mem (dstFAnc + fOffRCount) RF.R.card)
      (dstFAnc + fOffIsRootPtr) (fIsRootBase dstFAnc))
      (dstFAnc + fOffRListPtr) (fRListBase dstFAnc vCap_h))
      (dstFAnc + fOffCompIdPtr) (fCompIdBase dstFAnc vCap_h))
      (dstFAnc + fOffCompRootPtr) (fCompRootBase dstFAnc vCap_h))
      (dstFAnc + fOffCompSizePtr) (fCompSizeBase dstFAnc vCap_h)
  have hmem0_out : ∀ a, a < dstFAnc ∨ dstFAnc + fAncHdrSize ≤ a → mem0 a = mem a := fun a ha => by
    dsimp only [mem0]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hmem0_hdr : mem0 (dstFAnc + fOffRCount) = RF.R.card ∧
      mem0 (dstFAnc + fOffIsRootPtr) = fIsRootBase dstFAnc ∧
      mem0 (dstFAnc + fOffRListPtr) = fRListBase dstFAnc vCap_h ∧
      mem0 (dstFAnc + fOffCompIdPtr) = fCompIdBase dstFAnc vCap_h ∧
      mem0 (dstFAnc + fOffCompRootPtr) = fCompRootBase dstFAnc vCap_h ∧
      mem0 (dstFAnc + fOffCompSizePtr) = fCompSizeBase dstFAnc vCap_h := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [mem0] <;>
      repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])
  refine runs_seq_assign_flat (v := guestBase + fRListBase fAncPtr_g vCap_g) (by
    have h1 : mem0 (guestBase + fAncPtr_g + fOffRListPtr) = fRListBase fAncPtr_g vCap_g := by
      rw [hmem0_out _ (by omega)]; simpa [Nat.add_assoc] using hRLP
    have hlt2 : guestBase + fRListBase fAncPtr_g vCap_g < 2 ^ w := by dsimp [fRListBase, fIsRootBase]; omega
    eval_expr) ?_
  refine runs_seq_assign_flat (v := guestBase + fCompIdBase fAncPtr_g vCap_g) (by
    have h1 : mem0 (guestBase + fAncPtr_g + fOffCompIdPtr) = fCompIdBase fAncPtr_g vCap_g := by
      rw [hmem0_out _ (by omega)]; simpa [Nat.add_assoc] using hCIdP
    have hlt2 : guestBase + fCompIdBase fAncPtr_g vCap_g < 2 ^ w := by
      dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega
    eval_expr) ?_
  refine runs_seq_assign_flat (v := guestBase + fCompRootBase fAncPtr_g vCap_g) (by
    have h1 : mem0 (guestBase + fAncPtr_g + fOffCompRootPtr) = fCompRootBase fAncPtr_g vCap_g := by
      rw [hmem0_out _ (by omega)]; simpa [Nat.add_assoc] using hCRootP
    have hlt2 : guestBase + fCompRootBase fAncPtr_g vCap_g < 2 ^ w := by
      dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega
    eval_expr) ?_
  refine runs_seq_assign_flat (v := guestBase + fCompSizeBase fAncPtr_g vCap_g) (by
    have h1 : mem0 (guestBase + fAncPtr_g + fOffCompSizePtr) = fCompSizeBase fAncPtr_g vCap_g := by
      rw [hmem0_out _ (by omega)]; simpa [Nat.add_assoc] using hCSizeP
    have hlt2 : guestBase + fCompSizeBase fAncPtr_g vCap_g < 2 ^ w := by
      dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega
    eval_expr) ?_
  refine runs_seq_call_flat hCopy
    (by eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> (try dsimp [fRListBase, fIsRootBase]) <;> omega)
    ⟨fRListBase dstFAnc vCap_h, guestBase + fRListBase fAncPtr_g vCap_g, RF.R.card, rfl,
      by dsimp [fRListBase, fIsRootBase]; omega,
      by dsimp [fRListBase, fIsRootBase]; omega,
      by dsimp [fRListBase, fIsRootBase]; omega⟩
    (fun _ mem1 pos1 hpost1 => ?_)
  rcases hpost1 with ⟨_, _, _, harg1, _, hcp1, hfr1⟩
  cases harg1
  have hst1_out : ∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → mem1 a = mem a :=
    fun a ha => (hfr1 a (by dsimp [fRListBase, fIsRootBase]; omega)).trans (hmem0_out a (by omega))
  let RInv : ℕ → State → Prop := fun i st =>
    st.regs 1 = guestBase + dgFPtr_g ∧ st.regs 5 = RF.R.card ∧
    st.regs 6 = fIsRootBase dstFAnc ∧ st.regs 8 = fCompIdBase dstFAnc vCap_h ∧
    st.regs 9 = fCompRootBase dstFAnc vCap_h ∧ st.regs 10 = fCompSizeBase dstFAnc vCap_h ∧
    st.regs 11 = guestBase + fRListBase fAncPtr_g vCap_g ∧
    st.regs 12 = guestBase + fCompIdBase fAncPtr_g vCap_g ∧
    st.regs 13 = guestBase + fCompRootBase fAncPtr_g vCap_g ∧
    st.regs 14 = guestBase + fCompSizeBase fAncPtr_g vCap_g ∧ st.regs 16 = i ∧
    (∀ a, a < dstFAnc + fAncHdrSize ∨
        (fRListBase dstFAnc vCap_h ≤ a ∧ a < fCompRootBase dstFAnc vCap_h) ∨
        dstFAnc + fAncSize vCap_h ≤ a → st.mem a = mem1 a) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < rList.length),
      let r := rList[j]
      st.mem (fIsRootBase dstFAnc + r) = 1 ∧
      st.mem (fCompRootBase dstFAnc vCap_h + r) = mem (guestBase + fCompRootBase fAncPtr_g vCap_g + r) ∧
      st.mem (fCompSizeBase dstFAnc vCap_h + r) = mem (guestBase + fCompSizeBase fAncPtr_g vCap_g + r)) ∧
    (∀ v < vCap_h, (∀ j (hj : j < i), ∀ (hj' : j < rList.length), rList[j] ≠ v) →
      st.mem (fIsRootBase dstFAnc + v) = 0)
  have hrLoop : Triple w p
      (fun st => st.regs 1 = guestBase + dgFPtr_g ∧ st.regs 5 = RF.R.card ∧
        st.regs 6 = fIsRootBase dstFAnc ∧ st.regs 8 = fCompIdBase dstFAnc vCap_h ∧
        st.regs 9 = fCompRootBase dstFAnc vCap_h ∧ st.regs 10 = fCompSizeBase dstFAnc vCap_h ∧
        st.regs 11 = guestBase + fRListBase fAncPtr_g vCap_g ∧
        st.regs 12 = guestBase + fCompIdBase fAncPtr_g vCap_g ∧
        st.regs 13 = guestBase + fCompRootBase fAncPtr_g vCap_g ∧
        st.regs 14 = guestBase + fCompSizeBase fAncPtr_g vCap_g ∧ st.mem = mem1)
      (forRange 16 (.const 0) (.reg 5)
        (.assign 17 (.load (.bin .add (.reg 11) (.reg 16))) ;;
         .store (.bin .add (.reg 6) (.reg 17)) (.const 1) ;;
         .store (.bin .add (.reg 9) (.reg 17)) (.load (.bin .add (.reg 13) (.reg 17))) ;;
         .store (.bin .add (.reg 10) (.reg 17)) (.load (.bin .add (.reg 14) (.reg 17)))))
      (normalPost (RInv RF.R.card)) (fun _ => 45 * RF.R.card + 7) := by
    refine (Triple.forRange_const 36 0 RF.R.card (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q1, q5, q6, q8, q9, q10, q11, q12, q13, q14, hmeq⟩
        refine ⟨by eval_expr, q1, q5, q6, q8, q9, q10, q11, q12, q13, q14, by simp,
          fun _ _ => by rw [hmeq], fun j hj _ => by omega, fun v hv _ => ?_⟩
        rw [hmeq, hfr1 _ (Or.inl (by dsimp [fRListBase, fIsRootBase]; omega)),
            hmem0_out _ (Or.inr (by dsimp [fIsRootBase]; omega))]
        exact hzero _ (by dsimp [fIsRootBase]; omega) (by dsimp [fIsRootBase]; omega))
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h5 := hi.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨q1, q5, q6, q8, q9, q10, q11, q12, q13, q14, q16, hfrR, hRdone, hR0⟩
        have hiL : i < rList.length := by omega
        set r := rList[i]
        have hr_R : r ∈ RF.R := (hrmem r).mp (List.getElem_mem hiL)
        have hr_lt : r < vCap_g := hvltF r (hR_sub hr_R)
        have hst_out : ∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → st.mem a = mem a :=
          fun a ha => (hfrR a (by omega)).trans (hst1_out a ha)
        have hr_rd : st.mem (guestBase + fRListBase fAncPtr_g vCap_g + i) = r := by
          rw [hst_out _ (by dsimp [fRListBase, fIsRootBase]; omega)]
          simpa [Nat.add_assoc] using hrLA i hiL
        set crVal := mem (guestBase + fCompRootBase fAncPtr_g vCap_g + r)
        set csVal := mem (guestBase + fCompSizeBase fAncPtr_g vCap_g + r)
        have hcrW : crVal < 2 ^ w := hMemW _ (Or.inl ⟨by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega,
          by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega⟩)
        have hcsW : csVal < 2 ^ w := hMemW _ (Or.inl ⟨by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega,
          by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega⟩)
        have hr_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < rList.length), rList[j] ≠ r := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp hrnd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := r) (by
          have hlt : guestBase + fRListBase fAncPtr_g vCap_g + i < 2 ^ w := by dsimp [fRListBase, fIsRootBase]; omega
          eval_expr) ?_
        refine runs_seq_store_le (x := fIsRootBase dstFAnc + r) (v := 1)
          (by dsimp [fIsRootBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := fCompRootBase dstFAnc vCap_h + r) (v := crVal)
          (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; eval_expr)
          (by have hlt : guestBase + fCompRootBase fAncPtr_g vCap_g + r < 2 ^ w := by
                dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega
              have hrd : Function.update st.mem (fIsRootBase dstFAnc + r) 1
                  (guestBase + fCompRootBase fAncPtr_g vCap_g + r) = crVal := by
                rw [Function.update_of_ne (by dsimp [fIsRootBase, fCompRootBase, fCompIdBase, fRListBase]; omega)]
                exact hst_out _ (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
              eval_expr) ?_
        refine runs_store_le (x := fCompSizeBase dstFAnc vCap_h + r) (v := csVal)
          (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; eval_expr)
          (by have hlt : guestBase + fCompSizeBase fAncPtr_g vCap_g + r < 2 ^ w := by
                dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega
              have hrd : Function.update (Function.update st.mem (fIsRootBase dstFAnc + r) 1)
                  (fCompRootBase dstFAnc vCap_h + r) crVal
                  (guestBase + fCompSizeBase fAncPtr_g vCap_g + r) = csVal := by
                rw [Function.update_of_ne (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega),
                    Function.update_of_ne (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)]
                exact hst_out _ (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
              eval_expr) ?_ (by wram_cost)
        refine ⟨⟨by simp [q1], by simp [q5], by simp [q6], by simp [q8], by simp [q9],
          by simp [q10], by simp [q11], by simp [q12], by simp [q13], by simp [q14], by simp,
          fun a ha => by
            dsimp only
            rw [Function.update_of_ne (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega),
                Function.update_of_ne (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega),
                Function.update_of_ne (by dsimp [fIsRootBase, fRListBase, fCompRootBase] at ha ⊢; omega)]
            exact hfrR a ha,
          fun j hj hj' => ?_, fun v hv hne => ?_⟩, by simp [q16]⟩
        · by_cases hji : j = i
          · subst hji
            refine ⟨?_, ?_, Function.update_self _ _ _⟩
            · dsimp only
              rw [Function.update_of_ne (by dsimp [fIsRootBase, fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
                  Function.update_of_ne (by dsimp [fIsRootBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
                  Function.update_self]
            · dsimp only
              rw [Function.update_of_ne (by dsimp [fCompRootBase, fCompSizeBase]; omega), Function.update_self]
          · have hrj_ne := hr_ne_prev j (by omega) hj'
            have hrj_lt := hvltF _ (hR_sub ((hrmem _).mp (List.getElem_mem hj')))
            have hd := hRdone j (by omega) hj'
            refine ⟨by
                dsimp only
                rw [Function.update_of_ne (by dsimp [fIsRootBase, fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
                    Function.update_of_ne (by dsimp [fIsRootBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
                    Function.update_of_ne (by dsimp [fIsRootBase]; omega)]; exact hd.1,
              by
                dsimp only
                rw [Function.update_of_ne (by dsimp [fCompRootBase, fCompSizeBase]; omega),
                    Function.update_of_ne (by dsimp [fCompRootBase]; omega),
                    Function.update_of_ne (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)]; exact hd.2.1,
              by
                dsimp only
                rw [Function.update_of_ne (by dsimp [fCompSizeBase]; omega),
                    Function.update_of_ne (by dsimp [fCompSizeBase, fCompRootBase]; omega),
                    Function.update_of_ne (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)]; exact hd.2.2⟩
        · have hvr : v ≠ r := (hne i (by omega) hiL).symm
          dsimp only
          rw [Function.update_of_ne (by dsimp [fIsRootBase, fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
              Function.update_of_ne (by dsimp [fIsRootBase, fCompRootBase, fCompIdBase, fRListBase]; omega),
              Function.update_of_ne (by dsimp [fIsRootBase]; omega)]
          exact hR0 v hv fun j hj hj' => hne j (by omega) hj')).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hrLoop ⟨by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, rfl⟩ (fun st2 hR => ?_)
  rcases hR with ⟨q1, _, _, q8, _, _, _, q12, _, _, _, hfr2, hRdone, hR0⟩
  have hst2_out : ∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → st2.mem a = mem a :=
    fun a ha => (hfr2 a (by omega)).trans (hst1_out a ha)
  refine runs_seq_assign_le (v := vCap_g) (by
    have hv : st2.mem (guestBase + dgFPtr_g + dgVCapOff) = vCap_g := by rw [hst2_out _ (by omega)]; exact hdgVCap
    eval_expr) ?_
  refine runs_seq_assign_le (v := RF.F.n) (by
    have hv : st2.mem (guestBase + dgFPtr_g + dgNOff) = RF.F.n := by rw [hst2_out _ (by omega)]; exact hdgN
    eval_expr) ?_
  refine runs_seq_assign_le (v := dgVListBase (guestBase + dgFPtr_g) vCap_g) (by
    dsimp [dgVListBase]; eval_expr) ?_
  let VInv : ℕ → State → Prop := fun i st =>
    st.regs 8 = fCompIdBase dstFAnc vCap_h ∧
    st.regs 12 = guestBase + fCompIdBase fAncPtr_g vCap_g ∧
    st.regs 16 = RF.F.n ∧ st.regs 17 = dgVListBase (guestBase + dgFPtr_g) vCap_g ∧
    st.regs 18 = i ∧
    (∀ a, a < fCompIdBase dstFAnc vCap_h ∨ fCompRootBase dstFAnc vCap_h ≤ a → st.mem a = st2.mem a) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < vLF.length),
      st.mem (fCompIdBase dstFAnc vCap_h + vLF[j]) =
        mem (guestBase + fCompIdBase fAncPtr_g vCap_g + vLF[j]))
  have hvLoop : Triple w p
      (fun st => st.regs 8 = fCompIdBase dstFAnc vCap_h ∧
        st.regs 12 = guestBase + fCompIdBase fAncPtr_g vCap_g ∧
        st.regs 16 = RF.F.n ∧ st.regs 17 = dgVListBase (guestBase + dgFPtr_g) vCap_g ∧ st.mem = st2.mem)
      (forRange 18 (.const 0) (.reg 16)
        (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
         .store (.bin .add (.reg 8) (.reg 19)) (.load (.bin .add (.reg 12) (.reg 19)))))
      (normalPost (VInv RF.F.n)) (fun _ => 35 * RF.F.n + 7) := by
    refine (Triple.forRange_const 26 0 RF.F.n (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨p8, p12, p16, p17, hmeq⟩
        exact ⟨by eval_expr, p8, p12, p16, p17, by simp, fun _ _ => by rw [hmeq], fun j hj _ => by omega⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.1)
      (fun _ st _ _ hi => by have h16 := hi.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨p8, p12, p16, p17, p18, hfrV, hVdone⟩
        have hiL : i < vLF.length := by omega
        set v := vLF[i]
        have hv_mem : v ∈ RF.F.V := (hvLF_mem v).mp (List.getElem_mem hiL)
        have hv_lt : v < vCap_g := hvltF v hv_mem
        have hst_out : ∀ a, a < dstFAnc ∨ dstFAnc + fAncSize vCap_h ≤ a → st.mem a = mem a :=
          fun a ha => (hfrV a (by dsimp [fCompIdBase, fCompRootBase, fRListBase, fIsRootBase]; omega)).trans (hst2_out a ha)
        have hv_rd : st.mem (dgVListBase (guestBase + dgFPtr_g) vCap_g + i) = v := by
          rw [hst_out _ (by dsimp [dgVListBase]; omega)]; exact hvLF_LA i hiL
        set cidVal := mem (guestBase + fCompIdBase fAncPtr_g vCap_g + v)
        have hcidW : cidVal < 2 ^ w := hMemW _ (Or.inl ⟨by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega,
          by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega⟩)
        have hv_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < vLF.length), vLF[j] ≠ v := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp hvLF_nd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := v) (by
          have hlt : dgVListBase (guestBase + dgFPtr_g) vCap_g + i < 2 ^ w := by dsimp [dgVListBase]; omega
          eval_expr) ?_
        refine runs_store_le (x := fCompIdBase dstFAnc vCap_h + v) (v := cidVal)
          (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; eval_expr)
          (by have hlt : guestBase + fCompIdBase fAncPtr_g vCap_g + v < 2 ^ w := by
                dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega
              have hrd : st.mem (guestBase + fCompIdBase fAncPtr_g vCap_g + v) = cidVal :=
                hst_out _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)
              eval_expr) ?_ (by wram_cost)
        refine ⟨⟨by simp [p8], by simp [p12], by simp [p16], by simp [p17], by simp,
          fun a ha => by dsimp only; rw [Function.update_of_ne (by dsimp [fCompIdBase, fCompRootBase] at ha ⊢; omega)]; exact hfrV a ha,
          fun j hj hj' => ?_⟩, by simp [p18]⟩
        by_cases hji : j = i
        · subst hji; exact Function.update_self _ _ _
        · dsimp only; rw [Function.update_of_ne (by have := hv_ne_prev j (by omega) hj'; omega)]
          exact hVdone j (by omega) hj')).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hvLoop ⟨by simp [q8], by simp [q12], by simp, by simp, rfl⟩
    (fun st3 hV => ?_)
  rcases hV with ⟨_, _, _, _, _, hfr3, hVdone⟩
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_, fun a ha =>
    (hfr3 a (by dsimp [fCompIdBase, fCompRootBase, fRListBase, fIsRootBase]; omega)).trans
      (hst2_out a ha)⟩ (by
    simp [memCopyContract, argsSize, Expr.size]; omega)
  have hhdr_eq : ∀ off < fAncHdrSize, st3.mem (dstFAnc + off) = mem0 (dstFAnc + off) := fun off hoff =>
    (hfr3 _ (Or.inl (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega))).trans
      ((hfr2 _ (Or.inl (by omega))).trans (hfr1 _ (Or.inl (by dsimp [fRListBase, fIsRootBase]; omega))))
  dsimp only [FAncAt]
  refine ⟨(hhdr_eq _ (by omega)).trans hmem0_hdr.1, (hhdr_eq _ (by omega)).trans hmem0_hdr.2.1,
    (hhdr_eq _ (by omega)).trans hmem0_hdr.2.2.1, (hhdr_eq _ (by omega)).trans hmem0_hdr.2.2.2.1,
    (hhdr_eq _ (by omega)).trans hmem0_hdr.2.2.2.2.1, (hhdr_eq _ (by omega)).trans hmem0_hdr.2.2.2.2.2,
    fun v hv => lt_of_lt_of_le (hvltF v hv) hvCap, hrlen, hrnd, hrmem, by omega,
    ?_, ?_, hact, ?_, ?_⟩
  · intro i hi
    rw [hfr3 (fRListBase dstFAnc vCap_h + i) (Or.inl (by dsimp [fCompIdBase, fRListBase]; omega)),
        hfr2 (fRListBase dstFAnc vCap_h + i) (Or.inr (Or.inl ⟨by omega, by dsimp [fCompRootBase, fCompIdBase, fRListBase]; omega⟩)),
        hcp1 i (by omega), hmem0_out _ (by dsimp [fRListBase, fIsRootBase]; omega)]
    simpa [Nat.add_assoc] using hrLA i hi
  · intro v hv
    rw [hfr3 (fIsRootBase dstFAnc + v) (Or.inl (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega))]
    split_ifs with hvR
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hrmem v).mpr hvR)
      exact (hRdone j (by omega) hj).1
    · exact hR0 v hv fun j _ hj' hEq => hvR (hEq ▸ (hrmem _).mp (List.getElem_mem hj'))
  · intro c hc
    obtain ⟨hlt, hcr, hcrR, hcid_eq, hcs, hcs1, hcard⟩ := hcid c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hrmem c).mpr (hact hc))
    refine ⟨lt_of_lt_of_le hlt hvCap, ?_, hcrR, hcid_eq, ?_, hcs1, hcard⟩
    · rw [hfr3 (fCompRootBase dstFAnc vCap_h + rList[j]) (Or.inr (by omega)), (hRdone j (by omega) hj).2.1]
      simpa [Nat.add_assoc] using hcr
    · rw [hfr3 (fCompSizeBase dstFAnc vCap_h + rList[j]) (Or.inr (by dsimp [fCompSizeBase, fCompRootBase]; omega)),
          (hRdone j (by omega) hj).2.2]
      simpa [Nat.add_assoc] using hcs
  · intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hvLF_mem v).mpr hv)
    rw [hVdone j (by omega) hj]; simpa [Nat.add_assoc] using hvF _ hv

end MinCostFlow.SparseCore.Program
