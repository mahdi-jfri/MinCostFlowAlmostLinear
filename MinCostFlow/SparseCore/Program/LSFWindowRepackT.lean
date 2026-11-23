module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
public import MinCostFlow.SparseCore.Program.LSFWindowRepackDg
import WordRAM.Tactic

/-!
# Sparse Repack Verification for `TBlockAt`

Proves `repackTBlockProc_runs`, copying a guest `TBlockAt` into fresh zeroed host memory at host
capacities `(vCap_h, eCap_h)` in time `≤ 115 * G.n + 480 * tM + 400`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program

private def tHdrMem (m : ℕ → ℕ) (dstT vCap_h eCap_h tM : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update m
      (dstT + tOffM) tM) (dstT + tOffDgTPtr) (tDgTPtr dstT))
      (dstT + tOffOrigIdPtr) (tOrigIdBase dstT vCap_h tM))
      (dstT + tOffPiPtr) (tPiBase dstT vCap_h tM))
      (dstT + tOffFrozenTailPtr) (tFrozenTailBase dstT vCap_h tM))
      (dstT + tOffFrozenHeadPtr) (tFrozenHeadBase dstT vCap_h tM))
      (dstT + tOffIdxOfEdgePtr) (tIdxOfEdgeBase dstT vCap_h tM))
      (dstT + tOffSplitScratchPtr) (tSplitScratchBase dstT vCap_h eCap_h tM)

private lemma tHdrMem_out {m : ℕ → ℕ} {dstT vCap_h eCap_h tM a : ℕ}
    (ha : a < dstT ∨ dstT + tHdrSize ≤ a) :
    tHdrMem m dstT vCap_h eCap_h tM a = m a := by
  have h1 : ∀ k < tHdrSize, a ≠ dstT + k := fun k hk => by omega
  unfold tHdrMem
  repeat rw [Function.update_of_ne (h1 _ (by decide))]

private lemma tHdrMem_at (m : ℕ → ℕ) (dstT vCap_h eCap_h tM : ℕ) :
    let m0 := tHdrMem m dstT vCap_h eCap_h tM
    m0 (dstT + tOffM) = tM ∧ m0 (dstT + tOffDgTPtr) = tDgTPtr dstT ∧
    m0 (dstT + tOffOrigIdPtr) = tOrigIdBase dstT vCap_h tM ∧
    m0 (dstT + tOffPiPtr) = tPiBase dstT vCap_h tM ∧
    m0 (dstT + tOffFrozenTailPtr) = tFrozenTailBase dstT vCap_h tM ∧
    m0 (dstT + tOffFrozenHeadPtr) = tFrozenHeadBase dstT vCap_h tM ∧
    m0 (dstT + tOffIdxOfEdgePtr) = tIdxOfEdgeBase dstT vCap_h tM ∧
    m0 (dstT + tOffSplitScratchPtr) = tSplitScratchBase dstT vCap_h eCap_h tM := by
  have hne : ∀ {j k : ℕ}, j ≠ k → dstT + j ≠ dstT + k := fun h => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold tHdrMem <;>
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (hne (by decide))])

private lemma tBlock_bounds (p vCap eCap tM : ℕ) :
    p + tHdrSize = tDgTPtr p ∧
    tDgTPtr p + dynGraphSize vCap (2 * tM + 1) = tOrigIdBase p vCap tM ∧
    tOrigIdBase p vCap tM + tM = tPiBase p vCap tM ∧
    tPiBase p vCap tM + tM = tFrozenTailBase p vCap tM ∧
    tFrozenTailBase p vCap tM + tM = tFrozenHeadBase p vCap tM ∧
    tFrozenHeadBase p vCap tM + tM = tIdxOfEdgeBase p vCap tM ∧
    tIdxOfEdgeBase p vCap tM + eCap = tSplitScratchBase p vCap eCap tM ∧
    tSplitScratchBase p vCap eCap tM + (4 + 2 * tM) = p + tBlockSize vCap eCap tM :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, tBlock_end_eq p vCap eCap tM⟩

private lemma tBlock_sub_le (p vCap eCap tM : ℕ) :
    p + tHdrSize ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tDgTPtr p ∧ tDgTPtr p + dynGraphSize vCap (2 * tM + 1) ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tOrigIdBase p vCap tM ∧ tOrigIdBase p vCap tM + tM ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tPiBase p vCap tM ∧ tPiBase p vCap tM + tM ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tFrozenTailBase p vCap tM ∧ tFrozenTailBase p vCap tM + tM ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tFrozenHeadBase p vCap tM ∧ tFrozenHeadBase p vCap tM + tM ≤ p + tBlockSize vCap eCap tM ∧
    p ≤ tIdxOfEdgeBase p vCap tM ∧ tIdxOfEdgeBase p vCap tM + eCap ≤ p + tBlockSize vCap eCap tM := by
  have := tBlock_bounds p vCap eCap tM
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

private lemma repackT_idxLoop {w : ℕ} {p : Program} {mem mem5 : ℕ → ℕ}
    {srcOrig dstIdx eCap_h tM : ℕ} {tOrigList : List ℕ}
    (hw : 20 < 2 ^ w) (htM_w : tM < 2 ^ w)
    (hsrc_w : srcOrig + tM < 2 ^ w) (hdst_w : dstIdx + eCap_h < 2 ^ w)
    (hMemW : ∀ i < tM, mem (srcOrig + i) < 2 ^ w)
    (hlen : tOrigList.length = tM) (hnd : tOrigList.Nodup)
    (hLO : ∀ i (hi : i < tOrigList.length), mem (srcOrig + i) = tOrigList[i])
    (hsrc_disj : ∀ i < tM, srcOrig + i < dstIdx ∨ dstIdx + eCap_h ≤ srcOrig + i)
    (hmem5_src : ∀ i < tM, mem5 (srcOrig + i) = mem (srcOrig + i))
    (hidx_zero5 : ∀ e < eCap_h, mem5 (dstIdx + e) = 0) :
    Triple w p
      (fun st => st.regs 3 = eCap_h ∧ st.regs 5 = tM ∧ st.regs 12 = dstIdx ∧
        st.regs 15 = srcOrig ∧ st.mem = mem5)
      (forRange 16 (.const 0) (.reg 5)
        (.assign 17 (.load (.bin .add (.reg 15) (.reg 16))) ;;
         .cond (.bin .lt (.reg 17) (.reg 3))
           (.store (.bin .add (.reg 12) (.reg 17)) (.bin .add (.reg 16) (.const 1)))
           .nop))
      (normalPost fun st =>
        (∀ a, a < dstIdx ∨ dstIdx + eCap_h ≤ a → st.mem a = mem5 a) ∧
        (∀ j (_hj : j < tM), ∀ (hj' : j < tOrigList.length), tOrigList[j] < eCap_h →
          st.mem (dstIdx + tOrigList[j]) = j + 1) ∧
        (∀ e < eCap_h, (∀ j (_hj : j < tM), ∀ (hj' : j < tOrigList.length), tOrigList[j] ≠ e) →
          st.mem (dstIdx + e) = 0))
      (fun _ => 30 * tM + 7) := by
  let IInv : ℕ → State → Prop := fun i st =>
    st.regs 3 = eCap_h ∧ st.regs 5 = tM ∧ st.regs 12 = dstIdx ∧
    st.regs 15 = srcOrig ∧ st.regs 16 = i ∧
    (∀ a, a < dstIdx ∨ dstIdx + eCap_h ≤ a → st.mem a = mem5 a) ∧
    (∀ j (_hj : j < i), ∀ (hj' : j < tOrigList.length), tOrigList[j] < eCap_h →
      st.mem (dstIdx + tOrigList[j]) = j + 1) ∧
    (∀ e < eCap_h, (∀ j (_hj : j < i), ∀ (hj' : j < tOrigList.length), tOrigList[j] ≠ e) →
      st.mem (dstIdx + e) = 0)
  have hloop : Triple w p
      (fun st => st.regs 3 = eCap_h ∧ st.regs 5 = tM ∧ st.regs 12 = dstIdx ∧
        st.regs 15 = srcOrig ∧ st.mem = mem5)
      (forRange 16 (.const 0) (.reg 5)
        (.assign 17 (.load (.bin .add (.reg 15) (.reg 16))) ;;
         .cond (.bin .lt (.reg 17) (.reg 3))
           (.store (.bin .add (.reg 12) (.reg 17)) (.bin .add (.reg 16) (.const 1)))
           .nop))
      (normalPost (IInv tM)) (fun _ => 30 * tM + 7) := by
    refine (Triple.forRange_const 21 0 tM (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q3, q5, q12, q15, hmeq⟩
        exact ⟨by eval_expr, q3, q5, q12, q15, by simp, fun _ _ => by rw [hmeq],
          fun j hj _ _ => by omega, fun e he _ => by rw [hmeq]; exact hidx_zero5 e he⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.1)
      (fun _ st _ _ hi => by have h5 := hi.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨q3, q5, q12, q15, q16, hfrI, hIdone, hI0⟩
        have hiL : i < tOrigList.length := by omega
        set e := tOrigList[i]
        have he_rd : st.mem (srcOrig + i) = e := by
          rw [hfrI _ (hsrc_disj i hilt), hmem5_src i hilt, hLO i hiL]
        have heW : e < 2 ^ w := by dsimp only [e]; rw [← hLO i hiL]; exact hMemW i hilt
        have he_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < tOrigList.length), tOrigList[j] ≠ e := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        change ∃ o st' c, Runs w p ω' _ ⟨st.mem, st.regs, st.pos⟩ o st' c ∧ _
        refine runs_start_le ?_
        refine runs_seq_assign_flat (v := e) (by
          have hlt : srcOrig + i < 2 ^ w := by omega
          eval_expr) ?_
        refine WordRAM.runs_cond_le (v := if e < eCap_h then 1 else 0) (by eval_expr) (fun hne => ?_) (fun hzero' => ?_)
        · have hec : e < eCap_h := by by_contra h; simp [h] at hne
          refine runs_store_le (x := dstIdx + e) (v := i + 1)
            (by eval_expr) (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨by simp [q3], by simp [q5], by simp [q12], by simp [q15], by simp,
            fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfrI a ha,
            fun j hj hj' hjlt => ?_, fun e' he' hne => ?_⟩, by simp [q16]⟩
          · by_cases hji : j = i
            · subst hji; exact Function.update_self _ _ _
            · dsimp only
              rw [Function.update_of_ne (by have := he_ne_prev j (by omega) hj'; omega)]
              exact hIdone j (by omega) hj' hjlt
          · dsimp only
            rw [Function.update_of_ne (by have := hne i (by omega) hiL; omega)]
            exact hI0 e' he' fun j hj hj' => hne j (by omega) hj'
        · have hnotc : ¬ e < eCap_h := by intro h; simp [h] at hzero'
          refine runs_nop_le ?_ (by wram_cost)
          refine ⟨⟨by simp [q3], by simp [q5], by simp [q12], by simp [q15], by simp,
            hfrI, fun j hj hj' hjlt => ?_, fun e' he' hne => ?_⟩, by simp [q16]⟩
          · by_cases hji : j = i
            · subst hji; omega
            · exact hIdone j (by omega) hj' hjlt
          · exact hI0 e' he' fun j hj hj' => hne j (by omega) hj')).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  exact hloop.conseq (fun _ h => h) (fun o st h => by
    cases o with
    | normal => rcases h with ⟨_, _, _, _, _, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    | returned _ => exact h.elim) (fun _ _ => le_rfl)

set_option maxHeartbeats 600000 in
private lemma assemble_TBlockAt {mem mem1 mem2 mem3 mem4 mem5 mem6 : ℕ → ℕ}
    {guestBase tPtr_g dstT vCap_g eCap_g vCap_h eCap_h tM : ℕ}
    {G T_cur T₀ dgT : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hT : TBlockAt (fun a => mem (guestBase + a)) tPtr_g vCap_g eCap_g tM G T_cur T₀ π tOrigList)
    (hdgT_dst : DynGraphAt mem1 (tDgTPtr dstT) vCap_h (2 * tM + 1) dgT)
    (hdgTV : dgT.V = G.V) (hdgTE : ∀ e ∈ dgT.E, e < 2 * tM)
    (htrack : ∀ i (hi : i < tOrigList.length),
      let f := tOrigList[i]
      (2 * i ∈ dgT.E ↔ f ∈ G.E ∧ G.tail f = T_cur.tail f) ∧
      (2 * i ∈ dgT.E → dgT.tail (2 * i) = T_cur.tail f ∧ dgT.head (2 * i) = T_cur.tail f) ∧
      (2 * i ∉ dgT.E → mem (guestBase + (tFrozenTailBase tPtr_g vCap_g tM + i)) = T_cur.tail f) ∧
      (2 * i + 1 ∈ dgT.E ↔ f ∈ G.E ∧ G.head f = T_cur.head f) ∧
      (2 * i + 1 ∈ dgT.E → dgT.tail (2 * i + 1) = T_cur.head f ∧ dgT.head (2 * i + 1) = T_cur.head f) ∧
      (2 * i + 1 ∉ dgT.E → mem (guestBase + (tFrozenHeadBase tPtr_g vCap_g tM + i)) = T_cur.head f))
    (hsrc_out : ∀ a, guestBase + tPtr_g ≤ a → a < guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM →
      a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a)
    (hfr1 : ∀ a, a < tDgTPtr dstT ∨ tDgTPtr dstT + dynGraphSize vCap_h (2 * tM + 1) ≤ a →
      mem1 a = tHdrMem mem dstT vCap_h eCap_h tM a)
    (hfr2 : ∀ a, a < tOrigIdBase dstT vCap_h tM ∨ tOrigIdBase dstT vCap_h tM + tM ≤ a → mem2 a = mem1 a)
    (hcp2 : ∀ i < tM, mem2 (tOrigIdBase dstT vCap_h tM + i) = mem1 (guestBase + tOrigIdBase tPtr_g vCap_g tM + i))
    (hfr3 : ∀ a, a < tPiBase dstT vCap_h tM ∨ tPiBase dstT vCap_h tM + tM ≤ a → mem3 a = mem2 a)
    (hcp3 : ∀ i < tM, mem3 (tPiBase dstT vCap_h tM + i) = mem2 (guestBase + tPiBase tPtr_g vCap_g tM + i))
    (hfr4 : ∀ a, a < tFrozenTailBase dstT vCap_h tM ∨ tFrozenTailBase dstT vCap_h tM + tM ≤ a → mem4 a = mem3 a)
    (hcp4 : ∀ i < tM, mem4 (tFrozenTailBase dstT vCap_h tM + i) = mem3 (guestBase + tFrozenTailBase tPtr_g vCap_g tM + i))
    (hfr5 : ∀ a, a < tFrozenHeadBase dstT vCap_h tM ∨ tFrozenHeadBase dstT vCap_h tM + tM ≤ a → mem5 a = mem4 a)
    (hcp5 : ∀ i < tM, mem5 (tFrozenHeadBase dstT vCap_h tM + i) = mem4 (guestBase + tFrozenHeadBase tPtr_g vCap_g tM + i))
    (hfr6 : ∀ a, a < tIdxOfEdgeBase dstT vCap_h tM ∨ tIdxOfEdgeBase dstT vCap_h tM + eCap_h ≤ a → mem6 a = mem5 a)
    (hIdone : ∀ j (_hj : j < tM), ∀ (hj' : j < tOrigList.length), tOrigList[j] < eCap_h →
      mem6 (tIdxOfEdgeBase dstT vCap_h tM + tOrigList[j]) = j + 1)
    (hI0 : ∀ e < eCap_h, (∀ j (_hj : j < tM), ∀ (hj' : j < tOrigList.length), tOrigList[j] ≠ e) →
      mem6 (tIdxOfEdgeBase dstT vCap_h tM + e) = 0) :
    TBlockAt mem6 dstT vCap_h eCap_h tM G T_cur T₀ π tOrigList := by
  rcases hT with ⟨_, _, _, _, _, _, _, _, hlen, hnd, hmemL, hLO, hLPi, _, _, _, _, _, _, _⟩
  have hS := tBlock_sub_le tPtr_g vCap_g eCap_g tM
  have hD := tBlock_sub_le dstT vCap_h eCap_h tM
  have hB := tBlock_bounds dstT vCap_h eCap_h tM
  have hbelow_idx : ∀ a < tIdxOfEdgeBase dstT vCap_h tM, mem6 a = mem5 a := fun a ha => hfr6 a (Or.inl ha)
  have hbelow_fh : ∀ a < tFrozenHeadBase dstT vCap_h tM, mem6 a = mem4 a :=
    fun a ha => (hbelow_idx a (by omega)).trans (hfr5 a (Or.inl ha))
  have hbelow_ft : ∀ a < tFrozenTailBase dstT vCap_h tM, mem6 a = mem3 a :=
    fun a ha => (hbelow_fh a (by omega)).trans (hfr4 a (Or.inl ha))
  have hbelow_pi : ∀ a < tPiBase dstT vCap_h tM, mem6 a = mem2 a :=
    fun a ha => (hbelow_ft a (by omega)).trans (hfr3 a (Or.inl ha))
  have hbelow_orig : ∀ a < tOrigIdBase dstT vCap_h tM, mem6 a = mem1 a :=
    fun a ha => (hbelow_pi a (by omega)).trans (hfr2 a (Or.inl ha))
  have hbelow_dg : ∀ a < tDgTPtr dstT, mem6 a = tHdrMem mem dstT vCap_h eCap_h tM a :=
    fun a ha => (hbelow_orig a (by omega)).trans (hfr1 a (Or.inl ha))
  have hout1 : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem1 a = mem a := fun a ha =>
    (hfr1 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans
      (tHdrMem_out (Or.elim ha Or.inl (fun h => Or.inr (by omega))))
  have hout2 : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem2 a = mem a := fun a ha =>
    (hfr2 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout1 a ha)
  have hout3 : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem3 a = mem a := fun a ha =>
    (hfr3 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout2 a ha)
  have hout4 : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem4 a = mem a := fun a ha =>
    (hfr4 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout3 a ha)
  have hhdr : mem6 (dstT + tOffM) = tM ∧ mem6 (dstT + tOffDgTPtr) = tDgTPtr dstT ∧
      mem6 (dstT + tOffOrigIdPtr) = tOrigIdBase dstT vCap_h tM ∧
      mem6 (dstT + tOffPiPtr) = tPiBase dstT vCap_h tM ∧
      mem6 (dstT + tOffFrozenTailPtr) = tFrozenTailBase dstT vCap_h tM ∧
      mem6 (dstT + tOffFrozenHeadPtr) = tFrozenHeadBase dstT vCap_h tM ∧
      mem6 (dstT + tOffIdxOfEdgePtr) = tIdxOfEdgeBase dstT vCap_h tM ∧
      mem6 (dstT + tOffSplitScratchPtr) = tSplitScratchBase dstT vCap_h eCap_h tM := by
    have hm := tHdrMem_at mem dstT vCap_h eCap_h tM
    have hlt : ∀ k < tHdrSize, dstT + k < tDgTPtr dstT := fun k hk => by rw [← hB.1]; omega
    exact ⟨(hbelow_dg _ (hlt _ (by decide))).trans hm.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.2.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.2.2.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.2.2.2.2.1,
      (hbelow_dg _ (hlt _ (by decide))).trans hm.2.2.2.2.2.2.2⟩
  refine ⟨hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.1, hhdr.2.2.2.2.1,
    hhdr.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2,
    hlen, hnd, hmemL, ?_, ?_, fun i hi hlt => hIdone i (by omega) hi hlt, ?_, dgT, ?_, hdgTV, hdgTE, ?_⟩
  · intro i hi
    rw [hbelow_pi (tOrigIdBase dstT vCap_h tM + i) (by omega), hcp2 i (by omega),
        hout1 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hLO i hi
  · intro i hi
    have hiM : i < tM := by simp only [List.length_map] at hi; omega
    rw [hbelow_ft (tPiBase dstT vCap_h tM + i) (by omega), hcp3 i hiM,
        hout2 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hLPi i hi
  · intro e he hne
    by_contra hnone; push Not at hnone
    exact hne (hI0 e he fun j hj hj' hEq => hnone j hj' hEq (by simpa [hEq] using hIdone j hj hj' (hEq ▸ he)))
  · exact hdgT_dst.of_agree fun a _ ha2 => hbelow_orig a (by omega)
  · intro i hi
    obtain ⟨a, b, c, d, e, f⟩ := htrack i hi
    refine ⟨a, b, fun hnot => ?_, d, e, fun hnot => ?_⟩
    · rw [hbelow_fh (tFrozenTailBase dstT vCap_h tM + i) (by omega), hcp4 i (by omega),
          hout3 _ (hsrc_out _ (by omega) (by omega))]
      simpa [Nat.add_assoc] using c hnot
    · rw [hbelow_idx (tFrozenHeadBase dstT vCap_h tM + i) (by omega), hcp5 i (by omega),
          hout4 _ (hsrc_out _ (by omega) (by omega))]
      simpa [Nat.add_assoc] using f hnot

set_option maxHeartbeats 600000 in
lemma repackTBlockProc_runs {w : ℕ} {p : Program} {bCopy bRepDg : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {guestBase tPtr_g dstT vCap_g eCap_g vCap_h eCap_h tM : ℕ}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hRepDg : p.procs[bRepDg]? = some repackDynGraphProc)
    (hMemW : ∀ a, guestBase + tPtr_g ≤ a →
      a < guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM → mem a < 2 ^ w)
    (hT : TBlockAt (fun a => mem (guestBase + a)) tPtr_g vCap_g eCap_g tM G T_cur T₀ π tOrigList)
    (hvCap : vCap_g ≤ vCap_h) (_heCap : eCap_g ≤ eCap_h)
    (hsrc_w : guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM < 2 ^ w)
    (hdst_w : dstT + tBlockSize vCap_h eCap_h tM < 2 ^ w)
    (hdisj : guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM ≤ dstT ∨
             dstT + tBlockSize vCap_h eCap_h tM ≤ guestBase + tPtr_g)
    (hzero : ∀ a, dstT ≤ a → a < dstT + tBlockSize vCap_h eCap_h tM → mem a = 0) :
    ∃ st' c,
      Runs w p ω (repackTBlockProc bCopy bRepDg)
        (startState [guestBase + tPtr_g, dstT, vCap_h, eCap_h, guestBase] mem pos)
        (.returned 0) st' c ∧
      TBlockAt st'.mem dstT vCap_h eCap_h tM G T_cur T₀ π tOrigList ∧
      (∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → st'.mem a = mem a) ∧
      c ≤ 115 * G.n + 480 * tM + 400 := by
  suffices hmain : ∃ o st' c,
      Runs w p ω (repackTBlockProc bCopy bRepDg)
        (startState [guestBase + tPtr_g, dstT, vCap_h, eCap_h, guestBase] mem pos) o st' c ∧
      (o = .returned 0 ∧ TBlockAt st'.mem dstT vCap_h eCap_h tM G T_cur T₀ π tOrigList ∧
        (∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → st'.mem a = mem a)) ∧
      c ≤ 115 * G.n + 480 * tM + 400 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  rcases hT with ⟨hm, hdgP, horigP, hpiP, hftP, hfhP, hidxP, hscrP,
    hlen, hnd, hmemL, hLO, hLPi, hidx1, hidx2, dgT, hdgT, hdgTV, hdgTE, htrack⟩
  have hTfull : TBlockAt (fun a => mem (guestBase + a)) tPtr_g vCap_g eCap_g tM G T_cur T₀ π tOrigList :=
    ⟨hm, hdgP, horigP, hpiP, hftP, hfhP, hidxP, hscrP, hlen, hnd, hmemL, hLO, hLPi, hidx1, hidx2,
      dgT, hdgT, hdgTV, hdgTE, htrack⟩
  have hdgT_m : dgT.m ≤ 2 * tM := by
    have hsub : dgT.E ⊆ Finset.range (2 * tM) := fun e he => Finset.mem_range.mpr (hdgTE e he)
    calc dgT.m = dgT.E.card := rfl
      _ ≤ (Finset.range (2 * tM)).card := Finset.card_le_card hsub
      _ = 2 * tM := Finset.card_range _
  have hdgT_n : dgT.n = G.n := by dsimp [MGraph.n]; rw [hdgTV]
  have hS := tBlock_sub_le tPtr_g vCap_g eCap_g tM
  have hD := tBlock_sub_le dstT vCap_h eCap_h tM
  have hB := tBlock_bounds dstT vCap_h eCap_h tM
  have hdisj_sub : ∀ {s1 s2 d1 d2},
      guestBase + tPtr_g ≤ s1 → s2 ≤ guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM →
      dstT ≤ d1 → d2 ≤ dstT + tBlockSize vCap_h eCap_h tM → d2 ≤ s1 ∨ s2 ≤ d1 := fun h1 h2 h3 h4 =>
    Or.elim hdisj (fun h => Or.inr (Nat.le_trans h2 (Nat.le_trans h h3)))
      (fun h => Or.inl (Nat.le_trans h4 (Nat.le_trans h h1)))
  have hsrc_out : ∀ a, guestBase + tPtr_g ≤ a → a < guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM →
      a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a := fun _ h1 h2 =>
    Or.elim hdisj (fun h => Or.inl (Nat.lt_of_lt_of_le h2 h)) (fun h => Or.inr (Nat.le_trans h h1))
  clear hdisj
  have htM_w : tM < 2 ^ w := by dsimp [tBlockSize] at hdst_w; omega
  have h2tM1_w : 2 * tM + 1 < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hdst_w; omega
  have hvCap_w : vCap_h < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hdst_w; omega
  have hoffs : tOffM = 0 ∧ tOffDgTPtr = 1 ∧ tOffOrigIdPtr = 2 ∧ tOffPiPtr = 3 ∧
      tOffFrozenTailPtr = 4 ∧ tOffFrozenHeadPtr = 5 ∧ tOffIdxOfEdgePtr = 6 ∧
      tOffSplitScratchPtr = 7 ∧ tHdrSize = 8 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdg_sz_h : dynGraphSize vCap_h (2 * tM + 1) = 4 + 7 * vCap_h + 9 * (2 * tM + 1) := rfl
  refine runs_start_le ?_
  unfold repackTBlockProc startState
  refine runs_seq_assign_flat (v := tM) (by
    have hlt : guestBase + tPtr_g + tOffM < 2 ^ w := by omega
    have hval : mem (guestBase + tPtr_g + tOffM) = tM := by simpa [Nat.add_assoc] using hm
    eval_expr) ?_
  refine runs_seq_assign_flat (v := tDgTPtr dstT) (by rw [← hB.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := 2 * tM + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := tOrigIdBase dstT vCap_h tM) (by
    have h0a : tDgTPtr dstT + 4 < 2 ^ w := by omega
    have h0b : 7 * vCap_h < 2 ^ w := by omega
    have h1 : tDgTPtr dstT + 4 + 7 * vCap_h < 2 ^ w := by omega
    have h2 : 9 * (2 * tM + 1) < 2 ^ w := by omega
    have h3 : tDgTPtr dstT + 4 + 7 * vCap_h + 9 * (2 * tM + 1) = tOrigIdBase dstT vCap_h tM := by omega
    rw [← h3]; eval_expr) ?_
  refine runs_seq_assign_flat (v := tPiBase dstT vCap_h tM) (by rw [← hB.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := tFrozenTailBase dstT vCap_h tM) (by rw [← hB.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := tFrozenHeadBase dstT vCap_h tM) (by rw [← hB.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := tIdxOfEdgeBase dstT vCap_h tM) (by rw [← hB.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := tSplitScratchBase dstT vCap_h eCap_h tM)
    (by rw [← hB.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffM) (v := tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffDgTPtr) (v := tDgTPtr dstT) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffOrigIdPtr) (v := tOrigIdBase dstT vCap_h tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffPiPtr) (v := tPiBase dstT vCap_h tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffFrozenTailPtr) (v := tFrozenTailBase dstT vCap_h tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffFrozenHeadPtr) (v := tFrozenHeadBase dstT vCap_h tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffIdxOfEdgePtr) (v := tIdxOfEdgeBase dstT vCap_h tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstT + tOffSplitScratchPtr) (v := tSplitScratchBase dstT vCap_h eCap_h tM)
    (by eval_expr) (by eval_expr) ?_
  set mem0 := tHdrMem mem dstT vCap_h eCap_h tM
  change ∃ o st' c, Runs w p ω _ ⟨mem0, _, _⟩ o st' c ∧ _
  have hmem0_out : ∀ a, a < dstT ∨ dstT + tHdrSize ≤ a → mem0 a = mem a := fun _ ha => tHdrMem_out ha
  have hsrc_m0 : ∀ a, guestBase + tPtr_g ≤ a → a < guestBase + tPtr_g + tBlockSize vCap_g eCap_g tM →
      mem0 a = mem a := fun a h1 h2 =>
    hmem0_out a (Or.elim (hsrc_out a h1 h2) Or.inl (fun h => Or.inr (by omega)))
  have hdgT_rd : mem0 (guestBase + tPtr_g + tOffDgTPtr) = tDgTPtr tPtr_g := by
    rw [hsrc_m0 _ (by omega) (by omega)]; simpa [Nat.add_assoc] using hdgP
  refine runs_seq_call_body_flat
    (P_call := fun _ st1' => DynGraphAt st1'.mem (tDgTPtr dstT) vCap_h (2 * tM + 1) dgT ∧
      ∀ a, a < tDgTPtr dstT ∨ tDgTPtr dstT + dynGraphSize vCap_h (2 * tM + 1) ≤ a → st1'.mem a = mem0 a)
    hRepDg
    (vs := [guestBase + tDgTPtr tPtr_g, tDgTPtr dstT, vCap_h, 2 * tM + 1])
    (by have h1 : guestBase + tPtr_g + tOffDgTPtr < 2 ^ w := by omega
        have h2 : guestBase + tDgTPtr tPtr_g < 2 ^ w := by omega
        eval_expr)
    (by obtain ⟨st1', c1, hrun1, hdg1, hfr1, hc1⟩ :=
          repackDynGraphProc_runs (p := p) (ω := ω) (pos := pos) (dst := tDgTPtr dstT) hw
            (fun a ha1 ha2 => by rw [hsrc_m0 a (by omega) (by omega)]; exact hMemW a (by omega) (by omega))
            ((dynGraphAt_shift hdgT).of_agree fun a ha1 ha2 => hsrc_m0 a (by omega) (by omega))
            hvCap le_rfl (by omega) (by omega)
            ((hdisj_sub (by omega) (by omega) (by omega) (by omega)).symm)
            (fun a ha1 ha2 => by rw [hmem0_out a (Or.inr (by omega))]; exact hzero a (by omega) (by omega))
        exact ⟨0, st1', c1, hrun1, ⟨hdg1, hfr1⟩, hc1⟩)
    (fun _ st1' hret1 => ?_)
  rcases hret1 with ⟨hdgT_dst, hfr1⟩
  have hst1_out : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → st1'.mem a = mem a :=
    fun a ha => (hfr1 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans
      (hmem0_out a (Or.elim ha Or.inl (fun h => Or.inr (by omega))))
  have horigP_rd : st1'.mem (guestBase + tPtr_g + tOffOrigIdPtr) = tOrigIdBase tPtr_g vCap_g tM := by
    rw [hst1_out _ (hsrc_out _ (by omega) (by omega))]; simpa [Nat.add_assoc] using horigP
  refine runs_seq_assign_flat (v := guestBase + tOrigIdBase tPtr_g vCap_g tM) (by
    have h1 : guestBase + tPtr_g + tOffOrigIdPtr < 2 ^ w := by omega
    eval_expr) ?_
  refine runs_seq_call_flat hCopy
    (vs := [tOrigIdBase dstT vCap_h tM, guestBase + tOrigIdBase tPtr_g vCap_g tM, tM])
    (by eval_expr) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_sub (by omega) (by omega) (by omega) (by omega)⟩
    (fun _ mem2 pos2 hp2 => ?_)
  rcases hp2 with ⟨_, _, _, ha2, _, hcp2, hfr2⟩; cases ha2
  have hst2_out : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem2 a = mem a :=
    fun a ha => (hfr2 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst1_out a ha)
  have hpiP_rd : mem2 (guestBase + tPtr_g + tOffPiPtr) = tPiBase tPtr_g vCap_g tM := by
    rw [hst2_out _ (hsrc_out _ (by omega) (by omega))]; simpa [Nat.add_assoc] using hpiP
  refine runs_seq_call_flat hCopy
    (vs := [tPiBase dstT vCap_h tM, guestBase + tPiBase tPtr_g vCap_g tM, tM])
    (by have h1 : guestBase + tPtr_g + tOffPiPtr < 2 ^ w := by omega
        eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_sub (by omega) (by omega) (by omega) (by omega)⟩
    (fun _ mem3 pos3 hp3 => ?_)
  rcases hp3 with ⟨_, _, _, ha3, _, hcp3, hfr3⟩; cases ha3
  have hst3_out : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem3 a = mem a :=
    fun a ha => (hfr3 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst2_out a ha)
  have hftP_rd : mem3 (guestBase + tPtr_g + tOffFrozenTailPtr) = tFrozenTailBase tPtr_g vCap_g tM := by
    rw [hst3_out _ (hsrc_out _ (by omega) (by omega))]; simpa [Nat.add_assoc] using hftP
  refine runs_seq_call_flat hCopy
    (vs := [tFrozenTailBase dstT vCap_h tM, guestBase + tFrozenTailBase tPtr_g vCap_g tM, tM])
    (by have h1 : guestBase + tPtr_g + tOffFrozenTailPtr < 2 ^ w := by omega
        eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_sub (by omega) (by omega) (by omega) (by omega)⟩
    (fun _ mem4 pos4 hp4 => ?_)
  rcases hp4 with ⟨_, _, _, ha4, _, hcp4, hfr4⟩; cases ha4
  have hst4_out : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem4 a = mem a :=
    fun a ha => (hfr4 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst3_out a ha)
  have hfhP_rd : mem4 (guestBase + tPtr_g + tOffFrozenHeadPtr) = tFrozenHeadBase tPtr_g vCap_g tM := by
    rw [hst4_out _ (hsrc_out _ (by omega) (by omega))]; simpa [Nat.add_assoc] using hfhP
  refine runs_seq_call_flat hCopy
    (vs := [tFrozenHeadBase dstT vCap_h tM, guestBase + tFrozenHeadBase tPtr_g vCap_g tM, tM])
    (by have h1 : guestBase + tPtr_g + tOffFrozenHeadPtr < 2 ^ w := by omega
        eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_sub (by omega) (by omega) (by omega) (by omega)⟩
    (fun _ mem5 pos5 hp5 => ?_)
  rcases hp5 with ⟨_, _, _, ha5, _, hcp5, hfr5⟩; cases ha5
  have hst5_out : ∀ a, a < dstT ∨ dstT + tBlockSize vCap_h eCap_h tM ≤ a → mem5 a = mem a :=
    fun a ha => (hfr5 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst4_out a ha)
  have hidx_zero5 : ∀ e < eCap_h, mem5 (tIdxOfEdgeBase dstT vCap_h tM + e) = 0 := fun e he => by
    rw [hfr5 _ (Or.inr (by omega)), hfr4 _ (Or.inr (by omega)), hfr3 _ (Or.inr (by omega)),
        hfr2 _ (Or.inr (by omega)), hfr1 _ (Or.inr (by omega)), hmem0_out _ (Or.inr (by omega))]
    exact hzero _ (by omega) (by omega)
  refine runs_seq_triple_le
    (repackT_idxLoop (srcOrig := guestBase + tOrigIdBase tPtr_g vCap_g tM)
      (dstIdx := tIdxOfEdgeBase dstT vCap_h tM)
      hw htM_w (by omega) (by omega)
      (fun i hi => hMemW (guestBase + tOrigIdBase tPtr_g vCap_g tM + i) (by omega) (by omega)) hlen hnd
      (fun i hi => by simpa [Nat.add_assoc] using hLO i hi)
      (fun i hi => Or.elim (hsrc_out (guestBase + tOrigIdBase tPtr_g vCap_g tM + i) (by omega) (by omega))
        (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      (fun i hi => hst5_out (guestBase + tOrigIdBase tPtr_g vCap_g tM + i)
        (hsrc_out (guestBase + tOrigIdBase tPtr_g vCap_g tM + i) (by omega) (by omega))) hidx_zero5)
    ⟨by simp, by simp, by simp, by simp, rfl⟩
    (fun st6 hI => ?_)
  rcases hI with ⟨hfr6, hIdone, hI0⟩
  refine runs_ret_le (by eval_expr) ⟨rfl,
    assemble_TBlockAt hTfull hdgT_dst hdgTV hdgTE htrack hsrc_out hfr1 hfr2 hcp2 hfr3 hcp3
      hfr4 hcp4 hfr5 hcp5 hfr6 hIdone hI0,
    fun a ha => (hfr6 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst5_out a ha)⟩ (by
    simp [memCopyContract, argsSize, Expr.size]; omega)

end MinCostFlow.SparseCore.Program
