module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
import WordRAM.Tactic

/-!
# Sparse Repack Verification for `AuxAt`

Proves `repackAuxProc_runs`, copying a guest `AuxAt` block into fresh zeroed host memory at host
capacity `vCap_h` in time `≤ 60 * (n0 * auxLogCap n0) + 160 * n0 + 450`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program

private def auxHdrMem17 (m : ℕ → ℕ) (dstAux vCap_h n0 logCap : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update m
    (dstAux + auxOffVIdxPtr) (auxVIdxBase dstAux))
    (dstAux + auxOffVListPtr) (auxVListBase dstAux vCap_h))
    (dstAux + auxOffT0ParentPtr) (auxT0ParentBase dstAux vCap_h n0))
    (dstAux + auxOffT0ParentTreeIdxPtr) (auxT0ParentTreeIdxBase dstAux vCap_h n0))
    (dstAux + auxOffT0DepthPtr) (auxT0DepthBase dstAux vCap_h n0))
    (dstAux + auxOffLogCap) logCap)
    (dstAux + auxOffUpVPtr) (auxUpVBase dstAux vCap_h n0))
    (dstAux + auxOffUpMinIdxPtr) (auxUpMinIdxBase dstAux vCap_h n0))
    (dstAux + auxOffThParentPtr) (auxThParentBase dstAux vCap_h n0))
    (dstAux + auxOffOrigVertPtr) (auxOrigVertBase dstAux vCap_h n0))
    (dstAux + auxOffIsOrigVertPtr) (auxIsOrigVertBase dstAux vCap_h n0))
    (dstAux + auxOffQBufAPtr) (auxQBufABase dstAux vCap_h n0))
    (dstAux + auxOffQBufBPtr) (auxQBufBBase dstAux vCap_h n0))
    (dstAux + auxOffVisAPtr) (auxVisABase dstAux vCap_h n0))
    (dstAux + auxOffVisBPtr) (auxVisBBase dstAux vCap_h n0))
    (dstAux + auxOffThStackPtr) (auxThStackBase dstAux vCap_h n0))
    (dstAux + auxOffFSplitScratchPtr) (auxFSplitScratchBase dstAux vCap_h n0)

private lemma auxHdrMem17_out {m : ℕ → ℕ} {dstAux vCap_h n0 logCap a : ℕ}
    (ha : a < dstAux ∨ dstAux + 17 ≤ a) :
    auxHdrMem17 m dstAux vCap_h n0 logCap a = m a := by
  have h1 : ∀ k < 17, a ≠ dstAux + k := fun k hk => by omega
  unfold auxHdrMem17
  repeat rw [Function.update_of_ne (h1 _ (by decide))]

private def auxHdrMem (m : ℕ → ℕ) (dstAux vCap_h n0 logCap r0Idx : ℕ) : ℕ → ℕ :=
  Function.update (auxHdrMem17 m dstAux vCap_h n0 logCap) (dstAux + auxOffR0Idx) r0Idx

private lemma auxHdrMem_out {m : ℕ → ℕ} {dstAux vCap_h n0 logCap r0Idx a : ℕ}
    (ha : a < dstAux ∨ dstAux + auxHdrSize ≤ a) :
    auxHdrMem m dstAux vCap_h n0 logCap r0Idx a = m a := by
  unfold auxHdrMem
  rw [Function.update_of_ne (by dsimp [auxOffR0Idx, auxHdrSize] at ha ⊢; omega)]
  exact auxHdrMem17_out (by dsimp [auxHdrSize] at ha; omega)

private lemma auxHdrMem_at (m : ℕ → ℕ) (dstAux vCap_h n0 logCap r0Idx : ℕ) :
    let m0 := auxHdrMem m dstAux vCap_h n0 logCap r0Idx
    m0 (dstAux + auxOffVIdxPtr) = auxVIdxBase dstAux ∧
    m0 (dstAux + auxOffVListPtr) = auxVListBase dstAux vCap_h ∧
    m0 (dstAux + auxOffT0ParentPtr) = auxT0ParentBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffT0ParentTreeIdxPtr) = auxT0ParentTreeIdxBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffT0DepthPtr) = auxT0DepthBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffLogCap) = logCap ∧
    m0 (dstAux + auxOffUpVPtr) = auxUpVBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffUpMinIdxPtr) = auxUpMinIdxBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffThParentPtr) = auxThParentBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffOrigVertPtr) = auxOrigVertBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffIsOrigVertPtr) = auxIsOrigVertBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffQBufAPtr) = auxQBufABase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffQBufBPtr) = auxQBufBBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffVisAPtr) = auxVisABase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffVisBPtr) = auxVisBBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffThStackPtr) = auxThStackBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffFSplitScratchPtr) = auxFSplitScratchBase dstAux vCap_h n0 ∧
    m0 (dstAux + auxOffR0Idx) = r0Idx := by
  have hne : ∀ {j k : ℕ}, j ≠ k → dstAux + j ≠ dstAux + k := fun h => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold auxHdrMem auxHdrMem17 <;>
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (hne (by decide))])

private lemma aux_sub_le (p vCap n0 : ℕ) :
    p + auxHdrSize = auxVIdxBase p ∧
    auxVIdxBase p + vCap = auxVListBase p vCap ∧
    auxVListBase p vCap + n0 = auxT0ParentBase p vCap n0 ∧
    auxT0ParentBase p vCap n0 + n0 = auxT0ParentTreeIdxBase p vCap n0 ∧
    auxT0ParentTreeIdxBase p vCap n0 + n0 = auxT0DepthBase p vCap n0 ∧
    auxT0DepthBase p vCap n0 + n0 = auxUpVBase p vCap n0 ∧
    auxUpVBase p vCap n0 + n0 * auxLogCap n0 = auxUpMinIdxBase p vCap n0 ∧
    auxUpMinIdxBase p vCap n0 + n0 * auxLogCap n0 = auxThParentBase p vCap n0 ∧
    auxThParentBase p vCap n0 + n0 = auxOrigVertBase p vCap n0 ∧
    auxOrigVertBase p vCap n0 + vCap = auxIsOrigVertBase p vCap n0 ∧
    auxIsOrigVertBase p vCap n0 + vCap = auxQBufABase p vCap n0 ∧
    auxQBufABase p vCap n0 + 2 * vCap = auxVisABase p vCap n0 ∧
    auxVisABase p vCap n0 + vCap = auxVisBBase p vCap n0 ∧
    auxVisBBase p vCap n0 + vCap ≤ p + auxSize vCap n0 := by
  have hend := aux_end_eq p vCap n0
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by dsimp [auxVisABase, auxQBufBBase]; omega, rfl,
    by dsimp [auxFSplitScratchBase, auxThStackBase] at hend; omega⟩

private lemma repackAux_scatterLoop {w : ℕ} {p : Program} {mem mem7 : ℕ → ℕ}
    {srcVL srcOV dstVIdx dstVL dstOV dstIsOV dstQA vCap_g vCap_h n0 : ℕ}
    {S : LSFState} {vList : List ℕ}
    (hw : 20 < 2 ^ w) (hn0_w : n0 < 2 ^ w)
    (hsrcVL_w : srcVL + n0 < 2 ^ w) (hsrcOV_w : srcOV + vCap_g < 2 ^ w)
    (hdstVIdx_w : dstVIdx + vCap_h < 2 ^ w)
    (hdstOV_w : dstOV + vCap_h < 2 ^ w) (hdstIsOV_w : dstIsOV + vCap_h < 2 ^ w)
    (hsep1 : dstVIdx + vCap_h = dstVL) (hsep2 : dstVL ≤ dstOV)
    (hsep3 : dstOV + vCap_h = dstIsOV) (hsep4 : dstIsOV + vCap_h = dstQA)
    (hMemW : ∀ v < vCap_g, mem (srcOV + v) < 2 ^ w)
    (hvlen : vList.length = n0) (hvnd : vList.Nodup) (hvmem : ∀ v, v ∈ vList ↔ v ∈ S.T₀.V)
    (hvLA : ∀ i (hi : i < vList.length), mem (srcVL + i) = vList[i])
    (hvCap : vCap_g ≤ vCap_h) (hvlt : ∀ v ∈ S.T₀.V, v < vCap_g)
    (hsrcVL_disj : ∀ i < n0, srcVL + i < dstVIdx ∨ dstQA ≤ srcVL + i)
    (hsrcOV_disj : ∀ v < vCap_g, srcOV + v < dstVIdx ∨ dstQA ≤ srcOV + v)
    (hmem7_vl : ∀ i < n0, mem7 (srcVL + i) = mem (srcVL + i))
    (hmem7_ov : ∀ v < vCap_g, mem7 (srcOV + v) = mem (srcOV + v))
    (hzero_vidx : ∀ v < vCap_h, mem7 (dstVIdx + v) = 0)
    (hzero_isov : ∀ v < vCap_h, mem7 (dstIsOV + v) = 0) :
    Triple w p
      (fun st => st.regs 3 = n0 ∧ st.regs 6 = dstVIdx ∧ st.regs 15 = dstOV ∧
        st.regs 16 = dstIsOV ∧ st.regs 23 = srcVL ∧ st.regs 24 = srcOV ∧ st.mem = mem7)
      (forRange 25 (.const 0) (.reg 3)
        (.assign 26 (.load (.bin .add (.reg 23) (.reg 25))) ;;
         .store (.bin .add (.reg 6) (.reg 26)) (.bin .add (.reg 25) (.const 1)) ;;
         .store (.bin .add (.reg 16) (.reg 26)) (.const 1) ;;
         .store (.bin .add (.reg 15) (.reg 26)) (.load (.bin .add (.reg 24) (.reg 26)))))
      (normalPost fun st =>
        (∀ a, a < dstVIdx ∨ (dstVL ≤ a ∧ a < dstOV) ∨ dstQA ≤ a → st.mem a = mem7 a) ∧
        (∀ j (_hj : j < n0), ∀ (hj' : j < vList.length),
          let v := vList[j]
          st.mem (dstVIdx + v) = j + 1 ∧ st.mem (dstIsOV + v) = 1 ∧
          st.mem (dstOV + v) = mem (srcOV + v)) ∧
        (∀ v < vCap_h, (∀ j (_hj : j < n0), ∀ (hj' : j < vList.length), vList[j] ≠ v) →
          st.mem (dstVIdx + v) = 0 ∧ st.mem (dstIsOV + v) = 0))
      (fun _ => 45 * n0 + 7) := by
  let SInv : ℕ → State → Prop := fun i st =>
    st.regs 3 = n0 ∧ st.regs 6 = dstVIdx ∧ st.regs 15 = dstOV ∧ st.regs 16 = dstIsOV ∧
    st.regs 23 = srcVL ∧ st.regs 24 = srcOV ∧ st.regs 25 = i ∧
    (∀ a, a < dstVIdx ∨ (dstVL ≤ a ∧ a < dstOV) ∨ dstQA ≤ a → st.mem a = mem7 a) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < vList.length),
      let v := vList[j]
      st.mem (dstVIdx + v) = j + 1 ∧ st.mem (dstIsOV + v) = 1 ∧
      st.mem (dstOV + v) = mem (srcOV + v)) ∧
    (∀ v < vCap_h, (∀ j (hj : j < i), ∀ (hj' : j < vList.length), vList[j] ≠ v) →
      st.mem (dstVIdx + v) = 0 ∧ st.mem (dstIsOV + v) = 0)
  have hloop : Triple w p
      (fun st => st.regs 3 = n0 ∧ st.regs 6 = dstVIdx ∧ st.regs 15 = dstOV ∧
        st.regs 16 = dstIsOV ∧ st.regs 23 = srcVL ∧ st.regs 24 = srcOV ∧ st.mem = mem7)
      (forRange 25 (.const 0) (.reg 3)
        (.assign 26 (.load (.bin .add (.reg 23) (.reg 25))) ;;
         .store (.bin .add (.reg 6) (.reg 26)) (.bin .add (.reg 25) (.const 1)) ;;
         .store (.bin .add (.reg 16) (.reg 26)) (.const 1) ;;
         .store (.bin .add (.reg 15) (.reg 26)) (.load (.bin .add (.reg 24) (.reg 26)))))
      (normalPost (SInv n0)) (fun _ => 45 * n0 + 7) := by
    refine (Triple.forRange_const 36 0 n0 (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q3, q6, q15, q16, q23, q24, hmeq⟩
        exact ⟨by eval_expr, q3, q6, q15, q16, q23, q24, by simp, fun _ _ => by rw [hmeq],
          fun j hj _ => by omega, fun v hv _ => by rw [hmeq]; exact ⟨hzero_vidx v hv, hzero_isov v hv⟩⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨q3, q6, q15, q16, q23, q24, q25, hfrS, hSdone, hS0⟩
        have hiL : i < vList.length := by omega
        set v := vList[i]
        have hv_T0 : v ∈ S.T₀.V := (hvmem v).mp (List.getElem_mem hiL)
        have hv_lt : v < vCap_g := hvlt v hv_T0
        have hv_rd : st.mem (srcVL + i) = v := by
          rw [hfrS _ (Or.elim (hsrcVL_disj i hilt) Or.inl (fun h => Or.inr (Or.inr h))),
              hmem7_vl i hilt, hvLA i hiL]
        set ov := mem (srcOV + v)
        have hovW : ov < 2 ^ w := hMemW v hv_lt
        have hv_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < vList.length), vList[j] ≠ v := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp hvnd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        change ∃ o st' c, Runs w p ω' _ ⟨st.mem, st.regs, st.pos⟩ o st' c ∧ _
        refine runs_start_le ?_
        refine runs_seq_assign_flat (v := v) (by
          have hlt : srcVL + i < 2 ^ w := by omega
          eval_expr) ?_
        refine runs_seq_store_flat (x := dstVIdx + v) (v := i + 1) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dstIsOV + v) (v := 1) (by eval_expr) (by eval_expr) ?_
        refine runs_store_le (x := dstOV + v) (v := ov)
          (by eval_expr)
          (by have hlt : srcOV + v < 2 ^ w := by omega
              have hdis := hsrcOV_disj v hv_lt
              have hrd : Function.update (Function.update st.mem (dstVIdx + v) (i + 1))
                  (dstIsOV + v) 1 (srcOV + v) = ov := by
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    hfrS _ (Or.elim hdis Or.inl (fun h => Or.inr (Or.inr h))), hmem7_ov v hv_lt]
              eval_expr) ?_ (by wram_cost)
        refine ⟨⟨by simp [q3], by simp [q6], by simp [q15], by simp [q16], by simp [q23],
          by simp [q24], by simp,
          fun a ha => by
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfrS a ha,
          fun j hj hj' => ?_, fun u hu hne => ?_⟩, by simp [q25]⟩
        · by_cases hji : j = i
          · subst hji
            refine ⟨?_, ?_, Function.update_self _ _ _⟩
            · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            · dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]
          · have hvj_ne := hv_ne_prev j (by omega) hj'
            have hvj_lt := hvlt _ ((hvmem _).mp (List.getElem_mem hj'))
            have hd := hSdone j (by omega) hj'
            refine ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hd.1,
              by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hd.2.1,
              by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hd.2.2⟩
        · have huv : u ≠ v := (hne i (by omega) hiL).symm
          have h0 := hS0 u hu fun j hj hj' => hne j (by omega) hj'
          refine ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h0.1,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h0.2⟩)).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  exact hloop.conseq (fun _ h => h) (fun o st h => by
    cases o with
    | normal => rcases h with ⟨_, _, _, _, _, _, _, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    | returned _ => exact h.elim) (fun _ _ => le_rfl)

set_option maxHeartbeats 800000 in
private lemma assemble_AuxAt {mem mem1 mem2 mem3 mem4 mem5 mem6 mem7 mem8 : ℕ → ℕ}
    {guestBase auxPtr_g dstAux vCap_g vCap_h n0 tM : ℕ}
    {S : LSFState} {tOrigList vList : List ℕ}
    {t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ} {upV upMinIdx : ℕ → ℕ → ℕ}
    (hAux : AuxAt (fun a => mem (guestBase + a)) auxPtr_g vCap_g n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx)
    (hGV_eq : S.G.V = S.T₀.V) (hvlt : ∀ v ∈ S.T₀.V, v < vCap_g)
    (hsrc_out : ∀ a, guestBase + auxPtr_g ≤ a → a < guestBase + auxPtr_g + auxSize vCap_g n0 →
      a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a)
    (hzero : ∀ a, dstAux ≤ a → a < dstAux + auxSize vCap_h n0 → mem a = 0)
    (hfr1 : ∀ a, a < auxVListBase dstAux vCap_h ∨ auxVListBase dstAux vCap_h + n0 ≤ a →
      mem1 a = auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) (mem (guestBase + (auxPtr_g + auxOffR0Idx))) a)
    (hcp1 : ∀ i < n0, mem1 (auxVListBase dstAux vCap_h + i) =
      auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) (mem (guestBase + (auxPtr_g + auxOffR0Idx)))
        (guestBase + auxVListBase auxPtr_g vCap_g + i))
    (hfr2 : ∀ a, a < auxT0ParentBase dstAux vCap_h n0 ∨ auxT0ParentBase dstAux vCap_h n0 + n0 ≤ a → mem2 a = mem1 a)
    (hcp2 : ∀ i < n0, mem2 (auxT0ParentBase dstAux vCap_h n0 + i) = mem1 (guestBase + auxT0ParentBase auxPtr_g vCap_g n0 + i))
    (hfr3 : ∀ a, a < auxT0ParentTreeIdxBase dstAux vCap_h n0 ∨ auxT0ParentTreeIdxBase dstAux vCap_h n0 + n0 ≤ a → mem3 a = mem2 a)
    (hcp3 : ∀ i < n0, mem3 (auxT0ParentTreeIdxBase dstAux vCap_h n0 + i) = mem2 (guestBase + auxT0ParentTreeIdxBase auxPtr_g vCap_g n0 + i))
    (hfr4 : ∀ a, a < auxT0DepthBase dstAux vCap_h n0 ∨ auxT0DepthBase dstAux vCap_h n0 + n0 ≤ a → mem4 a = mem3 a)
    (hcp4 : ∀ i < n0, mem4 (auxT0DepthBase dstAux vCap_h n0 + i) = mem3 (guestBase + auxT0DepthBase auxPtr_g vCap_g n0 + i))
    (hfr5 : ∀ a, a < auxUpVBase dstAux vCap_h n0 ∨ auxUpVBase dstAux vCap_h n0 + n0 * auxLogCap n0 ≤ a → mem5 a = mem4 a)
    (hcp5 : ∀ i < n0 * auxLogCap n0, mem5 (auxUpVBase dstAux vCap_h n0 + i) = mem4 (guestBase + auxUpVBase auxPtr_g vCap_g n0 + i))
    (hfr6 : ∀ a, a < auxUpMinIdxBase dstAux vCap_h n0 ∨ auxUpMinIdxBase dstAux vCap_h n0 + n0 * auxLogCap n0 ≤ a → mem6 a = mem5 a)
    (hcp6 : ∀ i < n0 * auxLogCap n0, mem6 (auxUpMinIdxBase dstAux vCap_h n0 + i) = mem5 (guestBase + auxUpMinIdxBase auxPtr_g vCap_g n0 + i))
    (hfr7 : ∀ a, a < auxThParentBase dstAux vCap_h n0 ∨ auxThParentBase dstAux vCap_h n0 + n0 ≤ a → mem7 a = mem6 a)
    (hcp7 : ∀ i < n0, mem7 (auxThParentBase dstAux vCap_h n0 + i) = mem6 (guestBase + auxThParentBase auxPtr_g vCap_g n0 + i))
    (hfr8 : ∀ a, a < auxVIdxBase dstAux ∨
        (auxVListBase dstAux vCap_h ≤ a ∧ a < auxOrigVertBase dstAux vCap_h n0) ∨
        auxQBufABase dstAux vCap_h n0 ≤ a → mem8 a = mem7 a)
    (hSdone : ∀ j (_hj : j < n0), ∀ (hj' : j < vList.length),
      let v := vList[j]
      mem8 (auxVIdxBase dstAux + v) = j + 1 ∧
      mem8 (auxIsOrigVertBase dstAux vCap_h n0 + v) = 1 ∧
      mem8 (auxOrigVertBase dstAux vCap_h n0 + v) = mem (guestBase + auxOrigVertBase auxPtr_g vCap_g n0 + v))
    (hS0 : ∀ v < vCap_h, (∀ j (_hj : j < n0), ∀ (hj' : j < vList.length), vList[j] ≠ v) →
      mem8 (auxVIdxBase dstAux + v) = 0 ∧ mem8 (auxIsOrigVertBase dstAux vCap_h n0 + v) = 0) :
    AuxAt mem8 dstAux vCap_h n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx := by
  dsimp only [AuxAt] at hAux ⊢
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hvlen, hvnd, hvmem, htlen, hvLA, _, _, hr0lt, hr0v, hp, hpe, hd, hup, hth, hthR0,
    hdR0, ht0Edge, hUpProp, hThProp, _, hOrig, _⟩
  set r0Idx := mem (guestBase + (auxPtr_g + auxOffR0Idx))
  have hS := aux_sub_le auxPtr_g vCap_g n0
  have hD := aux_sub_le dstAux vCap_h n0
  have hout0 : ∀ a, a < dstAux ∨ dstAux + auxHdrSize ≤ a →
      auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) r0Idx a = mem a := fun _ ha => auxHdrMem_out ha
  have hout1 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem1 a = mem a := fun a ha =>
    (hfr1 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans
      (hout0 a (Or.elim ha Or.inl (fun h => Or.inr (by omega))))
  have hout2 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem2 a = mem a := fun a ha =>
    (hfr2 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout1 a ha)
  have hout3 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem3 a = mem a := fun a ha =>
    (hfr3 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout2 a ha)
  have hout4 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem4 a = mem a := fun a ha =>
    (hfr4 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout3 a ha)
  have hout5 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem5 a = mem a := fun a ha =>
    (hfr5 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout4 a ha)
  have hout6 : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem6 a = mem a := fun a ha =>
    (hfr6 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hout5 a ha)
  have hbelow_th : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxOrigVertBase dstAux vCap_h n0 → mem8 a = mem7 a :=
    fun a h1 h2 => hfr8 a (Or.inr (Or.inl ⟨h1, h2⟩))
  have hbelow_upM : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxThParentBase dstAux vCap_h n0 → mem8 a = mem6 a :=
    fun a h1 h2 => (hbelow_th a h1 (by omega)).trans (hfr7 a (Or.inl h2))
  have hbelow_upV : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxUpMinIdxBase dstAux vCap_h n0 → mem8 a = mem5 a :=
    fun a h1 h2 => (hbelow_upM a h1 (by omega)).trans (hfr6 a (Or.inl h2))
  have hbelow_dep : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxUpVBase dstAux vCap_h n0 → mem8 a = mem4 a :=
    fun a h1 h2 => (hbelow_upV a h1 (by omega)).trans (hfr5 a (Or.inl h2))
  have hbelow_pti : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxT0DepthBase dstAux vCap_h n0 → mem8 a = mem3 a :=
    fun a h1 h2 => (hbelow_dep a h1 (by omega)).trans (hfr4 a (Or.inl h2))
  have hbelow_par : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxT0ParentTreeIdxBase dstAux vCap_h n0 → mem8 a = mem2 a :=
    fun a h1 h2 => (hbelow_pti a h1 (by omega)).trans (hfr3 a (Or.inl h2))
  have hbelow_vl : ∀ a, auxVListBase dstAux vCap_h ≤ a → a < auxT0ParentBase dstAux vCap_h n0 → mem8 a = mem1 a :=
    fun a h1 h2 => (hbelow_par a h1 (by omega)).trans (hfr2 a (Or.inl h2))
  have hhdr :
      mem8 (dstAux + auxOffVIdxPtr) = auxVIdxBase dstAux ∧
      mem8 (dstAux + auxOffVListPtr) = auxVListBase dstAux vCap_h ∧
      mem8 (dstAux + auxOffT0ParentPtr) = auxT0ParentBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffT0ParentTreeIdxPtr) = auxT0ParentTreeIdxBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffT0DepthPtr) = auxT0DepthBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffLogCap) = auxLogCap n0 ∧
      mem8 (dstAux + auxOffUpVPtr) = auxUpVBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffUpMinIdxPtr) = auxUpMinIdxBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffThParentPtr) = auxThParentBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffOrigVertPtr) = auxOrigVertBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffIsOrigVertPtr) = auxIsOrigVertBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffQBufAPtr) = auxQBufABase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffQBufBPtr) = auxQBufBBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffVisAPtr) = auxVisABase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffVisBPtr) = auxVisBBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffThStackPtr) = auxThStackBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffFSplitScratchPtr) = auxFSplitScratchBase dstAux vCap_h n0 ∧
      mem8 (dstAux + auxOffR0Idx) = r0Idx := by
    have hhdr_eq : ∀ off < auxHdrSize, mem8 (dstAux + off) = auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) r0Idx (dstAux + off) :=
      fun off hoff =>
        (hfr8 _ (Or.inl (by omega))).trans ((hfr7 _ (Or.inl (by omega))).trans
          ((hfr6 _ (Or.inl (by omega))).trans ((hfr5 _ (Or.inl (by omega))).trans
            ((hfr4 _ (Or.inl (by omega))).trans ((hfr3 _ (Or.inl (by omega))).trans
              ((hfr2 _ (Or.inl (by omega))).trans (hfr1 _ (Or.inl (by omega)))))))))
    have hm := auxHdrMem_at mem dstAux vCap_h n0 (auxLogCap n0) r0Idx
    exact ⟨(hhdr_eq _ (by decide)).trans hm.1, (hhdr_eq _ (by decide)).trans hm.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (hhdr_eq _ (by decide)).trans hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  refine ⟨hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.1, hhdr.2.2.2.2.1, hhdr.2.2.2.2.2.1,
    hhdr.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.2.1,
    hhdr.2.2.2.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hvlen, hvnd, hvmem, htlen, ?_, fun i hi => (hSdone i (by omega) hi).1, ?_, hr0lt, hr0v,
    ?_, ?_, ?_, ?_, ?_, hthR0, hdR0, ht0Edge, hUpProp, hThProp, ?_, ?_, ?_⟩
  · intro i hi
    rw [hbelow_vl _ (Nat.le_add_right _ _) (by omega), hcp1 i (by omega),
        hout0 _ (Or.elim (hsrc_out _ (by omega) (by omega)) Or.inl (fun h => Or.inr (by omega)))]
    simpa [Nat.add_assoc] using hvLA i hi
  · intro v hv hvnot
    exact (hS0 v hv fun j _ hj' hEq => hvnot (hEq ▸ (hvmem _).mp (List.getElem_mem hj'))).1
  · intro i hi
    rw [hbelow_par _ (by omega) (by omega), hcp2 i hi, hout1 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hp i hi
  · intro i hi
    rw [hbelow_pti _ (by omega) (by omega), hcp3 i hi, hout2 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hpe i hi
  · intro i hi
    rw [hbelow_dep _ (by omega) (by omega), hcp4 i hi, hout3 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hd i hi
  · intro i hi j hj
    have hij : i * auxLogCap n0 + j < n0 * auxLogCap n0 := by
      calc i * auxLogCap n0 + j < (i + 1) * auxLogCap n0 := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ n0 * auxLogCap n0 := Nat.mul_le_mul_right _ hi
    have h1 : mem8 (auxUpVBase dstAux vCap_h n0 + (i * auxLogCap n0 + j)) =
        mem (guestBase + (auxUpVBase auxPtr_g vCap_g n0 + (i * auxLogCap n0 + j))) := by
      rw [hbelow_upV _ (by omega) (by omega),
          hcp5 _ hij, hout4 _ (hsrc_out _ (by omega) (by omega)), Nat.add_assoc]
    have h2 : mem8 (auxUpMinIdxBase dstAux vCap_h n0 + (i * auxLogCap n0 + j)) =
        mem (guestBase + (auxUpMinIdxBase auxPtr_g vCap_g n0 + (i * auxLogCap n0 + j))) := by
      rw [hbelow_upM _ (by omega) (by omega),
          hcp6 _ hij, hout5 _ (hsrc_out _ (by omega) (by omega)), Nat.add_assoc]
    rw [h1, h2]; exact hup i hi j hj
  · intro i hi
    rw [hbelow_th _ (by omega) (by omega), hcp7 i hi, hout6 _ (hsrc_out _ (by omega) (by omega))]
    simpa [Nat.add_assoc] using hth i hi
  · intro v hv
    split_ifs with hvT
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hvmem v).mpr hvT)
      exact (hSdone j (by omega) hj).2.1
    · exact (hS0 v hv fun j _ hj' hEq => hvT (hEq ▸ (hvmem _).mp (List.getElem_mem hj'))).2
  · intro u hu _
    have huT : u ∈ S.T₀.V := hGV_eq ▸ hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hvmem u).mpr huT)
    rw [(hSdone j (by omega) hj).2.2]
    simpa [Nat.add_assoc] using hOrig _ hu (hvlt _ huT)
  · intro v hv
    clear hS hhdr hbelow_th hbelow_upM hbelow_upV hbelow_dep hbelow_pti hbelow_par hbelow_vl
    have hze : ∀ a, auxOrigVertBase dstAux vCap_h n0 ≤ a → a < dstAux + auxSize vCap_h n0 → mem7 a = 0 :=
      fun a ha1 ha2 => by
        rw [hfr7 a (Or.inr (by omega)), hfr6 a (Or.inr (by omega)), hfr5 a (Or.inr (by omega)),
            hfr4 a (Or.inr (by omega)), hfr3 a (Or.inr (by omega)), hfr2 a (Or.inr (by omega)),
            hfr1 a (Or.inr (by omega)), hout0 a (Or.inr (by omega))]
        exact hzero a (by omega) ha2
    exact ⟨(hfr8 (auxVisABase dstAux vCap_h n0 + v) (Or.inr (Or.inr (by omega)))).trans
        (hze (auxVisABase dstAux vCap_h n0 + v) (by omega) (by omega)),
      (hfr8 (auxVisBBase dstAux vCap_h n0 + v) (Or.inr (Or.inr (by omega)))).trans
        (hze (auxVisBBase dstAux vCap_h n0 + v) (by omega) (by omega))⟩

private lemma aux_sub_ranges (p vCap n0 : ℕ) :
    (p ≤ auxVListBase p vCap ∧ auxVListBase p vCap + n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxT0ParentBase p vCap n0 ∧ auxT0ParentBase p vCap n0 + n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxT0ParentTreeIdxBase p vCap n0 ∧ auxT0ParentTreeIdxBase p vCap n0 + n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxT0DepthBase p vCap n0 ∧ auxT0DepthBase p vCap n0 + n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxUpVBase p vCap n0 ∧ auxUpVBase p vCap n0 + n0 * auxLogCap n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxUpMinIdxBase p vCap n0 ∧ auxUpMinIdxBase p vCap n0 + n0 * auxLogCap n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxThParentBase p vCap n0 ∧ auxThParentBase p vCap n0 + n0 ≤ p + auxSize vCap n0) ∧
    (p ≤ auxOrigVertBase p vCap n0 ∧ auxOrigVertBase p vCap n0 + vCap ≤ p + auxSize vCap n0) ∧
    auxHdrSize ≤ auxSize vCap n0 := by
  have h := aux_sub_le p vCap n0
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩

private lemma aux_copy_step {w : ℕ} {p : Program} {bCopy : ℕ} {ω : ℕ → Bool}
    {mem mem_i : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {s2 : Stmt}
    {Q : Outcome → State → Prop} {acc B : ℕ}
    {guestBase auxPtr_g dstAux vCap_g vCap_h n0 dstReg lenReg off dstBase srcBase len : ℕ}
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hr0 : regs 0 = guestBase + auxPtr_g) (hr4 : regs 4 = guestBase)
    (hrDst : regs dstReg = dstBase) (hrLen : regs lenReg = len)
    (hoff_lt : off < auxSize vCap_g n0)
    (hsrc_rd : mem (guestBase + (auxPtr_g + off)) = srcBase)
    (hdst_lo : dstAux ≤ dstBase) (hdst_hi : dstBase + len ≤ dstAux + auxSize vCap_h n0)
    (hsrc_lo : auxPtr_g ≤ srcBase) (hsrc_hi : srcBase + len ≤ auxPtr_g + auxSize vCap_g n0)
    (hdst_w : dstAux + auxSize vCap_h n0 < 2 ^ w)
    (hsrc_w : guestBase + auxPtr_g + auxSize vCap_g n0 < 2 ^ w)
    (hdisj : guestBase + auxPtr_g + auxSize vCap_g n0 ≤ dstAux ∨
             dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g)
    (hst_out : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem_i a = mem a)
    (hnext : ∀ mem' pos',
      (∀ i < len, mem' (dstBase + i) = mem_i (guestBase + srcBase + i)) →
      (∀ a, a < dstBase ∨ dstBase + len ≤ a → mem' a = mem_i a) →
      (∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem' a = mem a) →
      ∃ o st' c, Runs w p ω s2 ⟨mem', Function.update regs 25 0, pos'⟩ o st' c ∧
        Q o st' ∧ acc + (20 * len + 25) + c ≤ B) :
    ∃ o st' c,
      Runs w p ω (.call 25 bCopy [.reg dstReg, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const off))), .reg lenReg] ;; s2)
        ⟨mem_i, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B := by
  have hmem_rd : mem_i (guestBase + auxPtr_g + off) = srcBase := by
    have hout : guestBase + auxPtr_g + off < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g + off :=
      Or.elim hdisj (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))
    rw [hst_out _ hout, Nat.add_assoc]; exact hsrc_rd
  have hdisj_sub : dstBase + len ≤ guestBase + srcBase ∨ guestBase + srcBase + len ≤ dstBase :=
    Or.elim hdisj (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))
  clear hdisj
  refine runs_seq_call_flat hCopy
    (vs := [dstBase, guestBase + srcBase, len])
    (by have h1 : off < 2 ^ w := by omega
        have h2 : guestBase + auxPtr_g + off < 2 ^ w := by omega
        have h3 : guestBase + srcBase < 2 ^ w := by omega
        eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_sub⟩
    (fun ret mem' pos' hp => ?_)
  rcases hp with ⟨_, _, _, ha, hret, hcp, hfr⟩; cases ha; subst hret
  have hst' : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem' a = mem a := fun a ha =>
    (hfr a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans (hst_out a ha)
  have hrun := hnext mem' pos' hcp hfr hst'
  rcases hrun with ⟨o, st', c, hr, hQ, hc⟩
  exact ⟨o, st', c, hr, hQ, by simp [memCopyContract, argsSize, Expr.size] at hc ⊢; omega⟩

private def repackAuxTail (bCopy : ℕ) : Stmt :=
  .assign 23 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffVListPtr)))) ;;
  .call 25 bCopy [.reg 7, .reg 23, .reg 3] ;;
  .call 25 bCopy [.reg 8, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0ParentPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 9, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0ParentTreeIdxPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 10, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0DepthPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 11, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffUpVPtr))), .reg 12] ;;
  .call 25 bCopy [.reg 13, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffUpMinIdxPtr))), .reg 12] ;;
  .call 25 bCopy [.reg 14, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffThParentPtr))), .reg 3] ;;
  .assign 24 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffOrigVertPtr)))) ;;
  forRange 25 (.const 0) (.reg 3)
    (.assign 26 (.load (.bin .add (.reg 23) (.reg 25))) ;;
     .store (.bin .add (.reg 6) (.reg 26)) (.bin .add (.reg 25) (.const 1)) ;;
     .store (.bin .add (.reg 16) (.reg 26)) (.const 1) ;;
     .store (.bin .add (.reg 15) (.reg 26)) (.load (.bin .add (.reg 24) (.reg 26)))) ;;
  .ret (.const 0)

set_option maxHeartbeats 600000 in
private lemma repackAuxTail_runs {w : ℕ} {p : Program} {bCopy : ℕ} {mem : ℕ → ℕ}
    {regs : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    {guestBase auxPtr_g dstAux vCap_g vCap_h n0 tM : ℕ}
    {S : LSFState} {tOrigList vList : List ℕ}
    {t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ} {upV upMinIdx : ℕ → ℕ → ℕ}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hMemW : ∀ a, guestBase + auxPtr_g ≤ a →
      a < guestBase + auxPtr_g + auxSize vCap_g n0 → mem a < 2 ^ w)
    (hAux : AuxAt (fun a => mem (guestBase + a)) auxPtr_g vCap_g n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx)
    (hGV_eq : S.G.V = S.T₀.V) (hvCap : vCap_g ≤ vCap_h)
    (hvlt : ∀ v ∈ S.T₀.V, v < vCap_g)
    (hsrc_w : guestBase + auxPtr_g + auxSize vCap_g n0 < 2 ^ w)
    (hdst_w : dstAux + auxSize vCap_h n0 < 2 ^ w)
    (hdisj : guestBase + auxPtr_g + auxSize vCap_g n0 ≤ dstAux ∨
             dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g)
    (hzero : ∀ a, dstAux ≤ a → a < dstAux + auxSize vCap_h n0 → mem a = 0)
    (hr0 : regs 0 = guestBase + auxPtr_g) (hr3 : regs 3 = n0) (hr4 : regs 4 = guestBase)
    (hr6 : regs 6 = auxVIdxBase dstAux) (hr7 : regs 7 = auxVListBase dstAux vCap_h)
    (hr8 : regs 8 = auxT0ParentBase dstAux vCap_h n0)
    (hr9 : regs 9 = auxT0ParentTreeIdxBase dstAux vCap_h n0)
    (hr10 : regs 10 = auxT0DepthBase dstAux vCap_h n0)
    (hr11 : regs 11 = auxUpVBase dstAux vCap_h n0)
    (hr12 : regs 12 = n0 * auxLogCap n0)
    (hr13 : regs 13 = auxUpMinIdxBase dstAux vCap_h n0)
    (hr14 : regs 14 = auxThParentBase dstAux vCap_h n0)
    (hr15 : regs 15 = auxOrigVertBase dstAux vCap_h n0)
    (hr16 : regs 16 = auxIsOrigVertBase dstAux vCap_h n0)
    {c_pre B : ℕ} (hcB : c_pre + (40 * (n0 * auxLogCap n0) + 150 * n0 + 210) ≤ B) :
    ∃ o st' c,
      Runs w p ω (repackAuxTail bCopy)
        ⟨auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) (mem (guestBase + (auxPtr_g + auxOffR0Idx))),
          regs, pos⟩ o st' c ∧
      (o = .returned 0 ∧
        AuxAt st'.mem dstAux vCap_h n0 tM S tOrigList vList
          t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx ∧
        (∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → st'.mem a = mem a)) ∧
      c_pre + c ≤ B := by
  have h1 := hAux.2.1
  have h2 := hAux.2.2.1
  have h3 := hAux.2.2.2.1
  have h4 := hAux.2.2.2.2.1
  have h6 := hAux.2.2.2.2.2.2.1
  have h7 := hAux.2.2.2.2.2.2.2.1
  have h8 := hAux.2.2.2.2.2.2.2.2.1
  have h9 := hAux.2.2.2.2.2.2.2.2.2.1
  have hvlen := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvnd := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvmem := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvLA := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set r0Idx := mem (guestBase + (auxPtr_g + auxOffR0Idx))
  set mem0 := auxHdrMem mem dstAux vCap_h n0 (auxLogCap n0) r0Idx
  have hSr := aux_sub_ranges auxPtr_g vCap_g n0
  have hDr := aux_sub_ranges dstAux vCap_h n0
  have hhdr20 : auxHdrSize = 20 := rfl
  have hsrc_out : ∀ a, guestBase + auxPtr_g ≤ a → a < guestBase + auxPtr_g + auxSize vCap_g n0 →
      a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a := fun _ h1 h2 =>
    Or.elim hdisj (fun h => Or.inl (Nat.lt_of_lt_of_le h2 h)) (fun h => Or.inr (Nat.le_trans h h1))
  have hmem0_out : ∀ a, a < dstAux ∨ dstAux + auxHdrSize ≤ a → mem0 a = mem a := fun _ ha => auxHdrMem_out ha
  have hdisj_vl : auxVListBase dstAux vCap_h + n0 ≤ guestBase + auxVListBase auxPtr_g vCap_g ∨
      guestBase + auxVListBase auxPtr_g vCap_g + n0 ≤ auxVListBase dstAux vCap_h :=
    Or.elim hdisj (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))
  have hdisj_fn : Unit → guestBase + auxPtr_g + auxSize vCap_g n0 ≤ dstAux ∨
      dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g := fun _ => hdisj
  clear hdisj
  unfold repackAuxTail
  refine runs_seq_assign_flat (v := guestBase + auxVListBase auxPtr_g vCap_g) (by
    have hlt1 : guestBase + auxPtr_g + auxOffVListPtr < 2 ^ w := by change guestBase + auxPtr_g + 1 < 2 ^ w; omega
    have hlt2 : guestBase + auxVListBase auxPtr_g vCap_g < 2 ^ w := by omega
    have hrd : mem0 (guestBase + auxPtr_g + auxOffVListPtr) = auxVListBase auxPtr_g vCap_g := by
      have ho : auxOffVListPtr < auxSize vCap_g n0 := by change 1 < auxSize vCap_g n0; omega
      rw [hmem0_out _ (Or.elim (hsrc_out _ (by omega) (by omega)) Or.inl (fun h => Or.inr (by omega)))]
      simpa [Nat.add_assoc] using h1
    have h1w : auxOffVListPtr < 2 ^ w := by change 1 < 2 ^ w; omega
    eval_expr) ?_
  refine runs_seq_call_flat hCopy
    (vs := [auxVListBase dstAux vCap_h, guestBase + auxVListBase auxPtr_g vCap_g, n0])
    (by eval_expr) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hdisj_vl⟩
    (fun _ mem1 pos1 hp1 => ?_)
  rcases hp1 with ⟨_, _, _, ha1, _, hcp1, hfr1⟩; cases ha1
  have hst1_out : ∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → mem1 a = mem a := fun a ha =>
    (hfr1 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))).trans
      (hmem0_out a (Or.elim ha Or.inl (fun h => Or.inr (by omega))))
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr8]) (by simp [hr3])
    (by change 2 < auxSize vCap_g n0; omega) h2 hDr.2.1.1 hDr.2.1.2 hSr.2.1.1 hSr.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst1_out
    fun mem2 pos2 hcp2 hfr2 hst2_out => ?_
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr9]) (by simp [hr3])
    (by change 3 < auxSize vCap_g n0; omega) h3 hDr.2.2.1.1 hDr.2.2.1.2 hSr.2.2.1.1 hSr.2.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst2_out
    fun mem3 pos3 hcp3 hfr3 hst3_out => ?_
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr10]) (by simp [hr3])
    (by change 4 < auxSize vCap_g n0; omega) h4 hDr.2.2.2.1.1 hDr.2.2.2.1.2 hSr.2.2.2.1.1 hSr.2.2.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst3_out
    fun mem4 pos4 hcp4 hfr4 hst4_out => ?_
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr11]) (by simp [hr12])
    (by change 6 < auxSize vCap_g n0; omega) h6 hDr.2.2.2.2.1.1 hDr.2.2.2.2.1.2 hSr.2.2.2.2.1.1 hSr.2.2.2.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst4_out
    fun mem5 pos5 hcp5 hfr5 hst5_out => ?_
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr13]) (by simp [hr12])
    (by change 7 < auxSize vCap_g n0; omega) h7 hDr.2.2.2.2.2.1.1 hDr.2.2.2.2.2.1.2 hSr.2.2.2.2.2.1.1 hSr.2.2.2.2.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst5_out
    fun mem6 pos6 hcp6 hfr6 hst6_out => ?_
  refine aux_copy_step hCopy (by simp [hr0]) (by simp [hr4]) (by simp [hr14]) (by simp [hr3])
    (by change 8 < auxSize vCap_g n0; omega) h8 hDr.2.2.2.2.2.2.1.1 hDr.2.2.2.2.2.2.1.2 hSr.2.2.2.2.2.2.1.1 hSr.2.2.2.2.2.2.1.2 hdst_w hsrc_w (hdisj_fn ()) hst6_out
    fun mem7 pos7 hcp7 hfr7 hst7_out => ?_
  have hD := aux_sub_le dstAux vCap_h n0
  have hst7_zero_range : ∀ a, (auxVIdxBase dstAux ≤ a ∧ a < auxVListBase dstAux vCap_h) ∨
      (auxOrigVertBase dstAux vCap_h n0 ≤ a ∧ a < dstAux + auxSize vCap_h n0) → mem7 a = 0 := fun a ha => by
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · rw [hfr7 a (Or.inl (by omega)), hfr6 a (Or.inl (by omega)), hfr5 a (Or.inl (by omega)),
          hfr4 a (Or.inl (by omega)), hfr3 a (Or.inl (by omega)), hfr2 a (Or.inl (by omega)),
          hfr1 a (Or.inl ha2), hmem0_out a (Or.inr (by omega))]
      exact hzero a (by omega) (by omega)
    · rw [hfr7 a (Or.inr (by omega)), hfr6 a (Or.inr (by omega)), hfr5 a (Or.inr (by omega)),
          hfr4 a (Or.inr (by omega)), hfr3 a (Or.inr (by omega)), hfr2 a (Or.inr (by omega)),
          hfr1 a (Or.inr (by omega)), hmem0_out a (Or.inr (by omega))]
      exact hzero a (by omega) ha2
  refine runs_seq_assign_flat (v := guestBase + auxOrigVertBase auxPtr_g vCap_g n0) (by
    have h9w : auxOffOrigVertPtr < 2 ^ w := by change 9 < 2 ^ w; omega
    have hlt1 : guestBase + auxPtr_g + auxOffOrigVertPtr < 2 ^ w := by change guestBase + auxPtr_g + 9 < 2 ^ w; omega
    have hlt2 : guestBase + auxOrigVertBase auxPtr_g vCap_g n0 < 2 ^ w := by omega
    have hrd : mem7 (guestBase + auxPtr_g + auxOffOrigVertPtr) = auxOrigVertBase auxPtr_g vCap_g n0 := by
      have ho : auxOffOrigVertPtr < auxSize vCap_g n0 := by change 9 < auxSize vCap_g n0; omega
      rw [hst7_out _ (hsrc_out _ (by omega) (by omega))]; simpa [Nat.add_assoc] using h9
    eval_expr) ?_
  refine runs_seq_triple_le
    (repackAux_scatterLoop
      (srcVL := guestBase + auxVListBase auxPtr_g vCap_g)
      (srcOV := guestBase + auxOrigVertBase auxPtr_g vCap_g n0)
      (dstVIdx := auxVIdxBase dstAux) (dstVL := auxVListBase dstAux vCap_h)
      (dstOV := auxOrigVertBase dstAux vCap_h n0) (dstIsOV := auxIsOrigVertBase dstAux vCap_h n0)
      (dstQA := auxQBufABase dstAux vCap_h n0)
      hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hD.2.1 (by omega) hD.2.2.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2.2.2.1
      (fun v hv => hMemW (guestBase + auxOrigVertBase auxPtr_g vCap_g n0 + v) (by omega) (by omega))
      hvlen hvnd hvmem
      (fun i hi => by simpa [Nat.add_assoc] using hvLA i hi) hvCap hvlt
      (fun i hi => Or.elim (hsrc_out (guestBase + auxVListBase auxPtr_g vCap_g + i) (by omega) (by omega))
        (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      (fun v hv => Or.elim (hsrc_out (guestBase + auxOrigVertBase auxPtr_g vCap_g n0 + v) (by omega) (by omega))
        (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      (fun i hi => hst7_out (guestBase + auxVListBase auxPtr_g vCap_g + i)
        (hsrc_out (guestBase + auxVListBase auxPtr_g vCap_g + i) (by omega) (by omega)))
      (fun v hv => hst7_out (guestBase + auxOrigVertBase auxPtr_g vCap_g n0 + v)
        (hsrc_out (guestBase + auxOrigVertBase auxPtr_g vCap_g n0 + v) (by omega) (by omega)))
      (fun v hv => hst7_zero_range (auxVIdxBase dstAux + v) (Or.inl ⟨by omega, by omega⟩))
      (fun v hv => hst7_zero_range (auxIsOrigVertBase dstAux vCap_h n0 + v) (Or.inr ⟨by omega, by omega⟩)))
    ⟨by simp [hr3], by simp [hr6], by simp [hr15], by simp [hr16], by simp, by simp, rfl⟩
    (fun st8 hS8 => ?_)
  rcases hS8 with ⟨hfr8, hSdone, hS0⟩
  refine runs_ret_le (by eval_expr) ⟨rfl,
    assemble_AuxAt hAux hGV_eq hvlt hsrc_out hzero hfr1 hcp1 hfr2 hcp2 hfr3 hcp3 hfr4 hcp4
      hfr5 hcp5 hfr6 hcp6 hfr7 hcp7 hfr8 hSdone hS0,
    fun a ha => (hfr8 a (Or.elim ha (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inr (by omega))))).trans (hst7_out a ha)⟩ (by
    simp [memCopyContract, argsSize, Expr.size]; omega)

set_option maxHeartbeats 1200000 in
lemma repackAuxProc_runs {w : ℕ} {p : Program} {bCopy bLog : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {guestBase auxPtr_g dstAux vCap_g vCap_h n0 tM : ℕ}
    {S : LSFState} {tOrigList vList : List ℕ}
    {t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ} {upV upMinIdx : ℕ → ℕ → ℕ}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hLog : MeetsContract w p bLog log2Contract)
    (hMemW : ∀ a, guestBase + auxPtr_g ≤ a →
      a < guestBase + auxPtr_g + auxSize vCap_g n0 → mem a < 2 ^ w)
    (hAux : AuxAt (fun a => mem (guestBase + a)) auxPtr_g vCap_g n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx)
    (hGV_eq : S.G.V = S.T₀.V) (hn0_pos : 1 ≤ n0) (hvCap : vCap_g ≤ vCap_h)
    (hvlt : ∀ v ∈ S.T₀.V, v < vCap_g)
    (hsrc_w : guestBase + auxPtr_g + auxSize vCap_g n0 < 2 ^ w)
    (hdst_w : dstAux + auxSize vCap_h n0 < 2 ^ w)
    (hdisj : guestBase + auxPtr_g + auxSize vCap_g n0 ≤ dstAux ∨
             dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g)
    (hzero : ∀ a, dstAux ≤ a → a < dstAux + auxSize vCap_h n0 → mem a = 0) :
    ∃ st' c,
      Runs w p ω (repackAuxProc bCopy bLog)
        (startState [guestBase + auxPtr_g, dstAux, vCap_h, n0, guestBase] mem pos)
        (.returned 0) st' c ∧
      AuxAt st'.mem dstAux vCap_h n0 tM S tOrigList vList
        t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx ∧
      (∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → st'.mem a = mem a) ∧
      c ≤ 60 * (n0 * auxLogCap n0) + 160 * n0 + 450 := by
  suffices hmain : ∃ o st' c,
      Runs w p ω (repackAuxProc bCopy bLog)
        (startState [guestBase + auxPtr_g, dstAux, vCap_h, n0, guestBase] mem pos) o st' c ∧
      (o = .returned 0 ∧
        AuxAt st'.mem dstAux vCap_h n0 tM S tOrigList vList
          t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx ∧
        (∀ a, a < dstAux ∨ dstAux + auxSize vCap_h n0 ≤ a → st'.mem a = mem a)) ∧
      c ≤ 60 * (n0 * auxLogCap n0) + 160 * n0 + 450 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  have h5 : mem (guestBase + (auxPtr_g + auxOffLogCap)) = auxLogCap n0 := hAux.2.2.2.2.2.1
  set r0Idx := mem (guestBase + (auxPtr_g + auxOffR0Idx))
  have hlog_le : Nat.log 2 n0 ≤ auxLogCap n0 := by
    dsimp [auxLogCap]; exact Nat.le_succ_of_le (Nat.log_mono_right (Nat.le_succ n0))
  have hlog_w : auxLogCap n0 < 2 ^ w := by
    have : 1 * auxLogCap n0 ≤ n0 * auxLogCap n0 := Nat.mul_le_mul_right _ hn0_pos
    dsimp [auxSize] at this hdst_w ⊢; omega
  have hhld_eq : (Nat.log 2 n0 + 1) * (Nat.log 2 n0 + 1 + 1) + 2 = hldDepthBound n0 + 2 := rfl
  have hD := aux_sub_le dstAux vCap_h n0
  have hS_hdr : auxHdrSize ≤ auxSize vCap_g n0 := by dsimp [auxSize]; omega
  have hend := aux_end_eq dstAux vCap_h n0
  have hth_eq : auxThStackBase dstAux vCap_h n0 = auxVisBBase dstAux vCap_h n0 + vCap_h := rfl
  have hfs_eq : auxFSplitScratchBase dstAux vCap_h n0 = auxThStackBase dstAux vCap_h n0 + (hldDepthBound n0 + 2) := rfl
  have hqb_eq : auxQBufBBase dstAux vCap_h n0 = auxQBufABase dstAux vCap_h n0 + vCap_h := rfl
  have hva_eq : auxVisABase dstAux vCap_h n0 = auxQBufBBase dstAux vCap_h n0 + vCap_h := rfl
  have hoffs : auxOffVIdxPtr = 0 ∧ auxOffVListPtr = 1 ∧ auxOffT0ParentPtr = 2 ∧
      auxOffT0ParentTreeIdxPtr = 3 ∧ auxOffT0DepthPtr = 4 ∧ auxOffLogCap = 5 ∧
      auxOffUpVPtr = 6 ∧ auxOffUpMinIdxPtr = 7 ∧ auxOffThParentPtr = 8 ∧
      auxOffOrigVertPtr = 9 ∧ auxOffIsOrigVertPtr = 10 ∧ auxOffQBufAPtr = 11 ∧
      auxOffQBufBPtr = 12 ∧ auxOffVisAPtr = 13 ∧ auxOffVisBPtr = 14 ∧
      auxOffThStackPtr = 15 ∧ auxOffFSplitScratchPtr = 16 ∧ auxOffR0Idx = 17 ∧
      auxHdrSize = 20 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdisj_fn : Unit → guestBase + auxPtr_g + auxSize vCap_g n0 ≤ dstAux ∨
      dstAux + auxSize vCap_h n0 ≤ guestBase + auxPtr_g := fun _ => hdisj
  clear hdisj
  refine runs_start_le ?_
  unfold repackAuxProc startState
  refine runs_seq_assign_flat (v := auxLogCap n0) (by
    have hlt : guestBase + auxPtr_g + auxOffLogCap < 2 ^ w := by omega
    have hv : mem (guestBase + auxPtr_g + auxOffLogCap) = auxLogCap n0 := by simpa [Nat.add_assoc] using h5
    eval_expr) ?_
  refine runs_seq_assign_flat (v := auxVIdxBase dstAux) (by rw [← hD.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxVListBase dstAux vCap_h) (by rw [← hD.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxT0ParentBase dstAux vCap_h n0) (by rw [← hD.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxT0ParentTreeIdxBase dstAux vCap_h n0) (by rw [← hD.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxT0DepthBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxUpVBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := n0 * auxLogCap n0) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := auxUpMinIdxBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxThParentBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxOrigVertBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxIsOrigVertBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxQBufABase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxQBufBBase dstAux vCap_h n0) (by rw [hqb_eq]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxVisABase dstAux vCap_h n0) (by rw [hva_eq]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxVisBBase dstAux vCap_h n0) (by rw [← hD.2.2.2.2.2.2.2.2.2.2.2.2.1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := auxThStackBase dstAux vCap_h n0) (by rw [hth_eq]; eval_expr) ?_
  refine runs_seq_call_flat hLog
    (by eval_expr) (by intro v hv; simp at hv; subst hv; omega) ⟨n0, rfl, hn0_pos⟩
    (fun retLog memL posL hpostL => ?_)
  rcases hpostL with ⟨_, hargL, hmemL, hretL⟩
  cases hargL; subst hretL; subst memL
  have hlog_le_hld : Nat.log 2 n0 + 2 ≤ hldDepthBound n0 := by
    dsimp [hldDepthBound]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  refine runs_seq_assign_flat (v := Nat.log 2 n0 + 1) (by
    have : Nat.log 2 n0 + 1 < 2 ^ w := by omega
    eval_expr) ?_
  refine runs_seq_assign_flat (v := hldDepthBound n0 + 2) (by
    have h1 : Nat.log 2 n0 + 1 + 1 < 2 ^ w := by omega
    have h2 : (Nat.log 2 n0 + 1) * (Nat.log 2 n0 + 1 + 1) < 2 ^ w := by change hldDepthBound n0 < 2 ^ w; omega
    have h3 : (Nat.log 2 n0 + 1) * (Nat.log 2 n0 + 1 + 1) + 2 = hldDepthBound n0 + 2 := hhld_eq
    have h4 : hldDepthBound n0 + 2 < 2 ^ w := by omega
    simp [Expr.eval, BinOp.eval, Function.update, h1, h2, h3, h4, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := auxFSplitScratchBase dstAux vCap_h n0) (by rw [hfs_eq]; eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffVIdxPtr) (v := auxVIdxBase dstAux) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffVListPtr) (v := auxVListBase dstAux vCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffT0ParentPtr) (v := auxT0ParentBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffT0ParentTreeIdxPtr) (v := auxT0ParentTreeIdxBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffT0DepthPtr) (v := auxT0DepthBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffLogCap) (v := auxLogCap n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffUpVPtr) (v := auxUpVBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffUpMinIdxPtr) (v := auxUpMinIdxBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffThParentPtr) (v := auxThParentBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffOrigVertPtr) (v := auxOrigVertBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffIsOrigVertPtr) (v := auxIsOrigVertBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffQBufAPtr) (v := auxQBufABase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffQBufBPtr) (v := auxQBufBBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffVisAPtr) (v := auxVisABase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffVisBPtr) (v := auxVisBBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffThStackPtr) (v := auxThStackBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dstAux + auxOffFSplitScratchPtr) (v := auxFSplitScratchBase dstAux vCap_h n0) (by eval_expr) (by eval_expr) ?_
  set mem17 := auxHdrMem17 mem dstAux vCap_h n0 (auxLogCap n0)
  change ∃ o st' c, Runs w p ω _ ⟨mem17, _, _⟩ o st' c ∧ _
  refine runs_seq_store_flat (x := dstAux + auxOffR0Idx) (v := r0Idx)
    (by eval_expr)
    (by have hlt : guestBase + auxPtr_g + auxOffR0Idx < 2 ^ w := by omega
        have hr0w : r0Idx < 2 ^ w := hMemW (guestBase + (auxPtr_g + auxOffR0Idx)) (by omega) (by omega)
        have hsrc_out_hdr : guestBase + auxPtr_g + auxOffR0Idx < dstAux ∨
            dstAux + 17 ≤ guestBase + auxPtr_g + auxOffR0Idx :=
          Or.elim (hdisj_fn ()) (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))
        have hrd : mem17 (guestBase + auxPtr_g + auxOffR0Idx) = r0Idx := by
          dsimp only [mem17]; rw [auxHdrMem17_out hsrc_out_hdr, Nat.add_assoc]
        eval_expr) ?_
  exact repackAuxTail_runs hw hCopy hMemW hAux hGV_eq hvCap hvlt hsrc_w hdst_w (hdisj_fn ()) hzero
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [log2Contract, argsSize, Expr.size]
        have hlog_n : Nat.log 2 n0 ≤ n0 * auxLogCap n0 :=
          le_trans hlog_le (by simpa using Nat.mul_le_mul_right (auxLogCap n0) hn0_pos)
        omega)

end MinCostFlow.SparseCore.Program
