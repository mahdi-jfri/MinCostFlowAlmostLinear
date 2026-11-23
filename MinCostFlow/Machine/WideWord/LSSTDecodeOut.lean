module

public import MinCostFlow.Machine.WideWord.LSSTEncodeDecodeBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of `decodeOutProc`

This file defines `decodeOutCost` and `decodeOutContract`, and proves
`decodeOut_meetsContract` showing that `decodeOutProc` decodes the multiword tree edges
and appends inactive-vertex bridges into host arrays matching `decodeAN19Output`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Cost, contract, and decoding prefixes -/

def decodeOutCost (outLen inactLen L_sim : ℕ) : ℕ :=
  outLen * (25 * L_sim + 80) + 45 * inactLen + 60

def decodeOutContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ (out B inact origs : List ℕ)
      (outLimbsPtr m₁ bArr inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr : ℕ),
      args = [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀, L_sim,
        origsPtr, outOrigPtr, outBridgePtr, outHdrPtr] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ 1 ≤ L_sim ∧
      m₁ + B.length < 2 ^ w ∧
      outLimbsPtr + out.length * L_sim < 2 ^ w ∧
      bArr + B.length < 2 ^ w ∧
      inactArr + inact.length < 2 ^ w ∧
      origsPtr + m₁ < 2 ^ w ∧ origs.length = m₁ ∧
      outOrigPtr + out.length < 2 ^ w ∧
      outBridgePtr + 2 * (out.length + inact.length) < 2 ^ w ∧
      outHdrPtr + 2 < 2 ^ w ∧
      r₀ < 2 ^ w ∧
      (∀ x ∈ origs, x < 2 ^ w) ∧ (∀ x ∈ B, x < 2 ^ w) ∧ (∀ x ∈ inact, x < 2 ^ w) ∧
      DisjointRanges outOrigPtr out.length outBridgePtr (2 * (out.length + inact.length)) ∧
      DisjointRanges outOrigPtr out.length outHdrPtr 2 ∧
      DisjointRanges outBridgePtr (2 * (out.length + inact.length)) outHdrPtr 2 ∧
      DisjointRanges outOrigPtr out.length outLimbsPtr (out.length * L_sim) ∧
      DisjointRanges outOrigPtr out.length origsPtr m₁ ∧
      DisjointRanges outOrigPtr out.length bArr B.length ∧
      DisjointRanges outOrigPtr out.length inactArr inact.length ∧
      DisjointRanges outBridgePtr (2 * (out.length + inact.length)) outLimbsPtr (out.length * L_sim) ∧
      DisjointRanges outBridgePtr (2 * (out.length + inact.length)) origsPtr m₁ ∧
      DisjointRanges outBridgePtr (2 * (out.length + inact.length)) bArr B.length ∧
      DisjointRanges outBridgePtr (2 * (out.length + inact.length)) inactArr inact.length ∧
      DisjointRanges outHdrPtr 2 outLimbsPtr (out.length * L_sim) ∧
      DisjointRanges outHdrPtr 2 origsPtr m₁ ∧
      DisjointRanges outHdrPtr 2 bArr B.length ∧
      DisjointRanges outHdrPtr 2 inactArr inact.length ∧
      (∀ i (hi : i < out.length), LimbsAt mem (outLimbsPtr + i * L_sim) L_sim h (out[i]'hi) ∧ out[i]'hi < 2 ^ w) ∧
      ListAt mem origsPtr origs ∧ ListAt mem bArr B ∧ ListAt mem inactArr inact
  post args mem ret mem' :=
    ∃ (out B inact origs : List ℕ)
      (outLimbsPtr m₁ bArr inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr : ℕ),
      args = [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀, L_sim,
        origsPtr, outOrigPtr, outBridgePtr, outHdrPtr] ∧
      let origEdges := (out.filter fun j => decide (j < m₁)).map fun j => origs.getD j 0
      let bridgePairs := (out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
          (fun j => (r₀, B.getD (j - m₁) 0)) ++ inact.map fun u => (r₀, u)
      ret = 0 ∧
      mem' outHdrPtr = origEdges.length ∧
      mem' (outHdrPtr + 1) = bridgePairs.length ∧
      ListAt mem' outOrigPtr origEdges ∧
      ListAt mem' outBridgePtr (bridgePairs.flatMap fun p => [p.1, p.2]) ∧
      (∀ a, (a < outOrigPtr ∨ outOrigPtr + out.length ≤ a) →
        (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) →
        (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → mem' a = mem a) ∧
      origs.length = m₁ ∧
      (∀ i (hi : i < out.length), LimbsAt mem (outLimbsPtr + i * L_sim) L_sim h (out[i]'hi)) ∧
      ListAt mem origsPtr origs ∧ ListAt mem bArr B ∧ ListAt mem inactArr inact
  cost args _ := decodeOutCost (args.getD 1 0) (args.getD 5 0) (args.getD 8 0)

/-! ### Register and prefix helpers -/

private structure DOutRegs (s : State) (outLimbsPtr outLen m₁ B_len bArr inactLen inactArr
    r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr : ℕ) : Prop where
  r0 : s.regs 0 = outLimbsPtr
  r1 : s.regs 1 = outLen
  r2 : s.regs 2 = m₁
  r3 : s.regs 3 = B_len
  r4 : s.regs 4 = bArr
  r5 : s.regs 5 = inactLen
  r6 : s.regs 6 = inactArr
  r7 : s.regs 7 = r₀
  r8 : s.regs 8 = L_sim
  r9 : s.regs 9 = origsPtr
  r10 : s.regs 10 = outOrigPtr
  r11 : s.regs 11 = outBridgePtr
  r12 : s.regs 12 = outHdrPtr

private lemma dOutRegs_upd {s st' : State} {outLimbsPtr outLen m₁ B_len bArr inactLen inactArr
    r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr r v : ℕ}
    (h : DOutRegs s outLimbsPtr outLen m₁ B_len bArr inactLen inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr)
    (hreg : st'.regs = Function.update s.regs r v) (hr : 13 ≤ r) :
    DOutRegs st' outLimbsPtr outLen m₁ B_len bArr inactLen inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr :=
  ⟨by rw [hreg, Function.update_of_ne (by omega)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r9,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r10,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r12⟩

private lemma dOutRegs_of_eq {s st' : State} {outLimbsPtr outLen m₁ B_len bArr inactLen inactArr
    r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr : ℕ}
    (h : DOutRegs s outLimbsPtr outLen m₁ B_len bArr inactLen inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr)
    (heq : st'.regs = s.regs) :
    DOutRegs st' outLimbsPtr outLen m₁ B_len bArr inactLen inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr :=
  ⟨by rw [heq]; exact h.r0,
   by rw [heq]; exact h.r1,
   by rw [heq]; exact h.r2,
   by rw [heq]; exact h.r3,
   by rw [heq]; exact h.r4,
   by rw [heq]; exact h.r5,
   by rw [heq]; exact h.r6,
   by rw [heq]; exact h.r7,
   by rw [heq]; exact h.r8,
   by rw [heq]; exact h.r9,
   by rw [heq]; exact h.r10,
   by rw [heq]; exact h.r11,
   by rw [heq]; exact h.r12⟩

private def origPref (out : List ℕ) (m₁ : ℕ) (origs : List ℕ) (k : ℕ) : List ℕ :=
  ((out.take k).filter fun j => decide (j < m₁)).map fun j => origs.getD j 0

private def brPref (out : List ℕ) (m₁ : ℕ) (B : List ℕ) (r₀ k : ℕ) : List (ℕ × ℕ) :=
  ((out.take k).filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
    fun j => (r₀, B.getD (j - m₁) 0)

private lemma origPref_length_le (out : List ℕ) (m₁ : ℕ) (origs : List ℕ) (k : ℕ) :
    (origPref out m₁ origs k).length ≤ k := by
  dsimp only [origPref]
  rw [List.length_map]
  exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

private lemma brPref_length_le (out : List ℕ) (m₁ : ℕ) (B : List ℕ) (r₀ k : ℕ) :
    (brPref out m₁ B r₀ k).length ≤ k := by
  dsimp only [brPref]
  rw [List.length_map]
  exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

private lemma mem_disj_of_ranges {mem₁ mem₂ : ℕ → ℕ} {a lenA b lenB c lenC : ℕ}
    (hb : DisjointRanges a lenA b lenB) (hc : DisjointRanges a lenA c lenC)
    (hfr : ∀ p, (p < b ∨ b + lenB ≤ p) → (p < c ∨ c + lenC ≤ p) → mem₁ p = mem₂ p) :
    ∀ p, a ≤ p → p < a + lenA → mem₁ p = mem₂ p := fun p hp1 hp2 =>
  hfr p
    (hb.elim (fun h1 => Or.inl (by linarith only [h1, hp2]))
      (fun h1 => Or.inr (by linarith only [h1, hp1])))
    (hc.elim (fun h1 => Or.inl (by linarith only [h1, hp2]))
      (fun h1 => Or.inr (by linarith only [h1, hp1])))

/-! ### First decoding loop (`decodeOut_loop1_runs`) -/

private lemma decodeOut_loop1_runs {w h packBase : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {st₂ : State} {out B inact origs : List ℕ}
    {outLimbsPtr m₁ bArr inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr k_cost T : ℕ}
    {Q : Outcome → State → Prop}
    (hpw_mc : MeetsContract w p packBase (Num.packWordContract w h))
    (hh : 1 ≤ h) (hw4 : 2 ≤ w) (hw1 : 1 < 2 ^ w) (hL_w : L_sim < 2 ^ w)
    (houtLen_w : out.length < 2 ^ w) (hmB_w : m₁ + B.length < 2 ^ w)
    (houtL_w : outLimbsPtr + out.length * L_sim < 2 ^ w)
    (hb_w : bArr + B.length < 2 ^ w) (horig_w : origsPtr + m₁ < 2 ^ w)
    (ho_len : origs.length = m₁)
    (hoorig_w : outOrigPtr + out.length < 2 ^ w)
    (hobridge_w : outBridgePtr + 2 * (out.length + inact.length) < 2 ^ w)
    (hOrig_lt : ∀ x ∈ origs, x < 2 ^ w) (hB_lt : ∀ x ∈ B, x < 2 ^ w)
    (hd_ob : DisjointRanges outOrigPtr out.length outBridgePtr (2 * (out.length + inact.length)))
    (hd_oL : DisjointRanges outOrigPtr out.length outLimbsPtr (out.length * L_sim))
    (hd_oo : DisjointRanges outOrigPtr out.length origsPtr m₁)
    (hd_oB : DisjointRanges outOrigPtr out.length bArr B.length)
    (hd_bL : DisjointRanges outBridgePtr (2 * (out.length + inact.length)) outLimbsPtr (out.length * L_sim))
    (hd_bo : DisjointRanges outBridgePtr (2 * (out.length + inact.length)) origsPtr m₁)
    (hd_bB : DisjointRanges outBridgePtr (2 * (out.length + inact.length)) bArr B.length)
    (hout_limbs : ∀ i (hi : i < out.length), LimbsAt mem (outLimbsPtr + i * L_sim) L_sim h (out[i]'hi) ∧ out[i]'hi < 2 ^ w)
    (horig_at : ListAt mem origsPtr origs) (hb_at : ListAt mem bArr B)
    (hregs2 : DOutRegs st₂ outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr)
    (hr13_2 : st₂.regs 13 = 0) (hr14_2 : st₂.regs 14 = 0) (hm2 : st₂.mem = mem)
    (hrest : ∀ st₃ : State,
      DOutRegs st₃ outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr →
      st₃.regs 13 = (origPref out m₁ origs out.length).length →
      st₃.regs 14 = (brPref out m₁ B r₀ out.length).length →
      ListAt st₃.mem outOrigPtr (origPref out m₁ origs out.length) →
      ListAt st₃.mem outBridgePtr ((brPref out m₁ B r₀ out.length).flatMap fun p => [p.1, p.2]) →
      (∀ a, (a < outOrigPtr ∨ outOrigPtr + out.length ≤ a) →
        (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) → st₃.mem a = mem a) →
      ∃ o st' c,
        Runs w p ω
          (forRange 15 (.const 0) (.reg 5)
             (.assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;
              .assign 17 (.bin .mul (.const 2) (.reg 14)) ;;
              .store (.bin .add (.reg 11) (.reg 17)) (.reg 7) ;;
              .store (.bin .add (.reg 11) (.bin .add (.reg 17) (.const 1))) (.reg 16) ;;
              .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
           .store (.reg 12) (.reg 13) ;;
           .store (.bin .add (.reg 12) (.const 1)) (.reg 14) ;;
           .ret (.const 0))
          st₃ o st' c ∧ Q o st' ∧ (k_cost + (out.length * (25 * L_sim + 80) + 10)) + c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (forRange 15 (.const 0) (.reg 1)
           (.assign 16 (.bin .add (.reg 0) (.bin .mul (.reg 15) (.reg 8))) ;;
            .call 17 packBase [.reg 16, .reg 8] ;;
            .cond (.bin .lt (.reg 17) (.reg 2))
              (.assign 18 (.load (.bin .add (.reg 9) (.reg 17))) ;;
               .store (.bin .add (.reg 10) (.reg 13)) (.reg 18) ;;
               .assign 13 (.bin .add (.reg 13) (.const 1)))
              (.cond (.bin .lt (.reg 17) (.bin .add (.reg 2) (.reg 3)))
                (.assign 18 (.bin .sub (.reg 17) (.reg 2)) ;;
                 .assign 18 (.load (.bin .add (.reg 4) (.reg 18))) ;;
                 .assign 19 (.bin .mul (.const 2) (.reg 14)) ;;
                 .store (.bin .add (.reg 11) (.reg 19)) (.reg 7) ;;
                 .store (.bin .add (.reg 11) (.bin .add (.reg 19) (.const 1))) (.reg 18) ;;
                 .assign 14 (.bin .add (.reg 14) (.const 1)))
                .nop)) ;;
         forRange 15 (.const 0) (.reg 5)
           (.assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;
            .assign 17 (.bin .mul (.const 2) (.reg 14)) ;;
            .store (.bin .add (.reg 11) (.reg 17)) (.reg 7) ;;
            .store (.bin .add (.reg 11) (.bin .add (.reg 17) (.const 1))) (.reg 16) ;;
            .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
         .store (.reg 12) (.reg 13) ;;
         .store (.bin .add (.reg 12) (.const 1)) (.reg 14) ;;
         .ret (.const 0))
        st₂ o st' c ∧ Q o st' ∧ k_cost + c ≤ T := by
  let loopInv : ℕ → State → Prop := fun k st =>
    DOutRegs st outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr ∧
    st.regs 13 = (origPref out m₁ origs k).length ∧
    st.regs 14 = (brPref out m₁ B r₀ k).length ∧
    st.regs 15 = k ∧
    ListAt st.mem outOrigPtr (origPref out m₁ origs k) ∧
    ListAt st.mem outBridgePtr ((brPref out m₁ B r₀ k).flatMap fun p => [p.1, p.2]) ∧
    (∀ a, (a < outOrigPtr ∨ outOrigPtr + out.length ≤ a) →
      (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 15) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 16 (.bin .add (.reg 0) (.bin .mul (.reg 15) (.reg 8))) ;;
      .call 17 packBase [.reg 16, .reg 8] ;;
      .cond (.bin .lt (.reg 17) (.reg 2))
        (.assign 18 (.load (.bin .add (.reg 9) (.reg 17))) ;;
         .store (.bin .add (.reg 10) (.reg 13)) (.reg 18) ;;
         .assign 13 (.bin .add (.reg 13) (.const 1)))
        (.cond (.bin .lt (.reg 17) (.bin .add (.reg 2) (.reg 3)))
          (.assign 18 (.bin .sub (.reg 17) (.reg 2)) ;;
           .assign 18 (.load (.bin .add (.reg 4) (.reg 18))) ;;
           .assign 19 (.bin .mul (.const 2) (.reg 14)) ;;
           .store (.bin .add (.reg 11) (.reg 19)) (.reg 7) ;;
           .store (.bin .add (.reg 11) (.bin .add (.reg 19) (.const 1))) (.reg 18) ;;
           .assign 14 (.bin .add (.reg 14) (.const 1)))
          .nop))
    (P := fun st => st = st₂) (Inv := loopInv) (25 * L_sim + 70) 0 out.length (Nat.zero_le _) hw1
    (fun _ => houtLen_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [loopInv, origPref, brPref]
      refine ⟨dOutRegs_upd hregs2 rfl (by decide),
        by rw [Function.update_of_ne (by decide), hr13_2]; simp,
        by rw [Function.update_of_ne (by decide), hr14_2]; simp,
        by rw [Function.update_self],
        by simp [hm2, listAt_nil],
        by simp [hm2, listAt_nil],
        fun _ _ _ => by rw [hm2]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.r1)
    (fun k _ hk => by
      intro st ω hInv
      have hregs := hInv.1
      have hr13 := hInv.2.1
      have hr14 := hInv.2.2.1
      have hr15 := hInv.2.2.2.1
      have hlo_st := hInv.2.2.2.2.1
      have hlb_st := hInv.2.2.2.2.2.1
      have hfr_st := hInv.2.2.2.2.2.2
      let v := out[k]'hk
      let oc := (origPref out m₁ origs k).length
      let bc := (brPref out m₁ B r₀ k).length
      have hoc_le : oc ≤ k := origPref_length_le out m₁ origs k
      have hbc_le : bc ≤ k := brPref_length_le out m₁ B r₀ k
      have hoc_lt : oc < out.length := lt_of_le_of_lt hoc_le hk
      have hbc_lt : bc < out.length := lt_of_le_of_lt hbc_le hk
      have hkL_le : k * L_sim + L_sim ≤ out.length * L_sim := by
        have hm := Nat.mul_le_mul_right L_sim (Nat.succ_le_of_lt hk)
        rw [Nat.succ_mul] at hm; exact hm
      have ha_kL_w : outLimbsPtr + k * L_sim + L_sim < 2 ^ w := by linarith only [houtL_w, hkL_le]
      have ha_kL_addr_w : outLimbsPtr + k * L_sim < 2 ^ w := by linarith only [ha_kL_w, Nat.zero_le L_sim]
      have hkL_w : k * L_sim < 2 ^ w := by linarith only [ha_kL_addr_w]
      have hk_w : k < 2 ^ w := lt_trans hk houtLen_w
      have hv_spec := hout_limbs k hk
      have hv_limbs : LimbsAt st.mem (outLimbsPtr + k * L_sim) L_sim h v :=
        hv_spec.1.congr fun q hq1 hq2 =>
          mem_disj_of_ranges hd_oL.symm hd_bL.symm hfr_st q
            (by linarith only [hq1, Nat.zero_le (k * L_sim)])
            (by linarith only [hq2, hkL_le])
      have hv_w : v < 2 ^ w := hv_spec.2
      have hpre_pw : (Num.packWordContract w h).pre [outLimbsPtr + k * L_sim, L_sim] st.mem :=
        ⟨outLimbsPtr + k * L_sim, L_sim, rfl, ha_kL_w, limbsAt_numValid hv_limbs,
          by rw [limbsAt_unsignedVal (by omega : 0 < h) hv_limbs]; exact hv_w⟩
      refine runs_start_le ?_
      refine runs_seq_assign_step
        (Expr.eval_add (Expr.eval_reg_of_eq hregs.r0)
          (Expr.eval_mul (Expr.eval_reg_of_eq hr15) (Expr.eval_reg_of_eq hregs.r8) hkL_w) ha_kL_addr_w)
        rfl fun s1 hm1 _ hr1 => ?_
      have hregs1 := dOutRegs_upd hregs hr1 (by decide)
      have hs1_13 : s1.regs 13 = oc := by rw [hr1, Function.update_of_ne (by decide)]; exact hr13
      have hs1_14 : s1.regs 14 = bc := by rw [hr1, Function.update_of_ne (by decide)]; exact hr14
      have hs1_16 : s1.regs 16 = outLimbsPtr + k * L_sim := by rw [hr1, Function.update_self]
      refine runs_seq_call_step hpw_mc (vs := [outLimbsPtr + k * L_sim, L_sim])
        (evalArgs_cons (Expr.eval_reg_of_eq hs1_16) (evalArgs_cons (Expr.eval_reg_of_eq hregs1.r8) (evalArgs_nil _ _)))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx] <;> assumption)
        (hm1.symm ▸ hpre_pw) rfl (rfl : _ = 25 * L_sim + 6) fun _ mem_p s2 hp2 hm2 hr2 => ?_
      rcases hp2 with ⟨hm_p, hv_p⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at hv_p
      have hm_s2_mem : s2.mem = st.mem := by rw [hm2, hm_p, hm1]
      have hv_eq : s2.regs 17 = v := by
        rw [hr2, Function.update_self, hv_p, hm1, limbsAt_unsignedVal (by omega : 0 < h) hv_limbs]
      have hregs2 := dOutRegs_upd hregs1 hr2 (by decide)
      have hs2_13 : s2.regs 13 = oc := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_13
      have hs2_14 : s2.regs 14 = bc := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_14
      by_cases hlt : v < m₁
      · have hstep_o := decodeAN19_step_lt out m₁ origs k hk hlt
        have hstep_b := decodeAN19_bridge_step_skip out m₁ B r₀ k hk (by omega)
        have hm_orig_eq : st.mem (origsPtr + v) = origs.getD v 0 := by
          have hv_mem_eq : st.mem (origsPtr + v) = mem (origsPtr + v) :=
            mem_disj_of_ranges hd_oo.symm hd_bo.symm hfr_st (origsPtr + v)
              (Nat.le_add_right _ _) (by linarith only [hlt])
          rw [hv_mem_eq, horig_at v (by omega), List.getD_eq_getElem origs 0 (by omega)]
        have horig_val_w : origs.getD v 0 < 2 ^ w := by
          rw [List.getD_eq_getElem origs 0 (by omega)]
          exact hOrig_lt _ (List.getElem_mem _)
        have hoc_addr_w : outOrigPtr + oc < 2 ^ w := by linarith only [hoorig_w, hoc_lt]
        have hoc1_w : oc + 1 < 2 ^ w := by linarith only [hoc_lt, houtLen_w]
        refine runs_cond_le (Expr.eval_lt_true (Expr.eval_reg_of_eq hv_eq) (Expr.eval_reg_of_eq hregs2.r2) hlt hw1)
          (fun _ => ?_) (fun h0 => absurd h0 one_ne_zero)
        refine runs_seq_assign_step
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r9) (Expr.eval_reg_of_eq hv_eq)
            (by linarith only [hlt, horig_w])) (hm_s2_mem ▸ hm_orig_eq))
          rfl fun s3 hm3 _ hr3 => ?_
        have hregs3 := dOutRegs_upd hregs2 hr3 (by decide)
        have hs3_13 : s3.regs 13 = oc := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_13
        have hs3_14 : s3.regs 14 = bc := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_14
        have hs3_18 : s3.regs 18 = origs.getD v 0 := by rw [hr3, Function.update_self]
        refine runs_seq_store_step
          (Expr.eval_add (Expr.eval_reg_of_eq hregs3.r10) (Expr.eval_reg_of_eq hs3_13) hoc_addr_w)
          (Expr.eval_reg_of_eq hs3_18)
          rfl fun s4 hm4 hr4 _ => ?_
        have hs4_mem : s4.mem = Function.update st.mem (outOrigPtr + oc) (origs.getD v 0) := by
          rw [hm4, hm3, hm_s2_mem]
        have hs4_13 : s4.regs 13 = oc := by rw [hr4]; exact hs3_13
        have hs4_14 : s4.regs 14 = bc := by rw [hr4]; exact hs3_14
        refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs4_13) (Expr.eval_const hw1) hoc1_w) ?_ ?_
        · refine ⟨⟨dOutRegs_upd (dOutRegs_upd (dOutRegs_of_eq hregs3 hr4) rfl (by decide)) rfl (by decide), ?_, ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
          · dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
            rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k ++ [origs.getD v 0] from hstep_o,
              List.length_append, List.length_singleton]
          · dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs4_14]
            rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k from hstep_b]
          · dsimp only; rw [hs4_mem]
            rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k ++ [origs.getD v 0] from hstep_o]
            exact listAt_snoc' hlo_st
          · dsimp only; rw [hs4_mem]
            rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k from hstep_b]
            refine hlb_st.congr fun q hq1 hq2 => ?_
            have hne : q ≠ outOrigPtr + oc := by
              rcases hd_ob with h1 | h1
              · exact ne_of_gt (by linarith only [h1, hq1, hoc_lt])
              · exact ne_of_lt (by
                  have hlen_f : ((brPref out m₁ B r₀ k).flatMap fun p => [p.1, p.2]).length = 2 * bc := by
                    simp [bc, List.length_flatMap]; ring
                  linarith only [h1, hq2, hlen_f, hbc_lt])
            rw [Function.update_of_ne hne]
          · intro a ha1 ha2
            dsimp only; rw [hs4_mem, Function.update_of_ne ?_, hfr_st a ha1 ha2]
            rcases ha1 with h1 | h1
            · exact ne_of_lt (by linarith only [h1])
            · exact ne_of_gt (by linarith only [h1, hoc_lt])
          · dsimp only; rw [Function.update_of_ne (by decide), hr4, hr3, Function.update_of_ne (by decide),
              hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; exact hr15
        · dsimp only [argsSize, Expr.size]; omega
      · have hm_lt : m₁ ≤ v := Nat.le_of_not_lt hlt
        have hstep_o := decodeAN19_step_ge out m₁ origs k hk hm_lt
        refine runs_cond_le (Expr.eval_lt_false (Expr.eval_reg_of_eq hv_eq) (Expr.eval_reg_of_eq hregs2.r2) hm_lt hw1)
          (fun h1 => absurd rfl h1) (fun _ => ?_)
        by_cases hlt2 : v < m₁ + B.length
        · have hstep_b := decodeAN19_bridge_step_mem out m₁ B r₀ k hk hm_lt hlt2
          have hm_b_eq : st.mem (bArr + (v - m₁)) = B.getD (v - m₁) 0 := by
            have hv_mem_eq : st.mem (bArr + (v - m₁)) = mem (bArr + (v - m₁)) :=
              mem_disj_of_ranges hd_oB.symm hd_bB.symm hfr_st (bArr + (v - m₁))
                (Nat.le_add_right _ _) (by omega)
            rw [hv_mem_eq, hb_at (v - m₁) (by omega), List.getD_eq_getElem B 0 (by omega)]
          have hb_val_w : B.getD (v - m₁) 0 < 2 ^ w := by
            rw [List.getD_eq_getElem B 0 (by omega)]
            exact hB_lt _ (List.getElem_mem _)
          have hbc2_w : 2 * bc < 2 ^ w := by linarith only [hobridge_w, hbc_lt]
          have hbc21_w : 2 * bc + 1 < 2 ^ w := by linarith only [hobridge_w, hbc_lt]
          have hbr_addr0 : outBridgePtr + 2 * bc < 2 ^ w := by linarith only [hobridge_w, hbc_lt]
          have hbr_addr1 : outBridgePtr + (2 * bc + 1) < 2 ^ w := by linarith only [hobridge_w, hbc_lt]
          have hbc1_w : bc + 1 < 2 ^ w := by linarith only [hbc_lt, houtLen_w]
          have h2_w : 2 < 2 ^ w :=
            lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hw4)
          refine runs_cond_le
            (Expr.eval_lt_true (Expr.eval_reg_of_eq hv_eq)
              (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r2) (Expr.eval_reg_of_eq hregs2.r3) hmB_w) hlt2 hw1)
            (fun _ => ?_) (fun h0 => absurd h0 one_ne_zero)
          refine runs_seq_assign_step
            (Expr.eval_sub (Expr.eval_reg_of_eq hv_eq) (Expr.eval_reg_of_eq hregs2.r2) hv_w)
            rfl fun s3 hm3 _ hr3 => ?_
          have hregs3 := dOutRegs_upd hregs2 hr3 (by decide)
          have hs3_13 : s3.regs 13 = oc := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_13
          have hs3_14 : s3.regs 14 = bc := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_14
          have hs3_18 : s3.regs 18 = v - m₁ := by rw [hr3, Function.update_self]
          have hs3_mem : s3.mem = st.mem := hm3.trans hm_s2_mem
          refine runs_seq_assign_step
            (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs3.r4) (Expr.eval_reg_of_eq hs3_18)
              (by omega)) (hs3_mem ▸ hm_b_eq))
            rfl fun s4 hm4 _ hr4 => ?_
          have hregs4 := dOutRegs_upd hregs3 hr4 (by decide)
          have hs4_13 : s4.regs 13 = oc := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_13
          have hs4_14 : s4.regs 14 = bc := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_14
          have hs4_18 : s4.regs 18 = B.getD (v - m₁) 0 := by rw [hr4, Function.update_self]
          refine runs_seq_assign_step
            (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq hs4_14) hbc2_w)
            rfl fun s5 hm5 _ hr5 => ?_
          have hregs5 := dOutRegs_upd hregs4 hr5 (by decide)
          have hs5_13 : s5.regs 13 = oc := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_13
          have hs5_14 : s5.regs 14 = bc := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_14
          have hs5_18 : s5.regs 18 = B.getD (v - m₁) 0 := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_18
          have hs5_19 : s5.regs 19 = 2 * bc := by rw [hr5, Function.update_self]
          refine runs_seq_store_step
            (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r11) (Expr.eval_reg_of_eq hs5_19) hbr_addr0)
            (Expr.eval_reg_of_eq hregs5.r7)
            rfl fun s6 hm6 hr6 _ => ?_
          have hregs6 := dOutRegs_of_eq hregs5 hr6
          have hs6_13 : s6.regs 13 = oc := by rw [hr6]; exact hs5_13
          have hs6_14 : s6.regs 14 = bc := by rw [hr6]; exact hs5_14
          have hs6_18 : s6.regs 18 = B.getD (v - m₁) 0 := by rw [hr6]; exact hs5_18
          have hs6_19 : s6.regs 19 = 2 * bc := by rw [hr6]; exact hs5_19
          refine runs_seq_store_step
            (Expr.eval_add (Expr.eval_reg_of_eq hregs6.r11)
              (Expr.eval_add (Expr.eval_reg_of_eq hs6_19) (Expr.eval_const hw1) hbc21_w) hbr_addr1)
            (Expr.eval_reg_of_eq hs6_18)
            rfl fun s7 hm7 hr7 _ => ?_
          have hs7_mem : s7.mem =
              Function.update (Function.update st.mem (outBridgePtr + 2 * bc) r₀)
                (outBridgePtr + (2 * bc + 1)) (B.getD (v - m₁) 0) := by
            rw [hm7, hm6, hm5, hm4, hs3_mem]
          have hs7_13 : s7.regs 13 = oc := by rw [hr7]; exact hs6_13
          have hs7_14 : s7.regs 14 = bc := by rw [hr7]; exact hs6_14
          refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs7_14) (Expr.eval_const hw1) hbc1_w) ?_ ?_
          · refine ⟨⟨dOutRegs_upd (dOutRegs_upd (dOutRegs_of_eq hregs6 hr7) rfl (by decide)) rfl (by decide), ?_, ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
            · dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs7_13]
              rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k from hstep_o]
            · dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
              rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k ++ [(r₀, B.getD (v - m₁) 0)] from hstep_b,
                List.length_append, List.length_singleton]
            · dsimp only; rw [hs7_mem]
              rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k from hstep_o]
              refine hlo_st.congr fun q hq1 hq2 => ?_
              change q < outOrigPtr + oc at hq2
              have hne0 : q ≠ outBridgePtr + 2 * bc := by
                rcases hd_ob with h1 | h1
                · exact ne_of_lt (by linarith only [h1, hq2, hoc_lt, Nat.zero_le (2 * bc)])
                · exact ne_of_gt (by linarith only [h1, hq1, hbc_lt])
              have hne1 : q ≠ outBridgePtr + (2 * bc + 1) := by
                rcases hd_ob with h1 | h1
                · exact ne_of_lt (by linarith only [h1, hq2, hoc_lt, Nat.zero_le (2 * bc)])
                · exact ne_of_gt (by linarith only [h1, hq1, hbc_lt])
              rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
            · dsimp only; rw [hs7_mem]
              rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k ++ [(r₀, B.getD (v - m₁) 0)] from hstep_b]
              simpa [Nat.add_assoc] using listAt_pairs_snoc hlb_st
            · intro a ha1 ha2
              dsimp only; rw [hs7_mem]
              have hne0 : a ≠ outBridgePtr + 2 * bc := by
                rcases ha2 with h1 | h1
                · exact ne_of_lt (by linarith only [h1])
                · exact ne_of_gt (by linarith only [h1, hbc_lt])
              have hne1 : a ≠ outBridgePtr + (2 * bc + 1) := by
                rcases ha2 with h1 | h1
                · exact ne_of_lt (by linarith only [h1])
                · exact ne_of_gt (by linarith only [h1, hbc_lt])
              rw [Function.update_of_ne hne1, Function.update_of_ne hne0, hfr_st a ha1 ha2]
            · dsimp only; rw [Function.update_of_ne (by decide), hr7, hr6, hr5,
                Function.update_of_ne (by decide), hr4, Function.update_of_ne (by decide),
                hr3, Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide),
                hr1, Function.update_of_ne (by decide)]; exact hr15
          · dsimp only [argsSize, Expr.size]; omega
        · have hge2 : m₁ + B.length ≤ v := Nat.le_of_not_lt hlt2
          have hstep_b := decodeAN19_bridge_step_skip out m₁ B r₀ k hk (by omega)
          refine runs_cond_le
            (Expr.eval_lt_false (Expr.eval_reg_of_eq hv_eq)
              (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r2) (Expr.eval_reg_of_eq hregs2.r3) hmB_w) hge2 hw1)
            (fun h1 => absurd rfl h1) (fun _ => ?_)
          refine runs_nop_le ?_ (by dsimp only [argsSize, Expr.size]; omega)
          refine ⟨⟨dOutRegs_upd hregs2 rfl (by decide), ?_, ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
          · dsimp only; rw [Function.update_of_ne (by decide), hs2_13]
            rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k from hstep_o]
          · dsimp only; rw [Function.update_of_ne (by decide), hs2_14]
            rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k from hstep_b]
          · dsimp only; rw [hm_s2_mem]
            rw [show origPref out m₁ origs (k + 1) = origPref out m₁ origs k from hstep_o]
            exact hlo_st
          · dsimp only; rw [hm_s2_mem]
            rw [show brPref out m₁ B r₀ (k + 1) = brPref out m₁ B r₀ k from hstep_b]
            exact hlb_st
          · intro a ha1 ha2; dsimp only; rw [hm_s2_mem]; exact hfr_st a ha1 ha2
          · rw [hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; exact hr15)
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st3 hInv3
  obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest st3 hInv3.1 hInv3.2.1 hInv3.2.2.1
    hInv3.2.2.2.2.1 hInv3.2.2.2.2.2.1 hInv3.2.2.2.2.2.2
  refine ⟨o, st', c, hrun, hq, ?_⟩
  dsimp only [Expr.size] at hc ⊢
  simp only [Nat.sub_zero]
  have hmul : out.length * (25 * L_sim + 70 + 1 + 8) ≤ out.length * (25 * L_sim + 80) :=
    Nat.mul_le_mul_left _ (by omega)
  linarith only [hc, hmul]

/-! ### Second decoding loop (`decodeOut_loop2_runs`) and full contract -/

private lemma decodeOut_loop2_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem₃ : ℕ → ℕ} {st₃ : State} {out B inact origs : List ℕ}
    {outLimbsPtr m₁ bArr inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr k_cost T : ℕ}
    {Q : Outcome → State → Prop}
    (hw1 : 1 < 2 ^ w) (hw4 : 2 ≤ w)
    (hinact_len_w : inact.length < 2 ^ w) (hinact_w : inactArr + inact.length < 2 ^ w)
    (hobridge_w : outBridgePtr + 2 * (out.length + inact.length) < 2 ^ w)
    (horigLen_w : out.length + inact.length < 2 ^ w)
    (hinact_lt : ∀ x ∈ inact, x < 2 ^ w)
    (hd_bi : DisjointRanges outBridgePtr (2 * (out.length + inact.length)) inactArr inact.length)
    (hinact_at : ListAt mem₃ inactArr inact)
    (hregs3 : DOutRegs st₃ outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr)
    (hr13_3 : st₃.regs 13 = (origPref out m₁ origs out.length).length)
    (hr14_3 : st₃.regs 14 = (brPref out m₁ B r₀ out.length).length)
    (hlb_3 : ListAt mem₃ outBridgePtr ((brPref out m₁ B r₀ out.length).flatMap fun p => [p.1, p.2]))
    (hm3 : st₃.mem = mem₃)
    (hrest : ∀ st₄ : State,
      DOutRegs st₄ outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr →
      st₄.regs 13 = (origPref out m₁ origs out.length).length →
      st₄.regs 14 = (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).length →
      ListAt st₄.mem outBridgePtr ((brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).flatMap fun p => [p.1, p.2]) →
      (∀ a, (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) → st₄.mem a = mem₃ a) →
      ∃ o st' c,
        Runs w p ω
          (.store (.reg 12) (.reg 13) ;;
           .store (.bin .add (.reg 12) (.const 1)) (.reg 14) ;;
           .ret (.const 0))
          st₄ o st' c ∧ Q o st' ∧ (k_cost + (45 * inact.length + 10)) + c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (forRange 15 (.const 0) (.reg 5)
           (.assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;
            .assign 17 (.bin .mul (.const 2) (.reg 14)) ;;
            .store (.bin .add (.reg 11) (.reg 17)) (.reg 7) ;;
            .store (.bin .add (.reg 11) (.bin .add (.reg 17) (.const 1))) (.reg 16) ;;
            .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
         .store (.reg 12) (.reg 13) ;;
         .store (.bin .add (.reg 12) (.const 1)) (.reg 14) ;;
         .ret (.const 0))
        st₃ o st' c ∧ Q o st' ∧ k_cost + c ≤ T := by
  let bp0 := brPref out m₁ B r₀ out.length
  have hbp0_le : bp0.length ≤ out.length := brPref_length_le out m₁ B r₀ out.length
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw4)
  let loopInv : ℕ → State → Prop := fun k st =>
    DOutRegs st outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr ∧
    st.regs 13 = (origPref out m₁ origs out.length).length ∧
    st.regs 14 = bp0.length + k ∧
    st.regs 15 = k ∧
    ListAt st.mem outBridgePtr ((bp0 ++ (inact.take k).map fun u => (r₀, u)).flatMap fun p => [p.1, p.2]) ∧
    (∀ a, (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) → st.mem a = mem₃ a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 15) (lo := .const 0) (hi := .reg 5)
    (body :=
      .assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;
      .assign 17 (.bin .mul (.const 2) (.reg 14)) ;;
      .store (.bin .add (.reg 11) (.reg 17)) (.reg 7) ;;
      .store (.bin .add (.reg 11) (.bin .add (.reg 17) (.const 1))) (.reg 16) ;;
      .assign 14 (.bin .add (.reg 14) (.const 1)))
    (P := fun st => st = st₃) (Inv := loopInv) 35 0 inact.length (Nat.zero_le _) hw1
    (fun _ => hinact_len_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [loopInv]
      refine ⟨dOutRegs_upd hregs3 rfl (by decide),
        by rw [Function.update_of_ne (by decide), hr13_3],
        by rw [Function.update_of_ne (by decide), hr14_3]; simp [bp0],
        by rw [Function.update_self],
        by simpa [hm3, bp0] using hlb_3,
        fun _ _ => by rw [hm3]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.r5)
    (fun k _ hk => by
      intro st ω hInv
      have hregs := hInv.1
      have hr13 := hInv.2.1
      have hr14 := hInv.2.2.1
      have hr15 := hInv.2.2.2.1
      have hlb := hInv.2.2.2.2.1
      have hfr := hInv.2.2.2.2.2
      have hlen_p : (bp0 ++ (inact.take k).map fun u => (r₀, u)).length = bp0.length + k := by
        rw [List.length_append, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
      have hmem_i : st.mem (inactArr + k) = inact[k]'hk := by
        have hdisj : st.mem (inactArr + k) = mem₃ (inactArr + k) :=
          hfr _ (hd_bi.elim (fun h1 => Or.inr (by linarith only [h1]))
            (fun h1 => Or.inl (by linarith only [h1, hk])))
        rw [hdisj, hinact_at k hk]
      have hin_val_w : inact[k]'hk < 2 ^ w := hinact_lt _ (List.getElem_mem hk)
      have hbc2_w : 2 * (bp0.length + k) < 2 ^ w := by linarith only [hobridge_w, hbp0_le, hk]
      have hbc21_w : 2 * (bp0.length + k) + 1 < 2 ^ w := by linarith only [hobridge_w, hbp0_le, hk]
      have hbr0_w : outBridgePtr + 2 * (bp0.length + k) < 2 ^ w := by linarith only [hobridge_w, hbp0_le, hk]
      have hbr1_w : outBridgePtr + (2 * (bp0.length + k) + 1) < 2 ^ w := by linarith only [hobridge_w, hbp0_le, hk]
      have hbc1_w : bp0.length + k + 1 < 2 ^ w := by linarith only [horigLen_w, hbp0_le, hk]
      refine runs_start_le ?_
      refine runs_seq_assign_step
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs.r6) (Expr.eval_reg_of_eq hr15)
          (by linarith only [hinact_w, hk])) hmem_i)
        rfl fun s1 hm1 _ hr1 => ?_
      have hregs1 := dOutRegs_upd hregs hr1 (by decide)
      have hs1_13 : s1.regs 13 = (origPref out m₁ origs out.length).length := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hr13
      have hs1_14 : s1.regs 14 = bp0.length + k := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hr14
      have hs1_16 : s1.regs 16 = inact[k]'hk := by rw [hr1, Function.update_self]
      refine runs_seq_assign_step
        (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq hs1_14) hbc2_w)
        rfl fun s2 hm2 _ hr2 => ?_
      have hregs2 := dOutRegs_upd hregs1 hr2 (by decide)
      have hs2_13 : s2.regs 13 = (origPref out m₁ origs out.length).length := by
        rw [hr2, Function.update_of_ne (by decide)]; exact hs1_13
      have hs2_14 : s2.regs 14 = bp0.length + k := by
        rw [hr2, Function.update_of_ne (by decide)]; exact hs1_14
      have hs2_16 : s2.regs 16 = inact[k]'hk := by
        rw [hr2, Function.update_of_ne (by decide)]; exact hs1_16
      have hs2_17 : s2.regs 17 = 2 * (bp0.length + k) := by rw [hr2, Function.update_self]
      refine runs_seq_store_step
        (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r11) (Expr.eval_reg_of_eq hs2_17) hbr0_w)
        (Expr.eval_reg_of_eq hregs2.r7)
        rfl fun s3 hm3_s hr3 _ => ?_
      have hs3_13 : s3.regs 13 = (origPref out m₁ origs out.length).length := by rw [hr3]; exact hs2_13
      have hs3_14 : s3.regs 14 = bp0.length + k := by rw [hr3]; exact hs2_14
      have hs3_16 : s3.regs 16 = inact[k]'hk := by rw [hr3]; exact hs2_16
      have hs3_17 : s3.regs 17 = 2 * (bp0.length + k) := by rw [hr3]; exact hs2_17
      refine runs_seq_store_step
        (Expr.eval_add (Expr.eval_reg_of_eq (dOutRegs_of_eq hregs2 hr3).r11)
          (Expr.eval_add (Expr.eval_reg_of_eq hs3_17) (Expr.eval_const hw1) hbc21_w) hbr1_w)
        (Expr.eval_reg_of_eq hs3_16)
        rfl fun s4 hm4_s hr4 _ => ?_
      have hs4_mem : s4.mem =
          Function.update (Function.update st.mem (outBridgePtr + 2 * (bp0.length + k)) r₀)
            (outBridgePtr + (2 * (bp0.length + k) + 1)) (inact[k]'hk) := by
        rw [hm4_s, hm3_s, hm2, hm1]
      have hs4_13 : s4.regs 13 = (origPref out m₁ origs out.length).length := by rw [hr4]; exact hs3_13
      have hs4_14 : s4.regs 14 = bp0.length + k := by rw [hr4]; exact hs3_14
      refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs4_14) (Expr.eval_const hw1) hbc1_w) ?_ ?_
      · refine ⟨⟨dOutRegs_upd (dOutRegs_upd (dOutRegs_of_eq (dOutRegs_of_eq hregs2 hr3) hr4) rfl (by decide)) rfl (by decide), ?_, ?_, by simp, ?_, ?_⟩, ?_⟩
        · dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs4_13]
        · dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; ring
        · dsimp only; rw [hs4_mem, List.take_succ_eq_append_getElem hk, List.map_append,
            List.map_singleton, ← List.append_assoc]
          have hsn := listAt_pairs_snoc (u := r₀) (v := inact[k]'hk) hlb
          rw [hlen_p] at hsn
          simpa [Nat.add_assoc] using hsn
        · intro a ha
          dsimp only; rw [hs4_mem]
          have hne0 : a ≠ outBridgePtr + 2 * (bp0.length + k) := by
            rcases ha with h1 | h1
            · exact ne_of_lt (by linarith only [h1])
            · exact ne_of_gt (by linarith only [h1, hbp0_le, hk])
          have hne1 : a ≠ outBridgePtr + (2 * (bp0.length + k) + 1) := by
            rcases ha with h1 | h1
            · exact ne_of_lt (by linarith only [h1])
            · exact ne_of_gt (by linarith only [h1, hbp0_le, hk])
          rw [Function.update_of_ne hne1, Function.update_of_ne hne0, hfr a ha]
        · dsimp only; rw [Function.update_of_ne (by decide), hr4, hr3, hr2,
            Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; exact hr15
      · dsimp only [argsSize, Expr.size]; omega)
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st4 hInv4
  have htake_i : inact.take inact.length = inact := List.take_length
  have hlen_end : (bp0 ++ inact.map fun u => (r₀, u)).length = bp0.length + inact.length := by
    rw [List.length_append, List.length_map]
  have hlb4 : ListAt st4.mem outBridgePtr ((bp0 ++ inact.map fun u => (r₀, u)).flatMap fun p => [p.1, p.2]) := by
    simpa [htake_i] using hInv4.2.2.2.2.1
  have hr14_4 : st4.regs 14 = (bp0 ++ inact.map fun u => (r₀, u)).length := by
    rw [hlen_end]; exact hInv4.2.2.1
  obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest st4 hInv4.1 hInv4.2.1 hr14_4 hlb4 hInv4.2.2.2.2.2
  refine ⟨o, st', c, hrun, hq, ?_⟩
  dsimp only [Expr.size] at hc ⊢
  simp only [Nat.sub_zero]
  have hmul : inact.length * (35 + 1 + 8) ≤ 45 * inact.length := by omega
  linarith only [hc, hmul]

theorem decodeOut_meetsContract {w h a p w' s e : ℕ} {P : Program}
    (hp : P.HasAt e (encodeDecodeModule a p w' s e))
    (hpack : P.HasAt p (Num.packWordModule p h)) :
    MeetsContract w P (e + idxDecodeOut) (decodeOutContract w h) := by
  have hproc : P.procs[e + idxDecodeOut]? = some (decodeOutProc p) := by
    have := hp 3 (by rw [encodeDecodeModule_length]; omega)
    simpa [encodeDecodeModule, idxDecodeOut] using this
  refine meetsContract_of_runs hproc ?_
  intro args mem pos₀ ω hwords hpre
  rcases hpre with ⟨out, B, inact, origs,
    outLimbsPtr, m₁, bArr, inactArr, r₀, L_sim, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr,
    hargs, hh, hw2, hL1, hmB_w, houtL_w, hb_w, hinact_w, horig_w, ho_len,
    hoorig_w, hobridge_w, hohdr_w, hr₀_w, hOrig_lt, hB_lt, hinact_lt,
    hd_ob, hd_oh, hd_bh, hd_oL, hd_oo, hd_oB, hd_oi, hd_bL, hd_bo, hd_bB, hd_bi,
    hd_hL, hd_ho, hd_hB, hd_hi, hout_limbs, horig_at, hb_at, hinact_at⟩
  have hwords' : ∀ a ∈ [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀,
      L_sim, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr], a < 2 ^ w := hargs ▸ hwords
  rw [hargs]
  have hw4 : 2 ≤ w := by omega
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hbase_w : Num.base h < 2 ^ w :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : h < w)) (le_refl _)
  have hpw_mc := Num.packWord_meetsContract (w := w) (h := h) (b := p) hw1 hbase_w hpack
  have houtLen_w : out.length < 2 ^ w := hwords' out.length (by simp)
  have hinactLen_w : inact.length < 2 ^ w := hwords' inact.length (by simp)
  have hL_w : L_sim < 2 ^ w := hwords' L_sim (by simp)
  have horigLen_w : out.length + inact.length < 2 ^ w :=
    lt_of_le_of_lt (by omega : out.length + inact.length ≤ 2 * (out.length + inact.length))
      (lt_of_le_of_lt (Nat.le_add_left _ _) hobridge_w)
  have hregs0 : DOutRegs
      (startState [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀,
        L_sim, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr] mem pos₀)
      outLimbsPtr out.length m₁ B.length bArr inact.length inactArr r₀ L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState]
  refine runs_start_le ?_
  dsimp only [decodeOutProc]
  refine runs_seq_assign_step (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1)) rfl fun st1 hm1 _ hr1 => ?_
  have hregs1 := dOutRegs_upd hregs0 hr1 (by decide)
  have hr13_1 : st1.regs 13 = 0 := by rw [hr1, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1)) rfl fun st2 hm2 _ hr2 => ?_
  have hregs2 := dOutRegs_upd hregs1 hr2 (by decide)
  have hr13_2 : st2.regs 13 = 0 := by rw [hr2, Function.update_of_ne (by decide), hr13_1]
  have hr14_2 : st2.regs 14 = 0 := by rw [hr2, Function.update_self]
  have hm2_eq : st2.mem = mem := hm2.trans hm1
  refine decodeOut_loop1_runs hpw_mc hh hw4 hw1 hL_w houtLen_w hmB_w houtL_w hb_w horig_w ho_len
    hoorig_w hobridge_w hOrig_lt hB_lt hd_ob hd_oL hd_oo hd_oB hd_bL hd_bo hd_bB
    hout_limbs horig_at hb_at hregs2 hr13_2 hr14_2 hm2_eq ?_
  intro st3 hregs3 hr13_3 hr14_3 hlo_3 hlb_3 hfr_3
  have hinact_at3 : ListAt st3.mem inactArr inact :=
    hinact_at.congr fun q hq1 hq2 => mem_disj_of_ranges hd_oi.symm hd_bi.symm hfr_3 q hq1 hq2
  refine decodeOut_loop2_runs hw1 hw4 hinactLen_w hinact_w hobridge_w horigLen_w hinact_lt
    hd_bi hinact_at3 hregs3 hr13_3 hr14_3 hlb_3 rfl ?_
  intro st4 hregs4 hr13_4 hr14_4 hlb4 hfr_4
  have hhdr0_w : outHdrPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ 2) hohdr_w
  have hhdr1_w : outHdrPtr + 1 < 2 ^ w := by linarith only [hohdr_w]
  refine runs_seq_store_step
    (Expr.eval_reg_of_eq hregs4.r12) (Expr.eval_reg_of_eq hr13_4)
    rfl fun st5 hm5 hr5 _ => ?_
  have hregs5 := dOutRegs_of_eq hregs4 hr5
  have hr14_5 : st5.regs 14 = (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).length := by
    rw [hr5]; exact hr14_4
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r12) (Expr.eval_const hw1) hhdr1_w)
    (Expr.eval_reg_of_eq hr14_5)
    rfl fun st_end hm_end _ _ => ?_
  have hm_eq : st_end.mem =
      Function.update (Function.update st4.mem outHdrPtr (origPref out m₁ origs out.length).length)
        (outHdrPtr + 1) (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).length := by
    rw [hm_end, hm5]
  have htake_o : out.take out.length = out := List.take_length
  have ho_eq : origPref out m₁ origs out.length =
      (out.filter fun j => decide (j < m₁)).map fun j => origs.getD j 0 := by
    dsimp only [origPref]; rw [htake_o]
  have hb_eq : brPref out m₁ B r₀ out.length ++ inact.map (fun u => (r₀, u)) =
      (out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) ++ inact.map fun u => (r₀, u) := by
    dsimp only [brPref]; rw [htake_o]
  have hhdr0_val : st_end.mem outHdrPtr =
      ((out.filter fun j => decide (j < m₁)).map fun j => origs.getD j 0).length := by
    rw [hm_eq, Function.update_of_ne (by omega), Function.update_self, ho_eq]
  have hhdr1_val : st_end.mem (outHdrPtr + 1) =
      ((out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) ++ inact.map fun u => (r₀, u)).length := by
    rw [hm_eq, Function.update_self, hb_eq]
  have hlo_end : ListAt st_end.mem outOrigPtr
      ((out.filter fun j => decide (j < m₁)).map fun j => origs.getD j 0) := by
    rw [← ho_eq]
    have hlo_4 : ListAt st4.mem outOrigPtr (origPref out m₁ origs out.length) :=
      hlo_3.congr fun q hq1 hq2 => by
        refine hfr_4 q ?_
        have hlen_le := origPref_length_le out m₁ origs out.length
        rcases hd_ob with h1 | h1
        · left; linarith only [h1, hlen_le, hq2]
        · right; linarith only [h1, hq1]
    refine hlo_4.congr fun q hq1 hq2 => ?_
    rw [hm_eq]
    have hlen_le := origPref_length_le out m₁ origs out.length
    have hne0 : q ≠ outHdrPtr := by
      rcases hd_oh with h1 | h1
      · exact ne_of_lt (by linarith only [h1, hlen_le, hq2])
      · exact ne_of_gt (by linarith only [h1, hq1])
    have hne1 : q ≠ outHdrPtr + 1 := by
      rcases hd_oh with h1 | h1
      · exact ne_of_lt (by linarith only [h1, hlen_le, hq2])
      · exact ne_of_gt (by linarith only [h1, hq1])
    rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
  have hlb_end : ListAt st_end.mem outBridgePtr
      (((out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) ++ inact.map fun u => (r₀, u)).flatMap
        fun p => [p.1, p.2]) := by
    rw [← hb_eq]
    refine hlb4.congr fun q hq1 hq2 => ?_
    rw [hm_eq]
    have hlen_b : (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).length ≤
        out.length + inact.length := by
      rw [List.length_append, List.length_map]
      exact Nat.add_le_add_right (brPref_length_le out m₁ B r₀ out.length) _
    have hlen_f : ((brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).flatMap
        fun p => [p.1, p.2]).length ≤ 2 * (out.length + inact.length) := by
      simp only [List.length_flatMap, List.length_cons, List.length_nil]
      have hs : (List.map (fun _ => 2)
          (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u))).sum =
          2 * (brPref out m₁ B r₀ out.length ++ inact.map fun u => (r₀, u)).length := by
        simp only [List.map_append, List.map_map, Function.comp_def, List.map_const',
          List.sum_append, List.sum_replicate, smul_eq_mul, List.length_append, List.length_map]
        omega
      linarith only [hs, hlen_b]
    have hne0 : q ≠ outHdrPtr := by
      rcases hd_bh with h1 | h1
      · exact ne_of_lt (by linarith only [h1, hlen_f, hq2])
      · exact ne_of_gt (by linarith only [h1, hq1])
    have hne1 : q ≠ outHdrPtr + 1 := by
      rcases hd_bh with h1 | h1
      · exact ne_of_lt (by linarith only [h1, hlen_f, hq2])
      · exact ne_of_gt (by linarith only [h1, hq1])
    rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
  have hfr_end : ∀ a, (a < outOrigPtr ∨ outOrigPtr + out.length ≤ a) →
      (a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a) →
      (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → st_end.mem a = mem a := by
    intro a hao hab hah
    rw [hm_eq]
    have hne0 : a ≠ outHdrPtr := by
      rcases hah with h1 | h1 <;> omega
    have hne1 : a ≠ outHdrPtr + 1 := by
      rcases hah with h1 | h1 <;> omega
    rw [Function.update_of_ne hne1, Function.update_of_ne hne0, hfr_4 a hab, hfr_3 a hao hab]
  refine runs_ret_le (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1))
    ⟨out, B, inact, origs, outLimbsPtr, m₁, bArr, inactArr, r₀, L_sim, origsPtr, outOrigPtr,
      outBridgePtr, outHdrPtr, rfl, rfl, hhdr0_val, hhdr1_val, hlo_end, hlb_end, hfr_end,
      ho_len, fun i hi => (hout_limbs i hi).1, horig_at, hb_at, hinact_at⟩ ?_
  have hcost_eq : (decodeOutContract w h).cost
      [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀, L_sim,
        origsPtr, outOrigPtr, outBridgePtr, outHdrPtr] mem =
      decodeOutCost out.length inact.length L_sim := by
    simp [decodeOutContract, List.getD_eq_getElem?_getD]
  rw [hcost_eq]
  dsimp only [decodeOutCost, argsSize, Expr.size]
  linarith only

end MinCostFlow.WideWord
