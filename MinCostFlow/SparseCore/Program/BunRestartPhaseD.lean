module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseC

/-!
# The restart of the bundles: phase D (`BunRestartPhaseD`)

Phase D clears the listed slots in the table. Loop D1 writes `0` into `edgeSlot[e]` for the edge
`e` of every pair, and loop D2 writes `0` into the slot pointer of every listed slot. Both loops
are the same zero loop (`brZeroLoop_runs`): it reads a list `L` with stride `2` at `src` and
writes `0` at `dst + x` for each `x` in `L`. `brPhaseD_runs` puts the two loops together.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- **The zero loop.** Register `rSrc` holds `src`, where the list `L` is stored with stride `2`,
register `rDst` holds `dst`, and register `rN` holds the length of `L`. The loop writes `0` at
`dst + x` for every `x` in `L` and changes no other memory and no register but `10` and `11`. -/
theorem brZeroLoop_runs {rSrc rDst rN : ℕ} (hrS : rSrc ≠ 10 ∧ rSrc ≠ 11)
    (hrD : rDst ≠ 10 ∧ rDst ≠ 11) (hrN : rN ≠ 10 ∧ rN ≠ 11) {st : State} {src dst : ℕ}
    {L : List ℕ} (hw : 16 ≤ 2 ^ w) (hS : st.regs rSrc = src) (hD : st.regs rDst = dst)
    (hN : st.regs rN = L.length) (hL : ∀ i (hi : i < L.length), st.mem (src + 2 * i) = L[i])
    (hfit : src + 2 * L.length < 2 ^ w) (hdw : ∀ x ∈ L, dst + x < 2 ^ w)
    (hdisj : ∀ x ∈ L, ∀ i < L.length, dst + x ≠ src + 2 * i) :
    ∃ st' c, Runs w p ω (forRange 10 (.const 0) (.reg rN) (brZeroBody rSrc rDst)) st .normal
        st' c ∧
      (∀ r, r ≠ 10 → r ≠ 11 → st'.regs r = st.regs r) ∧
      (∀ a, (∀ x ∈ L, a ≠ dst + x) → st'.mem a = st.mem a) ∧
      (∀ x ∈ L, st'.mem (dst + x) = 0) ∧ c ≤ 30 * L.length + 7 := by
  let Inv : ℕ → State → Prop := fun i st' =>
    (∀ r, r ≠ 10 → r ≠ 11 → st'.regs r = st.regs r) ∧ st'.regs 10 = i ∧
      (∀ a, (∀ x ∈ L.take i, a ≠ dst + x) → st'.mem a = st.mem a) ∧
      (∀ x ∈ L.take i, st'.mem (dst + x) = 0)
  obtain ⟨st', c, hr, ⟨hregs, -, hfr, hz⟩, hc⟩ :=
    runs_forRange_const (w := w) (p := p) (ω := ω) (r := 10) (hi := .reg rN)
      (body := brZeroBody rSrc rDst) (Inv := Inv) 13 L.length (by omega) (by omega)
      (fun i st' _ hI => hI.2.1)
      (fun i st' _ hI => Expr.eval_reg_of_eq ((hI.1 rN hrN.1 hrN.2).trans hN))
      (fun i st₀ hi hI => by
        obtain ⟨hreg, h10, hfr, hz⟩ := hI
        obtain ⟨v, hv⟩ : ∃ v, L[i] = v := ⟨_, rfl⟩
        have hLi : v ∈ L := hv ▸ List.getElem_mem hi
        have hmi : st₀.mem (src + 2 * i) = v := by
          rw [hfr _ fun x hx => (hdisj x (List.mem_of_mem_take hx) i hi).symm, ← hv]
          exact hL i hi
        have hev1 : (Expr.load (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg 10)))).eval w
            st₀ = some v :=
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hreg _ hrS.1 hrS.2).trans hS))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h10) (by omega))
            (by omega)) hmi
        have hr₁ : Runs w p ω (.assign 11 (.load (.bin .add (.reg rSrc)
            (.bin .mul (.const 2) (.reg 10))))) st₀ .normal
            { st₀ with regs := Function.update st₀.regs 11 v } 7 :=
          runs_assign_iff.mpr ⟨v, hev1, rfl, rfl, by simp [Expr.size]⟩
        have hdx := hdw _ hLi
        have hr₂ : Runs w p ω (.store (.bin .add (.reg rDst) (.reg 11)) (.const 0))
            { st₀ with regs := Function.update st₀.regs 11 v } .normal
            { mem := Function.update st₀.mem (dst + v) 0,
              regs := Function.update st₀.regs 11 v, pos := st₀.pos } 5 :=
          runs_store_iff.mpr ⟨dst + v, 0,
            Expr.eval_add (Expr.eval_reg_of_eq (by
              show Function.update st₀.regs 11 v rDst = dst
              rw [Function.update_of_ne hrD.2]; exact (hreg _ hrD.1 hrD.2).trans hD))
              (Expr.eval_reg_of_eq (Function.update_self 11 v st₀.regs)) hdx,
            Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
        refine ⟨_, 7 + 5 + 1, runs_seq_normal hr₁ hr₂, ⟨?_, ?_, ?_, ?_, ?_⟩, le_rfl⟩
        · show Function.update st₀.regs 11 v 10 = i
          rw [Function.update_of_ne (by omega)]; exact h10
        · intro r h1 h2
          show Function.update (Function.update st₀.regs 11 v) 10 (i + 1) r = _
          rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hreg r h1 h2
        · simp
        · intro a ha
          show Function.update st₀.mem (dst + v) 0 a = _
          rw [List.take_succ_eq_append_getElem hi, hv] at ha
          rw [Function.update_of_ne (ha _ (by simp))]
          exact hfr a fun x hx => ha x (List.mem_append_left _ hx)
        · intro x hx
          show Function.update st₀.mem (dst + v) 0 _ = 0
          rw [List.take_succ_eq_append_getElem hi, hv, List.mem_append, List.mem_singleton] at hx
          by_cases hxe : dst + x = dst + v
          · rw [hxe, Function.update_self]
          · rw [Function.update_of_ne hxe]
            rcases hx with hx | hx
            · exact hz x hx
            · exact absurd (by rw [hx]) hxe)
      (st := st) ⟨fun r h1 _ => by simp [h1], by simp, fun a _ => rfl,
        fun x hx => by simp at hx⟩
  rw [List.take_length] at hfr hz
  refine ⟨st', c, hr, hregs, hfr, hz, ?_⟩
  simp only [Expr.size] at hc
  omega

variable {tbl tourH n slotsPtr h slotCap eCap E : ℕ}

/-- **Phase D.** With the pairs `P` (`E` of them) at `h + 6 n + 2 E` and the listed slots in the
specs at `h + 4 n`, phase D writes `0` into `edgeSlot[e]` for every pair `(e, s)` and into the slot
pointer of every listed slot. It changes no other memory and no register but `10` and `11`. -/
theorem brPhaseD_runs {st : State} {slots : List ℕ} {P : List (ℕ × ℕ)}
    (hR : BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap) (hL : BRRegsL st.regs h n E)
    (hn : slots.length = n) (hw : 16 ≤ 2 ^ w) (hfit : h + 6 * n + 10 * E < 2 ^ w)
    (hPlen : P.length = E)
    (hP : ∀ j < E, st.mem (h + 6 * n + 2 * E + 2 * j) = (P.getD j (0, 0)).1)
    (hPe : ∀ x ∈ P, btEdgeSlotBase tbl slotCap + x.1 < h)
    (hspec : ∀ i < n, st.mem (h + 4 * n + 2 * i) = slots.getD i 0)
    (hslots : ∀ s ∈ slots, s < slotCap ∧ btSlotPtrBase tbl + s < h) :
    ∃ st' c, Runs w p ω brPhaseD st .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 11 → st'.regs r = st.regs r) ∧
      (∀ a, (∀ x ∈ P, a ≠ btEdgeSlotBase tbl slotCap + x.1) →
        (∀ s ∈ slots, a ≠ btSlotPtrBase tbl + s) → st'.mem a = st.mem a) ∧
      (∀ x ∈ P, st'.mem (btEdgeSlotBase tbl slotCap + x.1) = 0) ∧
      (∀ s ∈ slots, st'.mem (btSlotPtrBase tbl + s) = 0) ∧
      c ≤ 30 * E + 30 * n + 20 := by
  have hPm : (P.map Prod.fst).length = E := by rw [List.length_map, hPlen]
  obtain ⟨st₁, c₁, hr₁, hreg₁, hfr₁, hz₁, hc₁⟩ := brZeroLoop_runs (w := w) (p := p) (ω := ω)
    (rSrc := 14) (rDst := 6) (rN := 9) (by omega) (by omega) (by omega) (st := st)
    (src := h + 6 * n + 2 * E) (dst := btEdgeSlotBase tbl slotCap) (L := P.map Prod.fst) hw
    hL.r14 hR.r6 (by rw [hPm]; exact hL.r9)
    (fun i hi => by
      rw [hPm] at hi
      rw [hP i hi, List.getElem_map, List.getD_eq_getElem _ _ (by omega)])
    (by omega) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hPe y hy; omega)
    (fun x hx i hi => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hPe y hy; omega)
  have hspec₁ : ∀ i (hi : i < slots.length), st₁.mem (h + 4 * n + 2 * i) = slots[i] := by
    intro i hi
    rw [hfr₁ _ fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hPe y hy; omega]
    rw [hspec i (by omega), List.getD_eq_getElem _ _ hi]
  obtain ⟨st₂, c₂, hr₂, hreg₂, hfr₂, hz₂, hc₂⟩ := brZeroLoop_runs (w := w) (p := p) (ω := ω)
    (rSrc := 8) (rDst := 5) (rN := 2) (by omega) (by omega) (by omega) (st := st₁)
    (src := h + 4 * n) (dst := btSlotPtrBase tbl) (L := slots) hw
    ((hreg₁ 8 (by omega) (by omega)).trans hR.r8) ((hreg₁ 5 (by omega) (by omega)).trans hR.r5)
    ((hreg₁ 2 (by omega) (by omega)).trans (hR.r2.trans hn.symm)) hspec₁ (by omega)
    (fun x hx => by have := (hslots x hx).2; omega)
    (fun x hx i _ => by have := (hslots x hx).2; omega)
  refine ⟨st₂, c₁ + c₂ + 1, runs_seq_normal hr₁ hr₂, fun r h1 h2 => ?_, fun a ha hb => ?_,
    fun x hx => ?_, hz₂, by omega⟩
  · rw [hreg₂ r h1 h2, hreg₁ r h1 h2]
  · rw [hfr₂ a hb, hfr₁ a fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact ha z hz]
  · have hne : ∀ s ∈ slots, btEdgeSlotBase tbl slotCap + x.1 ≠ btSlotPtrBase tbl + s := by
      intro s hs
      have := (hslots s hs).1
      unfold btEdgeSlotBase btSlotPtrBase
      omega
    rw [hfr₂ _ hne]
    exact hz₁ _ (List.mem_map_of_mem hx)

end

end MinCostFlow.SparseCore.Program.Restart
