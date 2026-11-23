module

public import MinCostFlow.SparseCore.Program.BunRestartLib

/-!
# The restart of the bundles: phase A (`BunRestartPhaseA`)

Phase A sets the registers, copies the listed slots into the specs `(s, 2 |E_s|)` at `h + 4 n`
(loop A), adds up the edge count `E = edgeTot S slots`, and lays out the five arrays of `2 E` words
that follow the specs (`brPhaseA_runs`). It reads only memory below `h`, which it does not change,
and writes only the specs.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w slotCap vCap eCap tbl tourH slotsPtr h : ℕ} {p : Program} {ω : ℕ → Bool}
  {S : Fin slotCap → Option BundleState} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
  {slots : List ℕ}

theorem edgeTot_take_succ {i : ℕ} (hi : i < slots.length) :
    edgeTot S (slots.take (i + 1)) = edgeTot S (slots.take i) + (slotB S slots[i]).edges.card := by
  unfold edgeTot
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

theorem edgeTot_take_le (i : ℕ) : edgeTot S (slots.take i) ≤ edgeTot S slots := by
  unfold edgeTot
  conv_rhs => rw [← List.take_append_drop i slots]
  rw [List.map_append, List.sum_append]
  omega

/-- What the restart reads in the table for an active slot `s`: its slot pointer `p` and the edge
count at `p + 2`, both below `h`. -/
theorem slot_reads (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl m a → a < h) {s : ℕ} (hs : s < slotCap)
    {B : BundleState} (hB : S ⟨s, hs⟩ = some B) :
    mem (btSlotPtrBase tbl + s) = (slotBlk m s).1 ∧ btSlotPtrBase tbl + s < h ∧
      mem ((slotBlk m s).1 + 2) = (slotB S s).edges.card ∧ (slotBlk m s).1 + 2 < h := by
  obtain ⟨hm, hptr, hslot, -⟩ := slot_facts hrep hs hB
  refine ⟨hptr, hfoot _ (btSlotPtr_in_foot hs), ?_,
    hfoot _ (bsAddr_in_foot (j := ⟨s, hs⟩) hm (by unfold bundleSlotBlockSize; omega))⟩
  rw [slotB_eq hs hB]
  obtain ⟨nB, -, -, -, -, -, -, -, h2, -⟩ := hslot
  exact h2

/-- **Phase A.** From the start state of the restart, phase A ends with the registers of
`BRRegs` and `BRRegsL`, the heap pointer `h + 6 n + 10 E` in register `19`, `0` in register `20`,
and the specs `(slots[i], 4 |E_{slots[i]}|)` at `h + 4 n + 2 i`; it writes nothing else. -/
theorem brPhaseA_runs (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (hlist : ListAt mem slotsPtr slots) (hsl : slotsPtr + slots.length ≤ h)
    (hw : 16 ≤ 2 ^ w)
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots < 2 ^ w)
    {st : State} (h0 : st.regs 0 = tbl) (h1 : st.regs 1 = tourH)
    (h2 : st.regs 2 = slots.length) (h3 : st.regs 3 = slotsPtr) (h4 : st.regs 4 = h)
    (hmem : st.mem = mem) :
    ∃ st' c, Runs w p ω brPhaseA st .normal st' c ∧
      BRRegs st'.regs tbl tourH slots.length slotsPtr h slotCap eCap ∧
      BRRegsL st'.regs h slots.length (edgeTot S slots) ∧
      st'.regs 19 = h + 6 * slots.length + 10 * edgeTot S slots ∧ st'.regs 20 = 0 ∧
      (∀ i (hi : i < slots.length), st'.mem (h + 4 * slots.length + 2 * i) = slots[i] ∧
        st'.mem (h + 4 * slots.length + 2 * i + 1) = 4 * (slotB S slots[i]).edges.card) ∧
      (∀ a, (a < h + 4 * slots.length ∨ h + 6 * slots.length ≤ a) → st'.mem a = mem a) ∧
      c ≤ 60 * slots.length + 120 := by
  set n := slots.length with hn
  set E := edgeTot S slots with hE
  have hb3 : tbl + 3 < h := hfoot _ (btHeader_in_foot (by unfold btHdrSize; omega))
  have hb4 : tbl + 4 < h := hfoot _ (btHeader_in_foot (by unfold btHdrSize; omega))
  have hb7 : tbl + 7 < h := hfoot _ (btHeader_in_foot (by unfold btHdrSize; omega))
  have hm3 : st.mem (tbl + 3) = btSlotPtrBase tbl := hmem ▸ hrep.2.2.2.1
  have hm4 : st.mem (tbl + 4) = btEdgeSlotBase tbl slotCap := hmem ▸ hrep.2.2.2.2.1
  have hm7 : st.mem (tbl + 7) = btEndNextBase tbl slotCap eCap := hmem ▸ hrep.2.2.2.2.2.2.2.1
  -- The start.
  obtain ⟨st₁, c₁, hr₁, ⟨hR₁, h9₁, hmem₁⟩, hc₁⟩ := normal_of_fwd (w := w) (p := p) (ω := ω) (s := brStart) (st := st) (K := 30)
    (P := fun st₁ => BRRegs st₁.regs tbl tourH n slotsPtr h slotCap eCap ∧ st₁.regs 9 = 0 ∧
      st₁.mem = mem) (by
    unfold brStart
    wram_run
    · simp only [normalPost_normal]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, hmem⟩ <;>
        simp [h0, h1, h2, h3, h4, hm3, hm4, hm7]
    · wram_cost)
  -- Loop A.
  let Inv : ℕ → State → Prop := fun i st =>
    BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap ∧ st.regs 10 = i ∧
      st.regs 9 = edgeTot S (slots.take i) ∧
      (∀ q (hq : q < n), q < i → st.mem (h + 4 * n + 2 * q) = slots[q] ∧
        st.mem (h + 4 * n + 2 * q + 1) = 4 * (slotB S slots[q]).edges.card) ∧
      (∀ a, (a < h + 4 * n ∨ h + 4 * n + 2 * i ≤ a) → st.mem a = mem a)
  obtain ⟨st₂, c₂, hr₂, ⟨hR₂, -, h9₂, hspec₂, hfr₂⟩, hc₂⟩ :=
    runs_forRange_const (w := w) (p := p) (ω := ω) (r := 10) (hi := .reg 2) (body := brLoopABody)
      (Inv := Inv) 50 n (by omega) (by omega)
      (fun i st _ hI => hI.2.1) (fun i st _ hI => by simp [Expr.eval, hI.1.r2])
      (fun i st hi hI => by
        obtain ⟨hR, h10, h9, hdone, hfr⟩ := hI
        have hR' := hR
        obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩ := hR'
        have hsi : slots[i] ∈ slots := List.getElem_mem hi
        obtain ⟨hs, B, hB⟩ := hact _ hsi
        obtain ⟨hp, hpb, hnE, hnEb⟩ := slot_reads hrep hfoot hs hB
        have hm1 : st.mem (slotsPtr + i) = slots[i] := by
          rw [hfr _ (Or.inl (by omega))]; exact hlist i hi
        have hm2 : st.mem (btSlotPtrBase tbl + slots[i]) = (slotBlk m slots[i]).1 := by
          rw [hfr _ (Or.inl (by omega))]; exact hp
        have hm3' : st.mem ((slotBlk m slots[i]).1 + 2) = (slotB S slots[i]).edges.card := by
          rw [hfr _ (Or.inl (by omega))]; exact hnE
        have hsum := edgeTot_take_succ (S := S) hi
        have hsumle := edgeTot_take_le (S := S) (slots := slots) (i + 1)
        refine normal_of_fwd ?_
        unfold brLoopABody
        wram_step; simp only [hm1]
        wram_step; simp only [hr5, hm2]
        wram_step; simp only [hm3']
        wram_run
        swap
        · wram_cost
        simp only [normalPost_normal, hr8, h10]
        refine ⟨by simp [h10], ((((hR.upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega), by simp, by simp [hsum, h9], ?_, ?_⟩
        · intro q hq hqi
          by_cases hqe : q = i
          · subst hqe
            refine ⟨?_, Function.update_self _ _ _⟩
            simp (disch := omega) only [Function.update_of_ne]
            exact Function.update_self _ _ _
          · have hqi' : q < i := by omega
            obtain ⟨hd1, hd2⟩ := hdone q hq hqi'
            simp (disch := omega) only [Function.update_of_ne]
            exact ⟨hd1, hd2⟩
        · intro a ha
          simp (disch := omega) only [Function.update_of_ne]
          exact hfr a (by omega))
      (st := st₁) ⟨hR₁.upd (by omega), by simp, by simp [h9₁, edgeTot], fun q _ hq => absurd hq (by omega),
        fun a _ => by simp [hmem₁]⟩
  -- The layout.
  obtain ⟨st₃, c₃, hr₃, hq₃, hc₃⟩ := normal_of_fwd (w := w) (p := p) (ω := ω) (s := brLayout) (st := st₂)
    (K := 60)
    (P := fun st₃ => BRRegs st₃.regs tbl tourH n slotsPtr h slotCap eCap ∧
      BRRegsL st₃.regs h n E ∧ st₃.regs 19 = h + 6 * n + 10 * E ∧ st₃.regs 20 = 0 ∧
      st₃.mem = st₂.mem) (by
    have hE9 : st₂.regs 9 = E := by rw [h9₂, List.take_length]
    obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩ := hR₂
    unfold brLayout
    wram_run
    · simp only [normalPost_normal]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
        simp [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hE9] <;> omega
    · wram_cost)
  obtain ⟨hR₃, hL₃, h19₃, h20₃, hmem₃⟩ := hq₃
  refine ⟨st₃, c₁ + (c₂ + c₃ + 1) + 1, runs_seq_normal hr₁ (runs_seq_normal hr₂ hr₃), hR₃, hL₃,
    h19₃, h20₃, fun i hi => ?_, fun a ha => ?_, ?_⟩
  · rw [hmem₃]; exact hspec₂ i hi hi
  · rw [hmem₃]; exact hfr₂ a (by omega)
  · simp only [Expr.size_reg] at hc₂
    omega

end

end MinCostFlow.SparseCore.Program.Restart
