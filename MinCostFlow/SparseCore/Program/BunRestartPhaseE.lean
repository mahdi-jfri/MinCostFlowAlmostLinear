module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseE1

/-!
# The restart of the bundles: phase E (`BunRestartPhaseE`)

Loop E exports the graph of each listed slot of the new table, one after the other on the heap,
and writes its descriptor at `h + 4 i` (`brPhaseE_runs`). The cost of round `i` depends on the
slot, so the loop pays it against the export costs of the rounds still to come
(`runs_forRange_amort`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

theorem exportAt_bounds {mem : ℕ → ℕ} {d hE : ℕ} {G : MGraph} (hex : ExportAt mem d hE G) :
    mem (d + 1) + mem d ≤ hE ∧ mem (d + 3) + 3 * mem (d + 2) ≤ hE :=
  ⟨hex.2.2.2.2.2.2.2.2.2.2.1, hex.2.2.2.2.2.2.2.2.2.2.2⟩

theorem sum_take_succ (f : ℕ → ℕ) {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    ((l.take (i + 1)).map f).sum = ((l.take i).map f).sum + f l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

theorem sum_take_le (f : ℕ → ℕ) (l : List ℕ) (i : ℕ) :
    ((l.take i).map f).sum ≤ (l.map f).sum := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.map_append, List.sum_append]
  omega

theorem sum_drop_eq (f : ℕ → ℕ) {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    ((l.drop i).map f).sum = f l[i] + ((l.drop (i + 1)).map f).sum := by
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.sum_cons]

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- The invariant of loop E after `i` rounds. -/
structure BrEInv (slotCap vCap eCap tbl tourH slotsPtr h hEnd : ℕ) (slots : List ℕ)
    (T : BundleTableState slotCap) (M' : BundleTableMeta slotCap) (stI : State) (i : ℕ)
    (st : State) : Prop where
  regs : BRRegs st.regs tbl tourH slots.length slotsPtr h slotCap eCap
  r10 : st.regs 10 = i
  r19 : st.regs 19 = hEnd + ((slots.take i).map fun s => bundleExportSpace (slotB T s)).sum
  zero : ZeroFrom st.mem (st.regs 19)
  tab : BundleTableRepAt slotCap vCap eCap tbl T M' st.mem
  frame : ∀ a < hEnd, ¬ (h ≤ a ∧ a < h + 4 * i) → st.mem a = stI.mem a
  ex : ∀ j < i, ExportAt st.mem (h + 4 * j) (st.regs 19) (slotB T (slots.getD j 0)).graph ∧
    hEnd ≤ st.mem (h + 4 * j + 1) ∧ hEnd ≤ st.mem (h + 4 * j + 3)

/-- **Phase E.** Each listed slot `s` holds a bundle state in the table `T`, the specs give the
slots, and the table lies outside the descriptors `[h, h + 4 n)` and below `hEnd`. Loop E then
writes at `h + 4 i` the descriptor of the graph of slot `slots[i]` and moves the heap pointer by
the export spaces of all slots. Below `hEnd` it writes only the descriptors. -/
theorem brPhaseE_runs {bExport : ℕ} (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    {slotCap vCap eCap tbl tourH slotsPtr h hEnd : ℕ} {slots : List ℕ}
    {T : BundleTableState slotCap} {M' : BundleTableMeta slotCap} {stI : State}
    (hw : 16 ≤ 2 ^ w) (hR : BRRegs stI.regs tbl tourH slots.length slotsPtr h slotCap eCap)
    (h19 : stI.regs 19 = hEnd)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, T ⟨s, hs⟩ = some B)
    (hspec : ∀ i < slots.length, stI.mem (h + 4 * slots.length + 2 * i) = slots.getD i 0)
    (htab : BundleTableRepAt slotCap vCap eCap tbl T M' stI.mem)
    (hfootT : ∀ a, bundleTableFoot eCap tbl M' a →
      a < h ∨ (h + 4 * slots.length ≤ a ∧ a < hEnd))
    (hz : ZeroFrom stI.mem hEnd) (hlay : h + 6 * slots.length ≤ hEnd)
    (hfit : hEnd + (slots.map fun s => bundleExportSpace (slotB T s)).sum < 2 ^ w)
    (htblw : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) :
    ∃ stE cE, Runs w p ω (brPhaseE bExport) stI .normal stE cE ∧
      stE.regs 19 = hEnd + (slots.map fun s => bundleExportSpace (slotB T s)).sum ∧
      ZeroFrom stE.mem (stE.regs 19) ∧
      BundleTableRepAt slotCap vCap eCap tbl T M' stE.mem ∧
      (∀ i (hi : i < slots.length),
        ExportAt stE.mem (h + 4 * i) (stE.regs 19) (slotB T slots[i]).graph) ∧
      (∀ a < hEnd, ¬ (h ≤ a ∧ a < h + 4 * slots.length) → stE.mem a = stI.mem a) ∧
      cE ≤ (slots.map fun s => bundleExportCost (slotB T s)).sum + 80 * slots.length + 10 := by
  set n := slots.length with hn
  have hnw : n < 2 ^ w := by
    have := hR.r8; omega
  obtain ⟨stE, cE, g, hr, ⟨hg, hI⟩, hc⟩ := runs_forRange_amort (w := w) (p := p) (ω := ω)
    (r := 10) (hi := .reg 2) (body := brLoopEBody bExport)
    (Inv := fun i g st => g = i ∧
      BrEInv slotCap vCap eCap tbl tourH slotsPtr h hEnd slots T M' stI i st)
    (fun g _ => ((slots.drop g).map fun s => bundleExportCost (slotB T s)).sum) 70 n (by omega)
    hnw
    (fun i g st _ hI => hI.2.r10) (fun i g st _ hI => Expr.eval_reg_of_eq hI.2.regs.r2)
    (fun i g st hi hI => by
      obtain ⟨hgi, hI⟩ := hI
      subst g
      obtain ⟨hs, B, hB⟩ := hact slots[i] (List.getElem_mem hi)
      have hsB : slotB T slots[i] = B := slotB_eq hs hB
      have hgd : slots.getD i 0 = slots[i] := List.getD_eq_getElem _ _ hi
      have hsum := sum_take_succ (fun s => bundleExportSpace (slotB T s)) hi
      have hle := sum_take_le (fun s => bundleExportSpace (slotB T s)) slots (i + 1)
      simp only [hsB] at hsum
      have hr19 := hI.r19
      obtain ⟨st₁, c, hr₁, hreg₁, hfr₁, hz₁, hex₁, hlo1, hlo3, hc₁⟩ := brLoopE_round
        (p := p) (ω := ω) hpExport (n := n) (i := i) (hc := st.regs 19) (s := slots[i])
        (B := B) (st := st) hw hI.regs.r0 hI.regs.r4 hI.regs.r8 hI.r10 rfl hi
        (by rw [hI.frame _ (by omega) (by omega), hspec i hi, hgd]) hs hB hI.tab
        (fun a ha => by rcases hfootT a ha with h' | h' <;> omega) hI.zero
        (by rw [hr19]; omega) htblw (by omega)
      have hreg' : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 19 →
          (Function.update st₁.regs 10 (i + 1)) r = st.regs r := by
        intro r h1 h2 h3 h4
        rw [Function.update_of_ne h1, hreg₁]
        simp [h2, h3, h4]
      have hnew19 : (Function.update st₁.regs 10 (i + 1)) 19 =
          st.regs 19 + bundleExportSpace B := by
        rw [Function.update_of_ne (by omega), hreg₁]; simp
      have hkeep : ∀ a < st.regs 19, ¬ (h + 4 * i ≤ a ∧ a < h + 4 * i + 4) →
          st₁.mem a = st.mem a := hfr₁
      refine ⟨st₁, c, i + 1, hr₁, by rw [hreg₁]; simp [hI.r10], ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?_⟩
      · exact hI.regs.of_eq fun r hr => hreg' r (by omega) (by omega) (by omega) (by omega)
      · simp
      · show (Function.update st₁.regs 10 (i + 1)) 19 = _
        rw [hnew19, hr19, hsum]; omega
      · show ZeroFrom st₁.mem ((Function.update st₁.regs 10 (i + 1)) 19)
        rw [hnew19]; exact hz₁
      · exact hI.tab.of_agree fun a ha => by
          rcases hfootT a ha with h' | h'
          · exact (hkeep a (by omega) (by omega)).symm
          · exact (hkeep a (by omega) (by omega)).symm
      · intro a ha hna
        show st₁.mem a = _
        rw [hkeep a (by omega) (by omega)]
        exact hI.frame a ha (by omega)
      · intro j hj
        show ExportAt st₁.mem (h + 4 * j) ((Function.update st₁.regs 10 (i + 1)) 19)
          (slotB T (slots.getD j 0)).graph ∧ hEnd ≤ st₁.mem (h + 4 * j + 1) ∧
          hEnd ≤ st₁.mem (h + 4 * j + 3)
        rw [hnew19]
        by_cases hji : j = i
        · rw [hji, hgd, hsB]
          refine ⟨hex₁, ?_, ?_⟩
          · have := hI.r19; omega
          · have := hI.r19; omega
        · obtain ⟨hexj, hj1, hj3⟩ := hI.ex j (by omega)
          obtain ⟨hb1, hb3⟩ := exportAt_bounds hexj
          refine ⟨brExportAt_congr hexj (by omega) fun a ha => hkeep a (by omega) (by omega),
            ?_, ?_⟩
          · rw [hkeep _ (by omega) (by omega)]; exact hj1
          · rw [hkeep _ (by omega) (by omega)]; exact hj3
      · rw [sum_drop_eq (fun s => bundleExportCost (slotB T s)) hi]
        simp only [hsB]
        omega)
    (st := stI) (g := 0)
    ⟨rfl, hR.of_eq fun r hr => Function.update_of_ne (by omega) _ _, by simp,
      by simp [h19], by simpa [h19] using hz, htab, fun a _ _ => rfl,
      fun j hj => absurd hj (by omega)⟩
  rw [hg] at hc
  have htk : slots.take n = slots := List.take_length
  have hdr : slots.drop n = [] := List.drop_length
  refine ⟨stE, cE, hr, by rw [hI.r19, htk], hI.zero, hI.tab, fun i hi => ?_,
    fun a ha hna => hI.frame a ha hna, ?_⟩
  · have := (hI.ex i hi).1
    rwa [List.getD_eq_getElem _ _ hi] at this
  · rw [hdr] at hc
    simp only [List.map_nil, List.sum_nil, Expr.size, List.drop_zero] at hc
    omega

end

end MinCostFlow.SparseCore.Program.Restart
