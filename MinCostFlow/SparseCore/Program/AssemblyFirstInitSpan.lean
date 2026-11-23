module

public import MinCostFlow.SparseCore.Program.RestartMain
public import MinCostFlow.SparseCore.Program.BunRestartPhaseA
public import MinCostFlow.SparseCore.Program.BunRestartPhaseE

/-!
# P6's spanners at the init of a branch (`AssemblyFirstInitSpan`)

At the init of a branch, each active pair gets a fresh bucket spanner on the graph of its
bundle. P6 starts the spanner of a slot with operation `0`, which reads the graph from an export.
So the init does two things, one procedure each.
1. `asmFirstInitExpBody` exports the graph of each listed slot of the bundle table. It is the
   restart of the bundles without its middle phases: phase A writes the specs of the slots, and
   phase E writes the exports and their descriptors (`asmFirstInitExp_runs`).
2. `asmFirstInitSpanBody` calls the export, then runs operation `0` of P6 on each listed slot,
   with the graph of its descriptor. This is the loop of the restart of a branch
   (`restartBranchStmt`), so its proof is `restartLoop_triple` and its cost is `loopCost_le`
   (`asmFirstInitSpan_runs`).

The table of the spanners starts empty: `cap` zero words (`bucketSpannerRep_empty`). P6's
init only returns the end of these words, so the init needs no call for it.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- **The export of the listed slots**, `[tbl, tourH, n, slotsPtr, h]`: phase A of the restart of
the bundles (the specs of the `n` slots listed at `slotsPtr`), then phase E (the export of the
graph of each slot and its descriptor at `h + 4 i`); it returns the heap pointer. -/
def asmFirstInitExpBody (bExport : ℕ) : Stmt :=
  brPhaseA ;; brPhaseE bExport ;; .ret (.reg 19)

/-- **P6's operation `0` on the listed slots**, `[bunTbl, tourH, spanTbl, x3, n, slotsPtr, h, x7,
x8, splitBound, vCap, eCap, L]` (the layout of `restartBranchStmt`; the words `x3`, `x7`, `x8` are
not read):
1. call the export (`fExp`), which writes the descriptors at `h, h + 4, …` and returns the heap
   pointer in register `13`;
2. for each `i < n`, call operation `0` of the bucket spanners (`fAct`) on slot `slots[i]` with
   the graph of descriptor `i`;
3. return the heap pointer. -/
def asmFirstInitSpanBody (fExp fAct : ℕ) : Stmt :=
  .call 13 fExp [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6] ;;
  forRange 14 (.const 0) (.reg 4) (restartLoopBody fAct) ;;
  .ret (.reg 13)

/-- The graph on which the spanner of slot `s` starts: the graph of its bundle, normalized. -/
noncomputable def asmFirstInitSlotGraph {slotCap : ℕ} (S : Fin slotCap → Option BundleState)
    (s : ℕ) : MGraph :=
  normGraph (slotB S s).graph

end

public section

theorem asmFirstInitExpBody_noRand (bExport : ℕ) : (asmFirstInitExpBody bExport).NoRand := by
  simp [asmFirstInitExpBody, brPhaseA, brPhaseE, brStart, brLayout, brLoopABody, brLoopEBody,
    forRange, forUp, Stmt.NoRand]

theorem asmFirstInitSpanBody_noRand (fExp fAct : ℕ) :
    (asmFirstInitSpanBody fExp fAct).NoRand := by
  simp [asmFirstInitSpanBody, restartLoopBody, forRange, forUp, Stmt.NoRand]

/-- The empty table of the spanners: `cap` zero words at `tbl`. -/
theorem bucketSpannerRep_empty (P : DSParams) (cap tbl : ℕ) {mem : ℕ → ℕ}
    (hz : ∀ j < cap, mem (tbl + j) = 0) :
    (bucketSpannerRep P cap).rep tbl (fun _ => none) ⟨fun _ => none⟩ mem := by
  refine ⟨fun j => ?_, fun _ _ _ _ _ _ _ h1 => by simp at h1⟩
  exact hz j.1 j.2

theorem bucketSpannerFoot_empty {P : DSParams} {cap tbl a : ℕ}
    (ha : (bucketSpannerRep P cap).foot tbl ⟨fun _ => none⟩ a) : tbl ≤ a ∧ a < tbl + cap := by
  rcases ha with h | ⟨_, _, _, h, _⟩
  · exact h
  · simp at h

theorem specPhi_empty (P : DSParams) (cap : ℕ) :
    specPhi P (fun _ => none : BucketSpannerState cap) = 0 := by
  simp [specPhi]

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- **The run of the export.** The listed slots hold bundles, the table and the list lie below
`h`, and memory from `h` on is zero. The export returns the end of the exports, after the
descriptors and the specs (`6 n` words) and the scratch arrays of phase A (`10 E` words, where
`E` is the number of edges of the listed slots). Descriptor `i`, at `h + 4 i`, describes the
graph of slot `slots[i]`. Memory below `h` is unchanged. -/
theorem asmFirstInitExp_runs {bExport : ℕ} (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    {slotCap vCap eCap tbl tourH slotsPtr h pos : ℕ} {slots : List ℕ}
    {S : Fin slotCap → Option BundleState} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hw : 16 ≤ 2 ^ w)
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (hlist : ListAt mem slotsPtr slots) (hsl : slotsPtr + slots.length ≤ h)
    (hz : ZeroFrom mem h)
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots +
      (slots.map fun s => bundleExportSpace (slotB S s)).sum < 2 ^ w)
    (htblw : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) :
    ∃ o st' c, Runs w p ω (asmFirstInitExpBody bExport)
        (startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) o st' c ∧
      o.value = h + 6 * slots.length + 10 * edgeTot S slots +
        (slots.map fun s => bundleExportSpace (slotB S s)).sum ∧
      ZeroFrom st'.mem o.value ∧
      BundleTableRepAt slotCap vCap eCap tbl S m st'.mem ∧
      (∀ i (hi : i < slots.length), ExportAt st'.mem (h + 4 * i) o.value (slotB S slots[i]).graph) ∧
      (∀ a < h, st'.mem a = mem a) ∧
      c ≤ (slots.map fun s => bundleExportCost (slotB S s)).sum + 140 * slots.length + 140 := by
  set st0 := startState [tbl, tourH, slots.length, slotsPtr, h] mem pos with hst0
  obtain ⟨st₁, c₁, hr₁, hR₁, -, h19₁, -, hspec₁, hfr₁, hc₁⟩ :=
    brPhaseA_runs (w := w) (p := p) (ω := ω) (tourH := tourH) hrep hfoot hact hlist hsl hw
      (by omega)
      (st := st0) (by simp [hst0, startState]) (by simp [hst0, startState])
      (by simp [hst0, startState]) (by simp [hst0, startState]) (by simp [hst0, startState]) rfl
  have hkeep₁ : ∀ a, a < h → st₁.mem a = mem a := fun a ha => hfr₁ a (Or.inl (by omega))
  have htab₁ : BundleTableRepAt slotCap vCap eCap tbl S m st₁.mem :=
    hrep.of_agree fun a ha => (hkeep₁ a (hfoot a ha)).symm
  obtain ⟨stE, cE, hrE, h19E, hzE, htabE, hexE, hfrE, hcE⟩ :=
    brPhaseE_runs (p := p) (ω := ω) hpExport hw hR₁ h19₁ hact
      (fun i hi => by rw [(hspec₁ i hi).1, List.getD_eq_getElem _ _ hi])
      htab₁ (fun a ha => Or.inl (hfoot a ha))
      (fun a ha => by rw [hfr₁ a (Or.inr (by omega))]; exact hz a (by omega))
      (by omega) (by omega) htblw
  have hret : Runs w p ω (.ret (.reg 19)) stE (.returned (stE.regs 19)) stE 2 :=
    runs_ret_iff.mpr ⟨_, by simp [Expr.eval], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨stE, _, _, hrE, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨st₁, _, _, hr₁, t1, rfl⟩)
  refine ⟨_, _, _, t2, h19E, ?_, htabE, ?_, ?_, ?_⟩
  · show ZeroFrom stE.mem (stE.regs 19); exact hzE
  · intro i hi; exact hexE i hi
  · intro a ha
    rw [hfrE a (by omega) (by omega)]
    exact hkeep₁ a ha
  · omega

/-- **The run of P6's operation `0` on the listed slots at the init.** The bundle table, the slot
list and the empty table of `cap` spanners at `spanTbl` lie below `h`, the spanner table is apart
from the slot list, and memory from `h` on is zero. Each listed slot holds a bundle and is below
`cap`, and its graph meets the conditions of a spanner initialization (`SpanGraphOK`). Then the
procedure ends with the spanner of each listed slot started on its graph
(`spanAfter (fun _ => none) (asmFirstInitSlotGraph S) slots`), whose new cells lie in the table
or in `[h, o)`. Memory below `h` outside the spanner table is unchanged. The cost and the new bank
of the spanners are at most the export costs and the bounds of operation `0` on the slots, plus
`200` per slot and `200`. -/
theorem asmFirstInitSpan_runs {P : DSParams} {cap fExp bExport bSpan : ℕ}
    (hfE : p.procs[fExp]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    {slotCap vCap eCap bunTbl tourH spanTbl x3 slotsPtr h x7 x8 pos : ℕ} {slots : List ℕ}
    {S : Fin slotCap → Option BundleState} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hw : 16 ≤ 2 ^ P.w) (hLW : P.L < 2 ^ P.w) (hSplitW : P.splitBound < 2 ^ P.w)
    (hVW : P.vCap < 2 ^ P.w) (hEW : P.eCap < 2 ^ P.w)
    (hrep : BundleTableRepAt slotCap vCap eCap bunTbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap bunTbl m a → a < h)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (hlist : ListAt mem slotsPtr slots) (hsl : slotsPtr + slots.length ≤ h)
    (hz : ZeroFrom mem h)
    (htblw : bunTbl + bundleTableFixedSize slotCap eCap < 2 ^ P.w)
    (hok : ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s))
    (hcap : ∀ s ∈ slots, s < cap)
    (hspanH : spanTbl + cap ≤ h) (hspanZ : ∀ j < cap, mem (spanTbl + j) = 0)
    (hspanL : ∀ a, spanTbl ≤ a → a < spanTbl + cap → ¬ (slotsPtr ≤ a ∧ a < slotsPtr + slots.length))
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots +
      (slots.map fun s => bundleExportSpace (slotB S s)).sum +
      (slots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S s)).sum < 2 ^ P.w) :
    ∃ o st' c x6, Runs P.w p ω (asmFirstInitSpanBody fExp (bSpan + bsIdxOp0 + 0))
        (startState [bunTbl, tourH, spanTbl, x3, slots.length, slotsPtr, h, x7, x8, P.splitBound,
          P.vCap, P.eCap, P.L] mem pos) o st' c ∧
      (bucketSpannerRep P cap).rep spanTbl
        (spanAfter (fun _ => none) (asmFirstInitSlotGraph S) slots) x6 st'.mem ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a →
        (spanTbl ≤ a ∧ a < spanTbl + cap) ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a < h, ¬ (spanTbl ≤ a ∧ a < spanTbl + cap) → st'.mem a = mem a) ∧
      h ≤ o.value ∧
      o.value ≤ h + 6 * slots.length + 10 * edgeTot S slots +
        (slots.map fun s => bundleExportSpace (slotB S s)).sum +
        (slots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S s)).sum ∧
      ZeroFrom st'.mem o.value ∧
      c + specPhi P (spanAfter (fun _ => none : BucketSpannerState cap) (asmFirstInitSlotGraph S)
        slots) ≤
        (slots.map fun s => bundleExportCost (slotB S s)).sum +
        (slots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S s)).sum +
        200 * slots.length + 200 := by
  set g := asmFirstInitSlotGraph S with hg
  set st0 := startState [bunTbl, tourH, spanTbl, x3, slots.length, slotsPtr, h, x7, x8, P.splitBound,
    P.vCap, P.eCap, P.L] mem pos with hst0
  -- Step 1: the export.
  obtain ⟨o5, st5, c5, hrun5, hov5, hz5, -, hexp5, hfr5, hc5⟩ :=
    asmFirstInitExp_runs (w := P.w) (p := p) (ω := ω) (tourH := tourH) (pos := pos) hpExport hw
      hrep hfoot hact hlist hsl hz (by omega) htblw
  set h1 := o5.value with hh1def
  set st1 : State := { st5 with regs := Function.update st0.regs 13 h1 } with hst1
  have hcall5 : Runs P.w p ω (.call 13 fExp [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6]) st0
      .normal st1 (argsSize [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6] + c5 + 1) :=
    runs_call_iff.mpr ⟨[bunTbl, tourH, slots.length, slotsPtr, h], _, o5, st5, c5,
      by simp [evalArgs, Expr.eval, hst0, startState], hfE, hrun5, rfl, rfl, rfl⟩
  have hspanZ5 : ∀ j < cap, st5.mem (spanTbl + j) = 0 := by
    intro j hj
    rw [hfr5 _ (by omega)]
    exact hspanZ j hj
  have hlist5 : ListAt st5.mem slotsPtr slots := by
    intro i hi
    rw [hfr5 _ (by omega)]
    exact hlist i hi
  have hrep6 := bucketSpannerRep_empty P cap spanTbl hspanZ5
  -- Step 2: the loop.
  have LH : LoopHyps P cap st1.regs spanTbl slotsPtr h h1 (fun _ => none) ⟨fun _ => none⟩ g
      slots st5.mem :=
    { hR2 := by simp [hst1, hst0, startState]
      hR4 := by simp [hst1, hst0, startState]
      hR5 := by simp [hst1, hst0, startState]
      hR6 := by simp [hst1, hst0, startState]
      hR9 := by simp [hst1, hst0, startState]
      hR10 := by simp [hst1, hst0, startState]
      hR11 := by simp [hst1, hst0, startState]
      hR12 := by simp [hst1, hst0, startState]
      hw16 := hw
      hL := hLW
      hSplit := hSplitW
      hV := hVW
      hE := hEW
      hlist := hlist5
      hlist_h := hsl
      hlist_free := fun a ha1 ha2 hf => by
        have := bucketSpannerFoot_empty hf
        exact hspanL a this.1 this.2 ⟨ha1, ha2⟩
      hh1 := by omega
      hexp := fun i hi => ⟨_, hexp5 i hi, rfl⟩
      hok := hok
      hact := hcap
      hrep := hrep6
      hfoot := fun a ha => by have := bucketSpannerFoot_empty ha; omega
      hz := hz5
      hspace := by omega }
  obtain ⟨oL, st2, cL, hrunL, hpostL, hcL⟩ :=
    restartLoop_triple hp LH st1 ω ⟨rfl, fun _ _ => rfl, by simp [hst1]⟩
  cases oL with
  | returned u => exact absurd hpostL (by simp)
  | normal =>
  obtain ⟨-, -, hc1, hc2, hz2, hfr2, hph, x6n, hrep6n, hft6n⟩ := hpostL
  rw [List.take_length] at hrep6n
  have hsum := sum_range_getD (fun s => spanActivateSpace P (g s)) slots
  have hLc := loopCost_le P (fun _ => none : BucketSpannerState cap) g slots hph
  rw [List.take_length, List.take_zero, spanAfter_nil, specPhi_empty] at hLc
  simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hcL
  have hret : Runs P.w p ω (.ret (.reg 13)) st2 (.returned (st2.regs 13)) st2 2 :=
    runs_ret_iff.mpr ⟨_, by simp [Expr.eval], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hrunL, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hcall5, t1, rfl⟩)
  have hfr2' : ∀ a < h1, ¬ (spanTbl ≤ a ∧ a < spanTbl + cap) → st2.mem a = st5.mem a :=
    fun a ha hn' => hfr2 a ha fun hf => hn' (bucketSpannerFoot_empty hf)
  refine ⟨_, _, _, x6n, t2, hrep6n, ?_, ?_, ?_, ?_, hz2, ?_⟩
  · intro a ha
    rcases hft6n a ha with h6 | ⟨hle, hlt⟩
    · exact Or.inl (bucketSpannerFoot_empty h6)
    · exact Or.inr ⟨by omega, hlt⟩
  · intro a ha hn'
    rw [hfr2' a (by omega) hn', hfr5 a ha]
  · show h ≤ st2.regs 13
    omega
  · show st2.regs 13 ≤ _
    rw [hsum] at hc2
    omega
  · simp only [argsSize, Expr.size] at hcL ⊢
    omega

end

end MinCostFlow.SparseCore.Program
