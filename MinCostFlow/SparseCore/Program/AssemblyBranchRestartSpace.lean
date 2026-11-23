module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartBound
public import MinCostFlow.SparseCore.Program.AssemblyBranchSpaceSpan
import MinCostFlow.SparseCore.Program.EmbRefreshBound

/-!
# The sizes of the slots after a restart (`AssemblyBranchRestartSpace`)

The heap space of the restart of a branch (`asmBrRestartSpace`) has three terms that depend on the
new spanners of the listed slots: the space of their initializations, the size `rebuildSize` of
the graphs that P10 reads to rebuild its graph `S`, and the size `embRefreshSizeAt` of the walks
that the refresh writes into the embedding table. To bound the space by a polynomial in the sizes
of the instance, we bound each term by the number of slots times a polynomial in the caps `spV`,
`spE` of the spanners and the walk length bound `⌈γ_ℓ mMax⌉` of the sparsifier.

The argument is the same for the three terms. After the restart, a listed slot `s` holds a fresh
spanner `⟨Hb, []⟩` on its new graph `Hb = restartSlotGraph …` (`restartSpanState_listed`). The
bundle side keeps `SpanGraphOK` for `Hb`, so the vertices of `Hb` are below `spV` and its edges
below `spE` (`spanGraphOK_n_le`, `spanGraphOK_m_le`). Then:
* the graph of the fresh spanner is `Hb`, and its spanner is a subgraph, so a slot adds at most
  `2 spE` to `rebuildSize` (`rebuildSize_restartSpanState_le`);
* every walk of a fresh spanner has length at most `γ_ℓ mMax` (`slotWalk_init_length_le`), so a
  slot adds at most `spE (2 ⌈γ_ℓ mMax⌉ + 3) + 1` to `embRefreshSizeAt`
  (`embRefreshSizeAt_restartSpanState_le`);
* the initialization of a slot takes at most the bound of `spanActivateSpace_le` with `spV` and
  `spE` in place of the sizes of `Hb` (`spanActivateSpace_le_caps`).
The slot list has at most `slotCap` slots, since its slots are distinct and below `slotCap`
(`slots_length_le_slotCap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Counting -/

/-- A set of names below `c` has at most `c` elements. -/
theorem card_le_of_forall_mem_lt {E : Finset ℕ} {c : ℕ} (h : ∀ e ∈ E, e < c) : E.card ≤ c :=
  (Finset.card_le_card fun e he => Finset.mem_range.mpr (h e he)).trans (Finset.card_range c).le

/-- A sum over a list of terms at most `B` is at most the length times `B`. -/
theorem sum_map_le_length_mul {α : Type} (l : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ a ∈ l, f a ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    omega

/-- **The slot list has at most `slotCap` slots**: its slots are distinct and below `slotCap`. -/
theorem slots_length_le_slotCap {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (h : SlotMapOK tr slotCap cap slots slotOf) :
    slots.length ≤ slotCap := by
  rw [← List.toFinset_card_of_nodup h.1]
  exact card_le_of_forall_mem_lt fun s hs => (h.2.2.2.2 s (List.mem_toFinset.mp hs)).1

/-- A graph that meets `SpanGraphOK P` has at most `P.vCap` vertices, since its vertices are below
`P.vCap`. -/
theorem spanGraphOK_n_le {P : DSParams} {G : MGraph} (h : SpanGraphOK P G) : G.n ≤ P.vCap :=
  card_le_of_forall_mem_lt h.2.2.2.2.2.2.2.2.1

/-- A graph that meets `SpanGraphOK P` has at most `P.eCap` edges, since its edges are below
`P.eCap`. -/
theorem spanGraphOK_m_le {P : DSParams} {G : MGraph} (h : SpanGraphOK P G) : G.m ≤ P.eCap :=
  card_le_of_forall_mem_lt h.2.2.2.2.2.2.2.2.2

/-! ## The fresh spanners of a restart -/

/-- A listed slot holds the fresh spanner on its new graph after the restart. -/
theorem restartSpanState_listed {slotCap cap : ℕ} (S6 : BucketSpannerState cap)
    (S : Fin slotCap → Option BundleState) (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ)
    {slots : List ℕ} {s : ℕ} (hs : s < cap) (hm : s ∈ slots) :
    restartSpanState S6 S cs ord k slots ⟨s, hs⟩ = some ⟨restartSlotGraph S cs ord k s, []⟩ := by
  simp [restartSpanState, hm]

/-- **The graphs that P10 reads after a restart.** Each listed slot adds at most `2 P.eCap` to
`rebuildSize`: the graph of its fresh spanner is its new graph, with at most `P.eCap` edges, and
the spanner is a subgraph of it (`dsHist_init_H_sub_E`). -/
theorem rebuildSize_restartSpanState_le (P : DSParams) {slotCap cap : ℕ}
    (S6 : BucketSpannerState cap) (S : Fin slotCap → Option BundleState) (cs : CompLSFState)
    (ord : ℕ → List End) (k : ℕ) (slots : List ℕ)
    (hok : ∀ s ∈ slots, s < cap ∧ SpanGraphOK P (restartSlotGraph S cs ord k s)) :
    rebuildSize P (restartSpanState S6 S cs ord k slots) slots ≤ slots.length * (2 * P.eCap) := by
  unfold rebuildSize
  refine sum_map_le_length_mul _ _ _ fun s hm => ?_
  obtain ⟨hs, hG⟩ := hok s hm
  have hval := hG.2.2.2.2.2.2.1
  have hmM := hG.2.2.2.2.2.2.2.1
  have hGE : slotGE P (restartSpanState S6 S cs ord k slots) s =
      (restartSlotGraph S cs ord k s).E := by
    simp only [slotGE, hs, ↓reduceDIte, restartSpanState_listed S6 S cs ord k hs hm,
      dsHist_init_G_eq]
  have hHE : slotHE P (restartSpanState S6 S cs ord k slots) s ⊆
      (restartSlotGraph S cs ord k s).E := by
    simp only [slotHE, hs, ↓reduceDIte, restartSpanState_listed S6 S cs ord k hs hm]
    exact dsHist_init_H_sub_E P hval hmM
  have h1 := Finset.card_le_card hHE
  have h2 := spanGraphOK_m_le hG
  rw [hGE]
  unfold MGraph.m at h2
  omega

/-- The length of a walk of a fresh spanner, as a natural number: at most `⌈γ_ℓ mMax⌉`. -/
theorem slotWalk_init_length_le_ceil (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap}
    {s : ℕ} (hs : s < cap) {Hb : MGraph} (hS : S6 ⟨s, hs⟩ = some ⟨Hb, []⟩)
    (hVal : Hb.IsValid) (hGm : Hb.m ≤ P.mMax) {e : ℕ} (he : e ∈ Hb.E) :
    (slotWalk P S6 s e).length ≤ ⌈P.impl.γ_ℓ P.mMax⌉₊ := by
  have h := slotWalk_init_length_le P hs hS hVal hGm he
  have h2 : (canonicalSparsifyParams P.impl P.mMax).absorbTime.γ_ℓ = P.impl.γ_ℓ P.mMax := rfl
  rw [h2] at h
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- **The walks that the refresh writes after a restart.** Each listed slot adds at most
`P.eCap · (2 ⌈γ_ℓ mMax⌉ + 3) + 1` to `embRefreshSizeAt`: its fresh spanner has no history, its
graph has at most `P.eCap` edges, and the walk of each edge has at most `⌈γ_ℓ mMax⌉` steps, so
`2 ⌈γ_ℓ mMax⌉ + 1` words (`walkWords`). -/
theorem embRefreshSizeAt_restartSpanState_le (P : DSParams) {slotCap cap : ℕ}
    (S6 : BucketSpannerState cap) (S : Fin slotCap → Option BundleState) (cs : CompLSFState)
    (ord : ℕ → List End) (k : ℕ) (slots : List ℕ)
    (hok : ∀ s ∈ slots, s < cap ∧ SpanGraphOK P (restartSlotGraph S cs ord k s)) :
    embRefreshSizeAt P (restartSpanState S6 S cs ord k slots) slots ≤
      slots.length * (P.eCap * (2 * ⌈P.impl.γ_ℓ P.mMax⌉₊ + 3) + 1) := by
  unfold embRefreshSizeAt
  refine sum_map_le_length_mul _ _ _ fun s hm => ?_
  obtain ⟨hs, hG⟩ := hok s hm
  have hval := hG.2.2.2.2.2.2.1
  have hmM := hG.2.2.2.2.2.2.2.1
  have hS := restartSpanState_listed S6 S cs ord k hs hm
  set Hb := restartSlotGraph S cs ord k s
  set g := ⌈P.impl.γ_ℓ P.mMax⌉₊
  simp only [hs, ↓reduceDIte, hS, dsHist_init_G_eq, ↓reduceIte]
  have hsum : (Hb.E.sum fun e =>
      Read.walkWords (slotWalk P (restartSpanState S6 S cs ord k slots) s e) + 0 + 2) ≤
      Hb.E.card * (2 * g + 3) := by
    rw [← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun e he => ?_
    have hl := slotWalk_init_length_le_ceil P hs hS hval hmM he
    unfold Read.walkWords
    omega
  have hm' : Hb.E.card ≤ P.eCap := spanGraphOK_m_le hG
  exact Nat.add_le_add_right (hsum.trans (Nat.mul_le_mul_right (2 * g + 3) hm')) 1

/-- **The space of the initialization of a slot, in the caps of the spanners.** The bound of
`spanActivateSpace_le` grows with the number of vertices and edges of the graph, and a graph that
meets `SpanGraphOK P` has at most `P.vCap` vertices and `P.eCap` edges. -/
theorem spanActivateSpace_le_caps (P : DSParams) {G : MGraph} (hG : SpanGraphOK P G) :
    spanActivateSpace P G ≤
      100 * ((P.L + 1) * (P.vCap + P.eCap + 1)) +
        (2 * (36 * (P.vCap + 2 * P.eCap + 1)) ^ P.impl.cw +
          30 * (P.eCap + 1) * (⌈P.impl.γ_ℓ P.mMax⌉₊ + 1) + 3 * P.vCap +
          dynGraphSize P.vCap P.eCap + P.eCap + 10) := by
  refine (spanActivateSpace_le P G).trans ?_
  have hn := spanGraphOK_n_le hG
  have hm := spanGraphOK_m_le hG
  have h1 : 2 * (36 * (G.n + 2 * G.m + 1)) ^ P.impl.cw ≤
      2 * (36 * (P.vCap + 2 * P.eCap + 1)) ^ P.impl.cw :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) _)
  have h2 : 30 * (G.m + 1) * (⌈P.impl.γ_ℓ P.mMax⌉₊ + 1) ≤
      30 * (P.eCap + 1) * (⌈P.impl.γ_ℓ P.mMax⌉₊ + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 30 (by omega))
  omega

end MinCostFlow.SparseCore.Program
