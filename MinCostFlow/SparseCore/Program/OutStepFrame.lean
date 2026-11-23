module

public import MinCostFlow.SparseCore.Program.OutStepProg
public import MinCostFlow.SparseCore.Program.OutRecords
public import MinCostFlow.SparseCore.Program.OutSpec

/-!
# The frame of the output step

During the output step, memory holds five things: the tour (piece P2), the stored output graph,
the batch written so far (from `h + 5`), the edits written so far (from `e0 + 1`), and the input
records below `h`. The program changes memory in three ways: its own stores in the two regions,
calls of the graph procedures, and calls of the tour. This file states what holds between the
steps (`SBase`, and `SState` with the registers) and proves that each kind of change keeps it.

* `SBase.of_own`: a change of cells of `[h, t0)` outside the records written so far.
* `SBase.of_graph`: a change of the cells of the stored graph.
* `SBase.of_tour`: a tour call that respects memory.
* `SBase.push_batch` and `SBase.push_edit`: one more record is counted, once it is written.

The places are fixed by the arguments (`OSArgs`): the regions of `R` words each start at `h + 4`
and `e0 = h + 4 + R`, and the tour may take cells from `t0 = e0 + R` on.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- The fixed words of one run of the output step. -/
structure OSArgs where
  outH : ℕ
  tourH : ℕ
  delPtr : ℕ
  splitPtr : ℕ
  insPtr : ℕ
  rotPtr : ℕ
  h : ℕ
  g : ℕ
  R : ℕ

/-- The start of the edit region. -/
def OSArgs.e0 (A : OSArgs) : ℕ := A.h + 4 + A.R

/-- The first cell that the tour may take. -/
def OSArgs.t0 (A : OSArgs) : ℕ := A.h + 4 + A.R + A.R

theorem OSArgs.t0_eq (A : OSArgs) : A.t0 = A.e0 + A.R := rfl

theorem outGraphRep_foot_iff {vCap eCap outH g a : ℕ} :
    (outGraphRep vCap eCap).foot outH g a ↔
      a = outH ∨ (g ≤ a ∧ a < g + dynGraphSize vCap eCap) := Iff.rfl

/-! ## Registers -/

/-- The registers that keep their value after the setup. -/
def IsFixedReg (r : ℕ) : Prop :=
  r ≤ 6 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 15 ∨ r = 19 ∨ r = 23 ∨ r = 24 ∨ r = 25

instance (r : ℕ) : Decidable (IsFixedReg r) := by unfold IsFixedReg; infer_instance

/-- The fixed registers hold the arguments, the graph address, the caps, the region size, the
edit region and the bases of four arrays of the graph. -/
def SRegs (st : State) (A : OSArgs) (vCap eCap : ℕ) : Prop :=
  st.regs 0 = A.outH ∧ st.regs 1 = A.tourH ∧ st.regs 2 = A.delPtr ∧ st.regs 3 = A.splitPtr ∧
    st.regs 4 = A.insPtr ∧ st.regs 5 = A.rotPtr ∧ st.regs 6 = A.h ∧ st.regs 10 = A.g ∧
    st.regs 11 = vCap ∧ st.regs 12 = eCap ∧ st.regs 13 = A.R ∧ st.regs 15 = A.e0 ∧
    st.regs 19 = dgEPresBase A.g vCap ∧ st.regs 23 = dgExtToIntBase A.g vCap ∧
    st.regs 24 = dgIncHeadBase A.g vCap ∧ st.regs 25 = dgHeNextBase A.g vCap eCap

theorem SRegs.of_fixed {st st' : State} {A : OSArgs} {vCap eCap : ℕ} (hS : SRegs st A vCap eCap)
    (h : ∀ r, IsFixedReg r → st'.regs r = st.regs r) : SRegs st' A vCap eCap := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h10, h11, h12, h13, h15, h19, h23, h24, h25⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rwa [h _ (by unfold IsFixedReg; omega)]

theorem SRegs.update {st st' : State} {A : OSArgs} {vCap eCap r : ℕ} (hS : SRegs st A vCap eCap)
    (ho : ∀ j, j ≠ r → st'.regs j = st.regs j) (hr : ¬ IsFixedReg r) : SRegs st' A vCap eCap :=
  hS.of_fixed fun j hj => ho j fun h => hr (h ▸ hj)

/-! ## The frame -/

section Frame

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The fixed facts about the places: the start tour and the stored graph lie below `h`, and
they do not share cells. -/
def SCtx (T : OutTourAt S w vCap eCap p nm sm fm lm) (A : OSArgs) (tx₀ : T.rep.τ) : Prop :=
  (∀ a, T.rep.foot A.tourH tx₀ a → a < A.h) ∧ A.outH < A.h ∧
    A.g + dynGraphSize vCap eCap ≤ A.h ∧
    (∀ a, (outGraphRep vCap eCap).foot A.outH A.g a → ¬ T.rep.foot A.tourH tx₀ a) ∧
    (A.outH < A.g ∨ A.g + dynGraphSize vCap eCap ≤ A.outH)

/-- **What holds between the steps.** The tour holds `s` as `tx`, memory is zero from the heap
pointer `cur` on, the tour takes only old cells or cells in `[t0, cur)`, the cells below `h`
outside the stored graph and the start tour are unchanged, the handle holds the graph address,
the stored graph is `G`, the batch records `U` lie in `[h + 5, bp)` and the edit records `E` in
`[e0 + 1, ep)`. -/
def SBase (T : OutTourAt S w vCap eCap p nm sm fm lm) (A : OSArgs) (tx₀ : T.rep.τ)
    (mem₀ : ℕ → ℕ) (S₀ G : MGraph) (U : List Update) (E : List OrdEdit) (bp ep cur : ℕ)
    (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) : Prop :=
  T.rep.rep A.tourH s tx mem ∧ ZeroFrom mem cur ∧ A.t0 ≤ cur ∧
    (∀ a, T.rep.foot A.tourH tx a → T.rep.foot A.tourH tx₀ a ∨ (A.t0 ≤ a ∧ a < cur)) ∧
    (∀ a < A.h, ¬ (outGraphRep vCap eCap).foot A.outH A.g a → ¬ T.rep.foot A.tourH tx₀ a →
      mem a = mem₀ a) ∧
    mem A.outH = A.g ∧ DynGraphAt mem A.g vCap eCap G ∧
    A.h + 5 ≤ bp ∧ bp ≤ A.e0 ∧ BatchBodyAt mem (A.h + 5) S₀ U (bp - (A.h + 5)) ∧
    A.e0 + 1 ≤ ep ∧ ep ≤ A.t0 ∧ EditsBody mem (A.e0 + 1) E (ep - (A.e0 + 1))

variable {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ} {mem : ℕ → ℕ}

/-- A cell of the tour lies below `h` or in `[t0, cur)`. -/
theorem SBase.foot_lt (hC : SCtx T A tx₀)
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {a : ℕ}
    (ha : T.rep.foot A.tourH tx a) : (a < A.h ∧ T.rep.foot A.tourH tx₀ a) ∨ (A.t0 ≤ a ∧ a < cur) := by
  rcases hB.2.2.2.1 a ha with h | h
  · exact Or.inl ⟨hC.1 a h, h⟩
  · exact Or.inr h

/-- **Own writes.** A change of cells of `[h, t0)` outside the records written so far keeps the
frame and the potential. -/
theorem SBase.of_own (hC : SCtx T A tx₀) (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem)
    {mem' : ℕ → ℕ}
    (hmem : ∀ a, (a < A.h ∨ A.t0 ≤ a ∨ (A.h + 5 ≤ a ∧ a < bp) ∨ (A.e0 + 1 ≤ a ∧ a < ep)) →
      mem' a = mem a) :
    SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem' ∧
      T.rep.phi A.tourH tx mem' = T.rep.phi A.tourH tx mem := by
  obtain ⟨hrep, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, hep1, hep2, hE⟩ := hB
  have hagree : ∀ a, T.rep.foot A.tourH tx a → mem a = mem' a := by
    intro a ha
    rcases hft a ha with ha | ⟨h1, -⟩
    · exact (hmem a (Or.inl (hC.1 a ha))).symm
    · exact (hmem a (Or.inr (Or.inl h1))).symm
  obtain ⟨hrepI, hphi⟩ := T.rep_local A.tourH s tx mem mem' hagree
  refine ⟨⟨hrepI hrep, fun a ha => by rw [hmem a (Or.inr (Or.inl (by omega)))]; exact hz a ha,
    ht0, hft, fun a ha hn hn' => by rw [hmem a (Or.inl ha)]; exact hfr a ha hn hn',
    by rw [hmem _ (Or.inl hC.2.1)]; exact hout, hG.of_agree fun a h1 h2 => hmem a (Or.inl
      (by have := hC.2.2.1; omega)), hbp1, hbp2,
    hU.of_agree fun i hi => hmem _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))), hep1, hep2,
    hE.of_agree fun i hi => hmem _ (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))⟩, hphi.symm⟩

/-- **A store** into a free cell of `[h, t0)`. -/
theorem SBase.of_store (hC : SCtx T A tx₀) (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem)
    {x v : ℕ} (hx : A.h ≤ x ∧ x < A.t0 ∧ ¬ (A.h + 5 ≤ x ∧ x < bp) ∧ ¬ (A.e0 + 1 ≤ x ∧ x < ep)) :
    SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx (Function.update mem x v) ∧
      T.rep.phi A.tourH tx (Function.update mem x v) = T.rep.phi A.tourH tx mem :=
  hB.of_own hC fun a ha => Function.update_of_ne (by
    rintro rfl
    rcases ha with ha | ha | ha | ha <;> omega) _ _

/-- **A graph call.** A change of the cells of the stored graph to a new graph `G'` keeps the
frame and the potential. -/
theorem SBase.of_graph (hC : SCtx T A tx₀)
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {G' : MGraph} {mem' : ℕ → ℕ}
    (hG' : DynGraphAt mem' A.g vCap eCap G')
    (hmem : ∀ a, a < A.g ∨ A.g + dynGraphSize vCap eCap ≤ a → mem' a = mem a) :
    SBase T A tx₀ mem₀ S₀ G' U E bp ep cur s tx mem' ∧
      T.rep.phi A.tourH tx mem' = T.rep.phi A.tourH tx mem := by
  obtain ⟨hrep, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, hep1, hep2, hE⟩ := hB
  have hgh := hC.2.2.1
  have hagree : ∀ a, T.rep.foot A.tourH tx a → mem a = mem' a := by
    intro a ha
    refine (hmem a ?_).symm
    by_contra hc
    rcases hft a ha with ha | ⟨h1, -⟩
    · exact hC.2.2.2.1 a (Or.inr ⟨by omega, by omega⟩) ha
    · have : A.h ≤ A.t0 := by unfold OSArgs.t0; omega
      omega
  obtain ⟨hrepI, hphi⟩ := T.rep_local A.tourH s tx mem mem' hagree
  have ht0h : A.h ≤ A.t0 := by unfold OSArgs.t0; omega
  refine ⟨⟨hrepI hrep, fun a ha => by rw [hmem a (Or.inr (by omega))]; exact hz a ha, ht0, hft,
    fun a ha hn hn' => ?_, ?_, hG', hbp1, hbp2,
    hU.of_agree fun i hi => hmem _ (Or.inr (by omega)), hep1, hep2,
    hE.of_agree fun i hi => hmem _ (Or.inr (by unfold OSArgs.e0 at *; omega))⟩, hphi.symm⟩
  · rw [hmem a ?_]
    · exact hfr a ha hn hn'
    · by_contra hc
      exact hn (Or.inr ⟨by omega, by omega⟩)
  · rw [hmem _ (by rcases hC.2.2.2.2 with h | h <;> omega)]; exact hout

/-- **A tour call** that respects memory, from the heap pointer `cur` to `cur'`. -/
theorem SBase.of_tour (hC : SCtx T A tx₀)
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {cur' sp : ℕ} {s' : OutTourAbs}
    {tx' : T.rep.τ} {mem' : ℕ → ℕ} (hrep : T.rep.rep A.tourH s' tx' mem')
    (hresp : T.rep.Respects (T.rep.foot A.tourH tx) cur sp mem cur' A.tourH tx' mem') :
    SBase T A tx₀ mem₀ S₀ G U E bp ep cur' s' tx' mem' ∧
      (∀ a, a < A.t0 → ¬ T.rep.foot A.tourH tx₀ a → mem' a = mem a) := by
  obtain ⟨-, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, hep1, hep2, hE⟩ := hB
  obtain ⟨hle, -, hz', hkeep, hft'⟩ := hresp
  have ht0h : A.h + 5 ≤ A.e0 := hbp1.trans hbp2
  have he0t0 : A.e0 + 1 ≤ A.t0 := hep1.trans hep2
  -- a cell below `t0` outside the start tour keeps its word
  have hk : ∀ a, a < A.t0 → ¬ T.rep.foot A.tourH tx₀ a → mem' a = mem a := by
    intro a ha hn
    refine hkeep a (by omega) fun hf => ?_
    rcases hft a hf with hf | ⟨h1, -⟩
    · exact hn hf
    · omega
  have hgh := hC.2.2.1
  have hfr' : ∀ a < A.h, ¬ (outGraphRep vCap eCap).foot A.outH A.g a →
      ¬ T.rep.foot A.tourH tx₀ a → mem' a = mem₀ a := fun a ha hn hn' => by
    rw [hk a (by unfold OSArgs.t0 at *; omega) hn']; exact hfr a ha hn hn'
  refine ⟨⟨hrep, hz', by omega, ?_, hfr', ?_, hG.of_agree fun a h1 h2 => hk a (by omega)
      (hC.2.2.2.1 a (Or.inr ⟨h1, h2⟩)), hbp1, hbp2,
    hU.of_agree fun i hi => hk _ (by omega) (fun hf => by have := hC.1 _ hf; omega), hep1, hep2,
    hE.of_agree fun i hi => hk _ (by omega) (fun hf => by have := hC.1 _ hf; omega)⟩, hk⟩
  · intro a ha
    rcases hft' a ha with ha | ⟨h1, h2⟩
    · rcases hft a ha with ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, h2⟩
  · rw [hk _ (by have := hC.2.1; omega) (hC.2.2.2.1 _ (Or.inl rfl))]; exact hout

/-- **One more batch record**, once it is written at `bp`. -/
theorem SBase.push_batch (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {u : Update}
    {len : ℕ} (hu : UpdateAt mem bp (S₀.applyBatch U) u len) (hle : bp + len ≤ A.e0) :
    SBase T A tx₀ mem₀ S₀ G (U ++ [u]) E (bp + len) ep cur s tx mem := by
  obtain ⟨hrep, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, hep1, hep2, hE⟩ := hB
  have h := batchBodyAt_snoc hU (by rw [show A.h + 5 + (bp - (A.h + 5)) = bp by omega]; exact hu)
  rw [show bp - (A.h + 5) + len = bp + len - (A.h + 5) by omega] at h
  exact ⟨hrep, hz, ht0, hft, hfr, hout, hG, by omega, hle, h, hep1, hep2, hE⟩

/-- **One more edit record**, once it is written at `ep`. -/
theorem SBase.push_edit (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {d : OrdEdit}
    {l : ℕ} (hd : decodeOrdEdit mem ep = (d, l)) (htag : mem ep ≤ 4) (hle : ep + l ≤ A.t0) :
    SBase T A tx₀ mem₀ S₀ G U (E ++ [d]) bp (ep + l) cur s tx mem := by
  obtain ⟨hrep, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, hep1, hep2, hE⟩ := hB
  have h := hE.snoc (d := d) (l := l)
    (by rw [show A.e0 + 1 + (ep - (A.e0 + 1)) = ep by omega]; exact hd)
    (by rw [show A.e0 + 1 + (ep - (A.e0 + 1)) = ep by omega]; exact htag)
  rw [show ep - (A.e0 + 1) + l = ep + l - (A.e0 + 1) by omega] at h
  exact ⟨hrep, hz, ht0, hft, hfr, hout, hG, hbp1, hbp2, hU, by omega, hle, h⟩

end Frame

end MinCostFlow.SparseCore.Program
