module

public import MinCostFlow.SparseCore.Program.OutStepJoinFront
public import MinCostFlow.SparseCore.Program.OutStepRotW

/-!
# The last three phases of the output step

The output step runs six phases (`outStepBody`). This file joins the last three: the insertions
(`osInsPhase_runs`), the rotations (`osRotPhaseW_runs`, with the exact edit pointer) and the
four words at the end (`osFinal_runs`). The lemma `osBack_runs` starts from the frame that
`osFront_runs` leaves, for any list of entering edges with the facts that the phase lemmas ask
for, so it does not mention the model. Afterwards the marked ends are those of the kept and the
entering edges (`outMarksOf_insTourAfter`), and the count words and the four words at `h` are
written.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- Marking both ends of the edges of `L`, whose ends are in the core lists, adds exactly the
ends of these edges to the marks. -/
theorem outMarksOf_insTourAfter {cord : ℕ → List End} {tl hd : ℕ → ℕ} :
    ∀ (L : List ℕ) (s : OutTourAbs) (Pres : Finset ℕ),
      (∀ e ∈ L, (e, true) ∈ cord (tl e) ∧ (e, false) ∈ cord (hd e)) →
      OutMarksOf s cord Pres → OutMarksOf (insTourAfter s L) cord (Pres ∪ L.toFinset)
  | [], s, Pres, _, hmk => by simpa [insTourAfter] using hmk
  | e :: L, s, Pres, hcord, hmk => by
    obtain ⟨hct, hch⟩ := hcord e List.mem_cons_self
    have hmk' : OutMarksOf (insTourStep s e) cord (insert e Pres) := by
      refine ⟨hmk.1, fun z => ?_⟩
      unfold insTourStep
      rw [mem_mark_both, hmk.2 z, Finset.mem_insert]
      obtain ⟨z1, z2⟩ := z
      constructor
      · rintro (⟨hz, hzP⟩ | hz)
        · exact ⟨hz, Or.inr hzP⟩
        · simp only at hz
          subst hz
          cases z2
          · exact ⟨⟨_, hch⟩, Or.inl rfl⟩
          · exact ⟨⟨_, hct⟩, Or.inl rfl⟩
      · rintro ⟨hz, hzP | hzP⟩
        · exact Or.inr hzP
        · exact Or.inl ⟨hz, hzP⟩
    have h := outMarksOf_insTourAfter L (insTourStep s e) (insert e Pres)
      (fun f hf => hcord f (List.mem_cons_of_mem _ hf)) hmk'
    have : Pres ∪ (e :: L).toFinset = insert e Pres ∪ L.toFinset := by
      ext f; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    rw [this]
    exact h

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ}

/-- **The insertions, the rotations and the four words.** -/
theorem osBack_runs (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (hRdef : A.R = (vCap + 1) * (eCap + 1) * 16)
    (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    {S₀ G₂ : MGraph} {U₀ : List Update} {E₀ : List OrdEdit} {cord : ℕ → List End}
    {keep : Finset ℕ} {insL : List ℕ} {tl hd : ℕ → ℕ} {T₀ : List ℕ} {s : OutTourAbs}
    {tx : T.rep.τ} {bp ep : ℕ} {st : State}
    (hB : SBase T A tx₀ mem₀ S₀ G₂ U₀ E₀ bp ep (st.regs 7) s tx st.mem)
    (hR : SRegs st A vCap eCap) (h14 : st.regs 14 = bp) (h16 : st.regs 16 = ep)
    (h17 : st.regs 17 = U₀.length) (h18 : st.regs 18 = E₀.length)
    (hmk : OutMarksOf s cord keep) (hkcap : ∀ e ∈ keep, e < eCap)
    (hG₂ : G₂ = S₀.applyBatch U₀)
    (hins : OutInsAt mem₀ A.insPtr insL tl hd)
    (hifree : OutCellsFree A.insPtr (1 + 3 * insL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hival : ∀ j (hj : j < insL.length),
      (G₂.applyBatch ((insL.take j).map fun e => Update.insert e (tl e) (hd e))).UpdateIsValid
        (.insert insL[j] (tl insL[j]) (hd insL[j])))
    (hicap : ∀ e ∈ insL, e < eCap) (hends : ∀ e ∈ insL, tl e < vCap ∧ hd e < vCap)
    (hcord : ∀ e ∈ insL, (e, true) ∈ cord (tl e) ∧ (e, false) ∈ cord (hd e))
    (hcnt : mem₀ A.rotPtr = T₀.length) (hT : ListAt mem₀ (A.rotPtr + 1) T₀)
    (hrfree : OutCellsFree A.rotPtr (1 + T₀.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hTv : ∀ v ∈ T₀, v < vCap)
    (hbpR : bp + 4 * insL.length ≤ A.e0) (hepR : ep + 8 * insL.length + 3 * T₀.length ≤ A.t0)
    (hroom : st.regs 7 + (4 * insL.length + T₀.length) * S.querySpace < 2 ^ w)
    (hnU : U₀.length + insL.length < 2 ^ w) :
    ∃ st₄ c₄ st₅ c₅ st₆ c₆ tx',
      Runs w p ω (osInsPhase nm sm au) st .normal st₄ c₄ ∧
      Runs w p ω (osRotPhase fm) st₄ .normal st₅ c₅ ∧
      Runs w p ω osFinal st₅ (.returned (st₅.regs 7)) st₆ c₆ ∧
      SBase T A tx₀ mem₀ S₀ (G₂.applyBatch (insL.map fun e => Update.insert e (tl e) (hd e)))
        (U₀ ++ insL.map fun e => Update.insert e (tl e) (hd e))
        (E₀ ++ insEditsTour tl hd s insL ++ outRotateEdits (insTourAfter s insL).markedList T₀)
        (bp + 4 * insL.length)
        (ep + 8 * insL.length + 3 * (outRotateEdits (insTourAfter s insL).markedList T₀).length)
        (st₅.regs 7) (insTourAfter s insL) tx' st₆.mem ∧
      OutMarksOf (insTourAfter s insL) cord (keep ∪ insL.toFinset) ∧
      st₆.mem A.h = A.h + 4 ∧ st₆.mem (A.h + 1) = bp + 4 * insL.length - (A.h + 4) ∧
      st₆.mem (A.h + 2) = A.e0 ∧
      st₆.mem (A.h + 3) = ep + 8 * insL.length +
        3 * (outRotateEdits (insTourAfter s insL).markedList T₀).length - A.e0 ∧
      st₆.mem (A.h + 4) = U₀.length + insL.length ∧
      st₆.mem A.e0 = E₀.length + 2 * insL.length +
        (outRotateEdits (insTourAfter s insL).markedList T₀).length ∧
      st.regs 7 ≤ st₅.regs 7 ∧
      st₅.regs 7 ≤ st.regs 7 + (4 * insL.length + T₀.length) * S.querySpace ∧
      c₄ + c₅ + c₆ + T.rep.phi A.tourH tx' st₆.mem ≤
        insL.length * (4 * (S.mul * ordStoreLog eCap) + 3100) +
          T₀.length * (S.mul * ordStoreLog eCap + 110) + 100 + T.rep.phi A.tourH tx st.mem := by
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hRpos : 16 ≤ A.R := by
    rw [hRdef]
    have := Nat.mul_le_mul (show 1 ≤ vCap + 1 by omega) (show 1 ≤ eCap + 1 by omega)
    omega
  have hq : (4 * insL.length + T₀.length) * S.querySpace =
      4 * insL.length * S.querySpace + T₀.length * S.querySpace := Nat.add_mul _ _ _
  have hbp5 := hB.2.2.2.2.2.2.2.1
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  -- the insertions
  obtain ⟨st₄, c₄, hr₄, φ₄, hI₄, hc₄⟩ := osInsPhase_runs (nm := nm) (sm := sm) (ω := ω) hC hau
    hG₂ hw ht0 htour hins hifree hival hicap hends
    (fun e he => by rw [hmk.1]; exact hcord e he) hbpR (by omega) (by omega) hB hR rfl h14 h16
    h17 h18
  obtain ⟨tx₄, hB₄, hR₄, h14₄, h16₄, h17₄, h18₄, -, -, -, hc4a, hc4b, hphi₄⟩ := hI₄
  simp only [List.take_length] at hB₄
  have hmk₄ := outMarksOf_insTourAfter (tl := tl) (hd := hd) insL s keep hcord hmk
  -- the rotations
  have hml : ∀ v ∈ T₀, ∀ y ∈ (insTourAfter s insL).markedList v, y.1 < eCap := by
    intro v _ y hy
    have hy' := (List.mem_filter.mp hy).2
    simp only [decide_eq_true_eq] at hy'
    have := ((hmk₄.2 y).mp hy').2
    rcases Finset.mem_union.mp this with h | h
    · exact hkcap _ h
    · exact hicap _ (List.mem_toFinset.mp h)
  obtain ⟨st₅, c₅, hr₅, φ₅, hI₅, hc₅⟩ := osRotPhaseW_runs (fm := fm) (ω := ω) hC hw ht0 htour
    hcnt hT hrfree hTv hml (by omega) (by omega) (by omega) hB₄ hR₄ rfl h14₄ h16₄
    (by rw [h17₄, List.length_append, List.length_map])
    (by rw [h18₄, List.length_append, insEditsTour_length])
  obtain ⟨tx₅, hB₅, hR₅, h14₅, h16₅, h17₅, h18₅, -, -, -, hc5a, hc5b, hphi₅⟩ := hI₅
  simp only [List.take_length] at hB₅ h16₅ h18₅
  set r := (outRotateEdits (insTourAfter s insL).markedList T₀).length with hr_def
  have hrle : r ≤ T₀.length := outRotateEdits_length_le _ _
  -- the four words
  have h6₅ : st₅.regs 6 = A.h := hR₅.2.2.2.2.2.2.1
  have h15₅ : st₅.regs 15 = A.e0 := hR₅.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨st₆, c₆, hr₆, hm₆, hc₆⟩ := osFinal_runs (p := p) (ω := ω) (A := A)
    (bp := bp + 4 * insL.length) (ep := ep + 8 * insL.length + 3 * r)
    (nU := U₀.length + insL.length)
    (nE := E₀.length + 2 * insL.length + r) h6₅ h14₅ h15₅ h16₅
    (by rw [h17₅, List.length_append, List.length_map])
    (by rw [h18₅, List.length_append, List.length_append, insEditsTour_length])
    (by omega) (by omega) (by omega) (by omega) hnU
  have hne : ∀ a, (a < A.h ∨ A.t0 ≤ a ∨ (A.h + 5 ≤ a ∧ a < bp + 4 * insL.length) ∨
      (A.e0 + 1 ≤ a ∧ a < ep + 8 * insL.length + 3 * r)) → st₆.mem a = st₅.mem a := by
    intro a ha
    rw [hm₆]
    have h1 : a ≠ A.h + 3 := by omega
    have h2 : a ≠ A.h + 2 := by omega
    have h3 : a ≠ A.h + 1 := by omega
    have h4 : a ≠ A.h := by omega
    have h5 : a ≠ A.e0 := by omega
    have h6 : a ≠ A.h + 4 := by omega
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]
  obtain ⟨hB₆, hp₆⟩ := hB₅.of_own hC hne
  have e1 : A.h ≠ A.h + 1 := by omega
  have e2 : A.h ≠ A.h + 2 := by omega
  have e3 : A.h ≠ A.h + 3 := by omega
  have e4 : A.h + 1 ≠ A.h + 2 := by omega
  have e5 : A.h + 1 ≠ A.h + 3 := by omega
  have e6 : A.h + 2 ≠ A.h + 3 := by omega
  have e7 : A.h + 4 ≠ A.e0 := by omega
  have e8 : A.h + 4 ≠ A.h := by omega
  have e9 : A.h + 4 ≠ A.h + 1 := by omega
  have e10 : A.h + 4 ≠ A.h + 2 := by omega
  have e11 : A.h + 4 ≠ A.h + 3 := by omega
  have e12 : A.e0 ≠ A.h := by omega
  have e13 : A.e0 ≠ A.h + 1 := by omega
  have e14 : A.e0 ≠ A.h + 2 := by omega
  have e15 : A.e0 ≠ A.h + 3 := by omega
  refine ⟨st₄, c₄, st₅, c₅, st₆, c₆, tx₅, hr₄, hr₅, hr₆, ?_, hmk₄, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, ?_, ?_⟩
  · rw [List.append_assoc] at hB₆ ⊢
    exact hB₆
  · rw [hm₆]
    simp only [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3,
      Function.update_self]
  · rw [hm₆]
    simp only [Function.update_of_ne e4, Function.update_of_ne e5, Function.update_self]
  · rw [hm₆]
    simp only [Function.update_of_ne e6, Function.update_self]
  · rw [hm₆]
    simp only [Function.update_self]
  · rw [hm₆]
    simp only [Function.update_of_ne e7, Function.update_of_ne e8, Function.update_of_ne e9,
      Function.update_of_ne e10, Function.update_of_ne e11, Function.update_self]
  · rw [hm₆]
    simp only [Function.update_of_ne e12, Function.update_of_ne e13, Function.update_of_ne e14,
      Function.update_of_ne e15, Function.update_self]
  · rw [hq]; omega
  · rw [hp₆, hphi₅]
    rw [hphi₄] at hc₅
    omega

end MinCostFlow.SparseCore.Program
