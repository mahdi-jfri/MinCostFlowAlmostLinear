module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseC1

/-!
# The restart of the bundles: phase C (`BunRestartPhaseC`)

Phase C goes over the `2 E` keys at `h + 6 n`. For an even key `2 e` it writes the pair
`(e, edgeSlot[e] - 1)` at `h + 6 n + 2 E` (`brPairsOf`); for every key it asks the tour for the
vertex whose tour list holds the end of the key and writes the answer at `h + 6 n + 4 E`
(`brPhaseC_runs`). The queries move the heap pointer and may grow the footprint of the tour above
`h1 = h + 6 n + 10 E`; their cost is paid against the potential of the tour
(`runs_forRange_amort`). `BrCInv` is the invariant of the loop and `brCStep` one round.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}

/-- The invariant of loop C after `i` rounds, with the tour in the concrete state `tx`. -/
structure BrCInv (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    (tbl tourH n slotsPtr h slotCap E h1 : ℕ) (M : ℕ → ℕ) (keys : List ℕ) (own : ℕ → ℕ)
    (cord : ℕ → List End) (tx₀ : htour.rep.τ) (i : ℕ) (tx : htour.rep.τ) (st : State) :
    Prop where
  regs : BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap
  regsL : BRRegsL st.regs h n E
  r10 : st.regs 10 = i
  r20 : st.regs 20 = (brPairsOf tbl slotCap M (keys.take i)).length
  r19lo : h1 ≤ st.regs 19
  r19hi : st.regs 19 ≤ h1 + i * TS.querySpace
  zero : ZeroFrom st.mem (st.regs 19)
  owners : ListAt st.mem (h + 6 * n + 4 * E) ((keys.take i).map own)
  pairs : ∀ j < (brPairsOf tbl slotCap M (keys.take i)).length,
    st.mem (h + 6 * n + 2 * E + 2 * j) =
        ((brPairsOf tbl slotCap M (keys.take i)).getD j (0, 0)).1 ∧
      st.mem (h + 6 * n + 2 * E + 2 * j + 1) =
        ((brPairsOf tbl slotCap M (keys.take i)).getD j (0, 0)).2
  rep : htour.rep.rep tourH cord tx st.mem
  foot : ∀ a, htour.rep.foot tourH tx a →
    htour.rep.foot tourH tx₀ a ∨ (h1 ≤ a ∧ a < st.regs 19)
  low : ∀ a < h, ¬ htour.rep.foot tourH tx₀ a → st.mem a = M a
  mid : ∀ a, h ≤ a → a < h1 → ¬ (h + 6 * n + 2 * E ≤ a ∧ a < h + 6 * n + 6 * E) →
    st.mem a = M a

/-- The hypotheses of phase C on the keys, the tour and the space. -/
structure BrCHyps (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    (tbl tourH n h slotCap E h1 : ℕ) (M : ℕ → ℕ) (keys : List ℕ) (own : ℕ → ℕ)
    (cord : ℕ → List End) (tx₀ : htour.rep.τ) : Prop where
  hw : 16 ≤ 2 ^ w
  keysLen : keys.length = 2 * E
  hh1 : h1 = h + 6 * n + 10 * E
  fit : h1 + 2 * E * TS.querySpace < 2 ^ w
  tourH_lt : tourH < 2 ^ w
  eCap_lt : 2 * eCap < 2 ^ w
  keys_ok : ∀ k ∈ keys, k < 2 * eCap ∧ own k < vCap ∧ endOfKey k ∈ cord (own k) ∧
    ∀ v', endOfKey k ∈ cord v' → v' = own k
  esl : ∀ k ∈ keys, k % 2 = 0 → btEdgeSlotBase tbl slotCap + k / 2 < h ∧
    ¬ htour.rep.foot tourH tx₀ (btEdgeSlotBase tbl slotCap + k / 2) ∧
    M (btEdgeSlotBase tbl slotCap + k / 2) ≤ slotCap
  even : (keys.filter fun k => k % 2 = 0).length ≤ E
  footT : ∀ a, htour.rep.foot tourH tx₀ a → a < h
  list : ListAt M (h + 6 * n) keys

/-- **One round of loop C.** -/
theorem brCStep (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    {tbl tourH n slotsPtr h slotCap E h1 : ℕ} {M : ℕ → ℕ} {keys : List ℕ} {own : ℕ → ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ}
    (H : BrCHyps htour tbl tourH n h slotCap E h1 M keys own cord tx₀)
    {i : ℕ} {tx : htour.rep.τ} {st : State} (hi : i < 2 * E)
    (hI : BrCInv htour tbl tourH n slotsPtr h slotCap E h1 M keys own cord tx₀ i tx st) :
    ∃ st₁ c tx₁, Runs w p ω (brLoopCBody bOwner) st .normal st₁ c ∧ st₁.regs 10 = i ∧
      BrCInv htour tbl tourH n slotsPtr h slotCap E h1 M keys own cord tx₀ (i + 1) tx₁
        { st₁ with regs := Function.update st₁.regs 10 (i + 1) } ∧
      c + htour.rep.phi tourH tx₁ st₁.mem ≤
        TS.mul * ordStoreLog eCap + 100 + htour.rep.phi tourH tx st.mem := by
  have hw := H.hw
  have hh1 := H.hh1
  have hfit := H.fit
  have hik : i < keys.length := by rw [H.keysLen]; exact hi
  obtain ⟨key, hkey⟩ : ∃ key, keys[i] = key := ⟨_, rfl⟩
  have hkeyMem : key ∈ keys := hkey ▸ List.getElem_mem hik
  obtain ⟨hk2, hown_lt, hown_mem, hown_uniq⟩ := H.keys_ok key hkeyMem
  have hkw : key < 2 ^ w := by have := H.eCap_lt; omega
  have hmK : st.mem (h + 6 * n + i) = key := by
    rw [hI.mid _ (by omega) (by omega) (by omega), ← hkey]
    exact H.list i hik
  have hcnt1 := brPairsOf_length_le (tbl := tbl) (slotCap := slotCap) (M := M) (ks := keys)
    (i + 1)
  have heven := H.even
  have hsucc := brPairsOf_take_succ (tbl := tbl) (slotCap := slotCap) (M := M) hik
  rw [hkey] at hsucc
  set cnt := (brPairsOf tbl slotCap M (keys.take i)).length with hcnt
  have hqbound : st.regs 19 + TS.querySpace ≤ h1 + 2 * E * TS.querySpace := by
    have h1' := hI.r19hi
    have : (i + 1) * TS.querySpace ≤ 2 * E * TS.querySpace := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_one_mul] at this
    omega
  -- The pair part.
  obtain ⟨st₁, c₁, hr₁, hc₁, hev₁, hodd₁⟩ := brLoopCPair_runs (w := w) (p := p) (ω := ω)
    (st := st) (esb := btEdgeSlotBase tbl slotCap) (keyP := h + 6 * n)
    (pairP := h + 6 * n + 2 * E) (i := i) (cnt := cnt) (key := key) hw hI.regs.r6 hI.r10
    hI.regsL.r13 hI.regsL.r14 hI.r20 hmK hkw (by omega) (fun hk => by
      obtain ⟨he1, he2, he3⟩ := H.esl key hkeyMem hk
      have hc1 : cnt + 1 ≤ E := by
        rw [hsucc, ite_eq_left hk, List.length_append] at hcnt1; simp at hcnt1; omega
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hI.low _ he1 he2]
      simp only [btEdgeSlotBase] at he1
      omega)
  -- What the pair part did, in both cases.
  have hregs₁ : ∀ r, r ≠ 11 → r ≠ 20 → r ≠ 21 → r ≠ 22 → st₁.regs r = st.regs r := by
    intro r h11 h20 h21 h22
    by_cases hk : key % 2 = 0
    · rw [(hev₁ hk).1]
      simp only [Function.update_apply, ite_eq_right h11, ite_eq_right h20, ite_eq_right h21, ite_eq_right h22]
    · rw [(hodd₁ hk).1]; simp [h11]
  have h11₁ : st₁.regs 11 = key := by
    by_cases hk : key % 2 = 0
    · rw [(hev₁ hk).1]; simp
    · rw [(hodd₁ hk).1]; simp
  have h20₁ : st₁.regs 20 = (brPairsOf tbl slotCap M (keys.take (i + 1))).length := by
    by_cases hk : key % 2 = 0
    · rw [(hev₁ hk).1, hsucc, ite_eq_left hk]; simp [hcnt]
    · rw [(hodd₁ hk).1, hsucc, ite_eq_right hk]; simp [hI.r20]
  have hfr₁ : ∀ a, (a < h + 6 * n + 2 * E ∨ h + 6 * n + 4 * E ≤ a) → st₁.mem a = st.mem a := by
    intro a ha
    by_cases hk : key % 2 = 0
    · have hc1 : cnt + 1 ≤ E := by
        rw [hsucc, ite_eq_left hk, List.length_append] at hcnt1; simp at hcnt1; omega
      rw [(hev₁ hk).2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [(hodd₁ hk).2]
  have hpairs₁ : ∀ j < (brPairsOf tbl slotCap M (keys.take (i + 1))).length,
      st₁.mem (h + 6 * n + 2 * E + 2 * j) =
          ((brPairsOf tbl slotCap M (keys.take (i + 1))).getD j (0, 0)).1 ∧
        st₁.mem (h + 6 * n + 2 * E + 2 * j + 1) =
          ((brPairsOf tbl slotCap M (keys.take (i + 1))).getD j (0, 0)).2 := by
    intro j hj
    by_cases hk : key % 2 = 0
    · obtain ⟨he1, he2, -⟩ := H.esl key hkeyMem hk
      rw [hsucc, ite_eq_left hk] at hj ⊢
      rw [(hev₁ hk).2]
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjc : j < cnt
      · rw [List.getD_append _ _ _ _ hjc, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hI.pairs j hjc
      · have hjeq : j = cnt := by omega
        subst hjeq
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self,
          hI.low _ he1 he2]
        exact ⟨rfl, rfl⟩
    · rw [hsucc, ite_eq_right hk, List.append_nil] at hj ⊢
      rw [(hodd₁ hk).2]
      exact hI.pairs j hj
  -- The footprint of the tour and the owner part.
  have hfootH : ∀ a, htour.rep.foot tourH tx a → a < h ∨ (h1 ≤ a ∧ a < st.regs 19) := by
    intro a ha
    rcases hI.foot a ha with h0 | h0
    · exact Or.inl (H.footT a h0)
    · exact Or.inr h0
  obtain ⟨hrepT₁, hphi₁⟩ := htour.rep_local tourH cord tx st.mem st₁.mem fun a ha => by
    have := hfootH a ha
    exact (hfr₁ a (by omega)).symm
  have hz₁ : ZeroFrom st₁.mem (st.regs 19) := fun a ha => by
    have := hI.r19lo
    rw [hfr₁ a (by omega)]; exact hI.zero a ha
  have hr19₁ : st₁.regs 19 = st.regs 19 := hregs₁ 19 (by omega) (by omega) (by omega) (by omega)
  obtain ⟨st₃, c₃, tx₂, mem₂, hEnd, hr₃, hreg₃, hmem₃, hrep₂, hresp, hcost⟩ :=
    brLoopCOwner_runs (ω := ω) htour (st := st₁) (tx := tx) (cord := cord) (key := key)
      (v := own key) (hc := st.regs 19) (ownP := h + 6 * n + 4 * E) (i := i)
      ((hregs₁ 1 (by omega) (by omega) (by omega) (by omega)).trans hI.regs.r1)
      ((hregs₁ 10 (by omega) (by omega) (by omega) (by omega)).trans hI.r10) h11₁
      ((hregs₁ 15 (by omega) (by omega) (by omega) (by omega)).trans hI.regsL.r15) hr19₁
      H.tourH_lt hk2 hkw hown_lt (by omega) hown_mem hown_uniq (hrepT₁ hI.rep)
      (fun a ha => by have := hfootH a ha; have := hI.r19lo; omega) hz₁ (by omega) (by omega)
  obtain ⟨hEnd_lo, hEnd_hi, hz₂, hfr₂, hft₂⟩ := hresp
  have hfoot₂ : ∀ a, htour.rep.foot tourH tx₂ a → a < h ∨ (h1 ≤ a ∧ a < hEnd) := by
    intro a ha
    rcases hft₂ a ha with h0 | h0
    · have := hfootH a h0; omega
    · have := hI.r19lo; omega
  obtain ⟨hrep₃, hphi₃⟩ := htour.rep_local tourH cord tx₂ mem₂ st₃.mem fun a ha => by
    have := hfoot₂ a ha
    rw [hmem₃, Function.update_of_ne (by omega)]
  -- Memory below `st.regs 19` outside the footprint of the tour is kept by the query.
  have hkeep : ∀ a, a < h1 → (a < h → ¬ htour.rep.foot tourH tx₀ a) →
      a ≠ h + 6 * n + 4 * E + i → st₃.mem a = st₁.mem a := by
    intro a ha hnf hne
    rw [hmem₃, Function.update_of_ne hne]
    refine hfr₂ a (by have := hI.r19lo; omega) fun hh => ?_
    rcases hI.foot a hh with h0 | h0
    · have := H.footT a h0
      exact hnf this h0
    · omega
  refine ⟨st₃, c₁ + c₃ + 1, tx₂, runs_seq_normal hr₁ hr₃, ?_, ?_, ?_⟩
  · rw [hreg₃]; simp [hregs₁ 10 (by omega) (by omega) (by omega) (by omega), hI.r10]
  · have hreg' : ∀ r, ({ st₃ with regs := Function.update st₃.regs 10 (i + 1) } : State).regs r =
        if r = 10 then i + 1 else if r = 19 then hEnd else if r = 12 then hEnd else
          st₁.regs r := by
      intro r
      show Function.update st₃.regs 10 (i + 1) r = _
      rw [hreg₃]
      by_cases h10 : r = 10
      · simp [h10]
      · by_cases h19 : r = 19
        · simp [h19]
        · by_cases h12 : r = 12
          · simp [h12]
          · simp [h10, h19, h12]
    have hr19' : ({ st₃ with regs := Function.update st₃.regs 10 (i + 1) } : State).regs 19 =
        hEnd := by rw [hreg']; simp
    have hlo := hI.r19lo
    refine ⟨?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine hI.regs.of_eq fun r hr => ?_
      rw [hreg', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hregs₁ r (by omega) (by omega) (by omega) (by omega)
    · refine hI.regsL.of_eq fun r hr => ?_
      rw [hreg', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hregs₁ r (by omega) (by omega) (by omega) (by omega)
    · rw [hreg', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact h20₁
    · rw [hr19']; omega
    · rw [hr19', Nat.add_one_mul]; have := hI.r19hi; omega
    · intro a ha
      rw [hr19'] at ha
      show st₃.mem a = 0
      rw [hmem₃, Function.update_of_ne (by omega)]
      exact hz₂ a ha
    · intro j hj
      rw [List.length_map, List.length_take] at hj
      show st₃.mem _ = _
      by_cases hji : j < i
      · rw [hkeep _ (by omega) (fun h' => by omega) (by omega),
          hfr₁ _ (by omega), hI.owners j (by simp; omega)]
        simp [List.getElem_map, List.getElem_take]
      · have hje : j = i := by omega
        subst hje
        rw [hmem₃, Function.update_self]
        simp [List.getElem_map, List.getElem_take, hkey]
    · intro j hj
      obtain ⟨hp1, hp2⟩ := hpairs₁ j hj
      have hjE : j + 1 ≤ E := by
        have := hj; omega
      show st₃.mem _ = _ ∧ st₃.mem _ = _
      rw [hkeep _ (by omega) (fun h' => by omega) (by omega),
        hkeep _ (by omega) (fun h' => by omega) (by omega)]
      exact ⟨hp1, hp2⟩
    · exact hrep₃ hrep₂
    · intro a ha
      rw [hr19']
      rcases hft₂ a ha with h0 | h0
      · rcases hI.foot a h0 with h00 | h00
        · exact Or.inl h00
        · exact Or.inr ⟨h00.1, by omega⟩
      · exact Or.inr ⟨by omega, h0.2⟩
    · intro a ha hnf
      show st₃.mem a = M a
      rw [hkeep _ (by omega) (fun _ => hnf) (by omega), hfr₁ _ (by omega)]
      exact hI.low a ha hnf
    · intro a ha1 ha2 ha3
      show st₃.mem a = M a
      rw [hkeep _ (by omega) (fun h' => by omega) (by omega), hfr₁ _ (by omega)]
      exact hI.mid a ha1 ha2 ha3
  · rw [← hphi₃]
    rw [← hphi₁] at hcost
    omega

/-- **Phase C.** Under the hypotheses `BrCHyps`, from a state that holds `M`, the tour in `tx₀`,
the registers of the restart, and the heap pointer `h1` in register `19`, phase C writes the pairs
of the keys (`brPairsOf`) at `h + 6 n + 2 E` and their owners at `h + 6 n + 4 E`. It moves the heap
pointer by at most `2 E` query spaces, keeps the tour, and changes no other memory below `h1`
outside the footprint of the tour. It costs at most `2 E` query bounds of the tour, `140` per key
and `20`, plus the drop of the potential of the tour. -/
theorem brPhaseC_runs (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    {tbl tourH n slotsPtr h slotCap E h1 : ℕ} {M : ℕ → ℕ} {keys : List ℕ} {own : ℕ → ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ}
    (H : BrCHyps htour tbl tourH n h slotCap E h1 M keys own cord tx₀)
    (hrepT : htour.rep.rep tourH cord tx₀ M) (hzero : ZeroFrom M h1)
    {st : State} (hst : st.mem = M) (hR : BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap)
    (hL : BRRegsL st.regs h n E) (h19 : st.regs 19 = h1) :
    ∃ st' c tx', Runs w p ω (brPhaseC bOwner) st .normal st' c ∧
      BRRegs st'.regs tbl tourH n slotsPtr h slotCap eCap ∧ BRRegsL st'.regs h n E ∧
      h1 ≤ st'.regs 19 ∧ st'.regs 19 ≤ h1 + 2 * E * TS.querySpace ∧
      ZeroFrom st'.mem (st'.regs 19) ∧
      ListAt st'.mem (h + 6 * n + 4 * E) (keys.map own) ∧
      (∀ j < (brPairsOf tbl slotCap M keys).length,
        st'.mem (h + 6 * n + 2 * E + 2 * j) = ((brPairsOf tbl slotCap M keys).getD j (0, 0)).1 ∧
        st'.mem (h + 6 * n + 2 * E + 2 * j + 1) =
          ((brPairsOf tbl slotCap M keys).getD j (0, 0)).2) ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h1 ≤ a ∧ a < st'.regs 19)) ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx₀ a → st'.mem a = M a) ∧
      (∀ a, h ≤ a → a < h1 → ¬ (h + 6 * n + 2 * E ≤ a ∧ a < h + 6 * n + 6 * E) →
        st'.mem a = M a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        2 * E * (TS.mul * ordStoreLog eCap + 140) + 20 + htour.rep.phi tourH tx₀ M := by
  have hw := H.hw
  have hfit := H.fit
  have hE2 : 2 * E < 2 ^ w := by
    have := H.hh1
    have : 2 * E ≤ h1 := by omega
    omega
  have hasg : Runs w p ω (.assign 20 (.const 0)) st .normal
      { st with regs := Function.update st.regs 20 0 } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp⟩
  obtain ⟨st', c, tx', hr, hI, hc⟩ := runs_forRange_amort (w := w) (p := p) (ω := ω) (r := 10)
    (hi := .bin .mul (.const 2) (.reg 9)) (body := brLoopCBody bOwner)
    (Inv := fun i tx st =>
      BrCInv htour tbl tourH n slotsPtr h slotCap E h1 M keys own cord tx₀ i tx st)
    (fun tx mem => htour.rep.phi tourH tx mem) (TS.mul * ordStoreLog eCap + 100) (2 * E)
    (by omega) hE2 (fun i tx st _ hI => hI.r10)
    (fun i tx st _ hI => Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq hI.regsL.r9) hE2)
    (fun i tx st hi hI => brCStep htour H hi hI)
    (st := { st with regs := Function.update st.regs 20 0 }) (g := tx₀) (by
      refine ⟨(hR.upd (by omega)).upd (by omega), (hL.upd (by omega)).upd (by omega), by simp,
        by simp [brPairsOf], by simp [h19], by simp [h19], ?_, fun j hj => by simp at hj,
        fun j hj => by simp [brPairsOf] at hj, ?_, fun a ha => Or.inl ha, ?_, ?_⟩
      · show ZeroFrom st.mem _
        simp only [Function.update_apply]
        rw [hst]; simpa [h19] using hzero
      · show htour.rep.rep tourH cord tx₀ st.mem
        rw [hst]; exact hrepT
      · intro a _ _; show st.mem a = M a; rw [hst]
      · intro a _ _ _; show st.mem a = M a; rw [hst])
  have htake : keys.take (2 * E) = keys := by rw [← H.keysLen, List.take_length]
  have hown := hI.owners
  have hpairs := hI.pairs
  rw [htake] at hown hpairs
  refine ⟨st', 2 + c + 1, tx', runs_seq_normal hasg hr, hI.regs, hI.regsL, hI.r19lo, hI.r19hi,
    hI.zero, hown, hpairs, hI.rep, hI.foot, hI.low, hI.mid, ?_⟩
  simp only [Expr.size_bin, Expr.size_const, Expr.size_reg] at hc
  have : 2 * E * (TS.mul * ordStoreLog eCap + 100 + (1 + 1 + 1) + 8) ≤
      2 * E * (TS.mul * ordStoreLog eCap + 140) := Nat.mul_le_mul_left _ (by omega)
  have hphi0 : htour.rep.phi tourH tx₀ st.mem = htour.rep.phi tourH tx₀ M := by rw [hst]
  omega

end

end MinCostFlow.SparseCore.Program.Restart
