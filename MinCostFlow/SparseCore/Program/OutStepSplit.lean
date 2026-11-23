module

public import MinCostFlow.SparseCore.Program.OutStepSplitC

/-!
# The splits of the output step

The split phase of the output step (`osSplitPhase`) walks the linked split records of the helper
(`OutSplitListsAt`) and, for each split, runs the three parts of a split round. Each round adds
one record to the batch and the edit `outSplitEdit` to the edits. This file proves one round
(`osSplitIter_runs`), the loop (`osSplitLoop_runs`, by induction on the splits left) and the
phase (`osSplitPhase_runs`). Only `osSplitPhase_runs` is used later.

The batch record of a split has `4 + Enc(u)` words and its edit has `3 + Enc(u)` words, so after
the splits `P` the two pointers have moved by `4 |P| + Enc(P)` and `3 |P| + Enc(P)`. The cost is
at most `2000` per end of the helper lists plus `5000` per unit of `Enc(P)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- A list of distinct ends of edges below `eCap` has at most `2 eCap` ends. -/
theorem endList_length_le {Y : List End} {eCap : ℕ} (hnd : Y.Nodup) (hY : ∀ x ∈ Y, x.1 < eCap) :
    Y.length ≤ 2 * eCap := by
  have h := nodup_length_le_of_lt (L := Y.map endKey) (m := 2 * eCap)
    (hnd.map endKey_injective) (fun k hk => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      exact endKey_lt_two_mul (hY x hx))
  rwa [List.length_map] at h

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- **One split round.** -/
theorem osSplitIter_runs (hC : SCtx T A tx₀) {au gd flt wk : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hflt : p.procs[flt]? = some outFilterBody) (hwk : p.procs[wk]? = some outWalkBody)
    {st : State} {a v v' nb ne : ℕ} {St Sh : Finset ℕ} {Y : List End}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (hR : SRegs st A vCap eCap) (h14 : st.regs 14 = bp) (h16 : st.regs 16 = ep)
    (h17 : st.regs 17 = nb) (h18 : st.regs 18 = ne) (h20 : st.regs 20 = a)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w)
    (hGU : G = S₀.applyBatch U) (hGv : G.IsValid) (hval : G.UpdateIsValid (.split v v' St Sh))
    (hv'c : v' < vCap) (ha5 : a + 5 ≤ A.h)
    (hafree : ∀ i < 5, ¬ ((outGraphRep vCap eCap).foot A.outH A.g (a + i) ∨
      T.rep.foot A.tourH tx₀ (a + i)))
    (hv : mem₀ a = v) (hv' : mem₀ (a + 1) = v') (hside : mem₀ (a + 2) ≤ 1)
    (hY : EndListAt mem₀ (mem₀ (a + 3)) Y) (hptr : mem₀ (a + 3) + 1 + Y.length ≤ A.h)
    (hpfree : ∀ i < 1 + Y.length, ¬ ((outGraphRep vCap eCap).foot A.outH A.g (mem₀ (a + 3) + i) ∨
      T.rep.foot A.tourH tx₀ (mem₀ (a + 3) + i)))
    (hnd : Y.Nodup) (hYc : ∀ x ∈ Y, x.1 < eCap)
    (hYs : ∀ x : End, x.1 ∈ G.E →
      (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x = if mem₀ (a + 2) = 0 then v else v'))
    (hspB : bp + 5 + 4 * eCap ≤ A.e0) (hspE : ep + 4 + 2 * eCap ≤ A.t0)
    (hnb : nb + 1 < 2 ^ w) (hne : ne + 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω (osSplitIter au gd flt wk) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) (U ++ [.split v v' St Sh])
        (E ++ [outSplitEdit G v v' St Sh]) (bp + (4 + G.updateEnc (.split v v' St Sh)))
        (ep + (3 + G.updateEnc (.split v v' St Sh))) cur s tx st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      SRegs st' A vCap eCap ∧ st'.regs 7 = st.regs 7 ∧
      st'.regs 14 = bp + (4 + G.updateEnc (.split v v' St Sh)) ∧
      st'.regs 16 = ep + (3 + G.updateEnc (.split v v' St Sh)) ∧
      st'.regs 17 = nb + 1 ∧ st'.regs 18 = ne + 1 ∧ st'.regs 20 = mem₀ (a + 4) ∧
      c ≤ 2000 * Y.length + 4700 * G.updateEnc (.split v v' St Sh) := by
  have hYl := endList_length_le hnd hYc
  obtain ⟨stA, cA, hrA, hBA, hpA, hoA, h21A, h22A, hcA⟩ := osSplitA_runs (ω := ω) hC hau hflt
    hB hR h14 h20 hw ht0 ha5 hafree hv hv' hside hY hptr hpfree hnd hYc hYs hval hv'c (by omega)
  have hRA : SRegs stA A vCap eCap := hR.of_fixed fun r hr => by
    unfold IsFixedReg at hr
    exact hoA r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have gA : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 9 →
      stA.regs r = st.regs r := hoA
  obtain ⟨stB, cB, L, hrB, hBB, hpB, hoB, h34B, h36B, hLnd, hLmem, hLB, hdecB, hencB, hcB⟩ :=
    osSplitB_runs (ω := ω) hC hgd hwk hBA hRA
      (by rw [gA 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        h16]) h21A h22A hw ht0 hGv hval hspE
  have hRB : SRegs stB A vCap eCap := hRA.of_fixed fun r hr => by
    unfold IsFixedReg at hr
    exact hoB r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have gB : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 9 → r ≠ 31 →
      r ≠ 32 → r ≠ 33 → r ≠ 34 → r ≠ 35 → r ≠ 36 → stB.regs r = st.regs r :=
    fun r a b c d e f g h i j k l m => by rw [hoB r h i j k l m, gA r a b c d e f g]
  have hLl : L.length ≤ 2 * eCap := by
    have := hLnd
    exact nodup_length_le_of_lt hLnd fun k hk => ((hLmem k).mp hk).1
  obtain ⟨stC, cC, hrC, hBC, hpC, hoC, h14C, h16C, h17C, h18C, h20C, hcC⟩ :=
    osSplitC_runs (ω := ω) (G := G) hC hflt hBB hGU hRB
      (by rw [gB 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h14])
      (by rw [gB 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h16])
      (by rw [gB 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h17])
      (by rw [gB 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h18])
      (by rw [gB 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h20])
      (by rw [hoB 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h21A])
      (by rw [hoB 22 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h22A])
      h34B h36B hLnd hLmem hLB hdecB hw ht0 hGv hval ha5 hafree (by omega) (by omega) hnb hne
  have e5 : 5 + L.length = 4 + G.updateEnc (.split v v' St Sh) := by omega
  have e4 : 4 + L.length = 3 + G.updateEnc (.split v v' St Sh) := by omega
  rw [e5, e4] at hBC
  rw [e5] at h14C
  rw [e4] at h16C
  refine ⟨stC, cA + (cB + cC), hrA _ _ _ _ (hrB _ _ _ _ hrC), hBC, by rw [hpC, hpB, hpA],
    hRB.of_fixed fun r hr => ?_, ?_, h14C, h16C, h17C, h18C, h20C, by omega⟩
  · unfold IsFixedReg at hr
    exact hoC r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hoC 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      gB 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

end MinCostFlow.SparseCore.Program

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ : MGraph} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ}

/-- **The loop of the splits**, by induction on the splits left. -/
theorem osSplitLoop_runs (hC : SCtx T A tx₀) {au gd flt wk : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hflt : p.procs[flt]? = some outFilterBody) (hwk : p.procs[wk]? = some outWalkBody)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) {keep E₀ : Finset ℕ}
    (hE₀ : ∀ e ∈ E₀, e < eCap) (P : List Update) :
    ∀ (Ys : List (List End)) (G : MGraph) (U : List Update) (E : List OrdEdit)
      (bp ep nb ne : ℕ) (st : State),
      SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem → SRegs st A vCap eCap →
      st.regs 14 = bp → st.regs 16 = ep → st.regs 17 = nb → st.regs 18 = ne →
      OutSplitListsAt mem₀ A.h
        (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a)
        keep E₀ (st.regs 20) G P Ys →
      G = S₀.applyBatch U → G.IsValid → G.BatchIsValid P →
      (∀ u ∈ P, UpdateWithinCaps vCap eCap u) → G.E ⊆ keep →
      bp + 4 * P.length + G.batchEnc P + 4 * eCap + 5 ≤ A.e0 →
      ep + 3 * P.length + G.batchEnc P + 2 * eCap + 4 ≤ A.t0 →
      nb + P.length < 2 ^ w → ne + P.length < 2 ^ w →
      ∃ st' c, Runs w p ω (.loop (.reg 20) (osSplitIter au gd flt wk)) st .normal st' c ∧
        SBase T A tx₀ mem₀ S₀ (G.applyBatch P) (U ++ P) (E ++ outPrefixEditsOn G P)
          (bp + (4 * P.length + G.batchEnc P)) (ep + (3 * P.length + G.batchEnc P)) cur s tx
          st'.mem ∧
        T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
        SRegs st' A vCap eCap ∧ st'.regs 7 = st.regs 7 ∧
        st'.regs 14 = bp + (4 * P.length + G.batchEnc P) ∧
        st'.regs 16 = ep + (3 * P.length + G.batchEnc P) ∧
        st'.regs 17 = nb + P.length ∧ st'.regs 18 = ne + P.length ∧
        c ≤ 2000 * (Ys.map List.length).sum + 5000 * G.batchEnc P + 2 := by
  induction P with
  | nil =>
    intro Ys G U E bp ep nb ne st hB hR h14 h16 h17 h18 hsl _ _ _ _ _ _ _ _ _
    match Ys, hsl with
    | [], hsl =>
      have h20 : st.regs 20 = 0 := hsl
      refine ⟨st, _, runs_loop_iff.mpr (Or.inl ⟨Expr.eval_reg_of_eq h20, rfl, rfl, rfl⟩), ?_, rfl,
        hR, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [MGraph.applyBatch, MGraph.batchEnc, outPrefixEditsOn] using hB
      · simpa [MGraph.batchEnc] using h14
      · simpa [MGraph.batchEnc] using h16
      · simpa using h17
      · simpa using h18
      · simp [Expr.size]
    | _ :: _, hsl => exact hsl.elim
  | cons u P ih =>
    intro Ys G U E bp ep nb ne st hB hR h14 h16 h17 h18 hsl hGU hGv hbv hcap hkeep hspB hspE hnb hne
    rcases Ys with _ | ⟨Y, Ys⟩
    · rcases u with ⟨⟩ | ⟨⟩ | ⟨⟩ <;> simp [OutSplitListsAt] at hsl
    rcases u with ⟨e, x, y⟩ | ⟨e⟩ | ⟨v, v', St, Sh⟩
    · simp [OutSplitListsAt] at hsl
    · simp [OutSplitListsAt] at hsl
    · 
      obtain ⟨hpos, ha5, hafree, hv, hv', hside, hY, hptr, hpfree, hnd, hYE, hYs, hrest⟩ := hsl
      have henc : G.batchEnc (.split v v' St Sh :: P) =
          G.updateEnc (.split v v' St Sh) + (G.applyUpdate (.split v v' St Sh)).batchEnc P := rfl
      have henc1 : 1 ≤ G.updateEnc (.split v v' St Sh) := by
        show 1 ≤ min _ _ + 1; omega
      simp only [List.length_cons] at hspB hspE hnb hne
      obtain ⟨st₁, c₁, hr₁, hB₁, hp₁, hR₁, h7₁, h14₁, h16₁, h17₁, h18₁, h20₁, hc₁⟩ :=
        osSplitIter_runs (ω := ω) hC hau hgd hflt hwk hB hR h14 h16 h17 h18 rfl hw ht0 hGU hGv
          hbv.1 (hcap _ List.mem_cons_self) ha5 hafree hv hv' hside hY hptr hpfree hnd
          (fun x hx => hE₀ _ (hYE x hx)) (fun x hx => hYs x (hkeep hx)) (by omega) (by omega)
          (by omega) (by omega)
      have hGU₁ : G.applyUpdate (.split v v' St Sh) = S₀.applyBatch (U ++ [.split v v' St Sh]) := by
        rw [hGU]; simp [MGraph.applyBatch, List.foldl_append]
      obtain ⟨st₂, c₂, hr₂, hB₂, hp₂, hR₂, h7₂, h14₂, h16₂, h17₂, h18₂, hc₂⟩ :=
        ih Ys _ _ _ _ _ _ _ st₁ hB₁ hR₁ h14₁ h16₁ h17₁ h18₁ (by rw [h20₁]; exact hrest) hGU₁
          (isValid_applyUpdate_of_notInsert hGv hbv.1) hbv.2
          (fun u hu => hcap u (List.mem_cons_of_mem _ hu)) hkeep (by omega) (by omega)
          (by omega) (by omega)
      have hbp : bp + (4 + G.updateEnc (.split v v' St Sh)) +
          (4 * P.length + (G.applyUpdate (.split v v' St Sh)).batchEnc P) =
          bp + (4 * (P.length + 1) + G.batchEnc (.split v v' St Sh :: P)) := by
        rw [henc]; ring
      have hep : ep + (3 + G.updateEnc (.split v v' St Sh)) +
          (3 * P.length + (G.applyUpdate (.split v v' St Sh)).batchEnc P) =
          ep + (3 * (P.length + 1) + G.batchEnc (.split v v' St Sh :: P)) := by
        rw [henc]; ring
      rw [hbp, hep, List.append_assoc, List.append_assoc, List.singleton_append,
        List.singleton_append] at hB₂
      rw [hbp] at h14₂
      rw [hep] at h16₂
      refine ⟨st₂, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨st.regs 20, st₁, c₁, c₂,
        Expr.eval_reg w 20 st, by omega, hr₁, hr₂, rfl⟩)), hB₂, by rw [hp₂, hp₁], hR₂,
        by rw [h7₂, h7₁], h14₂, h16₂, by rw [h17₂]; simp; omega, by rw [h18₂]; simp; omega, ?_⟩
      simp only [List.map_cons, List.sum_cons, Expr.size] at hc₂ ⊢
      rw [henc]
      omega

/-- **The split phase**: the splits `P` of the helper lists, from the first split record at
`splitPtr`. -/
theorem osSplitPhase_runs (hC : SCtx T A tx₀) {au gd flt wk : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hflt : p.procs[flt]? = some outFilterBody) (hwk : p.procs[wk]? = some outWalkBody)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) {keep E₀ : Finset ℕ}
    (hE₀ : ∀ e ∈ E₀, e < eCap) {P : List Update} {Ys : List (List End)} {G : MGraph}
    {U : List Update} {E : List OrdEdit} {bp ep : ℕ} {st : State}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem) (hR : SRegs st A vCap eCap)
    (h14 : st.regs 14 = bp) (h16 : st.regs 16 = ep) (h17 : st.regs 17 = U.length)
    (h18 : st.regs 18 = E.length)
    (hsl : OutSplitListsAt mem₀ A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a)
      keep E₀ A.splitPtr G P Ys)
    (hGU : G = S₀.applyBatch U) (hGv : G.IsValid) (hbv : G.BatchIsValid P)
    (hcap : ∀ u ∈ P, UpdateWithinCaps vCap eCap u) (hkeep : G.E ⊆ keep)
    (hspB : bp + 4 * P.length + G.batchEnc P + 4 * eCap + 5 ≤ A.e0)
    (hspE : ep + 3 * P.length + G.batchEnc P + 2 * eCap + 4 ≤ A.t0)
    (hnb : U.length + P.length < 2 ^ w) (hne : E.length + P.length < 2 ^ w) :
    ∃ st' c, Runs w p ω (osSplitPhase au gd flt wk) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ (G.applyBatch P) (U ++ P) (E ++ outPrefixEditsOn G P)
        (bp + (4 * P.length + G.batchEnc P)) (ep + (3 * P.length + G.batchEnc P)) cur s tx
        st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      SRegs st' A vCap eCap ∧ st'.regs 7 = st.regs 7 ∧
      st'.regs 14 = bp + (4 * P.length + G.batchEnc P) ∧
      st'.regs 16 = ep + (3 * P.length + G.batchEnc P) ∧
      st'.regs 17 = U.length + P.length ∧ st'.regs 18 = E.length + P.length ∧
      c ≤ 2000 * (Ys.map List.length).sum + 5000 * G.batchEnc P + 5 := by
  have hR' := hR
  obtain ⟨-, -, -, r3, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hR'
  obtain ⟨st₁, hr₁, hm₁, h20₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .reg 3) (st := st) (v := A.splitPtr) (Expr.eval_reg_of_eq r3)
  have g : ∀ r, r ≠ 20 → st₁.regs r = st.regs r := ho₁
  obtain ⟨st₂, c₂, hr₂, hB₂, hp₂, hR₂, h7₂, h14₂, h16₂, h17₂, h18₂, hc₂⟩ :=
    osSplitLoop_runs (ω := ω) hC hau hgd hflt hwk hw ht0 hE₀ P Ys G U E bp ep U.length E.length
      st₁ (by rw [hm₁]; exact hB) (hR.of_fixed fun r hr => g r (by rintro rfl; revert hr; decide))
      (by rw [g 14 (by omega), h14]) (by rw [g 16 (by omega), h16])
      (by rw [g 17 (by omega), h17]) (by rw [g 18 (by omega), h18]) (by rw [h20₁]; exact hsl)
      hGU hGv hbv hcap hkeep hspB hspE hnb hne
  refine ⟨st₂, _, runs_seq_normal hr₁ hr₂, hB₂, by rw [hp₂, hm₁], hR₂,
    by rw [h7₂, g 7 (by omega)], h14₂, h16₂, h17₂, h18₂, ?_⟩
  simp only [Expr.size] at hc₂ ⊢
  omega

end MinCostFlow.SparseCore.Program
