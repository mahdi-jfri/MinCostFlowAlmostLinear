module

public import MinCostFlow.Spanner.ProgTask3Ctx
public import MinCostFlow.Spanner.ProgWordRAMPot

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# `W_sub` Data-Structure Array Operations for Word-RAM Task 3

Defines `DSArrayWAt` for the array of per-component `PathDS` handles `[0..upTo)` on `c.W_sub`,
together with framing (`frame_range`, `frame_below`, `mono_hCur`) and single-call wrappers
(`step_init`, `call_delete`, `call_getPath`) preserving disjoint footprints and potential sum.
-/

/-- Disjointness + representation invariant for the `W_sub` PathDS array `[0..upTo)`. -/
structure DSArrayWAt (pdsImpl : PathDSImpl) (comps : List CompInfo)
    (phiNum phiDen M w dsBaseAddr handlesAddr hCur : ℕ) (mem : ℕ → ℕ)
    (upTo : ℕ) (states : ℕ → PathDSAbsState) (reps : ℕ → pdsImpl.R.τ) : Prop where
  h_ge : dsBaseAddr ≤ hCur
  zero_from : WordRAM.ZeroFrom mem hCur
  at_ci : ∀ ci < upTo,
    let handle := mem (handlesAddr + ci)
    dsBaseAddr ≤ handle ∧ handle ≤ hCur ∧
      pdsImpl.R.rep handle (states ci) (reps ci) mem ∧
      (∀ a, pdsImpl.R.foot handle (reps ci) a → dsBaseAddr ≤ a ∧ a < hCur) ∧
      (states ci).G = (comps.getD ci defaultCompInfo).W_sub ∧
      (states ci).phiNum = phiNum ∧ (states ci).phiDen = phiDen ∧ (states ci).M = M ∧
      PathDSAbsState.Valid pdsImpl.params (states ci)
  disjoint : ∀ ci₁ < upTo, ∀ ci₂ < upTo, ci₁ ≠ ci₂ →
    ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci₁)) (reps ci₁) a →
      ¬pdsImpl.R.foot (mem (handlesAddr + ci₂)) (reps ci₂) a

lemma DSArrayWAt.frame_range {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo : ℕ}
    {mem mem' : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    (hLoc : pdsImpl.R.Local)
    (h : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hHdl : ∀ ci < upTo, mem' (handlesAddr + ci) = mem (handlesAddr + ci))
    (hDS : ∀ a, dsBaseAddr ≤ a → a < hCur → mem' a = mem a)
    (hZ : WordRAM.ZeroFrom mem' hCur) :
    DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem' upTo states reps ∧
      dsTotalPhi pdsImpl handlesAddr upTo reps mem' = dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  refine ⟨⟨h.h_ge, hZ, fun ci hci => ?_, fun ci₁ h1 ci₂ h2 hne a ha => ?_⟩, ?_⟩
  · have hm := h.at_ci ci hci
    rw [hHdl ci hci]
    have hft : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → mem a = mem' a := by
      intro a ha
      have hb := hm.2.2.2.1 a ha
      exact (hDS a hb.1 hb.2).symm
    have hloc := hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft
    exact ⟨hm.1, hm.2.1, hloc.1 hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  · rw [hHdl ci₁ h1] at ha
    rw [hHdl ci₂ h2]
    exact h.disjoint ci₁ h1 ci₂ h2 hne a ha
  · unfold dsTotalPhi
    refine Finset.sum_congr rfl fun ci hci => ?_
    have hci' := Finset.mem_range.mp hci
    have hm := h.at_ci ci hci'
    rw [hHdl ci hci']
    have hft : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → mem a = mem' a := by
      intro a ha; have hb := hm.2.2.2.1 a ha; exact (hDS a hb.1 hb.2).symm
    exact (hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft).2.symm

lemma DSArrayWAt.frame_below {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo : ℕ}
    {mem mem' : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    (hLoc : pdsImpl.R.Local)
    (h : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hHdl : ∀ ci < upTo, mem' (handlesAddr + ci) = mem (handlesAddr + ci))
    (hDS : ∀ a, dsBaseAddr ≤ a → a < hCur → mem' a = mem a)
    (hZ : ∀ a, hCur ≤ a → mem' a = mem a) :
    DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem' upTo states reps ∧
      dsTotalPhi pdsImpl handlesAddr upTo reps mem' = dsTotalPhi pdsImpl handlesAddr upTo reps mem :=
  h.frame_range hLoc hHdl hDS (fun a ha => by rw [hZ a ha]; exact h.zero_from a ha)

lemma DSArrayWAt.mono_hCur {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur hCur' upTo : ℕ}
    {mem mem' : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    (hLoc : pdsImpl.R.Local)
    (h : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hle : hCur ≤ hCur')
    (hHdl : ∀ ci < upTo, mem' (handlesAddr + ci) = mem (handlesAddr + ci))
    (hDS : ∀ a, dsBaseAddr ≤ a → a < hCur → mem' a = mem a)
    (hZ : WordRAM.ZeroFrom mem' hCur') :
    DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur' mem' upTo states reps ∧
      dsTotalPhi pdsImpl handlesAddr upTo reps mem' = dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  refine ⟨⟨le_trans h.h_ge hle, hZ, fun ci hci => ?_, fun ci₁ h1 ci₂ h2 hne a ha => ?_⟩, ?_⟩
  · have hm := h.at_ci ci hci
    rw [hHdl ci hci]
    have hft : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → mem a = mem' a := by
      intro a ha; have hb := hm.2.2.2.1 a ha; exact (hDS a hb.1 hb.2).symm
    have hloc := hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft
    exact ⟨hm.1, le_trans hm.2.1 hle, hloc.1 hm.2.2.1,
      fun a ha => ⟨(hm.2.2.2.1 a ha).1, lt_of_lt_of_le (hm.2.2.2.1 a ha).2 hle⟩, hm.2.2.2.2⟩
  · rw [hHdl ci₁ h1] at ha
    rw [hHdl ci₂ h2]
    exact h.disjoint ci₁ h1 ci₂ h2 hne a ha
  · unfold dsTotalPhi
    refine Finset.sum_congr rfl fun ci hci => ?_
    have hci' := Finset.mem_range.mp hci
    have hm := h.at_ci ci hci'
    rw [hHdl ci hci']
    have hft : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → mem a = mem' a := by
      intro a ha; have hb := hm.2.2.2.1 a ha; exact (hDS a hb.1 hb.2).symm
    exact (hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft).2.symm

lemma DSArrayWAt.step_init {p : WordRAM.Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {gAddr : ℕ} {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hup : upTo < comps.length) (hHdl_lt : handlesAddr + comps.length ≤ dsBaseAddr)
    (hg_w : gAddr < 2 ^ w) (hp_w : phiNum < 2 ^ w) (hd_w : phiDen < 2 ^ w)
    (hM_w : M < 2 ^ w) (hh_w : hCur < 2 ^ w)
    (hga_le : gAddr + comps[upTo].W_sub.encode.length ≤ hCur)
    (hG_at : GraphAt mem gAddr comps[upTo].W_sub)
    (hφ1 : 1 ≤ phiNum) (hφ2 : phiNum ≤ phiDen)
    (hWval : comps[upTo].W_sub.IsValid) (hWm1 : 1 ≤ comps[upTo].W_sub.m)
    (hWmM : comps[upTo].W_sub.m ≤ M) (hdeg : ∀ v < comps[upTo].W_sub.n, 1 ≤ comps[upTo].W_sub.deg v)
    (hexp : comps[upTo].W_sub.IsConductanceExpanderOn comps[upTo].W_sub.verts (↑phiNum / ↑phiDen))
    (hcw : pdsImpl.params.cw * (Nat.log 2 (comps[upTo].W_sub.n + comps[upTo].W_sub.m +
      phiDen + M + ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.initSpace phiNum phiDen comps[upTo].W_sub.n comps[upTo].W_sub.m M < 2 ^ w) :
    ∃ body o st' c s' x',
      p.procs[dsBase]? = some body ∧
      WordRAM.Runs w p ω body (WordRAM.startState [gAddr, phiNum, phiDen, M, hCur] mem pos) o st' c ∧
      o.value ≤ hCur + pdsImpl.params.initSpace phiNum phiDen comps[upTo].W_sub.n comps[upTo].W_sub.m M ∧
      hCur ≤ o.value ∧
      (∀ a < hCur, st'.mem a = mem a) ∧
      (∀ a, pdsImpl.R.foot hCur x' a → hCur ≤ a ∧ a < o.value) ∧
      s'.Vhat = ∅ ∧ s'.deleted = ∅ ∧
      let mem'' := Function.update st'.mem (handlesAddr + upTo) hCur
      let states' := Function.update states upTo s'
      let reps' := Function.update reps upTo x'
      DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value mem'' (upTo + 1) states' reps' ∧
      c + dsTotalPhi pdsImpl handlesAddr (upTo + 1) reps' mem'' ≤
        ⌈pdsImpl.params.K_init * ↑comps[upTo].W_sub.m * pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ +
          dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  have hLoc := hSpec.1
  have hRead : Cited.readGraph mem gAddr = comps[upTo].W_sub := graphAt_iff_readGraph.mp hG_at
  have hArgs : ∀ a ∈ [gAddr, phiNum, phiDen, M, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPre : (pathDSDataStructure pdsImpl.params w).initPre [gAddr, phiNum, phiDen, M, hCur] mem :=
    ⟨gAddr, phiNum, phiDen, M, hCur, comps[upTo].W_sub, rfl, hga_le, hG_at, hφ1, hφ2,
      hWval, hWm1, hWmM, hdeg, hexp, hcw⟩
  have hSp_eq : (pathDSDataStructure pdsImpl.params w).initSpace [gAddr, phiNum, phiDen, M, hCur] mem =
      pdsImpl.params.initSpace phiNum phiDen comps[upTo].W_sub.n comps[upTo].W_sub.m M := by
    simp [pathDSDataStructure, hRead]
  have hCo_eq : (pathDSDataStructure pdsImpl.params w).initCost [gAddr, phiNum, phiDen, M, hCur] mem =
      ⌈pdsImpl.params.K_init * ↑comps[upTo].W_sub.m * pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, hRead]
  have hHeap : WordRAM.heapArg [gAddr, phiNum, phiDen, M, hCur] = hCur := by simp [WordRAM.heapArg]
  obtain ⟨body, hproc, o, st', c, hruns, s', x', hrep, hpost, hresp, hcost⟩ :=
    hSpec.2.1 [gAddr, phiNum, phiDen, M, hCur] mem pos ω hArgs hPre (hHeap ▸ hArr.zero_from) (hHeap ▸ hSp_eq ▸ hSpace_w)
  rw [hHeap, hSp_eq] at hresp
  rw [hHeap] at hrep hcost
  rw [hCo_eq] at hcost
  rcases hresp with ⟨hle_h, hle_sp, hz_o, hpres, hft_new⟩
  rcases hpost with ⟨gAddr', pN', pD', M', h', G', heq_a, hG'_at, hs_phiN, hs_phiD, hs_M, hs_G, hs_vh, hs_del, hs_val⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨hg_eq, hpN_eq, hpD_eq, hM_eq, _hh_eq⟩
  rw [← hg_eq] at hG'_at
  rw [← hpN_eq] at hs_phiN
  rw [← hpD_eq] at hs_phiD
  rw [← hM_eq] at hs_M
  have hG_eq : G' = comps[upTo].W_sub := (graphAt_iff_readGraph.mp hG'_at).symm.trans hRead
  have hs_G' : s'.G = comps[upTo].W_sub := hs_G.trans hG_eq
  have hpres' : ∀ a < hCur, st'.mem a = mem a := fun a ha => hpres a ha (by simp)
  have hft_new' : ∀ a, pdsImpl.R.foot hCur x' a → hCur ≤ a ∧ a < o.value := by
    intro a ha; rcases hft_new a ha with hf | ⟨hl, hr⟩; exact False.elim hf; exact ⟨hl, hr⟩
  have hbase_le : dsBaseAddr ≤ hCur := hArr.h_ge
  let mem'' := Function.update st'.mem (handlesAddr + upTo) hCur
  let states' := Function.update states upTo s'
  let reps' := Function.update reps upTo x'
  have hArr_sub : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value mem'' upTo states reps ∧
      dsTotalPhi pdsImpl handlesAddr upTo reps mem'' = dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
    refine hArr.mono_hCur hLoc hle_h (fun ci hci => ?_) (fun a ha1 ha2 => ?_) (fun a ha => ?_)
    · have hne : handlesAddr + ci ≠ handlesAddr + upTo := by omega
      have hlt : handlesAddr + ci < hCur := by omega
      simp only [mem'', Function.update_of_ne hne, hpres' _ hlt]
    · have hne : a ≠ handlesAddr + upTo := by omega
      simp only [mem'', Function.update_of_ne hne, hpres' a ha2]
    · have hne : a ≠ handlesAddr + upTo := by omega
      simp only [mem'', Function.update_of_ne hne, hz_o a ha]
  have hup_eq : mem'' (handlesAddr + upTo) = hCur := Function.update_self _ _ _
  have hft_mem'' : ∀ a, pdsImpl.R.foot hCur x' a → st'.mem a = mem'' a := by
    intro a ha; have := (hft_new' a ha).1
    have hne : a ≠ handlesAddr + upTo := by omega
    simp [mem'', Function.update_of_ne hne]
  have hloc_new := hLoc hCur s' x' st'.mem mem'' hft_mem''
  refine ⟨body, o, st', c, s', x', hproc, hruns, hle_sp, hle_h, hpres', hft_new', hs_vh, hs_del, ?_, ?_⟩
  · refine ⟨le_trans hbase_le hle_h, hArr_sub.1.zero_from, fun ci hci => ?_, fun ci₁ h1 ci₂ h2 hne a ha => ?_⟩
    · by_cases hlt : ci < upTo
      · have hci' := hArr_sub.1.at_ci ci hlt
        have hne : ci ≠ upTo := by omega
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hci'
      · have hci_eq : ci = upTo := by omega
        simp only [hci_eq, Function.update_self]
        refine ⟨hbase_le, hle_h, hloc_new.1 hrep,
          fun a ha => ⟨le_trans hbase_le (hft_new' a ha).1, (hft_new' a ha).2⟩,
          by rw [List.getD_eq_getElem _ _ hup]; exact hs_G', hs_phiN, hs_phiD, hs_M, hs_val⟩
    · by_cases h1u : ci₁ = upTo <;> by_cases h2u : ci₂ = upTo
      · exact absurd (h1u.trans h2u.symm) hne
      · have h2lt : ci₂ < upTo := by omega
        simp only [h1u, Function.update_self] at ha
        have hne' : ci₂ ≠ upTo := by omega
        rw [Function.update_of_ne hne']
        have hft1 := (hft_new' a ha).1
        have h2_mem : Function.update st'.mem (handlesAddr + upTo) hCur (handlesAddr + ci₂) =
            mem (handlesAddr + ci₂) := by
          have hne2 : handlesAddr + ci₂ ≠ handlesAddr + upTo := by omega
          have hlt2 : handlesAddr + ci₂ < hCur := by omega
          rw [Function.update_of_ne hne2, hpres' _ hlt2]
        intro ha2
        rw [h2_mem] at ha2
        have hft2 := ((hArr.at_ci ci₂ h2lt).2.2.2.1 a ha2).2
        omega
      · have h1lt : ci₁ < upTo := by omega
        rw [Function.update_of_ne h1u] at ha
        simp only [h2u, Function.update_self]
        have h1_mem : Function.update st'.mem (handlesAddr + upTo) hCur (handlesAddr + ci₁) =
            mem (handlesAddr + ci₁) := by
          have hne1 : handlesAddr + ci₁ ≠ handlesAddr + upTo := by omega
          have hlt1 : handlesAddr + ci₁ < hCur := by omega
          rw [Function.update_of_ne hne1, hpres' _ hlt1]
        rw [h1_mem] at ha
        have hft1 := ((hArr.at_ci ci₁ h1lt).2.2.2.1 a ha).2
        intro ha2
        have hft2 := (hft_new' a ha2).1
        omega
      · have h1lt : ci₁ < upTo := by omega
        have h2lt : ci₂ < upTo := by omega
        rw [Function.update_of_ne h1u] at ha
        rw [Function.update_of_ne h2u]
        exact hArr_sub.1.disjoint ci₁ h1lt ci₂ h2lt hne a ha
  · have hsum_prev : ∑ ci ∈ Finset.range upTo, pdsImpl.R.phi (mem'' (handlesAddr + ci)) (reps' ci) mem'' =
        dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
      rw [← hArr_sub.2]
      unfold dsTotalPhi
      refine Finset.sum_congr rfl fun ci hci => ?_
      have hne : ci ≠ upTo := by have := Finset.mem_range.mp hci; omega
      simp [reps', Function.update_of_ne hne]
    change c + (∑ ci ∈ Finset.range (upTo + 1), pdsImpl.R.phi (mem'' (handlesAddr + ci)) (reps' ci) mem'') ≤
      ⌈pdsImpl.params.K_init * ↑comps[upTo].W_sub.m * pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ +
        dsTotalPhi pdsImpl handlesAddr upTo reps mem
    rw [Finset.sum_range_succ, hsum_prev, hup_eq]
    dsimp only [reps']
    rw [Function.update_self, ← hloc_new.2]
    omega

lemma DSArrayWAt.call_delete {p : WordRAM.Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase ci eL : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hci : ci < upTo) (_hup : upTo ≤ comps.length) (hHdl_lt : handlesAddr + upTo ≤ dsBaseAddr)
    (he_m : eL < (comps.getD ci defaultCompInfo).W_sub.m) (he_ndel : eL ∉ (states ci).deleted)
    (hh_w : hCur < 2 ^ w) (he_w : eL < 2 ^ w)
    (hcw : pdsImpl.params.cw * (Nat.log 2 ((comps.getD ci defaultCompInfo).W_sub.n +
      (comps.getD ci defaultCompInfo).W_sub.m + phiDen + M +
      ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.delSpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
      (comps.getD ci defaultCompInfo).W_sub.m M < 2 ^ w) :
    ∃ body o st' c s' x' L,
      p.procs[dsBase + 1]? = some body ∧
      WordRAM.Runs w p ω body (WordRAM.startState [mem (handlesAddr + ci), eL, hCur] mem pos) o st' c ∧
      hCur ≤ o.value ∧
      o.value ≤ hCur + pdsImpl.params.delSpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
        (comps.getD ci defaultCompInfo).W_sub.m M ∧
      (∀ a < dsBaseAddr, st'.mem a = mem a) ∧
      (∀ a < hCur, ¬ pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → st'.mem a = mem a) ∧
      (∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) x' a →
        pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a ∨ (hCur ≤ a ∧ a < o.value)) ∧
      s'.G = (states ci).G ∧ s'.phiNum = phiNum ∧ s'.phiDen = phiDen ∧ s'.M = M ∧
      s'.deleted = insert eL (states ci).deleted ∧ (states ci).Vhat ⊆ s'.Vhat ∧
      WordRAM.SeqAt st'.mem hCur L ∧ L.Nodup ∧ L.toFinset = s'.Vhat \ (states ci).Vhat ∧
      DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
        (Function.update states ci s') (Function.update reps ci x') ∧
      c + dsTotalPhi pdsImpl handlesAddr upTo (Function.update reps ci x') st'.mem ≤
        ⌈pdsImpl.params.K_del * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ +
          dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  have hLoc := hSpec.1
  have hm := hArr.at_ci ci hci
  rcases hm with ⟨hb_lo, hb_hi, hrep, hft, hG, hpN, hpD, hM, hval⟩
  have hb_w : mem (handlesAddr + ci) < 2 ^ w := lt_of_le_of_lt hb_hi hh_w
  have hArgs : ∀ a ∈ [mem (handlesAddr + ci), eL, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hφ_in : (states ci).φ_in = ↑phiNum / ↑phiDen := by simp [PathDSAbsState.φ_in, hpN, hpD]
  have hPre : (pathDSDataStructure pdsImpl.params w).pre 0 (states ci) [mem (handlesAddr + ci), eL, hCur] mem :=
    ⟨mem (handlesAddr + ci), eL, hCur, rfl, hval, hG ▸ he_m, he_ndel, by simpa [hG, hpD, hM, hφ_in] using hcw⟩
  have hSp_eq : (pathDSDataStructure pdsImpl.params w).space 0 (states ci) [mem (handlesAddr + ci), eL, hCur] mem =
      pdsImpl.params.delSpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
        (comps.getD ci defaultCompInfo).W_sub.m M := by
    simp [pathDSDataStructure, hpN, hpD, hM, hG]
  have hCo_eq : (pathDSDataStructure pdsImpl.params w).cost 0 (states ci) [mem (handlesAddr + ci), eL, hCur] mem =
      ⌈pdsImpl.params.K_del * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, hφ_in, hM]
  have hHeap : WordRAM.heapArg [mem (handlesAddr + ci), eL, hCur] = hCur := by simp [WordRAM.heapArg]
  have hft_lt : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → a < hCur :=
    fun a ha => (hft a ha).2
  obtain ⟨body, hproc, o, st', c, hruns, s', x', hrep', hpost, hresp, hcost⟩ :=
    hSpec.2.2 0 (mem (handlesAddr + ci)) (states ci) (reps ci) [mem (handlesAddr + ci), eL, hCur] mem pos ω
      hArgs rfl hrep hPre hft_lt (hHeap ▸ hArr.zero_from) (hHeap ▸ hSp_eq ▸ hSpace_w)
  rw [hHeap, hSp_eq] at hresp
  rw [hCo_eq] at hcost
  rcases hresp with ⟨hle_h, hle_sp, hz_o, hpres, hft_new⟩
  rcases hpost with ⟨b', e', h', heq_a, hs'_pN, hs'_pD, hs'_M, hs'_G, hs'_del, hs'_vh, hs'_val,
    L, hL_seq, hL_nd, hL_fin⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨hb_eq, he_eq, hh_eq⟩
  subst b'; subst e'; subst h'
  have hpres_below : ∀ a < dsBaseAddr, st'.mem a = mem a := by
    intro a ha
    have hlt_h : a < hCur := lt_of_lt_of_le ha hArr.h_ge
    refine hpres a hlt_h (fun hf => by have := (hft a hf).1; omega)
  have hother : ∀ cj, cj < upTo → cj ≠ ci →
      pdsImpl.R.rep (mem (handlesAddr + cj)) (states cj) (reps cj) st'.mem ∧
      pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) st'.mem =
        pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) mem := by
    intro cj hcj hne
    have hjm := hArr.at_ci cj hcj
    have hmem_eq : ∀ a, pdsImpl.R.foot (mem (handlesAddr + cj)) (reps cj) a → mem a = st'.mem a := by
      intro a ha
      have hb := hjm.2.2.2.1 a ha
      have hnd := hArr.disjoint ci hci cj hcj (Ne.symm hne) a
      have hnot : ¬pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a := fun h => hnd h ha
      exact (hpres a hb.2 hnot).symm
    have hloc := hLoc (mem (handlesAddr + cj)) (states cj) (reps cj) mem st'.mem hmem_eq
    exact ⟨hloc.1 hjm.2.2.1, hloc.2.symm⟩
  have hci_hdl : st'.mem (handlesAddr + ci) = mem (handlesAddr + ci) :=
    hpres_below _ (by omega)
  refine ⟨body, o, st', c, s', x', L, hproc, hruns, hle_h, hle_sp, hpres_below, hpres, hft_new,
    hs'_G, hs'_pN.trans hpN, hs'_pD.trans hpD, hs'_M.trans hM, hs'_del, hs'_vh, hL_seq, hL_nd, hL_fin, ?_, ?_⟩
  · refine ⟨le_trans hArr.h_ge hle_h, hz_o, fun cj hcj => ?_, fun cj₁ h1 cj₂ h2 hne a ha => ?_⟩
    · by_cases heq : cj = ci
      · subst heq
        simp only [Function.update_self, hci_hdl]
        refine ⟨hb_lo, le_trans hb_hi hle_h, hrep', fun a ha => ?_,
          hs'_G.trans hG, hs'_pN.trans hpN, hs'_pD.trans hpD, hs'_M.trans hM, hs'_val⟩
        rcases hft_new a ha with hf | ⟨hl, hr⟩
        · exact ⟨(hft a hf).1, lt_of_lt_of_le (hft a hf).2 hle_h⟩
        · exact ⟨le_trans hArr.h_ge hl, hr⟩
      · have hjm := hArr.at_ci cj hcj
        have hcj_hdl : st'.mem (handlesAddr + cj) = mem (handlesAddr + cj) :=
          hpres_below _ (by omega)
        simp only [Function.update_of_ne heq, hcj_hdl]
        exact ⟨hjm.1, le_trans hjm.2.1 hle_h, (hother cj hcj heq).1,
          fun a ha => ⟨(hjm.2.2.2.1 a ha).1, lt_of_lt_of_le (hjm.2.2.2.1 a ha).2 hle_h⟩, hjm.2.2.2.2⟩
    · have h1_hdl : st'.mem (handlesAddr + cj₁) = mem (handlesAddr + cj₁) := hpres_below _ (by omega)
      have h2_hdl : st'.mem (handlesAddr + cj₂) = mem (handlesAddr + cj₂) := hpres_below _ (by omega)
      rw [h1_hdl] at ha
      rw [h2_hdl]
      by_cases hc1 : cj₁ = ci <;> by_cases hc2 : cj₂ = ci
      · exact absurd (hc1.trans hc2.symm) hne
      · subst hc1
        simp only [Function.update_self, Function.update_of_ne (Ne.symm hne)] at ha ⊢
        rcases hft_new a ha with hf | ⟨hl, _⟩
        · exact hArr.disjoint cj₁ h1 cj₂ h2 hne a hf
        · intro ha2; have := (hArr.at_ci cj₂ h2).2.2.2.1 a ha2; omega
      · subst hc2
        simp only [Function.update_of_ne hc1, Function.update_self] at ha ⊢
        intro ha2
        rcases hft_new a ha2 with hf | ⟨hl, _⟩
        · exact hArr.disjoint cj₁ h1 cj₂ h2 hne a ha hf
        · have := (hArr.at_ci cj₁ h1).2.2.2.1 a ha; omega
      · simp only [Function.update_of_ne hc1, Function.update_of_ne hc2] at ha ⊢
        exact hArr.disjoint cj₁ h1 cj₂ h2 hne a ha
  · unfold dsTotalPhi
    have hci_fin : ci ∈ Finset.range upTo := Finset.mem_range.mpr hci
    rw [← Finset.add_sum_erase _ _ hci_fin, ← Finset.add_sum_erase _ _ hci_fin]
    have hsum_eq : ∑ cj ∈ (Finset.range upTo).erase ci,
          pdsImpl.R.phi (st'.mem (handlesAddr + cj)) (Function.update reps ci x' cj) st'.mem =
        ∑ cj ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) mem := by
      refine Finset.sum_congr rfl fun cj hcj => ?_
      rcases Finset.mem_erase.mp hcj with ⟨hne, hmem⟩
      have hcj' := Finset.mem_range.mp hmem
      have hhdl : st'.mem (handlesAddr + cj) = mem (handlesAddr + cj) := hpres_below _ (by omega)
      simp only [Function.update_of_ne hne, hhdl]
      exact (hother cj hcj' hne).2
    simp only [Function.update_self, hci_hdl, hsum_eq]
    omega

lemma DSArrayWAt.call_getPath {p : WordRAM.Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase ci uL vL : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hci : ci < upTo) (_hup : upTo ≤ comps.length) (hHdl_lt : handlesAddr + upTo ≤ dsBaseAddr)
    (hu : uL ∈ (states ci).G.verts \ (states ci).Vhat)
    (hv : vL ∈ (states ci).G.verts \ (states ci).Vhat)
    (hu_w : uL < 2 ^ w) (hv_w : vL < 2 ^ w) (hh_w : hCur < 2 ^ w)
    (hcw : pdsImpl.params.cw * (Nat.log 2 ((comps.getD ci defaultCompInfo).W_sub.n +
      (comps.getD ci defaultCompInfo).W_sub.m + phiDen + M +
      ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.querySpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
      (comps.getD ci defaultCompInfo).W_sub.m M < 2 ^ w) :
    ∃ body o st' c x' P,
      p.procs[dsBase + 2]? = some body ∧
      WordRAM.Runs w p ω body (WordRAM.startState [mem (handlesAddr + ci), uL, vL, hCur] mem pos) o st' c ∧
      hCur ≤ o.value ∧
      o.value ≤ hCur + pdsImpl.params.querySpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
        (comps.getD ci defaultCompInfo).W_sub.m M ∧
      (∀ a < dsBaseAddr, st'.mem a = mem a) ∧
      (∀ a < hCur, ¬ pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → st'.mem a = mem a) ∧
      (∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) x' a →
        pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a ∨ (hCur ≤ a ∧ a < o.value)) ∧
      WalkAt st'.mem hCur P ∧
      Walk.IsWalk (comps.getD ci defaultCompInfo).W_sub uL vL P ∧
      P.verts.Nodup ∧ (∀ e ∈ P.edges, e ∉ (states ci).deleted) ∧
      (∀ y ∈ P.verts, y ∉ (states ci).Vhat) ∧
      (P.edges.length : ℝ) ≤ pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M ∧
      DSArrayWAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
        states (Function.update reps ci x') ∧
      c + dsTotalPhi pdsImpl handlesAddr upTo (Function.update reps ci x') st'.mem ≤
        ⌈pdsImpl.params.K_query * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ +
          dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  have hLoc := hSpec.1
  have hm := hArr.at_ci ci hci
  rcases hm with ⟨hb_lo, hb_hi, hrep, hft, hG, hpN, hpD, hM, hval⟩
  have hb_w : mem (handlesAddr + ci) < 2 ^ w := lt_of_le_of_lt hb_hi hh_w
  have hArgs : ∀ a ∈ [mem (handlesAddr + ci), uL, vL, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hφ_in : (states ci).φ_in = ↑phiNum / ↑phiDen := by simp [PathDSAbsState.φ_in, hpN, hpD]
  have hPre : (pathDSDataStructure pdsImpl.params w).pre 1 (states ci)
      [mem (handlesAddr + ci), uL, vL, hCur] mem :=
    ⟨mem (handlesAddr + ci), uL, vL, hCur, rfl, hval, hu, hv, by simpa [hG, hpD, hM, hφ_in] using hcw⟩
  have hSp_eq : (pathDSDataStructure pdsImpl.params w).space 1 (states ci)
      [mem (handlesAddr + ci), uL, vL, hCur] mem =
      pdsImpl.params.querySpace phiNum phiDen (comps.getD ci defaultCompInfo).W_sub.n
        (comps.getD ci defaultCompInfo).W_sub.m M := by
    simp [pathDSDataStructure, hpN, hpD, hM, hG]
  have hCo_eq : (pathDSDataStructure pdsImpl.params w).cost 1 (states ci)
      [mem (handlesAddr + ci), uL, vL, hCur] mem =
      ⌈pdsImpl.params.K_query * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, hφ_in, hM]
  have hHeap : WordRAM.heapArg [mem (handlesAddr + ci), uL, vL, hCur] = hCur := by simp [WordRAM.heapArg]
  have hft_lt : ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a → a < hCur :=
    fun a ha => (hft a ha).2
  obtain ⟨body, hproc, o, st', c, hruns, s', x', hrep', hpost, hresp, hcost⟩ :=
    hSpec.2.2 1 (mem (handlesAddr + ci)) (states ci) (reps ci)
      [mem (handlesAddr + ci), uL, vL, hCur] mem pos ω
      hArgs rfl hrep hPre hft_lt (hHeap ▸ hArr.zero_from) (hHeap ▸ hSp_eq ▸ hSpace_w)
  rw [hHeap, hSp_eq] at hresp
  rw [hCo_eq] at hcost
  rcases hresp with ⟨hle_h, hle_sp, hz_o, hpres, hft_new⟩
  rcases hpost with ⟨b', u', v', h', heq_a, rfl, P, hP_wk, hP_iso, hP_nd, hP_ndel, hP_nvh, hP_len⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨hb_eq, hu_eq, hv_eq, hh_eq⟩
  subst b'; subst u'; subst v'; subst h'
  rw [hφ_in, hM] at hP_len
  have hpres_below : ∀ a < dsBaseAddr, st'.mem a = mem a := by
    intro a ha
    have hlt_h : a < hCur := lt_of_lt_of_le ha hArr.h_ge
    refine hpres a hlt_h (fun hf => by have := (hft a hf).1; omega)
  have hother : ∀ cj, cj < upTo → cj ≠ ci →
      pdsImpl.R.rep (mem (handlesAddr + cj)) (states cj) (reps cj) st'.mem ∧
      pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) st'.mem =
        pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) mem := by
    intro cj hcj hne
    have hjm := hArr.at_ci cj hcj
    have hmem_eq : ∀ a, pdsImpl.R.foot (mem (handlesAddr + cj)) (reps cj) a → mem a = st'.mem a := by
      intro a ha
      have hb := hjm.2.2.2.1 a ha
      have hnd := hArr.disjoint ci hci cj hcj (Ne.symm hne) a
      have hnot : ¬pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a := fun h => hnd h ha
      exact (hpres a hb.2 hnot).symm
    have hloc := hLoc (mem (handlesAddr + cj)) (states cj) (reps cj) mem st'.mem hmem_eq
    exact ⟨hloc.1 hjm.2.2.1, hloc.2.symm⟩
  have hci_hdl : st'.mem (handlesAddr + ci) = mem (handlesAddr + ci) := hpres_below _ (by omega)
  refine ⟨body, o, st', c, x', P, hproc, hruns, hle_h, hle_sp, hpres_below, hpres, hft_new,
    hP_wk, hG ▸ hP_iso, hP_nd, hP_ndel, hP_nvh, hP_len, ?_, ?_⟩
  · refine ⟨le_trans hArr.h_ge hle_h, hz_o, fun cj hcj => ?_, fun cj₁ h1 cj₂ h2 hne a ha => ?_⟩
    · by_cases heq : cj = ci
      · subst heq
        simp only [Function.update_self, hci_hdl]
        refine ⟨hb_lo, le_trans hb_hi hle_h, hrep', fun a ha => ?_, hG, hpN, hpD, hM, hval⟩
        rcases hft_new a ha with hf | ⟨hl, hr⟩
        · exact ⟨(hft a hf).1, lt_of_lt_of_le (hft a hf).2 hle_h⟩
        · exact ⟨le_trans hArr.h_ge hl, hr⟩
      · have hjm := hArr.at_ci cj hcj
        have hcj_hdl : st'.mem (handlesAddr + cj) = mem (handlesAddr + cj) := hpres_below _ (by omega)
        simp only [Function.update_of_ne heq, hcj_hdl]
        exact ⟨hjm.1, le_trans hjm.2.1 hle_h, (hother cj hcj heq).1,
          fun a ha => ⟨(hjm.2.2.2.1 a ha).1, lt_of_lt_of_le (hjm.2.2.2.1 a ha).2 hle_h⟩, hjm.2.2.2.2⟩
    · have h1_hdl : st'.mem (handlesAddr + cj₁) = mem (handlesAddr + cj₁) := hpres_below _ (by omega)
      have h2_hdl : st'.mem (handlesAddr + cj₂) = mem (handlesAddr + cj₂) := hpres_below _ (by omega)
      rw [h1_hdl] at ha
      rw [h2_hdl]
      by_cases hc1 : cj₁ = ci <;> by_cases hc2 : cj₂ = ci
      · exact absurd (hc1.trans hc2.symm) hne
      · subst hc1
        simp only [Function.update_self, Function.update_of_ne (Ne.symm hne)] at ha ⊢
        rcases hft_new a ha with hf | ⟨hl, _⟩
        · exact hArr.disjoint cj₁ h1 cj₂ h2 hne a hf
        · intro ha2; have := (hArr.at_ci cj₂ h2).2.2.2.1 a ha2; omega
      · subst hc2
        simp only [Function.update_of_ne hc1, Function.update_self] at ha ⊢
        intro ha2
        rcases hft_new a ha2 with hf | ⟨hl, _⟩
        · exact hArr.disjoint cj₁ h1 cj₂ h2 hne a ha hf
        · have := (hArr.at_ci cj₁ h1).2.2.2.1 a ha; omega
      · simp only [Function.update_of_ne hc1, Function.update_of_ne hc2] at ha ⊢
        exact hArr.disjoint cj₁ h1 cj₂ h2 hne a ha
  · unfold dsTotalPhi
    have hci_fin : ci ∈ Finset.range upTo := Finset.mem_range.mpr hci
    rw [← Finset.add_sum_erase _ _ hci_fin, ← Finset.add_sum_erase _ _ hci_fin]
    have hsum_eq : ∑ cj ∈ (Finset.range upTo).erase ci,
          pdsImpl.R.phi (st'.mem (handlesAddr + cj)) (Function.update reps ci x' cj) st'.mem =
        ∑ cj ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (mem (handlesAddr + cj)) (reps cj) mem := by
      refine Finset.sum_congr rfl fun cj hcj => ?_
      rcases Finset.mem_erase.mp hcj with ⟨hne, hmem⟩
      have hcj' := Finset.mem_range.mp hmem
      have hhdl : st'.mem (handlesAddr + cj) = mem (handlesAddr + cj) := hpres_below _ (by omega)
      simp only [Function.update_of_ne hne, hhdl]
      exact (hother cj hcj' hne).2
    simp only [Function.update_self, hci_hdl, hsum_eq]
    omega

end MinCostFlow.Spanner