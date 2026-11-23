module

public import MinCostFlow.Spanner.ProgTask2Mem

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Task 2 PathDS delete/getPath calls and round potential -/

lemma DSArrayAt.call_delete {p : Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase ci b : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hci : ci < upTo) (hup : upTo ≤ comps.length)
    (hHdl_lt : handlesAddr + upTo ≤ dsBaseAddr)
    (hb_m : b < comps[ci].J_sub.m) (hb_ndel : b ∉ (states ci).deleted)
    (hh_w : hCur < 2 ^ w) (hb_w : b < 2 ^ w)
    (hcw : pdsImpl.params.cw * (Nat.log 2 (comps[ci].J_sub.n + comps[ci].J_sub.m + phiDen + M +
      ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.delSpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M < 2 ^ w) :
    ∃ body o st' c s' x' L,
      p.procs[dsBase + 1]? = some body ∧
      Runs w p ω body (startState [mem (handlesAddr + ci), b, hCur] mem pos) o st' c ∧
      hCur ≤ o.value ∧
      o.value ≤ hCur + pdsImpl.params.delSpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M ∧
      (∀ a < dsBaseAddr, st'.mem a = mem a) ∧
      s'.G = (states ci).G ∧ s'.phiNum = phiNum ∧ s'.phiDen = phiDen ∧ s'.M = M ∧
      s'.deleted = insert b (states ci).deleted ∧
      (states ci).Vhat ⊆ s'.Vhat ∧
      WordRAM.SeqAt st'.mem hCur L ∧ L.Nodup ∧ L.toFinset = s'.Vhat \ (states ci).Vhat ∧
      DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
        (Function.update states ci s') (Function.update reps ci x') ∧
      c + dsTotalPhi pdsImpl handlesAddr upTo (Function.update reps ci x') st'.mem ≤
        ⌈pdsImpl.params.K_del * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ +
          dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  have hci_at := hArr.at_ci ci hci
  have hci_c : ci < comps.length := lt_of_lt_of_le hci hup
  have hhdl_w : mem (handlesAddr + ci) < 2 ^ w := lt_of_le_of_lt hci_at.2.1 hh_w
  have hArgs_w : ∀ a ∈ [mem (handlesAddr + ci), b, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hG_eq : (states ci).G = comps[ci].J_sub := by
    rw [hci_at.2.2.2.2.1, List.getD_eq_getElem _ _ hci_c]
  have hφin_eq : (states ci).φ_in = (↑phiNum / ↑phiDen : ℝ) := by
    simp [PathDSAbsState.φ_in, hci_at.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.1]
  have hPre : (pathDSDataStructure pdsImpl.params w).pre 0 (states ci)
      [mem (handlesAddr + ci), b, hCur] mem := by
    refine ⟨mem (handlesAddr + ci), b, hCur, rfl, hci_at.2.2.2.2.2.2.2.2, ?_, hb_ndel, ?_⟩
    · rwa [hG_eq]
    · rw [hG_eq, hci_at.2.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.2.1, hφin_eq]; exact hcw
  have hsp : (pathDSDataStructure pdsImpl.params w).space 0 (states ci)
      [mem (handlesAddr + ci), b, hCur] mem =
      pdsImpl.params.delSpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M := by
    simp [pathDSDataStructure, hG_eq, hci_at.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.2.1]
  have hcost : (pathDSDataStructure pdsImpl.params w).cost 0 (states ci)
      [mem (handlesAddr + ci), b, hCur] mem =
      ⌈pdsImpl.params.K_del * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, hφin_eq, hci_at.2.2.2.2.2.2.2.1]
  have hlast : WordRAM.heapArg [mem (handlesAddr + ci), b, hCur] = hCur := rfl
  obtain ⟨body, hp, o, st', c, hr, s', x', hrep', hpost', hresp', hcost_le⟩ :=
    hSpec.2.2 0 (mem (handlesAddr + ci)) (states ci) (reps ci)
      [mem (handlesAddr + ci), b, hCur] mem pos ω hArgs_w rfl hci_at.2.2.1 hPre
      (fun a ha => (hci_at.2.2.2.1 a ha).2) hArr.zero_from
      (by simpa [hlast, hsp] using hSpace_w)
  rcases hresp' with ⟨hge', hle', hz', hpres', hfoot'⟩
  rw [hlast] at hge' hle' hpres' hfoot'
  rw [hsp] at hle'
  rcases hpost' with ⟨b', e', h', heq_a, hs'φn, hs'φd, hs'M, hs'G, hs'del, hs'Vh_sub, hs'Val, L, hSeq, hLnd, hLVh⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨rfl, rfl, rfl⟩
  have h_below : ∀ a < dsBaseAddr, st'.mem a = mem a := fun a ha =>
    hpres' a (lt_of_lt_of_le ha hArr.h_ge) fun hfa => absurd (hci_at.2.2.2.1 a hfa).1 (not_le_of_gt ha)
  have h_other_foot : ∀ ci' < upTo, ci' ≠ ci → ∀ a,
      pdsImpl.R.foot (mem (handlesAddr + ci')) (reps ci') a → st'.mem a = mem a := by
    intro ci' hci' hne a ha
    have hbounds := (hArr.at_ci ci' hci').2.2.2.1 a ha
    exact hpres' a hbounds.2 (hArr.disjoint ci' hci' ci hci hne a ha)
  let states' := Function.update states ci s'
  let reps' := Function.update reps ci x'
  have hArr' : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
      states' reps' := by
    refine ⟨le_trans hArr.h_ge hge', hz', fun k hk => ?_, fun c1 h1 c2 h2 hne a ha => ?_⟩
    · have hk_lt_cur : handlesAddr + k < dsBaseAddr := by omega
      rw [h_below _ hk_lt_cur]
      by_cases hkc : k = ci
      · subst hkc
        simp only [states', reps', Function.update_self]
        refine ⟨hci_at.1, le_trans hci_at.2.1 hge', hrep', fun a ha => ?_, ?_, ?_, ?_, ?_, hs'Val⟩
        · rcases hfoot' a ha with hold | ⟨hle_a, hlt_a⟩
          · exact ⟨(hci_at.2.2.2.1 a hold).1, lt_of_lt_of_le (hci_at.2.2.2.1 a hold).2 hge'⟩
          · exact ⟨le_trans hArr.h_ge hle_a, hlt_a⟩
        · rw [hs'G]; exact hci_at.2.2.2.2.1
        · rw [hs'φn]; exact hci_at.2.2.2.2.2.1
        · rw [hs'φd]; exact hci_at.2.2.2.2.2.2.1
        · rw [hs'M]; exact hci_at.2.2.2.2.2.2.2.1
      · have hold := hArr.at_ci k hk
        have hloc := hSpec.1 (mem (handlesAddr + k)) (states k) (reps k) mem st'.mem
          fun a ha => (h_other_foot k hk hkc a ha).symm
        simp only [states', reps', Function.update_of_ne hkc]
        exact ⟨hold.1, le_trans hold.2.1 hge', hloc.1 hold.2.2.1,
          fun a ha => ⟨(hold.2.2.2.1 a ha).1, lt_of_lt_of_le (hold.2.2.2.1 a ha).2 hge'⟩, hold.2.2.2.2⟩
    · have h1_lt : handlesAddr + c1 < dsBaseAddr := by omega
      have h2_lt : handlesAddr + c2 < dsBaseAddr := by omega
      rw [h_below _ h1_lt] at ha
      rw [h_below _ h2_lt]
      by_cases hc1 : c1 = ci
      · subst hc1
        simp only [reps', Function.update_self, Function.update_of_ne hne.symm] at ha ⊢
        intro h2_f
        have h2_b := ((hArr.at_ci c2 h2).2.2.2.1 a h2_f).2
        rcases hfoot' a ha with hold | ⟨hle_a, _⟩
        · exact hArr.disjoint c1 h1 c2 h2 hne a hold h2_f
        · omega
      · by_cases hc2 : c2 = ci
        · subst hc2
          simp only [reps', Function.update_self, Function.update_of_ne hc1] at ha ⊢
          intro h2_f
          have h1_b := ((hArr.at_ci c1 h1).2.2.2.1 a ha).2
          rcases hfoot' a h2_f with hold | ⟨hle_a, _⟩
          · exact hArr.disjoint c1 h1 c2 h2 hc1 a ha hold
          · omega
        · simp only [reps', Function.update_of_ne hc1, Function.update_of_ne hc2] at ha ⊢
          exact hArr.disjoint c1 h1 c2 h2 hne a ha
  refine ⟨body, o, st', c, s', x', L, hp, hr, hge', hle', h_below, hs'G,
    hs'φn.trans hci_at.2.2.2.2.2.1, hs'φd.trans hci_at.2.2.2.2.2.2.1, hs'M.trans hci_at.2.2.2.2.2.2.2.1,
    hs'del, hs'Vh_sub, hSeq, hLnd, hLVh, hArr', ?_⟩
  have hsum_diff : dsTotalPhi pdsImpl handlesAddr upTo reps' st'.mem +
      pdsImpl.R.phi (mem (handlesAddr + ci)) (reps ci) mem =
      dsTotalPhi pdsImpl handlesAddr upTo reps mem +
        pdsImpl.R.phi (mem (handlesAddr + ci)) x' st'.mem := by
    unfold dsTotalPhi
    have hmem_ci : ci ∈ Finset.range upTo := Finset.mem_range.mpr hci
    rw [← Finset.add_sum_erase (Finset.range upTo) _ hmem_ci,
        ← Finset.add_sum_erase (Finset.range upTo) _ hmem_ci]
    have hcongr : ∑ k ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (st'.mem (handlesAddr + k)) (reps' k) st'.mem =
        ∑ k ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (mem (handlesAddr + k)) (reps k) mem := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_r := Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
      have hne := Finset.ne_of_mem_erase hk
      simp only [reps', Function.update_of_ne hne]
      rw [h_below (handlesAddr + k) (by omega)]
      exact (hSpec.1 (mem (handlesAddr + k)) (states k) (reps k) mem st'.mem
        fun a ha => (h_other_foot k hk_r hne a ha).symm).2.symm
    rw [hcongr, h_below (handlesAddr + ci) (by omega)]
    simp only [reps', Function.update_self]
    omega
  dsimp only [reps'] at hsum_diff
  rw [hcost] at hcost_le
  omega

lemma DSArrayAt.call_getPath {p : Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase ci u v : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hci : ci < upTo) (hup : upTo ≤ comps.length)
    (hHdl_lt : handlesAddr + upTo ≤ dsBaseAddr)
    (hu : u ∈ (states ci).G.verts \ (states ci).Vhat)
    (hv : v ∈ (states ci).G.verts \ (states ci).Vhat)
    (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w)
    (hh_w : hCur < 2 ^ w)
    (hcw : pdsImpl.params.cw * (Nat.log 2 (comps[ci].J_sub.n + comps[ci].J_sub.m + phiDen + M +
      ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.querySpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M < 2 ^ w) :
    ∃ body o st' c x' P,
      p.procs[dsBase + 2]? = some body ∧
      Runs w p ω body (startState [mem (handlesAddr + ci), u, v, hCur] mem pos) o st' c ∧
      hCur ≤ o.value ∧
      o.value ≤ hCur + pdsImpl.params.querySpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M ∧
      (∀ a < dsBaseAddr, st'.mem a = mem a) ∧
      WalkAt st'.mem hCur P ∧ Walk.IsWalk comps[ci].J_sub u v P ∧ P.verts.Nodup ∧
      (∀ e ∈ P.edges, e ∉ (states ci).deleted) ∧ (∀ y ∈ P.verts, y ∉ (states ci).Vhat) ∧
      ↑P.edges.length ≤ pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M ∧
      DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
        states (Function.update reps ci x') ∧
      c + dsTotalPhi pdsImpl handlesAddr upTo (Function.update reps ci x') st'.mem ≤
        ⌈pdsImpl.params.K_query * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ +
          dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  have hci_at := hArr.at_ci ci hci
  have hci_c : ci < comps.length := lt_of_lt_of_le hci hup
  have hG_eq : (states ci).G = comps[ci].J_sub := by
    rw [hci_at.2.2.2.2.1, List.getD_eq_getElem _ _ hci_c]
  have hhdl_w : mem (handlesAddr + ci) < 2 ^ w := lt_of_le_of_lt hci_at.2.1 hh_w
  have hArgs_w : ∀ a ∈ [mem (handlesAddr + ci), u, v, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hφin_eq : (states ci).φ_in = (↑phiNum / ↑phiDen : ℝ) := by
    simp [PathDSAbsState.φ_in, hci_at.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.1]
  have hPre : (pathDSDataStructure pdsImpl.params w).pre 1 (states ci)
      [mem (handlesAddr + ci), u, v, hCur] mem := by
    refine ⟨mem (handlesAddr + ci), u, v, hCur, rfl, hci_at.2.2.2.2.2.2.2.2, hu, hv, ?_⟩
    rw [hG_eq, hci_at.2.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.2.1, hφin_eq]; exact hcw
  have hsp : (pathDSDataStructure pdsImpl.params w).space 1 (states ci)
      [mem (handlesAddr + ci), u, v, hCur] mem =
      pdsImpl.params.querySpace phiNum phiDen comps[ci].J_sub.n comps[ci].J_sub.m M := by
    simp [pathDSDataStructure, hG_eq, hci_at.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.1, hci_at.2.2.2.2.2.2.2.1]
  have hcost : (pathDSDataStructure pdsImpl.params w).cost 1 (states ci)
      [mem (handlesAddr + ci), u, v, hCur] mem =
      ⌈pdsImpl.params.K_query * pdsImpl.params.γ_query (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, hφin_eq, hci_at.2.2.2.2.2.2.2.1]
  have hlast : WordRAM.heapArg [mem (handlesAddr + ci), u, v, hCur] = hCur := rfl
  obtain ⟨body, hp, o, st', c, hr, s', x', hrep', hpost', hresp', hcost_le⟩ :=
    hSpec.2.2 1 (mem (handlesAddr + ci)) (states ci) (reps ci)
      [mem (handlesAddr + ci), u, v, hCur] mem pos ω hArgs_w rfl hci_at.2.2.1 hPre
      (fun a ha => (hci_at.2.2.2.1 a ha).2) hArr.zero_from
      (by simpa [hlast, hsp] using hSpace_w)
  rcases hresp' with ⟨hge', hle', hz', hpres', hfoot'⟩
  rw [hlast] at hge' hle' hpres' hfoot'
  rw [hsp] at hle'
  rcases hpost' with ⟨b', u', v', h', heq_a, heq_s, P, hWP, hPW, hPnd, hPed, hPVh, hPlen⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨rfl, rfl, rfl, rfl⟩
  subst heq_s
  have h_below : ∀ a < dsBaseAddr, st'.mem a = mem a := fun a ha =>
    hpres' a (lt_of_lt_of_le ha hArr.h_ge) fun hfa => absurd (hci_at.2.2.2.1 a hfa).1 (not_le_of_gt ha)
  have h_other_foot : ∀ ci' < upTo, ci' ≠ ci → ∀ a,
      pdsImpl.R.foot (mem (handlesAddr + ci')) (reps ci') a → st'.mem a = mem a := by
    intro ci' hci' hne a ha
    have hbounds := (hArr.at_ci ci' hci').2.2.2.1 a ha
    exact hpres' a hbounds.2 (hArr.disjoint ci' hci' ci hci hne a ha)
  let reps' := Function.update reps ci x'
  have hArr' : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value st'.mem upTo
      states reps' := by
    refine ⟨le_trans hArr.h_ge hge', hz', fun k hk => ?_, fun c1 h1 c2 h2 hne a ha => ?_⟩
    · have hk_lt_cur : handlesAddr + k < dsBaseAddr := by omega
      rw [h_below _ hk_lt_cur]
      by_cases hkc : k = ci
      · subst hkc
        simp only [reps', Function.update_self]
        refine ⟨hci_at.1, le_trans hci_at.2.1 hge', hrep', fun a ha => ?_, hci_at.2.2.2.2⟩
        rcases hfoot' a ha with hold | ⟨hle_a, hlt_a⟩
        · exact ⟨(hci_at.2.2.2.1 a hold).1, lt_of_lt_of_le (hci_at.2.2.2.1 a hold).2 hge'⟩
        · exact ⟨le_trans hArr.h_ge hle_a, hlt_a⟩
      · have hold := hArr.at_ci k hk
        have hloc := hSpec.1 (mem (handlesAddr + k)) (states k) (reps k) mem st'.mem
          fun a ha => (h_other_foot k hk hkc a ha).symm
        simp only [reps', Function.update_of_ne hkc]
        exact ⟨hold.1, le_trans hold.2.1 hge', hloc.1 hold.2.2.1,
          fun a ha => ⟨(hold.2.2.2.1 a ha).1, lt_of_lt_of_le (hold.2.2.2.1 a ha).2 hge'⟩, hold.2.2.2.2⟩
    · have h1_lt : handlesAddr + c1 < dsBaseAddr := by omega
      have h2_lt : handlesAddr + c2 < dsBaseAddr := by omega
      rw [h_below _ h1_lt] at ha
      rw [h_below _ h2_lt]
      by_cases hc1 : c1 = ci
      · subst hc1
        simp only [reps', Function.update_self, Function.update_of_ne hne.symm] at ha ⊢
        intro h2_f
        have h2_b := ((hArr.at_ci c2 h2).2.2.2.1 a h2_f).2
        rcases hfoot' a ha with hold | ⟨hle_a, _⟩
        · exact hArr.disjoint c1 h1 c2 h2 hne a hold h2_f
        · omega
      · by_cases hc2 : c2 = ci
        · subst hc2
          simp only [reps', Function.update_self, Function.update_of_ne hc1] at ha ⊢
          intro h2_f
          have h1_b := ((hArr.at_ci c1 h1).2.2.2.1 a ha).2
          rcases hfoot' a h2_f with hold | ⟨hle_a, _⟩
          · exact hArr.disjoint c1 h1 c2 h2 hc1 a ha hold
          · omega
        · simp only [reps', Function.update_of_ne hc1, Function.update_of_ne hc2] at ha ⊢
          exact hArr.disjoint c1 h1 c2 h2 hne a ha
  have hPlen' : (P.edges.length : ℝ) ≤ pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M := by
    rwa [← hφin_eq, ← hci_at.2.2.2.2.2.2.2.1]
  refine ⟨body, o, st', c, x', P, hp, hr, hge', hle', h_below, hWP, hG_eq ▸ hPW, hPnd, hPed, hPVh,
    hPlen', hArr', ?_⟩
  have hsum_diff : dsTotalPhi pdsImpl handlesAddr upTo reps' st'.mem +
      pdsImpl.R.phi (mem (handlesAddr + ci)) (reps ci) mem =
      dsTotalPhi pdsImpl handlesAddr upTo reps mem +
        pdsImpl.R.phi (mem (handlesAddr + ci)) x' st'.mem := by
    unfold dsTotalPhi
    have hmem_ci : ci ∈ Finset.range upTo := Finset.mem_range.mpr hci
    rw [← Finset.add_sum_erase (Finset.range upTo) _ hmem_ci,
        ← Finset.add_sum_erase (Finset.range upTo) _ hmem_ci]
    have hcongr : ∑ k ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (st'.mem (handlesAddr + k)) (reps' k) st'.mem =
        ∑ k ∈ (Finset.range upTo).erase ci, pdsImpl.R.phi (mem (handlesAddr + k)) (reps k) mem := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_r := Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
      have hne := Finset.ne_of_mem_erase hk
      simp only [reps', Function.update_of_ne hne]
      rw [h_below (handlesAddr + k) (by omega)]
      exact (hSpec.1 (mem (handlesAddr + k)) (states k) (reps k) mem st'.mem
        fun a ha => (h_other_foot k hk_r hne a ha).symm).2.symm
    rw [hcongr, h_below (handlesAddr + ci) (by omega)]
    simp only [reps', Function.update_self]
    omega
  dsimp only [reps'] at hsum_diff
  rw [hcost] at hcost_le
  omega

/-- Generic round-level potential combining DS potentials with remaining un-deleted edges,
un-isolated `Vhat` vertices, and un-drained incidence chain nodes. -/
noncomputable def t2RoundPhi (pdsImpl : PathDSImpl)
    (kDelPlusHdr kVhatStep kNodeStep handlesAddr upTo undelRem vhatRem nodeRem : ℕ)
    (reps : ℕ → pdsImpl.R.τ) (mem : ℕ → ℕ) : ℕ :=
  dsTotalPhi pdsImpl handlesAddr upTo reps mem +
    undelRem * kDelPlusHdr + vhatRem * kVhatStep + nodeRem * kNodeStep

end MinCostFlow.Spanner
