module

public import MinCostFlow.SparseCore.Program.CompBatchDispatch
public import MinCostFlow.SparseCore.Program.CompForestLift
public import MinCostFlow.SparseCore.Program.CompTrack

/-!
# Shared Step Helpers for Batch Updates (`CompBatchStepCommon`)

Provides:
1. Direct call wrappers around `compMarkTouch_meetsContract`, `ghostCons_meetsContract`,
   `ghostErase_meetsContract`, and `ghostAppend_meetsContract` (`CompGhostOps`).
2. Root-buffer capacity bound (`compRootCap_le_vCap`), lifting of per-component cut logs to the
   global `CompLSFState.RF` (`compForestCutsValid_comp_to_global`), and single-dispatch cost
   absorption (`compSingleDispatch_cost_le`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Helper-contract call wrappers -/

/-- Direct call wrapper for `compMarkTouchProc`. -/
lemma compMarkTouch_call {w cap bMark markBase listBase cntAddr c : ℕ} {L : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs[bMark]? = some compMarkTouchProc)
    (hw16 : 16 ≤ 2 ^ w) (hc : c < cap) (hm_w : markBase + cap < 2 ^ w)
    (hcnt_w : cntAddr < 2 ^ w) (hl_w : listBase + L.length + 1 < 2 ^ w)
    (h1 : cntAddr ≠ markBase + c) (h2 : listBase + L.length ≠ markBase + c)
    (h3 : listBase + L.length ≠ cntAddr)
    (h4 : ∀ i < L.length, listBase + i ≠ markBase + c ∧ listBase + i ≠ cntAddr)
    (hcnt : mem cntAddr = L.length) (hLA : ListAt mem listBase L)
    (hmk : mem (markBase + c) = 0 ∨ mem (markBase + c) = 1) :
    let L' := if mem (markBase + c) = 0 then L ++ [c] else L
    ∃ o st' cost,
      Runs w p ω compMarkTouchProc (startState [markBase, listBase, cntAddr, c] mem pos) o st' cost ∧
      o.value = 0 ∧
      st'.mem (markBase + c) = 1 ∧
      st'.mem cntAddr = L'.length ∧
      ListAt st'.mem listBase L' ∧
      (∀ a, a ≠ markBase + c → a ≠ cntAddr → a ≠ listBase + L.length → st'.mem a = mem a) ∧
      cost ≤ 60 := by
  intro L'
  obtain ⟨body, hbody, o, st', cost, hrun, ⟨m', l', ca', c', harg, hval, h1', h2', h3', hfr⟩, hcost⟩ :=
    compMarkTouch_meetsContract (cap := cap) (L := L) hp [markBase, listBase, cntAddr, c] mem pos ω
      (by simp; omega)
      ⟨markBase, listBase, cntAddr, c, rfl, hw16, hc, hm_w, hcnt_w, hl_w, h1, h2, h3, h4, hcnt, hLA, hmk⟩
  have hb : body = compMarkTouchProc := Option.some.inj (hbody.symm.trans hp)
  have ⟨hm, hl, hca, hc'⟩ : m' = markBase ∧ l' = listBase ∧ ca' = cntAddr ∧ c' = c := by
    simpa [eq_comm] using harg
  rw [hb] at hrun; simp only [hm, hl, hca, hc'] at h1' h2' h3' hfr
  exact ⟨o, st', cost, hrun, hval, h1', h2', h3', hfr, by simpa [compMarkTouchContract] using hcost⟩

/-- Direct call wrapper for `ghostConsProc`. -/
lemma ghostCons_call {w cap bCons headAddr prevBase nextBase cntAddr e : ℕ} {L : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs[bCons]? = some ghostConsProc)
    (hw16 : 16 ≤ 2 ^ w) (he : e < cap) (hne : e ∉ L)
    (hh_w : headAddr < 2 ^ w) (hc_w : cntAddr < 2 ^ w)
    (hp_w : prevBase + cap < 2 ^ w) (hn_w : nextBase + cap < 2 ^ w)
    (hcap_w : cap + 1 < 2 ^ w) (hl_w : L.length + 1 < 2 ^ w)
    (h1 : headAddr ≠ cntAddr)
    (h2 : ∀ x < cap, prevBase + x ≠ headAddr ∧ prevBase + x ≠ cntAddr)
    (h3 : ∀ x < cap, nextBase + x ≠ headAddr ∧ nextBase + x ≠ cntAddr)
    (h4 : ∀ x < cap, ∀ y < cap, prevBase + x ≠ nextBase + y)
    (hdll : IsDoublyLinkedList mem prevBase nextBase headAddr cap L)
    (hcnt : mem cntAddr = L.length) :
    ∃ o st' cost,
      Runs w p ω ghostConsProc (startState [headAddr, prevBase, nextBase, cntAddr, e] mem pos) o st' cost ∧
      o.value = 0 ∧
      IsDoublyLinkedList st'.mem prevBase nextBase headAddr cap (e :: L) ∧
      st'.mem cntAddr = L.length + 1 ∧
      (∀ a, a ≠ headAddr → a ≠ cntAddr → a ≠ prevBase + e → a ≠ nextBase + e →
        (∀ h₀ xs, L = h₀ :: xs → a ≠ prevBase + h₀) → st'.mem a = mem a) ∧
      cost ≤ 70 := by
  obtain ⟨body, hbody, o, st', cost, hrun, ⟨h', p', n', c', e', harg, hval, hdll', hcnt', hfr⟩, hcost⟩ :=
    ghostCons_meetsContract (cap := cap) (L := L) hp [headAddr, prevBase, nextBase, cntAddr, e] mem pos ω
      (by simp; omega)
      ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, hw16, he, hne, hh_w, hc_w, hp_w, hn_w,
        hcap_w, hl_w, h1, h2, h3, h4, hdll, hcnt⟩
  have hb : body = ghostConsProc := Option.some.inj (hbody.symm.trans hp)
  have ⟨hh, hp', hn, hc, he'⟩ : h' = headAddr ∧ p' = prevBase ∧ n' = nextBase ∧ c' = cntAddr ∧ e' = e := by
    simpa [eq_comm] using harg
  rw [hb] at hrun; simp only [hh, hp', hn, hc, he'] at hdll' hcnt' hfr
  exact ⟨o, st', cost, hrun, hval, hdll', hcnt', hfr, by simpa [ghostConsContract] using hcost⟩

/-- Direct call wrapper for `ghostEraseProc`. -/
lemma ghostErase_call {w cap bErase headAddr prevBase nextBase cntAddr e : ℕ} {L : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs[bErase]? = some ghostEraseProc)
    (hw16 : 16 ≤ 2 ^ w) (he : e < cap) (hmem : e ∈ L)
    (hh_w : headAddr < 2 ^ w) (hc_w : cntAddr < 2 ^ w)
    (hp_w : prevBase + cap < 2 ^ w) (hn_w : nextBase + cap < 2 ^ w)
    (hcap_w : cap + 1 < 2 ^ w) (hl_w : L.length < 2 ^ w)
    (h1 : headAddr ≠ cntAddr)
    (h2 : ∀ x < cap, prevBase + x ≠ headAddr ∧ prevBase + x ≠ cntAddr)
    (h3 : ∀ x < cap, nextBase + x ≠ headAddr ∧ nextBase + x ≠ cntAddr)
    (h4 : ∀ x < cap, ∀ y < cap, prevBase + x ≠ nextBase + y)
    (hdll : IsDoublyLinkedList mem prevBase nextBase headAddr cap L)
    (hcnt : mem cntAddr = L.length) :
    ∃ o st' cost,
      Runs w p ω ghostEraseProc (startState [headAddr, prevBase, nextBase, cntAddr, e] mem pos) o st' cost ∧
      o.value = 0 ∧
      IsDoublyLinkedList st'.mem prevBase nextBase headAddr cap (L.erase e) ∧
      st'.mem cntAddr = L.length - 1 ∧
      (∀ a, a ≠ headAddr → a ≠ cntAddr →
        (∀ x ∈ L, a ≠ prevBase + x ∧ a ≠ nextBase + x) → st'.mem a = mem a) ∧
      cost ≤ 90 := by
  obtain ⟨body, hbody, o, st', cost, hrun, ⟨h', p', n', c', e', harg, hval, hdll', hcnt', hfr⟩, hcost⟩ :=
    ghostErase_meetsContract (cap := cap) (L := L) hp [headAddr, prevBase, nextBase, cntAddr, e] mem pos ω
      (by simp; omega)
      ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, hw16, he, hmem, hh_w, hc_w, hp_w, hn_w,
        hcap_w, hl_w, h1, h2, h3, h4, hdll, hcnt⟩
  have hb : body = ghostEraseProc := Option.some.inj (hbody.symm.trans hp)
  have ⟨hh, hp', hn, hc, he'⟩ : h' = headAddr ∧ p' = prevBase ∧ n' = nextBase ∧ c' = cntAddr ∧ e' = e := by
    simpa [eq_comm] using harg
  rw [hb] at hrun; simp only [hh, hp', hn, hc, he'] at hdll' hcnt' hfr
  exact ⟨o, st', cost, hrun, hval, hdll', hcnt', hfr, by simpa [ghostEraseContract] using hcost⟩

/-- Direct call wrapper for `ghostAppendProc`. -/
lemma ghostAppend_call {w cap bApp headAddr prevBase nextBase outPtr : ℕ} {L : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs[bApp]? = some ghostAppendProc)
    (hw16 : 16 ≤ 2 ^ w) (hh_w : headAddr < 2 ^ w) (hn_w : nextBase + cap < 2 ^ w)
    (ho_w : outPtr + L.length < 2 ^ w) (hcap_w : cap + 1 < 2 ^ w)
    (hdisj : ∀ i < L.length, outPtr + i ≠ headAddr ∧ ∀ x < cap, outPtr + i ≠ nextBase + x)
    (hdll : IsDoublyLinkedList mem prevBase nextBase headAddr cap L) :
    ∃ o st' cost,
      Runs w p ω ghostAppendProc (startState [headAddr, nextBase, outPtr] mem pos) o st' cost ∧
      o.value = L.length ∧
      ListAt st'.mem outPtr L ∧
      (∀ a, a < outPtr ∨ outPtr + L.length ≤ a → st'.mem a = mem a) ∧
      cost ≤ 40 * L.length + 25 := by
  obtain ⟨body, hbody, o, st', cost, hrun, ⟨h', n', o', harg, hval, hLA, hfr⟩, hcost⟩ :=
    ghostAppend_meetsContract (cap := cap) (L := L) hp [headAddr, nextBase, outPtr] mem pos ω
      (by simp; omega)
      ⟨headAddr, nextBase, outPtr, prevBase, rfl, hw16, hh_w, hn_w, ho_w, hcap_w, hdisj, hdll⟩
  have hb : body = ghostAppendProc := Option.some.inj (hbody.symm.trans hp)
  have ⟨hh, hn, ho⟩ : h' = headAddr ∧ n' = nextBase ∧ o' = outPtr := by simpa [eq_comm] using harg
  rw [hb] at hrun; rw [ho] at hLA hfr
  exact ⟨o, st', cost, hrun, hval, hLA, hfr, by simpa [ghostAppendContract] using hcost⟩

/-! ## 2. Global root-capacity bound and per-component forest-cut lifting -/

/-- Any single-component update's newly closed `R_orig` vertices are disjoint from `cs.RF.R` and
lie in `Finset.range vCap`, so `cnt + (S_c'.R_orig \ S_c.R_orig).card ≤ vCap` whenever
`cnt ≤ cs.RF.R.card`. -/
lemma compRootCap_le_vCap {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap cnt : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (hcnt : cnt ≤ cs.RF.R.card) (c : Fin numComps) (u_c : Update) :
    let Sc := cs.compSt (compOf c)
    cnt + ((applyLSFUpdate Sc u_c).R_orig \ Sc.R_orig).card ≤ vCap := by
  classical
  intro Sc
  have hCmem : compOf c ∈ components cs.G₀ := hT.compOf_mem c
  have hInvC : LSFStructInv Sc := LSFInvWith.toStructInv (hI.hCompLSF _ hCmem).1
  have hRF_sub_V : cs.RF.R ⊆ cs.G.V := (compLSF_RF_isRSF hI).2.2.1
  have hR_sub_range : cs.RF.R ⊆ Finset.range vCap := fun r hr =>
    Finset.mem_range.mpr (hT.hVlt r (hRF_sub_V hr))
  have hNew_sub_T0 : (applyLSFUpdate Sc u_c).R_orig \ Sc.R_orig ⊆ Sc.T₀.V := by
    intro r hr
    have hr1 := (Finset.mem_sdiff.mp hr).1
    have hT0_eq : (applyLSFUpdate Sc u_c).T₀ = Sc.T₀ := by cases u_c <;> rfl
    have hr0_eq : (applyLSFUpdate Sc u_c).r₀ = Sc.r₀ := by cases u_c <;> rfl
    have hR0_sub : (applyLSFUpdate Sc u_c).R₀_base ⊆ Sc.T₀.V := by
      cases u_c with
      | insert _ a b =>
        intro z hz; simp only [applyLSFUpdate, Finset.mem_union, Finset.mem_filter] at hz
        exact hz.elim (fun h => hInvC.hR₀_sub h) (fun h => h.2)
      | delete _ =>
        intro z hz; simp only [applyLSFUpdate, Finset.mem_union, Finset.mem_filter] at hz
        exact hz.elim (fun h => hInvC.hR₀_sub h) (fun h => h.2)
      | split v _ _ _ =>
        intro z hz; dsimp only [applyLSFUpdate] at hz
        split_ifs at hz with hv
        · rcases Finset.mem_insert.mp hz with rfl | h
          · exact hv
          · exact hInvC.hR₀_sub h
        · exact hInvC.hR₀_sub hz
    have hr' : r ∈ upClosure (hldAuxTree Sc.T₀ Sc.r₀) Sc.r₀ (applyLSFUpdate Sc u_c).R₀_base := by
      dsimp only [LSFState.R_orig, LSFState.TH] at hr1; rwa [hT0_eq, hr0_eq] at hr1
    exact upClosure_subset (hldAuxTree_isRootedTree hInvC.hT₀) hR0_sub hr'
  have hNew_sub_range : (applyLSFUpdate Sc u_c).R_orig \ Sc.R_orig ⊆ Finset.range vCap := fun r hr =>
    Finset.mem_range.mpr (hT.hVlt r (hI.hV_eq ▸ Finset.mem_biUnion.mpr
      ⟨compOf c, hCmem, hInvC.hGV_eq ▸ Finset.mem_union_left _ (hNew_sub_T0 hr)⟩))
  have hDisj : Disjoint cs.RF.R ((applyLSFUpdate Sc u_c).R_orig \ Sc.R_orig) := by
    rw [Finset.disjoint_left]
    intro r hrR hrN
    have hrT0 : r ∈ Sc.T₀.V := hNew_sub_T0 hrN
    have hrV_c : r ∈ Sc.G.V := hInvC.hGV_eq ▸ Finset.mem_union_left _ hrT0
    change r ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).R) at hrR
    obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hrR
    have hInvD : LSFStructInv (cs.compSt D) := LSFInvWith.toStructInv (hI.hCompLSF D hD).1
    have hrV_D : r ∈ (cs.compSt D).G.V := by
      rcases Finset.mem_union.mp hrD with h1 | h2
      · exact hInvD.hGV_eq ▸ Finset.mem_union_left _
          (upClosure_subset (hldAuxTree_isRootedTree hInvD.hT₀) hInvD.hR₀_sub h1)
      · exact hInvD.hGV_eq ▸ Finset.mem_union_right _ h2
    have hDC : D = compOf c := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c) hCmem hne) hrV_D hrV_c
    subst hDC
    rcases Finset.mem_union.mp hrD with h1 | h2
    · exact (Finset.mem_sdiff.mp hrN).2 h1
    · exact Finset.disjoint_left.mp hInvC.hdisj_iso hrT0 h2
  have hun : cs.RF.R ∪ ((applyLSFUpdate Sc u_c).R_orig \ Sc.R_orig) ⊆ Finset.range vCap :=
    Finset.union_subset hR_sub_range hNew_sub_range
  have hcard := Finset.card_le_card hun
  rw [Finset.card_union_of_disjoint hDisj, Finset.card_range] at hcard
  omega

/-- Lift a valid cut sequence on one component `(cs.compSt (compOf c)).RF` to the global
`RootedForest` `cs.RF`. -/
lemma compForestCutsValid_comp_to_global {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (c : Fin numComps) {cuts : List (ℕ × ℕ)}
    (hvalid : CompForestCutsValid vCap (cs.compSt (compOf c)).RF cuts) :
    CompForestCutsValid vCap cs.RF cuts := by
  classical
  have hCmem : compOf c ∈ components cs.G₀ := hT.compOf_mem c
  have hInvC : LSFStructInv (cs.compSt (compOf c)) := LSFInvWith.toStructInv (hI.hCompLSF _ hCmem).1
  have hsub := compLSF_RF_sub_comp hI hCmem
  have hV_c : (cs.compSt (compOf c)).RF.F.V = (cs.compSt (compOf c)).G.V := hInvC.hT_cur_V
  have hRsub : (cs.compSt (compOf c)).RF.R ⊆ cs.RF.R := fun r hr =>
    Finset.mem_biUnion.mpr ⟨compOf c, hCmem, hr⟩
  have hRpart : ∀ r ∈ cs.RF.R, r ∈ (cs.compSt (compOf c)).RF.F.V → r ∈ (cs.compSt (compOf c)).RF.R := by
    intro r hr hrV
    rw [hV_c] at hrV
    obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hr
    have hInvD := LSFInvWith.toStructInv (hI.hCompLSF D hD).1
    have hrVD : r ∈ (cs.compSt D).G.V := by
      rcases Finset.mem_union.mp hrD with h1 | h2
      · exact hInvD.hGV_eq ▸ Finset.mem_union_left _
          (upClosure_subset (hldAuxTree_isRootedTree hInvD.hT₀) hInvD.hR₀_sub h1)
      · exact hInvD.hGV_eq ▸ Finset.mem_union_right _ h2
    have hDC : D = compOf c := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c) hCmem hne) hrVD hrV
    exact hDC ▸ hrD
  have hF1_val : (cs.compSt (compOf c)).RF.F.IsValid := (lsfInv_to_RS (hI.hCompLSF _ hCmem).1).1.1
  have hsep : ∀ e ∈ cs.RF.F.E, e ∉ (cs.compSt (compOf c)).RF.F.E →
      cs.RF.F.tail e ∉ (cs.compSt (compOf c)).RF.F.V ∧
      cs.RF.F.head e ∉ (cs.compSt (compOf c)).RF.F.V := by
    intro e he henot
    obtain ⟨D, hD, heD⟩ := Finset.mem_biUnion.mp he
    have hDC : D ≠ compOf c := fun h => henot (h ▸ heD)
    have hsubD := compLSF_RF_sub_comp hI hD
    have hRS_D := lsfInv_to_RS (hI.hCompLSF D hD).1
    have h1 := hRS_D.1.1 e heD
    rw [hRS_D.2.1] at h1
    rw [hV_c, ← (hsubD.2.2 e heD).1, ← (hsubD.2.2 e heD).2]
    exact ⟨fun ht => Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c) hCmem hDC) h1.1 ht,
      fun hh => Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c) hCmem hDC) h1.2 hh⟩
  have huniq_out : ∀ v ∈ cs.RF.F.V, v ∉ (cs.compSt (compOf c)).RF.F.V →
      ∃! rt, rt ∈ cs.RF.R ∧ cs.RF.F.Connected v rt := fun v hv _ =>
    (compLSF_RF_isRSF hI).2.2.2.1 v hv
  exact compForestCutsValid_part_to_global cuts cs.RF (cs.compSt (compOf c)).RF
    hsub.1 hsub.2.1 hRsub hRpart hsub.2.2
    hF1_val hsep huniq_out hvalid

/-- Congruence of `CompForestCutsValid` for rooted forests agreeing on `F.V`, `F.E`, `R`, and
`F.tail`/`F.head` on `F.E`. -/
lemma compForestCutsValid_congr {vCap : ℕ} :
    ∀ {cuts : List (ℕ × ℕ)} {RF₁ RF₂ : RootedForest},
      RF₁.F.V = RF₂.F.V → RF₁.F.E = RF₂.F.E → RF₁.R = RF₂.R →
      (∀ e ∈ RF₁.F.E, RF₁.F.tail e = RF₂.F.tail e ∧ RF₁.F.head e = RF₂.F.head e) →
      CompForestCutsValid vCap RF₁ cuts → CompForestCutsValid vCap RF₂ cuts
  | [], _, _, _, _, _, _, _ => trivial
  | (e, r) :: rest, RF₁, RF₂, hV, hE, hR, hends, ⟨he, hrCap, hrV, hrNotR, huniq, hrest⟩ => by
    have hwalk : ∀ {G₁ G₂ : MGraph}, G₁.E = G₂.E →
        (∀ f ∈ G₁.E, G₁.tail f = G₂.tail f ∧ G₁.head f = G₂.head f) →
        ∀ {a b : ℕ} {P : List (ℕ × Bool)}, G₁.IsWalk a b P → G₂.IsWalk a b P := by
      intro G₁ G₂ hGE hGends a b P hW
      induction hW with
      | nil x => exact .nil x
      | @cons x y z tl hzE hsrc _ ih =>
        rcases z with ⟨f, dir⟩
        have hsrc2 : G₂.src (f, dir) = x := by
          cases dir <;> simp [MGraph.src] at hsrc ⊢
          · rw [← (hGends f hzE).2]; exact hsrc
          · rw [← (hGends f hzE).1]; exact hsrc
        have hdst2 : G₂.dst (f, dir) = G₁.dst (f, dir) := by
          cases dir <;> simp [MGraph.dst, (hGends f hzE).1, (hGends f hzE).2]
        exact .cons (hGE ▸ hzE) hsrc2 (hdst2 ▸ ih)
    let F₁' : MGraph := { RF₁.F with E := RF₁.F.E.erase e }
    let F₂' : MGraph := { RF₂.F with E := RF₂.F.E.erase e }
    have hE' : F₁'.E = F₂'.E := by simp [F₁', F₂', hE]
    have hconn_iff : ∀ a b, F₁'.Connected a b ↔ F₂'.Connected a b := fun a b =>
      ⟨fun ⟨P, hP⟩ => ⟨P, hwalk (G₁ := F₁') (G₂ := F₂') hE'
         (fun f hf => hends f (Finset.mem_of_mem_erase hf)) hP⟩,
       fun ⟨P, hP⟩ => ⟨P, hwalk (G₁ := F₂') (G₂ := F₁') hE'.symm
         (fun f hf =>
           let h := hends f (Finset.mem_of_mem_erase (hE'.symm ▸ hf))
           ⟨h.1.symm, h.2.symm⟩) hP⟩⟩
    refine ⟨hE ▸ he, hrCap, hV ▸ hrV, hR ▸ hrNotR, ?_, ?_⟩
    · intro v hv
      obtain ⟨rt, ⟨hrtR, hconn⟩, hrtu⟩ := huniq v (hV.symm ▸ hv)
      exact ⟨rt, ⟨hR ▸ hrtR, (hconn_iff v rt).mp hconn⟩,
        fun rt' ⟨hrt'R, hconn'⟩ => hrtu rt' ⟨hR.symm ▸ hrt'R, (hconn_iff v rt').mpr hconn'⟩⟩
    · exact compForestCutsValid_congr (RF₁ := compApplyForestCut RF₁ (e, r))
        (RF₂ := compApplyForestCut RF₂ (e, r)) hV hE' (by simp [compApplyForestCut, hR])
        (fun f hf => hends f (Finset.mem_of_mem_erase hf)) hrest

/-- Every cut `(e, r)` in a valid cut list satisfies `e ∈ RF.F.E` and `r ∈ RF.F.V`. -/
lemma compForestCutsValid_mem_E_V {vCap : ℕ} :
    ∀ {RF : RootedForest} {cuts : List (ℕ × ℕ)},
      CompForestCutsValid vCap RF cuts →
      ∀ p ∈ cuts, p.1 ∈ RF.F.E ∧ p.2 ∈ RF.F.V
  | _, [], _, _, h => by cases h
  | RF, (e, r) :: rest, ⟨he, _, hrV, _, _, hrest⟩, p, hp => by
    rcases List.mem_cons.mp hp with rfl | htl
    · exact ⟨he, hrV⟩
    · have ⟨h1, h2⟩ := compForestCutsValid_mem_E_V hrest p htl
      exact ⟨Finset.mem_of_mem_erase h1, h2⟩

/-- After applying a valid cut list `cuts` to a rooted spanning forest `RF`, every vertex still has
a unique root in `(cuts.foldl compApplyForestCut RF).R`. -/
lemma compForestCutsValid_foldl_uniq {vCap : ℕ} :
    ∀ {RF : RootedForest} {cuts : List (ℕ × ℕ)},
      (∀ v ∈ RF.F.V, ∃! rt, rt ∈ RF.R ∧ RF.F.Connected v rt) →
      CompForestCutsValid vCap RF cuts →
      ∀ v ∈ (cuts.foldl compApplyForestCut RF).F.V,
        ∃! rt, rt ∈ (cuts.foldl compApplyForestCut RF).R ∧
          (cuts.foldl compApplyForestCut RF).F.Connected v rt
  | _, [], h0, _ => h0
  | RF, (e, r) :: _, _, ⟨_, _, _, _, huniq, hrest⟩ =>
    compForestCutsValid_foldl_uniq (RF := compApplyForestCut RF (e, r)) huniq hrest

/-- Lift valid cut sequences on two distinct components `c1 ≠ c2` to `cs.RF` as `cuts1 ++ cuts2`. -/
lemma compForestCutsValid_two_comps_to_global {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {c1 c2 : Fin numComps} (hne : c1 ≠ c2) {cuts1 cuts2 : List (ℕ × ℕ)}
    (hvalid1 : CompForestCutsValid vCap (cs.compSt (compOf c1)).RF cuts1)
    (hvalid2 : CompForestCutsValid vCap (cs.compSt (compOf c2)).RF cuts2) :
    CompForestCutsValid vCap cs.RF (cuts1 ++ cuts2) := by
  classical
  have h1_glob : CompForestCutsValid vCap cs.RF cuts1 :=
    compForestCutsValid_comp_to_global hI hT c1 hvalid1
  refine compForestCutsValid_append h1_glob ?_
  set RF_mid := cuts1.foldl compApplyForestCut cs.RF
  have hC1 : compOf c1 ∈ components cs.G₀ := hT.compOf_mem c1
  have hC2 : compOf c2 ∈ components cs.G₀ := hT.compOf_mem c2
  have hCne : compOf c1 ≠ compOf c2 := fun h => hne (hT.hBij.1 h)
  have hInv1 := LSFInvWith.toStructInv (hI.hCompLSF _ hC1).1
  have hInv2 := LSFInvWith.toStructInv (hI.hCompLSF _ hC2).1
  have hV_c1 : (cs.compSt (compOf c1)).RF.F.V = (cs.compSt (compOf c1)).G.V := hInv1.hT_cur_V
  have hV_c2 : (cs.compSt (compOf c2)).RF.F.V = (cs.compSt (compOf c2)).G.V := hInv2.hT_cur_V
  have hsub2 := compLSF_RF_sub_comp hI hC2
  have hV_mid : RF_mid.F.V = cs.RF.F.V := compApplyForestCut_foldl_V _ _
  have hE_mid : RF_mid.F.E = cs.RF.F.E \ (cuts1.map Prod.fst).toFinset :=
    compApplyForestCut_foldl_E _ _
  have hR_mid : RF_mid.R = cs.RF.R ∪ (cuts1.map Prod.snd).toFinset :=
    compApplyForestCut_foldl_R _ _
  have ht_mid : RF_mid.F.tail = cs.RF.F.tail := compApplyForestCut_foldl_tail _ _
  have hh_mid : RF_mid.F.head = cs.RF.F.head := compApplyForestCut_foldl_head _ _
  have hsubV : (cs.compSt (compOf c2)).RF.F.V ⊆ RF_mid.F.V := hV_mid ▸ hsub2.1
  have hsubE : (cs.compSt (compOf c2)).RF.F.E ⊆ RF_mid.F.E := by
    rw [hE_mid]; intro e he
    refine Finset.mem_sdiff.mpr ⟨hsub2.2.1 he, fun hcut => ?_⟩
    rw [List.mem_toFinset, List.mem_map] at hcut
    obtain ⟨p, hp, rfl⟩ := hcut
    have hp1 : p.1 ∈ (cs.compSt (compOf c1)).RF.F.E := (compForestCutsValid_mem_E_V hvalid1 p hp).1
    have hRS1 := (lsfInv_to_RS (hI.hCompLSF _ hC1).1).2.2.2.2
    have hRS2 := (lsfInv_to_RS (hI.hCompLSF _ hC2).1).2.2.2.2
    have hE1 : p.1 ∈ (cs.compSt (compOf c1)).G.E := hRS1.2.1 hp1
    have hE2 : p.1 ∈ (cs.compSt (compOf c2)).G.E := hRS2.2.1 he
    have ht1 := ((hI.hCompLSF _ hC1).1.hG_val p.1 hE1).1
    have ht2 := ((hI.hCompLSF _ hC2).1.hG_val p.1 hE2).1
    have hsub1 := compLSF_RF_sub_comp hI hC1
    have hteq : (cs.compSt (compOf c1)).G.tail p.1 = (cs.compSt (compOf c2)).G.tail p.1 := by
      rw [← (hRS1.2.2 p.1 hp1).1, ← (hRS2.2.2 p.1 he).1,
          (hsub1.2.2 p.1 hp1).1, (hsub2.2.2 p.1 he).1]
    exact Finset.disjoint_left.mp (hI.hV_disj _ hC1 _ hC2 hCne) ht1 (hteq ▸ ht2)
  have hRsub : (cs.compSt (compOf c2)).RF.R ⊆ RF_mid.R := by
    rw [hR_mid]; exact fun r hr => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨compOf c2, hC2, hr⟩)
  have hRpart : ∀ r ∈ RF_mid.R, r ∈ (cs.compSt (compOf c2)).RF.F.V → r ∈ (cs.compSt (compOf c2)).RF.R := by
    intro r hr hrV
    rw [hV_c2] at hrV
    rw [hR_mid, Finset.mem_union] at hr
    rcases hr with hrOld | hrNew
    · obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hrOld
      have hInvD := LSFInvWith.toStructInv (hI.hCompLSF D hD).1
      have hrVD : r ∈ (cs.compSt D).G.V := by
        rcases Finset.mem_union.mp hrD with h1 | h2
        · exact hInvD.hGV_eq ▸ Finset.mem_union_left _
            (upClosure_subset (hldAuxTree_isRootedTree hInvD.hT₀) hInvD.hR₀_sub h1)
        · exact hInvD.hGV_eq ▸ Finset.mem_union_right _ h2
      have hDC : D = compOf c2 := by
        by_contra hneD
        exact Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c2) hC2 hneD) hrVD hrV
      exact hDC ▸ hrD
    · rw [List.mem_toFinset, List.mem_map] at hrNew
      obtain ⟨p, hp, rfl⟩ := hrNew
      have hrV1 : p.2 ∈ (cs.compSt (compOf c1)).G.V :=
        hV_c1 ▸ (compForestCutsValid_mem_E_V hvalid1 p hp).2
      exact absurd hrV (Finset.disjoint_left.mp (hI.hV_disj _ hC1 _ hC2 hCne) hrV1)
  have hends : ∀ e ∈ (cs.compSt (compOf c2)).RF.F.E,
      (cs.compSt (compOf c2)).RF.F.tail e = RF_mid.F.tail e ∧
      (cs.compSt (compOf c2)).RF.F.head e = RF_mid.F.head e := fun e he => by
    rw [ht_mid, hh_mid]; exact hsub2.2.2 e he
  have hF1_val : (cs.compSt (compOf c2)).RF.F.IsValid := (lsfInv_to_RS (hI.hCompLSF _ hC2).1).1.1
  have hsep : ∀ e ∈ RF_mid.F.E, e ∉ (cs.compSt (compOf c2)).RF.F.E →
      RF_mid.F.tail e ∉ (cs.compSt (compOf c2)).RF.F.V ∧
      RF_mid.F.head e ∉ (cs.compSt (compOf c2)).RF.F.V := by
    intro e he henot
    have he0 : e ∈ cs.RF.F.E := (Finset.mem_sdiff.mp (hE_mid ▸ he)).1
    obtain ⟨D, hD, heD⟩ := Finset.mem_biUnion.mp he0
    have hDC : D ≠ compOf c2 := fun h => henot (h ▸ heD)
    have hsubD := compLSF_RF_sub_comp hI hD
    have hRS_D := lsfInv_to_RS (hI.hCompLSF D hD).1
    have h1 := hRS_D.1.1 e heD
    rw [hRS_D.2.1] at h1
    rw [hV_c2, ht_mid, hh_mid, ← (hsubD.2.2 e heD).1, ← (hsubD.2.2 e heD).2]
    exact ⟨fun ht => Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c2) hC2 hDC) h1.1 ht,
      fun hh => Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c2) hC2 hDC) h1.2 hh⟩
  have huniq_mid : ∀ v ∈ RF_mid.F.V, ∃! rt, rt ∈ RF_mid.R ∧ RF_mid.F.Connected v rt :=
    compForestCutsValid_foldl_uniq (compLSF_RF_isRSF hI).2.2.2.1 h1_glob
  exact compForestCutsValid_part_to_global cuts2 RF_mid (cs.compSt (compOf c2)).RF
    hsubV hsubE hRsub hRpart hends hF1_val hsep (fun v hv _ => huniq_mid v hv) hvalid2

/-! ## 3. Single-dispatch cost absorption -/

/-- Any single edgeful component dispatch + copy overhead is absorbed by
`k * (lsfBatchCostFactor * ((1 + len) * L_w + 1) + lsfBatchCostFactor * (len * L_w))`. -/
lemma compSingleDispatch_cost_le {k L_w len : ℕ} (hk : 1 ≤ k) (hLw : 1 ≤ L_w) (hlen : 2 ≤ len) :
    k * (lsfBatchCostFactor * ((1 + len) * L_w + 1) + 850) + 100 * len + 600 ≤
      k * (lsfBatchCostFactor * ((1 + len) * L_w + 1) + lsfBatchCostFactor * (len * L_w)) := by
  have h1 : 100 * len + 600 ≤ k * (100 * len + 600) := Nat.le_mul_of_pos_left _ hk
  have h2 : len ≤ len * L_w := Nat.le_mul_of_pos_right len hLw
  have h3a : 850 + (100 * len + 600) ≤ 1000 * len := by linarith
  have h3b : 1000 * len ≤ lsfBatchCostFactor * len := by
    have hf : 1000 ≤ lsfBatchCostFactor := by rw [lsfBatchCostFactor]; linarith
    exact Nat.mul_le_mul_right len hf
  have h3 : 850 + (100 * len + 600) ≤ lsfBatchCostFactor * (len * L_w) :=
    le_trans (le_trans h3a h3b) (Nat.mul_le_mul_left lsfBatchCostFactor h2)
  set A := lsfBatchCostFactor * ((1 + len) * L_w + 1)
  set B := lsfBatchCostFactor * (len * L_w)
  have h4 : k * (A + 850) + k * (100 * len + 600) = k * (A + (850 + (100 * len + 600))) := by
    rw [← Nat.mul_add, Nat.add_assoc]
  have h5 : k * (A + (850 + (100 * len + 600))) ≤ k * (A + B) :=
    Nat.mul_le_mul_left k (Nat.add_le_add_left h3 A)
  have h6 : k * (A + 850) + 100 * len + 600 ≤ k * (A + 850) + k * (100 * len + 600) := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left h1 _
  exact le_trans h6 (h4.symm ▸ h5)

end

end MinCostFlow.SparseCore.Program
