module

public import MinCostFlow.HierPaths.DelProgBounds
public import MinCostFlow.HierPaths.DelProgAmortized

/-!
# The Delete procedure

The model supplies the abstract state after deletion. The machine produces that state and
the pruned vertices, and its instruction charges are paid by the scaled potential.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- The Delete procedure uses a single body with no helper calls. -/
@[expose] def hierDeleteProc : HierProc where
  entry _ := hierDeleteEntry
  helpers _ := []

theorem hierDeleteProc_noRand : hierDeleteProc.NoRand := by
  intro k
  exact ⟨hierDeleteEntry_noRand, by simp [hierDeleteProc]⟩

private theorem length_encode_delete {a : ℕ} (x : HierConcrete) (e : ℕ)
    (hrel : x.H.Rel a x.ms) (hG : x.ms.abs.G.IsValid) (hnew : e ∉ x.ms.st.deleted) :
    (HierConcrete.mk x.H (x.H.delete x.ms e)).encode.length = x.encode.length := by
  rw [← x.afterDelReports_eq e hrel.spec.arrays hG hrel.inv hrel.vhat]
  unfold HierConcrete.afterDelReports HierConcrete.afterReports
  rw [HierConcrete.length_encode_withVhat, ← x.afterDelCursors_eq e]
  change ((x.afterDelConns e).delRefreshState _ _).encode.length = _
  rw [HierConcrete.length_encode_delRefreshState]
  unfold HierConcrete.afterDelConns
  rw [HierConcrete.length_encode_markIneligList]
  exact x.length_encode_afterDelLoss hnew

private theorem amortized {a : ℕ} (x : HierConcrete) (e : ℕ)
    (hrel : x.H.Rel a x.ms) (hG : x.ms.abs.G.IsValid) (hnew : e ∉ x.ms.st.deleted)
    (hm : x.m ≤ x.ms.abs.M) :
    hierDeleteEntryCost x e + hierPhiScale * (HierConcrete.mk x.H (x.H.delete x.ms e)).potential ≤
      106496 * gammaHP a (Nat.ceil (1 / x.ms.abs.φ_in)) x.ms.abs.M +
        hierPhiScale * x.potential := by
  let A := x.H.A
  let L := A.delCoef x.H.ξ x.H.κ x.H.lam
  let st := x.ms.st
  let st' := A.deleteState st e
  have hL := A.delCoef_le_gamma hm hrel.fits.depth hrel.fits.conns hrel.fits.xi hrel.fits.lam
  have hXi : 1 + x.H.ξ ≤ L := by
    dsimp only [L, StaticArrays.delCoef_eq]
    calc
      _ ≤ (1 + x.H.ξ) * (leafDepth A.x A.b + 2) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ * 4 ^ leafDepth A.x A.b := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
      _ ≤ _ * (1 + x.H.κ) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hE := A.events_le hrel.spec.arrays hrel.inv hrel.spec.walkLen
  obtain ⟨hinv, hdel⟩ := A.deleteState_inv hrel.spec.arrays hrel.inv e
  have hE' := A.events_le hrel.spec.arrays hinv hrel.spec.walkLen
  have hmono := (A.deleteCost_le hrel.spec.arrays hG hrel.inv e).1
  have hcard : st'.deleted.card = st.deleted.card + 1 := by
    change (A.deleteState st e).deleted.card = _
    rw [hdel, Finset.card_insert_of_notMem hnew]
  have hc := hierDeleteEntryCost_le_events x e hrel hG
  change _ ≤ 4096 * (1 + x.H.ξ + 2 * (A.events x.n st' - A.events x.n st)) at hc
  change A.events x.n st ≤ A.events x.n st' at hmono
  change A.events x.n st ≤ 12 * L * st.deleted.card at hE
  change A.events x.n st' ≤ 12 * L * st'.deleted.card at hE'
  change L ≤ _ at hL
  change hierDeleteEntryCost x e +
      4096 * (24 * L * st'.deleted.card - 2 * A.events x.n st') ≤ _ +
      4096 * (24 * L * st.deleted.card - 2 * A.events x.n st)
  rw [hcard, Nat.mul_add, Nat.mul_one] at hE' ⊢
  have h₀ : 24 * L * st.deleted.card = 2 * (12 * L * st.deleted.card) := by ring
  rw [h₀]
  omega

/-- The deterministic Delete procedure meets operation 0, including the amortized cost. -/
theorem hierDeleteProc_spec (a : ℕ) :
    DelProcSpec a hierDeleteProc 106496 hierDeleteSpace (11 * 16 ^ 12) 12 1 := by
  refine ⟨hierDeleteProc_noRand, by norm_num, hierDeleteSpace_form a, ?_⟩
  intro hc hcost hspace _ w p j k hp b s X args mem pos ω _ hhead hrep hpre hfoot hzero hroom
  obtain ⟨b', e, h, rfl, hValid, he, hnew, _⟩ := hpre
  have hb' : b' = b := Option.some.inj hhead
  subst b'
  obtain ⟨hs, hrel₀, hL₀⟩ := hrep
  subst s
  let x := X.delCursorWitness
  have hx : x.encode = X.encode := X.delCursorWitness_encode
  have hL : ListAt mem b x.encode := hx.symm ▸ hL₀
  have hrel := X.delCursorWitness_rel hrel₀
  have hcur := X.delCursorWitness_cur_le hrel₀
  have hheap : heapArg [b, e, h] = h := rfl
  have hSize : (pathDSDataStructure hc.params w).space 0 X.ms.abs [b, e, h] mem =
      hierDeleteSpace x.ms.abs.phiNum x.ms.abs.phiDen x.n x.m x.ms.abs.M := by
    change hc.delSpace x.ms.abs.phiNum x.ms.abs.phiDen x.n x.m x.ms.abs.M = _
    rw [hspace]
  rw [hheap, hSize] at hroom
  rw [hheap] at hzero
  have hb : b + x.encode.length ≤ h := by
    rw [hx]
    have hlen : 25 ≤ X.encode.length := by simp [HierConcrete.encode, layoutList, csrList, csrOffsets, X.length_sections']
    have hh := hfoot (b + X.encode.length - 1) ⟨by omega, by omega⟩
    change _ < h at hh
    omega
  have hValidFacts := hValid
  obtain ⟨_, _, hG, _, hm, _⟩ := hValidFacts
  have hnew' : e ∉ x.ms.st.deleted := by
    rw [← hrel.deleted]
    exact hnew
  have ⟨hw, hout⟩ := delEntryWorkBounds_of_space x (e := e) hrel hValid hb hroom hcur
  let y := HierConcrete.mk x.H (x.H.delete x.ms e)
  let L := (x.afterDelCursors e).delReports (x.H.A.delSupportVisits x.ms.st e)
  let start := startState [b, e, h] mem pos
  obtain ⟨o, st', c, hrun, hpost, hcRun⟩ :=
    hierDeleteEntry_triple (p := p) x (R := start.regs) rfl rfl rfl he hnew' hrel hG hb hw hout hzero
      start ω ⟨rfl, hL, rfl⟩
  cases o with
  | normal => contradiction
  | returned u =>
    obtain ⟨hu, hLy, hSeq, hn, hSet, hZero, hFrame⟩ := hpost
    change u = h + 1 + L.length at hu
    change L.Nodup at hn
    change L.toFinset = y.ms.abs.Vhat \ x.ms.abs.Vhat at hSet
    change c ≤ hierDeleteEntryCost x e at hcRun
    have hParams : IsHierParams a hc.params := ⟨fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩
    obtain ⟨hnum, hden, hM, hGraph, hdel, hV, hValid', _, _, hrel'⟩ :=
      x.H.model_delete hParams hrel hValid he
    have hlen : L.length ≤ x.n := by
      rw [← List.toFinset_card_of_nodup hn, hSet]
      have hv : y.ms.abs.Vhat ⊆ Finset.range x.n := by
        obtain ⟨_, _, _, _, _, _, _, hv, _⟩ := hValid'
        exact hv
      exact (Finset.card_le_card (Finset.sdiff_subset.trans hv)).trans_eq (Finset.card_range _)
    have hl := length_encode_delete x e hrel hG hnew'
    refine ⟨hierDeleteEntry, hp.1, .returned u, st', c, hrun, y.ms.abs, y,
      ⟨rfl, hrel', hLy⟩, ⟨b, e, h, rfl, hnum, hden, hM, hGraph, hdel, hV, hValid',
        L, hSeq, hn, hSet⟩, ?_, ?_⟩
    · rw [hheap, hSize]
      change h ≤ u ∧ u ≤ h + hierDeleteSpace _ _ x.n x.m _ ∧ _ ∧ _ ∧ _
      refine ⟨by omega, ?_, hZero, ?_, ?_⟩
      · unfold hierDeleteSpace
        omega
      · intro z hz hz'
        apply hFrame z hz
        change ¬ (b ≤ z ∧ z < b + X.encode.length) at hz'
        change z < b ∨ b + x.encode.length ≤ z
        rw [hx]
        omega
      · intro z hz
        apply Or.inl
        change b ≤ z ∧ z < b + y.encode.length at hz
        change b ≤ z ∧ z < b + X.encode.length
        rwa [← hx, ← hl]
    · let Γ := gammaHP a (Nat.ceil (1 / x.ms.abs.φ_in)) x.ms.abs.M
      change c + hierPhiScale * y.potential ≤ Nat.ceil (hc.K_del * (Γ : ℝ)) +
        hierPhiScale * X.potential
      have hcast : (106496 : ℝ) * (Γ : ℝ) = ((106496 * Γ : ℕ) : ℝ) := by norm_cast
      rw [hcost, hcast, Nat.ceil_natCast, ← X.delCursorWitness_potential]
      exact (Nat.add_le_add_right hcRun _).trans (amortized x e hrel hG hnew' hm)

end MinCostFlow.HierPaths
