module

public import MinCostFlow.LSF.Program.FRIdx
public import MinCostFlow.LSF.Program.THResult

/-!
# The upward closure on vertex indices

The program for `upClosure (hldAuxTree T₀ r₀) r₀ R` works on the indices `x < n`. It has the
depth `d x` and the parent `p x` of each index in `T_H`, and the set `R` as a flag array `f`.
It runs one pass per depth `j = D, D - 1, …, 1`. The pass at depth `j` flags the parent of each
flagged index of depth `j`. A pass reads flags at depth `j` and writes flags at depth `j - 1`,
so it never reads a flag that it wrote.

This file has the math of the passes.

* `IdxAnc d p y u`: `y` is reached from `u` by `d u - d y` parent steps. `idxAnc_iff` shows that
  this is `IsAncestor` in `T_H` when `d` and `p` are the depth and the parent in `T_H`.
* `UpState n d p f j y`: the flag of `y` after the passes at depths above `j`. `upState_init`,
  `upState_step` and `upState_zero` give its value before the first pass, after each pass, and at
  the end.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-- `y` is an ancestor of `u` for the depth array `d` and the parent array `p`. -/
def IdxAnc (d p : ℕ → ℕ) (y u : ℕ) : Prop := d y ≤ d u ∧ p^[d u - d y] u = y

/-- Each index of positive depth has a parent index one level up. -/
def ParDep (n : ℕ) (d p : ℕ → ℕ) : Prop := ∀ x < n, 0 < d x → p x < n ∧ d x = d (p x) + 1

variable {n : ℕ} {d p : ℕ → ℕ}

lemma ParDep.iterate (h : ParDep n d p) {u : ℕ} (hu : u < n) :
    ∀ k ≤ d u, p^[k] u < n ∧ d (p^[k] u) = d u - k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hu, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := h _ h1 (by omega)
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by omega⟩

lemma idxAnc_refl (d p : ℕ → ℕ) (y : ℕ) : IdxAnc d p y y := ⟨le_rfl, by simp⟩

/-- One parent step from an index of positive depth. -/
lemma ParDep.idxAnc_step (h : ParDep n d p) {u y : ℕ} (hu : u < n) (hd : 0 < d u) :
    IdxAnc d p y u ↔ y = u ∨ IdxAnc d p y (p u) := by
  obtain ⟨-, h2⟩ := h u hu hd
  constructor
  · rintro ⟨h3, h4⟩
    by_cases he : d y = d u
    · left
      rw [he, Nat.sub_self, Function.iterate_zero_apply] at h4
      exact h4.symm
    · right
      refine ⟨by omega, ?_⟩
      rwa [show d u - d y = (d (p u) - d y) + 1 by omega, Function.iterate_succ_apply] at h4
  · rintro (rfl | ⟨h3, h4⟩)
    · exact idxAnc_refl d p y
    · refine ⟨by omega, ?_⟩
      rwa [show d u - d y = (d (p u) - d y) + 1 by omega, Function.iterate_succ_apply]

/-- The flag of `y` after the passes at the depths above `j`: some flagged `u` has `y` as an
ancestor, and `y = u` or `y` has depth at least `j`. -/
def UpState (n : ℕ) (d p f : ℕ → ℕ) (j y : ℕ) : Prop :=
  ∃ u < n, f u = 1 ∧ IdxAnc d p y u ∧ (y = u ∨ j ≤ d y)

/-- Before the first pass the state is the input flags. -/
lemma upState_init {f : ℕ → ℕ} {D y : ℕ} (hD : ∀ x < n, d x ≤ D) (hy : y < n) :
    UpState n d p f D y ↔ f y = 1 := by
  constructor
  · rintro ⟨u, hu, hf, ⟨h1, h2⟩, h3 | h3⟩
    · rwa [h3]
    · have := hD u hu
      rw [show d u - d y = 0 by omega, Function.iterate_zero_apply] at h2
      rwa [← h2]
  · intro hf
    exact ⟨y, hy, hf, idxAnc_refl d p y, Or.inl rfl⟩

/-- The pass at depth `j`. -/
lemma ParDep.upState_step (h : ParDep n d p) {f : ℕ → ℕ} {j y : ℕ} (hj : 1 ≤ j) :
    (UpState n d p f j y ∨ ∃ x < n, d x = j ∧ p x = y ∧ UpState n d p f j x) ↔
      UpState n d p f (j - 1) y := by
  constructor
  · rintro (⟨u, hu, hf, ha, hc⟩ | ⟨x, hx, hdx, hpx, u, hu, hf, ⟨h1, h2⟩, -⟩)
    · exact ⟨u, hu, hf, ha, hc.imp id (fun h => by omega)⟩
    · obtain ⟨-, h4⟩ := h x hx (by omega)
      rw [hpx] at h4
      refine ⟨u, hu, hf, ⟨by omega, ?_⟩, Or.inr (by omega)⟩
      rw [show d u - d y = (d u - d x) + 1 by omega, Function.iterate_succ_apply', h2, hpx]
  · rintro ⟨u, hu, hf, ⟨h1, h2⟩, hc⟩
    by_cases hyu : y = u
    · exact Or.inl ⟨u, hu, hf, ⟨h1, h2⟩, Or.inl hyu⟩
    by_cases hjy : j ≤ d y
    · exact Or.inl ⟨u, hu, hf, ⟨h1, h2⟩, Or.inr hjy⟩
    have hdy : d y = j - 1 := by
      rcases hc with hc | hc
      · exact absurd hc hyu
      · omega
    have hlt : d y < d u := by
      rcases Nat.lt_or_ge (d y) (d u) with hlt | hge
      · exact hlt
      · rw [show d u - d y = 0 by omega, Function.iterate_zero_apply] at h2
        exact absurd h2.symm hyu
    obtain ⟨hxn, hdx⟩ := h.iterate hu (d u - d y - 1) (by omega)
    refine Or.inr ⟨p^[d u - d y - 1] u, hxn, by omega, ?_, u, hu, hf, ⟨by omega, ?_⟩,
      Or.inr (by omega)⟩
    · rw [← Function.iterate_succ_apply' p, show (d u - d y - 1).succ = d u - d y by omega, h2]
    · rw [hdx, show d u - (d u - (d u - d y - 1)) = d u - d y - 1 by omega]

/-- After the last pass the flags are the upward closure. -/
lemma upState_zero {f : ℕ → ℕ} {y : ℕ} :
    UpState n d p f 0 y ↔ ∃ u < n, f u = 1 ∧ IdxAnc d p y u :=
  ⟨fun ⟨u, hu, hf, ha, _⟩ => ⟨u, hu, hf, ha⟩,
    fun ⟨u, hu, hf, ha⟩ => ⟨u, hu, hf, ha, Or.inr (Nat.zero_le _)⟩⟩

/-! ## The bridge to `T_H` -/

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

/-- The depth and the parent in `T_H` on indices, as `thProc` gives them (`THOut`). -/
def THIdx (T₀ : MGraph) (vList : List ℕ) (r : ℕ) (dTH thPar : ℕ → ℕ) : Prop :=
  ∀ x < vList.length,
    dTH x = depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) ∧
    (x ≠ r → thPar x < vList.length ∧
      vList.getD (thPar x) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0))

/-- The root is the only index of depth `0`, and the other indices step to their parents. -/
lemma THIdx.parDep {dTH thPar : ℕ → ℕ} (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : THIdx T₀ vList r dTH thPar) : ParDep vList.length dTH thPar := by
  intro x hx hpos
  have hxr : x ≠ r := by
    rintro rfl
    rw [(h x hx).1, thDepth_root hI] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨hd, hp⟩ := (h x hx).2 hxr
  have hne : vList.getD x 0 ≠ vList.getD r 0 := fun he => hxr (hI.getD_inj hx hI.hr he)
  obtain ⟨-, -, hdep⟩ := hldAuxTree_parent hI.hT (hI.getD_mem hx) hne
  refine ⟨hd, ?_⟩
  rw [(h x hx).1, (h _ hd).1, hp, hdep]

/-- `IdxAnc` is `IsAncestor` in `T_H`. -/
theorem THIdx.idxAnc_iff {dTH thPar : ℕ → ℕ} (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : THIdx T₀ vList r dTH thPar) {y u : ℕ} (hy : y < vList.length) (hu : u < vList.length) :
    IdxAnc dTH thPar y u ↔ IsAncestor (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0)
      (vList.getD y 0) (vList.getD u 0) := by
  have hTH := hldAuxTree_isRootedTree hI.hT
  have hPD := h.parDep hI
  suffices H : ∀ k, ∀ u < vList.length, dTH u = k → (IdxAnc dTH thPar y u ↔
      IsAncestor (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD y 0)
        (vList.getD u 0)) from H _ u hu rfl
  intro k
  induction k with
  | zero =>
    intro u hu hk
    have hur : u = r := by
      by_contra hne
      have hne' : vList.getD u 0 ≠ vList.getD r 0 := fun he => hne (hI.getD_inj hu hI.hr he)
      obtain ⟨-, -, hdep⟩ := hldAuxTree_parent hI.hT (hI.getD_mem hu) hne'
      rw [(h u hu).1, hdep] at hk
      omega
    subst hur
    rw [isAncestor_iff_eq_or_parent hTH (hI.getD_mem hu)]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hk, show 0 - dTH y = 0 by omega, Function.iterate_zero_apply] at h2
      exact Or.inl (by rw [h2])
    · rintro (he | ⟨hne, -⟩)
      · rw [hI.getD_inj hy hu he]; exact idxAnc_refl _ _ _
      · exact absurd rfl hne
  | succ k ih =>
    intro u hu hk
    have hur : u ≠ r := by
      rintro rfl
      rw [(h _ hu).1, thDepth_root hI] at hk
      omega
    have hne' : vList.getD u 0 ≠ vList.getD r 0 := fun he => hur (hI.getD_inj hu hI.hr he)
    obtain ⟨hpn, hp⟩ := (h u hu).2 hur
    obtain ⟨hpar, -, -⟩ := hldAuxTree_parent hI.hT (hI.getD_mem hu) hne'
    obtain ⟨-, hdp⟩ := hPD u hu (by omega)
    rw [hPD.idxAnc_step hu (by omega), isAncestor_iff_eq_or_parent hTH (hI.getD_mem hu), hpar,
      ← hp, ih _ hpn (by omega)]
    constructor
    · rintro (rfl | ha)
      · exact Or.inl rfl
      · exact Or.inr ⟨hne', ha⟩
    · rintro (he | ⟨-, ha⟩)
      · exact Or.inl (hI.getD_inj hy hu he)
      · exact Or.inr ha

/-- The flags after the last pass are the upward closure of the flagged vertices. -/
theorem THIdx.upClosure_flag {dTH thPar f : ℕ → ℕ} {R : Finset ℕ}
    (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (h : THIdx T₀ vList r dTH thPar)
    (hR : ∀ v ∈ R, v ∈ vList) (hf : ∀ u < vList.length, f u = 1 ↔ vList.getD u 0 ∈ R)
    {y : ℕ} (hy : y < vList.length) :
    (∃ u < vList.length, f u = 1 ∧ IdxAnc dTH thPar y u) ↔
      vList.getD y 0 ∈ upClosure (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) R := by
  rw [mem_upClosure_iff]
  constructor
  · rintro ⟨u, hu, hfu, ha⟩
    exact ⟨_, (hf u hu).mp hfu, (h.idxAnc_iff hI hy hu).mp ha⟩
  · rintro ⟨v, hv, ha⟩
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem (hR v hv)
    rw [← List.getD_eq_getElem _ 0 hu] at hv ha
    exact ⟨u, hu, (hf u hu).mpr hv, (h.idxAnc_iff hI hy hu).mpr ha⟩

end MinCostFlow.LSF.Program

end
