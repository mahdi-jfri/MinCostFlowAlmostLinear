module

public import MinCostFlow.LSF.Program.FRMath
public import MinCostFlow.LSF.Program.THPlaceMath
public import MinCostFlow.LSF.Program.DecompBridge

/-!
# The roots pass on vertex indices

The program works on the indices `x < n` of the vertex list `vList`, with parent `par x` and
parent edge index `pe x` (`TreeIdx`). The root set `R` is given as a flag array: `inR x = 1`
exactly when the vertex `vList[x]` is in `R`. The edge order is given on edge indices:
`π (fid i) = piv i`.

The roots pass has three parts, and this file proves what each part gives.

* `mp_bridge`: the rule `MpRule` gives, at each index other than the root, the index of the
  `π`-smallest edge up to the nearest proper ancestor in `R` (`upMin`, `FRMath.lean`).
* `OwnState`: the owner array. For each edge index `i`, `own i = y + 1` when `i` is the edge of
  `mp` of an index `y` of `R` other than the root, and `own i = 0` when there is no such `y`.
* `rt_bridge`: the rule `RtRule` gives the root of every vertex in `F_T(R, π)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

lemma TreeIdx.getD_inj (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {a b : ℕ}
    (ha : a < vList.length) (hb : b < vList.length) (h : vList.getD a 0 = vList.getD b 0) :
    a = b := by
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hI.hnd.getElem_inj_iff).mp h

lemma TreeIdx.step (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {x : ℕ}
    (hx : x < vList.length) (hxr : x ≠ r) :
    par x < vList.length ∧ pe x < tM ∧ dep x = dep (par x) + 1 ∧
      parent T₀ (vList.getD r 0) (vList.getD x 0) = vList.getD (par x) 0 ∧
      parentEdge T₀ (vList.getD r 0) (vList.getD x 0) = fid (pe x) := by
  obtain ⟨hpe, -, hdep⟩ := hI.hR.step x hx hxr
  obtain ⟨-, hp⟩ := t0Rooted_spec hI.hT.isForest hI.hA hI.hnd hI.hR hI.hr hx
  exact ⟨hI.hR.par_lt x hx, hpe, hdep, (hp hxr).1, (hp hxr).2⟩

/-- The rule of the first part, at an index `x` other than the root. -/
def MpRule (inR par pe piv mp : ℕ → ℕ) (x : ℕ) : Prop :=
  mp x = if inR (par x) = 1 then pe x
    else if piv (pe x) < piv (mp (par x)) then pe x else mp (par x)

/-- The facts about the root set and the edge order that the bridges use. -/
structure RootSetIdx (T₀ : MGraph) (vList : List ℕ) (tM r : ℕ) (fid : ℕ → ℕ) (R : Finset ℕ)
    (π : ℕ → ℕ) (inR piv : ℕ → ℕ) : Prop where
  hR : IsBranchFree T₀ (vList.getD r 0) R
  hrR : vList.getD r 0 ∈ R
  hinR : ∀ x < vList.length, (inR x = 1 ↔ vList.getD x 0 ∈ R)
  hπ : IsEdgeOrder T₀ π
  hpiv : ∀ i < tM, π (fid i) = piv i

theorem mp_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {R : Finset ℕ}
    {π inR piv mp : ℕ → ℕ} (hS : RootSetIdx T₀ vList tM r fid R π inR piv)
    (hrule : ∀ x < vList.length, x ≠ r → MpRule inR par pe piv mp x) :
    ∀ x < vList.length, x ≠ r →
      mp x < tM ∧ fid (mp x) = upMin T₀ (vList.getD r 0) R π (vList.getD x 0) := by
  suffices H : ∀ d, ∀ x < vList.length, dep x = d → x ≠ r →
      mp x < tM ∧ fid (mp x) = upMin T₀ (vList.getD r 0) R π (vList.getD x 0) from
    fun x hx hxr => H _ x hx rfl hxr
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd hxr
  obtain ⟨hpn, hpe, hdep, hpar, hpeq⟩ := hI.step hx hxr
  have hxV := hI.getD_mem hx
  have hgxr : vList.getD x 0 ≠ vList.getD r 0 := fun h => hxr (hI.getD_inj hx hI.hr h)
  rw [hrule x hx hxr, upMin_step hI.hT hS.hR.1 hS.hrR hS.hπ hxV hgxr, hpar, hpeq]
  by_cases h1 : inR (par x) = 1
  · rw [if_pos h1, if_pos ((hS.hinR _ hpn).mp h1)]
    exact ⟨hpe, rfl⟩
  · have hpR : vList.getD (par x) 0 ∉ R := fun h => h1 ((hS.hinR _ hpn).mpr h)
    rw [if_neg h1, if_neg hpR]
    have hpr : par x ≠ r := by
      rintro h
      exact hpR (h ▸ hS.hrR)
    obtain ⟨hmp, hfid⟩ := ih (dep (par x)) (by omega) (par x) hpn rfl hpr
    rw [← hfid, hS.hpiv _ hpe, hS.hpiv _ hmp]
    split_ifs
    · exact ⟨hpe, rfl⟩
    · exact ⟨hmp, rfl⟩

/-! ## The owner array -/

/-- The owner array after the indices below `j`. -/
def OwnState (r tM : ℕ) (inR mp own : ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ i < tM, (own i ≠ 0 → own i - 1 < j ∧ own i - 1 ≠ r ∧ inR (own i - 1) = 1 ∧
      mp (own i - 1) = i) ∧
    (own i = 0 → ∀ y < j, y ≠ r → inR y = 1 → mp y ≠ i)

lemma ownState_zero {r tM : ℕ} {inR mp own : ℕ → ℕ} (h0 : ∀ i < tM, own i = 0) :
    OwnState r tM inR mp own 0 :=
  fun i hi => ⟨fun h => absurd (h0 i hi) h, fun _ y hy => absurd hy (Nat.not_lt_zero y)⟩

/-- The step at an index `j` that is not written. -/
lemma ownState_skip {r tM : ℕ} {inR mp own : ℕ → ℕ} {j : ℕ}
    (h : OwnState r tM inR mp own j) (hj : ¬ (j ≠ r ∧ inR j = 1)) :
    OwnState r tM inR mp own (j + 1) := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  refine ⟨fun hne => ?_, fun hz y hy hyr hyR => ?_⟩
  · obtain ⟨a, b, c, d⟩ := h1 hne
    exact ⟨by omega, b, c, d⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
    · exact h2 hz y hy hyr hyR
    · exact absurd ⟨hyr, hyR⟩ hj

/-- The step at an index `j` of `R` other than the root: `own (mp j) := j + 1`. -/
lemma ownState_write {r tM : ℕ} {inR mp own own' : ℕ → ℕ} {j : ℕ}
    (h : OwnState r tM inR mp own j) (hjr : j ≠ r) (hjR : inR j = 1)
    (hown' : ∀ i, own' i = if i = mp j then j + 1 else own i) :
    OwnState r tM inR mp own' (j + 1) := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  rw [hown' i]
  split_ifs with hij
  · refine ⟨fun _ => ⟨by omega, by simpa using hjr, by simpa using hjR, by simp [hij]⟩,
      fun hz => hz.elim⟩
  · refine ⟨fun hne => ?_, fun hz y hy hyr hyR => ?_⟩
    · obtain ⟨a, b, c, d⟩ := h1 hne
      exact ⟨by omega, b, c, d⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
      · exact h2 hz y hy hyr hyR
      · exact fun hm => hij hm.symm

/-! ## The roots -/

/-- The rule of the third part, at an index `x` other than the root. -/
def RtRule (inR par pe own rt : ℕ → ℕ) (x : ℕ) : Prop :=
  rt x = if inR x = 1 then x else if own (pe x) ≠ 0 then own (pe x) - 1 else rt (par x)

/-- Two vertices of `R` other than the root with the same deleted edge are equal. -/
lemma deletedEdge_inj {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) {R : Finset ℕ}
    (hR : IsBranchFree T r R) (hrR : r ∈ R) (π : ℕ → ℕ) {y₁ y₂ : ℕ}
    (h₁ : y₁ ∈ R.erase r) (h₂ : y₂ ∈ R.erase r)
    (h : deletedEdge T r R π y₁ = deletedEdge T r R π y₂) : y₁ = y₂ := by
  by_contra hne
  have h₁' : y₁ ∈ R.erase (topRoot T r R) := by rwa [topRoot_eq_of_mem hT hR hrR]
  have h₂' : y₂ ∈ R.erase (topRoot T r R) := by rwa [topRoot_eq_of_mem hT hR hrR]
  have hdisj := adjacent_paths_disjoint hT hR ⟨r, hrR⟩ h₁' h₂' hne
  exact Finset.disjoint_left.mp hdisj (deletedEdge_mem hT hR hrR π h₁)
    (h ▸ deletedEdge_mem hT hR hrR π h₂)

theorem rt_lt (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {inR mp own rt : ℕ → ℕ}
    (hown : OwnState r tM inR mp own vList.length) (hrt_r : rt r = r)
    (hrule : ∀ x < vList.length, x ≠ r → RtRule inR par pe own rt x) :
    ∀ x < vList.length, rt x < vList.length := by
  suffices H : ∀ d, ∀ x < vList.length, dep x = d → rt x < vList.length from
    fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd
  by_cases hxr : x = r
  · rw [hxr, hrt_r]; exact hI.hr
  obtain ⟨hpn, hpe, hdep, -, -⟩ := hI.step hx hxr
  rw [hrule x hx hxr]
  split_ifs with h1 h2
  · exact hx
  · exact ((hown _ hpe).1 h2).1
  · exact ih _ (by omega) _ hpn rfl

/-- The third part gives the root of every vertex in `F_T(R, π)`. -/
theorem rt_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {R : Finset ℕ}
    {π inR piv mp own rt : ℕ → ℕ} (hS : RootSetIdx T₀ vList tM r fid R π inR piv)
    (hmp : ∀ x < vList.length, x ≠ r → MpRule inR par pe piv mp x)
    (hown : OwnState r tM inR mp own vList.length) (hrt_r : rt r = r)
    (hrule : ∀ x < vList.length, x ≠ r → RtRule inR par pe own rt x) :
    ∀ x < vList.length, rt x < vList.length ∧
      vList.getD (rt x) 0 ∈ R ∧
      (forestGivenRoots T₀ (vList.getD r 0) R π).Connected (vList.getD x 0)
        (vList.getD (rt x) 0) := by
  classical
  have hT := hI.hT
  have hMP := mp_bridge hI hS hmp
  have hlt := rt_lt hI hown hrt_r hrule
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < vList.length ∧ vList.getD (vList.idxOf v) 0 = v := fun v hv =>
    ⟨List.idxOf_lt_length_of_mem ((hI.hV v).mp hv), getD_idxOf ((hI.hV v).mp hv)⟩
  have hidx' : ∀ x < vList.length, vList.idxOf (vList.getD x 0) = x := fun x hx => idxOf_getD hI.hnd hx
  -- An index of `R` other than the root whose `mp` is `i` is the owner of `i`.
  have howner : ∀ i < tM, own i ≠ 0 →
      own i - 1 < vList.length ∧ vList.getD (own i - 1) 0 ∈ R.erase (vList.getD r 0) ∧
        deletedEdge T₀ (vList.getD r 0) R π (vList.getD (own i - 1) 0) = fid i := by
    intro i hi hne
    obtain ⟨a, b, c, d⟩ := (hown i hi).1 hne
    refine ⟨a, Finset.mem_erase.mpr ⟨fun h => b (hI.getD_inj a hI.hr h),
      (hS.hinR _ a).mp c⟩, ?_⟩
    rw [deletedEdge_eq_upMin, ← (hMP _ a b).2, d]
  have hrules := forestRoot_rule hT hS.hR hS.hrR π (fun v => vList.getD (rt (vList.idxOf v)) 0)
    (fun v hv hvR => by
      obtain ⟨hxl, hgx⟩ := hidx v hv
      by_cases hxr : vList.idxOf v = r
      · rw [hxr, hrt_r, ← hgx, hxr]
      · rw [hrule _ hxl hxr, if_pos ((hS.hinR _ hxl).mpr (by rw [hgx]; exact hvR)), hgx])
    (fun v hv hvR y hy hpe => by
      obtain ⟨hxl, hgx⟩ := hidx v hv
      set x := vList.idxOf v
      have hxr : x ≠ r := fun h => hvR (by rw [← hgx, h]; exact hS.hrR)
      obtain ⟨-, hpe', -, -, hpeq⟩ := hI.step hxl hxr
      have hyV := hS.hR.1 (Finset.mem_erase.mp hy).2
      obtain ⟨hyl, hgy⟩ := hidx y hyV
      have hyr : vList.idxOf y ≠ r := fun h => (Finset.mem_erase.mp hy).1 (by
        rw [← hgy, h])
      have hyR : inR (vList.idxOf y) = 1 :=
        (hS.hinR _ hyl).mpr (by rw [hgy]; exact (Finset.mem_erase.mp hy).2)
      obtain ⟨hmpl, hmpf⟩ := hMP _ hyl hyr
      -- The edge index of `mp y` is the parent edge index of `x`.
      have hmpe : mp (vList.idxOf y) = pe x := by
        refine hI.hA.fid_inj _ hmpl _ hpe' ?_
        rw [hmpf, hgy, ← deletedEdge_eq_upMin, ← hpe, ← hgx, hpeq]
      have hne : own (pe x) ≠ 0 := fun hz => (hown _ hpe').2 hz _ hyl hyr hyR hmpe
      obtain ⟨hol, hoR, hod⟩ := howner _ hpe' hne
      have hyy : vList.getD (own (pe x) - 1) 0 = y := by
        refine deletedEdge_inj hT hS.hR hS.hrR π hoR hy ?_
        rw [hod, ← hpe, ← hgx, hpeq]
      have hxR : inR x ≠ 1 := fun h => hvR (hgx ▸ (hS.hinR _ hxl).mp h)
      rw [hrule _ hxl hxr, if_neg hxR, if_pos hne, hyy])
    (fun v hv hvR hno => by
      obtain ⟨hxl, hgx⟩ := hidx v hv
      set x := vList.idxOf v
      have hxr : x ≠ r := fun h => hvR (by rw [← hgx, h]; exact hS.hrR)
      obtain ⟨hpn, hpe', -, hpar, hpeq⟩ := hI.step hxl hxr
      have hz : own (pe x) = 0 := by
        by_contra hne
        obtain ⟨-, hoR, hod⟩ := howner _ hpe' hne
        exact hno _ hoR (by rw [hod, ← hgx, hpeq])
      have hxR : inR x ≠ 1 := fun h => hvR (hgx ▸ (hS.hinR _ hxl).mp h)
      rw [hrule _ hxl hxr, if_neg hxR, if_neg (not_not.mpr hz), ← hgx, hpar, hidx' _ hpn])
  intro x hx
  obtain ⟨h1, h2⟩ := hrules (vList.getD x 0) (hI.getD_mem hx)
  rw [hidx' x hx] at h1 h2
  exact ⟨hlt x hx, h1, h2⟩

end MinCostFlow.LSF.Program
