module

public import MinCostFlow.SparseCore.CoreQuotient

import Mathlib.Tactic.Linarith

/-!
# Dynamic vertex-split quotient maintenance (`tildeStepBatch`)

Maintains the vertex-split quotient graph `\tilde{C}` under edge deletions and vertex splits
on `G`, preserving `RootPieceInv` and exact endpoint agreement with `G`, while
bounding total new splits per update `u` by
`(S'.R \ S.R).card + (if split then (E_s ∩ S.RF.F.E).card else 0)`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 4. Dynamic deletion + split maintenance of vertex-split quotient graphs -/

/-- Structural lineage invariant linking `S₀` (time `0` state) to any later state `S`. -/
structure LSFDerivedFrom (S₀ S : LSFState) : Prop where
  hG₀_eq : S.G₀ = S₀.G₀
  hS₀_G : S₀.G = S₀.G₀
  hT₀_eq : S.T₀ = S₀.T₀
  hW_eq : S.W_init = S₀.W_init
  hS₀_iso : S₀.isolatedVerts = ∅
  hR_sub : S₀.R ⊆ S.R
  hFE_sub : S.RF.F.E ⊆ S₀.RF.F.E

lemma lsfDerivedFrom_refl {S₀ : LSFState} (hS₀_G : S₀.G = S₀.G₀) (hS₀_iso : S₀.isolatedVerts = ∅) :
    LSFDerivedFrom S₀ S₀ :=
  ⟨rfl, hS₀_G, rfl, rfl, hS₀_iso, Finset.Subset.rfl, Finset.Subset.rfl⟩

lemma lsfDerivedFrom_step {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {u : Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S) :
    LSFDerivedFrom S₀ (applyLSFUpdate S u) := by
  have hsp := applyLSFUpdate_inv_with hI hu
  exact ⟨hsp.2.2.1.trans hD.hG₀_eq, hD.hS₀_G, hsp.2.2.2.1.trans hD.hT₀_eq,
    hsp.2.2.2.2.2.2.2.1.trans hD.hW_eq, hD.hS₀_iso,
    Finset.Subset.trans hD.hR_sub hsp.2.2.2.2.2.2.2.2.1,
    Finset.Subset.trans hsp.2.2.2.2.2.2.2.2.2.1 hD.hFE_sub⟩

/-- Edge-deletion prefix on `\tilde{C}` when `u = .delete e₀` and `e₀ ∈ C.E`. -/
def delStepC (C : MGraph) (u : Update) : List Update :=
  match u with
  | .delete e₀ => if e₀ ∈ C.E then [.delete e₀] else []
  | _ => []

/-- Step 3a: for `u = .split v v' St Sh`, move edges incident to `v` in `St`/`Sh` (checked on `G_old`)
off `m_prev v` onto `nextVid`. -/
def splitStepA (m_prev : ℕ → ℕ) (G_old C_del : MGraph) (u : Update) (nextVid : ℕ) :
    List Update × (ℕ → ℕ) × ℕ :=
  match u with
  | .split v v' St Sh =>
    let St_A := C_del.E.filter fun e => e ∈ St ∧ G_old.tail e = v
    let Sh_A := C_del.E.filter fun e => e ∈ Sh ∧ G_old.head e = v
    ([.split (m_prev v) nextVid St_A Sh_A],
      Function.update m_prev v' nextVid, nextVid + 1)
  | _ => ([], m_prev, nextVid)

lemma forest_connected_stepProj {thresh K_σ thresh' K_σ' : ℝ} {ℓ₀ : ℕ → ℝ}
    {S S' : LSFState} {u : Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hu : S.G.UpdateIsValid u)
    (hI' : LSFInvWith thresh' K_σ' ℓ₀ S') (hS' : S' = applyLSFUpdate S u)
    {x y : ℕ} (hconn : S'.RF.F.Connected x y) :
    S.RF.F.Connected (stepProj u x) (stepProj u y) := by
  have hRF := lsfInv_to_RS hI
  have hRF' := lsfInv_to_RS hI'
  have hFE_sub : S'.RF.F.E ⊆ S.RF.F.E := by
    rw [hS']; exact (applyLSFUpdate_inv_with hI hu).2.2.2.2.2.2.2.2.2.1
  have hG'_eq : S'.G = S.G.applyUpdate u := by
    rw [hS']; exact (applyLSFUpdate_inv_with hI hu).2.1
  obtain ⟨P, hP⟩ := hconn
  refine ⟨P, ?_⟩
  induction hP with
  | nil z => exact .nil (stepProj u z)
  | @cons a _ x₀ P₀ hxE hsrc _ ih =>
    have hxF : x₀.1 ∈ S.RF.F.E := hFE_sub hxE
    have hxG' : x₀.1 ∈ S'.G.E := hRF'.2.2.2.2.2.1 hxE
    have hxG : x₀.1 ∈ S.G.E := hRF.2.2.2.2.2.1 hxF
    have hend := stepProj_applyUpdate_eq hI.hG_val hu hxG (hG'_eq ▸ hxG')
    have hSub' := hRF'.2.2.2.2.2.2 x₀.1 hxE
    have hSub := hRF.2.2.2.2.2.2 x₀.1 hxF
    have ht_eq' : S'.RF.F.tail x₀.1 = (S.G.applyUpdate u).tail x₀.1 := by rw [hSub'.1, ← hG'_eq]
    have hh_eq' : S'.RF.F.head x₀.1 = (S.G.applyUpdate u).head x₀.1 := by rw [hSub'.2, ← hG'_eq]
    have hte : S.RF.F.tail x₀.1 = stepProj u (S'.RF.F.tail x₀.1) := by
      rw [hSub.1, ← hend.1, ← ht_eq']
    have hhe : S.RF.F.head x₀.1 = stepProj u (S'.RF.F.head x₀.1) := by
      rw [hSub.2, ← hend.2, ← hh_eq']
    have hsrc_proj : S.RF.F.src x₀ = stepProj u a := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hte, hhe]
    have hdst_proj : S.RF.F.dst x₀ = stepProj u (S'.RF.F.dst x₀) := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hte, hhe]
    exact .cons hxF hsrc_proj (by simpa [hdst_proj] using ih)

lemma stepProj_old_V {S : LSFState} {u : Update} (hu : S.G.UpdateIsValid u)
    {x : ℕ} (hx : x ∈ S.G.V) : stepProj u x = x := by
  cases u with
  | delete _ => rfl
  | insert _ _ _ => rfl
  | split _ v' _ _ =>
    have hne : x ≠ v' := fun h => hu.2.1 (h ▸ hx)
    simp [stepProj, hne]

lemma root_eq_of_new_root_eq {thresh K_σ thresh' K_σ' : ℝ} {ℓ₀ : ℕ → ℝ}
    {S S' : LSFState} {u : Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hu : S.G.UpdateIsValid u)
    (hI' : LSFInvWith thresh' K_σ' ℓ₀ S') (hS' : S' = applyLSFUpdate S u)
    {x y : ℕ} (hx : x ∈ S.G.V) (hy : y ∈ S.G.V) (hrt : S'.RF.root x = S'.RF.root y) :
    S.RF.root x = S.RF.root y := by
  have hRF := lsfInv_to_RS hI
  have hRF' := lsfInv_to_RS hI'
  have hS'G : S'.G = S.G.applyUpdate u := by rw [hS']; exact (applyLSFUpdate_inv_with hI hu).2.1
  have hV_sub : S.G.V ⊆ S'.G.V := by
    rw [hS'G]
    cases u with
    | delete _ => exact Finset.Subset.rfl
    | insert _ _ _ => exact Finset.Subset.rfl
    | split _ v' _ _ => exact Finset.subset_insert v' S.G.V
  obtain ⟨Px, hPx⟩ := (rootedForest_root_spec hRF' (hV_sub hx)).2
  obtain ⟨Py, hPy⟩ := (rootedForest_root_spec hRF' (hV_sub hy)).2
  have hconn' : S'.RF.F.Connected x y := ⟨Px ++ walkRev Py, IsWalk.append hPx (hrt ▸ isWalk_walkRev hPy)⟩
  have hconn := forest_connected_stepProj hI hu hI' hS' hconn'
  rw [stepProj_old_V hu hx, stepProj_old_V hu hy] at hconn
  exact rootedForest_root_eq_of_connected hRF hx hy hconn

lemma delStepC_splitStepA_spec {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {u : Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    {C : MGraph} (hC_val : C.IsValid)
    (hCE_sub : C.E ⊆ S.G.E \ S.RF.F.E)
    {m_prev : ℕ → ℕ} (hV_sub : ∀ x ∈ S.G.V, m_prev x ∈ C.V)
    (hEnds : ∀ e ∈ C.E, C.tail e = m_prev (S.G.tail e) ∧ C.head e = m_prev (S.G.head e))
    (hRPI : RootPieceInv S₀ S m_prev)
    {nextVid : ℕ} (hFresh : ∀ v ∈ C.V, v < nextVid) :
    let S' := applyLSFUpdate S u
    let U_del := delStepC C u
    let C_del := C.applyBatch U_del
    let spA := splitStepA m_prev S.G C_del u nextVid
    let C_mid := C_del.applyBatch spA.1
    U_del.length ≤ (match u with | .delete _ => 1 | _ => 0) ∧
    spA.1.length ≤ (match u with | .split _ _ _ _ => 1 | _ => 0) ∧
    C.BatchIsValid (U_del ++ spA.1) ∧
    C_mid.IsValid ∧
    C_mid.E ⊆ S'.G.E \ S'.RF.F.E ∧
    (∀ x ∈ S'.G.V, spA.2.1 x ∈ C_mid.V) ∧
    (∀ e ∈ C_mid.E, C_mid.tail e = spA.2.1 (S'.G.tail e) ∧ C_mid.head e = spA.2.1 (S'.G.head e)) ∧
    (∀ v ∈ C_mid.V, v < spA.2.2) ∧
    nextVid ≤ spA.2.2 ∧
    (∀ x ∈ S'.G.V, ∀ y ∈ S'.G.V,
      spA.2.1 x = spA.2.1 y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W))) := by
  have hsp := applyLSFUpdate_inv_with hI hu
  have hS'G := hsp.2.1
  have hFE_sub := hsp.2.2.2.2.2.2.2.2.2.1
  cases u with
  | delete e₀ =>
    dsimp only [delStepC, splitStepA]
    split_ifs with he₀
    · have hu_val : C.UpdateIsValid (.delete e₀) := he₀
      have hU_val : C.BatchIsValid [.delete e₀] := ⟨hu_val, trivial⟩
      have hC_mid_val : (C.applyBatch [.delete e₀]).IsValid :=
        applyUpdate_isValid hC_val hu_val
      refine ⟨le_rfl, le_rfl, ?_, hC_mid_val, ?_, ?_, ?_, ?_, le_rfl, ?_⟩
      · simpa [MGraph.applyBatch] using hU_val
      · intro e he
        simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
          Finset.mem_erase] at he
        have he_sub := Finset.mem_sdiff.mp (hCE_sub he.2)
        refine Finset.mem_sdiff.mpr ⟨?_, fun hf => he_sub.2 (hFE_sub hf)⟩
        rw [hS'G]; exact Finset.mem_erase.mpr ⟨he.1, he_sub.1⟩
      · intro x hx
        rw [hS'G] at hx
        simpa [MGraph.applyBatch, MGraph.applyUpdate] using hV_sub x hx
      · intro e he
        simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
          Finset.mem_erase] at he ⊢
        rw [hS'G]
        exact hEnds e he.2
      · intro w hw
        simpa [MGraph.applyBatch, MGraph.applyUpdate] using hFresh w hw
      · intro x hx y hy
        rw [hS'G] at hx hy
        exact hRPI x hx y hy
    · simp only [MGraph.applyBatch, List.foldl_nil]
      refine ⟨by simp, le_rfl, trivial, hC_val, ?_, ?_, ?_, hFresh, le_rfl, ?_⟩
      · intro e he
        have he_sub := Finset.mem_sdiff.mp (hCE_sub he)
        refine Finset.mem_sdiff.mpr ⟨?_, fun hf => he_sub.2 (hFE_sub hf)⟩
        rw [hS'G]; exact Finset.mem_erase.mpr ⟨fun h => he₀ (h ▸ he), he_sub.1⟩
      · intro x hx; rw [hS'G] at hx; exact hV_sub x hx
      · intro e he; rw [hS'G]; exact hEnds e he
      · intro x hx y hy; rw [hS'G] at hx hy; exact hRPI x hx y hy
  | insert e₀ a b =>
    dsimp only [delStepC, splitStepA]
    refine ⟨le_rfl, le_rfl, trivial, hC_val, ?_, ?_, ?_, hFresh, le_rfl, ?_⟩
    · intro e he
      have he_sub := Finset.mem_sdiff.mp (hCE_sub he)
      refine Finset.mem_sdiff.mpr ⟨?_, fun hf => he_sub.2 (hFE_sub hf)⟩
      rw [hS'G]; exact Finset.mem_insert_of_mem he_sub.1
    · intro x hx; rw [hS'G] at hx; exact hV_sub x hx
    · intro e he
      have he_sub := Finset.mem_sdiff.mp (hCE_sub he)
      have hne : e ≠ e₀ := fun h => hu.1 (h ▸ he_sub.1)
      rw [hS'G]
      simp [MGraph.applyBatch, MGraph.applyUpdate, Function.update_of_ne hne, hEnds e he]
    · intro x hx y hy; rw [hS'G] at hx hy; exact hRPI x hx y hy
  | split v v' St Sh =>
    dsimp only [delStepC, splitStepA]
    have hv_mem : v ∈ S.G.V := hu.1
    have hv'_not : v' ∉ S.G.V := hu.2.1
    have hmv_mem : m_prev v ∈ C.V := hV_sub v hv_mem
    have hnv_not : nextVid ∉ C.V := fun h => absurd (hFresh nextVid h) (lt_irrefl _)
    let St_A := C.E.filter fun e => e ∈ St ∧ S.G.tail e = v
    let Sh_A := C.E.filter fun e => e ∈ Sh ∧ S.G.head e = v
    have hEs_sub : St_A ∪ Sh_A ⊆ C.E :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hEs_inc : ∀ e ∈ St_A ∪ Sh_A, C.tail e = m_prev v ∨ C.head e = m_prev v := by
      intro e he
      rcases Finset.mem_union.mp he with heT | heH
      · rw [Finset.mem_filter] at heT
        left; exact (hEnds e heT.1).1.trans (congrArg m_prev heT.2.2)
      · rw [Finset.mem_filter] at heH
        right; exact (hEnds e heH.1).2.trans (congrArg m_prev heH.2.2)
    have hu_split_val : C.UpdateIsValid (.split (m_prev v) nextVid St_A Sh_A) :=
      ⟨hmv_mem, hnv_not, hEs_sub, hEs_inc⟩
    have hBV : C.BatchIsValid [.split (m_prev v) nextVid St_A Sh_A] := ⟨hu_split_val, trivial⟩
    have hC_mid_val : (C.applyBatch [.split (m_prev v) nextVid St_A Sh_A]).IsValid :=
      applyUpdate_isValid hC_val hu_split_val
    have hC_mid_tail : ∀ e ∈ C.E,
        (C.applyBatch [.split (m_prev v) nextVid St_A Sh_A]).tail e =
          Function.update m_prev v' nextVid ((S.G.applyUpdate (.split v v' St Sh)).tail e) := by
      intro e he
      have heS : e ∈ S.G.E := (Finset.mem_sdiff.mp (hCE_sub he)).1
      have ht_ne_v' : S.G.tail e ≠ v' := fun h => hv'_not (h ▸ (hI.hG_val e heS).1)
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        St_A, Finset.mem_filter, he, true_and]
      by_cases htv : e ∈ St ∧ S.G.tail e = v
      · have hCt : C.tail e = m_prev v := (hEnds e he).1.trans (congrArg m_prev htv.2)
        simp only [htv.1, htv.2, hCt, and_self, ↓reduceIte, Function.update_self]
      · simp only [htv, false_and, ↓reduceIte, Function.update_of_ne ht_ne_v', (hEnds e he).1]
    have hC_mid_head : ∀ e ∈ C.E,
        (C.applyBatch [.split (m_prev v) nextVid St_A Sh_A]).head e =
          Function.update m_prev v' nextVid ((S.G.applyUpdate (.split v v' St Sh)).head e) := by
      intro e he
      have heS : e ∈ S.G.E := (Finset.mem_sdiff.mp (hCE_sub he)).1
      have hh_ne_v' : S.G.head e ≠ v' := fun h => hv'_not (h ▸ (hI.hG_val e heS).2)
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Sh_A, Finset.mem_filter, he, true_and]
      by_cases hhv : e ∈ Sh ∧ S.G.head e = v
      · have hCh : C.head e = m_prev v := (hEnds e he).2.trans (congrArg m_prev hhv.2)
        simp only [hhv.1, hhv.2, hCh, and_self, ↓reduceIte, Function.update_self]
      · simp only [hhv, false_and, ↓reduceIte, Function.update_of_ne hh_ne_v', (hEnds e he).2]
    refine ⟨by simp, le_rfl, ?_, hC_mid_val, ?_, ?_, ?_, ?_, Nat.le_succ _, ?_⟩
    · simpa [MGraph.applyBatch] using hBV
    · intro e he
      have he_sub := Finset.mem_sdiff.mp (hCE_sub he)
      refine Finset.mem_sdiff.mpr ⟨?_, fun hf => he_sub.2 (hFE_sub hf)⟩
      rw [hS'G]; exact he_sub.1
    · intro x hx
      rw [hS'G] at hx
      dsimp only [MGraph.applyUpdate] at hx
      rw [Finset.mem_insert] at hx
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Finset.mem_insert]
      rcases hx with hxv | hxS
      · left; subst hxv; simp
      · right
        have hx_ne : x ≠ v' := fun h => hv'_not (h ▸ hxS)
        rw [Function.update_of_ne hx_ne]; exact hV_sub x hxS
    · intro e he
      rw [hS'G]
      exact ⟨hC_mid_tail e he, hC_mid_head e he⟩
    · intro w hw
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Finset.mem_insert] at hw
      rcases hw with rfl | hwC
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hFresh w hwC)
    · intro x hx y hy
      rw [hS'G] at hx hy
      dsimp only [MGraph.applyUpdate] at hx hy
      rw [Finset.mem_insert] at hx hy
      have hS₀_sub : S₀.G.V ⊆ S.G.V := by
        rw [hD.hS₀_G, ← hD.hG₀_eq, ← hI.hTV, hI.hGV_eq]; exact Finset.subset_union_left
      rcases hx with hxv | hxS <;> rcases hy with hyv | hyS
      · subst hxv; subst hyv; simp
      · have hy_ne : y ≠ v' := fun h => hv'_not (h ▸ hyS)
        have hne : Function.update m_prev v' nextVid x ≠
            Function.update m_prev v' nextVid y := by
          rw [hxv, Function.update_self, Function.update_of_ne hy_ne]
          intro h; exact hnv_not (h ▸ hV_sub y hyS)
        simp only [hne, false_iff]
        rintro (hxy | ⟨hx₀, _, _⟩)
        · exact hy_ne (hxy.symm.trans hxv)
        · exact hv'_not (hS₀_sub (hxv ▸ hx₀))
      · have hx_ne : x ≠ v' := fun h => hv'_not (h ▸ hxS)
        have hne : Function.update m_prev v' nextVid x ≠
            Function.update m_prev v' nextVid y := by
          rw [hyv, Function.update_self, Function.update_of_ne hx_ne]
          intro h; exact hnv_not (h.symm ▸ hV_sub x hxS)
        simp only [hne, false_iff]
        rintro (hxy | ⟨_, hy₀, _⟩)
        · exact hx_ne (hxy.trans hyv)
        · exact hv'_not (hS₀_sub (hyv ▸ hy₀))
      · have hx_ne : x ≠ v' := fun h => hv'_not (h ▸ hxS)
        have hy_ne : y ≠ v' := fun h => hv'_not (h ▸ hyS)
        rw [Function.update_of_ne hx_ne, Function.update_of_ne hy_ne]
        exact hRPI x hxS y hyS

/-- Target `(r', ṽ)` pairs in Step 3b that actually split an equivalence class. -/
noncomputable def splitTargets (S S' : LSFState) (C_mid : MGraph) (m_mid : ℕ → ℕ) :
    Finset (ℕ × ℕ) :=
  open Classical in
  ((S'.R \ S.R) ×ˢ C_mid.V).filter fun p =>
    (∃ x ∈ S'.G.V, m_mid x = p.2 ∧ S'.RF.root x = p.1) ∧
    (∃ y ∈ S'.G.V, m_mid y = p.2 ∧ S'.RF.root y ≠ p.1)

/-- Lookup fresh vertex ID assigned to `(r', vT)`. -/
def assocPairVid : List ((ℕ × ℕ) × ℕ) → ℕ × ℕ → Option ℕ
  | [], _ => none
  | (k, vid) :: rest, key => if key = k then some vid else assocPairVid rest key

/-- Lookup parent vertex `vT` assigned to fresh vertex `vid`. -/
def parentOfPairVid : List ((ℕ × ℕ) × ℕ) → ℕ → ℕ
  | [], _ => 0
  | ((_, vT), vid) :: rest, v => if v = vid then vT else parentOfPairVid rest v

lemma assocPairVid_some_iff {ps : List ((ℕ × ℕ) × ℕ)} (hnd_k : (ps.map Prod.fst).Nodup) :
    ∀ {k vid}, assocPairVid ps k = some vid ↔ (k, vid) ∈ ps := by
  induction ps with
  | nil => simp [assocPairVid]
  | cons p rest ih =>
    rcases p with ⟨k₀, vid₀⟩
    rw [List.map_cons, List.nodup_cons] at hnd_k
    intro k vid
    dsimp only [assocPairVid]
    by_cases hk : k = k₀
    · subst hk
      simp only [↓reduceIte, Option.some.injEq, List.mem_cons, Prod.mk.injEq, true_and]
      constructor
      · intro h; left; exact h.symm
      · rintro (rfl | hmem)
        · rfl
        · exact absurd (List.mem_map_of_mem (f := Prod.fst) hmem) hnd_k.1
    · simp only [hk, ↓reduceIte, List.mem_cons, Prod.mk.injEq, false_and, false_or]
      exact ih hnd_k.2

lemma parentOfPairVid_eq {ps : List ((ℕ × ℕ) × ℕ)} (hnd_v : (ps.map Prod.snd).Nodup) :
    ∀ {k vid}, (k, vid) ∈ ps → parentOfPairVid ps vid = k.2 := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨⟨r₀, vT₀⟩, vid₀⟩
    rw [List.map_cons, List.nodup_cons] at hnd_v
    intro ⟨r, vT⟩ vid hmem
    dsimp only [parentOfPairVid]
    rcases List.mem_cons.mp hmem with hhead | hrest
    · cases hhead
      simp
    · have hne : vid ≠ vid₀ := fun h => hnd_v.1 (List.mem_map.mpr ⟨_, hrest, h⟩)
      simp only [hne, ↓reduceIte]
      exact ih hnd_v.2 hrest

lemma assocPairVid_mem_snd {ps : List ((ℕ × ℕ) × ℕ)} {k vid}
    (h : assocPairVid ps k = some vid) : ∃ p ∈ ps, p.2 = vid := by
  induction ps with
  | nil => simp [assocPairVid] at h
  | cons q rest ih =>
    rcases q with ⟨qk, qv⟩
    dsimp only [assocPairVid] at h
    split_ifs at h with hq
    · rw [Option.some.injEq] at h
      exact ⟨(qk, qv), List.mem_cons_self, h⟩
    · obtain ⟨p, hp, hpe⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpe⟩

lemma assocPairVid_inj_vid {ps : List ((ℕ × ℕ) × ℕ)} (hnd_v : (ps.map Prod.snd).Nodup)
    {k₁ k₂ vid} (h1 : assocPairVid ps k₁ = some vid) (h2 : assocPairVid ps k₂ = some vid) :
    k₁ = k₂ := by
  induction ps with
  | nil => simp [assocPairVid] at h1
  | cons p rest ih =>
    rcases p with ⟨k₀, vid₀⟩
    rw [List.map_cons, List.nodup_cons] at hnd_v
    dsimp only [assocPairVid] at h1 h2
    split_ifs at h1 h2 with c1 c2
    · exact c1.trans c2.symm
    · rw [Option.some.injEq] at h1
      subst h1
      obtain ⟨q, hq, rfl⟩ := assocPairVid_mem_snd h2
      exact absurd (List.mem_map_of_mem (f := Prod.snd) hq) hnd_v.1
    · rw [Option.some.injEq] at h2
      subst h2
      obtain ⟨q, hq, rfl⟩ := assocPairVid_mem_snd h1
      exact absurd (List.mem_map_of_mem (f := Prod.snd) hq) hnd_v.1
    · exact ih hnd_v.2 h1 h2

lemma zipIdx_map_fst_eq {α : Type*} (l : List α) (k : ℕ) : (l.zipIdx k).map Prod.fst = l := by
  induction l generalizing k with
  | nil => rfl
  | cons a rest ih => simp [List.zipIdx_cons, ih]

lemma zipIdx_mem_snd_bounds {α : Type*} {l : List α} {k : ℕ} {p : α × ℕ}
    (hp : p ∈ l.zipIdx k) : k ≤ p.2 ∧ p.2 < k + l.length := by
  induction l generalizing k with
  | nil => simp at hp
  | cons a rest ih =>
    rw [List.zipIdx_cons, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · exact ⟨le_rfl, by simp⟩
    · obtain ⟨h1, h2⟩ := ih hrest
      exact ⟨le_trans (Nat.le_succ _) h1, by simp; omega⟩

lemma zipIdx_map_snd_nodup {α : Type*} (l : List α) (k : ℕ) :
    ((l.zipIdx k).map Prod.snd).Nodup := by
  induction l generalizing k with
  | nil => simp
  | cons a rest ih =>
    rw [List.zipIdx_cons, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (k + 1)⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨q, hq, hqk⟩ := hmem
    have hb := (zipIdx_mem_snd_bounds hq).1
    omega

/-- Step 3b: partition non-uniform equivalence classes of `m_mid` under `S'.RF.root`. -/
noncomputable def rootSplitStep (S S' : LSFState) (C_mid : MGraph) (m_mid : ℕ → ℕ)
    (nextVid : ℕ) : List Update × (ℕ → ℕ) × ℕ :=
  let tgts := (splitTargets S S' C_mid m_mid).toList
  let pairs := tgts.zipIdx nextVid
  let m_next : ℕ → ℕ := fun x =>
    match assocPairVid pairs (S'.RF.root x, m_mid x) with
    | some vid => vid
    | none => m_mid x
  let splits := (pairs.map Prod.snd).map fun vid =>
    Update.split (parentOfPairVid pairs vid) vid
      (C_mid.E.filter fun e => m_next (S'.G.tail e) = vid)
      (C_mid.E.filter fun e => m_next (S'.G.head e) = vid)
  (splits, m_next, nextVid + tgts.length)

lemma rootSplitStep_spec {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {u : Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    {C_mid : MGraph} (hC_val : C_mid.IsValid)
    {m_mid : ℕ → ℕ}
    (hV_sub : ∀ x ∈ (applyLSFUpdate S u).G.V, m_mid x ∈ C_mid.V)
    (hEnds : ∀ e ∈ C_mid.E,
      C_mid.tail e = m_mid ((applyLSFUpdate S u).G.tail e) ∧
      C_mid.head e = m_mid ((applyLSFUpdate S u).G.head e))
    (hMidInv : ∀ x ∈ (applyLSFUpdate S u).G.V, ∀ y ∈ (applyLSFUpdate S u).G.V,
      m_mid x = m_mid y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W)))
    {nextVid : ℕ} (hFresh : ∀ v ∈ C_mid.V, v < nextVid) :
    let S' := applyLSFUpdate S u
    let spB := rootSplitStep S S' C_mid m_mid nextVid
    let C' := C_mid.applyBatch spB.1
    spB.1.length = (splitTargets S S' C_mid m_mid).card ∧
    C_mid.BatchIsValid spB.1 ∧
    C'.IsValid ∧
    C'.E = C_mid.E ∧
    (∀ x ∈ S'.G.V, spB.2.1 x ∈ C'.V) ∧
    (∀ e ∈ C'.E, C'.tail e = spB.2.1 (S'.G.tail e) ∧ C'.head e = spB.2.1 (S'.G.head e)) ∧
    (∀ v ∈ C'.V, v < spB.2.2) ∧
    nextVid ≤ spB.2.2 ∧
    RootPieceInv S₀ S' spB.2.1 := by
  intro S' spB C'
  have hsp := applyLSFUpdate_inv_with hI hu
  have hI' := hsp.1
  have hS'G := hsp.2.1
  have hD' := lsfDerivedFrom_step hI hu hD
  have hRF' := lsfInv_to_RS hI'
  have hRF := lsfInv_to_RS hI
  set tgts := (splitTargets S S' C_mid m_mid).toList
  set pairs := tgts.zipIdx nextVid
  set vids := pairs.map Prod.snd
  have hnd_tgts : tgts.Nodup := Finset.nodup_toList _
  have hnd_fst : (pairs.map Prod.fst).Nodup := by
    rw [zipIdx_map_fst_eq]; exact hnd_tgts
  have hnd_vids : vids.Nodup := zipIdx_map_snd_nodup tgts nextVid
  have hdisj : ∀ vid ∈ vids, vid ∉ C_mid.V := by
    intro vid hvid hmem
    rw [List.mem_map] at hvid
    obtain ⟨q, hq, rfl⟩ := hvid
    have hb := (zipIdx_mem_snd_bounds hq).1
    have hlt := hFresh q.2 hmem
    omega
  have hvids_bounds : ∀ vid ∈ vids, nextVid ≤ vid ∧ vid < nextVid + tgts.length := by
    intro vid hvid
    rw [List.mem_map] at hvid
    obtain ⟨q, hq, rfl⟩ := hvid
    exact zipIdx_mem_snd_bounds hq
  have hparent : ∀ vid ∈ vids, parentOfPairVid pairs vid ∈ C_mid.V := by
    intro vid hvid
    rw [List.mem_map] at hvid
    obtain ⟨q, hq, rfl⟩ := hvid
    rw [parentOfPairVid_eq hnd_vids hq]
    have hq1_in : q.1 ∈ tgts := by
      have : q.1 ∈ pairs.map Prod.fst := List.mem_map_of_mem hq
      rwa [zipIdx_map_fst_eq] at this
    rw [Finset.mem_toList, splitTargets, Finset.mem_filter, Finset.mem_product] at hq1_in
    exact hq1_in.1.2
  have hspecT : ∀ e ∈ C_mid.E,
      (spB.2.1 (S'.G.tail e) ∈ C_mid.V ∧ spB.2.1 (S'.G.tail e) = C_mid.tail e) ∨
      (spB.2.1 (S'.G.tail e) ∈ vids ∧ parentOfPairVid pairs (spB.2.1 (S'.G.tail e)) = C_mid.tail e) := by
    intro e he
    have he_end := (hEnds e he).1
    dsimp only [spB, rootSplitStep]
    cases ha : assocPairVid pairs (S'.RF.root (S'.G.tail e), m_mid (S'.G.tail e)) with
    | none =>
      left
      refine ⟨?_, he_end.symm⟩
      rw [← he_end]
      exact (hC_val e he).1
    | some vid =>
      right
      have hmem : ((S'.RF.root (S'.G.tail e), m_mid (S'.G.tail e)), vid) ∈ pairs :=
        (assocPairVid_some_iff hnd_fst).mp ha
      refine ⟨List.mem_map_of_mem hmem, ?_⟩
      rw [parentOfPairVid_eq hnd_vids hmem]
      exact he_end.symm
  have hspecH : ∀ e ∈ C_mid.E,
      (spB.2.1 (S'.G.head e) ∈ C_mid.V ∧ spB.2.1 (S'.G.head e) = C_mid.head e) ∨
      (spB.2.1 (S'.G.head e) ∈ vids ∧ parentOfPairVid pairs (spB.2.1 (S'.G.head e)) = C_mid.head e) := by
    intro e he
    have he_end := (hEnds e he).2
    dsimp only [spB, rootSplitStep]
    cases ha : assocPairVid pairs (S'.RF.root (S'.G.head e), m_mid (S'.G.head e)) with
    | none =>
      left
      refine ⟨?_, he_end.symm⟩
      rw [← he_end]
      exact (hC_val e he).2
    | some vid =>
      right
      have hmem : ((S'.RF.root (S'.G.head e), m_mid (S'.G.head e)), vid) ∈ pairs :=
        (assocPairVid_some_iff hnd_fst).mp ha
      refine ⟨List.mem_map_of_mem hmem, ?_⟩
      rw [parentOfPairVid_eq hnd_vids hmem]
      exact he_end.symm
  have hsplit_spec := applyUpdate_split_list_spec hC_val hnd_vids hdisj hparent hspecT hspecH
  have hlen : spB.1.length = (splitTargets S S' C_mid m_mid).card := by
    dsimp only [spB, rootSplitStep]
    simp [List.length_map]
  have hm_next_eq_iff : ∀ x ∈ S'.G.V, ∀ y ∈ S'.G.V,
      spB.2.1 x = spB.2.1 y ↔ m_mid x = m_mid y ∧ S'.RF.root x = S'.RF.root y := by
    intro x hx y hy
    dsimp only [spB, rootSplitStep]
    cases hax : assocPairVid pairs (S'.RF.root x, m_mid x) with
    | some vx =>
      have hmx : ((S'.RF.root x, m_mid x), vx) ∈ pairs := (assocPairVid_some_iff hnd_fst).mp hax
      have hvx_bnd := hvids_bounds vx (List.mem_map_of_mem hmx)
      cases hay : assocPairVid pairs (S'.RF.root y, m_mid y) with
      | some vy =>
        simp only []
        constructor
        · rintro rfl
          have hpair := assocPairVid_inj_vid hnd_vids hax hay
          exact ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩
        · rintro ⟨hm, hrt⟩
          have hpair : (S'.RF.root x, m_mid x) = (S'.RF.root y, m_mid y) := Prod.ext hrt hm
          rw [hpair] at hax
          have : some vx = some vy := hax.symm.trans hay
          exact Option.some.inj this
      | none =>
        simp only []
        constructor
        · intro heq
          have hlt := hFresh _ (heq ▸ hV_sub y hy)
          omega
        · rintro ⟨hm, hrt⟩
          exfalso
          have hpair : (S'.RF.root x, m_mid x) = (S'.RF.root y, m_mid y) := Prod.ext hrt hm
          rw [← hpair, hax] at hay
          simp at hay
    | none =>
      cases hay : assocPairVid pairs (S'.RF.root y, m_mid y) with
      | some vy =>
        have hmy : ((S'.RF.root y, m_mid y), vy) ∈ pairs := (assocPairVid_some_iff hnd_fst).mp hay
        have hvy_bnd := hvids_bounds vy (List.mem_map_of_mem hmy)
        simp only []
        constructor
        · intro heq
          have hlt := hFresh _ (heq.symm ▸ hV_sub x hx)
          omega
        · rintro ⟨hm, hrt⟩
          exfalso
          have hpair : (S'.RF.root x, m_mid x) = (S'.RF.root y, m_mid y) := Prod.ext hrt hm
          rw [hpair, hay] at hax
          simp at hax
      | none =>
        simp only []
        constructor
        · intro hm
          refine ⟨hm, ?_⟩
          by_contra hrt_ne
          rcases (hMidInv x hx y hy).mp hm with rfl | ⟨hx₀, hy₀, hrt_old, _, _⟩
          · exact hrt_ne rfl
          · have hS₀_sub_S : S₀.G.V ⊆ S.G.V := by
              rw [hD.hS₀_G, ← hD.hG₀_eq, ← hI.hTV, hI.hGV_eq]; exact Finset.subset_union_left
            have hxS : x ∈ S.G.V := hS₀_sub_S hx₀
            have hyS : y ∈ S.G.V := hS₀_sub_S hy₀
            have hx_not_old : ¬ (S'.RF.root x ∈ S.R ∧ S'.RF.root y ∈ S.R) := by
              rintro ⟨hrxS, hryS⟩
              have hrxV : S'.RF.root x ∈ S.G.V := lsfInv_R_sub_V hI hrxS
              have hryV : S'.RF.root y ∈ S.G.V := lsfInv_R_sub_V hI hryS
              have hcx := forest_connected_stepProj hI hu hI' rfl (rootedForest_root_spec hRF' hx).2
              have hcy := forest_connected_stepProj hI hu hI' rfl (rootedForest_root_spec hRF' hy).2
              rw [stepProj_old_V hu hxS, stepProj_old_V hu hrxV] at hcx
              rw [stepProj_old_V hu hyS, stepProj_old_V hu hryV] at hcy
              have heqx : S'.RF.root x = S.RF.root x :=
                (hRF.2.2.2.1 x hxS).unique ⟨hrxS, hcx⟩ (rootedForest_root_spec hRF hxS)
              have heqy : S'.RF.root y = S.RF.root y :=
                (hRF.2.2.2.1 y hyS).unique ⟨hryS, hcy⟩ (rootedForest_root_spec hRF hyS)
              exact hrt_ne (heqx.trans (hrt_old.trans heqy.symm))
            have hmem_tgt : (S'.RF.root x, m_mid x) ∈ splitTargets S S' C_mid m_mid ∨
                (S'.RF.root y, m_mid y) ∈ splitTargets S S' C_mid m_mid := by
              by_cases hrxS : S'.RF.root x ∈ S.R
              · right
                have hryS : S'.RF.root y ∉ S.R := fun h => hx_not_old ⟨hrxS, h⟩
                rw [splitTargets, Finset.mem_filter, Finset.mem_product]
                refine ⟨⟨Finset.mem_sdiff.mpr ⟨(rootedForest_root_spec hRF' hy).1, hryS⟩,
                  hV_sub y hy⟩, ⟨y, hy, rfl, rfl⟩, ⟨x, hx, hm, hrt_ne⟩⟩
              · left
                rw [splitTargets, Finset.mem_filter, Finset.mem_product]
                refine ⟨⟨Finset.mem_sdiff.mpr ⟨(rootedForest_root_spec hRF' hx).1, hrxS⟩,
                  hV_sub x hx⟩, ⟨x, hx, rfl, rfl⟩, ⟨y, hy, hm.symm, Ne.symm hrt_ne⟩⟩
            rcases hmem_tgt with htx | hty
            · have hin : (S'.RF.root x, m_mid x) ∈ pairs.map Prod.fst := by
                rw [zipIdx_map_fst_eq, Finset.mem_toList]; exact htx
              rw [List.mem_map] at hin
              obtain ⟨⟨k₀, v₀⟩, hmem_p, hk_eq⟩ := hin
              dsimp only at hk_eq
              rw [← hk_eq, (assocPairVid_some_iff hnd_fst).mpr hmem_p] at hax
              simp at hax
            · have hin : (S'.RF.root y, m_mid y) ∈ pairs.map Prod.fst := by
                rw [zipIdx_map_fst_eq, Finset.mem_toList]; exact hty
              rw [List.mem_map] at hin
              obtain ⟨⟨k₀, v₀⟩, hmem_p, hk_eq⟩ := hin
              dsimp only at hk_eq
              rw [← hk_eq, (assocPairVid_some_iff hnd_fst).mpr hmem_p] at hay
              simp at hay
        · rintro ⟨hm, _⟩; exact hm
  have hCE' : C'.E = C_mid.E := hsplit_spec.2.2.1
  have hCV' : C'.V = C_mid.V ∪ vids.toFinset := hsplit_spec.2.1
  have hEnds' : ∀ e ∈ C'.E,
      C'.tail e = spB.2.1 (S'.G.tail e) ∧ C'.head e = spB.2.1 (S'.G.head e) := by
    intro e he
    exact hsplit_spec.2.2.2.1 e (hCE' ▸ he)
  refine ⟨hlen, hsplit_spec.1, hsplit_spec.2.2.2.2, hCE',
    fun x hx => ?_, hEnds', fun v hv => ?_, by dsimp [spB, rootSplitStep]; exact Nat.le_add_right _ _,
    fun x hx y hy => ?_⟩
  · rw [hCV', Finset.mem_union]
    dsimp only [spB, rootSplitStep]
    cases ha : assocPairVid pairs (S'.RF.root x, m_mid x) with
    | some vid =>
      right
      rw [List.mem_toFinset]
      exact List.mem_map_of_mem ((assocPairVid_some_iff hnd_fst).mp ha)
    | none =>
      left
      exact hV_sub x hx
  · rw [hCV', Finset.mem_union] at hv
    rcases hv with hvM | hvV
    · dsimp only [spB, rootSplitStep]
      exact lt_of_lt_of_le (hFresh v hvM) (Nat.le_add_right _ _)
    · rw [List.mem_toFinset] at hvV
      exact (hvids_bounds v hvV).2
  · rw [hm_next_eq_iff x hx y hy]
    constructor
    · rintro ⟨hm, hrt'⟩
      rcases (hMidInv x hx y hy).mp hm with rfl | ⟨hx₀, hy₀, _, hRiff, hW⟩
      · left; rfl
      · right; exact ⟨hx₀, hy₀, hrt', hRiff, hW⟩
    · rintro (rfl | ⟨hx₀, hy₀, hrt', hRiff, hW⟩)
      · exact ⟨rfl, rfl⟩
      · have hS₀_sub_S : S₀.G.V ⊆ S.G.V := by
          rw [hD.hS₀_G, ← hD.hG₀_eq, ← hI.hTV, hI.hGV_eq]; exact Finset.subset_union_left
        have hrt_old := root_eq_of_new_root_eq hI hu hI' rfl (hS₀_sub_S hx₀) (hS₀_sub_S hy₀) hrt'
        exact ⟨(hMidInv x hx y hy).mpr (Or.inr ⟨hx₀, hy₀, hrt_old, hRiff, hW⟩), hrt'⟩


end

end MinCostFlow.SparseCore
