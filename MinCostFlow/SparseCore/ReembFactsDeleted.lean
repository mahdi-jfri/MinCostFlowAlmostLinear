module

public import MinCostFlow.SparseCore.ReembFactsStep
public import MinCostFlow.MinRatio.WireReembFacts

import Mathlib.Tactic

/-!
# Embedding change on re-inserted edges (`ReembFactsDeleted`)

Shows that on any valid ordered step `(U, ord')` from a nonempty state reached under
`SparseCoreOrdInput` for `sparseCoreBundleRestartToolMachWith` (and in particular
`sparseCoreProgTool`):

1. `mem_batchDeletes_of_inserts_in_G`: in any valid batch `U` on `G`, any edge `e ∈ G.E` inserted
   by `U` must also be deleted by `U` (`e ∈ batchDeletes U`).
2. `sparseCoreOrdInput_emb_mem_G_and_not_del`: every step `x` of `tr.emb e` for an off-spanner
   edge `e ∉ tr.S_cur.E` satisfies `x.1 ∈ G.E`, and after the step every step `x` of
   `info.state.emb e` for `e ∉ info.state.S_cur.E` satisfies `x.1 ∉ batchDeletes U`.
3. `sparseCoreOrdInput_emb_ne_of_inserts` and `progTool_emb_ne_of_inserts`: if `e` stays outside
   `S_cur` across the step and some step `x ∈ tr.emb e` is inserted by `U`, then
   `info.state.emb e ≠ tr.emb e`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.LSF
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.DynSpanner.Program

/-- In any valid batch `U` on `G`, if an edge `e ∈ G.E` is inserted by `U`, then `U` must also
delete `e` (`e ∈ batchDeletes U`). -/
theorem mem_batchDeletes_of_inserts_in_G :
    ∀ {G : MGraph} {U : List Update} {e : ℕ},
      G.BatchIsValid U → e ∈ G.E → (∃ u ∈ U, u.Inserts e) → e ∈ batchDeletes U
  | _, [], _, _, _, ⟨_, hu, _⟩ => absurd hu List.not_mem_nil
  | G, u :: rest, e, hBV, heG, ⟨u₀, hu₀, hIns⟩ => by
    obtain ⟨huV, hrestV⟩ := hBV
    cases u with
    | delete e₀ =>
      by_cases hEq : e = e₀
      · subst hEq; rw [mem_batchDeletes_iff]; exact ⟨.delete e, List.mem_cons_self, rfl⟩
      · rcases List.mem_cons.mp hu₀ with rfl | hmem
        · simp [Update.Inserts] at hIns
        · have heG' : e ∈ (G.applyUpdate (.delete e₀)).E := by
            simp [MGraph.applyUpdate, hEq, heG]
          have hrec := mem_batchDeletes_of_inserts_in_G hrestV heG' ⟨u₀, hmem, hIns⟩
          rw [mem_batchDeletes_iff] at hrec ⊢
          obtain ⟨u', hu', hEq'⟩ := hrec
          exact ⟨u', List.mem_cons_of_mem _ hu', hEq'⟩
    | insert e₀ a b =>
      rcases List.mem_cons.mp hu₀ with rfl | hmem
      · simp only [Update.Inserts] at hIns
        subst hIns
        exact absurd heG huV.1
      · have heG' : e ∈ (G.applyUpdate (.insert e₀ a b)).E := Finset.mem_insert_of_mem heG
        have hrec := mem_batchDeletes_of_inserts_in_G hrestV heG' ⟨u₀, hmem, hIns⟩
        rw [mem_batchDeletes_iff] at hrec ⊢
        obtain ⟨u', hu', hEq'⟩ := hrec
        exact ⟨u', List.mem_cons_of_mem _ hu', hEq'⟩
    | split v v' St Sh =>
      rcases List.mem_cons.mp hu₀ with rfl | hmem
      · simp [Update.Inserts] at hIns
      · have heG' : e ∈ (G.applyUpdate (.split v v' St Sh)).E := heG
        have hrec := mem_batchDeletes_of_inserts_in_G hrestV heG' ⟨u₀, hmem, hIns⟩
        rw [mem_batchDeletes_iff] at hrec ⊢
        obtain ⟨u', hu', hEq'⟩ := hrec
        exact ⟨u', List.mem_cons_of_mem _ hu', hEq'⟩

private lemma rotation_ext'' {G : MGraph} {ρ₁ ρ₂ : Rotation G} (h : ρ₁.order = ρ₂.order) :
    ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp only [Rotation.mk.injEq]; exact h

private lemma cast_rot_order'' {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ : Rotation G₁) :
    (h ▸ ρ : Rotation G₂).order = ρ.order := by
  cases h; rfl

private lemma cast_rotBatch'' {G₁ G₂ G₁' G₂' : MGraph} {U₁ U₂ : List Update} {c : ℕ}
    (h1 : G₁ = G₂) (h2 : G₁' = G₂') (hU : U₁ = U₂) (hG1 : G₁' = G₁.applyBatch U₁)
    (ρ : Rotation G₁) (σ : Rotation G₁')
    (hRB : RotationBatch c U₁ ρ (hG1 ▸ σ)) :
    RotationBatch c U₂ (h1 ▸ ρ)
      ((show G₂' = G₂.applyBatch U₂ by subst h1; subst h2; subst hU; exact hG1) ▸ (h2 ▸ σ)) := by
  subst h1; subst h2; subst hU; exact hRB

private lemma runOrdAfterUpdate_congr'' (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} :
    ∀ t,
      (∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
        ord₁ s = ord₂ s) →
      (∀ s < t, r₁ s = r₂ s) →
      T.runOrdAfterUpdate k M N D₁ ord₁ r₁ t = T.runOrdAfterUpdate k M N D₂ ord₂ r₂ t
  | 0, hD, _ => by
    have h0 := hD 0 le_rfl
    simp [SparseCoreRestartTool.runOrdAfterUpdate, h0.1, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2]
  | t + 1, hD, hr => by
    have ih := runOrdAfterUpdate_congr'' T k M N t
      (fun s hs => hD s (Nat.le_succ_of_le hs))
      (fun s hs => hr s (Nat.lt_succ_of_lt hs))
    have ht1 := hD (t + 1) le_rfl
    have hrt := hr t (Nat.lt_succ_self t)
    simp only [SparseCoreRestartTool.runOrdAfterUpdate, ih, hrt, ht1.2.1, ht1.2.2.1,
      ht1.2.2.2.1, ht1.2.2.2.2]

private lemma runOrdAfterRestarts_congr'' (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} (t : ℕ)
    (hD : ∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
      ord₁ s = ord₂ s)
    (hr : ∀ s ≤ t, r₁ s = r₂ s) :
    T.runOrdAfterRestarts k M N D₁ ord₁ r₁ t = T.runOrdAfterRestarts k M N D₂ ord₂ r₂ t := by
  simp only [SparseCoreRestartTool.runOrdAfterRestarts, hr t le_rfl,
    runOrdAfterUpdate_congr'' T k M N t hD (fun s hs => hr s hs.le)]

private lemma sparseCoreOrdInput_exists_run_step' (T : SparseCoreRestartTool) {k M N : ℕ}
    {s : T.State} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hinp : SparseCoreOrdInput T k M N s G ord n)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord') :
    ∃ (τ : ℕ) (D' : DynamicInstance) (ordSeq' : ℕ → ℕ → List End) (restarts' : ℕ → List ℕ),
      (D'.G 0).IsValid ∧ (D'.G 0).m ≤ M ∧ (D'.G 0).n ≤ N ∧
      (∀ e ∈ (D'.G 0).E, 0 < D'.ℓ 0 e) ∧
      D'.IsValid (τ + 1) ∧ OrderedUpTo D' (τ + 1) 2 ordSeq' ∧
      D'.G τ = G ∧ D'.U (τ + 1) = U ∧ ordSeq' τ = ord ∧ ordSeq' (τ + 1) = ord' ∧
      restarts' (τ + 1) = [] ∧
      T.runOrdAfterRestarts k M N D' ordSeq' restarts' τ = s := by
  obtain ⟨τ, D, ordSeq, restarts, hG0, hm0, hn0, hℓ0, hD, hOrd, hGτ, hordτ, _, _, hrun⟩ :=
    sparseCoreOrdInput_exists_run T hinp
  let D' : DynamicInstance :=
    { G := fun t => if t ≤ τ then D.G t else G.applyBatch U
      U := fun t => if t ≤ τ then D.U t else U
      g := fun t => if t ≤ τ then D.g t else fun _ => 0
      ℓ := fun t => if t ≤ τ then D.ℓ t else fun _ => 1 }
  let ordSeq' : ℕ → ℕ → List End := fun t => if t ≤ τ then ordSeq t else ord'
  let restarts' : ℕ → List ℕ := fun t => if t ≤ τ then restarts t else []
  have hagree : ∀ t ≤ τ, D'.G t = D.G t ∧ D'.U t = D.U t ∧ D'.ℓ t = D.ℓ t ∧ D'.g t = D.g t ∧
      ordSeq' t = ordSeq t := fun t ht => by simp [D', ordSeq', ht]
  have hD'_val : D'.IsValid (τ + 1) := by
    intro t ht1 ht2
    by_cases ht : t ≤ τ
    · have h1 := hD t ht1 ht
      have htm : t - 1 ≤ τ := by omega
      simp only [D', ht, htm, ↓reduceIte]
      exact h1
    · have hteq : t = τ + 1 := by omega
      subst hteq
      have hnot : ¬ (τ + 1 ≤ τ) := by omega
      simp only [D', hnot, Nat.add_sub_cancel, le_refl, ↓reduceIte, hGτ]
      exact ⟨hBV, trivial⟩
  have hOrd' : OrderedUpTo D' (τ + 1) 2 ordSeq' := by
    obtain ⟨ρ, hρ_ord, hρ_step⟩ := hOrd
    obtain ⟨ρU, σU, hρU, hσU, hRB⟩ := hOrdB
    let ρ' : ∀ t, Rotation (D'.G t) := fun t =>
      if ht : t ≤ τ then
        (show D.G t = D'.G t by simp [D', ht]) ▸ ρ t
      else
        (show G.applyBatch U = D'.G t by simp [D', ht]) ▸ σU
    refine ⟨ρ', fun t ht => ?_, fun t ht => ?_⟩
    · by_cases hle : t ≤ τ
      · have h1 : (ρ' t).order = (ρ t).order := by
          dsimp only [ρ']
          rw [dite_eq_left_of_eq_true (eq_true hle)]
          exact cast_rot_order'' _ _
        rw [h1, hρ_ord t hle]; simp [ordSeq', hle]
      · have h1 : (ρ' t).order = σU.order := by
          dsimp only [ρ']
          rw [dite_eq_right_of_eq_false (eq_false hle)]
          exact cast_rot_order'' _ _
        rw [h1, hσU]; simp [ordSeq', hle]
    · by_cases hlt : t < τ
      · have ht_le : t ≤ τ := hlt.le
        have ht1_le : t + 1 ≤ τ := hlt
        obtain ⟨hGstep, hstep⟩ := hρ_step t hlt
        have hGeq : D'.G (t + 1) = (D'.G t).applyBatch (D'.U (t + 1)) := by
          simp only [D', ht_le, ht1_le, ↓reduceIte]; exact hGstep
        refine ⟨hGeq, ?_⟩
        have hD't : D.G t = D'.G t := by simp [D', ht_le]
        have hD't1 : D.G (t + 1) = D'.G (t + 1) := by simp [D', ht1_le]
        have hD'U : D.U (t + 1) = D'.U (t + 1) := by simp [D', ht1_le]
        dsimp only [ρ']
        rw [dite_eq_left_of_eq_true (eq_true ht_le), dite_eq_left_of_eq_true (eq_true ht1_le)]
        exact cast_rotBatch'' hD't hD't1 hD'U hGstep (ρ t) (ρ (t + 1)) hstep
      · have hteq : t = τ := by omega
        subst t
        have hnot : ¬ (τ + 1 ≤ τ) := by omega
        have hGeq : D'.G (τ + 1) = (D'.G τ).applyBatch (D'.U (τ + 1)) := by
          simp [D', hnot, hGτ]
        refine ⟨hGeq, ?_⟩
        have hD't : D.G τ = D'.G τ := by simp [D']
        have hD't1 : G.applyBatch U = D'.G (τ + 1) := by simp [D', hnot]
        have hD'U : U = D'.U (τ + 1) := by simp [D', hnot]
        dsimp only [ρ']
        rw [dite_eq_left_of_eq_true (eq_true le_rfl), dite_eq_right_of_eq_false (eq_false hnot)]
        have hρ_eq : ρ τ = hGτ.symm ▸ ρU := by
          apply rotation_ext''
          rw [cast_rot_order'', hρU, hρ_ord τ le_rfl, hordτ]
        have hRB0 : RotationBatch 2 U ρU ((rfl : G.applyBatch U = G.applyBatch U) ▸ σU) := hRB
        have hRB1 := cast_rotBatch'' (hGτ.symm.trans hD't) hD't1 hD'U rfl ρU σU hRB0
        have hcast : (hGτ.symm.trans hD't) ▸ ρU = hD't ▸ ρ τ := by
          rw [hρ_eq]; cases hGτ; rfl
        rwa [hcast] at hRB1
  have hrun_τ : T.runOrdAfterRestarts k M N D' ordSeq' restarts' τ = s := by
    have hprev := runOrdAfterRestarts_congr'' T k M N (r₁ := restarts') (r₂ := restarts) τ hagree
      (fun s hs => by dsimp only [restarts']; simp [hs])
    exact hprev.trans hrun
  have hnot : ¬ (τ + 1 ≤ τ) := by omega
  refine ⟨τ, D', ordSeq', restarts', by simpa [D'] using hG0, by simpa [D'] using hm0,
    by simpa [D'] using hn0, by simpa [D'] using hℓ0, hD'_val, hOrd',
    by simp [D', hGτ], by simp [D', hnot], by simp [ordSeq', hordτ], by simp [ordSeq', hnot],
    by simp [restarts', hnot], hrun_τ⟩

/-- On a nonempty state `s` reached under `SparseCoreOrdInput` for
`sparseCoreBundleRestartToolMachWith`, across any valid ordered step `(U, ord')`:
- every edge appearing in `tr.emb e` for `e ∉ tr.S_cur.E` lies in `G.E`;
- every edge appearing in `info.state.emb e` for `e ∉ info.state.S_cur.E` lies outside
  `batchDeletes U`. -/
theorem sparseCoreOrdInput_emb_mem_G_and_not_del
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N n j : ℕ) (hk : 1 ≤ k) (hSp : SparsifySpec M P_b (sparsify M))
    (s : SparseCoreBundleState L) (G : MGraph) (ord : ℕ → List End)
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hne : s.isNonempty = true)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let tr := s.trees j
    let info := stepBundleTree sparsify tr U s.ord ord'
    (∀ e, e ∉ tr.S_cur.E → ∀ x ∈ tr.emb e, x.1 ∈ G.E) ∧
    (∀ e, e ∉ info.state.S_cur.E → ∀ x ∈ info.state.emb e, x.1 ∉ batchDeletes U) := by
  classical
  intro tr info
  let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
  let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  obtain ⟨_, hord_s, _⟩ := asm_input_inv lsfInit C_lsst L sparsify params spanConst hinp
  have hs_ord : SparseCoreBundleState.ord (L := L) s = ord := hord_s hne
  obtain ⟨τ, D', ordSeq', restarts', hG₀, hM, hN, hℓ₀, hD', hOrd', hGτ, hU_eq, hord_τ, hord_τ1,
      _, hrun_τ⟩ :=
    sparseCoreOrdInput_exists_run_step' Tm hinp U ord' hBV hOrdB
  have hNM_τ := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D' ordSeq' restarts' τ).2.2
  rw [hrun_τ] at hNM_τ
  have hV₀ : (D'.G 0).V.Nonempty := by
    have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D' ordSeq' restarts' τ).2.1
    rw [← hNM_τ.isNonempty, hne] at h1
    exact of_decide_eq_true h1.symm
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N (τ + 1) hk D' ordSeq' restarts' hG₀ hV₀ hℓ₀ hD' hOrd' j hInit
  have hBun_τ := hBun τ (Nat.le_succ τ)
  have hBun_τ1 := hBun (τ + 1) le_rfl
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D'.G 0) (D'.ℓ 0) (ordSeq' 0) j
  set pre := (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' τ).1.trees j
  set post := (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).trees j
  set pre' := (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' (τ + 1)).1.trees j
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' τ).1 (restarts' τ)).2.2.2.2.1 j
  have hEq : BundleNonMachEq tr post := hNM_τ.trees j
  have hne_post : (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).isNonempty = true :=
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D' ordSeq' restarts' τ).2.1.trans
      (decide_eq_true hV₀)
  have hord_post : (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).ord = ord := by
    have h1 := ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D' ordSeq' restarts' τ).2.2.2.2 hV₀).2
    exact h1.trans hord_τ
  set infoB := stepBundleTree sparsify post U ord ord'
  have hpre'_eq : pre' = infoB.state := by
    dsimp only [pre', Tb, infoB]
    rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
      sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_post, hord_post, hU_eq, hord_τ1]
  have hStepNM := BundleNonMachEq.step sparsify hEq U ord ord'
  have hinfo_eq : info = stepBundleTree sparsify tr U ord ord' := by
    dsimp only [info]; rw [hs_ord]
  have hEq' : BundleNonMachEq info.state pre' := by
    rw [hinfo_eq, hpre'_eq]; exact hStepNM.1
  set s₀ := bundleLastRestart restarts' j τ
  obtain ⟨hs₀_le, hs₀_cases, hs₀_none⟩ := bundleLastRestart_spec restarts' j τ
  have hNoRest : ∀ r, s₀ < r → r < τ + 1 → j ∉ restarts' r := fun r h1 h2 =>
    hs₀_none r h1 (Nat.lt_succ_iff.mp h2)
  set ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D' ordSeq' restarts' s₀ (τ + 1) j
  have hEpEq := epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D' ordSeq' restarts'
    s₀ (τ + 1) j (by omega)
  have hDynAll := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N (τ + 1) hk D' ordSeq' restarts' hM hN hSp hG₀ hV₀ hℓ₀ hD' hOrd'
    s₀ (τ + 1) j hInit (by omega) le_rfl hs₀_cases hNoRest
  have hpiMem : ∀ (δ : ℕ) (hδ : δ ≤ τ + 1 - s₀) (p : Finset ℕ × ℤ)
      (_hC0 : p.1 ∈ components (D'.G 0)) (e : ℕ) (x : ℕ × Bool),
      e ∈ ((ep δ).bun p).edges → x ∈ DynSpanner.piTotal ((ep δ).dyn p) e →
      x.1 ∈ ((ep δ).bun p).edges := by
    intro δ hδ p hC0 e x heB hxPi
    have hDyn := hDynAll p.1 hC0 p.2
    set Hb := ((ep 0).bun p).graph
    set G_init := normGraph Hb
    set q := phaseBase (Hb.n + bundleSplitBudget k M) L
    set Us_ep : List (List Update) := (List.range (τ + 1 - s₀)).map fun r =>
      (stepBundleTree sparsify (ep r) (D'.U (s₀ + r + 1))
        (ordSeq' (s₀ + r)) (ordSeq' (s₀ + r + 1))).U_B p
    have hG_val : G_init.IsValid := normGraph_isValid hDyn.1
    have hq1 : 1 ≤ q := le_trans (by omega) (two_le_phaseBase _ L)
    have hGm : G_init.m ≤ M := le_trans hDyn.2.1 hM
    have hBV_norm : G_init.BatchIsValid Us_ep.flatten :=
      batchIsValid_of_graphEq (graphEq_symm (normGraph_graphEq Hb)) hDyn.2.2.2.2.2.1
    have hds_norm : ∀ u ∈ Us_ep.flatten, isDelOrSplit u := hDyn.2.2.2.2.2.2.1
    have hδlen : δ ≤ Us_ep.length := by simp only [Us_ep, List.length_map, List.length_range]; exact hδ
    have hBT := (DynSpanner.batchTrace_spec (L := L) (q := q) hG_val hL hq1 hGm hSp hBV_norm
      hds_norm).1 δ hδlen
    have hStepδ := hDyn.2.2.2.2.2.2.2.2.2.1 δ hδ
    have hSubH : ((ep δ).dyn p).G.IsSubgraph ((ep δ).dyn p).H := hStepδ.2.2.2.1
    have hGE : ((ep δ).dyn p).G.E = ((ep δ).bun p).edges := hStepδ.2.1.2.1
    have hEmb : (DynSpanner.piTotal ((ep δ).dyn p)).IsEmbedding ((ep δ).dyn p).G ((ep δ).dyn p).H := by
      rw [hStepδ.1]; exact hBT.2.2.1
    have heG : e ∈ ((ep δ).dyn p).G.E := hGE.symm ▸ heB
    have hWalk := hEmb.2 e heG
    exact hGE ▸ hSubH.2.1 (MGraph.isWalk_edges_mem hWalk x hxPi)
  constructor
  · intro e heOff x hx
    unfold BundleTreeState.emb at hx
    simp only [heOff, ↓reduceIte] at hx
    split_ifs at hx with h2
    · set p := h2.choose
      obtain ⟨hCact, _, heB⟩ := h2.choose_spec
      have hC0 : p.1 ∈ components (D'.G 0) :=
        hBun_τ.2.2.2.2.2.2.2.2.2.1.2 (hbf.activeComps ▸ hEq.activeComps ▸ hCact)
      have hep_τ : ep (τ - s₀) = post := by
        have h1 := hEpEq.1 (τ - s₀) (by omega)
        have hadd : s₀ + (τ - s₀) = τ := by omega
        rwa [hadd] at h1
      have hxB : x.1 ∈ (post.bun p).edges := by
        rw [← hep_τ]
        exact hpiMem (τ - s₀) (by omega) p hC0 e x (hep_τ.symm ▸ hEq.bun ▸ heB)
          (hep_τ.symm ▸ hEq.dyn ▸ hx)
      have hReady := ((hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2).2.1
      have hI_τ : CompLSFInv C_lsst (D'.ℓ 0) post.cs := hbf.cs ▸ hBun_τ.2.2.2.2.2.2.2.1
      have hG₀_eq : post.cs.G₀ = D'.G 0 := by
        rw [hbf.cs, hBun_τ.2.2.2.2.2.2.1, compLSFBatch_G₀]
        rfl
      have hSubG : (post.bun p).edges ⊆ post.cs.G.E := fun f hf =>
        hI_τ.hCE_sub p.1 (hG₀_eq.symm ▸ hC0) (hReady.2.2 hf)
      have hpostG : post.cs.G = G := by
        rw [hbf.cs, hBun_τ.2.2.2.2.2.2.2.2.1, hGτ]
      rw [← hpostG]
      exact hSubG hxB
    · simp at hx
  · intro e heOff' x hx
    unfold BundleTreeState.emb at hx
    simp only [heOff', ↓reduceIte] at hx
    split_ifs at hx with h2
    · set p := h2.choose
      obtain ⟨hCact, _, heB⟩ := h2.choose_spec
      have hC0 : p.1 ∈ components (D'.G 0) :=
        hBun_τ1.2.2.2.2.2.2.2.2.2.1.2 (hEq'.activeComps ▸ hCact)
      have hep_end : ep (τ + 1 - s₀) = pre' := hEpEq.2.2 (by omega)
      have hxB : x.1 ∈ (pre'.bun p).edges := by
        rw [← hep_end]
        exact hpiMem (τ + 1 - s₀) le_rfl p hC0 e x (hep_end.symm ▸ hEq'.bun ▸ heB)
          (hep_end.symm ▸ hEq'.dyn ▸ hx)
      have hEdgeEq : (pre'.bun p).edges =
          (st₀.bun p).edges \ (Finset.Icc 1 (τ + 1)).biUnion (fun r => batchDeletes (D'.U r)) :=
        ((hBun_τ1.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2).2.2.1
      rw [hEdgeEq] at hxB
      intro hdel
      apply (Finset.mem_sdiff.mp hxB).2
      exact Finset.mem_biUnion.mpr ⟨τ + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hU_eq ▸ hdel⟩
    · simp at hx

/-- If an off-spanner edge `e` stays outside `S_cur` across a valid ordered step `(U, ord')`, and
some step `x ∈ tr.emb e` is inserted by `U`, then `info.state.emb e ≠ tr.emb e`. -/
theorem sparseCoreOrdInput_emb_ne_of_inserts
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N n j : ℕ) (hk : 1 ≤ k) (hSp : SparsifySpec M P_b (sparsify M))
    (s : SparseCoreBundleState L) (G : MGraph) (ord : ℕ → List End)
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hne : s.isNonempty = true)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {e : ℕ} (heOff : e ∉ (s.trees j).S_cur.E)
    (heOff' : e ∉ (stepBundleTree sparsify (s.trees j) U s.ord ord').state.S_cur.E)
    {x : ℕ × Bool} (hx : x ∈ (s.trees j).emb e) (hins : ∃ u ∈ U, u.Inserts x.1) :
    (stepBundleTree sparsify (s.trees j) U s.ord ord').state.emb e ≠ (s.trees j).emb e := by
  obtain ⟨hmemG, hnotDel⟩ := sparseCoreOrdInput_emb_mem_G_and_not_del lsfInit C_lsst L hL P_b
    sparsify params spanConst k M N n j hk hSp s G ord hinp hne U ord' hBV hOrdB hInit
  have hxG : x.1 ∈ G.E := hmemG e heOff x hx
  have hxDel : x.1 ∈ batchDeletes U := mem_batchDeletes_of_inserts_in_G hBV hxG hins
  intro heq
  exact hnotDel e heOff' x (heq.symm ▸ hx) hxDel

/-- Specialization of `sparseCoreOrdInput_emb_ne_of_inserts` to `sparseCoreProgTool`. -/
theorem progTool_emb_ne_of_inserts
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ) (hdepth : 1 ≤ depth) (impl : SparsifyImpl)
    {k M N n j : ℕ} (hk : 1 ≤ k)
    (s : SparseCoreBundleState depth) (G : MGraph) (ord : ℕ → List End)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N s G ord n)
    (hne : s.isNonempty = true)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {e : ℕ} (heOff : e ∉ (s.trees j).S_cur.E)
    (heOff' : e ∉ (stepBundleTree (fun _ => canonicalSparsify impl) (s.trees j) U s.ord ord').state.S_cur.E)
    {x : ℕ × Bool} (hx : x ∈ (s.trees j).emb e) (hins : ∃ u ∈ U, u.Inserts x.1) :
    (stepBundleTree (fun _ => canonicalSparsify impl) (s.trees j) U s.ord ord').state.emb e ≠
      (s.trees j).emb e :=
  sparseCoreOrdInput_emb_ne_of_inserts lsfInit C_lsst depth hdepth
    (canonicalSparsifyParams impl M).absorbTime (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) k M N n j hk
    (canonicalSparsify_spec_absorb impl M) s G ord hinp hne U ord' hBV hOrdB hInit heOff heOff' hx hins

end MinCostFlow.SparseCore
