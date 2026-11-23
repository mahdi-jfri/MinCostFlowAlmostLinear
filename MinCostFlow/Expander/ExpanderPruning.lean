module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Expander.PruningState
public import MinCostFlow.Expander.ExpanderPruningStep

import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Loop and Termination Guarantees (Algorithm 5 Helper)

Formalizes the deterministic pruning loop around `pruneStep`:
- `pruneLoopFuel`: bounded-fuel execution of `pruneStep` until both `peelQ` and `active` are empty.
- `pruneLoopFuel_spec`: proves termination in at most `pot cfg (initState cfg)` steps, preserving
  `PruningInv` and `volPminusB + 2 * C_cap * cutPR`.
- `conductance_of_pruned`: proves `G.IsConductanceExpanderOn R (φ₀ / 3)` whenever `G` is a
  `φ₀`-conductance expander on `X`, `active = []`, `5 ≤ C_cap`, and `4 ≤ φ₀ * (C_cap - 1)`.
- `pruneExpander` & `pruneExpander_spec`: packages the full pruning output and guarantees on a
  vertex subset `X` with boundary/low-degree set `B ⊆ X`.
-/

namespace MinCostFlow.Expander

open Classical

public section

/-- Bounded-fuel pruning loop iterating `pruneStep` until both `peelQ` and `active` vanish. -/
@[expose] noncomputable def pruneLoopFuel (cfg : PruneCfg) : ℕ → PruneState → PruneState
  | 0, s => s
  | k + 1, s =>
    if s.peelQ = [] ∧ s.active = [] then s
    else pruneLoopFuel cfg k (pruneStep cfg s)

/-- Whenever either `peelQ` or `active` is non-empty, `pot cfg s` is strictly positive. -/
lemma pot_pos_of_ne (cfg : PruneCfg) (s : PruneState)
    (hne : s.peelQ ≠ [] ∨ s.active ≠ []) : 0 < pot cfg s := by
  unfold pot phiActive
  rcases hne with hq | ha
  · have : 0 < s.peelQ.length := List.length_pos_of_ne_nil hq
    omega
  · cases hact : s.active with
    | nil => exact False.elim (ha hact)
    | cons u rest =>
      have : 2 ≤ ((u :: rest).map fun x => if s.inR x then s.h x + 2 else 2).sum := by
        simp only [List.map_cons, List.sum_cons]
        split_ifs <;> omega
      omega

/-- Running `pruneLoopFuel` with fuel `k ≥ pot cfg s` terminates with `peelQ = []` and
`active = []`, preserves `PruningInv`, bounds `steps`, and keeps `volPminusB + 2 * C_cap * cutPR`
non-increasing. -/
theorem pruneLoopFuel_spec {cfg : PruneCfg} (hcfg : cfg.Valid)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x) :
    ∀ (k : ℕ) (s : PruneState),
      PruningInv cfg s → pot cfg s ≤ k →
      let s' := pruneLoopFuel cfg k s
      PruningInv cfg s' ∧
      s'.peelQ = [] ∧
      s'.active = [] ∧
      s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
      volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
        volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s
  | 0, s, hinv, hk => by
    have hdone : s.peelQ = [] ∧ s.active = [] := by
      by_contra hne
      have hne' : s.peelQ ≠ [] ∨ s.active ≠ [] := by
        by_cases hq : s.peelQ = []
        · right; intro ha; exact hne ⟨hq, ha⟩
        · exact Or.inl hq
      have hpos := pot_pos_of_ne cfg s hne'
      omega
    exact ⟨hinv, hdone.1, hdone.2, le_rfl, le_rfl⟩
  | k + 1, s, hinv, hk => by
    dsimp only [pruneLoopFuel]
    by_cases hdone : s.peelQ = [] ∧ s.active = []
    · rw [ite_eq_left_iff.mpr fun hn => False.elim (hn hdone)]
      exact ⟨hinv, hdone.1, hdone.2, le_rfl, le_rfl⟩
    · rw [ite_eq_right_iff.mpr fun hp => False.elim (hdone hp)]
      have hne : s.peelQ ≠ [] ∨ s.active ≠ [] := by
        by_cases hq : s.peelQ = []
        · right; intro ha; exact hdone ⟨hq, ha⟩
        · exact Or.inl hq
      rcases pruneStep_inv_pot hcfg hinv hne hθ with ⟨h1_inv, h1_steps, h1_pot, h1_vc⟩
      have hk1 : pot cfg (pruneStep cfg s) ≤ k := by omega
      rcases pruneLoopFuel_spec hcfg hθ k (pruneStep cfg s) h1_inv hk1 with
        ⟨hf_inv, hfq, hfa, hf_steps, hf_vc⟩
      exact ⟨hf_inv, hfq, hfa, le_trans hf_steps h1_steps, le_trans hf_vc h1_vc⟩

private lemma filter_length_eq_sum_map {α : Type*} (p : α → Bool) (L : List α) :
    (L.filter p).length = (L.map fun x => if p x then 1 else 0).sum := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases p a <;> simp [ih, Nat.add_comm]

private lemma crossCutList_le_cutIn (G : Cited.Graph) (X R S : Finset ℕ) (inR : ℕ → Bool)
    (hinR : ∀ v, inR v = true ↔ v ∈ R) (hSR : S ⊆ R) :
    crossCutList inR S (G.inside X) ≤ G.cutIn X R := by
  rw [cutIn_eq_sum_map]
  unfold crossCutList
  rw [filter_length_eq_sum_map]
  suffices h : ∀ (L : List (ℕ × ℕ)),
      (L.map fun e => if decide ((e.1 ∈ S ∧ !inR e.2) ∨ (e.2 ∈ S ∧ !inR e.1)) = true then 1 else 0).sum ≤
      (L.map fun e => if (decide (e.1 ∈ R) != decide (e.2 ∈ R)) = true then 1 else 0).sum from
    h (G.inside X)
  intro L
  induction L with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : decide ((e.1 ∈ S ∧ (!inR e.2) = true) ∨ (e.2 ∈ S ∧ (!inR e.1) = true)) = true →
        (decide (e.1 ∈ R) != decide (e.2 ∈ R)) = true := by
      simp only [decide_eq_true_eq]
      rintro (⟨hS, hn⟩ | ⟨hS, hn⟩)
      · have he1 : e.1 ∈ R := hSR hS
        have he2 : e.2 ∉ R := fun hr => by simp [(hinR e.2).mpr hr] at hn
        simp [he1, he2]
      · have he2 : e.2 ∈ R := hSR hS
        have he1 : e.1 ∉ R := fun hr => by simp [(hinR e.1).mpr hr] at hn
        simp [he1, he2]
    split_ifs with ha hb hb2
    · omega
    · exact False.elim (hb (h1 ha))
    · omega
    · omega

private lemma conductance_half {cfg : PruneCfg} {sFin : PruneState} {φ₀ : ℝ}
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hinv : PruningInv cfg sFin) (hact : sFin.active = [])
    {S : Finset ℕ} (hSR : S ⊆ sFin.Rset cfg) (hSne : S.Nonempty) (hSneR : S ≠ sFin.Rset cfg)
    (hvol_le : cfg.G.volIn (sFin.Rset cfg) S ≤ cfg.G.volIn (sFin.Rset cfg) (sFin.Rset cfg \ S)) :
    (φ₀ / 3) * (cfg.G.volIn (sFin.Rset cfg) S : ℝ) ≤
      (cfg.G.cutIn (sFin.Rset cfg) S : ℝ) := by
  set R := sFin.Rset cfg
  have hRX : R ⊆ cfg.X := Finset.filter_subset _ _
  have hSX : S ⊆ cfg.X := hSR.trans hRX
  have hSneX : S ≠ cfg.X := by
    intro hEq
    apply hSneR
    exact Finset.Subset.antisymm hSR (fun x hxR => hEq ▸ hRX hxR)
  have hinR_iff : ∀ v, sFin.inR v = true ↔ v ∈ R := fun v =>
    (sFin.mem_Rset cfg hinv.inR_sub).symm
  have hSR_bool : ∀ u ∈ S, sFin.inR u = true := fun u hu => (hinR_iff u).mpr (hSR hu)
  set cross := crossCutList sFin.inR S cfg.edges
  have hdiff := crossCutList_eq_volDiff (G := cfg.G) sFin.inR hinR_iff hRX hSR
  change cfg.G.volIn cfg.X S = cfg.G.volIn R S + cross ∧
      cfg.G.cutIn cfg.X S = cfg.G.cutIn R S + cross at hdiff
  have hcross_le_cut : cross ≤ cfg.G.cutIn cfg.X R :=
    crossCutList_le_cutIn cfg.G cfg.X R S sFin.inR hinR_iff hSR
  have hcut_sdiff : cfg.G.cutIn cfg.X R = cfg.G.cutIn cfg.X (cfg.X \ R) :=
    (cutIn_sdiff cfg.G cfg.X R hRX).symm
  have hcross_le_volP : cross ≤ cfg.G.volIn cfg.X (cfg.X \ R) :=
    le_trans hcross_le_cut (hcut_sdiff ▸ cutIn_le_volIn cfg.G cfg.X (cfg.X \ R))
  have hvol_comp : cfg.G.volIn cfg.X S ≤ cfg.G.volIn cfg.X (cfg.X \ S) := by
    have hunion : cfg.X \ S = (cfg.X \ R) ∪ (R \ S) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro ⟨hxX, hxS⟩
        by_cases hxR : x ∈ R
        · exact Or.inr ⟨hxR, hxS⟩
        · exact Or.inl ⟨hxX, hxR⟩
      · rintro (⟨hxX, hxR⟩ | ⟨hxR, hxS⟩)
        · exact ⟨hxX, fun hxS => hxR (hSR hxS)⟩
        · exact ⟨hRX hxR, hxS⟩
    have hdisj : Disjoint (cfg.X \ R) (R \ S) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_sdiff.mp hx2).1
    rw [hunion, volIn_disjoint_union cfg.G cfg.X (cfg.X \ R) (R \ S) hdisj]
    have hmono : cfg.G.volIn R (R \ S) ≤ cfg.G.volIn cfg.X (R \ S) :=
      volIn_mono_left hRX (R \ S)
    omega
  have hexpS := hexp S hSX hSne hSneX
  rw [min_eq_left (by exact_mod_cast hvol_comp), hdiff.2, hdiff.1] at hexpS
  have hex0 : ∀ u ∈ S, sFin.ex u = 0 := by
    intro u hu
    by_contra hne
    have hmem := hinv.active_cov u (hSR_bool u hu) (Nat.pos_of_ne_zero hne)
    rw [hact] at hmem
    simp at hmem
  have hsum_le : ∑ u ∈ S, ((sFin.ex u : ℤ) + (sFin.abs u : ℤ)) ≤
      (cfg.G.volIn cfg.X S : ℤ) := by
    have h1 : ∀ u ∈ S, ((sFin.ex u : ℤ) + (sFin.abs u : ℤ)) ≤ (cfg.G.degIn cfg.X u : ℤ) := by
      intro u hu
      have he0 := hex0 u hu
      have hle := hinv.abs_le u (hSR_bool u hu)
      change sFin.abs u ≤ cfg.G.degIn cfg.X u at hle
      omega
    have h2 : ∑ u ∈ S, ((sFin.ex u : ℤ) + (sFin.abs u : ℤ)) ≤
        ∑ u ∈ S, (cfg.G.degIn cfg.X u : ℤ) := Finset.sum_le_sum h1
    have hvol_eq : (cfg.G.volIn cfg.X S : ℤ) = ∑ u ∈ S, (cfg.G.degIn cfg.X u : ℤ) := by
      unfold Cited.Graph.volIn
      push_cast
      rfl
    omega
  have hsum_fb : ∑ u ∈ S, ((sFin.ex u : ℤ) + (sFin.abs u : ℤ)) =
      (cfg.C_cap : ℤ) * (cross : ℤ) - flowOutAux sFin.inR S sFin.flow 0 cfg.edges := by
    have hpt : ∑ u ∈ S, ((sFin.ex u : ℤ) + (sFin.abs u : ℤ)) =
        ∑ u ∈ S, ((cfg.incEdges u).map (edgeContrib sFin.inR sFin.flow cfg.C_cap)).sum := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hinv.flow_balance u (hSR_bool u hu)
    rw [hpt]
    exact sum_edgeContrib_eq sFin.inR S hSR_bool sFin.flow cfg.C_cap 0 cfg.edges
  have hfo := flowOutAux_le_cutIn sFin.inR hinR_iff hRX hSR sFin.flow cfg.C_cap hinv.flow_cap
  change flowOutAux sFin.inR S sFin.flow 0 cfg.edges ≤ (cfg.C_cap : ℤ) * (cfg.G.cutIn R S : ℤ) at hfo
  have hcross_Z : ((cfg.C_cap : ℤ) - 1) * (cross : ℤ) ≤
      (cfg.G.volIn R S : ℤ) + (cfg.C_cap : ℤ) * (cfg.G.cutIn R S : ℤ) := by
    have hdiff_Z : (cfg.G.volIn cfg.X S : ℤ) = (cfg.G.volIn R S : ℤ) + (cross : ℤ) := by
      exact_mod_cast hdiff.1
    have hmul_sub : ((cfg.C_cap : ℤ) - 1) * (cross : ℤ) =
        (cfg.C_cap : ℤ) * (cross : ℤ) - (cross : ℤ) := by ring
    rw [hmul_sub]
    linarith
  have hcross_R : ((cfg.C_cap : ℝ) - 1) * (cross : ℝ) ≤
      (cfg.G.volIn R S : ℝ) + (cfg.C_cap : ℝ) * (cfg.G.cutIn R S : ℝ) := by
    exact_mod_cast hcross_Z
  have hC_pos : (0 : ℝ) < (cfg.C_cap : ℝ) - 1 := by
    have : (5 : ℝ) ≤ (cfg.C_cap : ℝ) := by exact_mod_cast hC5
    linarith
  have hC5_R : (5 : ℝ) ≤ (cfg.C_cap : ℝ) := by exact_mod_cast hC5
  have hv0 : (0 : ℝ) ≤ (cfg.G.volIn R S : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (cfg.G.cutIn R S : ℝ) := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ (cross : ℝ) := Nat.cast_nonneg _
  have h1 : φ₀ * (cfg.G.volIn R S : ℝ) ≤ (cfg.G.cutIn R S : ℝ) + (cross : ℝ) := by
    push_cast at hexpS ⊢
    nlinarith
  have hmul : ((cfg.C_cap : ℝ) - 1) * (φ₀ * (cfg.G.volIn R S : ℝ)) ≤
      ((cfg.C_cap : ℝ) - 1) * ((cfg.G.cutIn R S : ℝ) + (cross : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hC_pos.le
  have hcomb : (φ₀ * ((cfg.C_cap : ℝ) - 1) - 1) * (cfg.G.volIn R S : ℝ) ≤
      (2 * (cfg.C_cap : ℝ) - 1) * (cfg.G.cutIn R S : ℝ) := by
    nlinarith
  have hlhs_ge : (3 / 4 : ℝ) * (φ₀ * ((cfg.C_cap : ℝ) - 1)) * (cfg.G.volIn R S : ℝ) ≤
      (φ₀ * ((cfg.C_cap : ℝ) - 1) - 1) * (cfg.G.volIn R S : ℝ) := by
    nlinarith
  have hrhs_le : (2 * (cfg.C_cap : ℝ) - 1) * (cfg.G.cutIn R S : ℝ) ≤
      (9 / 4 : ℝ) * ((cfg.C_cap : ℝ) - 1) * (cfg.G.cutIn R S : ℝ) := by
    nlinarith
  have hmain : ((cfg.C_cap : ℝ) - 1) * ((φ₀ / 3) * (cfg.G.volIn R S : ℝ)) ≤
      ((cfg.C_cap : ℝ) - 1) * (cfg.G.cutIn R S : ℝ) := by
    linarith
  exact le_of_mul_le_mul_left hmain hC_pos

/-- At termination (`active = []`), `R = sFin.Rset cfg` is a `(φ₀ / 3)`-conductance expander
whenever `G` is a `φ₀`-conductance expander on `X`, `5 ≤ C_cap`, and `4 ≤ φ₀ * (C_cap - 1)`. -/
theorem conductance_of_pruned {cfg : PruneCfg} {sFin : PruneState} {φ₀ : ℝ}
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hinv : PruningInv cfg sFin) (hact : sFin.active = []) :
    cfg.G.IsConductanceExpanderOn (sFin.Rset cfg) (φ₀ / 3) := by
  intro S hSR hSne hSneR
  set R := sFin.Rset cfg
  by_cases hle : cfg.G.volIn R S ≤ cfg.G.volIn R (R \ S)
  · rw [min_eq_left (by exact_mod_cast hle)]
    exact conductance_half hexp hφ₀ hC5 hCphi hinv hact hSR hSne hSneR hle
  · have hle' : cfg.G.volIn R (R \ S) ≤ cfg.G.volIn R (R \ (R \ S)) := by
      rw [Finset.sdiff_sdiff_eq_self hSR]
      omega
    have hSne' : (R \ S).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
      exact hSneR (Finset.Subset.antisymm hSR hem)
    have hSneR' : R \ S ≠ R := by
      intro hEq
      rcases hSne with ⟨x, hxS⟩
      have hxR : x ∈ R := hSR hxS
      have hx_sdiff : x ∈ R \ S := by rw [hEq]; exact hxR
      exact (Finset.mem_sdiff.mp hx_sdiff).2 hxS
    have hhalf := conductance_half hexp hφ₀ hC5 hCphi hinv hact Finset.sdiff_subset hSne' hSneR' hle'
    rw [min_eq_right (by exact_mod_cast le_of_not_ge hle), ← cutIn_sdiff cfg.G R S hSR]
    exact hhalf

/-- Constructs the pruning configuration for `(G, X, B, φ₀, θ_in)` using
`C_cap = max 7 (⌈4 / φ₀⌉ + 2)`, `H = 4 * C_cap * (⌊log₂(2m_X + 1)⌋ + 1) + 2`,
and `θ_out_nat = ⌈θ_in / 3⌉`. -/
@[expose] noncomputable def pruneCfgOf (G : Cited.Graph) (X B : Finset ℕ) (φ₀ θ_in : ℝ) :
    PruneCfg :=
  let C_cap := max 7 (Nat.ceil (4 / φ₀) + 2)
  let H := 4 * C_cap * (Nat.log 2 (2 * (G.inside X).length + 1) + 1) + 2
  { G := G
    X := X
    B := B
    C_cap := C_cap
    H := H
    θ_out_nat := Nat.ceil (θ_in / 3) }

/-- Final pruning state returned by running `pruneLoopFuel` from `initState`. -/
@[expose] noncomputable def pruneFinalState (cfg : PruneCfg) : PruneState :=
  pruneLoopFuel cfg (pot cfg (initState cfg)) (initState cfg)

/-- Deterministic expander pruning on `X` given initial bad/boundary set `B ⊆ X`,
conductance `φ₀`, and inner degree lower bound `θ_in`. -/
@[expose] noncomputable def pruneExpander (G : Cited.Graph) (X B : Finset ℕ) (φ₀ θ_in : ℝ) :
    Finset ℕ :=
  (pruneFinalState (pruneCfgOf G X B φ₀ θ_in)).Rset (pruneCfgOf G X B φ₀ θ_in)

private lemma cutPR_eq_cutIn (cfg : PruneCfg) {s : PruneState}
    (hinR : ∀ u, s.inR u = true → u ∈ cfg.X) :
    cutPR cfg s = cfg.G.cutIn cfg.X (s.Rset cfg) := by
  unfold cutPR PruneCfg.edges
  rw [filter_length_eq_sum_map, cutIn_eq_sum_map]
  congr 1
  apply List.map_congr_left
  intro e _
  have h1 : s.inR e.1 = true ↔ e.1 ∈ s.Rset cfg := (s.mem_Rset cfg hinR).symm
  have h2 : s.inR e.2 = true ↔ e.2 ∈ s.Rset cfg := (s.mem_Rset cfg hinR).symm
  by_cases he1 : e.1 ∈ s.Rset cfg <;> by_cases he2 : e.2 ∈ s.Rset cfg
  · have hs1 : s.inR e.1 = true := h1.mpr he1
    have hs2 : s.inR e.2 = true := h2.mpr he2
    simp [hs1, hs2, he1, he2]
  · have hs1 : s.inR e.1 = true := h1.mpr he1
    have hs2 : s.inR e.2 = false := Bool.eq_false_iff.mpr fun h => he2 (h2.mp h)
    simp [hs1, hs2, he1, he2]
  · have hs1 : s.inR e.1 = false := Bool.eq_false_iff.mpr fun h => he1 (h1.mp h)
    have hs2 : s.inR e.2 = true := h2.mpr he2
    simp [hs1, hs2, he1, he2]
  · have hs1 : s.inR e.1 = false := Bool.eq_false_iff.mpr fun h => he1 (h1.mp h)
    have hs2 : s.inR e.2 = false := Bool.eq_false_iff.mpr fun h => he2 (h2.mp h)
    simp [hs1, hs2, he1, he2]

/-- Specification of `pruneExpander`:
1. `R ⊆ X \ B`;
2. `G` is a `(φ₀ / 3)`-conductance expander on `R`;
3. Every `v ∈ R` has `G.degIn R v ≥ θ_in / 3`;
4. `G.volIn X ((X \ B) \ R) + 2 * cfg.C_cap * G.cutIn X R ≤ 2 * cfg.C_cap * G.cutIn X B`;
5. `G.volIn X (X \ R) ≤ G.volIn X B + 2 * cfg.C_cap * G.cutIn X B`;
6. Step count is bounded by `(4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * (G.inside X).length + 1)`. -/
theorem pruneExpander_spec {G : Cited.Graph} (hG : G.IsValid) {X B : Finset ℕ} (hBX : B ⊆ X)
    {φ₀ θ_in : ℝ} (hexp : G.IsConductanceExpanderOn X φ₀) (hφ₀ : 0 < φ₀)
    (hθ : ∀ v ∈ X, v ∉ B → θ_in ≤ (G.degIn X v : ℝ)) :
    let cfg := pruneCfgOf G X B φ₀ θ_in
    let sFin := pruneFinalState cfg
    let R := pruneExpander G X B φ₀ θ_in
    R ⊆ X \ B ∧
    G.IsConductanceExpanderOn R (φ₀ / 3) ∧
    (∀ v ∈ R, θ_in / 3 ≤ (G.degIn R v : ℝ)) ∧
    G.volIn X ((X \ B) \ R) + 2 * cfg.C_cap * G.cutIn X R ≤ 2 * cfg.C_cap * G.cutIn X B ∧
    G.volIn X (X \ R) ≤ G.volIn X B + 2 * cfg.C_cap * G.cutIn X B ∧
    sFin.steps ≤ (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * (G.inside X).length + 1) := by
  set cfg := pruneCfgOf G X B φ₀ θ_in
  set sFin := pruneFinalState cfg
  set R := pruneExpander G X B φ₀ θ_in
  have hC_ge7 : 7 ≤ cfg.C_cap := le_max_left _ _
  have hC_ceil : Nat.ceil (4 / φ₀) + 2 ≤ cfg.C_cap := le_max_right _ _
  have hcfg : cfg.Valid := by
    refine ⟨hG, hBX, by omega, le_rfl, ?_⟩
    intro v hvX hvB
    have hv := hθ v hvX hvB
    change Nat.ceil (θ_in / 3) ≤ G.degIn X v
    by_cases hpos : 0 ≤ θ_in
    · exact Nat.ceil_le.mpr (by linarith)
    · have h0 : θ_in / 3 ≤ 0 := by linarith
      rw [Nat.ceil_eq_zero.mpr h0]
      exact Nat.zero_le _
  have hθ_nat : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x := by
    intro x hxX hxB d hd
    have hltR : (d : ℝ) < θ_in / 3 := Nat.lt_ceil.mp hd
    have hx_deg := hθ x hxX hxB
    have hlt3 : (3 * d : ℝ) < (G.degIn X x : ℝ) := by linarith
    change 3 * d ≤ G.degIn X x
    exact Nat.le_of_lt (by exact_mod_cast hlt3)
  have hinit_inv := initState_inv hcfg
  rcases pruneLoopFuel_spec hcfg hθ_nat (pot cfg (initState cfg)) (initState cfg)
      hinit_inv le_rfl with
    ⟨hf_inv, hfq, hfa, hf_steps, hf_vc⟩
  have hR_sub_diff : R ⊆ X \ B := by
    intro u hu
    rw [Finset.mem_sdiff]
    have huR : sFin.inR u = true := (sFin.mem_Rset cfg hf_inv.inR_sub).mp hu
    refine ⟨hf_inv.inR_sub u huR, fun huB => ?_⟩
    exact Bool.false_ne_true ((hf_inv.not_inR_B u huB).symm.trans huR)
  have hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1) := by
    have h1 : (Nat.ceil (4 / φ₀) : ℝ) + 2 ≤ (cfg.C_cap : ℝ) := by exact_mod_cast hC_ceil
    have h2 : 4 / φ₀ ≤ (Nat.ceil (4 / φ₀) : ℝ) := Nat.le_ceil _
    have h3 : 4 / φ₀ ≤ (cfg.C_cap : ℝ) - 1 := by linarith
    rw [mul_comm]
    exact (div_le_iff₀ hφ₀).mp h3
  have hexpR : G.IsConductanceExpanderOn R (φ₀ / 3) :=
    conductance_of_pruned hexp hφ₀ (by change 5 ≤ cfg.C_cap; omega) hCphi hf_inv hfa
  have hdegR : ∀ v ∈ R, θ_in / 3 ≤ (G.degIn R v : ℝ) := by
    intro v hvR
    have hvR_b : sFin.inR v = true := (sFin.mem_Rset cfg hf_inv.inR_sub).mp hvR
    have hge : cfg.θ_out_nat ≤ sFin.degR v := by
      by_contra hlt
      have := hf_inv.degR_peel v hvR_b (Nat.lt_of_not_le hlt)
      rw [hfq] at this
      simp at this
    have hdeg_eq : sFin.degR v = G.degIn R v := hf_inv.degR_eq v hvR_b
    rw [hdeg_eq] at hge
    have hgeR : (cfg.θ_out_nat : ℝ) ≤ (G.degIn R v : ℝ) := by exact_mod_cast hge
    have hceil : θ_in / 3 ≤ (cfg.θ_out_nat : ℝ) := Nat.le_ceil _
    linarith
  have hvolP_init : volPminusB cfg (initState cfg) = 0 := by
    unfold volPminusB initState
    apply Finset.sum_eq_zero
    intro u hu
    have huX : u ∈ X := hu
    by_cases huB : u ∈ B <;> simp [cfg, pruneCfgOf, huX, huB]
  have hR_init : (initState cfg).Rset cfg = X \ B := by
    ext u
    simp [PruneState.Rset, initState, cfg, pruneCfgOf, Finset.mem_sdiff]
  have hcut_init : cutPR cfg (initState cfg) = G.cutIn X B := by
    rw [cutPR_eq_cutIn cfg hinit_inv.inR_sub, hR_init]
    exact cutIn_sdiff G X B hBX
  have hvolP_fin : volPminusB cfg sFin = G.volIn X ((X \ B) \ R) := by
    unfold volPminusB Cited.Graph.volIn
    have hfilt : (X \ B) \ R = cfg.X.filter fun u => !sFin.inR u && decide (u ∉ cfg.B) := by
      ext u
      simp only [Finset.mem_sdiff, Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨huX, huB⟩, huR⟩
        refine ⟨huX, ?_, huB⟩
        by_contra h
        have htrue : sFin.inR u = true := Bool.eq_true_of_not_eq_false h
        exact huR ((sFin.mem_Rset cfg hf_inv.inR_sub).mpr htrue)
      · rintro ⟨huX, hfalse, huB⟩
        refine ⟨⟨huX, huB⟩, fun huR => ?_⟩
        have htrue := (sFin.mem_Rset cfg hf_inv.inR_sub).mp huR
        simp [htrue] at hfalse
    rw [hfilt, Finset.sum_filter]
    rfl
  have hcut_fin : cutPR cfg sFin = G.cutIn X R := cutPR_eq_cutIn cfg hf_inv.inR_sub
  have hvc_final : G.volIn X ((X \ B) \ R) + 2 * cfg.C_cap * G.cutIn X R ≤
      2 * cfg.C_cap * G.cutIn X B := by
    have hf_vc' : volPminusB cfg sFin + 2 * cfg.C_cap * cutPR cfg sFin ≤
        volPminusB cfg (initState cfg) + 2 * cfg.C_cap * cutPR cfg (initState cfg) := hf_vc
    rw [hvolP_fin, hcut_fin, hvolP_init, hcut_init, zero_add] at hf_vc'
    exact hf_vc'
  have hvol_XR : G.volIn X (X \ R) ≤ G.volIn X B + 2 * cfg.C_cap * G.cutIn X B := by
    have hunion : X \ R = B ∪ ((X \ B) \ R) := by
      ext u
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro ⟨huX, huR⟩
        by_cases huB : u ∈ B
        · exact Or.inl huB
        · exact Or.inr ⟨⟨huX, huB⟩, huR⟩
      · rintro (huB | ⟨⟨huX, _⟩, huR⟩)
        · exact ⟨hBX huB, fun huR => (hR_sub_diff huR |> Finset.mem_sdiff.mp).2 huB⟩
        · exact ⟨huX, huR⟩
    have hdisj : Disjoint B ((X \ B) \ R) := by
      rw [Finset.disjoint_left]
      intro u huB hu2
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu2).1).2 huB
    rw [hunion, volIn_disjoint_union G X B ((X \ B) \ R) hdisj]
    omega
  have hsteps_final : sFin.steps ≤
      (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * (G.inside X).length + 1) := by
    have hf_steps' : sFin.steps + pot cfg sFin ≤ (initState cfg).steps + pot cfg (initState cfg) :=
      hf_steps
    have hinit_steps : (initState cfg).steps = 0 := rfl
    have heq_len : cfg.edges.length = (G.inside X).length := rfl
    rw [← heq_len]
    exact le_trans (Nat.le_add_right _ _)
      (le_trans hf_steps' (by rw [hinit_steps, zero_add]; exact pot_initState_le hcfg))
  exact ⟨hR_sub_diff, hexpR, hdegR, hvc_final, hvol_XR, hsteps_final⟩

end

end MinCostFlow.Expander
