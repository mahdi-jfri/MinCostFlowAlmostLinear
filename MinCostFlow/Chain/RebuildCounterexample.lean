module

public import MinCostFlow.Chain.Theorem5_1Helpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Switched-Recourse Counterexample (RebuildBounds Helpers)

Split from `MinCostFlow.Chain.RebuildBounds`: concrete counterexample
`exSwitchedRecourse_counterexample` and restart tool `exSwRestartTool`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section Counterexample

/-- Parameters for `exSwitchedRecourse_counterexample` (`k = 2, γ_r = 3, γ_ℓ = 5, γ_c = 1, c_R = 1`). -/
def exSwParams : SparseCoreParams where
  σ := fun _ n => max 1 (n : ℝ)
  γ_ℓ := fun _ => 5
  γ_c := fun _ => 1
  γ_r := fun _ => 3
  c_R := 1
  c_T := 10
  p_T := 1

lemma exSwParams_valid : exSwParams.Valid :=
  ⟨fun _ _ _ => le_max_left _ _, fun _ _ _ _ _ hn => max_le_max_left 1 (by exact_mod_cast hn),
    fun _ => by change (1 : ℝ) ≤ 5; norm_num, fun _ _ _ => le_refl _, fun _ => le_refl _,
    fun _ _ _ => le_refl _, fun _ => by change (1 : ℝ) ≤ 3; norm_num, fun _ _ _ => le_refl _,
    by change (0 : ℝ) ≤ 1; norm_num, by change (0 : ℝ) ≤ 10; norm_num⟩

/-- Base graph (`V = {0, 1, 2, 3}`, `E = {0, 1, 2, 3, 4}`): parallel edges `0, 1 : 0 → 2`, tree
edges `2 : 0 → 1`, `3 : 2 → 3`, and cross edge `4 : 1 → 3`. -/
def exSwG0 : MGraph where
  V := {0, 1, 2, 3}
  E := {0, 1, 2, 3, 4}
  tail := fun e => if e = 3 then 2 else if e = 4 then 1 else 0
  head := fun e => if e = 2 then 1 else if e = 3 ∨ e = 4 then 3 else 2

/-- Valid dynamic instance with two 1-edge deletion batches (`U 1 = [.delete 0]`, `U 2 = [.delete 1]`). -/
def exSwDyn : DynamicInstance where
  G := fun t => match t with
    | 0 => exSwG0
    | 1 => exSwG0.applyBatch [.delete 0]
    | _ + 2 => (exSwG0.applyBatch [.delete 0]).applyBatch [.delete 1]
  U := fun t => match t with | 1 => [.delete 0] | 2 => [.delete 1] | _ => []
  g := fun _ _ => 1
  ℓ := fun _ _ => 1

def exSwF0 : MGraph := { exSwG0 with E := {2, 3} }
def exSwF01 : MGraph := { exSwG0 with E := {2} }
def exSwFempty : MGraph := { exSwG0 with E := ∅ }
def exSwL0 : LSF := ⟨exSwF0, ⟨exSwF0, {0, 2}⟩, fun _ => 3⟩
def exSwL01 : LSF := ⟨exSwF0, ⟨exSwF01, {0, 2, 3}⟩, fun _ => 3⟩
def exSwLempty : LSF := ⟨exSwF0, ⟨exSwFempty, {0, 1, 2, 3}⟩, fun _ => 3⟩
def exSwSInit : MGraph := { V := {0, 2}, E := {0, 1, 4}, tail := fun _ => 0, head := fun _ => 2 }
def exSwU01 : List Update := [.delete 0, .split 2 3 {4} {4}, .insert 3 2 3]
def exSwU02 : List Update := [.delete 1]
def exSwU11 : List Update := [.delete 0]
def exSwU12 : List Update := [.delete 1, .split 0 1 {4} {4}, .insert 2 0 1, .split 2 3 {4} {4}, .insert 3 2 3]

/-- Concrete 2-branch `SparseCoreTool` for `exSwitchedRecourse_counterexample`. -/
def exSwTool : SparseCoreTool where
  State := ℕ × MGraph × MGraph
  init := fun _ _ _ _ _ _ => (0, exSwSInit, exSwSInit)
  update := fun (t, S0, S1) _ _ _ =>
    let uS : ℕ → List Update := fun j =>
      if j = 0 then (if t = 0 then exSwU01 else if t = 1 then exSwU02 else [])
      else (if t = 0 then exSwU11 else if t = 1 then exSwU12 else [])
    ((t + 1, S0.applyBatch (uS 0), S1.applyBatch (uS 1)), uS)
  lsfs := fun (t, _, _) j =>
    if j = 0 then (if t = 0 then exSwL0 else exSwL01)
    else (if t ≤ 1 then exSwL0 else exSwLempty)
  S := fun (_, S0, S1) j => if j = 0 then S0 else S1
  emb := fun _ _ e => [(e, true)]
  cost := fun (t, _, _) => t + 1

lemma log_six_lt_two : Real.log 6 < 2 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2 (by nlinarith)

private lemma exSw_comp_walk {F : MGraph} (hE : F.E ⊆ ({2, 3} : Finset ℕ))
    (ht : F.tail = exSwG0.tail) (hh : F.head = exSwG0.head) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, F.IsWalk u v P →
      ((u = 0 ∨ u = 1) → (v = 0 ∨ v = 1) ∧ ∀ w ∈ F.walkVertices u P, w = 0 ∨ w = 1) ∧
      ((u = 2 ∨ u = 3) → (v = 2 ∨ v = 3) ∧ ∀ w ∈ F.walkVertices u P, w = 2 ∨ w = 3) ∧
      (3 ∉ F.E → u = 2 ∨ u = 3 → v = u) := by
  intro u v P hP
  induction hP with
  | nil z =>
    refine ⟨fun h => ⟨h, fun w hw => ?_⟩, fun h => ⟨h, fun w hw => ?_⟩, fun _ _ => rfl⟩ <;>
      · simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw; subst hw; exact h
  | @cons a _ x Q he hsrc _ ih =>
    have hxE : x.1 = 2 ∨ x.1 = 3 := by simpa using hE he
    have ha_inv : ((a = 0 ∨ a = 1) → (F.dst x = 0 ∨ F.dst x = 1) ∧ x.1 = 2) ∧
        ((a = 2 ∨ a = 3) → (F.dst x = 2 ∨ F.dst x = 3) ∧ x.1 = 3) := by
      cases hx : x.2 <;> rcases hxE with hxE | hxE <;>
        simp [MGraph.src, MGraph.dst, hx, hxE, ht, hh, exSwG0] at hsrc ⊢ <;> omega
    refine ⟨?_, ?_, fun hn3 ha23 => absurd ((ha_inv.2 ha23).2 ▸ he) hn3⟩
    · intro ha01; rcases ha_inv.1 ha01 with ⟨hb01, _⟩; rcases ih.1 hb01 with ⟨hv01, hW⟩
      refine ⟨hv01, fun w hw => ?_⟩
      change w ∈ a :: F.walkVertices (F.dst x) Q at hw
      rcases List.mem_cons.mp hw with rfl | hwQ
      · exact ha01
      · exact hW w hwQ
    · intro ha23; rcases ha_inv.2 ha23 with ⟨hb23, _⟩; rcases ih.2.1 hb23 with ⟨hv23, hW⟩
      refine ⟨hv23, fun w hw => ?_⟩
      change w ∈ a :: F.walkVertices (F.dst x) Q at hw
      rcases List.mem_cons.mp hw with rfl | hwQ
      · exact ha23
      · exact hW w hwQ

private lemma exSw_isForest {F : MGraph} (hV : F.V = ({0, 1, 2, 3} : Finset ℕ))
    (hE : F.E ⊆ ({2, 3} : Finset ℕ)) (ht : F.tail = exSwG0.tail) (hh : F.head = exSwG0.head) :
    F.IsForest := by
  refine ⟨fun e he => by rcases (by simpa using hE he : e = 2 ∨ e = 3) with rfl | rfl <;> simp [hV, ht, hh, exSwG0],
    fun P hP => ?_⟩
  rcases hP with ⟨hPne, hNodup, _, hWalk⟩
  cases hWalk with
  | nil => exact hPne rfl
  | @cons _ _ x Q he hsrc hQ =>
    have hxE : x.1 = 2 ∨ x.1 = 3 := by simpa using hE he
    cases hQ with
    | nil =>
      cases hx : x.2 <;> rcases hxE with hx2 | hx2 <;>
        simp [MGraph.src, MGraph.dst, hx, hx2, ht, hh, exSwG0] at hsrc
    | @cons _ _ y _ hey hysrc _ =>
      have hyE : y.1 = 2 ∨ y.1 = 3 := by simpa using hE hey
      have hxy : x.1 ≠ y.1 := (List.pairwise_cons.mp hNodup).1 y.1 List.mem_cons_self
      rcases hxE with h2 | h2 <;> rcases hyE with h3 | h3
      · exact hxy (h2.trans h3.symm)
      · have hb : F.dst x = 0 ∨ F.dst x = 1 := by cases hx : x.2 <;> simp [MGraph.dst, hx, h2, ht, hh, exSwG0]
        have hb' : F.dst x = 2 ∨ F.dst x = 3 := by
          cases hy : y.2 <;> simp [MGraph.src, hy, h3, ht, hh, exSwG0] at hysrc <;> omega
        omega
      · have hb : F.dst x = 2 ∨ F.dst x = 3 := by cases hx : x.2 <;> simp [MGraph.dst, hx, h2, ht, hh, exSwG0]
        have hb' : F.dst x = 0 ∨ F.dst x = 1 := by
          cases hy : y.2 <;> simp [MGraph.src, hy, h3, ht, hh, exSwG0] at hysrc <;> omega
        omega
      · exact hxy (h2.trans h3.symm)

private lemma exSw_stretch_le_three {RF : RootedForest} (hE : RF.F.E ⊆ ({2, 3} : Finset ℕ))
    (ht : RF.F.tail = exSwG0.tail) (hh : RF.F.head = exSwG0.head)
    {G : MGraph} (hGV : G.V = ({0, 1, 2, 3} : Finset ℕ)) (hG : G.IsValid) {e : ℕ} (he : e ∈ G.E) :
    RF.stretch G (fun _ => 1) e ≤ 3 := by
  have path_len_le1 {u v : ℕ} (hu : u ∈ ({0, 1, 2, 3} : Finset ℕ)) {P : List (ℕ × Bool)}
      (hPath : RF.F.IsPath u v P) : P.length ≤ 1 := by
    have hSub : (RF.F.walkVertices u P).toFinset ⊆ ({0, 1} : Finset ℕ) ∨
        (RF.F.walkVertices u P).toFinset ⊆ ({2, 3} : Finset ℕ) := by
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · left; intro w hw; simpa using ((exSw_comp_walk hE ht hh hPath.1).1 (Or.inl rfl)).2 w (List.mem_toFinset.mp hw)
      · rcases Finset.mem_insert.mp hu' with rfl | hu''
        · left; intro w hw; simpa using ((exSw_comp_walk hE ht hh hPath.1).1 (Or.inr rfl)).2 w (List.mem_toFinset.mp hw)
        · right; intro w hw; simpa using ((exSw_comp_walk hE ht hh hPath.1).2.1 (by simpa using hu'')).2 w (List.mem_toFinset.mp hw)
    have hCard : (RF.F.walkVertices u P).length ≤ 2 := by
      rw [← List.toFinset_card_of_nodup hPath.2]
      rcases hSub with h01 | h23
      · exact le_trans (Finset.card_le_card h01) (by decide)
      · exact le_trans (Finset.card_le_card h23) (by decide)
    have hLen : (RF.F.walkVertices u P).length = P.length + 1 := by
      simp [MGraph.walkVertices]
    omega
  have wl_le1 {P : List (ℕ × Bool)} (hLen : P.length ≤ 1) : walkLength (fun _ => (1 : ℝ)) P ≤ 1 := by
    rcases P with _ | ⟨⟨e', b'⟩, _ | _⟩
    · simp [walkLength, walkEdges]
    · cases b' <;> simp [walkLength, walkEdges, walkFlow]
    · simp at hLen
  have fle (a b : ℕ) (ha : a ∈ ({0, 1, 2, 3} : Finset ℕ)) :
      0 ≤ walkLength (fun _ => 1) (MGraph.forestPath RF.F a b) ∧
      walkLength (fun _ => 1) (MGraph.forestPath RF.F a b) ≤ 1 := by
    refine ⟨Finset.sum_nonneg fun _ _ => mul_nonneg zero_le_one (abs_nonneg _), ?_⟩
    dsimp only [MGraph.forestPath]
    split_ifs with hEx
    · exact wl_le1 (path_len_le1 ha hEx.choose_spec)
    · simp [walkLength, walkEdges]
  dsimp only [RootedForest.stretch]
  have h1 := fle (G.tail e) (G.head e) (hGV ▸ (hG e he).1)
  have h2 := fle (G.tail e) (RF.root (G.tail e)) (hGV ▸ (hG e he).1)
  have h3 := fle (G.head e) (RF.root (G.head e)) (hGV ▸ (hG e he).2)
  split_ifs <;> linarith

lemma exSwL_holds_all {G : MGraph} (hGV : G.V = ({0, 1, 2, 3} : Finset ℕ))
    (hGt : G.tail = exSwG0.tail) (hGh : G.head = exSwG0.head) (hG : G.IsValid) :
    (({2, 3} : Finset ℕ) ⊆ G.E → exSwL0.Holds G (fun _ => 1) (exSwParams.σ 2 G.n)) ∧
    (({2} : Finset ℕ) ⊆ G.E → exSwL01.Holds G (fun _ => 1) (exSwParams.σ 2 G.n)) ∧
    exSwLempty.Holds G (fun _ => 1) (exSwParams.σ 2 G.n) := by
  have hn : G.n = 4 := by simp [MGraph.n, hGV]
  have hσ : (3 : ℝ) ≤ exSwParams.σ 2 G.n := by simp [exSwParams, hn]; norm_num
  have hFT : exSwF0.IsForest := exSw_isForest rfl (by decide) rfl rfl
  have hsubE (F : MGraph) (hFt : F.tail = exSwG0.tail) (hFh : F.head = exSwG0.head)
      (hFV : F.V = {0, 1, 2, 3}) (hFE : F.E ⊆ G.E) : G.IsSubgraph F :=
    ⟨hGV.symm ▸ hFV ▸ Finset.Subset.refl _, hFE, fun _ _ => ⟨by simp [hFt, hGt], by simp [hFh, hGh]⟩⟩
  refine ⟨fun hGE => ?_, fun hGE => ?_, ?_⟩
  · refine ⟨hFT, ⟨hFT, hGV.symm, by rw [hGV]; decide, ?_, hsubE exSwF0 rfl rfl rfl hGE⟩,
      ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩,
      fun _ he => ⟨exSw_stretch_le_three (by decide) rfl rfl hGV hG he, by simpa [exSwL0] using hσ⟩⟩
    intro v hv; rw [hGV] at hv
    have u01 : ∀ w, exSwF0.Connected 0 w → w ∈ ({0, 2} : Finset ℕ) → w = 0 := fun w ⟨P, hP⟩ hw => by
      have := ((exSw_comp_walk (F := exSwF0) (by decide) rfl rfl hP).1 (Or.inl rfl)).1
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · rfl
      · simp only [Finset.mem_singleton] at hw'; omega
    have u23 : ∀ w, exSwF0.Connected 2 w → w ∈ ({0, 2} : Finset ℕ) → w = 2 := fun w ⟨P, hP⟩ hw => by
      have := ((exSw_comp_walk (F := exSwF0) (by decide) rfl rfl hP).2.1 (Or.inl rfl)).1
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · omega
      · simpa using hw'
    rcases Finset.mem_insert.mp hv with rfl | hv1
    · exact ⟨0, ⟨by decide, ⟨[], .nil 0⟩⟩, fun r ⟨hr, hc⟩ => u01 r hc hr⟩
    · rcases Finset.mem_insert.mp hv1 with rfl | hv2
      · exact ⟨0, ⟨by decide, ⟨[(2, false)], .cons (by decide) rfl (.nil 0)⟩⟩,
          fun r ⟨hr, ⟨P, hP⟩⟩ => u01 r ⟨(2, true) :: P, .cons (by decide) rfl hP⟩ hr⟩
      · rcases Finset.mem_insert.mp hv2 with rfl | hv3
        · exact ⟨2, ⟨by decide, ⟨[], .nil 2⟩⟩, fun r ⟨hr, hc⟩ => u23 r hc hr⟩
        · have : v = 3 := by simpa using hv3
          subst this
          exact ⟨2, ⟨by decide, ⟨[(3, false)], .cons (by decide) rfl (.nil 2)⟩⟩,
            fun r ⟨hr, ⟨P, hP⟩⟩ => u23 r ⟨(3, true) :: P, .cons (by decide) rfl hP⟩ hr⟩
  · refine ⟨hFT, ⟨exSw_isForest rfl (by decide) rfl rfl, hGV.symm, by rw [hGV]; decide, ?_,
        hsubE exSwF01 rfl rfl rfl hGE⟩,
      ⟨Finset.Subset.refl _, by decide, fun _ _ => ⟨rfl, rfl⟩⟩,
      fun _ he => ⟨exSw_stretch_le_three (by decide) rfl rfl hGV hG he, by simpa [exSwL01] using hσ⟩⟩
    intro v hv; rw [hGV] at hv
    have u01 : ∀ w, exSwF01.Connected 0 w → w ∈ ({0, 2, 3} : Finset ℕ) → w = 0 := fun w ⟨P, hP⟩ hw => by
      have := ((exSw_comp_walk (F := exSwF01) (by decide) rfl rfl hP).1 (Or.inl rfl)).1
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · rfl
      · rcases Finset.mem_insert.mp hw' with rfl | hw''
        · omega
        · simp only [Finset.mem_singleton] at hw''; omega
    rcases Finset.mem_insert.mp hv with rfl | hv1
    · exact ⟨0, ⟨by decide, ⟨[], .nil 0⟩⟩, fun r ⟨hr, hc⟩ => u01 r hc hr⟩
    · rcases Finset.mem_insert.mp hv1 with rfl | hv2
      · exact ⟨0, ⟨by decide, ⟨[(2, false)], .cons (by decide) rfl (.nil 0)⟩⟩,
          fun r ⟨hr, ⟨P, hP⟩⟩ => u01 r ⟨(2, true) :: P, .cons (by decide) rfl hP⟩ hr⟩
      · rcases Finset.mem_insert.mp hv2 with rfl | hv3
        · exact ⟨2, ⟨by decide, ⟨[], .nil 2⟩⟩, fun r ⟨_, ⟨P, hP⟩⟩ =>
            (exSw_comp_walk (F := exSwF01) (by decide) rfl rfl hP).2.2 (by decide) (Or.inl rfl)⟩
        · have : v = 3 := by simpa using hv3
          subst this
          exact ⟨3, ⟨by decide, ⟨[], .nil 3⟩⟩, fun r ⟨_, ⟨P, hP⟩⟩ =>
            (exSw_comp_walk (F := exSwF01) (by decide) rfl rfl hP).2.2 (by decide) (Or.inr rfl)⟩
  · refine ⟨hFT, ⟨exSw_isForest rfl (by decide) rfl rfl, hGV.symm, by rw [hGV]; decide, ?_,
        hsubE exSwFempty rfl rfl rfl (Finset.empty_subset _)⟩,
      ⟨Finset.Subset.refl _, by decide, fun _ _ => ⟨rfl, rfl⟩⟩,
      fun _ he => ⟨exSw_stretch_le_three (by decide) rfl rfl hGV hG he, by simpa [exSwLempty] using hσ⟩⟩
    intro v hv
    refine ⟨v, ⟨by simpa [exSwLempty, hGV] using hv, ⟨[], .nil v⟩⟩, fun r ⟨_, ⟨P, hP⟩⟩ => ?_⟩
    cases hP with | nil => rfl | cons he _ => cases he

lemma exSw_roots_eq :
    (exSwL0.F.root 0 = 0 ∧ exSwL0.F.root 1 = 0 ∧ exSwL0.F.root 2 = 2 ∧ exSwL0.F.root 3 = 2) ∧
    (exSwL01.F.root 0 = 0 ∧ exSwL01.F.root 1 = 0 ∧ exSwL01.F.root 2 = 2 ∧ exSwL01.F.root 3 = 3) ∧
    (exSwLempty.F.root 0 = 0 ∧ exSwLempty.F.root 1 = 1 ∧ exSwLempty.F.root 2 = 2 ∧ exSwLempty.F.root 3 = 3) := by
  have exG0V : exSwG0.IsValid := fun e he => by
    have : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by simpa [exSwG0] using he
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [exSwG0]
  have hAll := exSwL_holds_all (G := exSwG0) rfl rfl rfl exG0V
  have root_eq (L : LSF) (hU : ∀ v ∈ ({0, 1, 2, 3} : Finset ℕ), ∃! r, r ∈ L.F.R ∧ L.F.F.Connected v r)
      {v r : ℕ} (hv : v ∈ ({0, 1, 2, 3} : Finset ℕ)) (hr : r ∈ L.F.R) (hc : L.F.F.Connected v r) :
      L.F.root v = r := by
    have hex : ∃ r', r' ∈ L.F.R ∧ L.F.F.Connected v r' := (hU v hv).exists
    have hrt : L.F.root v = Classical.choose hex := by
      unfold RootedForest.root
      split_ifs
      rfl
    rw [hrt]
    exact (hU v hv).unique (Classical.choose_spec hex) ⟨hr, hc⟩
  have hU0 := (hAll.1 (by decide)).2.1.2.2.2.1
  have hU01 := (hAll.2.1 (by decide)).2.1.2.2.2.1
  have hUe := hAll.2.2.2.1.2.2.2.1
  refine ⟨⟨root_eq exSwL0 hU0 (by decide) (by decide) ⟨[], .nil 0⟩,
      root_eq exSwL0 hU0 (by decide) (by decide) ⟨[(2, false)], .cons (by decide) rfl (.nil 0)⟩,
      root_eq exSwL0 hU0 (by decide) (by decide) ⟨[], .nil 2⟩,
      root_eq exSwL0 hU0 (by decide) (by decide) ⟨[(3, false)], .cons (by decide) rfl (.nil 2)⟩⟩,
    ⟨root_eq exSwL01 hU01 (by decide) (by decide) ⟨[], .nil 0⟩,
      root_eq exSwL01 hU01 (by decide) (by decide) ⟨[(2, false)], .cons (by decide) rfl (.nil 0)⟩,
      root_eq exSwL01 hU01 (by decide) (by decide) ⟨[], .nil 2⟩,
      root_eq exSwL01 hU01 (by decide) (by decide) ⟨[], .nil 3⟩⟩,
    ⟨root_eq exSwLempty hUe (by decide) (by decide) ⟨[], .nil 0⟩,
      root_eq exSwLempty hUe (by decide) (by decide) ⟨[], .nil 1⟩,
      root_eq exSwLempty hUe (by decide) (by decide) ⟨[], .nil 2⟩,
      root_eq exSwLempty hUe (by decide) (by decide) ⟨[], .nil 3⟩⟩⟩

lemma exSw_sparsified_of_eq {G S : MGraph} {L : LSF}
    (hV : S.V = L.F.R) (hE : S.E = G.E \ L.F.F.E)
    (hEnds : ∀ e ∈ S.E, S.tail e = L.F.root (G.tail e) ∧ S.head e = L.F.root (G.head e))
    (hwstr : L.wstr = fun _ => 3) (hCard : (S.E.card : ℝ) ≤ (G.m : ℝ) * 5 / 2) :
    IsSparsifiedCoreGraph G L (fun _ => 1) 2 5 1 S (fun e => [(e, true)]) := by
  have hSub : (coreGraph G L).IsSubgraph S := ⟨hV.le, hE.le, fun e he => hEnds e he⟩
  have hEmb : Embedding.IsEmbedding (fun e => [(e, true)]) (coreGraph G L) S := by
    refine ⟨hV.symm.le, fun e he => ?_⟩
    have heS : e ∈ S.E := hE.symm ▸ he
    refine MGraph.IsWalk.cons (u := (coreGraph G L).tail e) (x := (e, true)) (P := []) heS ?_ ?_
    · simpa [MGraph.src, coreGraph] using (hEnds e heS).1
    · simpa [MGraph.dst, (hEnds e heS).2, coreGraph] using MGraph.IsWalk.nil (S.head e)
  have hApp : ∀ e ∈ (coreGraph G L).E, ∀ e' ∈ walkEdges [(e, true)],
      approx2 (coreLen L (fun _ => 1) e) (coreLen L (fun _ => 1) e') := by
    intro e _ e' he'
    have hEq : e' = e := by simpa [walkEdges] using he'
    subst hEq; refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp [coreLen, hwstr]; try norm_num)
  have hLen : (Embedding.length (fun e => [(e, true)]) (coreGraph G L) : ℝ) ≤ 5 := by
    have hnat : Embedding.length (fun e => [(e, true)]) (coreGraph G L) ≤ 1 := by
      unfold Embedding.length; refine Finset.sup_le fun e _ => by simp
    exact le_trans (Nat.cast_le (α := ℝ).mpr hnat) (by norm_num)
  have hEcong : Embedding.econg (fun e => [(e, true)]) (coreGraph G L) S (fun _ => 1) (fun _ => 1) ≤ 2 * 1 := by
    unfold Embedding.econg Embedding.econgAt
    split_ifs with hne
    · have hsup : S.E.sup' hne (fun eH =>
          (∑ e ∈ (coreGraph G L).E with eH ∈ walkEdges [(e, true)], (1 : ℝ)) / 1) ≤ 1 := by
        refine Finset.sup'_le hne _ fun eH heH => ?_
        rw [hE] at heH
        have hf : (coreGraph G L).E.filter (fun e => eH ∈ walkEdges [(e, true)]) = {eH} := by
          ext x
          simp only [Finset.mem_filter, walkEdges, List.map_cons, List.map_nil,
            List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton]
          exact ⟨fun h => h.2.symm, fun h => ⟨h ▸ heH, h.symm⟩⟩
        rw [hf, Finset.sum_singleton, div_one]
      exact le_trans hsup (by norm_num)
    · norm_num
  exact ⟨hSub, hEmb, hApp, hLen, hEcong, hCard⟩

private lemma exSw_deg_le (G : MGraph) (v : ℕ) : G.deg v ≤ 2 * G.E.card := by
  unfold MGraph.deg
  have h1 : (G.E.filter fun e => G.tail e = v).card ≤ G.E.card := Finset.card_filter_le _ _
  have h2 : (G.E.filter fun e => G.head e = v).card ≤ G.E.card := Finset.card_filter_le _ _
  omega

lemma exSw_updateEnc_split_le (G : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) :
    G.updateEnc (.split v v' St Sh) ≤ 2 * G.E.card + 1 := by
  simp only [MGraph.updateEnc]
  have hm := Nat.min_le_left ((G.applyUpdate (.split v v' St Sh)).deg v)
    ((G.applyUpdate (.split v v' St Sh)).deg v')
  have hd := exSw_deg_le (G.applyUpdate (.split v v' St Sh)) v
  have hE : (G.applyUpdate (.split v v' St Sh)).E = G.E := rfl
  rw [hE] at hd; omega

/-- **Counterexample to dropping `ToolSwitchedRecourse` when `d > 1` (`jtree.tex` page 30, line 852)**:
at `(k = 2, τ = 2, M = 20, N = 4)` on `exSwDyn`, `exSwTool` satisfies all fixed-branch `IsSpecUpTo`,
`ToolMWUUpTo`, `ToolEmbedsSurvivingUpTo`, and `ToolNoReinsertUpTo` guarantees, yet **violates
`ToolSwitchedRecourse`** under `b(1) = 0, b(2) = 1` (`3 + 5 = 8 > 6 = exSwParams.γ_r 20 * 2`). -/
theorem exSwitchedRecourse_counterexample :
    let P := exSwParams; let T := exSwTool; let D := exSwDyn
    let k := 2; let τ := 2; let M := 20; let N := 4
    let Ψ : ℝ := 1; let c : ℕ → ℕ → ℝ := fun _ _ => 0; let w : ℕ → ℕ → ℝ := fun _ _ => 1
    let σ_mwu : ℕ → ℝ := fun _ => 3
    let st := fun t => (T.run k D t).1; let U_S := fun t => (T.run k D t).2
    P.Valid ∧ 0 < k ∧ (D.G 0).IsValid ∧ D.IsValid τ ∧ LengthsStable D τ ∧
    WeakHiddenStable D τ Ψ c w ∧ (D.G 0).m ≤ M ∧ (D.G 0).n ≤ N ∧
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N ∧
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraph (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M)
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ,
      WeakHiddenStable (T.coreInstance k D j) τ Ψ' (T.coreC k D c j) (T.coreW k D w j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n) ∧
    (∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (st t) j).E, T.emb (st t) j e = [(e, true)]) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k, NoBatchReinsert (T.S (st (t - 1)) j) (U_S t j)) ∧
    ¬ T.ToolSwitchedRecourse P := by
  dsimp only
  have hG0_V : (exSwDyn.G 0).V = {0, 1, 2, 3} := rfl
  have hG1_V : (exSwDyn.G 1).V = {0, 1, 2, 3} := rfl
  have hG2_V : (exSwDyn.G 2).V = {0, 1, 2, 3} := rfl
  have hG0_E : (exSwDyn.G 0).E = {0, 1, 2, 3, 4} := rfl
  have hG1_E : (exSwDyn.G 1).E = {1, 2, 3, 4} := by
    simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate, exSwG0]
  have hG2_E : (exSwDyn.G 2).E = {2, 3, 4} := by
    simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate, exSwG0]
  have hG_tail : ∀ t, (exSwDyn.G t).tail = exSwG0.tail := fun t => by
    rcases t with _ | _ | _ <;> simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate]
  have hG_head : ∀ t, (exSwDyn.G t).head = exSwG0.head := fun t => by
    rcases t with _ | _ | _ <;> simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate]
  have hG0_val : (exSwDyn.G 0).IsValid := fun e he => by
    have : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by simpa [hG0_E] using he
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [exSwDyn, exSwG0]
  have hG1_val : (exSwDyn.G 1).IsValid := by
    rw [MGraph.IsValid, hG1_V, hG1_E, hG_tail 1, hG_head 1]
    exact by decide
  have hG2_val : (exSwDyn.G 2).IsValid := by
    rw [MGraph.IsValid, hG2_V, hG2_E, hG_tail 2, hG_head 2]
    exact by decide
  have hDyn_val : exSwDyn.IsValid 2 := fun t ht1 ht2 => by
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
    · refine ⟨?_, rfl⟩; simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwDyn, exSwG0]
    · refine ⟨?_, rfl⟩; simp only [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwDyn]
      exact ⟨by change 1 ∈ (exSwDyn.G 1).E; rw [hG1_E]; decide, True.intro⟩
  have hTh : (((Finset.Icc 1 2).sum fun s => (exSwDyn.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold 2 20 4 := by
    have hsum : (Finset.Icc 1 2).sum (fun s => (exSwDyn.U s).length) = 2 := by decide
    rw [hsum]; unfold SparseCoreTool.updateThreshold
    have hlog0 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    have hlog2 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlogSq : (Real.log (6 : ℝ)) ^ 2 < 4 := by have := log_six_lt_two; nlinarith
    rw [show ((4 : ℕ) : ℝ) + 2 = 6 by norm_num, le_div_iff₀ (by positivity)]
    push_cast; nlinarith
  let S01 := exSwSInit.applyBatch exSwU01
  let S02 := S01.applyBatch exSwU02
  let S11 := exSwSInit.applyBatch exSwU11
  let S12 := S11.applyBatch exSwU12
  have hS01 : S01.V = {0, 2, 3} ∧ S01.E = {1, 3, 4} ∧
      S01.tail 1 = 0 ∧ S01.head 1 = 2 ∧ S01.tail 3 = 2 ∧ S01.head 3 = 3 ∧
      S01.tail 4 = 0 ∧ S01.head 4 = 3 := by
    dsimp only [S01]
    simp only [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU01, Function.update, List.foldl]
    exact ⟨by decide, by decide, by decide⟩
  have hS02 : S02.V = {0, 2, 3} ∧ S02.E = {3, 4} ∧
      S02.tail 3 = 2 ∧ S02.head 3 = 3 ∧ S02.tail 4 = 0 ∧ S02.head 4 = 3 := by
    dsimp only [S02, exSwU02, MGraph.applyBatch]
    exact ⟨hS01.1, by change S01.E.erase 1 = {3, 4}; rw [hS01.2.1]; decide,
      hS01.2.2.2.2.1, hS01.2.2.2.2.2.1, hS01.2.2.2.2.2.2.1, hS01.2.2.2.2.2.2.2⟩
  have hS11 : S11.V = {0, 2} ∧ S11.E = {1, 4} ∧
      S11.tail 1 = 0 ∧ S11.head 1 = 2 ∧ S11.tail 4 = 0 ∧ S11.head 4 = 2 := by
    dsimp only [S11]; simp [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU11]
  have hS12 : S12.V = {0, 1, 2, 3} ∧ S12.E = {2, 3, 4} ∧
      S12.tail 2 = 0 ∧ S12.head 2 = 1 ∧ S12.tail 3 = 2 ∧ S12.head 3 = 3 ∧
      S12.tail 4 = 1 ∧ S12.head 4 = 3 := by
    dsimp only [S12, S11]
    simp only [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU11, exSwU12, Function.update, List.foldl]
    exact ⟨by decide, by decide, by decide⟩
  have hRunS : exSwTool.S (exSwTool.run 2 exSwDyn 0).1 0 = exSwSInit ∧
      exSwTool.S (exSwTool.run 2 exSwDyn 0).1 1 = exSwSInit ∧
      exSwTool.S (exSwTool.run 2 exSwDyn 1).1 0 = S01 ∧
      exSwTool.S (exSwTool.run 2 exSwDyn 1).1 1 = S11 ∧
      exSwTool.S (exSwTool.run 2 exSwDyn 2).1 0 = S02 ∧
      exSwTool.S (exSwTool.run 2 exSwDyn 2).1 1 = S12 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hB01 : exSwSInit.BatchIsValid exSwU01 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, MGraph.applyUpdate, exSwSInit, exSwU01]
  have hB02 : S01.BatchIsValid exSwU02 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwU02, hS01.2.1]
  have hB11 : exSwSInit.BatchIsValid exSwU11 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwSInit, exSwU11]
  have hB12 : S11.BatchIsValid exSwU12 := by
    dsimp only [S11]
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, MGraph.applyBatch, MGraph.applyUpdate,
      exSwSInit, exSwU11, exSwU12, Function.update]
  have hEnc01 : exSwSInit.batchEnc exSwU01 ≤ 7 := by
    simp only [exSwU01, MGraph.batchEnc, MGraph.updateEnc]
    have hsp := exSw_updateEnc_split_le (exSwSInit.applyUpdate (.delete 0)) 2 3 {4} {4}
    have hcard : (exSwSInit.applyUpdate (.delete 0)).E.card = 2 := by simp [MGraph.applyUpdate, exSwSInit]
    simp only [MGraph.updateEnc] at hsp; omega
  have hEnc12 : S11.batchEnc exSwU12 ≤ 11 := by
    simp only [exSwU12, MGraph.batchEnc, MGraph.updateEnc]
    have hs1 := exSw_updateEnc_split_le (S11.applyUpdate (.delete 1)) 0 1 {4} {4}
    have hs2 := exSw_updateEnc_split_le ((((S11.applyUpdate (.delete 1)).applyUpdate
      (.split 0 1 {4} {4})).applyUpdate (.insert 2 0 1))) 2 3 {4} {4}
    have hc1 : (S11.applyUpdate (.delete 1)).E.card = 1 := by simp [MGraph.applyUpdate, hS11.2.1]
    have hc2 : ((((S11.applyUpdate (.delete 1)).applyUpdate
        (.split 0 1 {4} {4})).applyUpdate (.insert 2 0 1))).E.card = 2 := by
      simp [MGraph.applyUpdate, hS11.2.1]
    simp only [MGraph.updateEnc] at hs1 hs2; omega
  have rBound (r t : ℕ) (hr : r ≤ 4) : (r : ℝ) ≤ exSwParams.c_R * ((20 : ℝ) / (2 : ℝ) +
      (((Finset.Icc 1 t).sum fun s => (exSwDyn.U s).length : ℕ) : ℝ) * (Real.log ((4 : ℝ) + 2)) ^ 2 + 1) := by
    have hnn : 0 ≤ (((Finset.Icc 1 t).sum fun s => (exSwDyn.U s).length : ℕ) : ℝ) * (Real.log ((4 : ℝ) + 2)) ^ 2 := by
      positivity
    have hr' : (r : ℝ) ≤ (4 : ℝ) := by exact_mod_cast hr
    simp only [exSwParams]; rw [one_mul, show (20 : ℝ) / (2 : ℝ) = 10 by norm_num]; linarith [hnn, hr']
  rcases exSw_roots_eq with ⟨⟨r00, r01, r02, r03⟩, ⟨r10, r11, r12, r13⟩, ⟨re0, re1, re2, re3⟩⟩
  refine ⟨exSwParams_valid, by omega, hG0_val, hDyn_val, fun _ _ _ _ _ _ _ => rfl,
    fun _ _ => ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp,
      ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp, fun _ _ => by norm_num⟩,
      fun _ _ _ _ _ => by norm_num, fun _ _ => ⟨zero_lt_one, by simp, zero_lt_one, by simp [exSwDyn]⟩⟩,
    by simp [MGraph.m, hG0_E], by simp [MGraph.n, hG0_V], hTh,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht j hj
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · refine ⟨(exSwL_holds_all hG0_V (hG_tail 0) (hG_head 0) hG0_val).1 (by rw [hG0_E]; decide), ?_, fun _ => ?_⟩
      · rw [hRunS.1]; refine exSw_sparsified_of_eq rfl (by rw [hG0_E]; decide) (fun e he => ?_) rfl ?_
        · have : e = 0 ∨ e = 1 ∨ e = 4 := by simpa [exSwSInit] using he
          rcases this with rfl | rfl | rfl <;>
            simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwSInit, r00, r01, r02, r03, hG_tail 0, hG_head 0, exSwG0]
        · simp [MGraph.m, hG0_E, exSwSInit]; norm_num
      · exact rBound _ 0 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0])
    · refine ⟨(exSwL_holds_all hG0_V (hG_tail 0) (hG_head 0) hG0_val).1 (by rw [hG0_E]; decide), ?_, fun _ => ?_⟩
      · rw [hRunS.2.1]; refine exSw_sparsified_of_eq rfl (by rw [hG0_E]; decide) (fun e he => ?_) rfl ?_
        · have : e = 0 ∨ e = 1 ∨ e = 4 := by simpa [exSwSInit] using he
          rcases this with rfl | rfl | rfl <;>
            simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwSInit, r00, r01, r02, r03, hG_tail 0, hG_head 0, exSwG0]
        · simp [MGraph.m, hG0_E, exSwSInit]; norm_num
      · exact rBound _ 0 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0])
    · refine ⟨(exSwL_holds_all hG1_V (hG_tail 1) (hG_head 1) hG1_val).2.1 (by rw [hG1_E]; decide), ?_, fun _ => ?_⟩
      · rw [hRunS.2.2.1]; refine exSw_sparsified_of_eq hS01.1 (by rw [hG1_E]; exact hS01.2.1) (fun e he => ?_) rfl ?_
        · have : e = 1 ∨ e = 3 ∨ e = 4 := by rw [hS01.2.1] at he; simpa using he
          rcases this with rfl | rfl | rfl
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS01.2.2.1, hS01.2.2.2.1, r10, r12, hG_tail 1, hG_head 1, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS01.2.2.2.2.1, hS01.2.2.2.2.2.1, r12, r13, hG_tail 1, hG_head 1, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS01.2.2.2.2.2.2.1, hS01.2.2.2.2.2.2.2, r11, r13, hG_tail 1, hG_head 1, exSwG0]
        · simp [MGraph.m, hG1_E, hS01.2.1]; norm_num
      · exact rBound _ 1 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL01])
    · refine ⟨(exSwL_holds_all hG1_V (hG_tail 1) (hG_head 1) hG1_val).1 (by rw [hG1_E]; decide), ?_, fun _ => ?_⟩
      · rw [hRunS.2.2.2.1]; refine exSw_sparsified_of_eq hS11.1 (by rw [hG1_E]; exact hS11.2.1) (fun e he => ?_) rfl ?_
        · have : e = 1 ∨ e = 4 := by rw [hS11.2.1] at he; simpa using he
          rcases this with rfl | rfl
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS11.2.2.1, hS11.2.2.2.1, r00, r02, hG_tail 1, hG_head 1, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS11.2.2.2.2.1, hS11.2.2.2.2.2, r01, r03, hG_tail 1, hG_head 1, exSwG0]
        · simp [MGraph.m, hG1_E, hS11.2.1]; norm_num
      · exact rBound _ 1 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0])
    · refine ⟨(exSwL_holds_all hG2_V (hG_tail 2) (hG_head 2) hG2_val).2.1 (by rw [hG2_E]; decide), ?_, fun _ => ?_⟩
      · rw [hRunS.2.2.2.2.1]; refine exSw_sparsified_of_eq hS02.1 (by rw [hG2_E]; exact hS02.2.1) (fun e he => ?_) rfl ?_
        · have : e = 3 ∨ e = 4 := by rw [hS02.2.1] at he; simpa using he
          rcases this with rfl | rfl
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS02.2.2.1, hS02.2.2.2.1, r12, r13, hG_tail 2, hG_head 2, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS02.2.2.2.2.1, hS02.2.2.2.2.2, r11, r13, hG_tail 2, hG_head 2, exSwG0]
        · simp [MGraph.m, hG2_E, hS02.2.1]; norm_num
      · exact rBound _ 2 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL01])
    · refine ⟨(exSwL_holds_all hG2_V (hG_tail 2) (hG_head 2) hG2_val).2.2, ?_, fun _ => ?_⟩
      · rw [hRunS.2.2.2.2.2]; refine exSw_sparsified_of_eq hS12.1 (by rw [hG2_E]; exact hS12.2.1) (fun e he => ?_) rfl ?_
        · have : e = 2 ∨ e = 3 ∨ e = 4 := by rw [hS12.2.1] at he; simpa using he
          rcases this with rfl | rfl | rfl
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS12.2.2.1, hS12.2.2.2.1, re0, re1, hG_tail 2, hG_head 2, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS12.2.2.2.2.1, hS12.2.2.2.2.2.1, re2, re3, hG_tail 2, hG_head 2, exSwG0]
          · simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, hS12.2.2.2.2.2.2.1, hS12.2.2.2.2.2.2.2, re1, re3, hG_tail 2, hG_head 2, exSwG0]
        · simp [MGraph.m, hG2_E, hS12.2.1]; norm_num
      · exact rBound _ 2 (by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwLempty])
  · intro t ht1 ht2 j hj
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0, exSwL01, exSwF0, exSwF01],
        fun _ _ _ _ => rfl, fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h, hB01, rfl⟩
    · exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0], fun _ _ _ _ => rfl,
        fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h, hB11, rfl⟩
    · exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL01], fun _ _ _ _ => rfl,
        fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h, hB02, rfl⟩
    · exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwL0, exSwLempty, exSwFempty], fun _ _ _ _ => rfl,
        fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h, hB12, rfl⟩
  · intro t ht j hj
    have hU1 : (Finset.Icc 1 1).sum (fun s => (exSwDyn.U s).length) = 1 := by decide
    have hU2 : (Finset.Icc 1 2).sum (fun s => (exSwDyn.U s).length) = 2 := by decide
    have h33 : exSwParams.γ_r 20 * (((20 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) = ((33 : ℕ) : ℝ) := by
      simp [exSwParams]; norm_num
    have h36 : exSwParams.γ_r 20 * (((20 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) = ((36 : ℕ) : ℝ) := by
      simp [exSwParams]; norm_num
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simp only [exSwDyn, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty,
        Nat.cast_zero, mul_zero, le_refl, true_and]
      norm_num [exSwParams]
    · simp only [exSwDyn, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty,
        Nat.cast_zero, mul_zero, le_refl, true_and]
      norm_num [exSwParams]
    · rw [hU1, Finset.Icc_self, Finset.sum_singleton]
      exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwParams, exSwU01],
        by dsimp only [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt]; rw [h33]; exact_mod_cast (by omega : exSwSInit.batchEnc exSwU01 ≤ 33)⟩
    · rw [hU1, Finset.Icc_self, Finset.sum_singleton]
      have : exSwSInit.batchEnc exSwU11 ≤ 1 := by simp [MGraph.batchEnc, MGraph.updateEnc, exSwU11]
      exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwParams, exSwU11],
        by dsimp only [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt]; rw [h33]; exact_mod_cast (by omega : exSwSInit.batchEnc exSwU11 ≤ 33)⟩
    · rw [hU2, Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
      have h02 : S01.batchEnc exSwU02 ≤ 1 := by simp [MGraph.batchEnc, MGraph.updateEnc, exSwU02]
      exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwParams, exSwU01, exSwU02]; norm_num,
        by dsimp only [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt]; rw [h36]; exact_mod_cast (by omega : exSwSInit.batchEnc exSwU01 + S01.batchEnc exSwU02 ≤ 36)⟩
    · rw [hU2, Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
      have h11 : exSwSInit.batchEnc exSwU11 ≤ 1 := by simp [MGraph.batchEnc, MGraph.updateEnc, exSwU11]
      exact ⟨by simp [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwParams, exSwU11, exSwU12]; norm_num,
        by dsimp only [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt]; rw [h36]; exact_mod_cast (by omega : exSwSInit.batchEnc exSwU11 + S11.batchEnc exSwU12 ≤ 36)⟩
  · intro j hj
    refine ⟨10, fun t ht => ?_⟩
    have hcoreC : ∀ s e, exSwTool.coreC 2 exSwDyn (fun _ _ => 0) j s e = 0 := fun s e => by
      simp [SparseCoreTool.coreC, SparseCoreTool.coreCAt, passSparseCoreC, passCoreC]
    have hSame : ∀ s ≤ 2, (exSwTool.S (exSwTool.run 2 exSwDyn s).1 j).E =
        (coreGraph (exSwDyn.G s) (exSwTool.lsfs (exSwTool.run 2 exSwDyn s).1 j)).E := fun s hs => by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
        rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> dsimp only [coreGraph]
      · rw [hRunS.1, hG0_E]; decide
      · rw [hRunS.2.2.1, hS01.2.1, hG1_E]; decide
      · rw [hRunS.2.2.2.2.1, hS02.2.1, hG2_E]; decide
      · rw [hRunS.2.1, hG0_E]; decide
      · rw [hRunS.2.2.2.1, hS11.2.1, hG1_E]; decide
      · rw [hRunS.2.2.2.2.2, hS12.2.1, hG2_E]; decide
    have hwstr3 : ∀ s ≤ 2, (exSwTool.lsfs (exSwTool.run 2 exSwDyn s).1 j).wstr = fun _ => 3 := fun s hs => by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
        rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> rfl
    have hcoreW : ∀ s ≤ 2, ∀ e ∈ (exSwTool.S (exSwTool.run 2 exSwDyn s).1 j).E,
        exSwTool.coreW 2 exSwDyn (fun _ _ => 1) j s e = 6 := by
      intro s hs e he; have heC := hSame s hs ▸ he
      have hemb : ∀ x, exSwTool.emb (exSwTool.run 2 exSwDyn s).1 j x = [(x, true)] := fun _ => rfl
      dsimp only [SparseCoreTool.coreW, SparseCoreTool.coreWAt, passSparseCoreW, passCoreW]
      simp_rw [hemb]
      rw [hwstr3 s hs]
      have hEq : (∑ x ∈ (coreGraph (exSwDyn.G s) (exSwTool.lsfs (exSwTool.run 2 exSwDyn s).1 j)).E,
          ((3 : ℝ) * 1) * walkCount [(x, true)] e) =
          ∑ x ∈ (coreGraph (exSwDyn.G s) (exSwTool.lsfs (exSwTool.run 2 exSwDyn s).1 j)).E,
            if x = e then (3 : ℝ) else 0 :=
        Finset.sum_congr rfl fun x _ => by
          by_cases hxe : x = e
          · subst hxe; rw [walkCount_cons, walkCount_nil]; simp
          · rw [walkCount_cons, walkCount_nil]; simp [hxe]
      have hsum1 : (∑ x ∈ (coreGraph (exSwDyn.G s) (exSwTool.lsfs (exSwTool.run 2 exSwDyn s).1 j)).E,
          ((3 : ℝ) * 1) * walkCount [(x, true)] e) = 3 := by
        rw [hEq, Finset.sum_ite_eq']
        simp only [heC, ↓reduceIte]
      rw [hsum1]; norm_num
    have hlog6 : |Real.log (6 : ℝ)| ≤ 10 := by
      rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
      exact le_trans (le_of_lt log_six_lt_two) (by norm_num)
    have hlog3 : |Real.log (3 : ℝ)| ≤ 10 := by
      rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
      exact le_trans (Real.log_le_log (by norm_num) (by norm_num)) (le_trans (le_of_lt log_six_lt_two) (by norm_num))
    refine ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, hcoreC],
      ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, hcoreC],
        fun e he => by simp only [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt] at he; rw [hcoreC, mul_zero, abs_zero, hcoreW t ht e he]; norm_num⟩,
      fun e he t' ht' hNotIns => by
        by_cases he' : e ∈ (exSwTool.S (exSwTool.run 2 exSwDyn t').1 j).E
        · rw [hcoreW t ht e (by simpa [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt] using he), hcoreW t' (le_trans ht' ht) e he']; norm_num
        · exfalso; simp only [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt] at he
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
            rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
            rcases (by omega : t' = 0 ∨ t' = 1 ∨ t' = 2) with rfl | rfl | rfl
          all_goals try (exfalso; omega)
          · rw [hRunS.1] at he he'; exact he' he
          · rw [hRunS.2.2.1] at he; rw [hRunS.1] at he'; rw [hS01.2.1] at he; change e ∉ exSwSInit.E at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact he' (by simp [exSwSInit])
            · rcases Finset.mem_insert.mp he1 with rfl | he2
              · exact hNotIns 1 (by omega) (by omega) (.insert 3 2 3)
                  (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU01]) rfl
              · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by simp [exSwSInit])
          · rw [hRunS.2.2.1] at he he'; exact he' he
          · rw [hRunS.2.2.2.2.1] at he; rw [hRunS.1] at he'; rw [hS02.2.1] at he; change e ∉ exSwSInit.E at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact hNotIns 1 (by omega) (by omega) (.insert 3 2 3)
                (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU01]) rfl
            · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by simp [exSwSInit])
          · rw [hRunS.2.2.2.2.1] at he; rw [hRunS.2.2.1] at he'; rw [hS02.2.1] at he; rw [hS01.2.1] at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact he' (by decide)
            · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by decide)
          · rw [hRunS.2.2.2.2.1] at he he'; exact he' he
          · rw [hRunS.2.1] at he he'; exact he' he
          · rw [hRunS.2.2.2.1] at he; rw [hRunS.2.1] at he'; rw [hS11.2.1] at he; change e ∉ exSwSInit.E at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact he' (by simp [exSwSInit])
            · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by simp [exSwSInit])
          · rw [hRunS.2.2.2.1] at he he'; exact he' he
          · rw [hRunS.2.2.2.2.2] at he; rw [hRunS.2.1] at he'; rw [hS12.2.1] at he; change e ∉ exSwSInit.E at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact hNotIns 2 (by omega) (le_refl 2) (.insert 2 0 1)
                (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU12]) rfl
            · rcases Finset.mem_insert.mp he1 with rfl | he2
              · exact hNotIns 2 (by omega) (le_refl 2) (.insert 3 2 3)
                  (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU12]) rfl
              · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by simp [exSwSInit])
          · rw [hRunS.2.2.2.2.2] at he; rw [hRunS.2.2.2.1] at he'; rw [hS12.2.1] at he; rw [hS11.2.1] at he'
            rcases Finset.mem_insert.mp he with rfl | he1
            · exact hNotIns 2 (by omega) (le_refl 2) (.insert 2 0 1)
                (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU12]) rfl
            · rcases Finset.mem_insert.mp he1 with rfl | he2
              · exact hNotIns 2 (by omega) (le_refl 2) (.insert 3 2 3)
                  (by simp [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt, exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU12]) rfl
              · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by decide)
          · rw [hRunS.2.2.2.2.2] at he he'; exact he' he,
      fun e he => by
        simp only [SparseCoreTool.coreInstance, SparseCoreTool.coreInstanceAt] at he ⊢
        rw [hcoreW t ht e he]; unfold coreLen; rw [hwstr3 t ht]
        exact ⟨by norm_num, hlog6, by simp [exSwDyn], by simpa [exSwDyn] using hlog3⟩⟩
  · simp only [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwParams, pow_one]
    have hlog26 : 1 ≤ Real.log (26 : ℝ) := by
      have : Real.exp 1 < 26 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      exact le_of_lt ((Real.lt_log_iff_exp_lt (by norm_num)).2 this)
    rw [show ((20 : ℕ) : ℝ) + (4 : ℕ) + 2 = 26 by norm_num]; push_cast; nlinarith
  · intro t ht e _
    have hw3 : ∀ j < 2, (exSwTool.lsfs (exSwTool.run 2 exSwDyn t).1 j).wstr e = 3 := fun j hj => by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> rfl
    rw [Finset.sum_range_succ, Finset.sum_range_one, hw3 0 (by omega), hw3 1 (by omega)]; norm_num
  · intro _ _ _ _ _ _; rfl
  · intro t ht1 ht2 j hj e he u hu hIns
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [hRunS.1] at he
      have : u = .delete 0 ∨ u = .split 2 3 {4} {4} ∨ u = .insert 3 2 3 := by
        simpa [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU01] using hu
      rcases this with rfl | rfl | rfl <;> (simp [Update.Inserts, exSwSInit] at hIns he; try omega)
    · have : u = .delete 0 := by simpa [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU11] using hu
      subst this; simp [Update.Inserts] at hIns
    · have : u = .delete 1 := by simpa [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU02] using hu
      subst this; simp [Update.Inserts] at hIns
    · change e ∈ (exSwTool.S (exSwTool.run 2 exSwDyn 1).1 1).E at he
      rw [hRunS.2.2.2.1, hS11.2.1] at he
      have : u = .delete 1 ∨ u = .split 0 1 {4} {4} ∨ u = .insert 2 0 1 ∨ u = .split 2 3 {4} {4} ∨ u = .insert 3 2 3 := by
        simpa [exSwTool, SparseCoreTool.run, SparseCoreTool.runAt, exSwU12] using hu
      rcases this with rfl | rfl | rfl | rfl | rfl <;> (simp [Update.Inserts] at hIns he; try omega)
  · intro hSw
    let b : ℕ → ℕ := fun s => if s ≤ 1 then 0 else 1
    have hbad := hSw 2 2 20 4 exSwDyn 1 (fun _ _ => 0) (fun _ _ => 1) b
      (by omega) hG0_val hDyn_val (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ => ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp,
        ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp, fun _ _ => by norm_num⟩,
        fun _ _ _ _ _ => by norm_num, fun _ _ => ⟨zero_lt_one, by simp, zero_lt_one, by simp [exSwDyn]⟩⟩)
      (by simp [MGraph.m, hG0_E]) (by simp [MGraph.n, hG0_V]) hTh
      (fun s => by dsimp [b]; split_ifs <;> omega) 2 (le_refl 2)
    have h1 : ((exSwTool.runAt 2 20 4 exSwDyn 1).2 (b 1)).length = 3 := by simp [b, exSwTool, SparseCoreTool.runAt, exSwU01]
    have h2 : ((exSwTool.runAt 2 20 4 exSwDyn 2).2 (b 2)).length = 5 := by simp [b, exSwTool, SparseCoreTool.runAt, exSwU12]
    have hLHS : (Finset.Icc 1 2).sum (fun s => ((exSwTool.runAt 2 20 4 exSwDyn s).2 (b s)).length) = 8 := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton, h1, h2]
    have hRHS : (Finset.Icc 1 2).sum (fun s => (exSwDyn.U s).length) = 2 := by decide
    rw [hLHS, hRHS] at hbad; simp only [exSwParams] at hbad; push_cast at hbad; linarith

/-- Concrete 2-branch `SparseCoreRestartTool` curing `exSwTool`'s switched-branch recourse burst:
without restarts (`restarts r = []`), its outputs match `exSwTool` (`|U_S 1 0| = 3`, `|U_S 2 1| = 5`);
whenever branch `1` is restarted by round `1` (`1 ∈ restarts 0 ∨ 1 ∈ restarts 1`), step `2` on
branch `1` maintains `exSwL0` and emits only `[.delete 1]` (`|U_S 2 1| = 1 ≤ γ_r · |U 2| = 3`). -/
def exSwRestartTool : SparseCoreRestartTool where
  State := ℕ × MGraph × MGraph × Bool × Bool × ℕ
  init := fun _ _ _ _ _ _ => (0, exSwSInit, exSwSInit, false, false, 0)
  restart := fun (t, S0, S1, rstReq, updUsedRst, extraCost) j =>
    (t, S0, S1, rstReq || (j == 1), updUsedRst, extraCost + 1)
  update := fun (t, S0, S1, rstReq, updUsedRst, extraCost) _ _ _ =>
    let used := if t = 1 then rstReq else updUsedRst
    let uS : ℕ → List Update := fun j =>
      if j = 0 then (if t = 0 then exSwU01 else if t = 1 then exSwU02 else [])
      else (if t = 0 then exSwU11 else if t = 1 then (if used then [.delete 1] else exSwU12) else [])
    ((t + 1, S0.applyBatch (uS 0), S1.applyBatch (uS 1), rstReq, used, extraCost), uS)
  lsfs := fun (t, _, _, _, updUsedRst, _) j =>
    if j = 0 then (if t = 0 then exSwL0 else exSwL01)
    else (if t ≤ 1 ∨ updUsedRst then exSwL0 else exSwLempty)
  S := fun (_, S0, S1, _, _, _) j => if j = 0 then S0 else S1
  emb := fun _ _ e => [(e, true)]
  cost := fun (t, _, _, _, _, extraCost) => t + 1 + extraCost

lemma exSwRestartTool_foldl_restart (xs : List ℕ) (t : ℕ) (S0 S1 : MGraph)
    (rstReq used : Bool) (c : ℕ) :
    xs.foldl exSwRestartTool.restart (t, S0, S1, rstReq, used, c) =
      (t, S0, S1, rstReq || decide (1 ∈ xs), used, c + xs.length) := by
  let f : ℕ × MGraph × MGraph × Bool × Bool × ℕ → ℕ → ℕ × MGraph × MGraph × Bool × Bool × ℕ :=
    exSwRestartTool.restart
  change xs.foldl f (t, S0, S1, rstReq, used, c) = _
  induction xs generalizing rstReq c with
  | nil => simp [List.foldl_nil]
  | cons x xs ih =>
    have hstep : f (t, S0, S1, rstReq, used, c) x =
        (t, S0, S1, rstReq || (x == 1), used, c + 1) := rfl
    rw [List.foldl_cons, hstep, ih]
    cases rstReq <;> by_cases hx : x = 1
    · subst hx; simp [List.length_cons]; omega
    · have hbeq : (x == 1) = false := beq_false_of_ne hx
      have hne : (1 = x) ↔ False := iff_false_intro (Ne.symm hx)
      simp [hbeq, hne, List.length_cons, Prod.mk.injEq]; omega
    · subst hx; simp [List.length_cons]; omega
    · have hbeq : (x == 1) = false := beq_false_of_ne hx
      have hne : (1 = x) ↔ False := iff_false_intro (Ne.symm hx)
      simp [hbeq, hne, List.length_cons, Prod.mk.injEq]; omega


end Counterexample

end MinCostFlow.Chain
