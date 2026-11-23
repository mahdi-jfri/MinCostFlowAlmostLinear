module

public import MinCostFlow.Basic.Dynamic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

/-!
# Total encoding size of dynamic graph updates (Lemma 2.1)

This file formalizes Lemma 2.1 (page 6): for a dynamic graph starting with `m` edges and
undergoing batches of updates `U^{(1)}, …, U^{(τ)}` with `q = ∑_t |U^{(t)}|` total updates, the
total encoding size satisfies
`∑_t Enc(U^{(t)}) ≤ 20 * (m + q) * log(m + q + 2)`,
making the `Õ(m + ∑_t |U^{(t)}|)` bound explicit.

Following the paper, the proof uses the degree-entropy potential `Φ(G) = ∑_{v ∈ V} deg(v) log deg(v)`:
edge deletions do not increase `Φ`, edge insertions increase `Φ` by `O(log(m + q + 2))`, and
splitting `v` into `v_1, v_2` decreases `Φ` by at least `(log 2) * min(deg(v_1), deg(v_2))`.
-/

public section

namespace MinCostFlow.Chain

private noncomputable def phiTerm (d : ℕ) : ℝ :=
  (d : ℝ) * Real.log (d : ℝ)

private noncomputable def degPotential (G : MGraph) : ℝ :=
  ∑ v ∈ G.V, phiTerm (G.deg v)

private lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (- (1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  rw [← Real.log_exp (1 / 2 : ℝ)]
  exact Real.log_lt_log (Real.exp_pos _) h2

private lemma log_two_lt_one : Real.log 2 < 1 := by
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (by norm_num) h

private lemma phiTerm_zero : phiTerm 0 = 0 := by simp [phiTerm]

private lemma phiTerm_one : phiTerm 1 = 0 := by simp [phiTerm]

private lemma phiTerm_nonneg (d : ℕ) : 0 ≤ phiTerm d := by
  cases d with
  | zero => simp [phiTerm]
  | succ n =>
    unfold phiTerm
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)

private lemma phiTerm_mono {a b : ℕ} (hab : a ≤ b) : phiTerm a ≤ phiTerm b := by
  cases a with
  | zero =>
    rw [phiTerm_zero]
    exact phiTerm_nonneg b
  | succ m =>
    have hb : 1 ≤ b := le_trans (Nat.succ_pos m) hab
    unfold phiTerm
    refine mul_le_mul (by exact_mod_cast hab) ?_ ?_ (by exact_mod_cast Nat.cast_nonneg b)
    · exact Real.log_le_log (by exact_mod_cast Nat.succ_pos m) (by exact_mod_cast hab)
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos m)

private lemma phiTerm_split_drop_of_le {a b : ℕ} (hab : a ≤ b) :
    Real.log 2 * (a : ℝ) ≤ phiTerm (a + b) - phiTerm a - phiTerm b := by
  cases a with
  | zero => simp [phiTerm]
  | succ m =>
    have ha_pos : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (Nat.succ_pos m) hab
    have hab_pos : (0 : ℝ) < ((m + 1 + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1 + b)
    have hlog2 : Real.log 2 ≤ Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hab_pos.ne' ha_pos.ne']
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ ha_pos]
      have hle : (2 * ((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 + b : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * (m + 1) ≤ m + 1 + b)
      linarith
    have hlogb : 0 ≤ Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ) := by
      refine sub_nonneg.mpr (Real.log_le_log hb_pos ?_)
      exact_mod_cast (by omega : b ≤ m + 1 + b)
    have h1 : Real.log 2 * ((m + 1 : ℕ) : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) := by
      calc
        Real.log 2 * ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * Real.log 2 := mul_comm _ _
        _ ≤ ((m + 1 : ℕ) : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog2 ha_pos.le
    have h2 : 0 ≤ (b : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ)) :=
      mul_nonneg hb_pos.le hlogb
    have hcalc : phiTerm (m + 1 + b) - phiTerm (m + 1) - phiTerm b =
        ((m + 1 : ℕ) : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) +
        (b : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ)) := by
      simp only [phiTerm, Nat.cast_add]
      ring
    linarith

private lemma phiTerm_split_drop (a b : ℕ) :
    Real.log 2 * ((min a b : ℕ) : ℝ) ≤ phiTerm (a + b) - phiTerm a - phiTerm b := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    exact phiTerm_split_drop_of_le hab
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [min_eq_right hba, add_comm a b]
    have h := phiTerm_split_drop_of_le hba
    linarith

private lemma phiTerm_succ_sub_le (d : ℕ) :
    phiTerm (d + 1) - phiTerm d ≤ Real.log ((d + 1 : ℕ) : ℝ) + 1 := by
  cases d with
  | zero => simp [phiTerm]
  | succ n =>
    have hd_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have hd1_pos : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (n + 1)
    have hlog : Real.log ((n + 1 + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hd1_pos.ne' hd_pos.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
      have hdiv : ((n + 1 + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = 1 / ((n + 1 : ℕ) : ℝ) := by
        have hcast : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        field_simp [hd_pos.ne']
        ring
      linarith
    have hmul : ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 1 + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
      calc
        ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 1 + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))
            ≤ ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog hd_pos.le
        _ = 1 := mul_one_div_cancel hd_pos.ne'
    have hcalc : phiTerm (n + 1 + 1) - phiTerm (n + 1) =
        Real.log ((n + 1 + 1 : ℕ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 1 + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
      simp only [phiTerm, Nat.cast_add, Nat.cast_one]
      ring
    linarith

private lemma phiTerm_add_two_sub_le (d : ℕ) :
    phiTerm (d + 2) - phiTerm d ≤ 2 * Real.log ((d + 2 : ℕ) : ℝ) + 2 := by
  have h1 := phiTerm_succ_sub_le d
  have h2 := phiTerm_succ_sub_le (d + 1)
  have hlog : Real.log ((d + 1 : ℕ) : ℝ) ≤ Real.log ((d + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos d) (by exact_mod_cast (by omega : d + 1 ≤ d + 2))
  linarith

private lemma sum_deg_eq_two_mul_m {G : MGraph} (hG : G.IsValid) :
    ∑ v ∈ G.V, G.deg v = 2 * G.m := by
  simp only [MGraph.deg, Finset.sum_add_distrib, MGraph.m]
  have htail : ∑ v ∈ G.V, (G.E.filter (fun e => G.tail e = v)).card = G.E.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun e he => ?_).trans (Finset.card_eq_sum_ones G.E).symm
    have hmem : G.tail e ∈ G.V := (hG e he).1
    rw [Finset.sum_eq_single (G.tail e)]
    · simp
    · intro v _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd hmem hnot
  have hhead : ∑ v ∈ G.V, (G.E.filter (fun e => G.head e = v)).card = G.E.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun e he => ?_).trans (Finset.card_eq_sum_ones G.E).symm
    have hmem : G.head e ∈ G.V := (hG e he).2
    rw [Finset.sum_eq_single (G.head e)]
    · simp
    · intro v _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd hmem hnot
  rw [htail, hhead]
  omega

private lemma deg_le_two_mul_m (G : MGraph) (v : ℕ) : G.deg v ≤ 2 * G.m := by
  simp only [MGraph.deg, MGraph.m]
  have h1 : (G.E.filter (fun e => G.tail e = v)).card ≤ G.E.card := Finset.card_filter_le _ _
  have h2 : (G.E.filter (fun e => G.head e = v)).card ≤ G.E.card := Finset.card_filter_le _ _
  omega

private lemma isValid_applyUpdate {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) : (G.applyUpdate u).IsValid := by
  cases u with
  | insert e a b =>
    rcases hu with ⟨_, ha, hb⟩
    intro e' he'
    simp only [MGraph.applyUpdate, Finset.mem_insert] at he' ⊢
    rcases he' with rfl | he'
    · simp [ha, hb]
    · by_cases hEq : e' = e
      · subst hEq; simp [ha, hb]
      · simp [Function.update_of_ne hEq, hG e' he']
  | delete e =>
    intro e' he'
    simp only [MGraph.applyUpdate, Finset.mem_erase] at he'
    exact hG e' he'.2
  | split v v' St Sh =>
    intro e' he'
    simp only [MGraph.applyUpdate] at he' ⊢
    have hEnds := hG e' he'
    constructor <;> split_ifs <;> simp [hEnds.1, hEnds.2]

private lemma m_applyUpdate_le (G : MGraph) (u : Update) : (G.applyUpdate u).m ≤ G.m + 1 := by
  cases u with
  | insert e a b =>
    simp only [MGraph.applyUpdate, MGraph.m]
    exact Finset.card_insert_le _ _
  | delete e =>
    simp only [MGraph.applyUpdate, MGraph.m]
    exact Nat.le_trans Finset.card_erase_le (Nat.le_succ _)
  | split v v' St Sh =>
    simp [MGraph.applyUpdate, MGraph.m]

private lemma deg_delete_le (G : MGraph) (e w : ℕ) :
    (G.applyUpdate (.delete e)).deg w ≤ G.deg w := by
  simp only [MGraph.applyUpdate, MGraph.deg]
  exact Nat.add_le_add
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset e G.E)))
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset e G.E)))

private lemma deg_insert_eq_of_ne {G : MGraph} {e a b w : ℕ} (he : e ∉ G.E)
    (hwa : w ≠ a) (hwb : w ≠ b) :
    (G.applyUpdate (.insert e a b)).deg w = G.deg w := by
  let G' := G.applyUpdate (.insert e a b)
  change G'.deg w = G.deg w
  simp only [MGraph.deg]
  have hpart : ∀ (f f' : ℕ → ℕ) (val : ℕ),
      (∀ e', f' e' = Function.update f e val e') → w ≠ val →
      (G'.E.filter (fun e' => f' e' = w)).card = (G.E.filter (fun e' => f e' = w)).card := by
    intro f f' val hf' hne
    refine congrArg Finset.card (Finset.ext fun e' => ?_)
    simp only [Finset.mem_filter, G', MGraph.applyUpdate, Finset.mem_insert, hf']
    constructor
    · rintro ⟨rfl | he', ht⟩
      · simp only [Function.update_self] at ht; exact absurd ht.symm hne
      · have hne' : e' ≠ e := fun h => he (h ▸ he')
        rw [Function.update_of_ne hne'] at ht
        exact ⟨he', ht⟩
    · rintro ⟨he', ht⟩
      have hne' : e' ≠ e := fun h => he (h ▸ he')
      exact ⟨Or.inr he', by rw [Function.update_of_ne hne']; exact ht⟩
  rw [hpart G.tail G'.tail a (fun _ => rfl) hwa, hpart G.head G'.head b (fun _ => rfl) hwb]

private lemma deg_insert_le_add_two {G : MGraph} {e a b w : ℕ} (he : e ∉ G.E) :
    (G.applyUpdate (.insert e a b)).deg w ≤ G.deg w + 2 := by
  let G' := G.applyUpdate (.insert e a b)
  change G'.deg w ≤ G.deg w + 2
  simp only [MGraph.deg]
  have hfilter : ∀ (f f' : ℕ → ℕ) (val : ℕ),
      (∀ e', f' e' = Function.update f e val e') →
      (G'.E.filter (fun e' => f' e' = w)).card ≤
        (G.E.filter (fun e' => f e' = w)).card + 1 := by
    intro f f' val hf'
    have hsub : G'.E.filter (fun e' => f' e' = w) ⊆
        insert e (G.E.filter (fun e' => f e' = w)) := by
      intro e' he'
      simp only [Finset.mem_filter, G', MGraph.applyUpdate, Finset.mem_insert, hf'] at he' ⊢
      rcases he'.1 with rfl | he'G
      · exact Or.inl rfl
      · have hne : e' ≠ e := fun h => he (h ▸ he'G)
        rw [Function.update_of_ne hne] at he'
        exact Or.inr ⟨he'G, he'.2⟩
    exact Nat.le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  have h1 := hfilter G.tail G'.tail a (fun _ => rfl)
  have h2 := hfilter G.head G'.head b (fun _ => rfl)
  omega

private lemma deg_insert_le_add_one_of_ne {G : MGraph} {e a b w : ℕ} (he : e ∉ G.E)
    (h1 : w = a ∧ w ≠ b ∨ w = b ∧ w ≠ a) :
    (G.applyUpdate (.insert e a b)).deg w ≤ G.deg w + 1 := by
  let G' := G.applyUpdate (.insert e a b)
  change G'.deg w ≤ G.deg w + 1
  simp only [MGraph.deg]
  have h_eq : ∀ (f f' : ℕ → ℕ) (val : ℕ),
      (∀ e', f' e' = Function.update f e val e') → w ≠ val →
      (G'.E.filter (fun e' => f' e' = w)).card = (G.E.filter (fun e' => f e' = w)).card := by
    intro f f' val hf' hne
    refine congrArg Finset.card (Finset.ext fun e' => ?_)
    simp only [Finset.mem_filter, G', MGraph.applyUpdate, Finset.mem_insert, hf']
    constructor
    · rintro ⟨rfl | he'G, hf⟩
      · simp only [Function.update_self] at hf; exact absurd hf.symm hne
      · have hne' : e' ≠ e := fun h => he (h ▸ he'G)
        rw [Function.update_of_ne hne'] at hf
        exact ⟨he'G, hf⟩
    · rintro ⟨he'G, hf⟩
      have hne' : e' ≠ e := fun h => he (h ▸ he'G)
      exact ⟨Or.inr he'G, by rw [Function.update_of_ne hne']; exact hf⟩
  have h_le : ∀ (f f' : ℕ → ℕ) (val : ℕ),
      (∀ e', f' e' = Function.update f e val e') →
      (G'.E.filter (fun e' => f' e' = w)).card ≤ (G.E.filter (fun e' => f e' = w)).card + 1 := by
    intro f f' val hf'
    have hsub : G'.E.filter (fun e' => f' e' = w) ⊆
        insert e (G.E.filter (fun e' => f e' = w)) := by
      intro e' he'
      simp only [Finset.mem_filter, G', MGraph.applyUpdate, Finset.mem_insert, hf'] at he' ⊢
      rcases he'.1 with rfl | he'G
      · exact Or.inl rfl
      · have hne' : e' ≠ e := fun h => he (h ▸ he'G)
        rw [Function.update_of_ne hne'] at he'
        exact Or.inr ⟨he'G, he'.2⟩
    exact Nat.le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  rcases h1 with ⟨_, hwb⟩ | ⟨_, hwa⟩
  · have h1 := h_eq G.head G'.head b (fun _ => rfl) hwb
    have h2 := h_le G.tail G'.tail a (fun _ => rfl)
    omega
  · have h1 := h_eq G.tail G'.tail a (fun _ => rfl) hwa
    have h2 := h_le G.head G'.head b (fun _ => rfl)
    omega

private lemma deg_split_eq_of_mem_ne {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (hv' : v' ∉ G.V) {w : ℕ} (hw : w ∈ G.V) (hwv : w ≠ v) :
    (G.applyUpdate (.split v v' St Sh)).deg w = G.deg w := by
  have hwv' : w ≠ v' := fun h => hv' (h ▸ hw)
  let G' := G.applyUpdate (.split v v' St Sh)
  change G'.deg w = G.deg w
  simp only [MGraph.deg]
  have hpart : ∀ (S : Finset ℕ) (f f' : ℕ → ℕ),
      (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (G'.E.filter (fun e => f' e = w)).card = (G.E.filter (fun e => f e = w)).card := by
    intro S f f' hf'
    refine congrArg Finset.card (Finset.ext fun e => ?_)
    have hGE : G'.E = G.E := rfl
    simp only [Finset.mem_filter, hGE, hf']
    constructor
    · rintro ⟨he, ht⟩
      split_ifs at ht
      · exact absurd ht.symm hwv'
      · exact ⟨he, ht⟩
    · rintro ⟨he, ht⟩
      refine ⟨he, ?_⟩
      split_ifs with hcond
      · exact absurd (ht.symm.trans hcond.2) hwv
      · exact ht
  rw [hpart St G.tail G'.tail (fun _ => rfl), hpart Sh G.head G'.head (fun _ => rfl)]

private lemma deg_split_add {G : MGraph} (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hv : v ∈ G.V) (hv' : v' ∉ G.V) :
    (G.applyUpdate (.split v v' St Sh)).deg v + (G.applyUpdate (.split v v' St Sh)).deg v' = G.deg v := by
  have hne : v ≠ v' := fun h => hv' (h ▸ hv)
  let G' := G.applyUpdate (.split v v' St Sh)
  have hpart : ∀ (S : Finset ℕ) (f f' : ℕ → ℕ),
      (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (∀ e ∈ G.E, f e ∈ G.V) →
      (G.E.filter (fun e => f' e = v)).card + (G.E.filter (fun e => f' e = v')).card =
        (G.E.filter (fun e => f e = v)).card := by
    intro S f f' hf' hfV
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext e
      simp only [Finset.mem_union, Finset.mem_filter]
      rw [hf' e]
      constructor
      · rintro (⟨he, h⟩ | ⟨he, h⟩)
        · split_ifs at h
          · exact absurd h hne.symm
          · exact ⟨he, h⟩
        · split_ifs at h with hcond
          · exact ⟨he, hcond.2⟩
          · exact absurd (h ▸ hfV e he) hv'
      · rintro ⟨he, h⟩
        by_cases heS : e ∈ S
        · exact Or.inr ⟨he, by simp [heS, h]⟩
        · exact Or.inl ⟨he, by simp [heS, h]⟩
    · rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [Finset.mem_filter] at he1 he2
      exact hne (he1.2.symm.trans he2.2)
  have ht := hpart St G.tail G'.tail (fun _ => rfl) (fun e he => (hG e he).1)
  have hh := hpart Sh G.head G'.head (fun _ => rfl) (fun e he => (hG e he).2)
  change (G'.E.filter (fun e => G'.tail e = v)).card +
      (G'.E.filter (fun e => G'.head e = v)).card +
      ((G'.E.filter (fun e => G'.tail e = v')).card +
        (G'.E.filter (fun e => G'.head e = v')).card) =
      (G.E.filter (fun e => G.tail e = v)).card + (G.E.filter (fun e => G.head e = v)).card
  have hGE : G'.E = G.E := rfl
  rw [hGE]
  omega

private lemma step_potential_bound {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) {N : ℕ} (hN : (G.applyUpdate u).m ≤ N) :
    Real.log 2 * (G.updateEnc u : ℝ) ≤
      degPotential G - degPotential (G.applyUpdate u) +
        (2 * Real.log (2 * (N : ℝ) + 2) + 3) := by
  have hlog2_pos : 0 ≤ Real.log 2 := (show (0 : ℝ) < 1 / 2 by norm_num).trans log_two_gt_half |>.le
  have hlog2_lt : Real.log 2 < 1 := log_two_lt_one
  have hlogN_nonneg : 0 ≤ Real.log (2 * (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ N by positivity])
  cases u with
  | delete e =>
    have hpot : degPotential (G.applyUpdate (.delete e)) ≤ degPotential G := by
      unfold degPotential
      change ∑ v ∈ G.V, phiTerm ((G.applyUpdate (.delete e)).deg v) ≤ ∑ v ∈ G.V, phiTerm (G.deg v)
      refine Finset.sum_le_sum fun v _ => ?_
      exact phiTerm_mono (deg_delete_le G e v)
    have henc : (G.updateEnc (.delete e) : ℝ) = 1 := by simp [MGraph.updateEnc]
    rw [henc, mul_one]
    linarith
  | insert e a b =>
    rcases hu with ⟨he, ha, hb⟩
    let G' := G.applyUpdate (.insert e a b)
    have hG'V : G'.V = G.V := rfl
    have hm_eq : G'.m = G.m + 1 := by
      simp only [G', MGraph.applyUpdate, MGraph.m]
      exact Finset.card_insert_of_notMem he
    have hN' : G'.m ≤ N := hN
    have hm_le : G.m ≤ N := by omega
    have hdeg_a_bound : G.deg a ≤ 2 * N := by
      have h2 := deg_le_two_mul_m G a
      omega
    have hdeg_b_bound : G.deg b ≤ 2 * N := by
      have h2 := deg_le_two_mul_m G b
      omega
    have hdiff : degPotential G' - degPotential G ≤ 2 * Real.log (2 * (N : ℝ) + 2) + 2 := by
      unfold degPotential
      rw [hG'V, ← Finset.sum_sub_distrib]
      by_cases hab : a = b
      · subst hab
        rw [Finset.sum_eq_single a]
        · have hle : G'.deg a ≤ G.deg a + 2 := deg_insert_le_add_two he
          have hmono := phiTerm_mono hle
          have hadd := phiTerm_add_two_sub_le (G.deg a)
          have hlog : Real.log ((G.deg a + 2 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
            refine Real.log_le_log (by exact_mod_cast Nat.succ_pos _) ?_
            exact_mod_cast (by omega : G.deg a + 2 ≤ 2 * N + 2)
          linarith
        · intro w _ hwa
          rw [deg_insert_eq_of_ne he hwa hwa, sub_self]
        · intro hnot; exact absurd ha hnot
      · have ha_le : G'.deg a ≤ G.deg a + 1 :=
          deg_insert_le_add_one_of_ne he (Or.inl ⟨rfl, hab⟩)
        have hb_le : G'.deg b ≤ G.deg b + 1 :=
          deg_insert_le_add_one_of_ne he (Or.inr ⟨rfl, Ne.symm hab⟩)
        have ha_diff : phiTerm (G'.deg a) - phiTerm (G.deg a) ≤ Real.log (2 * (N : ℝ) + 2) + 1 := by
          have hmono := phiTerm_mono ha_le
          have hsucc := phiTerm_succ_sub_le (G.deg a)
          have hlog : Real.log ((G.deg a + 1 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
            refine Real.log_le_log (by exact_mod_cast Nat.succ_pos _) ?_
            exact_mod_cast (by omega : G.deg a + 1 ≤ 2 * N + 2)
          linarith
        have hb_diff : phiTerm (G'.deg b) - phiTerm (G.deg b) ≤ Real.log (2 * (N : ℝ) + 2) + 1 := by
          have hmono := phiTerm_mono hb_le
          have hsucc := phiTerm_succ_sub_le (G.deg b)
          have hlog : Real.log ((G.deg b + 1 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
            refine Real.log_le_log (by exact_mod_cast Nat.succ_pos _) ?_
            exact_mod_cast (by omega : G.deg b + 1 ≤ 2 * N + 2)
          linarith
        have hsum_ab :
            ∑ w ∈ G.V, (phiTerm (G'.deg w) - phiTerm (G.deg w)) =
              (phiTerm (G'.deg a) - phiTerm (G.deg a)) +
                (phiTerm (G'.deg b) - phiTerm (G.deg b)) := by
          have hsub : ∀ w ∈ G.V, w ≠ a → w ≠ b → phiTerm (G'.deg w) - phiTerm (G.deg w) = 0 := by
            intro w _ hwa hwb
            rw [deg_insert_eq_of_ne he hwa hwb, sub_self]
          rw [← Finset.add_sum_erase G.V _ ha, ← Finset.add_sum_erase (G.V.erase a) _
            (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]
          have hzero : ∑ w ∈ (G.V.erase a).erase b, (phiTerm (G'.deg w) - phiTerm (G.deg w)) = 0 := by
            refine Finset.sum_eq_zero fun w hw => ?_
            simp only [Finset.mem_erase] at hw
            exact hsub w hw.2.2 hw.2.1 hw.1
          rw [hzero, add_zero]
        rw [hsum_ab]
        linarith
    have henc : (G.updateEnc (.insert e a b) : ℝ) = 1 := by simp [MGraph.updateEnc]
    rw [henc, mul_one]
    linarith
  | split v v' St Sh =>
    rcases hu with ⟨hv, hv', _, _⟩
    let G' := G.applyUpdate (.split v v' St Sh)
    have hdrop : Real.log 2 * ((min (G'.deg v) (G'.deg v') : ℕ) : ℝ) ≤
        phiTerm (G.deg v) - phiTerm (G'.deg v) - phiTerm (G'.deg v') := by
      have hadd := deg_split_add (St := St) (Sh := Sh) hG hv hv'
      rw [← hadd]
      exact phiTerm_split_drop (G'.deg v) (G'.deg v')
    have hpot_eq : degPotential G - degPotential G' =
        phiTerm (G.deg v) - phiTerm (G'.deg v) - phiTerm (G'.deg v') := by
      unfold degPotential
      have hG'V : G'.V = insert v' G.V := rfl
      rw [hG'V, Finset.sum_insert hv', ← Finset.add_sum_erase G.V _ hv,
        ← Finset.add_sum_erase G.V _ hv]
      have hsame : ∑ w ∈ G.V.erase v, phiTerm (G'.deg w) =
          ∑ w ∈ G.V.erase v, phiTerm (G.deg w) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        simp only [Finset.mem_erase] at hw
        rw [deg_split_eq_of_mem_ne hv' hw.2 hw.1]
      rw [hsame]
      ring
    have henc : (G.updateEnc (.split v v' St Sh) : ℝ) =
        (min (G'.deg v) (G'.deg v') : ℝ) + 1 := by
      simp [MGraph.updateEnc, G']
    rw [Nat.cast_min] at hdrop
    rw [henc, mul_add, mul_one]
    linarith

private lemma degPotential_nonneg (G : MGraph) : 0 ≤ degPotential G :=
  Finset.sum_nonneg fun v _ => phiTerm_nonneg (G.deg v)

private lemma degPotential_le {G : MGraph} (hG : G.IsValid) {N : ℕ} (hN : G.m ≤ N) :
    degPotential G ≤ 2 * (G.m : ℝ) * Real.log (2 * (N : ℝ) + 2) := by
  unfold degPotential phiTerm
  have hlogN : 0 ≤ Real.log (2 * (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ N by positivity])
  calc
    ∑ v ∈ G.V, (G.deg v : ℝ) * Real.log (G.deg v : ℝ)
        ≤ ∑ v ∈ G.V, (G.deg v : ℝ) * Real.log (2 * (N : ℝ) + 2) := by
          refine Finset.sum_le_sum fun v _ => ?_
          cases hd : G.deg v with
          | zero => simp
          | succ d =>
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            refine Real.log_le_log (by exact_mod_cast Nat.succ_pos d) ?_
            have hle := deg_le_two_mul_m G v
            rw [hd] at hle
            exact_mod_cast (by omega : d + 1 ≤ 2 * N + 2)
    _ = ((∑ v ∈ G.V, G.deg v : ℕ) : ℝ) * Real.log (2 * (N : ℝ) + 2) := by
          rw [← Finset.sum_mul, Nat.cast_sum]
    _ = 2 * (G.m : ℝ) * Real.log (2 * (N : ℝ) + 2) := by
          rw [sum_deg_eq_two_mul_m hG]
          push_cast
          ring

private lemma batchEnc_potential_telescope {N : ℕ} :
    ∀ (U : List Update) (G : MGraph),
      G.IsValid → G.BatchIsValid U → G.m + U.length ≤ N →
      Real.log 2 * (G.batchEnc U : ℝ) ≤
        degPotential G - degPotential (G.applyBatch U) +
          (U.length : ℝ) * (2 * Real.log (2 * (N : ℝ) + 2) + 3) := by
  intro U
  induction U with
  | nil =>
    intro G _ _ _
    simp [MGraph.batchEnc, MGraph.applyBatch]
  | cons u U ih =>
    intro G hG hU hmN
    rcases hU with ⟨hu, hU'⟩
    have hG' : (G.applyUpdate u).IsValid := isValid_applyUpdate hG hu
    have hm' : (G.applyUpdate u).m ≤ N := by
      have := m_applyUpdate_le G u
      simp only [List.length_cons] at hmN
      omega
    have hmU' : (G.applyUpdate u).m + U.length ≤ N := by
      have := m_applyUpdate_le G u
      simp only [List.length_cons] at hmN
      omega
    have hstep := step_potential_bound hG hu hm'
    have htail := ih (G.applyUpdate u) hG' hU' hmU'
    have hbatch : G.batchEnc (u :: U) = G.updateEnc u + (G.applyUpdate u).batchEnc U := rfl
    have happly : G.applyBatch (u :: U) = (G.applyUpdate u).applyBatch U := rfl
    rw [hbatch, happly]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- Lemma 2.1 (page 6), single-batch form: for a valid graph `G` with `m = G.m` edges undergoing
a valid update sequence `U` of length `q = U.length`, the total encoding size satisfies
`G.batchEnc U ≤ 20 * (m + q) * log(m + q + 2)`, making the `Õ(m + q)` bound explicit. -/
theorem lemma_2_1_batch {G : MGraph} (hG : G.IsValid) {U : List Update} (hU : G.BatchIsValid U) :
    (G.batchEnc U : ℝ) ≤
      20 * ((G.m : ℝ) + (U.length : ℝ)) * Real.log ((G.m : ℝ) + (U.length : ℝ) + 2) := by
  let N : ℕ := G.m + U.length
  have htel := batchEnc_potential_telescope U G hG hU (le_refl N)
  have hpot0 : degPotential G ≤ 2 * (G.m : ℝ) * Real.log (2 * (N : ℝ) + 2) :=
    degPotential_le hG (Nat.le_add_right _ _)
  have hpot1 : 0 ≤ degPotential (G.applyBatch U) := degPotential_nonneg _
  have hlog2_pos : (1 / 2 : ℝ) < Real.log 2 := log_two_gt_half
  have hlogN2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [show (0 : ℝ) ≤ N by positivity])
  have hlog2N2 : Real.log (2 * (N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2) := by
    have hle : (2 * (N : ℝ) + 2) ≤ 2 * ((N : ℝ) + 2) := by linarith
    calc
      Real.log (2 * (N : ℝ) + 2) ≤ Real.log (2 * ((N : ℝ) + 2)) :=
        Real.log_le_log (by positivity) hle
      _ = Real.log 2 + Real.log ((N : ℝ) + 2) :=
        Real.log_mul (by norm_num) (by positivity)
      _ ≤ Real.log ((N : ℝ) + 2) + Real.log ((N : ℝ) + 2) := add_le_add hlogN2 le_rfl
      _ = 2 * Real.log ((N : ℝ) + 2) := by ring
  have h3_le : (3 : ℝ) ≤ 6 * Real.log ((N : ℝ) + 2) := by linarith
  have hlog_mul :
      Real.log 2 * (G.batchEnc U : ℝ) ≤ 10 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
    have hm_le : (G.m : ℝ) ≤ N := by exact_mod_cast Nat.le_add_right G.m U.length
    have hq_le : (U.length : ℝ) ≤ N := by exact_mod_cast Nat.le_add_left U.length G.m
    have hnonneg : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ N by positivity])
    calc
      Real.log 2 * (G.batchEnc U : ℝ)
          ≤ 2 * (G.m : ℝ) * Real.log (2 * (N : ℝ) + 2) +
              (U.length : ℝ) * (2 * Real.log (2 * (N : ℝ) + 2) + 3) := by linarith
      _ ≤ 2 * (G.m : ℝ) * (2 * Real.log ((N : ℝ) + 2)) +
              (U.length : ℝ) * (2 * (2 * Real.log ((N : ℝ) + 2)) + 6 * Real.log ((N : ℝ) + 2)) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left hlog2N2 (by positivity)
            · exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ = (4 * (G.m : ℝ) + 10 * (U.length : ℝ)) * Real.log ((N : ℝ) + 2) := by ring
      _ ≤ 10 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
            have hcoeff : 4 * (G.m : ℝ) + 10 * (U.length : ℝ) ≤ 10 * (N : ℝ) := by
              have : (N : ℝ) = (G.m : ℝ) + (U.length : ℝ) := by simp [N]
              linarith [show (0 : ℝ) ≤ G.m by positivity]
            exact mul_le_mul_of_nonneg_right hcoeff hnonneg
  have hhalf : (1 / 2 : ℝ) * (G.batchEnc U : ℝ) ≤ Real.log 2 * (G.batchEnc U : ℝ) :=
    mul_le_mul_of_nonneg_right hlog2_pos.le (Nat.cast_nonneg _)
  have hNcast : (N : ℝ) = (G.m : ℝ) + (U.length : ℝ) := by simp [N]
  rw [← hNcast]
  linarith

private lemma applyBatch_append (G : MGraph) (U₁ U₂ : List Update) :
    G.applyBatch (U₁ ++ U₂) = (G.applyBatch U₁).applyBatch U₂ :=
  List.foldl_append

private lemma batchIsValid_append (G : MGraph) (U₁ U₂ : List Update) :
    G.BatchIsValid (U₁ ++ U₂) ↔ G.BatchIsValid U₁ ∧ (G.applyBatch U₁).BatchIsValid U₂ := by
  induction U₁ generalizing G with
  | nil => simp [MGraph.BatchIsValid, MGraph.applyBatch]
  | cons u U₁ ih =>
    simp only [List.cons_append, MGraph.BatchIsValid]
    have hfold : (G.applyUpdate u).applyBatch U₁ = G.applyBatch (u :: U₁) := rfl
    rw [ih (G.applyUpdate u), hfold, and_assoc]

private lemma batchEnc_append (G : MGraph) (U₁ U₂ : List Update) :
    G.batchEnc (U₁ ++ U₂) = G.batchEnc U₁ + (G.applyBatch U₁).batchEnc U₂ := by
  induction U₁ generalizing G with
  | nil => simp [MGraph.batchEnc, MGraph.applyBatch]
  | cons u U₁ ih =>
    simp only [List.cons_append, MGraph.batchEnc]
    have hfold : (G.applyUpdate u).applyBatch U₁ = G.applyBatch (u :: U₁) := rfl
    rw [ih (G.applyUpdate u), hfold]
    omega

private def flatBatches (U : ℕ → List Update) : ℕ → List Update
  | 0 => []
  | t + 1 => flatBatches U t ++ U (t + 1)

/-- Lemma 2.1 (page 6): for a dynamic graph starting at valid `G 0` with `m = (G 0).m` edges and
undergoing `τ` valid update batches `U 1, …, U τ` with total update count
`q = ∑ t ∈ Finset.Icc 1 τ, (U t).length`, the total encoding size satisfies
`∑ t ∈ Finset.Icc 1 τ, (G (t - 1)).batchEnc (U t) ≤ 20 * (m + q) * log(m + q + 2)`,
making the `Õ(m + ∑_t |U^{(t)}|)` bound explicit. -/
theorem lemma_2_1 {G : ℕ → MGraph} {U : ℕ → List Update} {τ : ℕ}
    (hG0 : (G 0).IsValid)
    (hvalid : ∀ t, 1 ≤ t → t ≤ τ →
      (G (t - 1)).BatchIsValid (U t) ∧ G t = (G (t - 1)).applyBatch (U t)) :
    ((∑ t ∈ Finset.Icc 1 τ, (G (t - 1)).batchEnc (U t) : ℕ) : ℝ) ≤
      20 * (((G 0).m : ℝ) + ((∑ t ∈ Finset.Icc 1 τ, (U t).length : ℕ) : ℝ)) *
        Real.log (((G 0).m : ℝ) + ((∑ t ∈ Finset.Icc 1 τ, (U t).length : ℕ) : ℝ) + 2) := by
  have hflat : ∀ n ≤ τ,
      (G 0).BatchIsValid (flatBatches U n) ∧
      G n = (G 0).applyBatch (flatBatches U n) ∧
      (G 0).batchEnc (flatBatches U n) = ∑ t ∈ Finset.Icc 1 n, (G (t - 1)).batchEnc (U t) ∧
      (flatBatches U n).length = ∑ t ∈ Finset.Icc 1 n, (U t).length := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [flatBatches, MGraph.BatchIsValid, MGraph.applyBatch, MGraph.batchEnc]
    | succ k ih =>
      intro hk
      obtain ⟨hv_k, hg_k, henc_k, hlen_k⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨hv_step, hg_step⟩ := hvalid (k + 1) (by omega) hk
      have hv_k' : (G 0).BatchIsValid (flatBatches U (k + 1)) := by
        dsimp only [flatBatches]
        rw [batchIsValid_append]
        exact ⟨hv_k, hg_k ▸ hv_step⟩
      have hg_k' : G (k + 1) = (G 0).applyBatch (flatBatches U (k + 1)) := by
        dsimp only [flatBatches]
        rw [applyBatch_append, ← hg_k]
        exact hg_step
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      have henc_k' : (G 0).batchEnc (flatBatches U (k + 1)) =
          ∑ t ∈ Finset.Icc 1 (k + 1), (G (t - 1)).batchEnc (U t) := by
        dsimp only [flatBatches]
        rw [batchEnc_append, henc_k, ← hg_k, hIcc, Finset.sum_insert hnot]
        simp [add_comm]
      have hlen_k' : (flatBatches U (k + 1)).length =
          ∑ t ∈ Finset.Icc 1 (k + 1), (U t).length := by
        dsimp only [flatBatches]
        rw [List.length_append, hlen_k, hIcc, Finset.sum_insert hnot]
        omega
      exact ⟨hv_k', hg_k', henc_k', hlen_k'⟩
  obtain ⟨hv, _, henc, hlen⟩ := hflat τ (le_refl τ)
  have h := lemma_2_1_batch hG0 hv
  rwa [henc, hlen] at h

end MinCostFlow.Chain
