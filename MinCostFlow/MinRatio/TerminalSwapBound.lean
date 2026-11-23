module

public import MinCostFlow.Basic.Forest
import MinCostFlow.MinRatio.PathSwapBudget
import MinCostFlow.MinRatio.TerminalCutUsage
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.LSF.Walks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Bounding path swaps in a forest

Algorithm 2 (page 29) needs to route the signed flow while charging
its exact absolute changes. For a list of paths in one component,
improving destination swaps use only the existing terminals. The
sample of rooted cuts bounds their number independently of all
expanded path lengths.
-/

public section

namespace MinCostFlow.MinRatio

/-- A swap history within one component uses at most half the initial
path count times the square of the terminal count in swaps. -/
theorem terminalSwapBound {F : MGraph} (hF : F.IsForest) {r : ℕ}
    (terminals : Finset ℕ) (hc : ∀ v ∈ terminals, F.Connected r v)
    (route : ℕ → List (ℕ × ℕ)) (steps : ℕ)
    (hterm : ∀ p ∈ route 0, p.1 ∈ terminals ∧ p.2 ∈ terminals)
    (hstep : ∀ t < steps, ∃ a b c d : ℕ, ∃ x : ℕ × Bool, ∃ rest : List (ℕ × ℕ),
      a ∈ terminals ∧ b ∈ terminals ∧ c ∈ terminals ∧ d ∈ terminals ∧
      x ∈ F.forestPath a b ∧ (x.1, !x.2) ∈ F.forestPath c d ∧
      (route t).Perm ((a,b) :: (c,d) :: rest) ∧
      (route (t + 1)).Perm ((a,d) :: (c,b) :: rest)) :
    2 * steps ≤ (terminals.card * terminals.card) * (route 0).length := by
  classical
  obtain ⟨sample, _, hsample, hrep⟩ := terminalCut_representatives hF terminals hc
  have hconn (p : ℕ × ℕ) (hp : p ∈ route 0) : F.Connected p.1 p.2 := by
    obtain ⟨ha, hb⟩ := hterm p hp
    exact MGraph.connected_trans (MGraph.connected_symm (hc _ ha)) (hc _ hb)
  refine (pathSwapPotential_history_bound F hF sample route steps hconn ?_).trans
    (Nat.mul_le_mul_right _ hsample)
  intro t ht
  obtain ⟨a,b,c,d,x,rest,ha,hb,hc',hd,hx,hy,h₀,h₁⟩ := hstep t ht
  have hab := MGraph.connected_trans (MGraph.connected_symm (hc a ha)) (hc b hb)
  have hcd := MGraph.connected_trans (MGraph.connected_symm (hc c hc')) (hc d hd)
  have hpath := LSF.forestPath_isPath hF hab
  have he := MGraph.isWalk_edges_mem hpath.1 x hx
  have hused : ∃ u ∈ terminals, x.1 ∈ walkEdges (F.forestPath r u) := by
    by_contra hn
    have hna : x.1 ∉ walkEdges (F.forestPath r a) := fun h => hn ⟨a, ha, h⟩
    have hnb : x.1 ∉ walkEdges (F.forestPath r b) := fun h => hn ⟨b, hb, h⟩
    have hzero := terminalCut_usage hF (hc a ha) (hc b hb) x.1
    have hcross : x.1 ∈ walkEdges (F.forestPath a b) :=
      List.mem_toFinset.mpr (List.mem_map_of_mem hx)
    rw [LSF.walkFlow_abs_of_nodup (LSF.isPath_nodup_edges hpath)] at hzero
    norm_num [hcross, hna, hnb] at hzero
  obtain ⟨f, hmem, hr⟩ := hrep x.1 he hused
  refine pathSwapPotential_drop_of_representative hF sample hab hcd hx hy hmem ?_ rest _ _ h₀ h₁
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hr _ ha _ hb
  · exact hr _ hc' _ hd
  · exact hr _ ha _ hd
  · exact hr _ hc' _ hb

/-- A forest-wide sample can be formed by taking the union of the
samples rooted at each terminal. Its cardinality is at most cubic
in the terminal count, and it represents path usage within every
terminal component. -/
theorem forestTerminal_representatives {F : MGraph} (hF : F.IsForest) (terminals : Finset ℕ) :
    ∃ sample : Finset ℕ, sample.card ≤ terminals.card ^ 3 ∧
      ∀ r ∈ terminals, ∀ e ∈ F.E,
        (∃ t ∈ terminals, F.Connected r t ∧ e ∈ walkEdges (F.forestPath r t)) →
        ∃ f ∈ sample, ∀ u ∈ terminals, ∀ v ∈ terminals,
          F.Connected r u → F.Connected r v →
          |walkFlow (F.forestPath u v) f| = |walkFlow (F.forestPath u v) e| := by
  classical
  let comp (r : ℕ) := terminals.filter (F.Connected r)
  have hex (r : ℕ) := terminalCut_representatives hF (comp r) (fun t ht => (Finset.mem_filter.mp ht).2)
  let sampleAt := fun r => (hex r).choose
  let sample := terminals.biUnion sampleAt
  have hcap (r : ℕ) : (sampleAt r).card ≤ terminals.card * terminals.card :=
    (hex r).choose_spec.2.1.trans
      (Nat.mul_le_mul (Finset.card_filter_le _ _) (Finset.card_filter_le _ _))
  refine ⟨sample, ?_, ?_⟩
  · calc
      sample.card ≤ ∑ r ∈ terminals, (sampleAt r).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ terminals, terminals.card * terminals.card := Finset.sum_le_sum fun r _ => hcap r
      _ = terminals.card ^ 3 := by simp [pow_succ, mul_assoc]
  · intro r hr e he hused
    obtain ⟨t, ht, hrt, hepath⟩ := hused
    obtain ⟨f, hf, hrep⟩ := (hex r).choose_spec.2.2 e he
      ⟨t, Finset.mem_filter.mpr ⟨ht, hrt⟩, hepath⟩
    refine ⟨f, Finset.mem_biUnion.mpr ⟨r, hr, hf⟩, ?_⟩
    intro u hu v hv hru hrv
    exact hrep u (Finset.mem_filter.mpr ⟨hu, hru⟩) v (Finset.mem_filter.mpr ⟨hv, hrv⟩)

/-- Across an arbitrary forest, improving swaps have a bound in the
terminal count and the initial number of paths. The same-component
guard is the one used when obtaining the four weighted lengths. -/
theorem terminalSwapBound_forest {F : MGraph} (hF : F.IsForest)
    (terminals : Finset ℕ) (route : ℕ → List (ℕ × ℕ)) (steps : ℕ)
    (hconn : ∀ p ∈ route 0, F.Connected p.1 p.2)
    (hstep : ∀ t < steps, ∃ a b c d : ℕ, ∃ x : ℕ × Bool, ∃ rest : List (ℕ × ℕ),
      a ∈ terminals ∧ b ∈ terminals ∧ c ∈ terminals ∧ d ∈ terminals ∧
      F.Connected a b ∧ F.Connected a c ∧ F.Connected c d ∧
      x ∈ F.forestPath a b ∧ (x.1, !x.2) ∈ F.forestPath c d ∧
      (route t).Perm ((a,b) :: (c,d) :: rest) ∧
      (route (t + 1)).Perm ((a,d) :: (c,b) :: rest)) :
    2 * steps ≤ terminals.card ^ 3 * (route 0).length := by
  classical
  obtain ⟨sample, hcap, hrep⟩ := forestTerminal_representatives hF terminals
  refine (pathSwapPotential_history_bound F hF sample route steps hconn ?_).trans
    (Nat.mul_le_mul_right _ hcap)
  intro t ht
  obtain ⟨a,b,c,d,x,rest,ha,hb,hc,hd,hab,hac,hcd,hx,hy,h₀,h₁⟩ := hstep t ht
  have had := MGraph.connected_trans hac hcd
  have he := MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath hab) x hx
  have hcross : x.1 ∈ walkEdges (F.forestPath a b) :=
    List.mem_toFinset.mpr (List.mem_map_of_mem hx)
  obtain ⟨f, hmem, hr⟩ := hrep a ha x.1 he ⟨b, hb, hab, hcross⟩
  refine pathSwapPotential_drop_of_representative hF sample hab hcd hx hy hmem ?_ rest _ _ h₀ h₁
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hr _ ha _ hb ⟨[], .nil _⟩ hab
  · exact hr _ hc _ hd hac had
  · exact hr _ ha _ hd ⟨[], .nil _⟩ had
  · exact hr _ hc _ hb hac hab

/-- The initial route supplies all terminals for the entire history.
With `K` initial paths, the swap count is at most `4 * K^4`. -/
theorem terminalSwapBound_pathCount {F : MGraph} (hF : F.IsForest)
    (route : ℕ → List (ℕ × ℕ)) (steps : ℕ)
    (hconn : ∀ p ∈ route 0, F.Connected p.1 p.2)
    (hstep : ∀ t < steps, ∃ a b c d : ℕ, ∃ x : ℕ × Bool, ∃ rest : List (ℕ × ℕ),
      F.Connected a b ∧ F.Connected a c ∧ F.Connected c d ∧
      x ∈ F.forestPath a b ∧ (x.1, !x.2) ∈ F.forestPath c d ∧
      (route t).Perm ((a,b) :: (c,d) :: rest) ∧
      (route (t + 1)).Perm ((a,d) :: (c,b) :: rest)) :
    steps ≤ 4 * (route 0).length ^ 4 := by
  let terminals := ((route 0).map Prod.fst).toFinset ∪ ((route 0).map Prod.snd).toFinset
  have hcap : terminals.card ≤ 2 * (route 0).length := by
    have h₁ := ((route 0).map Prod.fst).toFinset_card_le
    have h₂ := ((route 0).map Prod.snd).toFinset_card_le
    rw [List.length_map] at h₁ h₂
    have hu := Finset.card_union_le (s := ((route 0).map Prod.fst).toFinset)
      (t := ((route 0).map Prod.snd).toFinset)
    change terminals.card ≤ _ at hu
    omega
  have hterm : ∀ t ≤ steps, ∀ p ∈ route t, p.1 ∈ terminals ∧ p.2 ∈ terminals := by
    intro t
    induction t with
    | zero =>
      intro _ p hp
      exact ⟨Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hp)),
        Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem hp))⟩
    | succ t ih =>
      intro ht p hp
      obtain ⟨a,b,c,d,x,rest,_,_,_,_,_,h₀,h₁⟩ := hstep t (by omega)
      have hprev := ih (by omega)
      have hAB := hprev (a,b) (h₀.mem_iff.mpr (by simp))
      have hCD := hprev (c,d) (h₀.mem_iff.mpr (by simp))
      have hp' := h₁.mem_iff.mp hp
      simp only [List.mem_cons] at hp'
      rcases hp' with rfl | rfl | hp'
      · exact ⟨hAB.1, hCD.2⟩
      · exact ⟨hCD.1, hAB.2⟩
      · exact hprev p (h₀.mem_iff.mpr (by simp [hp']))
  have hb := terminalSwapBound_forest hF terminals route steps hconn (fun t ht => by
    obtain ⟨a,b,c,d,x,rest,hab,hac,hcd,hx,hy,h₀,h₁⟩ := hstep t ht
    have hAB := hterm t (by omega) (a,b) (h₀.mem_iff.mpr (by simp))
    have hCD := hterm t (by omega) (c,d) (h₀.mem_iff.mpr (by simp))
    exact ⟨a,b,c,d,x,rest,hAB.1,hAB.2,hCD.1,hCD.2,hab,hac,hcd,hx,hy,h₀,h₁⟩)
  have hu := hb.trans (Nat.mul_le_mul_right (route 0).length (Nat.pow_le_pow_left hcap 3))
  have he : (2 * (route 0).length) ^ 3 * (route 0).length = 8 * (route 0).length ^ 4 := by ring
  omega

end MinCostFlow.MinRatio
