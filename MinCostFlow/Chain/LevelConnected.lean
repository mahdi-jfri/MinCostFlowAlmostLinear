module

public import MinCostFlow.Chain.Algorithm1Proofs
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algorithm 1 Level Connectedness and Last-Level Size Bound

Establishes connectedness propagation across Algorithm 1's dynamic tree chain (`ChainInv`),
yielding `((st.G i).n : ℝ) ≤ (st.G i).m + 1` at every level `0 ≤ i ≤ P.d`, the small
last-level vertex bound `(st.G P.d).n ≤ levelM TP P P.d + 1`, and `ChainInv.toTreeChain_holds_own`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF

section Connectedness

private lemma walk_exit_finset {G : MGraph} {S : Finset ℕ} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ G.E, (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.head e ∈ S ∧ G.tail e ∉ S) := by
  induction hW with
  | nil z => exact absurd hu hv
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    by_cases hdst : G.dst x₀ ∈ S
    · exact ih hdst hv
    · rcases x₀ with ⟨e, _ | _⟩
      · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
        simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hdst
        exact ⟨e, hxE, Or.inr ⟨hsrc ▸ hu, hdst⟩⟩
      · simp only [MGraph.src, ↓reduceIte] at hsrc
        simp only [MGraph.dst, ↓reduceIte] at hdst
        exact ⟨e, hxE, Or.inl ⟨hsrc ▸ hu, hdst⟩⟩

private lemma connected_prefix_step {G : MGraph} (hG : G.IsValid)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    {r : ℕ} (hr : r ∈ G.V) :
    ∀ k : ℕ, k + 1 ≤ G.V.card →
      ∃ (S F : Finset ℕ), S ⊆ G.V ∧ F ⊆ G.E ∧ r ∈ S ∧ S.card = k + 1 ∧ F.card = k ∧
        ∀ e ∈ F, G.tail e ∈ S ∧ G.head e ∈ S := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨{r}, ∅, Finset.singleton_subset_iff.mpr hr, Finset.empty_subset _,
      Finset.mem_singleton_self r, Finset.card_singleton r, Finset.card_empty, fun e he => by
        cases Finset.notMem_empty e he⟩
  | succ k ih =>
    intro hk1
    obtain ⟨S, F, hSV, hFE, hrS, hScard, hFcard, hFends⟩ := ih (Nat.le_of_succ_le hk1)
    have hlt : S.card < G.V.card := by omega
    obtain ⟨w, hwV, hwS⟩ : ∃ w ∈ G.V, w ∉ S := by
      by_contra hnone
      push Not at hnone
      exact (Nat.not_lt_of_le (Finset.card_le_card (fun v hv => hnone v hv))) hlt
    obtain ⟨P, hP⟩ := hConn r hr w hwV
    obtain ⟨e, heE, hsplit⟩ := walk_exit_finset hP hrS hwS
    have heEnds := hG e heE
    have he_not_F : e ∉ F := by
      intro heF
      have ⟨htS, hhS⟩ := hFends e heF
      rcases hsplit with ⟨_, hnh⟩ | ⟨_, hnt⟩
      · exact hnh hhS
      · exact hnt htS
    rcases hsplit with ⟨htS, hnh⟩ | ⟨hhS, hnt⟩
    · refine ⟨insert (G.head e) S, insert e F,
        Finset.insert_subset heEnds.2 hSV, Finset.insert_subset heE hFE,
        Finset.mem_insert_of_mem hrS, ?_, ?_, fun f hf => ?_⟩
      · rw [Finset.card_insert_of_notMem hnh, hScard]
      · rw [Finset.card_insert_of_notMem he_not_F, hFcard]
      · rcases Finset.mem_insert.mp hf with rfl | hfF
        · exact ⟨Finset.mem_insert_of_mem htS, Finset.mem_insert_self _ _⟩
        · exact ⟨Finset.mem_insert_of_mem (hFends f hfF).1,
            Finset.mem_insert_of_mem (hFends f hfF).2⟩
    · refine ⟨insert (G.tail e) S, insert e F,
        Finset.insert_subset heEnds.1 hSV, Finset.insert_subset heE hFE,
        Finset.mem_insert_of_mem hrS, ?_, ?_, fun f hf => ?_⟩
      · rw [Finset.card_insert_of_notMem hnt, hScard]
      · rw [Finset.card_insert_of_notMem he_not_F, hFcard]
      · rcases Finset.mem_insert.mp hf with rfl | hfF
        · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hhS⟩
        · exact ⟨Finset.mem_insert_of_mem (hFends f hfF).1,
            Finset.mem_insert_of_mem (hFends f hfF).2⟩

/-- Every valid connected multigraph satisfies `G.n ≤ G.m + 1`. -/
lemma connected_n_le_m_add_one {G : MGraph} (hG : G.IsValid)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    G.n ≤ G.m + 1 := by
  by_cases hV : G.V.Nonempty
  · obtain ⟨r, hr⟩ := hV
    have hpos : 0 < G.V.card := Finset.card_pos.mpr ⟨r, hr⟩
    obtain ⟨S, F, _, hFE, _, _, hFcard, _⟩ :=
      connected_prefix_step hG hConn hr (G.V.card - 1) (by omega)
    have hScard' : G.V.card ≤ F.card + 1 := by
      have : G.V.card = G.V.card - 1 + 1 := by omega
      omega
    have hFm : F.card ≤ G.m := Finset.card_le_card hFE
    change G.V.card ≤ G.m + 1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hV
    change G.V.card ≤ G.m + 1
    rw [hV, Finset.card_empty]
    omega

private lemma isWalk_coreGraph_contract {G : MGraph} {L : LSF}
    (hRF : L.F.IsRootedSpanningForestOf G) {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) :
    (coreGraph G L).IsWalk (L.F.root u) (L.F.root v) (P.filter fun x => x.1 ∉ L.F.F.E) := by
  induction hW with
  | nil z =>
    simpa [List.filter_nil] using (MGraph.IsWalk.nil (G := coreGraph G L) (L.F.root z))
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    by_cases hxF : x₀.1 ∈ L.F.F.E
    · rw [List.filter_cons_of_neg (by simp [hxF])]
      have hroot_tail := root_eq_of_edge_mem_F hRF hRF.2.2.2.2 hxF
      have hroot_step : L.F.root u₀ = L.F.root (G.dst x₀) := by
        rw [← hsrc]
        rcases x₀ with ⟨e, _ | _⟩
        · exact hroot_tail.symm
        · exact hroot_tail
      rw [hroot_step]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [hxF])]
      have hxC : x₀.1 ∈ (coreGraph G L).E := Finset.mem_sdiff.mpr ⟨hxE, hxF⟩
      have hsrcC : (coreGraph G L).src x₀ = L.F.root u₀ := by
        rw [← hsrc]
        rcases x₀ with ⟨e, _ | _⟩ <;> rfl
      have hdstC : (coreGraph G L).dst x₀ = L.F.root (G.dst x₀) := by
        rcases x₀ with ⟨e, _ | _⟩ <;> rfl
      exact .cons hxC hsrcC (hdstC ▸ ih)

/-- Contracting a valid connected graph `G` along a rooted spanning forest `L.F` yields a
connected core graph `coreGraph G L`. -/
lemma coreGraph_connected {G : MGraph} {L : LSF}
    (hRF : L.F.IsRootedSpanningForestOf G)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    ∀ u ∈ (coreGraph G L).V, ∀ v ∈ (coreGraph G L).V, (coreGraph G L).Connected u v := by
  intro u hu v hv
  have huR : u ∈ L.F.R := hu
  have hvR : v ∈ L.F.R := hv
  have huV : u ∈ G.V := hRF.2.2.1 huR
  have hvV : v ∈ G.V := hRF.2.2.1 hvR
  obtain ⟨P, hP⟩ := hConn u huV v hvV
  have hc := isWalk_coreGraph_contract (G := G) (L := L) hRF hP
  rw [root_eq_of_mem_R hRF huR, root_eq_of_mem_R hRF hvR] at hc
  exact ⟨_, hc⟩

private lemma isWalk_expand_embedding {C S : MGraph} {emb : Embedding}
    (hEmb : emb.IsEmbedding C S) {u v : ℕ} {P : List (ℕ × Bool)} (hW : C.IsWalk u v P) :
    S.Connected u v := by
  induction hW with
  | nil z => exact MGraph.connected_refl S z
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    have hxWalk : S.IsWalk (C.tail x₀.1) (C.head x₀.1) (emb x₀.1) := hEmb.2 x₀.1 hxE
    have hstep : S.Connected u₀ (C.dst x₀) := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩
      · exact ⟨walkRev (emb e), MGraph.isWalk_walkRev hxWalk⟩
      · exact ⟨emb e, hxWalk⟩
    exact MGraph.connected_trans hstep ih

/-- Any sparsified core graph `(S, emb)` of a connected graph `G` is connected on `S.V`. -/
lemma isSparsifiedCoreGraph_connected {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c σ : ℝ}
    {m_cap : ℕ} {S : MGraph} {emb : Embedding} (hHolds : L.Holds G ℓ σ)
    (hSp : IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ γ_c m_cap S emb)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    ∀ u ∈ S.V, ∀ v ∈ S.V, S.Connected u v := by
  intro u hu v hv
  have huC : u ∈ (coreGraph G L).V := hSp.1.1 hu
  have hvC : v ∈ (coreGraph G L).V := hSp.1.1 hv
  obtain ⟨P, hP⟩ := coreGraph_connected hHolds.2.1 hConn u huC v hvC
  exact isWalk_expand_embedding hSp.2.1 hP

/-- Under `ChainInv`, if `st.G 0` is connected, then every level graph `st.G i` (`0 ≤ i ≤ P.d`)
is connected and satisfies `(st.G i).n ≤ (st.G i).m + 1`. -/
theorem chainInv_connected {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    ∀ i ≤ P.d,
      (∀ u ∈ (st.G i).V, ∀ v ∈ (st.G i).V, (st.G i).Connected u v) ∧
      (st.G i).n ≤ (st.G i).m + 1 := by
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  intro i hi
  induction i with
  | zero => exact ⟨hConn0, connected_n_le_m_add_one (hLvl 0 (Nat.zero_le _)).1 hConn0⟩
  | succ i ih =>
    have hi_lt : i < P.d := hi
    obtain ⟨hConni, _⟩ := ih (Nat.le_of_lt hi_lt)
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    have hConnsucc : ∀ u ∈ (st.G (i + 1)).V, ∀ v ∈ (st.G (i + 1)).V, (st.G (i + 1)).Connected u v := by
      rw [hInv.hGSucc i hi_lt]
      exact isSparsifiedCoreGraph_connected hBi.1 hBi.2 hConni
    exact ⟨hConnsucc, connected_n_le_m_add_one (hLvl (i + 1) hi).1 hConnsucc⟩

/-- Under `ChainInv` and connectedness of `st.G 0`, every level `i ≤ P.d` satisfies the
component bound `((st.G i).n : ℝ) ≤ 1 * (((st.G i).m : ℝ) + 1)` (`c_n = 1`), and at level `P.d`
the vertex count satisfies `(st.G P.d).n ≤ levelM TP P P.d + 1`. -/
theorem chainInv_comp_bound_all_levels {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    (∀ i ≤ P.d, ((st.G i).n : ℝ) ≤ (1 : ℝ) * (((st.G i).m : ℝ) + 1)) ∧
    (st.G P.d).n ≤ levelM TP P P.d + 1 := by
  have hConnAll := chainInv_connected hTP hT hγM₀ hγk hInv hConn0
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  refine ⟨fun i hi => ?_, ?_⟩
  · have hnat : (st.G i).n ≤ (st.G i).m + 1 := (hConnAll i hi).2
    have hreal : ((st.G i).n : ℝ) ≤ ((st.G i).m : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  · have hPd_nat : (st.G P.d).n ≤ (st.G P.d).m + 1 := (hConnAll P.d le_rfl).2
    have hm_le_lvl : ((st.G P.d).m : ℝ) ≤ (levelM TP P P.d : ℝ) :=
      (hLvl P.d le_rfl).2.2.1
    have hm_nat : (st.G P.d).m ≤ levelM TP P P.d := by exact_mod_cast hm_le_lvl
    omega

/-- Connectedness-based counterpart of `ChainInv.toTreeChain_holds_noHidden`: under connectedness
of `st.G 0`, the last-level stretch in `TreeChain.Holds` is bounded at its own level-`d` vertex
cap `LP.σ_last (levelM TP P P.d + 1)` instead of `LP.σ_last (st.G 0).n`. -/
theorem ChainInv.toTreeChain_holds_own {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hMWU : T.ToolMWURestartNoHidden σ_mwu)
    (hEmb : T.ToolEmbedsSurvivingRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (levelM TP P P.d + 1))
    let σ_mwu_tot := max (σ_mwu (st.G 0).n) (LP.σ_mwu (st.G 0).n)
    st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    st.toTreeChain.LastLevelSpans ∧
    st.toTreeChain.EmbedsSurviving := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  have hPd_le : (st.G P.d).n ≤ levelM TP P P.d + 1 :=
    (chainInv_comp_bound_all_levels hTP hT hγM₀ hγk hInv hConn0).2
  have hOld := hInv.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP hT hMWU hEmb hγM₀ hγk
  refine ⟨?_, hOld.2.1, hOld.2.2⟩
  refine ⟨hOld.1.1, hOld.1.2.1, hOld.1.2.2.1, hOld.1.2.2.2.1, ?_, hOld.1.2.2.2.2.2.1, ?_,
    hOld.1.2.2.2.2.2.2.2⟩
  · intro i hi
    refine ⟨hInv.hBran i hi, ?_, ?_, ?_⟩
    · intro j hj
      have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
      exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
    · exact (hOld.1.2.2.2.2.1 i hi).2.2.1
    · exact (hOld.1.2.2.2.2.1 i hi).2.2.2
  · intro j hj
    exact LSF.Holds.mono_σ (hInv.hLastHolds j hj)
      (le_trans (hLP.2.1 _ _ hPd_le) (le_max_right _ _))

end Connectedness

end MinCostFlow.Chain
