module

public import MinCostFlow.ExpanderDecomp.OuterCorePlayer
public import MinCostFlow.ExpanderDecomp.OuterMatching
public import MinCostFlow.ExpanderDecomp.MatchingPlayer
public import MinCostFlow.ExpanderDecomp.PortRounding
public import MinCostFlow.ExpanderDecomp.FakeEdges
public import MinCostFlow.ExpanderDecomp.Params
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.OuterBudgets
import MinCostFlow.ExpanderDecomp.Injection
import MinCostFlow.ExpanderDecomp.Rounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-node outer cut-matching game

This file formalizes the cut-matching game at one node of the outer algorithm, on
the port graph `portGraph cloud G X`, calling the static matching player through `IsMatchingPlayer`
(`MatchingPlayer.lean`) and the recursive core through `IsCorePlayer` (`OuterCorePlayer.lean`):

* `OuterGameResult`, `outerGameLoop`, `outerGame`: runs the cut-matching game for up to
  `49 * L + 1` rounds, returning either a sparse port cut `U` or a spanning port witness `(W, F)`.
* `outerGame_spec`: proves via the round bound `round_bound_nat`, the injection lemma
  (`isExpansionExpanderOn_of_injection`), `GameEmbInv`, and `padToBisection_spec` that the loop
  never exhausts fuel and yields either:
  - a sparse port cut `U` with `b_out · |∂ U| ≤ min(|U|, |Ū|)` and both sides at least `(z+1)/2`;
  - or a spanning port witness of expansion `1 / (2 P_r)` embedded into `Hhat + F` with congestion
    at most `t · R_out`, at most `t · z` fake edges, and fake port degree at most `t`.
* `outerWitness_removeFake`: applies `isConductanceExpanderOn_contractedGraph_of_embedding`
  and `removeFake_spec` to obtain `R ⊆ X` with `G.IsConductanceExpanderOn R (1 / Q)`,
  `R.Nonempty`, and `16 · b_out · vol_{G[X]}(X \ R) ≤ e`.
* `outerGameCost`, `outerGame_cost_le`: exact per-node operation count of the game and its bound.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Outcome of the outer cut-matching game on a port graph `Hhat`. -/
inductive OuterGameResult where
  /-- Router returned a sparse port cut `U`. -/
  | cut (U : Finset ℕ)
  /-- Core returned a half-size expander and the final injection succeeded, yielding spanning
  witness edges `W_edges` and fake port edges `F_edges`. -/
  | witness (W_edges F_edges : List (ℕ × ℕ))

/-- Bounded-fuel cut-matching game loop on `Hhat` (`2 * e` ports) with deficit budget `z`,
calling `route` at `Δ = 10`, `L = LParam M`, `b = bOut cfg M`. -/
def outerGameLoop (cfg : ParamConfig) (M r e z : ℕ)
    (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (Hhat : Graph) : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → OuterGameResult
  | 0, _, _ => .cut ∅
  | fuel + 1, W_edges, F_edges =>
    let W := Graph.mk (2 * e) W_edges
    match core (coreLevel M r (2 * e)) W with
    | .expander S =>
      let A := Finset.range (2 * e) \ S
      match route Hhat Hhat.verts [(A, S)] 10 (LParam M) (bOut cfg M) z with
      | .cut U => .cut U
      | .matched matchings _ =>
        let M_inj := matchings.getD 0 []
        let F_inj := fakeCompletion A S M_inj
        .witness (W_edges ++ (M_inj ++ F_inj)) (F_edges ++ F_inj)
    | .cut U =>
      let (A, B) := padToBisection e U
      match route Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z with
      | .cut U_cut => .cut U_cut
      | .matched matchings _ =>
        let M_k := matchings.getD 0 []
        let F_k := fakeCompletion A B M_k
        outerGameLoop cfg M r e z core route Hhat fuel
          (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k)

/-- Run the outer cut-matching game on `Hhat = portGraph cloud G X` for up to `49 * L + 1` rounds
at one node of the outer recursion. -/
def outerGame (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (X : Finset ℕ) : OuterGameResult :=
  let e := (G.inside X).length
  let z := e / DOut cfg M r
  let Hhat := portGraph cloud G X
  outerGameLoop cfg M r e z core route Hhat (49 * LParam M + 1) [] []

/-- Operation count of `outerGameLoop` (counting `coreCost`, `routeCost`, and `4 * e` per round
for bisection padding and matching completion). -/
def outerGameLoopCost (cfg : ParamConfig) (M r e z : ℕ)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (Hhat : Graph) : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ
  | 0, _, _ => 0
  | fuel + 1, W_edges, F_edges =>
    let W := Graph.mk (2 * e) W_edges
    let cCore := coreCost (coreLevel M r (2 * e)) W
    match core (coreLevel M r (2 * e)) W with
    | .expander S =>
      let A := Finset.range (2 * e) \ S
      let cRoute := routeCost Hhat Hhat.verts [(A, S)] 10 (LParam M) (bOut cfg M) z
      cCore + cRoute + 4 * e
    | .cut U =>
      let (A, B) := padToBisection e U
      let cRoute := routeCost Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z
      match route Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z with
      | .cut _ => cCore + cRoute + 4 * e
      | .matched matchings _ =>
        let M_k := matchings.getD 0 []
        let F_k := fakeCompletion A B M_k
        cCore + cRoute + 4 * e +
          outerGameLoopCost cfg M r e z core coreCost route routeCost Hhat fuel
            (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k)

/-- Total operation count of `outerGame` (including port-graph construction `12 * e`). -/
def outerGameCost (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (G : Graph) (X : Finset ℕ) : ℕ :=
  let e := (G.inside X).length
  let z := e / DOut cfg M r
  let Hhat := portGraph cloud G X
  12 * e + outerGameLoopCost cfg M r e z core coreCost route routeCost Hhat (49 * LParam M + 1) [] []

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Bridging `MatchingPlayer` parameters to outer parameters -/

/-- `routePathLen` at `Δ = 10`, `b = bOut cfg M`, `L = LParam M` equals `dOut cfg M`. -/
theorem routePathLen_outer (cfg : ParamConfig) (M : ℕ) :
    routePathLen 10 (bOut cfg M) (LParam M) = dOut cfg M := by
  unfold routePathLen dOut; ring

/-- `routeCong` at `Δ = 10`, `b = bOut cfg M`, `L = LParam M` equals `ROut cfg M`. -/
theorem routeCong_outer (cfg : ParamConfig) (M : ℕ) :
    routeCong 10 (bOut cfg M) (LParam M) = ROut cfg M := by
  unfold routeCong routeBatchH ROut
  rw [routePathLen_outer]
  ring

private theorem two_le_bOut (cfg : ParamConfig) (M : ℕ) : 2 ≤ bOut cfg M := by
  unfold bOut
  have hk := cfg.kappa_pos
  have hL := four_le_LParam M
  have hE := cfg.hE
  have h1 : 16 * 4 * 5 * 1 ≤ 16 * cfg.kappa * (LParam M + 1) * cfg.E :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hk) (by omega)) hE
  omega

private theorem validTerminalPairs_singleton {X A B : Finset ℕ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hdisj : Disjoint A B) (hcard : A.card ≤ B.card) :
    ValidTerminalPairs X [(A, B)] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hA, hB, hcard⟩
  · simp [hdisj]

/-- Extract single-pair partial-matching guarantees from `RouteMatchedSpec` at `pairs = [(A, B)]`. -/
private theorem singlePair_matched {Hhat : Graph} {A B : Finset ℕ} {cfg : ParamConfig} {M z : ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z matchings emb) :
    let E := matchings.getD 0 []
    IsPartialMatching A B E ∧
      A.card - E.length ≤ z ∧
      IsEmbeddingOn ⟨Hhat.n, E⟩ Hhat Hhat.verts emb ∧
      ∀ i < Hhat.m, congestion ⟨Hhat.n, E⟩ emb i ≤ ROut cfg M := by
  obtain ⟨hlen, hpair, hdef, hemb, _, hcong⟩ := h
  cases matchings with
  | nil => simp at hlen
  | cons E rest =>
    cases rest with
    | cons _ _ => simp at hlen
    | nil =>
      have h0 := hpair 0 (by simp)
      simp only [List.getD_cons_zero, List.getElem_cons_zero] at h0
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
        add_zero] at hdef
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        routeCong_outer] at hemb hcong
      exact ⟨h0, hdef, hemb, hcong⟩

/-! ### Correctness of `outerGame` -/

/-- Accumulated loop invariant at step `k` of `outerGameLoop` (after `k` completed bisection rounds). -/
private structure LoopInv (cfg : ParamConfig) (M r e z : ℕ) (Hhat : Graph)
    (M_hist : ℕ → List (ℕ × ℕ)) (k : ℕ) (W_edges F_edges : List (ℕ × ℕ)) : Prop where
  hW_eq : W_edges = witnessEdges M_hist k
  hM_perf : ∀ j < k, IsPerfectMatchingOn (Finset.range (2 * e)) (M_hist j)
  hM_cut : ∀ j < k, ∃ C ⊆ Finset.range (2 * e),
    (Finset.range (2 * e)).card ≤ 4 * C.card ∧
    (∀ ed ∈ M_hist j, ¬ (ed.1 ∈ C ∧ ed.2 ∈ C)) ∧
    100 * (Graph.mk (2 * e) (witnessEdges M_hist j)).cutIn (Finset.range (2 * e)) C ≤
      (Finset.range (2 * e)).card
  hW_valid : (Graph.mk (2 * e) W_edges).IsValid
  hW_loopless : (Graph.mk (2 * e) W_edges).IsLoopless
  hW_deg : ∀ v < 2 * e, (Graph.mk (2 * e) W_edges).deg v ≤ k
  hF_valid : ∀ ed ∈ F_edges, ed.1 < 2 * e ∧ ed.2 < 2 * e
  hF_len : F_edges.length ≤ k * z
  hF_deg : ∀ v < 2 * e, (Graph.mk (2 * e) F_edges).deg v ≤ k
  hemb : GameEmbInv Hhat W_edges F_edges (ROut cfg M) k

private theorem loopInv_zero (cfg : ParamConfig) (M r e z : ℕ) (Hhat : Graph) :
    LoopInv cfg M r e z Hhat (fun _ => []) 0 [] [] where
  hW_eq := rfl
  hM_perf := fun _ hj => absurd hj (Nat.not_lt_zero _)
  hM_cut := fun _ hj => absurd hj (Nat.not_lt_zero _)
  hW_valid := fun _ he => by cases he
  hW_loopless := fun _ he => by cases he
  hW_deg := fun _ _ => by simp [Graph.deg, Graph.degIn, Graph.inside]
  hF_valid := fun _ he => by cases he
  hF_len := by simp
  hF_deg := fun _ _ => by simp [Graph.deg, Graph.degIn, Graph.inside]
  hemb := GameEmbInv.empty Hhat (ROut cfg M)

/-- Inductive specification of `outerGameLoop` starting from `k` completed rounds with
`k + fuel = 49 * LParam M + 1`. -/
private theorem outerGameLoop_spec {cfg : ParamConfig} {M r e z routeC : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {Hhat : Graph}
    (hcore : IsCorePlayer cfg M r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    (hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
      X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
      1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
      ValidTerminalPairs X' pairs →
      routeCost G' X' pairs Δ L b z' ≤
        routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
    (he_pos : 1 ≤ e) (hHhat_n : Hhat.n = 2 * e)
    (hHhat_val : Hhat.IsValid) (hHhat_loop : Hhat.IsLoopless)
    (hHhat_deg : ∀ v, Hhat.deg v ≤ 10)
    (h2e_pow : 2 * e ≤ (NOf M r) ^ r)
    (h2e_L : 2 * e < 2 ^ LParam M) :
    ∀ fuel k M_hist W_edges F_edges,
      k + fuel = 49 * LParam M + 1 →
      LoopInv cfg M r e z Hhat M_hist k W_edges F_edges →
      (match outerGameLoop cfg M r e z core route Hhat fuel W_edges F_edges with
      | .cut U =>
          U ⊆ Hhat.verts ∧
            bOut cfg M * Hhat.cut U ≤ min U.card (Hhat.verts \ U).card ∧
            z + 1 ≤ 2 * U.card ∧
            z + 1 ≤ 2 * (Hhat.verts \ U).card
      | .witness W_out F_out =>
          (Graph.mk (2 * e) W_out).IsExpansionExpanderOn (Finset.range (2 * e))
              (1 / (2 * (PParam cfg M r : ℝ))) ∧
            (∀ ed ∈ F_out, ed.1 < 2 * e ∧ ed.2 < 2 * e) ∧
            F_out.length ≤ tParam M * z ∧
            (∀ v < 2 * e, (Graph.mk (2 * e) F_out).deg v ≤ tParam M) ∧
            ∃ emb : ℕ → List ℕ,
              IsEmbeddingOn ⟨2 * e, W_out⟩ ⟨2 * e, Hhat.edges ++ F_out⟩ (Finset.range (2 * e)) emb ∧
              ∀ i < (Graph.mk (2 * e) (Hhat.edges ++ F_out)).m,
                congestion ⟨2 * e, W_out⟩ emb i ≤ tParam M * ROut cfg M) ∧
      outerGameLoopCost cfg M r e z core coreCost route routeCost Hhat fuel W_edges F_edges ≤
        fuel * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
          routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
  have hHhat_verts : Hhat.verts = Finset.range (2 * e) := by
    unfold Graph.verts; rw [hHhat_n]
  have hHhat_card : Hhat.verts.card = Hhat.n := Finset.card_range Hhat.n
  have hHhat_card_L : Hhat.verts.card < 2 ^ LParam M := by rw [hHhat_card, hHhat_n]; exact h2e_L
  have hHhat_ins : Hhat.inside Hhat.verts = Hhat.edges := inside_verts_of_isValid hHhat_val
  have hHhat_ins_loop : ∀ ed ∈ Hhat.inside Hhat.verts, ed.1 ≠ ed.2 := by
    rw [hHhat_ins]; exact hHhat_loop
  have hL1 : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hb2 : 2 ≤ bOut cfg M := two_le_bOut cfg M
  have hdegIn : ∀ v ∈ Hhat.verts, Hhat.degIn Hhat.verts v ≤ 10 := fun v _ => hHhat_deg v
  have hroute_step : ∀ A B : Finset ℕ, A ⊆ Hhat.verts → B ⊆ Hhat.verts →
      Disjoint A B → A.card ≤ B.card →
      RouteSpec Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z
        (route Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z) ∧
      routeCost Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z ≤
        routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) := by
    intro A B hA hB hd hc
    have hvp := validTerminalPairs_singleton hA hB hd hc
    refine ⟨hroute.spec Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z
      (Finset.Subset.refl _) hHhat_ins_loop (by decide) hdegIn hL1 hHhat_card_L hb2 hvp, ?_⟩
    have hcb := hrouteC Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z
      (Finset.Subset.refl _) hHhat_ins_loop (by decide) hdegIn hL1 hHhat_card_L hb2 hvp
    rw [hHhat_card, hHhat_ins, routePathLen_outer, routeCong_outer] at hcb
    simpa [Graph.m] using hcb
  intro fuel
  induction fuel with
  | zero =>
    intro k M_hist W_edges F_edges hk hinv
    exfalso
    have hk_eq : k = 49 * LParam M + 1 := by omega
    have hVne : (Finset.range (2 * e)).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_range]; omega)
    have hVL : (Finset.range (2 * e)).card < 2 ^ LParam M := by
      rw [Finset.card_range]; exact h2e_L
    have hlt := round_bound_nat (n := 2 * e) hVne hVL hinv.hM_perf hinv.hM_cut
    omega
  | succ fuel ih =>
    intro k M_hist W_edges F_edges hk hinv
    have hL4 : 4 ≤ LParam M := four_le_LParam M
    have hk_le_delta : k ≤ deltaParam M := by unfold deltaParam tParam; omega
    have hk1_le_t : k + 1 ≤ tParam M := by unfold tParam; omega
    let W : Graph := Graph.mk (2 * e) W_edges
    have hW_deg_delta : ∀ v < W.n, W.deg v ≤ deltaParam M := fun v hv =>
      le_trans (hinv.hW_deg v hv) hk_le_delta
    have hcore_spec := hcore.spec_coreLevel hinv.hW_valid hinv.hW_loopless h2e_pow hW_deg_delta
    have hcore_cost : coreCost (coreLevel M r (2 * e)) W ≤
        2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) :=
      hcore.cost_coreLevel hinv.hW_valid hinv.hW_loopless (by omega : 2 ≤ 2 * e) h2e_pow hW_deg_delta
    dsimp only [outerGameLoop, outerGameLoopCost]
    cases hres : core (coreLevel M r (2 * e)) W with
    | expander S =>
      dsimp only
      rw [hres] at hcore_spec
      obtain ⟨hSV, hS2, hSexp⟩ := hcore_spec
      change S ⊆ Finset.range (2 * e) at hSV
      change 2 * e ≤ 2 * S.card at hS2
      let A : Finset ℕ := Finset.range (2 * e) \ S
      have hAV : A ⊆ Hhat.verts := by rw [hHhat_verts]; exact Finset.sdiff_subset
      have hSV' : S ⊆ Hhat.verts := by rw [hHhat_verts]; exact hSV
      have hdisjAS : Disjoint A S := disjoint_sdiff_self_left
      have hAcard_le : A.card ≤ S.card := by
        have hsum := Finset.card_sdiff_add_card_eq_card hSV
        rw [Finset.card_range] at hsum
        dsimp only [A]
        omega
      obtain ⟨hrt_spec, hrt_cost⟩ := hroute_step A S hAV hSV' hdisjAS hAcard_le
      have hcost_step :
          coreCost (coreLevel M r (2 * e)) W +
              routeCost Hhat Hhat.verts [(A, S)] 10 (LParam M) (bOut cfg M) z + 4 * e ≤
            (fuel + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
        have h1 : coreCost (coreLevel M r (2 * e)) W +
              routeCost Hhat Hhat.verts [(A, S)] 10 (LParam M) (bOut cfg M) z + 4 * e ≤
            1 * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
          rw [one_mul]; omega
        exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))
      cases hrt : route Hhat Hhat.verts [(A, S)] 10 (LParam M) (bOut cfg M) z with
      | cut U =>
        dsimp only
        rw [hrt] at hrt_spec
        exact ⟨hrt_spec, hcost_step⟩
      | matched matchings emb_inj =>
        dsimp only
        rw [hrt] at hrt_spec
        let M_inj := matchings.getD 0 []
        obtain ⟨hM_pm, hM_def, hemb_inj, hcong_inj⟩ := singlePair_matched hrt_spec
        change A.card - M_inj.length ≤ z at hM_def
        let F_inj := fakeCompletion A S M_inj
        obtain ⟨hF_len, hF_pm, hF_deg, hE_pm, _, hE_covA, _⟩ :=
          fakeCompletion_spec hdisjAS hAcard_le hM_pm
        change F_inj.length = A.card - M_inj.length at hF_len
        change ∀ n v, (Graph.mk n F_inj).deg v ≤ 1 at hF_deg
        have hPr_ge1 : (1 : ℝ) ≤ (PParam cfg M r : ℝ) := by
          exact_mod_cast one_le_PParam cfg M r
        have hβ0 : (0 : ℝ) ≤ 1 / (PParam cfg M r : ℝ) := by positivity
        have hβ1 : (1 : ℝ) / (PParam cfg M r : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact hPr_ge1
        have hW_exp : (Graph.mk (2 * e) (W_edges ++ (M_inj ++ F_inj))).IsExpansionExpanderOn
            (Finset.range (2 * e)) (1 / (2 * (PParam cfg M r : ℝ))) := by
          have h1 := isExpansionExpanderOn_of_injection (n := 2 * e) (E := W_edges)
            (M := M_inj ++ F_inj) (X := Finset.range (2 * e)) (S := S) hβ0 hβ1 hSV hSexp
            (fun ed hed => by
              have hm := hE_pm.1 ed hed
              have hA := Finset.mem_sdiff.mp hm.1
              exact ⟨hA.1, hA.2, hm.2⟩)
            hE_pm.2.2
            (fun v hvV hvS => hE_covA v (Finset.mem_sdiff.mpr ⟨hvV, hvS⟩))
          have hdiv : (1 : ℝ) / (PParam cfg M r : ℝ) / 2 = 1 / (2 * (PParam cfg M r : ℝ)) := by
            ring
          rwa [hdiv] at h1
        have hF_inj_valid : ∀ ed ∈ F_inj, ed.1 < 2 * e ∧ ed.2 < 2 * e := by
          intro ed hed
          have hm := hF_pm.1 ed hed
          exact ⟨Finset.mem_range.mp (Finset.sdiff_subset hm.1),
            Finset.mem_range.mp (hSV hm.2)⟩
        have hF_all_valid : ∀ ed ∈ F_edges ++ F_inj, ed.1 < 2 * e ∧ ed.2 < 2 * e := by
          intro ed hed
          rcases List.mem_append.mp hed with h | h
          · exact hinv.hF_valid ed h
          · exact hF_inj_valid ed h
        have hF_all_len : (F_edges ++ F_inj).length ≤ tParam M * z := by
          rw [List.length_append]
          have h1 : F_edges.length ≤ k * z := hinv.hF_len
          have h2 : F_inj.length ≤ z := by omega
          have h3 : (k + 1) * z ≤ tParam M * z := Nat.mul_le_mul_right z hk1_le_t
          have h4 : k * z + z = (k + 1) * z := by ring
          omega
        have hF_all_deg : ∀ v < 2 * e, (Graph.mk (2 * e) (F_edges ++ F_inj)).deg v ≤ tParam M := by
          intro v hv
          rw [deg_append]
          have h1 := hinv.hF_deg v hv
          have h2 := hF_deg (2 * e) v
          omega
        have hM_inj_ends : ∀ ed ∈ M_inj, ed.1 ∈ Hhat.verts ∧ ed.2 ∈ Hhat.verts := by
          intro ed hed
          have hm := hM_pm.1 ed hed
          exact ⟨hAV hm.1, hSV' hm.2⟩
        have hF_inj_ends : ∀ ed ∈ F_inj, ed.1 ∈ Hhat.verts ∧ ed.2 ∈ Hhat.verts := by
          intro ed hed
          have hm := hF_pm.1 ed hed
          exact ⟨hAV hm.1, hSV' hm.2⟩
        have hemb_next := hinv.hemb.append_round hemb_inj hcong_inj hM_inj_ends hF_inj_ends
        have h1_le_tR : 1 ≤ tParam M * ROut cfg M :=
          Nat.mul_pos (one_le_tParam M) (one_le_ROut cfg M)
        have hkR_le : (k + 1) * ROut cfg M ≤ tParam M * ROut cfg M :=
          Nat.mul_le_mul_right _ hk1_le_t
        obtain ⟨emb_out, hemb_out, hcong_out⟩ := hemb_next.congestion_le h1_le_tR hkR_le
        rw [hHhat_n, hHhat_verts] at hemb_out
        rw [hHhat_n] at hcong_out
        exact ⟨⟨hW_exp, hF_all_valid, hF_all_len, hF_all_deg, emb_out, hemb_out, hcong_out⟩,
          hcost_step⟩
    | cut U =>
      dsimp only
      rw [hres] at hcore_spec
      obtain ⟨hUV, hU1, hU2, hUcut⟩ := hcore_spec
      change U ⊆ Finset.range (2 * e) at hUV
      change 2 * e ≤ 4 * U.card at hU1
      change 2 * e ≤ 4 * (Finset.range (2 * e) \ U).card at hU2
      change 100 * W.cut U ≤ 2 * e at hUcut
      obtain ⟨hCV, hC4, _, hAV, hBV, hdisjAB, hunionAB, hAcard, hBcard, _, hdisjCB, hCcut⟩ :=
        padToBisection_spec hUV hU1 hU2
      let A : Finset ℕ := (padToBisection e U).1
      let B : Finset ℕ := (padToBisection e U).2
      change A.card = e at hAcard
      change B.card = e at hBcard
      change Disjoint A B at hdisjAB
      change A ∪ B = Finset.range (2 * e) at hunionAB
      have hAV' : A ⊆ Hhat.verts := by rw [hHhat_verts]; exact hAV
      have hBV' : B ⊆ Hhat.verts := by rw [hHhat_verts]; exact hBV
      obtain ⟨hrt_spec, hrt_cost⟩ := hroute_step A B hAV' hBV' hdisjAB (by omega)
      cases hrt : route Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z with
      | cut U_cut =>
        dsimp only
        rw [hrt] at hrt_spec
        refine ⟨hrt_spec, ?_⟩
        have h1 : coreCost (coreLevel M r (2 * e)) W +
              routeCost Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z + 4 * e ≤
            1 * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
          rw [one_mul]; omega
        exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))
      | matched matchings emb_k =>
        dsimp only
        rw [hrt] at hrt_spec
        let M_k := matchings.getD 0 []
        obtain ⟨hMk_pm, hMk_def, hemb_k, hcong_k⟩ := singlePair_matched hrt_spec
        change A.card - M_k.length ≤ z at hMk_def
        let F_k := fakeCompletion A B M_k
        obtain ⟨hFk_len, hFk_pm, hFk_deg, hEk_pm, hEk_nd, _, hEk_perf⟩ :=
          fakeCompletion_spec hdisjAB (by omega) hMk_pm
        change F_k.length = A.card - M_k.length at hFk_len
        change ∀ n v, (Graph.mk n F_k).deg v ≤ 1 at hFk_deg
        let E_k := M_k ++ F_k
        have hEk_perfV : IsPerfectMatchingOn (Finset.range (2 * e)) E_k :=
          hEk_perf (Finset.range (2 * e)) (by omega) hunionAB
        set M_hist' : ℕ → List (ℕ × ℕ) := fun j => if j = k then E_k else M_hist j
        have hwit_eq : ∀ j ≤ k, witnessEdges M_hist' j = witnessEdges M_hist j := by
          intro j hj
          induction j with
          | zero => rfl
          | succ m ihm =>
            simp only [witnessEdges, ihm (by omega), M_hist']
            have hne : m ≠ k := by omega
            simp [hne]
        have hinv_next : LoopInv cfg M r e z Hhat M_hist' (k + 1) (W_edges ++ E_k) (F_edges ++ F_k) := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [witnessEdges, hwit_eq k le_rfl, M_hist', ↓reduceIte, hinv.hW_eq]
          · intro j hj
            by_cases hjk : j = k
            · subst hjk; simpa [M_hist'] using hEk_perfV
            · simpa [M_hist', hjk] using hinv.hM_perf j (by omega)
          · intro j hj
            by_cases hjk : j = k
            · subst hjk
              refine ⟨outerSmallerSide e U, hCV, by rw [Finset.card_range]; exact hC4, ?_, ?_⟩
              · intro ed hed
                simp only [M_hist', ↓reduceIte] at hed
                have hm := hEk_pm.1 ed hed
                intro ⟨_, h2⟩
                exact Finset.disjoint_left.mp hdisjCB h2 hm.2
              · rw [hwit_eq j le_rfl, ← hinv.hW_eq, hCcut, Finset.card_range]
                exact hUcut
            · have hprev := hinv.hM_cut j (by omega)
              obtain ⟨C, h1, h2, h3, h4⟩ := hprev
              refine ⟨C, h1, h2, ?_, ?_⟩
              · simpa [M_hist', hjk] using h3
              · rwa [hwit_eq j (by omega)]
          · intro ed hed
            rcases List.mem_append.mp hed with h | h
            · exact hinv.hW_valid ed h
            · have hm := hEk_pm.1 ed h
              exact ⟨Finset.mem_range.mp (hAV hm.1), Finset.mem_range.mp (hBV hm.2)⟩
          · intro ed hed
            rcases List.mem_append.mp hed with h | h
            · exact hinv.hW_loopless ed h
            · have hm := hEk_pm.1 ed h
              exact fun heq => Finset.disjoint_left.mp hdisjAB hm.1 (heq ▸ hm.2)
          · intro v hv
            rw [deg_append]
            have h1 := hinv.hW_deg v hv
            have h2 : (Graph.mk (2 * e) E_k).deg v ≤ 1 :=
              deg_le_one_of_nodup_flatMap (n := 2 * e) hEk_nd v
            omega
          · intro ed hed
            rcases List.mem_append.mp hed with h | h
            · exact hinv.hF_valid ed h
            · have hm := hFk_pm.1 ed h
              exact ⟨Finset.mem_range.mp (hAV hm.1), Finset.mem_range.mp (hBV hm.2)⟩
          · rw [List.length_append]
            have h1 := hinv.hF_len
            have h2 : F_k.length ≤ z := by omega
            have hring : (k + 1) * z = k * z + z := by ring
            omega
          · intro v hv
            rw [deg_append]
            have h1 := hinv.hF_deg v hv
            have h2 := hFk_deg (2 * e) v
            omega
          · exact hinv.hemb.append_round hemb_k hcong_k
              (fun ed hed => ⟨hAV' (hMk_pm.1 ed hed).1, hBV' (hMk_pm.1 ed hed).2⟩)
              (fun ed hed => ⟨hAV' (hFk_pm.1 ed hed).1, hBV' (hFk_pm.1 ed hed).2⟩)
        obtain ⟨hrec_spec, hrec_cost⟩ :=
          ih (k + 1) M_hist' (W_edges ++ E_k) (F_edges ++ F_k) (by omega) hinv_next
        refine ⟨hrec_spec, ?_⟩
        have hring : (fuel + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) =
            (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) +
            fuel * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
              routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
          ring
        have hstep_cost :
            coreCost (coreLevel M r (2 * e)) W +
                routeCost Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z + 4 * e ≤
              2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
                routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e := by
          omega
        rw [hring]
        exact Nat.add_le_add hstep_cost hrec_cost

/-- **Cut-matching game specification**: running `outerGame` on an induced subgraph
`G[X]` with `1 ≤ e`, `2e ≤ N^r`, and `2e < 2^L` returns either a sparse port cut or a spanning port
witness with embedding congestion `≤ t · R_out`, fake edges `≤ t · z`, and fake port degree `≤ t`. -/
theorem outerGame_spec {cfg : ParamConfig} {M r : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (hcore : IsCorePlayer cfg M r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ}
    (he_pos : 1 ≤ (G.inside X).length)
    (h2e_pow : 2 * (G.inside X).length ≤ (NOf M r) ^ r)
    (h2e_L : 2 * (G.inside X).length < 2 ^ LParam M) :
    let e := (G.inside X).length
    let z := e / DOut cfg M r
    let Hhat := portGraph cloud G X
    match outerGame cfg M r cloud core route G X with
    | .cut U =>
        U ⊆ Hhat.verts ∧
          bOut cfg M * Hhat.cut U ≤ min U.card (Hhat.verts \ U).card ∧
          z + 1 ≤ 2 * U.card ∧
          z + 1 ≤ 2 * (Hhat.verts \ U).card
    | .witness W_out F_out =>
        (Graph.mk (2 * e) W_out).IsExpansionExpanderOn (Finset.range (2 * e))
            (1 / (2 * (PParam cfg M r : ℝ))) ∧
          (∀ ed ∈ F_out, ed.1 < 2 * e ∧ ed.2 < 2 * e) ∧
          F_out.length ≤ tParam M * z ∧
          (∀ v < 2 * e, (Graph.mk (2 * e) F_out).deg v ≤ tParam M) ∧
          ∃ emb : ℕ → List ℕ,
            IsEmbeddingOn ⟨2 * e, W_out⟩ ⟨2 * e, Hhat.edges ++ F_out⟩ (Finset.range (2 * e)) emb ∧
            ∀ i < (Graph.mk (2 * e) (Hhat.edges ++ F_out)).m,
              congestion ⟨2 * e, W_out⟩ emb i ≤ tParam M * ROut cfg M := by
  obtain ⟨C, hC⟩ := hroute.cost_bound
  exact (outerGameLoop_spec hcore hroute hC he_pos (portGraph_n cloud G X)
    (portGraph_isValid hcloud G X) (portGraph_isLoopless hcloud G X)
    (portGraph_deg_le hcloud G X) h2e_pow h2e_L (49 * LParam M + 1) 0 (fun _ => []) [] []
    (by omega) (loopInv_zero cfg M r (G.inside X).length ((G.inside X).length / DOut cfg M r)
      (portGraph cloud G X))).1

/-- **Cut-matching game cost**: given a concrete router cost constant `routeC`,
bounds `outerGameCost` on `G[X]`. -/
theorem outerGame_cost_le {cfg : ParamConfig} {M r routeC : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (hcore : IsCorePlayer cfg M r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    (hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
      X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
      1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
      ValidTerminalPairs X' pairs →
      routeCost G' X' pairs Δ L b z' ≤
        routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
    {G : Graph} {X : Finset ℕ}
    (he_pos : 1 ≤ (G.inside X).length)
    (h2e_pow : 2 * (G.inside X).length ≤ (NOf M r) ^ r)
    (h2e_L : 2 * (G.inside X).length < 2 ^ LParam M) :
    let e := (G.inside X).length
    outerGameCost cfg M r cloud core coreCost route routeCost G X ≤
      12 * e + (49 * LParam M + 1) *
        (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
          routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) := by
  let e := (G.inside X).length
  let z := e / DOut cfg M r
  let Hhat := portGraph cloud G X
  have hcost := (outerGameLoop_spec hcore hroute hrouteC he_pos (portGraph_n cloud G X)
    (portGraph_isValid hcloud G X) (portGraph_isLoopless hcloud G X)
    (portGraph_deg_le hcloud G X) h2e_pow h2e_L (49 * LParam M + 1) 0 (fun _ => []) [] []
    (by omega) (loopInv_zero cfg M r e z Hhat)).2
  have hnm : Hhat.n + Hhat.m + 1 ≤ 12 * e + 1 := by
    have hn : Hhat.n = 2 * e := portGraph_n cloud G X
    have hm : Hhat.m ≤ 10 * e := portGraph_m_le hcloud G X
    omega
  have hrt_le : routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) ≤
      routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) :=
    Nat.mul_le_mul_left routeC (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hnm)) 1)
  have hmul : (49 * LParam M + 1) *
      (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
        routeC * ((Hhat.n + Hhat.m + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) ≤
      (49 * LParam M + 1) *
      (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
        routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold outerGameCost
  dsimp only
  exact Nat.add_le_add_left (le_trans hcost hmul) (12 * e)

/-! ### Witness contraction and `RemoveFake` -/

/-- **Witness outcome**: given a witness `(W_out, F_out)`
from `outerGame`, contracting clouds and applying `removeFake` at `ρ = 1 / Λ` yields `R ⊆ X`
satisfying:
1. `R.Nonempty` (when `1 ≤ e`);
2. `G.IsConductanceExpanderOn R (1 / QOut cfg M r)`;
3. `∀ v ∈ R, 1 ≤ G.degIn R v`;
4. `16 * bOut cfg M * G.volIn X (X \ R) ≤ e`. -/
theorem outerWitness_removeFake {cfg : ParamConfig} {M r : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hA60 : 60 ≤ cfg.A)
    {G : Graph} {X : Finset ℕ} (hv : G.IsValid) (hX : X ⊆ G.verts)
    (hXdeg : ∀ v ∈ X, 1 ≤ G.degIn X v)
    (he_pos : 1 ≤ (G.inside X).length)
    {W_out F_out : List (ℕ × ℕ)}
    (hW_exp : (Graph.mk (2 * (G.inside X).length) W_out).IsExpansionExpanderOn
      (Finset.range (2 * (G.inside X).length)) (1 / (2 * (PParam cfg M r : ℝ))))
    (hF_valid : ∀ ed ∈ F_out, ed.1 < 2 * (G.inside X).length ∧ ed.2 < 2 * (G.inside X).length)
    (hF_len : F_out.length ≤ tParam M * ((G.inside X).length / DOut cfg M r))
    (hF_deg : ∀ v < 2 * (G.inside X).length,
      (Graph.mk (2 * (G.inside X).length) F_out).deg v ≤ tParam M)
    {emb : ℕ → List ℕ}
    (hemb : IsEmbeddingOn ⟨2 * (G.inside X).length, W_out⟩
      ⟨2 * (G.inside X).length, (portGraph cloud G X).edges ++ F_out⟩
      (Finset.range (2 * (G.inside X).length)) emb)
    (hcong : ∀ i < (Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F_out)).m,
      congestion ⟨2 * (G.inside X).length, W_out⟩ emb i ≤ tParam M * ROut cfg M) :
    let F' := contractEdges G X F_out
    let R := removeFake G.n G.edges F' X (1 / (Lambda cfg M r : ℝ))
    R ⊆ X ∧
      R.Nonempty ∧
      G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)) ∧
      (∀ v ∈ R, 1 ≤ G.degIn R v) ∧
      16 * bOut cfg M * G.volIn X (X \ R) ≤ (G.inside X).length := by
  let e := (G.inside X).length
  let z := e / DOut cfg M r
  let F' := contractEdges G X F_out
  let Λ := Lambda cfg M r
  let R := removeFake G.n G.edges F' X (1 / (Λ : ℝ))
  have hηpos : 0 < tParam M * ROut cfg M :=
    Nat.mul_pos (one_le_tParam M) (one_le_ROut cfg M)
  have hβ0 : (0 : ℝ) ≤ 1 / (2 * (PParam cfg M r : ℝ)) := by positivity
  have hKcond_raw := isConductanceExpanderOn_contractedGraph_of_embedding hcloud hF_valid hF_deg
    hηpos hemb hcong hβ0 hW_exp
  have hLam_eq : (1 / (2 * (PParam cfg M r : ℝ))) /
      (((tParam M * ROut cfg M : ℕ) : ℝ) * ((tParam M + 1 : ℕ) : ℝ)) = 1 / (Λ : ℝ) := by
    have hPpos : (0 : ℝ) < (PParam cfg M r : ℝ) := by exact_mod_cast one_le_PParam cfg M r
    have htpos : (0 : ℝ) < (tParam M : ℝ) := by exact_mod_cast one_le_tParam M
    have hRpos : (0 : ℝ) < (ROut cfg M : ℝ) := by exact_mod_cast one_le_ROut cfg M
    have h1 : (Λ : ℝ) = (2 : ℝ) * (PParam cfg M r : ℝ) * (tParam M : ℝ) * (ROut cfg M : ℝ) *
        ((tParam M : ℝ) + 1) := by
      dsimp only [Λ]; unfold Lambda; push_cast; ring
    rw [h1]
    push_cast
    field_simp
  rw [hLam_eq] at hKcond_raw
  have hF'mem : ∀ ed ∈ F', ed.1 ∈ X ∧ ed.2 ∈ X := fun ed hed =>
    ⟨(mem_contractEdges hF_valid hed).1, (mem_contractEdges hF_valid hed).2.1⟩
  have hΛ1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hρ0 : (0 : ℝ) < 1 / (Λ : ℝ) := by positivity
  have hρ1 : (1 : ℝ) / (Λ : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hΛ1
  have hKdeg : ∀ v ∈ X, 1 ≤ (contractedGraph G X F_out).degIn X v := by
    intro v hv
    have h1 := hXdeg v hv
    have h2 : G.degIn X v ≤ (contractedGraph G X F_out).degIn X v := by
      unfold contractedGraph
      rw [degIn_eq_sum_map, degIn_eq_sum_map]
      unfold Graph.inside
      dsimp only
      rw [List.filter_append, List.map_append, List.sum_append]
      omega
    omega
  obtain ⟨hRX, hRcond, hRdeg, hRvol⟩ :=
    removeFake_spec hX hv hF'mem hρ0 hρ1 hKcond_raw hKdeg
  have hRcondQ : G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)) := by
    apply isConductanceExpanderOn_mono _ hRcond
    have h12 : 12 * Λ ≤ QOut cfg M r := twelve_mul_Lambda_le_QOut cfg M r
    have h9 : (9 * Λ : ℝ) ≤ (QOut cfg M r : ℝ) := by exact_mod_cast (by omega : 9 * Λ ≤ QOut cfg M r)
    have h9pos : (0 : ℝ) < 9 * (Λ : ℝ) := by positivity
    have hrew : (1 : ℝ) / (Λ : ℝ) / 9 = 1 / (9 * (Λ : ℝ)) := by ring
    rw [hrew]
    exact one_div_le_one_div_of_le h9pos h9
  have hvol_le_K : G.volIn X (X \ R) ≤ (contractedGraph G X F_out).volIn X (X \ R) := by
    unfold contractedGraph
    rw [volIn_eq_sum_map, volIn_eq_sum_map]
    unfold Graph.inside
    dsimp only
    rw [List.filter_append, List.map_append, List.sum_append]
    omega
  have hF'len : F'.length ≤ tParam M * z :=
    le_trans (contractEdges_length_le G X F_out) hF_len
  have hvol_nat : G.volIn X (X \ R) ≤ cfg.A * tParam M * z * Λ := by
    have h1 : (G.volIn X (X \ R) : ℝ) ≤ (60 / (1 / (Λ : ℝ))) * (F'.length : ℝ) :=
      le_trans (by exact_mod_cast hvol_le_K) hRvol
    have h2 : (60 : ℝ) / (1 / (Λ : ℝ)) = 60 * (Λ : ℝ) := by field_simp
    rw [h2] at h1
    have h3 : (G.volIn X (X \ R) : ℝ) ≤ ((60 * Λ * F'.length : ℕ) : ℝ) := by
      push_cast; linarith
    have h4 : G.volIn X (X \ R) ≤ 60 * Λ * F'.length := by exact_mod_cast h3
    calc G.volIn X (X \ R) ≤ 60 * Λ * F'.length := h4
      _ ≤ cfg.A * Λ * (tParam M * z) := Nat.mul_le_mul (Nat.mul_le_mul_right Λ hA60) hF'len
      _ = cfg.A * tParam M * z * Λ := by ring
  have h35 : 16 * bOut cfg M * G.volIn X (X \ R) ≤ e := by
    calc 16 * bOut cfg M * G.volIn X (X \ R)
        ≤ 16 * bOut cfg M * (cfg.A * tParam M * z * Λ) := Nat.mul_le_mul_left _ hvol_nat
      _ = DOut cfg M r * z := by dsimp only [Λ]; unfold DOut; ring
      _ ≤ e := Nat.mul_div_le e (DOut cfg M r)
  have hRne : R.Nonempty := by
    have hret : 15 * (G.inside X).length ≤ 16 * (G.inside R).length :=
      (edge_shrink_witness G hRX (one_le_bOut cfg M) (one_le_DOut cfg M r) he_pos h35).2.2.2.1
    have hR_pos : 0 < (G.inside R).length := by omega
    obtain ⟨ed, hed⟩ := List.exists_mem_of_length_pos hR_pos
    exact ⟨ed.1, (mem_inside_iff.mp hed).2.1⟩
  exact ⟨hRX, hRne, hRcondQ, hRdeg, h35⟩

end MinCostFlow.ExpanderDecomp
