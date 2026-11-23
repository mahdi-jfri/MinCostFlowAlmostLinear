module

public import WordRAM.Contract
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.OneShotProgFilterEdges
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
public import MinCostFlow.ExpanderDecomp.OneShotStepD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step D Word-RAM Procedure for `OneShot`

Defines the shared procedure-index table `CoreIdx`, the deterministic Word-RAM procedure
`stepDProc` for Step D of `OneShot` (filtering `G.inside X` via `filterEdgesInProc` and calling
`ProgRemoveFake.removeFakeContract` at `ρ = 12 / P_q`), and proves:
* `stepDProc_noRand`: `stepDProc` uses no randomness.
* `stepDProc_meetsContract`: `MeetsContract w p idx.stepD (stepDContract w)`.
* `stepD_of_removeFake_out`: relational version of `stepD_removeFake` bridging the postcondition
  of `ProgRemoveFake.removeFakeContract` directly to `OneShotSpec` (`R ⊆ X`,
  `11 * |X| ≤ 12 * |R|`, and `G.IsExpansionExpanderOn R (1 / P_q)`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Procedure Index Table -/

/-- Procedure indices for the `OneShot` / `Core` Word-RAM module and its 4 external callees. -/
structure CoreIdx where
  copyWords     : ℕ
  initRange     : ℕ
  filterDiff    : ℕ
  filterInter   : ℕ
  filterEdgesIn : ℕ
  completeFake  : ℕ
  stepD         : ℕ
  stepCLeftover : ℕ
  stepCMacro    : ℕ
  stepBRound    : ℕ
  stepB         : ℕ
  oneShot       : ℕ
  coreOn        : ℕ
  core          : ℕ
  routeOrCut    : ℕ
  cloudExpander : ℕ
  edgeColor17   : ℕ
  removeFake    : ℕ

/-! ## 2. Step D Space, Cost, Procedure, and Contract -/

/-- Heap advance of `stepDProc` (strictly covering `rhoAddr`, `hEdgesAddr`, and `workAddr`). -/
def stepDSpace (k mG mF L Pq : ℕ) : ℕ :=
  16 * k + 9 * mG + 30 * mF + 40 * (Pq + 2) * L + 11

/-- Word-size headroom required above `h` for `stepDProc` and `ProgRemoveFake.removeFakeContract`. -/
def stepDWordSpace (k mG mF L Pq : ℕ) : ℕ :=
  16 * k + 9 * mG + 30 * mF + 40 * (Pq + 2) * L +
    8 * (Pq + 2) * (mG + 2 * mF) + 16 * Pq + 40

/-- Word-RAM step bound of `stepDProc`. -/
def stepDCost (k mG mH mF Pq : ℕ) : ℕ :=
  filterEdgesInCost k mG + removeFakeCost k mH mF 12 Pq + 150

/-- Step D procedure: `args = [gAddr, k, xAddr, mF, fAddr, L, Pq, locAddr, outAddr, h]`.
Filters `H = G.inside X`, calls `idx.removeFake` at `ρ = 12 / Pq`, writes `CoreOutAt` at
`outAddr`, and returns the advanced heap pointer `h + stepDSpace k G.m mF L Pq`. -/
def stepDProc (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 10 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 11 (.bin .add (.reg 0) (.const 2))
    , .store (.reg 9) (.const 12)
    , .store (.bin .add (.reg 9) (.const 1)) (.reg 6)
    , .assign 12 (.bin .add (.reg 9) (.const 2))
    , .call 13 idx.filterEdgesIn [.reg 10, .reg 11, .reg 1, .reg 2, .reg 7, .reg 12]
    , .assign 14 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 10)))
    , .assign 15 (.bin .add (.reg 8) (.const 2))
    , .call 16 idx.removeFake
        [.reg 1, .reg 2, .reg 13, .reg 12, .reg 3, .reg 4, .reg 9, .reg 7, .reg 15, .reg 14]
    , .store (.reg 8) (.const 1)
    , .store (.bin .add (.reg 8) (.const 1)) (.reg 16)
    , .assign 17 (.bin .add (.reg 9)
        (.bin .add
          (.bin .add
            (.bin .add
              (.bin .mul (.const 16) (.reg 1))
              (.bin .mul (.const 9) (.reg 10)))
            (.bin .mul (.const 30) (.reg 3)))
          (.bin .add
            (.bin .mul (.bin .mul (.const 40) (.bin .add (.reg 6) (.const 2))) (.reg 5))
            (.const 11))))
    , .ret (.reg 17) ]

/-- Contract for `stepDProc`: `args = [gAddr, k, xAddr, mF, fAddr, L, Pq, locAddr, outAddr, h]`. -/
def stepDContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr k xAddr mF fAddr L Pq locAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)),
      args = [gAddr, k, xAddr, mF, fAddr, L, Pq, locAddr, outAddr, h] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      VertsAt mem xAddr k X ∧
      X ⊆ Finset.range G.n ∧
      EdgesAt mem fAddr F ∧
      F.length = mF ∧
      mF ≤ k ∧
      4 ≤ L ∧ k < 2 ^ L ∧ 12 ≤ Pq ∧
      (G.inside X).length ≤ 512 * L * k ∧
      (∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) ∧
      (Graph.mk G.n (G.inside X ++ F)).IsConductanceExpanderOn X ((12 : ℝ) / (Pq : ℝ)) ∧
      (∀ v ∈ X, 1 ≤ (Graph.mk G.n (G.inside X ++ F)).degIn X v) ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + k ≤ h ∧
      fAddr + 2 * mF ≤ h ∧
      locAddr + G.n ≤ h ∧
      outAddr + 2 + k ≤ h ∧
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) ∧
      DisjointRange locAddr G.n xAddr k ∧
      DisjointRange locAddr G.n fAddr (2 * mF) ∧
      DisjointRange locAddr G.n outAddr (2 + k) ∧
      DisjointRange outAddr (2 + k) xAddr k ∧
      DisjointRange outAddr (2 + k) fAddr (2 * mF) ∧
      ZeroFrom mem h ∧
      h + stepDWordSpace k G.m mF L Pq < 2 ^ w
  post args mem v mem' :=
    ∀ (gAddr k xAddr mF fAddr L Pq locAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)),
      args = [gAddr, k, xAddr, mF, fAddr, L, Pq, locAddr, outAddr, h] →
      GraphAt mem gAddr G →
      G.IsValid →
      VertsAt mem xAddr k X →
      X ⊆ Finset.range G.n →
      EdgesAt mem fAddr F →
      F.length = mF →
      mF ≤ k →
      4 ≤ L → k < 2 ^ L → 12 ≤ Pq →
      (G.inside X).length ≤ 512 * L * k →
      (∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) →
      (Graph.mk G.n (G.inside X ++ F)).IsConductanceExpanderOn X ((12 : ℝ) / (Pq : ℝ)) →
      (∀ v ∈ X, 1 ≤ (Graph.mk G.n (G.inside X ++ F)).degIn X v) →
      (∀ u < G.n, mem (locAddr + u) = 0) →
      gAddr + 2 + 2 * G.m ≤ h →
      xAddr + k ≤ h →
      fAddr + 2 * mF ≤ h →
      locAddr + G.n ≤ h →
      outAddr + 2 + k ≤ h →
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) →
      DisjointRange locAddr G.n xAddr k →
      DisjointRange locAddr G.n fAddr (2 * mF) →
      DisjointRange locAddr G.n outAddr (2 + k) →
      DisjointRange outAddr (2 + k) xAddr k →
      DisjointRange outAddr (2 + k) fAddr (2 * mF) →
      ZeroFrom mem h →
      h + stepDWordSpace k G.m mF L Pq < 2 ^ w →
      ∃ R : Finset ℕ,
        CoreOutAt mem' outAddr (.expander R) ∧
        R ⊆ X ∧
        (Graph.mk G.n (G.inside X)).IsConductanceExpanderOn R (((12 : ℝ) / (Pq : ℝ)) / 9) ∧
        (∀ u ∈ R, 1 ≤ (Graph.mk G.n (G.inside X)).degIn R u) ∧
        ((Graph.mk G.n (G.inside X ++ F)).volIn X (X \ R) : ℝ) ≤
          60 / ((12 : ℝ) / (Pq : ℝ)) * (mF : ℝ) ∧
        v = h + stepDSpace k G.m mF L Pq ∧
        ZeroFrom mem' v ∧
        (∀ u < G.n, mem' (locAddr + u) = 0) ∧
        (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let k := args.getD 1 0
    let xAddr := args.getD 2 0
    let mF := args.getD 3 0
    let Pq := args.getD 6 0
    let G := readGraph mem gAddr
    let X := (readList mem xAddr k).toFinset
    stepDCost k G.m (G.inside X).length mF Pq

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Induced-Subgraph Equivalence and Relational Step D Lemma -/

lemma inside_mk_inside {n : ℕ} {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X) :
    (Graph.mk n (G.inside X)).inside R = G.inside R := by
  unfold Graph.inside
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases h1 : e.1 ∈ R <;> by_cases h2 : e.2 ∈ R
  · simp [h1, h2, hRX h1, hRX h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma inside_append_inside {n : ℕ} {G : Graph} {F : List (ℕ × ℕ)} {X : Finset ℕ} :
    (Graph.mk n (G.inside X ++ F)).inside X = (Graph.mk n (G.edges ++ F)).inside X := by
  unfold Graph.inside
  simp only [List.filter_append]
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  cases decide (e.1 ∈ X) <;> cases decide (e.2 ∈ X) <;> rfl

lemma degIn_mk_inside {n : ℕ} {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X) (v : ℕ) :
    (Graph.mk n (G.inside X)).degIn R v = G.degIn R v := by
  unfold Graph.degIn
  rw [inside_mk_inside hRX]

lemma cutIn_mk_inside {n : ℕ} {G : Graph} {X R S : Finset ℕ} (hRX : R ⊆ X) :
    (Graph.mk n (G.inside X)).cutIn R S = G.cutIn R S := by
  unfold Graph.cutIn
  rw [inside_mk_inside hRX]

lemma volIn_mk_inside {n : ℕ} {G : Graph} {X R S : Finset ℕ} (hRX : R ⊆ X) :
    (Graph.mk n (G.inside X)).volIn R S = G.volIn R S := by
  unfold Graph.volIn
  apply Finset.sum_congr rfl
  intro v _
  exact degIn_mk_inside hRX v

lemma isConductanceExpanderOn_mk_inside {n : ℕ} {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X)
    {φ : ℝ} (h : (Graph.mk n (G.inside X)).IsConductanceExpanderOn R φ) :
    G.IsConductanceExpanderOn R φ := by
  intro S hSR
  have hS := h S hSR
  rwa [cutIn_mk_inside hRX, volIn_mk_inside hRX, volIn_mk_inside hRX] at hS

lemma degIn_append_inside {n : ℕ} {G : Graph} {F : List (ℕ × ℕ)} {X : Finset ℕ} (v : ℕ) :
    (Graph.mk n (G.inside X ++ F)).degIn X v = (Graph.mk n (G.edges ++ F)).degIn X v := by
  unfold Graph.degIn
  rw [inside_append_inside]

lemma cutIn_append_inside {n : ℕ} {G : Graph} {F : List (ℕ × ℕ)} {X S : Finset ℕ} :
    (Graph.mk n (G.inside X ++ F)).cutIn X S = (Graph.mk n (G.edges ++ F)).cutIn X S := by
  unfold Graph.cutIn
  rw [inside_append_inside]

lemma volIn_append_inside {n : ℕ} {G : Graph} {F : List (ℕ × ℕ)} {X S : Finset ℕ} :
    (Graph.mk n (G.inside X ++ F)).volIn X S = (Graph.mk n (G.edges ++ F)).volIn X S := by
  unfold Graph.volIn
  apply Finset.sum_congr rfl
  intro v _
  exact degIn_append_inside v

lemma isConductanceExpanderOn_append_inside {n : ℕ} {G : Graph} {F : List (ℕ × ℕ)} {X : Finset ℕ}
    {φ : ℝ} (h : (Graph.mk n (G.edges ++ F)).IsConductanceExpanderOn X φ) :
    (Graph.mk n (G.inside X ++ F)).IsConductanceExpanderOn X φ := by
  intro S hSX
  have hS := h S hSX
  rwa [← cutIn_append_inside, ← volIn_append_inside, ← volIn_append_inside] at hS

/-- Relational Step D bridge: given valid routing calls whose witness graph expands on `X`,
establishes both the preconditions of `stepDContract` on `H = G.inside X`, `F = callsFakeEdges calls`
and the implication from `stepDContract`'s postcondition on any `R` to the Step D guarantees
(`R ⊆ X`, `11 * |X| ≤ 12 * |R|`, `G.IsExpansionExpanderOn R (1 / P_q)`). -/
theorem stepD_of_removeFake_out {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq1 : 1 ≤ q) (hqr : q ≤ r) {G : Graph} {X : Finset ℕ}
    (hX2 : 2 ≤ X.card) (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ)
    {calls : List RoutedCall} (hcalls_len : calls.length ≤ cfg.Δ)
    (hcalls : ∀ c ∈ calls, c.Valid G X (routeCong cfg.Δ 100 cfg.L) (X.card / cfg.D q))
    (hwit_exp : (Graph.mk G.n (callsWitnessEdges calls)).IsExpansionExpanderOn X
      (cfg.α / (40 * (cfg.P (q - 1) : ℝ)))) :
    let H := G.inside X
    let F := callsFakeEdges calls
    let ρ : ℝ := (12 : ℝ) / (cfg.P q : ℝ)
    F.length ≤ X.card ∧
    (∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) ∧
    (Graph.mk G.n (H ++ F)).IsConductanceExpanderOn X ρ ∧
    (∀ v ∈ X, 1 ≤ (Graph.mk G.n (H ++ F)).degIn X v) ∧
    (∀ R : Finset ℕ, R ⊆ X →
      (Graph.mk G.n H).IsConductanceExpanderOn R (ρ / 9) →
      (∀ u ∈ R, 1 ≤ (Graph.mk G.n H).degIn R u) →
      ((Graph.mk G.n (H ++ F)).volIn X (X \ R) : ℝ) ≤ 60 / ρ * (F.length : ℝ) →
      R ⊆ X ∧ 11 * X.card ≤ 12 * R.card ∧ G.IsExpansionExpanderOn R (1 / (cfg.P q : ℝ))) := by
  dsimp only
  set H := G.inside X
  set F := callsFakeEdges calls
  set R_c := routeCong cfg.Δ 100 cfg.L
  set K := Graph.mk G.n (G.edges ++ F)
  set W := Graph.mk G.n (callsWitnessEdges calls)
  set ρ : ℝ := (12 : ℝ) / (cfg.P q : ℝ)
  have hRc_pos : 1 ≤ R_c := hcfg.routeCong_pos
  have hΔ_pos : 1 ≤ cfg.Δ := hcfg.hΔ_pos
  obtain ⟨hFlen, hFmem, hFdeg, emb, hemb, hcongG, hcongF⟩ := embed_calls calls hcalls
  set η := cfg.Δ * R_c
  have hη_pos : 0 < η := Nat.mul_pos hΔ_pos hRc_pos
  have hcong_all : ∀ i < K.m, congestion W emb i ≤ η := by
    intro i _
    by_cases hi : i < G.m
    · exact le_trans (hcongG i hi) (Nat.mul_le_mul_right R_c hcalls_len)
    · exact le_trans (hcongF i (by omega)) hη_pos
  have hdegK : ∀ v ∈ X, K.degIn X v ≤ 2 * cfg.Δ := by
    intro v hv
    show (Graph.mk G.n (G.edges ++ F)).degIn X v ≤ 2 * cfg.Δ
    rw [degIn_append]
    have h1 : (Graph.mk G.n G.edges).degIn X v ≤ cfg.Δ := hdegG v hv
    have h2 : (Graph.mk G.n F).degIn X v ≤ calls.length := hFdeg v hv
    omega
  have hPprev_pos : (0 : ℝ) < cfg.P (q - 1) := Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
  have hPq_pos : (0 : ℝ) < cfg.P q := Nat.cast_pos.mpr (hcfg.hP_pos hqr)
  have hψW_pos : 0 < cfg.α / (40 * (cfg.P (q - 1) : ℝ)) := div_pos hcfg.hα0 (by positivity)
  have hK_cond0 : K.IsConductanceExpanderOn X
      ((cfg.α / (40 * (cfg.P (q - 1) : ℝ))) / ((η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ))) :=
    isConductanceExpanderOn_of_embedding hemb hcong_all hη_pos hψW_pos.le hwit_exp
      (by omega : 0 < 2 * cfg.Δ) hdegK
  have hρ_le : ρ ≤ (cfg.α / (40 * (cfg.P (q - 1) : ℝ))) / ((η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ)) := by
    have hstep := hcfg.hPstep q hq1 hqr
    have hden_pos : (0 : ℝ) < (η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ) := by
      push_cast [η]; positivity
    rw [div_le_div_iff₀ hPq_pos hden_pos]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 40 * (cfg.P (q - 1) : ℝ))]
    have hcast : (η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ) = 2 * (cfg.Δ : ℝ) ^ 2 * (R_c : ℝ) := by
      push_cast [η]; ring
    rw [hcast]
    nlinarith
  have hK_cond : K.IsConductanceExpanderOn X ρ := isConductanceExpanderOn_mono hρ_le hK_cond0
  have hdegK_pos : ∀ v ∈ X, 1 ≤ K.degIn X v := by
    intro v hv
    have hsub : ({v} : Finset ℕ) ⊆ X := Finset.singleton_subset_iff.mpr hv
    have hne : ({v} : Finset ℕ).Nonempty := Finset.singleton_nonempty v
    have hneX : ({v} : Finset ℕ) ≠ X := by
      intro heq
      have hcard := congrArg Finset.card heq
      simp only [Finset.card_singleton] at hcard
      omega
    have hcutW := hwit_exp {v} hsub hne hneX
    have hsd_pos : 1 ≤ (X \ {v}).card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]
      omega
    have hmin1 : (1 : ℝ) ≤ min (({v} : Finset ℕ).card : ℝ) ((X \ {v}).card : ℝ) := by
      simp only [Finset.card_singleton, Nat.cast_one]
      exact le_min (le_refl 1) (by exact_mod_cast hsd_pos)
    have hWpos : (0 : ℝ) < (W.cutIn X {v} : ℝ) := lt_of_lt_of_le (by nlinarith) hcutW
    have hW1 : 1 ≤ W.cutIn X {v} := by
      have : (0 : ℕ) < W.cutIn X {v} := by exact_mod_cast hWpos
      omega
    have hcutK_mul : W.cutIn X {v} ≤ K.cutIn X {v} * η :=
      cutIn_le_mul_of_embedding hemb hcong_all {v}
    have hK1 : 1 ≤ K.cutIn X {v} := by
      by_contra h0
      have hk0 : K.cutIn X {v} = 0 := by omega
      rw [hk0, zero_mul] at hcutK_mul
      omega
    have hvol := cutIn_le_volIn K X {v}
    simp only [Graph.volIn, Finset.sum_singleton] at hvol
    omega
  have hDq_ge_nat : 60 * cfg.Δ * cfg.P q ≤ cfg.D q := hcfg.hD q hq1 hqr
  have hPq12 : 12 ≤ cfg.P q := hcfg.hP12 q hq1 hqr
  have hF_le_X : F.length ≤ X.card := by
    have h1 : F.length ≤ cfg.Δ * (X.card / cfg.D q) :=
      le_trans hFlen (Nat.mul_le_mul_right _ hcalls_len)
    have h2 : cfg.Δ ≤ cfg.D q := by
      have : 1 ≤ 60 * cfg.P q := by omega
      calc cfg.Δ = cfg.Δ * 1 := (Nat.mul_one _).symm
        _ ≤ cfg.Δ * (60 * cfg.P q) := Nat.mul_le_mul_left _ this
        _ = 60 * cfg.Δ * cfg.P q := by ring
        _ ≤ cfg.D q := hDq_ge_nat
    calc F.length ≤ cfg.Δ * (X.card / cfg.D q) := h1
      _ ≤ cfg.D q * (X.card / cfg.D q) := Nat.mul_le_mul_right _ h2
      _ ≤ X.card := Nat.mul_div_le X.card (cfg.D q)
  refine ⟨hF_le_X, hFmem, isConductanceExpanderOn_append_inside hK_cond, ?_, ?_⟩
  · intro v hv
    rw [degIn_append_inside]
    exact hdegK_pos v hv
  · intro R hRsub hRcond hRdeg hRvol
    have hRvolK : (K.volIn X (X \ R) : ℝ) ≤ 60 / ρ * (F.length : ℝ) := by
      rwa [volIn_append_inside] at hRvol
    have hcard_le_vol : ((X \ R).card : ℝ) ≤ (K.volIn X (X \ R) : ℝ) := by
      exact_mod_cast card_le_volIn fun v hv => hdegK_pos v (Finset.sdiff_subset hv)
    have hFlen_r : (F.length : ℝ) ≤ (cfg.Δ : ℝ) * ((X.card / cfg.D q : ℕ) : ℝ) := by
      have hnat : F.length ≤ cfg.Δ * (X.card / cfg.D q) :=
        le_trans hFlen (Nat.mul_le_mul_right _ hcalls_len)
      exact_mod_cast hnat
    have hDq_pos : (0 : ℝ) < cfg.D q := Nat.cast_pos.mpr (hcfg.hD_pos hq1 hqr)
    have hz_le : ((X.card / cfg.D q : ℕ) : ℝ) ≤ (X.card : ℝ) / (cfg.D q : ℝ) := by
      rw [le_div_iff₀ hDq_pos]
      exact_mod_cast Nat.div_mul_le_self X.card (cfg.D q)
    have hDq_ge : (60 : ℝ) * (cfg.Δ : ℝ) * (cfg.P q : ℝ) ≤ (cfg.D q : ℝ) := by
      exact_mod_cast hDq_ge_nat
    have hrem_le : ((X \ R).card : ℝ) ≤ (X.card : ℝ) / 12 := by
      have h60 : 60 / ρ = 5 * (cfg.P q : ℝ) := by
        dsimp only [ρ]; field_simp; ring
      have h1 : ((X \ R).card : ℝ) ≤ 5 * (cfg.P q : ℝ) * (F.length : ℝ) := by
        rw [h60] at hRvolK
        exact le_trans hcard_le_vol hRvolK
      have h2 : 5 * (cfg.P q : ℝ) * (F.length : ℝ) ≤
          5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) := by
        have h3 : (F.length : ℝ) ≤ (cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ)) :=
          le_trans hFlen_r (mul_le_mul_of_nonneg_left hz_le (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h3 : 5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) ≤
          (X.card : ℝ) / 12 := by
        rw [show 5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) =
          (5 * (cfg.P q : ℝ) * (cfg.Δ : ℝ) * (X.card : ℝ)) / (cfg.D q : ℝ) by ring]
        rw [div_le_div_iff₀ hDq_pos (by norm_num : (0 : ℝ) < 12)]
        nlinarith
      exact le_trans h1 (le_trans h2 h3)
    have hrem_nat : 12 * (X \ R).card ≤ X.card := by
      have : (12 : ℝ) * ((X \ R).card : ℝ) ≤ (X.card : ℝ) := by linarith
      exact_mod_cast this
    have hRcard : 11 * X.card ≤ 12 * R.card := by
      have hadd : (X \ R).card + R.card = X.card := Finset.card_sdiff_add_card_eq_card hRsub
      omega
    have hφ_le : 1 / (cfg.P q : ℝ) ≤ ρ / 9 := by
      dsimp only [ρ]
      rw [div_div, div_le_div_iff₀ hPq_pos (by positivity)]
      linarith
    have hRcondG : G.IsConductanceExpanderOn R (1 / (cfg.P q : ℝ)) :=
      isConductanceExpanderOn_mono hφ_le (isConductanceExpanderOn_mk_inside hRsub hRcond)
    have hRdegG : ∀ u ∈ R, 1 ≤ G.degIn R u := fun u hu => by
      have := hRdeg u hu
      rwa [degIn_mk_inside hRsub] at this
    exact ⟨hRsub, hRcard, isExpansionExpanderOn_of_conductance_minDeg (by positivity) hRcondG hRdegG⟩

/-! ## 4. Workspace and Word-Bound Lemmas -/

lemma rfCcap_twelve (Pq : ℕ) : rfCcap 12 Pq = Pq + 2 := by
  unfold rfCcap
  omega

lemma rfHParam_twelve_le {k mH mF L Pq : ℕ} (hL4 : 4 ≤ L) (hkL : k < 2 ^ L)
    (hmH : mH ≤ 512 * L * k) (hmF : mF ≤ k) :
    rfHParam mH mF 12 Pq ≤ 20 * (Pq + 2) * L + 2 := by
  have hlog_le : Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1 ≤ 5 * L := by
    have hlt : 2 * (mH + 2 * mF) + 1 < 2 ^ (5 * L) := by
      have hLpow : L < 2 ^ L := Nat.lt_two_pow_self
      have h1 : 2 * (mH + 2 * mF) + 1 ≤ 2 * (512 * L * k + 2 * k) + 1 := by omega
      have h2 : 2 * (512 * L * k + 2 * k) + 1 ≤ 2048 * L * 2 ^ L := by
        have h2k : 2 * k ≤ 2 * L * k := by
          calc 2 * k = 2 * 1 * k := by ring
            _ ≤ 2 * L * k := Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 (by omega))
        have h514 : 512 * L * k + 2 * L * k = 514 * L * k := by ring
        have h1028 : 2 * (514 * L * k) + 1 ≤ 1028 * L * 2 ^ L := by
          have h1' : 1 ≤ 1028 * L := by omega
          have h2' : 1028 * L * k + 1028 * L ≤ 1028 * L * 2 ^ L := by
            calc 1028 * L * k + 1028 * L = 1028 * L * (k + 1) := by ring
              _ ≤ 1028 * L * 2 ^ L := Nat.mul_le_mul_left _ hkL
          have hmul : 2 * (514 * L * k) = 1028 * L * k := by ring
          omega
        have h2048 : 1028 * L * 2 ^ L ≤ 2048 * L * 2 ^ L :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right L (by decide))
        omega
      have h3 : 2048 * L * 2 ^ L < 2 ^ (5 * L) := by
        calc 2048 * L * 2 ^ L
            < 2048 * 2 ^ L * 2 ^ L :=
              Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_left hLpow (by decide)) (Nat.two_pow_pos L)
          _ = 2 ^ (2 * L + 11) := by
              rw [show (2048 : ℕ) = 2 ^ 11 by decide, ← pow_add, ← pow_add]; congr 1; omega
          _ ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hlog : Nat.log 2 (2 * (mH + 2 * mF) + 1) < 5 * L :=
      Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  unfold rfHParam
  rw [rfCcap_twelve]
  have hmul : 4 * (Pq + 2) * (Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1) ≤
      4 * (Pq + 2) * (5 * L) := Nat.mul_le_mul_left _ hlog_le
  have hring : 4 * (Pq + 2) * (5 * L) = 20 * (Pq + 2) * L := by ring
  omega

lemma removeFakeWorkSpace_le_stepDSpace {k mG mH mF L Pq : ℕ} (hmH_le : mH ≤ mG)
    (hL4 : 4 ≤ L) (hkL : k < 2 ^ L) (hmH : mH ≤ 512 * L * k) (hmF : mF ≤ k) :
    2 + 2 * mG + removeFakeWorkSpace k mH mF (rfHParam mH mF 12 Pq) ≤
      stepDSpace k mG mF L Pq := by
  have hH := rfHParam_twelve_le (Pq := Pq) hL4 hkL hmH hmF
  have h40 : 2 * (20 * (Pq + 2) * L) = 40 * (Pq + 2) * L := by ring
  unfold removeFakeWorkSpace pruneWorkSpace stepDSpace
  omega

lemma removeFakeWordBound_of_stepD {w n k mG mH mF L Pq xAddr fAddr locAddr outAddr h : ℕ}
    (hmH_le : mH ≤ mG) (hL4 : 4 ≤ L) (hkL : k < 2 ^ L) (hmH : mH ≤ 512 * L * k) (hmF : mF ≤ k)
    (hx : xAddr + k ≤ h) (hf : fAddr + 2 * mF ≤ h) (hloc : locAddr + n ≤ h)
    (hout : outAddr + 2 + k ≤ h) (hw : h + stepDWordSpace k mG mF L Pq < 2 ^ w) :
    RemoveFakeWordBound w n k mH mF 12 Pq xAddr (h + 2) fAddr h locAddr (outAddr + 2)
      (h + 2 + 2 * mG) := by
  have hH := rfHParam_twelve_le (Pq := Pq) hL4 hkL hmH hmF
  have h40 : 2 * (20 * (Pq + 2) * L) = 40 * (Pq + 2) * L := by ring
  have hws := removeFakeWorkSpace_le_stepDSpace (Pq := Pq) hmH_le hL4 hkL hmH hmF
  have hds : stepDSpace k mG mF L Pq + 2 ≤ stepDWordSpace k mG mF L Pq := by
    unfold stepDSpace stepDWordSpace; omega
  unfold RemoveFakeWordBound PruneWordBound rfPruneWorkAddr
  rw [rfCcap_twelve]
  have h8 : 8 * (Pq + 2) * (mH + 2 * mF) ≤ 8 * (Pq + 2) * (mG + 2 * mF) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpr1 :
      h + 2 + 2 * mG + 4 * (k + mF) + 6 * (mH + 2 * mF) + 3 +
        pruneWorkSpace (k + mF) (mH + 2 * mF) (rfHParam mH mF 12 Pq) + 2 < 2 ^ w := by
    unfold removeFakeWorkSpace at hws
    omega
  have hpr2 :
      8 * (Pq + 2) * (mH + 2 * mF) + 4 * (Pq + 2) + 2 * (k + mF) + 2 * (mH + 2 * mF) +
        rfHParam mH mF 12 Pq + 16 < 2 ^ w := by
    unfold stepDWordSpace at hw
    omega
  have hmax :
      max (h + 2 + 2 * mG + 4 * (k + mF) + 6 * (mH + 2 * mF) + 3 +
            pruneWorkSpace (k + mF) (mH + 2 * mF) (rfHParam mH mF 12 Pq) + 2)
          (8 * (Pq + 2) * (mH + 2 * mF) + 4 * (Pq + 2) + 2 * (k + mF) + 2 * (mH + 2 * mF) +
            rfHParam mH mF 12 Pq + 16) < 2 ^ w :=
    max_lt hpr1 hpr2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hmax⟩
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega
  · unfold stepDWordSpace at hw; omega

/-! ## 5. `NoRand` and Contract Proof for `stepDProc` -/

lemma stepDProc_noRand (idx : CoreIdx) : (stepDProc idx).NoRand := by
  simp [stepDProc, seqStmts, Stmt.NoRand]

theorem stepDProc_meetsContract (w : ℕ) (p : Program) (idx : CoreIdx)
    (hself : p.procs[idx.stepD]? = some (stepDProc idx))
    (hfe : MeetsContract w p idx.filterEdgesIn (filterEdgesInContract w))
    (hrf : MeetsContract w p idx.removeFake (removeFakeContract w)) :
    MeetsContract w p idx.stepD (stepDContract w) := by
  refine meetsContract_of_runs hself fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gAddr, k, xAddr, mF, fAddr, L, Pq, locAddr, outAddr, h, G, X, F,
    hargs, hG, hGvalid, hX, hXrange, hF, hFmF, hmFk, hL4, hkL, hP12, hmH_bd, hFmem,
    hKcond, hKdeg, hloc0, hg_h, hx_h, hf_h, hloc_h, hout_h,
    hd_lg, hd_lx, hd_lf, hd_lo, hd_ox, hd_of, hz, hw⟩
  subst hargs
  have h1 : 40 ≤ stepDWordSpace k G.m mF L Pq := by unfold stepDWordSpace; omega
  have h2w : 40 < 2 ^ w := by omega
  have hG_m : mem (gAddr + 1) = G.m := graphAt_m hG
  have hG_e : EdgesAt mem (gAddr + 2) G.edges := fun j hj => by
    refine ⟨graphAt_edge_fst hG hj, ?_⟩
    rw [show gAddr + 2 + 2 * j + 1 = gAddr + 3 + 2 * j by omega]
    exact graphAt_edge_snd hG hj
  have hverts_len : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX.1.symm
  have hverts_nd : (X.sort (· ≤ ·)).Nodup := X.sort_nodup (· ≤ ·)
  have hverts_lt : ∀ u ∈ X.sort (· ≤ ·), u < G.n := fun u hu => by
    rw [Finset.mem_sort] at hu
    exact Finset.mem_range.mp (hXrange hu)
  have hverts_fin : (X.sort (· ≤ ·)).toFinset = X := X.sort_toFinset (· ≤ ·)
  have hG_rd : readGraph mem gAddr = G := readGraph_eq_of_graphAt hG
  have hX_rd : (readList mem xAddr k).toFinset = X := by
    have hrl := readList_eq_of_listAt hX.2
    rw [hverts_len] at hrl
    rw [hrl, hverts_fin]
  refine runs_start_le ?_
  dsimp only [stepDProc, seqStmts]
  -- Step 1: reg 10 := load (gAddr + 1) = G.m
  refine runs_seq_assign_le (v := G.m)
    (hG_m ▸ Expr.eval_load (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))) ?_
  -- Step 2: reg 11 := gAddr + 2
  refine runs_seq_assign_le (v := gAddr + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  -- Step 3: mem[h] := 12
  refine runs_seq_store_le (x := h) (v := 12)
    (Expr.eval_reg_of_eq (by simp [startState]))
    (Expr.eval_const (by omega)) ?_
  -- Step 4: mem[h + 1] := Pq
  refine runs_seq_store_le (x := h + 1) (v := Pq)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp [startState])) ?_
  -- Step 5: reg 12 := h + 2
  refine runs_seq_assign_le (v := h + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  -- Step 6: call `idx.filterEdgesIn`
  set mem2 : ℕ → ℕ := Function.update (Function.update mem h 12) (h + 1) Pq
  have hmem2_eq : ∀ a, a ≠ h → a ≠ h + 1 → mem2 a = mem a := fun a h1' h2' => by
    simp [mem2, h1', h2']
  have hmem2_edges : EdgesAt mem2 (gAddr + 2) G.edges := by
    intro j hj
    have hlt1 : gAddr + 2 + 2 * j < h := by unfold Graph.m at hg_h; omega
    have hlt2 : gAddr + 2 + 2 * j + 1 < h := by unfold Graph.m at hg_h; omega
    rw [hmem2_eq _ (by omega) (by omega), hmem2_eq _ (by omega) (by omega)]
    exact hG_e j hj
  have hmem2_X : VertsAt mem2 xAddr k X := by
    refine ⟨hX.1, fun i hi => ?_⟩
    rw [hmem2_eq _ (by omega) (by omega)]
    exact hX.2 i hi
  have hmem2_loc0 : ∀ u < G.n, mem2 (locAddr + u) = 0 := fun u hu => by
    rw [hmem2_eq _ (by omega) (by omega)]
    exact hloc0 u hu
  have hfe_pre : (filterEdgesInContract w).pre [G.m, gAddr + 2, k, xAddr, locAddr, h + 2] mem2 := by
    refine ⟨G.n, G.m, gAddr + 2, k, xAddr, locAddr, h + 2, G.edges, X,
      rfl, rfl, hGvalid, hmem2_edges, hmem2_X, hXrange, hmem2_loc0, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold stepDWordSpace at hw <;> omega
    · refine ⟨?_, hd_lx, Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      rcases hd_lg with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hfe_words : ∀ v ∈ [G.m, gAddr + 2, k, xAddr, locAddr, h + 2], v < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    unfold stepDWordSpace at hw; omega
  refine runs_seq_call_le (vs := [G.m, gAddr + 2, k, xAddr, locAddr, h + 2])
    hfe (by simp [evalArgs, Expr.eval, startState]) hfe_words hfe_pre ?_
  intro mH mem3 pos3 hfe_post
  change (filterEdgesInContract w).post [G.m, gAddr + 2, k, xAddr, locAddr, h + 2] mem2 mH mem3 at hfe_post
  have hreadE : readEdges mem2 (gAddr + 2) G.m = G.edges := readEdges_eq_of_edgesAt hmem2_edges
  have hreadX : (readList mem2 xAddr k).toFinset = X := by
    have hrl := readList_eq_of_listAt hmem2_X.2
    rw [hverts_len] at hrl
    rw [hrl, hverts_fin]
  have hH_eq : (Graph.mk 0 (readEdges mem2 (gAddr + 2) G.m)).inside
      (readList mem2 xAddr k).toFinset = G.inside X := by
    rw [hreadE, hreadX]; rfl
  simp only [filterEdgesInContract, List.getD_cons_zero, List.getD_cons_succ, hH_eq] at hfe_post
  obtain ⟨hmH_eq, hmH_le, hmem3_H, hmem3_frame⟩ := hfe_post
  -- Step 7: reg 14 := (h + 2) + 2 * G.m
  refine runs_seq_assign_le (v := h + 2 + 2 * G.m)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp [startState]))
        (by unfold stepDWordSpace at hw; omega))
      (by unfold stepDWordSpace at hw; omega)) ?_
  -- Step 8: reg 15 := outAddr + 2
  refine runs_seq_assign_le (v := outAddr + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega))
      (by unfold stepDWordSpace at hw; omega)) ?_
  -- Step 9: call `idx.removeFake`
  have hmem3_eq_mem : ∀ a < h, mem3 a = mem a := fun a ha => by
    rw [hmem3_frame a (Or.inl (by omega)), hmem2_eq a (by omega) (by omega)]
  have hmem3_rho0 : mem3 h = 12 := by
    rw [hmem3_frame h (Or.inl (by omega))]
    simp [mem2]
  have hmem3_rho1 : mem3 (h + 1) = Pq := by
    rw [hmem3_frame (h + 1) (Or.inl (by omega))]
    simp [mem2]
  have hmem3_X : ListAt mem3 xAddr (X.sort (· ≤ ·)) := fun i hi => by
    rw [hmem3_eq_mem _ (by omega)]
    exact hX.2 i hi
  have hmem3_F : EdgesAt mem3 fAddr F := fun j hj => by
    rw [hmem3_eq_mem _ (by omega), hmem3_eq_mem _ (by omega)]
    exact hF j hj
  have hH_mem : ∀ e ∈ G.inside X,
      e.1 ∈ (X.sort (· ≤ ·)).toFinset ∧ e.2 ∈ (X.sort (· ≤ ·)).toFinset := by
    rw [hverts_fin]; intro e he; exact (mem_inside_iff.mp he).2
  have hF_mem' : ∀ e ∈ F,
      e.1 ∈ (X.sort (· ≤ ·)).toFinset ∧ e.2 ∈ (X.sort (· ≤ ·)).toFinset := by
    rw [hverts_fin]; exact hFmem
  have hmH_512 : mH ≤ 512 * L * k := hmH_eq ▸ hmH_bd
  have hrf_wb : RemoveFakeWordBound w G.n k mH mF 12 Pq xAddr (h + 2) fAddr h locAddr
      (outAddr + 2) (h + 2 + 2 * G.m) :=
    removeFakeWordBound_of_stepD hmH_le hL4 hkL hmH_512 hmFk hx_h hf_h hloc_h hout_h hw
  have hrf_disj : RemoveFakeDisjoint G.n k mH mF (rfHParam mH mF 12 Pq)
      xAddr (h + 2) fAddr h locAddr (outAddr + 2) (h + 2 + 2 * G.m) := by
    unfold RemoveFakeDisjoint
    have hd_lo' : DisjointRange locAddr G.n (outAddr + 2) k := by
      rcases hd_lo with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hd_ox' : DisjointRange (outAddr + 2) k xAddr k := by
      rcases hd_ox with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hd_of' : DisjointRange (outAddr + 2) k fAddr (2 * mF) := by
      rcases hd_of with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine ⟨hd_lx, Or.inl (by omega), hd_lf, Or.inl (by omega), hd_lo', Or.inl (by omega),
      hd_ox', Or.inl (by omega), hd_of', Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hrf_pre : (removeFakeContract w).pre
      [k, xAddr, mH, h + 2, mF, fAddr, h, locAddr, outAddr + 2, h + 2 + 2 * G.m] mem3 := by
    refine ⟨G.n, k, xAddr, mH, h + 2, mF, fAddr, h, locAddr, outAddr + 2, h + 2 + 2 * G.m,
      12, Pq, X.sort (· ≤ ·), G.inside X, F,
      rfl, hverts_len, hverts_nd, hverts_lt, hmH_eq.symm, hFmF, hH_mem, hF_mem',
      hmem3_X, hmem3_H, hmem3_F, hmem3_rho0, hmem3_rho1, by omega, hP12, ?_, ?_, hrf_wb, hrf_disj⟩
    · rw [hverts_fin]; exact hKcond
    · rw [hverts_fin]; exact hKdeg
  have hrf_words : ∀ v ∈ [k, xAddr, mH, h + 2, mF, fAddr, h, locAddr, outAddr + 2, h + 2 + 2 * G.m],
      v < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    unfold stepDWordSpace at hw; omega
  refine runs_seq_call_le
    (vs := [k, xAddr, mH, h + 2, mF, fAddr, h, locAddr, outAddr + 2, h + 2 + 2 * G.m])
    hrf (by simp [evalArgs, Expr.eval, startState]) hrf_words hrf_pre ?_
  intro cardR mem4 pos4 hrf_post
  have hrf_rl : readList mem3 xAddr k = X.sort (· ≤ ·) := by
    have hrl := readList_eq_of_listAt hmem3_X
    rwa [hverts_len] at hrl
  have hrf_rH : readEdges mem3 (h + 2) mH = G.inside X := by
    have hre := readEdges_eq_of_edgesAt hmem3_H
    rwa [← hmH_eq] at hre
  have hrf_rF : readEdges mem3 fAddr mF = F := by
    have hre := readEdges_eq_of_edgesAt hmem3_F
    rwa [hFmF] at hre
  simp only [removeFakeContract, List.getD_cons_zero, List.getD_cons_succ,
    hrf_rl, hverts_fin, hrf_rH, hrf_rF, hmem3_rho0, hmem3_rho1] at hrf_post
  obtain ⟨hcardR_le, hR_nd, hR_sub, hR_spec, hR_loc0, hR_frame⟩ := hrf_post
  -- Step 10: mem[outAddr] := 1
  refine runs_seq_store_le (x := outAddr) (v := 1)
    (Expr.eval_reg_of_eq (by simp [startState]))
    (Expr.eval_const (by omega)) ?_
  -- Step 11: mem[outAddr + 1] := cardR
  refine runs_seq_store_le (x := outAddr + 1) (v := cardR)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega))
      (by unfold stepDWordSpace at hw; omega))
    (Expr.eval_reg_of_eq (by simp [startState])) ?_
  -- Step 12: reg 17 := h + stepDSpace k G.m mF L Pq
  set hNew := h + stepDSpace k G.m mF L Pq
  have h16k : 16 * k < 2 ^ w := by unfold stepDWordSpace at hw; omega
  have h9m : 9 * G.m < 2 ^ w := by unfold stepDWordSpace at hw; omega
  have h30f : 30 * mF < 2 ^ w := by unfold stepDWordSpace at hw; omega
  have hP2 : Pq + 2 < 2 ^ w := by unfold stepDWordSpace at hw; omega
  have h40P2 : 40 * (Pq + 2) < 2 ^ w := by
    have hmul : 40 * (Pq + 2) ≤ 40 * (Pq + 2) * L :=
      le_mul_of_one_le_right (Nat.zero_le _) (by omega)
    unfold stepDWordSpace at hw; omega
  have h40P2L : 40 * (Pq + 2) * L < 2 ^ w := by unfold stepDWordSpace at hw; omega
  have hNew_lt : hNew < 2 ^ w := by
    unfold hNew stepDSpace; unfold stepDWordSpace at hw; omega
  have hNew_eq : h + ((16 * k + 9 * G.m) + 30 * mF + (40 * (Pq + 2) * L + 11)) = hNew := by
    unfold hNew stepDSpace; omega
  refine runs_seq_assign_le (v := hNew) (by
    rw [← hNew_eq]
    exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_add
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [startState])) h16k)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [startState])) h9m)
            (by unfold stepDWordSpace at hw; omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [startState])) h30f)
          (by unfold stepDWordSpace at hw; omega))
        (Expr.eval_add
          (Expr.eval_mul
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
                (Expr.eval_const (by omega)) hP2) h40P2)
            (Expr.eval_reg_of_eq (by simp [startState])) h40P2L)
          (Expr.eval_const (by omega))
          (by unfold stepDWordSpace at hw; omega))
        (by unfold stepDWordSpace at hw; omega))
      (by omega)) ?_
  -- Step 13: ret reg 17
  refine ⟨.returned hNew, _, 2,
    runs_ret_iff.mpr ⟨hNew, Expr.eval_reg_of_eq (by simp), rfl, rfl, by simp [Expr.size]⟩, ?_, ?_⟩
  · -- Postcondition
    dsimp only [stepDContract, Outcome.value]
    intro gAddr' k' xAddr' mF' fAddr' L' Pq' locAddr' outAddr' h' G' X' F'
      hargs' hG' _ hX' _ hF' hFmF' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs'
    have hG_eq : G = G' := by
      rw [← graphAt_iff_readGraph.mp hG, graphAt_iff_readGraph.mp hG']
    rcases hG_eq with rfl
    have hX_eq : X = X' := by
      have h1' := readList_eq_of_listAt hX.2
      have h2' := readList_eq_of_listAt hX'.2
      rw [Finset.length_sort, ← hX.1] at h1'
      rw [Finset.length_sort, ← hX'.1] at h2'
      have hs : X.sort (· ≤ ·) = X'.sort (· ≤ ·) := h1'.symm.trans h2'
      simpa [Finset.sort_toFinset] using congrArg List.toFinset hs
    rcases hX_eq with rfl
    have hF_eq : F = F' := by
      have h1' := readEdges_eq_of_edgesAt hF
      have h2' := readEdges_eq_of_edgesAt hF'
      rw [hFmF] at h1'; rw [hFmF'] at h2'
      exact h1'.symm.trans h2'
    rcases hF_eq with rfl
    set mem6 := Function.update (Function.update mem4 outAddr 1) (outAddr + 1) cardR
    set R_list := readList mem4 (outAddr + 2) cardR
    set R := R_list.toFinset
    have hcardR_eq : R.card = cardR := by
      rw [List.toFinset_card_of_nodup hR_nd, readList_length]
    have hR_spec' := hR_spec G.n hverts_lt
    have hread_mem6 : readList mem6 (outAddr + 2) R.card = R_list := by
      rw [hcardR_eq]
      apply List.ext_getElem (by simp [R_list, readList])
      intro i hi _
      simp only [readList_length] at hi
      rw [readList_getElem _ _ _ _ hi, readList_getElem _ _ _ _ hi]
      simp [mem6, show outAddr + 2 + i ≠ outAddr + 1 by omega,
        show outAddr + 2 + i ≠ outAddr by omega]
    have hcoreOut : CoreOutAt mem6 outAddr (.expander R) := by
      refine ⟨by simp [mem6], R_list, hR_nd, rfl, by simp [mem6, R_list, readList_length], ?_⟩
      rw [← hread_mem6]
      exact listAt_readList mem6 (outAddr + 2) R.card
    have hws_le := removeFakeWorkSpace_le_stepDSpace (Pq := Pq) hmH_le hL4 hkL hmH_512 hmFk
    have hZero6 : ZeroFrom mem6 hNew := by
      intro a ha
      have ha_ne1 : a ≠ outAddr + 1 := by unfold hNew stepDSpace at ha; omega
      have ha_ne0 : a ≠ outAddr := by unfold hNew stepDSpace at ha; omega
      have ha_not_loc : ∀ u ∈ X.sort (· ≤ ·), a ≠ locAddr + u := fun u hu => by
        have hlt := hverts_lt u hu; unfold hNew stepDSpace at ha; omega
      have ha_out : a < outAddr + 2 ∨ outAddr + 2 + k ≤ a :=
        Or.inr (by unfold hNew stepDSpace at ha; omega)
      have ha_ws : a < h + 2 + 2 * G.m ∨
          h + 2 + 2 * G.m + removeFakeWorkSpace k mH mF (rfHParam mH mF 12 Pq) ≤ a :=
        Or.inr (by unfold hNew at ha; omega)
      simp only [mem6, Function.update_of_ne ha_ne1, Function.update_of_ne ha_ne0]
      rw [hR_frame a ha_not_loc ha_out ha_ws]
      rw [hmem3_frame a (Or.inr (by unfold hNew stepDSpace at ha; omega))]
      rw [hmem2_eq a (by unfold hNew stepDSpace at ha; omega)
        (by unfold hNew stepDSpace at ha; omega)]
      exact hz a (by unfold hNew stepDSpace at ha; omega)
    have hloc6 : ∀ u < G.n, mem6 (locAddr + u) = 0 := fun u hu => by
      have hne1 : locAddr + u ≠ outAddr + 1 := by
        rcases hd_lo with h' | h' <;> omega
      have hne0 : locAddr + u ≠ outAddr := by
        rcases hd_lo with h' | h' <;> omega
      simp only [mem6, Function.update_of_ne hne1, Function.update_of_ne hne0]
      by_cases huX : u ∈ X.sort (· ≤ ·)
      · exact hR_loc0 u huX
      · have hnot : ∀ v ∈ X.sort (· ≤ ·), locAddr + u ≠ locAddr + v := fun v hv heq =>
          huX ((Nat.add_left_cancel heq).symm ▸ hv)
        have hout' : locAddr + u < outAddr + 2 ∨ outAddr + 2 + k ≤ locAddr + u := by
          rcases hd_lo with h' | h'
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        have hws' : locAddr + u < h + 2 + 2 * G.m ∨
            h + 2 + 2 * G.m + removeFakeWorkSpace k mH mF (rfHParam mH mF 12 Pq) ≤ locAddr + u :=
          Or.inl (by omega)
        rw [hR_frame _ hnot hout' hws', hmem3_eq_mem _ (by omega)]
        exact hloc0 u hu
    have hframe6 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem6 a = mem a := by
      intro a ha hout_a
      have hne1 : a ≠ outAddr + 1 := by omega
      have hne0 : a ≠ outAddr := by omega
      simp only [mem6, Function.update_of_ne hne1, Function.update_of_ne hne0]
      by_cases hloc_a : ∃ u ∈ X.sort (· ≤ ·), a = locAddr + u
      · obtain ⟨u, hu, rfl⟩ := hloc_a
        rw [hR_loc0 u hu, hloc0 u (hverts_lt u hu)]
      · push Not at hloc_a
        have hout' : a < outAddr + 2 ∨ outAddr + 2 + k ≤ a := by omega
        have hws' : a < h + 2 + 2 * G.m ∨
            h + 2 + 2 * G.m + removeFakeWorkSpace k mH mF (rfHParam mH mF 12 Pq) ≤ a :=
          Or.inl (by omega)
        rw [hR_frame a hloc_a hout' hws', hmem3_eq_mem a ha]
    exact ⟨R, hcoreOut, hR_sub, hR_spec'.1, hR_spec'.2.1, hR_spec'.2.2.2,
      rfl, hZero6, hloc6, hframe6⟩
  · -- Cost bound
    have harg1 : argsSize [.reg 10, .reg 11, .reg 1, .reg 2, .reg 7, .reg 12] = 6 := by decide
    have harg2 : argsSize [.reg 1, .reg 2, .reg 13, .reg 12, .reg 3, .reg 4, .reg 9, .reg 7,
        .reg 15, .reg 14] = 10 := by decide
    simp only [stepDContract, stepDCost, filterEdgesInContract, removeFakeContract,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size, harg1, harg2,
      hG_rd, hX_rd, ← hmH_eq, hmem3_rho0, hmem3_rho1]
    omega

end MinCostFlow.ExpanderDecomp
