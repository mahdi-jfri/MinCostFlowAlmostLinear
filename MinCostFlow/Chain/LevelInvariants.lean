module

public import MinCostFlow.Chain.LevelConnected
public import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algorithm 1 Level Graph Invariants: `hComp_bound` and `hB_bound`

Bridges Algorithm 1's dynamic level-chain invariant (`ChainInv`) to the per-level instance
hypotheses `hComp_bound` and `hB_bound` of `MinCostFlow.SparseCore.SparseCoreInstanceHyps`,
using connectedness and level-`d` size bounds from `MinCostFlow.Chain.LevelConnected`:

1. **Connectedness & `hComp_bound` (`c_n = 1`)** (imported from `LevelConnected.lean`).
2. **Length & bucket bounds (`hB_bound`)**:
   * `chainInv_length_bounds`: if input edge lengths at level `0` satisfy
     `Real.exp (-Ψ_ℓ) ≤ st.ℓ e ≤ Real.exp Ψ_ℓ`, then at every level `0 ≤ i ≤ P.d`,
     `Real.exp (-Ψ_ℓ) ≤ st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp Ψ_ℓ * σ_cap ^ i`.
   * `initCompLSF_bucket_bound` & `chainInv_bucket_bound_all_levels`: at every level `i < P.d`,
     branch `j < P.k`, and component `C ∈ components (st.G i)`, the initial bucket quotient
     graph `(initTildeState (cs₀.compSt C)).C` uses at most
     `⌈(2 * Ψ_ℓ + P.d * log (max 2 σ_cap)) / log 2⌉ + 2` distinct power-of-two length buckets.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore

section LengthAndBucketBounds

/-- Under `ChainInv`, if level-`0` lengths satisfy `exp(-Ψ_ℓ) ≤ st.ℓ e ≤ exp Ψ_ℓ` (`0 ≤ Ψ_ℓ`),
then at every level `i ≤ P.d`, every edge `e ∈ (st.G i).E` satisfies
`exp(-Ψ_ℓ) ≤ chainLen st.ℓ i e ≤ exp Ψ_ℓ * (max 2 (TP.σ P.k N₀)) ^ i`. -/
theorem chainInv_length_bounds {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {Ψ_ℓ : ℝ} (hℓ_bounds : ∀ e ∈ (st.G 0).E, Real.exp (-Ψ_ℓ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp Ψ_ℓ) :
    let σ_cap := max (2 : ℝ) (TP.σ P.k N₀)
    ∀ i ≤ P.d, ∀ e ∈ (st.G i).E,
      Real.exp (-Ψ_ℓ) ≤ st.toTreeChain.chainLen st.ℓ i e ∧
      st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp Ψ_ℓ * σ_cap ^ i := by
  intro σ_cap i hi e he
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  have hσ_le_cap : TP.σ P.k (st.G 0).n ≤ σ_cap := by
    have hn : (st.G 0).n ≤ N₀ := hInv.hG0n
    exact le_trans (hTP.2.1 _ _ _ _ le_rfl hn) (le_max_right _ _)
  have hσ_cap_pos : 0 ≤ σ_cap := by positivity
  induction i generalizing e with
  | zero =>
    simpa [TreeChain.chainLen] using hℓ_bounds e he
  | succ i ih =>
    have hi_lt : i < P.d := hi
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    rw [hInv.hGSucc i hi_lt] at he
    have heCore : e ∈ (coreGraph (st.G i) (T.lsfs (st.scState i) (st.bran i))).E :=
      hBi.2.1.2.1 he
    have heGi : e ∈ (st.G i).E := (Finset.mem_sdiff.mp heCore).1
    have hPrev := ih (Nat.le_of_lt hi_lt) e heGi
    have hℓ_pos : ∀ f ∈ (st.G i).E, 0 ≤ st.toTreeChain.chainLen st.ℓ i f := fun f hf =>
      (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.1 f hf |>.le
    have hstr1 : 1 ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e :=
      le_trans (one_le_stretch hBi.1.2.1.2.2.2.2 hℓ_pos heGi) (hBi.1.2.2.2 e heGi).1
    have hw_le : (T.lsfs (st.scState i) (st.bran i)).wstr e ≤ σ_cap :=
      le_trans (hBi.1.2.2.2 e heGi).2 hσ_le_cap
    have hcl_eq : st.toTreeChain.chainLen st.ℓ (i + 1) e =
        (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e := by
      simp [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hi_lt]
    rw [hcl_eq]
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ st.toTreeChain.chainLen st.ℓ i e := le_trans (Real.exp_pos _).le hPrev.1
      calc Real.exp (-Ψ_ℓ) = 1 * Real.exp (-Ψ_ℓ) := by ring
        _ ≤ 1 * st.toTreeChain.chainLen st.ℓ i e := mul_le_mul_of_nonneg_left hPrev.1 zero_le_one
        _ ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e :=
            mul_le_mul_of_nonneg_right hstr1 h0
    · have h0 : 0 ≤ st.toTreeChain.chainLen st.ℓ i e := le_trans (Real.exp_pos _).le hPrev.1
      calc (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e
          ≤ σ_cap * (Real.exp Ψ_ℓ * σ_cap ^ i) := mul_le_mul hw_le hPrev.2 h0 hσ_cap_pos
        _ = Real.exp Ψ_ℓ * σ_cap ^ (i + 1) := by rw [pow_succ]; ring

/-- Any edge set whose edge values lie in `[exp (-A), exp B]` (`0 ≤ A`, `0 ≤ B`) maps via
`bucketOf` into at most `⌈(A + B) / log 2⌉ + 2` distinct power-of-two length buckets. -/
lemma bucketOf_image_card_le_of_bounds {Eset : Finset ℕ} {f : ℕ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ e ∈ Eset, Real.exp (-A) ≤ f e ∧ f e ≤ Real.exp B) :
    (Eset.image fun e => bucketOf (f e)).card ≤ Nat.ceil ((A + B) / Real.log 2) + 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let blo : ℤ := Int.floor ((-A) / Real.log 2)
  let bhi : ℤ := Int.floor (B / Real.log 2)
  have hsub : (Eset.image fun e => bucketOf (f e)) ⊆ Finset.Icc blo bhi := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨e, he, rfl⟩
    have hfe := hf e he
    have hpos : 0 < f e := lt_of_lt_of_le (Real.exp_pos _) hfe.1
    have hlog_lo : -A ≤ Real.log (f e) := by
      calc -A = Real.log (Real.exp (-A)) := (Real.log_exp _).symm
        _ ≤ Real.log (f e) := Real.log_le_log (Real.exp_pos _) hfe.1
    have hlog_hi : Real.log (f e) ≤ B := by
      calc Real.log (f e) ≤ Real.log (Real.exp B) := Real.log_le_log hpos hfe.2
        _ = B := Real.log_exp _
    rw [Finset.mem_Icc]
    refine ⟨Int.floor_mono (div_le_div_of_nonneg_right hlog_lo hlog2.le),
      Int.floor_mono (div_le_div_of_nonneg_right hlog_hi hlog2.le)⟩
  have hcard : (Finset.Icc blo bhi).card = (bhi + 1 - blo).toNat := by simp
  have hab_nn : 0 ≤ (A + B) / Real.log 2 := div_nonneg (add_nonneg hA hB) hlog2.le
  have hblo_lt : (-A) / Real.log 2 - 1 < (blo : ℝ) := by
    have := Int.lt_floor_add_one ((-A) / Real.log 2)
    linarith
  have hbhi_le : (bhi : ℝ) ≤ B / Real.log 2 := Int.floor_le _
  have hdiff_lt : (bhi : ℝ) + 1 - (blo : ℝ) < (A + B) / Real.log 2 + 2 := by
    have : (A + B) / Real.log 2 = B / Real.log 2 - (-A) / Real.log 2 := by ring
    linarith
  have hceil_ge : (A + B) / Real.log 2 ≤ (Nat.ceil ((A + B) / Real.log 2) : ℝ) :=
    Nat.le_ceil _
  have hcast_lt : ((bhi + 1 - blo : ℤ) : ℝ) < ((Nat.ceil ((A + B) / Real.log 2) + 2 : ℕ) : ℝ) := by
    have hc : ((bhi + 1 - blo : ℤ) : ℝ) = (bhi : ℝ) + 1 - (blo : ℝ) := by push_cast; ring
    have hc2 : ((Nat.ceil ((A + B) / Real.log 2) + 2 : ℕ) : ℝ) =
        (Nat.ceil ((A + B) / Real.log 2) : ℝ) + 2 := by push_cast; ring
    rw [hc, hc2]
    linarith
  have hint_lt : bhi + 1 - blo < (Nat.ceil ((A + B) / Real.log 2) + 2 : ℤ) := by
    exact_mod_cast hcast_lt
  have htoNat : (bhi + 1 - blo).toNat ≤ Nat.ceil ((A + B) / Real.log 2) + 2 := by
    omega
  exact le_trans (Finset.card_le_card hsub) (by rw [hcard]; exact htoNat)

/-- For any valid graph `G` with lengths in `[exp (-A), exp B]` (`0 ≤ A`, `0 ≤ B`) and LSST
stretch parameter `mwuK0 C_lsst * k * log^6(G.n + 2) ≤ σ_cap` (`2 ≤ σ_cap`), every component
`C ∈ components G` and branch `j < k` uses at most `⌈(A + B + log σ_cap) / log 2⌉ + 2`
buckets in `(initTildeState (cs₀.compSt C)).C`. -/
theorem initCompLSF_bucket_bound
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k : ℕ} (hk : 1 ≤ k) {G : MGraph} (hG : G.IsValid) {ℓ : ℕ → ℝ} {A B σ_cap : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ_ge : 2 ≤ σ_cap)
    (hσ : mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6 ≤ σ_cap)
    (hℓ : ∀ e ∈ G.E, Real.exp (-A) ≤ ℓ e ∧ ℓ e ≤ Real.exp B)
    (j : ℕ) (hj : j < k) (C : Finset ℕ) (hC : C ∈ components G) :
    let cs₀ := initCompLSF oracle C_lsst G ℓ k j
    ((initTildeState (cs₀.compSt C)).C.E.image
      fun e => bucketOf (coreLen cs₀.lsf ℓ e)).card ≤
      Nat.ceil ((A + B + Real.log σ_cap) / Real.log 2) + 2 := by
  intro cs₀
  by_cases hV : G.V.Nonempty
  · have hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e := fun e he => lt_of_lt_of_le (Real.exp_pos _) (hℓ e he).1
    let D0 : DynamicInstance := { G := fun _ => G, U := fun _ => [], ℓ := fun _ => ℓ, g := fun _ => fun _ => 0 }
    have hD0_val : D0.IsValid 0 := fun _ ht1 _ => by omega
    have hD0_len : LengthsStable D0 0 := fun _ ht1 _ => by omega
    let dummySp : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut :=
      fun _ _ _ _ => ⟨emptyGraph, fun _ => [], 0⟩
    have hLSF := sparseCore_lsf_guarantees oracle C_lsst 1 dummySp hLSST
      k 0 hk D0 hG hD0_val (fun _ _ => hℓ_pos) hD0_len
    have hHolds : cs₀.lsf.Holds G ℓ (mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6) := by
      have hAt := (hLSF.1 0 le_rfl j hj).1
      simpa [sparseCoreTool, sparseCoreToolWith, SparseCoreTool.run, SparseCoreTool.runAt,
        hV, D0, cs₀, initTreeCore, dummySp] using hAt
    have hI₀ := compLSFInv_init oracle hLSST hG hV hℓ_pos hk j
    have hσ_pos : 0 < σ_cap := by linarith
    have hB2 : 0 ≤ B + Real.log σ_cap := add_nonneg hB (Real.log_nonneg (by linarith))
    have hsub := bucketOf_image_card_le_of_bounds (A := A) (B := B + Real.log σ_cap) hA hB2
      (Eset := (initTildeState (cs₀.compSt C)).C.E)
      (f := fun e => coreLen cs₀.lsf ℓ e) ?_
    · rwa [show A + (B + Real.log σ_cap) = A + B + Real.log σ_cap by ring] at hsub
    intro e he
    have heComp : e ∈ (cs₀.compSt C).G.E := (Finset.mem_sdiff.mp he).1
    have heG : e ∈ G.E := (hI₀.hCE_sub C hC) heComp
    have hℓ_nn : ∀ f ∈ G.E, 0 ≤ ℓ f := fun f hf => (hℓ_pos f hf).le
    have hw1 : 1 ≤ cs₀.lsf.wstr e :=
      le_trans (one_le_stretch hHolds.2.1.2.2.2.2 hℓ_nn heG) (hHolds.2.2.2 e heG).1
    have hw_le : cs₀.lsf.wstr e ≤ σ_cap := le_trans (hHolds.2.2.2 e heG).2 hσ
    have hℓe := hℓ e heG
    have hℓe_nn : 0 ≤ ℓ e := (hℓ_pos e heG).le
    refine ⟨?_, ?_⟩
    · change Real.exp (-A) ≤ cs₀.lsf.wstr e * ℓ e
      calc Real.exp (-A) = 1 * Real.exp (-A) := by ring
        _ ≤ 1 * ℓ e := mul_le_mul_of_nonneg_left hℓe.1 zero_le_one
        _ ≤ cs₀.lsf.wstr e * ℓ e := mul_le_mul_of_nonneg_right hw1 hℓe_nn
    · change cs₀.lsf.wstr e * ℓ e ≤ Real.exp (B + Real.log σ_cap)
      rw [Real.exp_add, Real.exp_log hσ_pos]
      calc cs₀.lsf.wstr e * ℓ e ≤ σ_cap * Real.exp B :=
            mul_le_mul hw_le hℓe.2 hℓe_nn hσ_pos.le
        _ = Real.exp B * σ_cap := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hV
    exfalso
    simp [components, hV] at hC

/-- Under `ChainInv` for `TP := sparseCoreParams E` (`E.C_lsst = C_lsst`) and level-`0` length
bounds `exp(-Ψ_ℓ) ≤ st.ℓ e ≤ exp Ψ_ℓ` (`0 ≤ Ψ_ℓ`), **every** level `i < P.d`, branch
`j < P.k`, and component `C ∈ components (st.G i)` satisfies `hB_bound` with explicit bound
`⌈(2 * Ψ_ℓ + P.d * log (max 2 (TP.σ P.k N₀))) / log 2⌉ + 2`. -/
theorem chainInv_bucket_bound_all_levels
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {Ψ_ℓ : ℝ} (hΨℓ : 0 ≤ Ψ_ℓ)
    (hℓ_bounds : ∀ e ∈ (st.G 0).E, Real.exp (-Ψ_ℓ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp Ψ_ℓ) :
    let σ_cap := max (2 : ℝ) (TP.σ P.k N₀)
    ∀ i < P.d, ∀ j < P.k,
      let cs₀ := initCompLSF oracle C_lsst (st.G i) (st.toTreeChain.chainLen st.ℓ i) P.k j
      ∀ C ∈ components (st.G i),
        ((initTildeState (cs₀.compSt C)).C.E.image
          fun e => bucketOf (coreLen cs₀.lsf (st.toTreeChain.chainLen st.ℓ i) e)).card ≤
          Nat.ceil ((2 * Ψ_ℓ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2) + 2 := by
  intro σ_cap i hi j hj cs₀ C hC
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  have hGi_val := (hLvl i (Nat.le_of_lt hi)).1
  have hGi_V := (hLvl i (Nat.le_of_lt hi)).2.1
  have hGin : (st.G i).n ≤ N₀ := le_trans (Finset.card_le_card hGi_V) hInv.hG0n
  have hlen := chainInv_length_bounds hTP hT hγM₀ hγk hInv hℓ_bounds i (Nat.le_of_lt hi)
  have hσ_cap_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hσ_cap_pos : 0 < σ_cap := by linarith
  have hlog_σ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hσ_mwu : mwuK0 C_lsst * (P.k : ℝ) * (Real.log (((st.G i).n : ℝ) + 2)) ^ 6 ≤ σ_cap := by
    have hn_r : ((st.G i).n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hGin
    have hlog_le : Real.log (((st.G i).n : ℝ) + 2) ≤ Real.log ((N₀ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith [hn_r])
    have hlog_nn : 0 ≤ Real.log (((st.G i).n : ℝ) + 2) := by
      linarith [half_lt_log_add_two (st.G i).n]
    have hK_pos : 0 ≤ mwuK0 C_lsst := (mwuK0_pos C_lsst).le
    have h1 : mwuK0 C_lsst * (P.k : ℝ) * (Real.log (((st.G i).n : ℝ) + 2)) ^ 6 ≤
        mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 := by gcongr
    have h2 : mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 ≤ TP.σ P.k N₀ := by
      rw [hσ_eq]; exact le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_max_right _ _))
  have hB_nn : 0 ≤ Ψ_ℓ + (i : ℝ) * Real.log σ_cap := by positivity
  have hlen' : ∀ e ∈ (st.G i).E,
      Real.exp (-Ψ_ℓ) ≤ st.toTreeChain.chainLen st.ℓ i e ∧
      st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp (Ψ_ℓ + (i : ℝ) * Real.log σ_cap) := by
    intro e he
    refine ⟨(hlen e he).1, ?_⟩
    calc st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp Ψ_ℓ * σ_cap ^ i := (hlen e he).2
      _ = Real.exp Ψ_ℓ * Real.exp ((i : ℝ) * Real.log σ_cap) := by
          conv_lhs => rw [← Real.exp_log hσ_cap_pos, ← Real.exp_nat_mul]
      _ = Real.exp (Ψ_ℓ + (i : ℝ) * Real.log σ_cap) := (Real.exp_add _ _).symm
  have hbd := initCompLSF_bucket_bound oracle hLSST P.hk hGi_val hΨℓ hB_nn hσ_cap_ge2
    hσ_mwu hlen' j hj C hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi1_le_d : (i + 1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hi
  have hnum_le : (Ψ_ℓ + (Ψ_ℓ + (i : ℝ) * Real.log σ_cap) + Real.log σ_cap) / Real.log 2 ≤
      (2 * Ψ_ℓ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 := by
    refine div_le_div_of_nonneg_right ?_ hlog2.le
    nlinarith [hi1_le_d, hlog_σ_nn]
  exact le_trans hbd (Nat.add_le_add_right (Nat.ceil_mono hnum_le) 2)

end LengthAndBucketBounds

end MinCostFlow.Chain
