module

public import MinCostFlow.LastLevelProgram.RepresentativeGraph
public import MinCostFlow.Machine.WideWord.LSSTProgramBase
public import MinCostFlow.LastLevelProgram.QueryMemory
public import MinCostFlow.LastLevelProgram.SelectedTraversal
public import MinCostFlow.LastLevelProgram.GuestFormatSetup
public import MinCostFlow.LastLevelProgram.CollectionFormat
public import MinCostFlow.LastLevelProgram.StagedRebuildProof
public import MinCostFlow.LastLevelProgram.StagedAppendModel
import Mathlib.Analysis.Complex.ExponentialBounds
public import MinCostFlow.MinRatio.LastLevelContract
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Charging the tree calls in a last-level rebuild

Theorem 2.2 (page 7) charges for both vertices and edges. In the
representative graph every vertex is an endpoint of a retained edge.
This lets Definition 5.8 (pages 19–20) pay for all the tree calls from
the edge-based iteration budget.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord SparseCore
open scoped BigOperators

/-- The multiplier for the Theorem 2.2 calls, given their limb count. -/
noncomputable def lastLevelLSSTMultiplier (Q : Program) (c : ℕ) (K : ℝ)
    (H : MGraph) (L : ℕ) : ℕ :=
  48000 * ⌈lsstOverheadFactor Q c K H.n H.m L⌉₊

/-- A single cited tree call is linear in the original edge count
with the explicit Theorem 2.2 overhead. -/
theorem representativeGuestCallCost_le (Q : Program) (c : ℕ) (K : ℝ)
    (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) (L cost : ℕ) :
    let H := representativeGraph G ℓ
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) *
      lsstOverheadFactor Q c K H.n H.m L →
    cost ≤ lastLevelLSSTMultiplier Q c K H L * (G.m+1) := by
  intro H hbound
  let B := ⌈lsstOverheadFactor Q c K H.n H.m L⌉₊
  have hn := representativeGraph_n_le_twice_m G ℓ
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hsize : H.m + H.n + 1 ≤ 3 * (G.m + 1) := by
    change H.n ≤ 2 * H.m at hn
    omega
  have hceil : lsstOverheadFactor Q c K H.n H.m L ≤ (B : ℝ) := Nat.le_ceil _
  have hsize' : ((H.m + H.n + 1 : ℕ) : ℝ) ≤ 3 * ((G.m : ℝ) + 1) := by exact_mod_cast hsize
  have hcast : (cost : ℝ) ≤ ((48000 * B * (G.m + 1) : ℕ) : ℝ) := by
    calc
      _ ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) * B :=
        hbound.trans (mul_le_mul_of_nonneg_left hceil (by positivity))
      _ ≤ 16000 * (3 * ((G.m : ℝ) + 1)) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize' (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  exact_mod_cast hcast

/-- Charge the sum of the actual tree-call costs to the last-level model
budget. Each call uses the cost bound of `theorem_2_2_program_linear`. -/
theorem lastLevelLSSTCosts_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) (L : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (cost : ℕ → ℕ)
    (hc : let H := representativeGraph G ℓ
      ∀ j < lastMWUK H, (cost j : ℝ) ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) *
        lsstOverheadFactor Q c K H.n H.m L) :
    let H := representativeGraph G ℓ
    ∑ j ∈ Finset.range (lastMWUK H), cost j ≤
      lastLevelLSSTMultiplier Q c K H L * (fixedPointLastLevelTool oracle C |>.cost G) := by
  intro H
  have hcall (j : ℕ) (hj : j < lastMWUK H) :=
    representativeGuestCallCost_le Q c K G hG ℓ L (cost j) (hc j hj)
  have hk : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  calc
    _ ≤ ∑ _ ∈ Finset.range (lastMWUK H), lastLevelLSSTMultiplier Q c K H L * (G.m + 1) :=
      Finset.sum_le_sum fun j hj => hcall j (Finset.mem_range.mp hj)
    _ = lastLevelLSSTMultiplier Q c K H L * (lastMWUK H * (G.m + 1)) := by
      simp [Finset.sum_const, Nat.mul_left_comm]
    _ ≤ _ := by
      simp only [fixedPointLastLevelTool, hnl, ↓reduceIte, hk]
      exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/-- Charge the copying and relocation overhead across all rounds.
The extra copy visits only the four packed input arrays. -/
theorem lastLevelRelocatedCosts_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) (L : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (guest host : ℕ → ℕ)
    (hc : let H := representativeGraph G ℓ
      ∀ j < lastMWUK H, (guest j : ℝ) ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) *
        lsstOverheadFactor Q c K H.n H.m L)
    (hhost : let H := representativeGraph G ℓ
      ∀ j < lastMWUK H, host j ≤ 17 * (queryOriginals H L + 1) +
        ((Program.mk (lsstModule Q 0 1)).regBound + 6) * guest j + 1) :
    let H := representativeGraph G ℓ
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    ∑ j ∈ Finset.range (lastMWUK H), host j ≤
      (34 * (L + 1) + 18 + (R + 6) * lastLevelLSSTMultiplier Q c K H L) *
        (fixedPointLastLevelTool oracle C |>.cost G) := by
  intro H R
  let budget := (fixedPointLastLevelTool oracle C).cost G
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hcopy : 17 * (queryOriginals H L + 1) + 1 ≤ (34 * (L + 1) + 18) * (G.m + 1) := by
    unfold queryOriginals queryWeights queryLengths
    calc
      _ = 34 * (L + 1) * H.m + 18 := by ring
      _ ≤ 34 * (L + 1) * G.m + 18 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hm) _
      _ ≤ _ := by
        calc
          _ ≤ 34 * (L + 1) * (G.m + 1) + 18 * (G.m + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_succ _))
              (by simp)
          _ = _ := (Nat.add_mul _ _ _).symm
  have hk : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  have hbudget : lastMWUK H * (G.m + 1) ≤ budget := by
    simp only [budget, fixedPointLastLevelTool, hnl, ↓reduceIte, hk]
    exact Nat.le_add_right _ _
  calc
    _ ≤ ∑ j ∈ Finset.range (lastMWUK H),
          ((34 * (L + 1) + 18) * (G.m + 1) + (R + 6) * guest j) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hhost j (Finset.mem_range.mp hj)
      rw [Nat.add_right_comm] at h
      exact h.trans (Nat.add_le_add_right hcopy _)
    _ = (34 * (L + 1) + 18) * (lastMWUK H * (G.m + 1)) +
          (R + 6) * ∑ j ∈ Finset.range (lastMWUK H), guest j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum _ _ (R + 6)]
      simp [Nat.mul_left_comm]
    _ ≤ _ := by
      conv_rhs => rw [Nat.add_mul, Nat.mul_assoc (R + 6)]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hbudget)
        (Nat.mul_le_mul_left _ (lastLevelLSSTCosts_le Q c K C oracle G hG ℓ L hnl guest hc))

/-- Charge selection, deduplication, and the numeric update across all
rounds. The two forwarding lists have total expression cost at most
`forward` per round. -/
theorem lastLevelSelectedRoundCosts_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) (L levels forward : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (guest relocated round : ℕ → ℕ) :
    let H := representativeGraph G ℓ
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    let F := 110 * L + 126 * levels + edgeStretchCost L + narrowWeightCost L + 988
    (∀ j < lastMWUK H, (guest j : ℝ) ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) *
      lsstOverheadFactor Q c K H.n H.m L) →
    (∀ j < lastMWUK H, relocated j ≤ 17 * (queryOriginals H L + 1) + (R + 6) * guest j + 1) →
    (∀ j < lastMWUK H, round j ≤ relocated j + F * (H.m + 1) + 40 * H.n + forward + 57) →
    ∑ j ∈ Finset.range (lastMWUK H), round j ≤
      (34 * (L + 1) + 18 + (R + 6) * lastLevelLSSTMultiplier Q c K H L +
        F + 137 + forward) * (fixedPointLastLevelTool oracle C).cost G := by
  intro H R F hguest hrelocated hround
  let budget := (fixedPointLastLevelTool oracle C).cost G
  let B := 34 * (L + 1) + 18 + (R + 6) * lastLevelLSSTMultiplier Q c K H L
  have hcost : ∑ j ∈ Finset.range (lastMWUK H), relocated j ≤ B * budget :=
    lastLevelRelocatedCosts_le Q c K C oracle G hG ℓ L hnl guest relocated hguest hrelocated
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hn : H.n ≤ 2 * H.m := representativeGraph_n_le_twice_m G ℓ
  have hk : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  have hbudget : lastMWUK H * (G.m + 1) ≤ budget := by
    simp only [budget, fixedPointLastLevelTool, hnl, ↓reduceIte, hk]
    exact Nat.le_add_right _ _
  have hextra : F * (H.m + 1) + 40 * H.n + forward + 57 ≤
      (F + 137 + forward) * (G.m + 1) := by
    conv_rhs => rw [Nat.add_mul, Nat.add_mul, Nat.mul_add 137, Nat.mul_one]
    have hf : F * (H.m + 1) ≤ F * (G.m + 1) := Nat.mul_le_mul_left F (Nat.succ_le_succ hm)
    have hfor : forward ≤ forward * (G.m + 1) := Nat.le_mul_of_pos_right forward (Nat.succ_pos G.m)
    omega
  calc
    _ ≤ ∑ j ∈ Finset.range (lastMWUK H),
        (relocated j + (F + 137 + forward) * (G.m + 1)) :=
      Finset.sum_le_sum fun j hj => (hround j (Finset.mem_range.mp hj)).trans
        (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hextra (relocated j))
    _ = (∑ j ∈ Finset.range (lastMWUK H), relocated j) +
        (F + 137 + forward) * (lastMWUK H * (G.m + 1)) := by
      simp [Finset.sum_add_distrib, Nat.mul_left_comm]
    _ ≤ B * budget + (F + 137 + forward) * budget :=
      Nat.add_le_add hcost (Nat.mul_le_mul_left _ hbudget)
    _ = _ := by change _ = (B + F + 137 + forward) * budget; ring

/-- The multiplier for the linked round calls, with their concrete
register forwarding cost. -/
noncomputable def selectedRoundMultiplier (Q : Program) (c : ℕ) (K : ℝ)
    (H : MGraph) (L levels : ℕ) : ℕ :=
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  34 * (L + 1) + 18 + (R + 6) * lastLevelLSSTMultiplier Q c K H L +
    (110 * L + 126 * levels + edgeStretchCost L + narrowWeightCost L + 988) +
    137 + (2 * R + 12)

/-- The concrete round budget has the multiplicative form of the
last-level rebuild contract. -/
theorem lastLevelLinkedRoundCosts_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) (L levels : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (guest relocated round : ℕ → ℕ) :
    let H := representativeGraph G ℓ
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    let F := 110 * L + 126 * levels + edgeStretchCost L + narrowWeightCost L + 988
    (∀ j < lastMWUK H, (guest j : ℝ) ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) *
      lsstOverheadFactor Q c K H.n H.m L) →
    (∀ j < lastMWUK H, relocated j ≤ 17 * (queryOriginals H L + 1) + (R + 6) * guest j + 1) →
    (∀ j < lastMWUK H, round j ≤ relocated j + F * (H.m + 1) + 40 * H.n + (2 * R + 12) + 57) →
    ∑ j ∈ Finset.range (lastMWUK H), round j ≤
      selectedRoundMultiplier Q c K H L levels * ((fixedPointLastLevelTool oracle C).cost G + 1) := by
  intro H R F hg hr hround
  exact (lastLevelSelectedRoundCosts_le Q c K C oracle G hG ℓ L levels (2 * R + 12)
    hnl guest relocated round hg hr hround).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- The simulator's word-width bound grows with the edge count and the
guest limb count. Its vertex-count argument does not enter the bound. -/
theorem lastLevel_simWord_le {c n n' m m' L L' : ℕ}
    (hm : m ≤ m') (hL : L ≤ L') :
    w'Max c n m L 1 ≤ w'Max c n' m' L' 1 := by
  have hk : kWidthOf m L ≤ kWidthOf m' L' := (kWidthOf_mono hm).trans (by
    dsimp only [kWidthOf]
    omega)
  have hlog : Nat.log 2 (6+16*m) ≤ Nat.log 2 (6+16*m') :=
    Nat.log_mono_right (by omega)
  unfold w'Max
  exact Nat.mul_le_mul_left _ (by omega)

/-- Padding the edge count and guest width also bounds the simulation width. -/
theorem lastLevel_simLimbs_le {c n n' m m' L L' : ℕ}
    (hm : m ≤ m') (hL : L ≤ L') :
    lsstLSimMin c n m L 1 ≤ lsstLSimMin c n' m' L' 1 := by
  have hk : kWidthOf m L ≤ kWidthOf m' L' := (kWidthOf_mono hm).trans (by
    dsimp only [kWidthOf]
    omega)
  exact max_le_max hk (lastLevel_simWord_le hm hL)

/-- On a graph with at least two vertices, padding the sizes and width
can only increase the explicit Theorem 2.2 overhead. -/
theorem lastLevel_lsstOverhead_le (Q : Program) (c : ℕ) (K : ℝ)
    {n n' m m' L L' : ℕ} (hn₂ : 2 ≤ n) (hn : n ≤ n') (hm : m ≤ m') (hL : L ≤ L') :
    lsstOverheadFactor Q c K n m L ≤ lsstOverheadFactor Q c K n' m' L' := by
  let S := lsstLSimMin c n m L 1
  let S' := lsstLSimMin c n' m' L' 1
  have hS : S ≤ S' := lastLevel_simLimbs_le hm hL
  have hW := lastLevel_simWord_le (c := c) (n := n) (n' := n') hm hL
  have hs : (S : ℝ) ≤ S' := by exact_mod_cast hS
  have hw : (w'Max c n m L 1 : ℝ) ≤ w'Max c n' m' L' 1 := by exact_mod_cast hW
  have hnp : (0 : ℝ) < (n : ℝ)+2 := by positivity
  have hn' : (n : ℝ)+2 ≤ (n' : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hn 2
  have hlog := Real.log_le_log hnp hn'
  have hfour : (4 : ℝ) ≤ (n : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hn₂ 2
  have hone : 1 ≤ Real.log ((n : ℝ)+2) := by
    have hl : Real.log (4 : ℝ) ≤ Real.log ((n : ℝ)+2) := Real.log_le_log (by norm_num) hfour
    rw [show (4 : ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)] at hl
    linarith [Real.log_two_gt_d9]
  have hloglog := Real.log_le_log (by linarith : 0 < Real.log ((n : ℝ)+2)) hlog
  have hpow : (2 : ℕ)^S ≤ 2^S' := Nat.pow_le_pow_right (by decide) hS
  have hp : (((2^S : ℕ) : ℝ)+2) ≤ (((2^S' : ℕ) : ℝ)+2) := by
    exact_mod_cast Nat.add_le_add_right hpow 2
  have hpLog := Real.log_le_log (by positivity : 0 < (((2^S : ℕ) : ℝ)+2)) hp
  have hlogW : 0 ≤ Real.log (((2^S : ℕ) : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (2^S : ℕ); linarith)
  have hlogW' := Real.log_le_log (by linarith : 0 < Real.log (((2^S : ℕ) : ℝ)+2)+2)
    (add_le_add hpLog (le_refl (2 : ℝ)))
  have hlogs : Cited.logLogFactor n + Cited.weightFactor n (2^S) ≤
      Cited.logLogFactor n' + Cited.weightFactor n' (2^S') := by
    unfold Cited.logLogFactor Cited.weightFactor
    exact add_le_add (mul_le_mul hlog hloglog (Real.log_nonneg hone) (by linarith))
      (mul_le_mul hlog hlogW' (Real.log_nonneg (by linarith)) (by linarith))
  have hlogs0 : 0 ≤ Cited.logLogFactor n + Cited.weightFactor n (2^S) := by
    unfold Cited.logLogFactor Cited.weightFactor
    exact add_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hone))
      (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
  unfold lsstOverheadFactor
  change (S : ℝ)^2 + (simScale Q : ℝ)*(S : ℝ)*(w'Max c n m L 1 : ℝ)*
        (max K 1*(Cited.logLogFactor n+Cited.weightFactor n (2^S))+1) ≤ _
  apply add_le_add (pow_le_pow_left₀ (by positivity) hs 2)
  have hK : 0 ≤ max K 1 := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right ..)
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hw (by positivity) (by positivity))
    (add_le_add (mul_le_mul_of_nonneg_left hlogs hK) (le_refl (1 : ℝ)))
    (by have := mul_nonneg hK hlogs0; linarith) (by positivity)

/-- The tree-call multiplier can use the caller graph sizes and any
upper bound on the actual guest width. -/
theorem lastLevelLSSTMultiplier_le (Q : Program) (c : ℕ) (K : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (hG : G.IsValid) {L B : ℕ} (hLB : L ≤ B)
    (hm : 0 < (representativeGraph G ℓ).m) :
    lastLevelLSSTMultiplier Q c K (representativeGraph G ℓ) L ≤
      48000*⌈lsstOverheadFactor Q c K G.n G.m B⌉₊ := by
  have hsub := representativeGraph_subgraph hG ℓ
  exact Nat.mul_le_mul_left _ (Nat.ceil_mono (lastLevel_lsstOverhead_le Q c K
    (representativeGraph_two_le_n G ℓ hm) (Finset.card_le_card hsub.1)
    (Finset.card_le_card hsub.2.1) hLB))

/-- The converted selector factor uses only the caller's limb count
and original graph sizes, for a fixed cited program and scale constant. -/
noncomputable def representativeSelectorMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  let B := representativeGuestWidthBound D L m
  let sim := lsstLSimMin c n m B 1
  let heap := (2+2*B)*m+3*n+2
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  (114*B+71)+(R+6)*(48000*⌈lsstOverheadFactor Q c K n m B⌉₊)+
    guestWorkspaceCost Q D n sim+40*paddedGuestWidth Q D n m sim heap+
    argsSize paddedWidthArgs+argsSize stagedGuestWeightsArgs+
    argsSize (stagedConvertedTreeArgs R)+stagedConvertedGuestCursor.size+100

/-- Charge a canonical converted selector call to the original edge count. -/
theorem representativeSelectorCost_le (w : ℕ) (Q : Program) (c D : ℕ) (K : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (L N cost : ℕ) (hG : G.IsValid)
    (hN : N ≤ representativeGuestWidthBound D L G.m) :
    let H := representativeGraph G ℓ
    let sim := lsstLSimMin c H.n H.m N 1
    0 < H.m →
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) * lsstOverheadFactor Q c K H.n H.m N →
    convertedTreeSelectorCost w Q D H N sim cost ≤
      representativeSelectorMultiplier Q c D K L G.n G.m*(G.m+1) := by
  intro H sim hm hcost
  have hsub := representativeGraph_subgraph hG ℓ
  have hn : H.n ≤ G.n := Finset.card_le_card hsub.1
  have hm' : H.m ≤ G.m := Finset.card_le_card hsub.2.1
  have hrun := (representativeGuestCallCost_le Q c K G hG ℓ N cost hcost).trans
    (Nat.mul_le_mul_right (G.m+1) (lastLevelLSSTMultiplier_le Q c K G ℓ hG hN hm))
  unfold representativeSelectorMultiplier
  exact convertedTreeSelectorCost_le w Q D H N sim cost G.n G.m _ _ _
    hn hm' hN (lastLevel_simLimbs_le hm' hN) hrun

/-- The numeric rebuild pays for the scans, arithmetic, and lifting
table from one linear budget in the original edge count. -/
theorem stagedRebuildNumericCost_le (H : MGraph) (N levels L J m : ℕ)
    (hN : N ≤ L) (hlevels : levels ≤ J) (hm : H.m ≤ m) (hn : H.n ≤ m+1) :
    stagedRebuildNumericCost H N levels ≤
      (stagedNumericFactor L J+108*L+1000)*(m+1) := by
  have hf : stagedNumericFactor N levels ≤ stagedNumericFactor L J := by
    unfold stagedNumericFactor edgeStretchCost stretchFromLengthCost narrowWeightCost
      widenWeightCost weightUpdateCost
    dsimp only
    gcongr
  have ha : argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
    argsSize stagedNumericArgs +
    argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 19) ++
      [.reg 19]) ≤ 600 := by decide
  have hm' : H.m ≤ m+1 := hm.trans (Nat.le_succ m)
  have hp := Nat.mul_le_mul hf (Nat.succ_le_succ hm)
  have hx := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 17 hN) 75) hm'
  have hy := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 35 hN) 60) hm'
  have hz := Nat.mul_le_mul (Nat.mul_le_mul_left 56 hN) (Nat.succ_le_succ (Nat.zero_le m))
  change stagedNumericFactor N levels*(H.m+1) ≤ stagedNumericFactor L J*(m+1) at hp
  change 56*N*1 ≤ 56*L*(m+1) at hz
  have hv := Nat.mul_le_mul_left 112 hn
  unfold stagedRebuildNumericCost
  simp only [Nat.add_mul, Nat.mul_one] at hx hy hz ⊢
  have hconst : 751 ≤ 753*(m+1) :=
    (by decide : 751 ≤ 753).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos m))
  have hsplit : 75*(m+1)+60*(m+1)+112*(m+1)+753*(m+1) = 1000*(m+1) := by ring
  have hlimbs : 17*L*(m+1)+35*L*(m+1)+56*L*(m+1) = 108*L*(m+1) := by ring
  omega

/-- The staged round factor for a fixed cited program and runtime scale. -/
noncomputable def representativeStagedRoundMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativeSelectorMultiplier Q c D K L n m+
    stagedNumericFactor L (n+2).size+198*L+17*representativeGuestWidthBound D L m+4000

/-- Combine numeric, selector, and publication budgets for one staged
round of Definition 5.8 (pages 19–20). -/
theorem representativeStagedRoundCost_le (w : ℕ) (Q : Program) (c D : ℕ) (K : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (L N levels cost : ℕ)
    (hG : G.IsValid) (hn : G.n ≤ G.m+1)
    (hN : N ≤ representativeGuestWidthBound D L G.m) (hlevels : levels ≤ (G.n+2).size) :
    let H := representativeGraph G ℓ
    let sim := lsstLSimMin c H.n H.m N 1
    0 < H.m →
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) * lsstOverheadFactor Q c K H.n H.m N →
    argsSize convertedGuestCallArgs+convertedTreeSelectorCost w Q D H N sim cost+
      argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+
      40*H.n+stagedRebuildNumericCost H L levels+18+
      (argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9)+
      stagedAppendModelCost G L (lastMWUK H)+21+17*queryWeights H N+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤
    representativeStagedRoundMultiplier Q c D K L G.n G.m*(G.m+1) := by
  intro H sim hm hcost
  let B := representativeGuestWidthBound D L G.m
  unfold representativeStagedRoundMultiplier
  have hsub := representativeGraph_subgraph hG ℓ
  have hm' : H.m ≤ G.m := Finset.card_le_card hsub.2.1
  have hn' : H.n ≤ G.m+1 := (Finset.card_le_card hsub.1).trans hn
  have hsel := representativeSelectorCost_le w Q c D K G ℓ L N cost hG hN hm hcost
  have hnum := stagedRebuildNumericCost_le H L levels L _ G.m le_rfl hlevels hm' hn'
  have happ := stagedAppendModelCost_model_le G ℓ L hG hn
  have hgraph := Nat.mul_le_mul_left 40 hn'
  have hweights : 17*queryWeights H N ≤ (17*B+34)*(G.m+1) := by
    have hs := Nat.mul_le_mul hm' hN
    change H.m*N ≤ G.m*B at hs
    unfold queryWeights queryLengths
    have he : (17*B+34)*(G.m+1) = 17*(G.m*B)+17*B+34*(G.m+1) := by ring
    rw [he]
    omega
  have ha : argsSize convertedGuestCallArgs+
      argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+
      (argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9)+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤ 600 := by decide
  have hc : 653 ≤ 726*(G.m+1) :=
    (by decide : 653 ≤ 726).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  dsimp only [H,sim,B] at *
  simp only [Nat.add_mul] at hnum happ hweights ⊢
  have hl : 108*L*(G.m+1)+90*L*(G.m+1) = 198*L*(G.m+1) := by ring
  omega

/-- Sum the staged budgets over the exact model round count. -/
theorem representativeStagedRoundCosts_le (Q : Program) (c D : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ) (budget : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let factor := representativeStagedRoundMultiplier Q c D K L G.n G.m
    (∀ j < lastMWUK H, budget j ≤ factor*(G.m+1)) →
    ∑ j ∈ Finset.range (lastMWUK H), budget j ≤
      factor*((fixedPointLastLevelTool oracle C).cost G+1) := by
  intro H factor hround
  have hcount : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  calc
    _ ≤ ∑ _ ∈ Finset.range (lastMWUK H), factor*(G.m+1) :=
      Finset.sum_le_sum fun j hj => hround j (Finset.mem_range.mp hj)
    _ = factor*(lastMWUK H*(G.m+1)) := by
      simp [Finset.sum_const, Nat.mul_left_comm]
    _ ≤ _ := by
      simp only [fixedPointLastLevelTool, hnl, ↓reduceIte, hcount]
      exact Nat.mul_le_mul_left _ (by omega)

/-- The controller also charges its round call arguments and loop
guards. Seven additional steps cover termination. -/
theorem representativeControllerLoopCost_le (Q : Program) (c D : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ) (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let factor := representativeStagedRoundMultiplier Q c D K L G.n G.m
    let forward := argsSize publishedRoundArgs+10
    (forward+factor*(G.m+1))*lastMWUK H+7 ≤
      (factor+forward+7)*((fixedPointLastLevelTool oracle C).cost G+1) := by
  intro H factor forward
  have hk : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  let model := (fixedPointLastLevelTool oracle C).cost G+1
  have hmodel : lastMWUK H*(G.m+1) ≤ model := by
    simp only [model, fixedPointLastLevelTool, hnl, ↓reduceIte, hk]
    omega
  have hcount : lastMWUK H ≤ model :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos G.m)).trans hmodel
  have hfactor := Nat.mul_le_mul_left factor hmodel
  have hforward := Nat.mul_le_mul_left forward hcount
  have hseven : 7 ≤ 7*model := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ (factor+forward+7)*model
  calc
    _ = factor*(lastMWUK H*(G.m+1))+forward*lastMWUK H+7 := by ring
    _ ≤ factor*model+forward*model+7*model := Nat.add_le_add (Nat.add_le_add hfactor hforward) hseven
    _ = _ := by ring

/-- The linked tree, traversal and update cost factor, evaluated using
the original graph and the caller's format. -/
noncomputable def representativeLinkedRoundMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  let B := representativeGuestWidthBound D L m
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  34*(B+1)+18+(R+6)*(48000*⌈lsstOverheadFactor Q c K n m B⌉₊) +
    (110*B+126*(n+2).size+edgeStretchCost B+narrowWeightCost B+988)+
    137+(2*R+12)

/-- The linked round accounting can use the caller format and original
graph sizes whenever the installed traversal uses at most `(n+2).size` levels. -/
theorem selectedRoundMultiplier_le (Q : Program) (c : ℕ) (K C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (L N levels : ℕ) (hG : G.IsValid)
    (hm : 0 < (representativeGraph G ℓ).m)
    (hN : N ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m)
    (hlevels : levels ≤ (G.n+2).size) :
    selectedRoundMultiplier Q c K (representativeGraph G ℓ) N levels ≤
      representativeLinkedRoundMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m := by
  let B := representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m
  have htree := lastLevelLSSTMultiplier_le Q c K G ℓ hG hN hm
  have hs : edgeStretchCost N ≤ edgeStretchCost B := by
    unfold edgeStretchCost stretchFromLengthCost
    gcongr
  have hw : narrowWeightCost N ≤ narrowWeightCost B := by
    unfold narrowWeightCost widenWeightCost weightUpdateCost
    dsimp only
    gcongr
  unfold representativeLinkedRoundMultiplier selectedRoundMultiplier
  dsimp only
  change _ ≤ 34*(B+1)+18+(_+6)*(48000*⌈lsstOverheadFactor Q c K G.n G.m B⌉₊)+
    (110*B+126*(G.n+2).size+edgeStretchCost B+narrowWeightCost B+988)+137+_
  gcongr

/-- The original-name sorting and stretch-index scan are paid once.
The model's round count absorbs the scan over the representative edges. -/
theorem runtimeStretchTablesCost_le (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (hG : G.IsValid)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    200*G.m*(Nat.log 2 (G.m+1)+1)+17*G.m+100+
      argsSize (stretchIndexKeyArgs 134 136 133)+argsSize (stretchIndexKeyArgs 100 138 73)+
      57*(G.m+H.m)+(26*H.m+48)*G.m ≤
    (200*(Nat.log 2 (G.m+1)+1)+500)*((fixedPointLastLevelTool oracle C).cost G+1) := by
  intro H
  let budget := (fixedPointLastLevelTool oracle C).cost G+1
  have hn : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hp : 0 < H.m := Nat.pos_of_ne_zero (fun h =>
    (representativeGraph_m_eq_zero_iff G ℓ).mp h hnl)
  have hk : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m, representativeGraph_m]
  have hmodel : H.m*(G.m+1) ≤ budget := by
    simp only [budget,fixedPointLastLevelTool,hnl,ite_true,hk]
    exact (Nat.mul_le_mul_right _ (lastMWUK_ge_edges H)).trans (by omega)
  have hbase : G.m+1 ≤ budget := by
    have hh := Nat.mul_le_mul_right (G.m+1) hp
    simpa only [Nat.one_mul] using hh.trans hmodel
  have hscan : H.m*G.m ≤ budget :=
    (Nat.mul_le_mul_left _ (Nat.le_succ _)).trans hmodel
  have hsort := Nat.mul_le_mul_left (200*(Nat.log 2 (G.m+1)+1)) hbase
  have hargs : argsSize (stretchIndexKeyArgs 134 136 133)+
      argsSize (stretchIndexKeyArgs 100 138 73) ≤ 100 := by decide
  change _ ≤ _*budget
  rw [Nat.add_mul]
  have he : 200*G.m*(Nat.log 2 (G.m+1)+1) ≤
      200*(Nat.log 2 (G.m+1)+1)*budget := by
    calc
      _ = 200*(Nat.log 2 (G.m+1)+1)*G.m := by ring
      _ ≤ _ := (Nat.mul_le_mul_left _ (Nat.le_succ _)).trans hsort
  simp only [Nat.add_mul, Nat.mul_assoc] at he ⊢
  omega

end MinCostFlow.LastLevelProgram
