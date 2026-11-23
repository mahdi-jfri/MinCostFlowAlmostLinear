module

public import MinCostFlow.LastLevelProgram.LSSTCallCost
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Charging the last-level initialization

Combine the tree-call costs with the preparation, round arithmetic, and publication costs of Definition 5.8 (pages 19–20).
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord SparseCore
open scoped BigOperators

/-- Combined factor for representative input, guest length setup and linked rounds. -/
noncomputable def representativeSetupRoundsMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  runtimeEndpointMultiplier L m + representativeGuestSetupMultiplier D L m +
    (representativeStagedRoundMultiplier Q c D K L n m + (argsSize publishedRoundArgs+10)+7) +
    (200*(Nat.log 2 (m+1)+1)+500) + 4

/-- The last-level model budget absorbs the verified preparation costs and
the linked round budget on inputs with at least one retained edge. -/
theorem representativeSetupRoundsCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep tables format rounds : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hm : 0 < (representativeGraph G ℓ).m)
    (hprep : prep ≤ runtimeEndpointMultiplier L G.m * (G.m+1))
    (htables : tables ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*
      ((fixedPointLastLevelTool oracle C).cost G+1))
    (hformat : format ≤ representativeGuestSetupMultiplier ⌈max 1 C⌉₊ L G.m * (G.m+1))
    (hrounds : rounds ≤ (representativeStagedRoundMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m +
      (argsSize publishedRoundArgs+10)+7) *
      ((fixedPointLastLevelTool oracle C).cost G+1)) :
    prep+format+rounds+tables+4 ≤ representativeSetupRoundsMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1) := by
  let budget := (fixedPointLastLevelTool oracle C).cost G+1
  have hcount : (representativeGraph G (fun _ => 1)).m = (representativeGraph G ℓ).m := by
    rw [representativeGraph_m,representativeGraph_m]
  have hbudget : G.m+1 ≤ budget := by
    simp only [budget,fixedPointLastLevelTool,hnl,ite_true]
    have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) :=
      (show 1 ≤ (representativeGraph G (fun _ => 1)).m by rwa [hcount]).trans
        (lastMWUK_ge_edges _)
    have hmul := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at hmul
    omega
  have hp := hprep.trans (Nat.mul_le_mul_left _ hbudget)
  have hf := hformat.trans (Nat.mul_le_mul_left _ hbudget)
  have hfour : 4 ≤ 4*budget := Nat.le_mul_of_pos_right 4 (by omega)
  unfold representativeSetupRoundsMultiplier
  simp only [Nat.add_mul]
  simp only [Nat.add_mul] at htables hrounds
  dsimp only [budget] at hp hf hfour
  omega

/-- Add the initial unit weights and publication overhead to the linked
representative-round factor. -/
noncomputable def representativeRuntimeMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativeSetupRoundsMultiplier Q c D K L n m + (73*L+535+40*(n+2).size)

/-- On the non-loop path, initialization and publication are absorbed by the
same model budget as preparation, format selection, and the linked rounds. -/
theorem representativeRuntimeCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep tables format rounds levelCost : ℕ) (hnl : (nonLoopEdges G).Nonempty)
    (hcost : prep+format+rounds+tables+4 ≤ representativeSetupRoundsMultiplier
      Q c ⌈max 1 C⌉₊ K L G.n G.m * ((fixedPointLastLevelTool oracle C).cost G+1))
    (hlevelCost : levelCost ≤ 40*(G.n+2).size+22) :
    let m := (representativeGraph G ℓ).m
    m ≤ G.m → 0 < m →
    prep+format+rounds+tables+4 +
      (argsSize initialWeightControllerArgs + ((17*L+27)*m+56*L+111) +
        17*(m+1)+19+17+2*(narrowWeightSpaceExpr (.reg 127)).size+
        collectionHeaderAddress.size+17+levelCost+1) ≤
      representativeRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
        ((fixedPointLastLevelTool oracle C).cost G+1) := by
  dsimp only
  intro hm hmpos
  have hbudget : G.m+1 ≤ (fixedPointLastLevelTool oracle C).cost G+1 := by
    simp only [fixedPointLastLevelTool,hnl,ite_true]
    have hcount : (representativeGraph G (fun _ => 1)).m = (representativeGraph G ℓ).m := by
      rw [representativeGraph_m,representativeGraph_m]
    have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) := by
      exact (show 1 ≤ (representativeGraph G (fun _ => 1)).m by rwa [hcount]).trans
        (lastMWUK_ge_edges _)
    have h := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at h
    omega
  have ha : argsSize initialWeightControllerArgs ≤ 64 := by decide
  have hb : 2*(narrowWeightSpaceExpr (.reg 127)).size+collectionHeaderAddress.size ≤ 128 := by decide
  have hmul := Nat.mul_le_mul_left (17*L+27) hm
  let extra := 73*L+535+40*(G.n+2).size
  have hmul' : (17*L+27)*G.m+17*G.m ≤ extra*G.m := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by unfold extra; omega)
  have hover :
      argsSize initialWeightControllerArgs+((17*L+27)*(representativeGraph G ℓ).m+56*L+111)+
        17*((representativeGraph G ℓ).m+1)+19+17+2*(narrowWeightSpaceExpr (.reg 127)).size+
        collectionHeaderAddress.size+17+levelCost+1 ≤ extra*(G.m+1) := by
    rw [Nat.mul_add extra G.m 1, Nat.mul_one]
    dsimp [extra] at hmul' ⊢
    omega
  unfold representativeRuntimeMultiplier
  rw [Nat.add_mul (representativeSetupRoundsMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m)]
  apply Nat.add_le_add hcost
  exact hover.trans (Nat.mul_le_mul_left _ hbudget)

/-- Runtime multiplier for the non-loop path, including the scan that
selects the initializer. Its variable arguments are the caller limb count
and the original vertex and edge counts. -/
noncomputable def representativeDispatchMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativeRuntimeMultiplier Q c D K L n m+80

/-- The dispatch scan costs at most eighty times the non-loop model
budget. The branch initializer keeps its own multiplier. -/
theorem representativeDispatchCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (L cost : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hcost : cost ≤ representativeRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1)) :
    cost+29*G.m+80 ≤ representativeDispatchMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1) := by
  have hm : 0 < (representativeGraph G (fun _ => 1)).m := by
    by_contra! h
    exact (representativeGraph_m_eq_zero_iff G _).mp (Nat.eq_zero_of_le_zero h) hnl
  have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) :=
    hm.trans_le (lastMWUK_ge_edges _)
  have hbudget : G.m+1 ≤ (fixedPointLastLevelTool oracle C).cost G+1 := by
    have hd := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at hd
    simp only [fixedPointLastLevelTool,hnl,ite_true]
    omega
  have hscan : 29*G.m+80 ≤ 80*((fixedPointLastLevelTool oracle C).cost G+1) :=
    (show 29*G.m+80 ≤ 80*(G.m+1) by omega).trans (Nat.mul_le_mul_left _ hbudget)
  unfold representativeDispatchMultiplier
  rw [Nat.add_mul (representativeRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m)]
  omega

/-- The runtime precision bound controls scratch widths uniformly in
the caller limb count and the traversal depth. -/
theorem packedRoundScratchWidth_le {L P levels : ℕ} (hP : P ≤ 4*L) :
    L+(P+levels+7)/4 ≤ 2*L+levels+1 := by omega

/-- The widened preparation and compact packing passes together cost
a linear number of block operations per edge. -/
theorem packedRoundTableCost_le (L K m : ℕ) (hLK : L ≤ K) :
    stagedScratchWidthExpr.size+
      argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
        [.reg 64])+37+34*m+(2*((30*K+90)*m+20)+56*K+72)+
      (2*((35*L+60)*m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21)
      ≤ (130*K+900)*(m+1) := by
  have hprep : stagedScratchWidthExpr.size+
      argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
        [.reg 64]) ≤ 400 := by decide
  have hpack : argsSize packedStagedOutputArgs+
      argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20)) ≤ 200 := by decide
  have hmul := Nat.mul_le_mul_right m hLK
  nlinarith only [hprep,hpack,hmul]

/-- Bound widened arithmetic and both table passes using only caller
limbs, graph size, and the maximum traversal depth. -/
theorem packedRoundNumericCost_le (H : MGraph) (L P levels count n m : ℕ)
    (hP : P ≤ 4*L) (hlevels : levels ≤ (n+2).size)
    (hcount : count ≤ H.n) (hn : H.n ≤ m+1) (hm : H.m ≤ m) :
    let K := L+(P+levels+7)/4
    let B := 2*L+(n+2).size+1
    argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
      argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor K levels*(H.m+1)+13+
      (130*K+900)*(H.m+1)
      ≤ (stagedNumericFactor B (n+2).size+238*B+1900)*(m+1) := by
  intro K B
  have hKB : K ≤ B := (packedRoundScratchWidth_le hP).trans (by dsimp [B]; omega)
  have hmain := stagedRebuildNumericCost_le H K levels B (n+2).size m hKB hlevels hm hn
  have htable := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 130 hKB) 900) (Nat.succ_le_succ hm)
  have hsz : argsSize (stagedNumericArgsFrom 24) = argsSize stagedNumericArgs := by decide
  have hbase : argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
      argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor K levels*(H.m+1)+13
      ≤ stagedRebuildNumericCost H K levels := by
    unfold stagedRebuildNumericCost
    rw [hsz]
    have := Nat.mul_le_mul_left 112 hcount
    omega
  have he : (stagedNumericFactor B (n+2).size+108*B+1000)*(m+1)+(130*B+900)*(m+1) =
      (stagedNumericFactor B (n+2).size+238*B+1900)*(m+1) := by ring
  exact (Nat.add_le_add (hbase.trans hmain) htable).trans_eq he

/-- The packed round factor uses the caller format for selection and
branch publication, and a separate bound for widened arithmetic. -/
noncomputable def representativePackedRoundMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  let B := 2*L+(n+2).size+1
  representativeStagedRoundMultiplier Q c D K L n m+
    (stagedNumericFactor B (n+2).size+238*B+1900+(90*L+2200))

/-- Charge a packed round including tree selection, signed arithmetic,
output packing, branch append, and the controller's staging work. -/
theorem representativePackedRoundCost_le (w : ℕ) (Q : Program) (c D : ℕ) (K : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (L N P levels count cost : ℕ)
    (hG : G.IsValid) (hn : G.n ≤ G.m+1)
    (hN : N ≤ representativeGuestWidthBound D L G.m) (hlevels : levels ≤ (G.n+2).size)
    (hP : P ≤ 4*L) :
    let H := representativeGraph G ℓ
    let sim := lsstLSimMin c H.n H.m N 1
    let scratch := L+(P+levels+7)/4
    0 < H.m → count ≤ H.n →
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) * lsstOverheadFactor Q c K H.n H.m N →
    argsSize convertedGuestCallArgs+convertedTreeSelectorCost w Q D H N sim cost+
      argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+40*H.n+19+
      (argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13))+
        argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor scratch levels*(H.m+1)+13)+
      (130*scratch+900)*(H.m+1)+
      stagedAppendModelCost G L count+21+17*queryWeights H N+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤
    representativePackedRoundMultiplier Q c D K L G.n G.m*(G.m+1) := by
  intro H sim scratch hm hcount hcost
  have hsub := representativeGraph_subgraph hG ℓ
  have hm' : H.m ≤ G.m := Finset.card_le_card hsub.2.1
  have hn' : H.n ≤ G.m+1 := (Finset.card_le_card hsub.1).trans hn
  have hGm : 1 ≤ G.m := hm.trans_le hm'
  have hAppend : stagedAppendModelCost G L count ≤ (90*L+2200)*(G.m+1) :=
    stagedAppendModelCost_le G L count hn (by omega)
  have hbase := representativeStagedRoundCost_le w Q c D K G ℓ L N levels cost hG hn hN hlevels hm hcost
  have hnum := packedRoundNumericCost_le H L P levels count G.n G.m hP hlevels hcount hn' hm'
  dsimp only [H,sim,scratch] at *
  unfold representativePackedRoundMultiplier
  dsimp only
  simp only [Nat.add_mul] at hnum hAppend ⊢
  omega

/-- Charge the packed controller loop, including the call overhead and
loop setup, against the model budget for the representative graph. -/
theorem representativePackedLoopCost_le (Q : Program) (c D : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ) (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let R := representativePackedRoundMultiplier Q c D K L G.n G.m
    (argsSize publishedRoundArgs+R*(G.m+1)+10)*lastMWUK H+7 ≤
      (R+argsSize publishedRoundArgs+10+7)*((fixedPointLastLevelTool oracle C).cost G+1) := by
  intro H R
  have hc : lastMWUK (representativeGraph G (fun _ => 1)) = lastMWUK H := by
    unfold lastMWUK
    rw [representativeGraph_m,representativeGraph_m]
  have hm : lastMWUK H*(G.m+1)+2 = (fixedPointLastLevelTool oracle C).cost G+1 := by
    simp only [fixedPointLastLevelTool,hnl,ite_true,hc]
  rw [← hm]
  have h₁ : lastMWUK H ≤ lastMWUK H*(G.m+1)+2 := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have h₂ : R*(G.m+1)*lastMWUK H ≤ R*(lastMWUK H*(G.m+1)+2) := by
    rw [Nat.mul_assoc,Nat.mul_comm (G.m+1) (lastMWUK H)]
    exact Nat.mul_le_mul_left R (Nat.le_add_right _ _)
  have h₃ := Nat.mul_le_mul_left (argsSize publishedRoundArgs+10) h₁
  have h₄ : 7 ≤ 7*(lastMWUK H*(G.m+1)+2) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  simp only [Nat.add_mul] at h₃ ⊢
  omega

/-- Charge endpoint packing, guest setup, and packed rounds together. -/
noncomputable def representativePackedSetupRoundsMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  runtimeEndpointMultiplier L m + representativeGuestSetupMultiplier D L m +
    (representativePackedRoundMultiplier Q c D K L n m + (argsSize publishedRoundArgs+10)+7) +
    (200*(Nat.log 2 (m+1)+1)+500) + 4

/-- The last-level model budget absorbs the verified preparation costs and
the linked round budget on inputs with at least one retained edge. -/
theorem representativePackedSetupRoundsCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep tables format rounds : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hm : 0 < (representativeGraph G ℓ).m)
    (hprep : prep ≤ runtimeEndpointMultiplier L G.m * (G.m+1))
    (htables : tables ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*
      ((fixedPointLastLevelTool oracle C).cost G+1))
    (hformat : format ≤ representativeGuestSetupMultiplier ⌈max 1 C⌉₊ L G.m * (G.m+1))
    (hrounds : rounds ≤ (representativePackedRoundMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m +
      (argsSize publishedRoundArgs+10)+7) *
      ((fixedPointLastLevelTool oracle C).cost G+1)) :
    prep+format+rounds+tables+4 ≤ representativePackedSetupRoundsMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1) := by
  let budget := (fixedPointLastLevelTool oracle C).cost G+1
  have hcount : (representativeGraph G (fun _ => 1)).m = (representativeGraph G ℓ).m := by
    rw [representativeGraph_m,representativeGraph_m]
  have hbudget : G.m+1 ≤ budget := by
    simp only [budget,fixedPointLastLevelTool,hnl,ite_true]
    have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) :=
      (show 1 ≤ (representativeGraph G (fun _ => 1)).m by rwa [hcount]).trans
        (lastMWUK_ge_edges _)
    have hmul := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at hmul
    omega
  have hp := hprep.trans (Nat.mul_le_mul_left _ hbudget)
  have hf := hformat.trans (Nat.mul_le_mul_left _ hbudget)
  have hfour : 4 ≤ 4*budget := Nat.le_mul_of_pos_right 4 (by omega)
  unfold representativePackedSetupRoundsMultiplier
  simp only [Nat.add_mul]
  simp only [Nat.add_mul] at htables hrounds
  dsimp only [budget] at hp hf hfour
  omega

/-- Add the initial unit weights and publication overhead to the linked
representative-round factor. -/
noncomputable def representativePackedRuntimeMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativePackedSetupRoundsMultiplier Q c D K L n m + (73*L+535+40*(n+2).size)

/-- On the non-loop path, initialization and publication are absorbed by the
same model budget as preparation, format selection, and the linked rounds. -/
theorem representativePackedRuntimeCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep tables format rounds levelCost : ℕ) (hnl : (nonLoopEdges G).Nonempty)
    (hcost : prep+format+rounds+tables+4 ≤ representativePackedSetupRoundsMultiplier
      Q c ⌈max 1 C⌉₊ K L G.n G.m * ((fixedPointLastLevelTool oracle C).cost G+1))
    (hlevelCost : levelCost ≤ 40*(G.n+2).size+22) :
    let m := (representativeGraph G ℓ).m
    m ≤ G.m → 0 < m →
    prep+format+rounds+tables+4 +
      (argsSize initialWeightControllerArgs + ((17*L+27)*m+56*L+111) +
        17*(m+1)+19+17+
        collectionHeaderAddress.size+20+levelCost+1) ≤
      representativePackedRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
        ((fixedPointLastLevelTool oracle C).cost G+1) := by
  dsimp only
  intro hm hmpos
  have hbudget : G.m+1 ≤ (fixedPointLastLevelTool oracle C).cost G+1 := by
    simp only [fixedPointLastLevelTool,hnl,ite_true]
    have hcount : (representativeGraph G (fun _ => 1)).m = (representativeGraph G ℓ).m := by
      rw [representativeGraph_m,representativeGraph_m]
    have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) := by
      exact (show 1 ≤ (representativeGraph G (fun _ => 1)).m by rwa [hcount]).trans
        (lastMWUK_ge_edges _)
    have h := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at h
    omega
  have ha : argsSize initialWeightControllerArgs ≤ 64 := by decide
  have hb : collectionHeaderAddress.size ≤ 125 := by decide
  have hmul := Nat.mul_le_mul_left (17*L+27) hm
  let extra := 73*L+535+40*(G.n+2).size
  have hmul' : (17*L+27)*G.m+17*G.m ≤ extra*G.m := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by unfold extra; omega)
  have hover :
      argsSize initialWeightControllerArgs+((17*L+27)*(representativeGraph G ℓ).m+56*L+111)+
        17*((representativeGraph G ℓ).m+1)+19+17+
        collectionHeaderAddress.size+20+levelCost+1 ≤ extra*(G.m+1) := by
    rw [Nat.mul_add extra G.m 1, Nat.mul_one]
    dsimp [extra] at hmul' ⊢
    omega
  unfold representativePackedRuntimeMultiplier
  rw [Nat.add_mul (representativePackedSetupRoundsMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m)]
  apply Nat.add_le_add hcost
  exact hover.trans (Nat.mul_le_mul_left _ hbudget)

/-- Runtime multiplier for the non-loop path, including the scan that
selects the initializer. Its variable arguments are the caller limb count
and the original vertex and edge counts. -/
noncomputable def representativePackedDispatchMultiplier (Q : Program) (c D : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativePackedRuntimeMultiplier Q c D K L n m+80

/-- The dispatch scan costs at most eighty times the non-loop model
budget. The branch initializer keeps its own multiplier. -/
theorem representativePackedDispatchCost_le (Q : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (L cost : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hcost : cost ≤ representativePackedRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1)) :
    cost+29*G.m+80 ≤ representativePackedDispatchMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m *
      ((fixedPointLastLevelTool oracle C).cost G+1) := by
  have hm : 0 < (representativeGraph G (fun _ => 1)).m := by
    by_contra! h
    exact (representativeGraph_m_eq_zero_iff G _).mp (Nat.eq_zero_of_le_zero h) hnl
  have hk : 1 ≤ lastMWUK (representativeGraph G (fun _ => 1)) :=
    hm.trans_le (lastMWUK_ge_edges _)
  have hbudget : G.m+1 ≤ (fixedPointLastLevelTool oracle C).cost G+1 := by
    have hd := Nat.mul_le_mul_right (G.m+1) hk
    simp only [Nat.one_mul] at hd
    simp only [fixedPointLastLevelTool,hnl,ite_true]
    omega
  have hscan : 29*G.m+80 ≤ 80*((fixedPointLastLevelTool oracle C).cost G+1) :=
    (show 29*G.m+80 ≤ 80*(G.m+1) by omega).trans (Nat.mul_le_mul_left _ hbudget)
  unfold representativePackedDispatchMultiplier
  rw [Nat.add_mul (representativePackedRuntimeMultiplier Q c ⌈max 1 C⌉₊ K L G.n G.m)]
  omega

/-- Account for the actual phase costs and the sequence node between
tree selection and the widened numeric pass. -/
theorem representativePackedLinkCost_le (w : ℕ) (Q : Program) (c D : ℕ) (K : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (L N P levels count cost cs cn cp cb : ℕ)
    (hG : G.IsValid) (hn : G.n ≤ G.m+1)
    (hN : N ≤ representativeGuestWidthBound D L G.m) (hlevels : levels ≤ (G.n+2).size)
    (hP : P ≤ 4*L) :
    let H := representativeGraph G ℓ
    let scratch := L+(P+levels+7)/4
    let sim := lsstLSimMin c H.n H.m N 1
    0 < H.m → count ≤ H.n →
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) * lsstOverheadFactor Q c K H.n H.m N →
    cs ≤ argsSize convertedGuestCallArgs+convertedTreeSelectorCost w Q D H N sim cost+
      argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+40*H.n+17 →
    cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13))+
      argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor scratch levels*(H.m+1)+13+
      (stagedScratchWidthExpr.size+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
          [.reg 64])+37+34*H.m+(2*((30*scratch+90)*H.m+20)+56*scratch+72))+1 →
    cp ≤ 2*((35*L+60)*H.m+17)+argsSize packedStagedOutputArgs+
      argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 →
    cb ≤ stagedAppendModelCost G L count →
    cs+cn+1+cp+cb+21+17*queryWeights H N+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤
    representativePackedRoundMultiplier Q c D K L G.n G.m*(G.m+1) := by
  intro H scratch sim hm hc hcost hcs hcn hcp hcb
  have htable := packedRoundTableCost_le L scratch H.m (Nat.le_add_right _ _)
  have htotal := representativePackedRoundCost_le w Q c D K G ℓ L N P levels count cost
    hG hn hN hlevels hP hm hc hcost
  dsimp only [H,scratch,sim] at *
  simp only [Nat.add_mul] at htable htotal hcn hcp
  omega

/-- The runtime guest width and lifting depth satisfy the dimension
bounds used in the representative round multiplier. -/
theorem representativePackedCost_dimensions (C : ℝ) (G : MGraph)
    (mem : ℕ → ℕ) (src L Q : ℕ) (hG : G.IsValid) (hQ : Q ≤ 4*L)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hvalid : ∀ e ∈ G.E, Num.Valid mem (src+e*L) 4 L)
    (hpos : ∀ e ∈ G.E, 0 < MinRatio.readEdgeValues mem src 4 L Q G.E e) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L Q G.E
    let H := representativeGraph G ℓ
    roundQueryLimbs C H (LSF.safeLen H ℓ) ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m ∧
      Nat.clog 2 H.n ≤ (G.n+2).size := by
  intro ℓ H
  obtain ⟨e,he⟩ := hne
  have hf := (representativeGraph_shortest (ℓ := ℓ) he).1
  have hm : 0 < H.m := Finset.card_pos.mpr ⟨_,hf⟩
  have hsub := representativeGraph_subgraph hG ℓ
  have hn : H.n ≤ G.n := Finset.card_le_card hsub.1
  have hblocks (f : ℕ) (hf' : f ∈ G.E) :
      Num.Valid mem (src+f*L) 4 L ∧ 0 < Num.intVal mem (src+f*L) 4 L := by
    have hp := hpos f hf'
    simp only [MinRatio.readEdgeValues,ite_eq_left hf',Num.fixVal] at hp
    have hi := (div_pos_iff_of_pos_right (show (0 : ℝ) < (2 : ℝ)^Q by positivity)).mp hp
    exact ⟨hvalid f hf',by exact_mod_cast hi⟩
  have hlen : LSF.safeLen H ℓ =
      fun f => if f ∈ H.E then Num.fixVal mem (src+f*L) 4 L Q else 0 := by
    funext f
    by_cases hf' : f ∈ H.E
    · rw [LSF.safeLen_eq_of_mem ℓ hf',ite_eq_left hf']
      simp only [ℓ,MinRatio.readEdgeValues,ite_eq_left (hsub.2.1 hf')]
    · simp [LSF.safeLen,hf']
  refine ⟨?_,(Nat.clog_le_iff_le_pow (by decide)).2 ?_⟩
  · rw [hlen]
    exact representativeRoundQueryLimbs_le C G ℓ mem src L Q hG hQ hm hblocks
  · exact hn.trans ((Nat.le_add_right G.n 2).trans (Nat.lt_size_self _).le)

/-- The runtime initializer supplies the format and length facts needed
to charge the guest calls and traversal tables. -/
theorem representativePackedCost_dimensions_of_initPre
    {w L vCap eCap multiplier P graph src heap : ℕ} (fmt : Num.Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (C : ℝ) (G : MGraph) (mem : ℕ → ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [graph,src,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    roundQueryLimbs C H (LSF.safeLen H ℓ) ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m ∧
      Nat.clog 2 H.n ≤ (G.n+2).size := by
  obtain ⟨g',src',heap',hargs,hbits,hQ,hbase,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at hargs
  obtain ⟨rfl,rfl,rfl⟩ := hargs
  obtain ⟨g',src',heap',hargs,hgraph,_,_,hvalid,hpos⟩ := hbase
  simp only [List.cons.injEq,and_true] at hargs
  obtain ⟨rfl,rfl,rfl⟩ := hargs
  exact representativePackedCost_dimensions C G mem src L fmt.precision hgraph.1 hQ hne
    (by simpa only [hbits] using hvalid) (by simpa only [hbits] using hpos)

/-- Charge the linked round directly at the guest width and lifting
depth chosen from the runtime input. -/
theorem representativePackedLinkCost_of_initPre
    {w L vCap eCap multiplier P stretchPrecision graph src heap : ℕ} (fmt : Num.Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (Q : Program) (c : ℕ) (C K : ℝ) (G : MGraph) (mem : ℕ → ℕ)
    (count cost cs cn cp cb : ℕ) (hG : G.IsValid) (hn : G.n ≤ G.m+1)
    (hne : (SparseCore.nonLoopEdges G).Nonempty) (hP : P ≤ 4*L)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision
      allocation).initPre [graph,src,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let N := roundQueryLimbs C H (LSF.safeLen H ℓ)
    let levels := Nat.clog 2 H.n
    let D := ⌈max 1 C⌉₊
    let scratch := L+(P+levels+7)/4
    let sim := lsstLSimMin c H.n H.m N 1
    0 < H.m → count ≤ H.n →
    (cost : ℝ) ≤ 16000 * ((H.m+H.n+1 : ℕ) : ℝ) * lsstOverheadFactor Q c K H.n H.m N →
    cs ≤ argsSize convertedGuestCallArgs+convertedTreeSelectorCost w Q D H N sim cost+
      argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+40*H.n+17 →
    cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13))+
      argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor scratch levels*(H.m+1)+13+
      (stagedScratchWidthExpr.size+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
          [.reg 64])+37+34*H.m+(2*((30*scratch+90)*H.m+20)+56*scratch+72))+1 →
    cp ≤ 2*((35*L+60)*H.m+17)+argsSize packedStagedOutputArgs+
      argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 →
    cb ≤ stagedAppendModelCost G L count →
    cs+cn+1+cp+cb+21+17*queryWeights H N+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤
    representativePackedRoundMultiplier Q c D K L G.n G.m*(G.m+1) := by
  intro ℓ H N levels D scratch sim
  obtain ⟨hN,hlevels⟩ :=
    representativePackedCost_dimensions_of_initPre fmt tool allocation C G mem hne hpre
  exact representativePackedLinkCost_le w Q c D K G ℓ L N P levels count cost cs cn cp cb
    hG hn hN hlevels hP

/-- The graph-only reservation bounds the space computed from the live
length table at a connected non-loop initializer call. -/
theorem representativePackedRuntimeSpace_le_of_initPre
    {w L vCap eCap multiplier P g src heap : ℕ} (fmt : Num.Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (guest : Program) (C : ℝ) (c₀ : ℕ) (mem : ℕ → ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,src,L,fmt.precision,heap] mem) :
    representativePackedRuntimeSpace G guest C c₀ vCap eCap mem [g,src,L,fmt.precision,heap] ≤
      representativePackedSpaceBound G guest C c₀ L vCap eCap := by
  obtain ⟨hwidth,_⟩ :=
    representativePackedCost_dimensions_of_initPre fmt tool allocation C G mem hne hpre
  obtain ⟨hgraph,_,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool allocation G mem hpre
  exact representativePackedInitSpace_le_bound G guest C c₀ L vCap eCap _
    (MinRatio.readEdgeValues mem src 4 L fmt.precision G.E)
    hgraph.1 hne hconn hwidth

end MinCostFlow.LastLevelProgram
