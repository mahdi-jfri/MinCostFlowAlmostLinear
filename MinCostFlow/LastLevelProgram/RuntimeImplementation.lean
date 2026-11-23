module

public import MinCostFlow.LastLevelProgram.PackedRuntimeInit

/-!
# Implementation of the runtime last-level data structure

Definition 5.8 (pages 19–20) uses a single initializer with a separate
route for a graph with only loops. Operation zero reads a branch from
the resulting collection.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Charge the dispatcher and the initialization route taken by the graph. -/
@[expose] noncomputable def packedLastLevelMultiplier (guest : Program) (c d : ℕ)
    (K : ℝ) (G : MGraph) (L : ℕ) : ℕ :=
  if (SparseCore.nonLoopEdges G).Nonempty then
    packedNonLoopDispatchMultiplier guest c d K L G.n G.m
  else
    loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2

/-- The initialization budget is quadratic in live edges, multiplied
by the explicit machine overhead for the graph and caller format. -/
theorem packedLastLevelInitCost_quadratic
    (guest : Program) (c d L : ℕ) (K C : ℝ) (G : MGraph)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (hG : G.IsValid) :
    packedLastLevelMultiplier guest c d K G L*((fixedPointLastLevelTool oracle C).cost G+1) ≤
      2*(G.m+1)^2*packedLastLevelMultiplier guest c d K G L := by
  have hmodel : (fixedPointLastLevelTool oracle C).cost G+1 ≤ 2*(G.m+1)^2 := by
    by_cases hne : (SparseCore.nonLoopEdges G).Nonempty
    · let H := representativeGraph G (fun _ => 1)
      have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG _).2.1
      have hp : 1 ≤ H.m := by
        obtain ⟨e,he⟩ := hne
        exact Finset.card_pos.mpr ⟨_,(representativeGraph_shortest (ℓ := fun _ => 1) he).1⟩
      have hk : SparseCore.lastMWUK H ≤ 2*G.m :=
        (SparseCore.lastMWUK_bounds hp).2.2.2.trans (Nat.mul_le_mul_left 2 hm)
      simp only [fixedPointLastLevelTool, ite_eq_left hne]
      refine (Nat.add_le_add_right (Nat.mul_le_mul_right (G.m+1) hk) 2).trans ?_
      rw [pow_two, ← Nat.mul_assoc, Nat.mul_succ 2]
      have h := Nat.le_mul_of_pos_right 2 (Nat.succ_pos G.m)
      rw [Nat.add_mul]
      omega
    · simp only [fixedPointLastLevelTool,ite_eq_right hne]
      exact Nat.le_mul_of_pos_right 2 (Nat.pow_pos (Nat.succ_pos _))
  exact (Nat.mul_le_mul_left _ hmodel).trans_eq (Nat.mul_comm _ _)

/-- One program implements initialization and readout for the canonical
fixed-point tool on connected inputs in the four-bit caller format. -/
theorem packedLastLevelProgram_implements :
    ∃ (guest : Program) (c : ℕ) (K Cf : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      let C := graphCanonicalConstant K Cf
      let d := ⌈max 1 C⌉₊
      let p := packedLastLevelProgram guest d c
      let tool := fixedPointLastLevelTool oracle C
      tool.IsSpec (SparseCore.lastLevelParams (128 * max 1 C)) ∧
      ∀ {w L vCap eCap : ℕ} (fmt : Format w) (G : MGraph),
        fmt.limbBits = 4 →
        (∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) → G.n ≤ G.m+1 →
        let P := (1024*d).size+3*(G.m+1).size
        let multiplier := packedLastLevelMultiplier guest c d K G L
        let alloc := packedRuntimeAllocation G guest C c L vCap eCap
        (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
          w p 15 (fun _ => 16)
          (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc) := by
  obtain ⟨guest,c,K,Cf,oracle,hSpec,hrun⟩ := packedLastLevelProgram_nonLoop_withCanonical
  refine ⟨guest,c,K,Cf,oracle,hSpec,?_⟩
  intro w L vCap eCap fmt G hformat hconn hn P multiplier alloc
  let C := graphCanonicalConstant K Cf
  let d := ⌈max 1 C⌉₊
  have hw : 16 ≤ 2^w := by
    have h := fmt.product_fits
    rw [hformat] at h
    exact (show 16 ≤ 2^10 by decide).trans (Nat.pow_le_pow_right (by decide) h)
  by_cases hne : (SparseCore.nonLoopEdges G).Nonempty
  · have hmult : multiplier = packedNonLoopDispatchMultiplier guest c d K L G.n G.m := by
      simp only [multiplier, packedLastLevelMultiplier, ite_eq_left hne, d, C]
    rw [hmult]
    obtain ⟨_,hinit,hop,_,_,_⟩ := packedLastLevelProgram_entries guest d c
    apply lastLevelRuntime_implements_of_init fmt (fixedPointLastLevelTool oracle C) G
      alloc (dispatchRuntimeInit 17 19) hinit hop
    intro D args mem pos ω hargs hpre hz hroom
    have hshape := hpre
    obtain ⟨g,lengths,handle,rfl,_,_,_,_⟩ := hshape
    obtain ⟨ret,out,cost,hr,hrep,hpost,hbound,hzero,hframe,hcost⟩ :=
      hrun fmt G g lengths handle mem pos ω hne hconn hn hargs hpre hz hroom
    exact ⟨ret,out,cost,_,hr,hrep,hpost,hbound,hzero,hframe,hcost⟩
  · have hmult : multiplier = loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2 := by
      simp only [multiplier, packedLastLevelMultiplier, ite_eq_right hne]
    rw [hmult]
    exact packedLastLevelProgram_implements_loopOnly fmt oracle C G guest d c hw hne

end MinCostFlow.LastLevelProgram
