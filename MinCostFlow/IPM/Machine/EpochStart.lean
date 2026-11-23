module

public import MinCostFlow.IPM.Machine.MinRatioInitInput
public import MinCostFlow.IPM.Machine.MinRatioInitProgram

/-!
# Starting an epoch from explicit stored coordinates

Compute all lengths and gradients using the epoch residual, then
initEntry the min-ratio structure from these actual arrays. The arrays
occupy the numerical procedures' reserved workspaces. The structure
starts at the next heap address, which is its handle for this epoch.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The fourteen-word coefficient-refresh packet is followed by the graph
pointer. Register 15 preserves that pointer across both calls. -/
def epochStartBody (refresh initEntry : ℕ) : Stmt :=
  .assign 15 (.reg 14) ;;
  .call 14 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13] ;;
  .call 16 initEntry [.reg 15,.bin .add (.reg 13) (.reg 11),.reg 13,.reg 8,.reg 9,.reg 14] ;;
  .ret (.reg 16)

/-- Determinism of the epoch-start driver's own instructions. -/
theorem epochStartBody_noRand (refresh initEntry : ℕ) :
    (epochStartBody refresh initEntry).NoRand := by
  simp [epochStartBody,Stmt.NoRand]

/-- Exact numerical workspace followed by the parameter's initialization
allocation. The DS handle is the endpoint of the numerical workspace. -/
def epochStartSpace {w : ℕ} (F : MinRatioFormat w) (I : Instance) (E graph heap : ℕ)
    (allocation : ℕ → List ℕ → ℕ) : ℕ :=
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  la+ga+allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,heap+(la+ga)]

/-- Starting an epoch checks the original numeric inputs and graph.
Every postcondition names the actual intermediate coefficient memory. -/
def epochStartContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (q K : ℕ) : Contract where
  pre args mem := ∃ cp rp lo fp up ap one E graph heap,
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
    args=[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap,graph] ∧
    I.IsValid ∧ GraphAt mem graph (namedInstance I) ∧
    (∀ z∈graphWords (namedInstance I),z<2^w) ∧
    graph+(graphWords (namedInstance I)).length≤heap ∧
    (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α ∧
    5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision ∧
    (coefficientRefreshContract w F.fmt.limbBits q K).pre (args.take 14) mem ∧
    heap+epochStartSpace F I E graph heap allocation<2^w ∧
    ∀ i<I.m,(2:ℝ)^(-(F.rangeExponent:ℤ))*2≤
      Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i ∧
      2*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i≤
        (2:ℝ)^F.rangeExponent
  post args mem v mem' := ∃ coefficients,
    let heap := args.getD 13 0
    let la := args.getD 11 0
    let ga := args.getD 12 0
    let handle := heap+(la+ga)
    (coefficientRefreshContract w F.fmt.limbBits q K).post (args.take 14) mem handle coefficients ∧
    (minRatioInitContract w R (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation)).post
      [args.getD 14 0,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients v mem'
  cost args _ := Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision (args.getD 10 0)+
    Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision (args.getD 10 0)+rate I.m*(I.m+1)+500

/-- Adapts a `V`-aware 7-argument Init allocation function to the 6-argument
epoch allocation interface by inserting `V` at index 5 when `j = 3`. -/
def allocationWithV (V : ℕ) (allocation : ℕ → List ℕ → ℕ) (j : ℕ) (args : List ℕ) : ℕ :=
  if j = 3 then allocation 3 (args.take 5 ++ [V] ++ args.drop 5) else allocation j args

/-- Kernel-definitional reduction of `allocationWithV` on a 6-element Init packet. -/
theorem allocationWithV_init (V : ℕ) (allocation : ℕ → List ℕ → ℕ) (a b c d e f : ℕ) :
    allocationWithV V allocation 3 [a, b, c, d, e, f] = allocation 3 [a, b, c, d, e, V, f] :=
  rfl

/-- A uniform bound on `allocation` across `j < 4` yields the same bound on `allocationWithV`. -/
theorem allocationWithV_le (V : ℕ) {allocation : ℕ → List ℕ → ℕ} {B : ℕ}
    (halloc : ∀ j < 4, ∀ args, allocation j args ≤ B) :
    ∀ j < 4, ∀ args, allocationWithV V allocation j args ≤ B := by
  intro j hj args
  unfold allocationWithV
  split_ifs
  · exact halloc 3 (by decide) _
  · exact halloc j hj args

/-- An implementation for `allocation` (at any `initPre`) restricts cleanly to an
operation-only implementation (`initPre := fun _ _ => False`) for `allocationWithV V allocation`. -/
theorem minRatioImplements_allocationWithV {w : ℕ} {p : Program} {init : ℕ} {op : ℕ → ℕ}
    {F : MinRatioFormat w} {A : MinRatioDataStructureWithFailure} {G : MGraph} {m : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {initPre : List ℕ → (ℕ → ℕ) → Prop}
    (R : DSRep A.State) (V : ℕ)
    (himpl : R.Implements w p init op (minRatioMachineContractAt F A G m κ α rate allocation initPre)) :
    R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate (allocationWithV V allocation) (fun _ _ => False)) := by
  refine ⟨himpl.1, ?_, ?_⟩
  · intro _ _ _ _ _ hpre
    exact False.elim hpre
  · intro i
    rcases i with _ | _ | _ | i
    · exact himpl.2.2 0
    · exact himpl.2.2 1
    · exact himpl.2.2 2
    · intro b s x vs mem pos ω hwords hhandle hrep hpre
      exact False.elim hpre.2

/-- `V`-passing variant of `epochStartBody`: takes 16 arguments `[..., heap, graph, V]`,
saves `graph` in `.reg 16`, keeps `V` in `.reg 15` across `refresh`, and passes
`[graph, heap+la, heap, L, P, V, handle]` to `initEntry`. -/
def epochStartBodyWithV (refresh initEntry : ℕ) : Stmt :=
  .assign 16 (.reg 14) ;;
  .call 14 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13] ;;
  .call 17 initEntry [.reg 16,.bin .add (.reg 13) (.reg 11),.reg 13,.reg 8,.reg 9,.reg 15,.reg 14] ;;
  .ret (.reg 17)

/-- Determinism of the `V`-passing epoch-start driver's own instructions. -/
theorem epochStartBodyWithV_noRand (refresh initEntry : ℕ) :
    (epochStartBodyWithV refresh initEntry).NoRand := by
  simp [epochStartBodyWithV,Stmt.NoRand]

end MinCostFlow.IPM.Machine
