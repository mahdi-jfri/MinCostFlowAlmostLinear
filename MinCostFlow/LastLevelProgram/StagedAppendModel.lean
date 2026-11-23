module

public import MinCostFlow.LastLevelProgram.StagedAppendProof
public import MinCostFlow.MinRatio.LastLevelContract
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Space and state for staged branch publication

Definition 5.8 (pages 19–20) reserves the space for every branch and
carries the next weights in the round invariant.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num SparseCore DynSpanner.Program

/-- Each staged round reserves the same number of words. Sizes depend
on the graph and formats, while only its starting cursor changes. -/
@[expose] def stagedPublishedRoundSpace (H : MGraph) (guest : Program)
    (D guestL sim levels L count vCap eCap : ℕ) : ℕ :=
  let guestEnd := queryOriginals H guestL+1+
    2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
  let parents := guestEnd+H.m+H.n
  let adj := parents+stagedTraversalReserve H.n levels
  let tails := adj+H.n+6*H.n
  let old := tails+2*H.m+H.m*L
  let heap := old+H.m*L+2*L+H.n*L
  let numericEnd := heap+(H.n-1)*L+H.m*edgeStretchSpace L+H.m*narrowWeightSpace L
  let tree := numericEnd+2*L+3*count+4
  let addresses := tree+dynGraphSize vCap eCap+vCap+2
  addresses+eCap+eCap*L+eCap*L+1

/-- Space from the collection base includes its table, initial unit
weights, and one published allocation per round of Definition 5.8. -/
@[expose] def stagedPublishedCollectionSpace (H : MGraph) (guest : Program)
    (D guestL sim levels L count vCap eCap : ℕ) : ℕ :=
  1+count+2*L+H.m*narrowWeightSpace L+1+
    count*stagedPublishedRoundSpace H guest D guestL sim levels L count vCap eCap

/-- A widened round reserves room for numeric scratch, two compact
output tables, the published branch, and the next weight descriptor. -/
@[expose] def stagedPackedRoundSpace (H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap : ℕ) : ℕ :=
  let K := L+(P+levels+7)/4
  let guestEnd := queryOriginals H guestL+1+
    2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
  let parents := guestEnd+H.m+H.n
  let adj := parents+stagedTraversalReserve H.n levels
  let tails := adj+H.n+6*H.n
  let old := tails+2*H.m+H.m*K
  let heap := old+H.m*K+2*K+H.n*K
  let numericEnd := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
  let packedEnd := numericEnd+H.m*L+H.m*L
  let tree := packedEnd+2*L+3*count+4
  let addresses := tree+dynGraphSize vCap eCap+vCap+2
  addresses+eCap+eCap*L+eCap*L+1

/-- Reserving branch records for the vertex count covers any number
of retained tree edges. Only the three-word record array depends on that count. -/
theorem stagedPackedRoundSpace_mono_count (H : MGraph) (guest : Program)
    (D guestL sim levels L P vCap eCap : ℕ) {count boundCount : ℕ}
    (hcount : count ≤ boundCount) :
    stagedPackedRoundSpace H guest D guestL sim levels L P count vCap eCap ≤
      stagedPackedRoundSpace H guest D guestL sim levels L P boundCount vCap eCap := by
  unfold stagedPackedRoundSpace
  dsimp only
  have hrecords := Nat.mul_le_mul_left 3 hcount
  omega

/-- The simulation width grows with the edge count and guest limb
count. It can be reserved before the runtime length scan. -/
theorem packedSimWidth_mono {c n n' m m' N N' : ℕ} (hm : m ≤ m') (hN : N ≤ N') :
    WideWord.lsstLSimMin c n m N 1 ≤ WideWord.lsstLSimMin c n' m' N' 1 := by
  have hk : WideWord.kWidthOf m N ≤ WideWord.kWidthOf m' N' := by
    unfold WideWord.kWidthOf
    have hl := Nat.log_mono_right (b := 2) (show 4*m+2 ≤ 4*m'+2 by omega)
    omega
  have hl := Nat.log_mono_right (b := 2) (show 6+16*m ≤ 6+16*m' by omega)
  unfold WideWord.lsstLSimMin WideWord.w'Max
  exact max_le_max hk (Nat.mul_le_mul_left c (by simp only [Nat.mul_one]; omega))

/-- Increasing the guest limb and simulation budgets leaves the same
host arithmetic and publication layout within the larger reservation. -/
theorem stagedPackedRoundSpace_mono_guest (H : MGraph) (guest : Program)
    (D levels L P count vCap eCap : ℕ) {N N' sim sim' : ℕ}
    (hN : N ≤ N') (hsim : sim ≤ sim') :
    stagedPackedRoundSpace H guest D N sim levels L P count vCap eCap ≤
      stagedPackedRoundSpace H guest D N' sim' levels L P count vCap eCap := by
  have hmul := Nat.mul_le_mul_left H.m hN
  have hheap : queryHeap H N ≤ queryHeap H N' := by
    simp only [queryHeap,queryHeader,queryBridges,queryOriginals,queryWeights]
    omega
  have hwidth := paddedGuestWidth_mono guest (D := D) (n := H.n) (m := H.m) le_rfl le_rfl le_rfl hsim hheap
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hwidth
  simp only [stagedPackedRoundSpace,queryOriginals,queryWeights]
  omega

/-- The packed reservation depends on the representative counts, so
it can be sized using any representative graph with those counts. -/
theorem stagedPackedRoundSpace_congr_counts {H H' : MGraph} (guest : Program)
    (D N sim levels L P count vCap eCap : ℕ)
    (hn : H.n = H'.n) (hm : H.m = H'.m) :
    stagedPackedRoundSpace H guest D N sim levels L P count vCap eCap =
      stagedPackedRoundSpace H' guest D N sim levels L P count vCap eCap := by
  simp only [stagedPackedRoundSpace,queryHeap,queryHeader,queryBridges,queryOriginals,queryWeights,
    queryLengths,hn,hm]

/-- The collection reservation uses compact unit weights at entry. -/
@[expose] def stagedPackedCollectionSpace (H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap : ℕ) : ℕ :=
  1+count+2*L+H.m*L+1+
    count*stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap

/-- The reserved space covers every round from the compact initial cursor. -/
theorem stagedPackedCollectionSpace_initial (H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap base bound : ℕ)
    (hfit : base+stagedPackedCollectionSpace H guest D guestL sim levels L P count vCap eCap ≤ bound) :
    base+1+count+2*L+H.m*L+1+
      count*stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap ≤ bound := by
  simpa only [stagedPackedCollectionSpace,Nat.add_assoc] using hfit

/-- The collection reservation covers the initial weights and the
remaining round strides at the first loop entry. -/
theorem stagedPublishedCollectionSpace_initial (H : MGraph) (guest : Program)
    (D guestL sim levels L count vCap eCap base bound : ℕ) :
    let initial := base+1+count+2*L+H.m*narrowWeightSpace L+1
    let step := stagedPublishedRoundSpace H guest D guestL sim levels L count vCap eCap
    base+stagedPublishedCollectionSpace H guest D guestL sim levels L count vCap eCap ≤ bound →
    initial ≤ bound ∧ initial+count*step ≤ bound := by
  intro initial step h
  have hfit : initial+count*step ≤ bound := by
    simpa only [initial,step,stagedPublishedCollectionSpace,Nat.add_assoc] using h
  exact ⟨(Nat.le_add_right _ _).trans hfit,hfit⟩

/-- Reserve the representative input tables, packed collection, and
word-range slack for the controller's guest-prefix copy. -/
@[expose] def representativePackedInitSpace (G H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap : ℕ) : ℕ :=
  11*G.m+vCap+1+queryWeights H guestL+
    stagedPackedCollectionSpace H guest D guestL sim levels L P count vCap eCap+
    queryWeights H guestL

/-- The input and collection allocation supplies the initial controller
reservation and keeps the guest-prefix copy endpoint in word range. -/
theorem representativePackedInitSpace_bounds (G H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap handle w : ℕ)
    (hm : H.m ≤ G.m) (hn : H.n ≤ 2*G.m) (hc : count ≤ H.m) (hmPos : 0 < G.m)
    (hfit : handle+representativePackedInitSpace G H guest D guestL sim levels L P
      count vCap eCap < 2^w) :
    let src := handle+11*G.m+vCap+1
    let base := src+queryWeights H guestL
    let step := stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap
    let bound := base+stagedPackedCollectionSpace H guest D guestL sim levels L P count vCap eCap
    src+queryLengths H < 2^w ∧ queryHeap H guestL < 2^w ∧
      handle+1+count ≤ base ∧
      base+1+count+2*L+H.m*L+1+count*step ≤ bound ∧ bound+queryWeights H guestL < 2^w := by
  intro src base step bound
  have hw : bound+queryWeights H guestL < 2^w := by
    simpa only [bound,base,src,representativePackedInitSpace,Nat.add_assoc] using hfit
  have hlen : queryLengths H ≤ queryWeights H guestL := by
    unfold queryWeights
    exact Nat.le_add_right _ _
  have hsrc : src+queryLengths H ≤ base := Nat.add_le_add_left hlen _
  have hb : base ≤ bound := Nat.le_add_right _ _
  have hheap : queryHeap H guestL ≤ bound+queryWeights H guestL := by
    have hlen' : 2*H.m ≤ queryLengths H := by rfl
    dsimp only [bound,base,src,queryHeap,queryHeader,queryBridges,queryOriginals,queryWeights]
    have he : queryWeights H guestL = queryLengths H+H.m*guestL := rfl
    omega
  have hhandle : handle+1+count ≤ base := by
    dsimp only [base,src]
    omega
  exact ⟨(hsrc.trans hb).trans_lt ((Nat.le_add_right _ _).trans_lt hw),
    hheap.trans_lt hw,hhandle,
    stagedPackedCollectionSpace_initial H guest D guestL sim levels L P count vCap eCap
      base bound le_rfl,hw⟩

/-- The non-loop model builds one branch per representative edge.
Use that exact count in the runtime allocation and controller bounds. -/
theorem representativePackedInitSpace_modelBounds (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (guest : Program)
    (D guestL sim levels L P vCap eCap handle w : ℕ)
    (hG : G.IsValid) (hne : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let count := ((fixedPointLastLevelTool oracle C).build G ℓ).1
    let src := handle+11*G.m+vCap+1
    let base := src+queryWeights H guestL
    let step := stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap
    let bound := base+stagedPackedCollectionSpace H guest D guestL sim levels L P count vCap eCap
    handle+representativePackedInitSpace G H guest D guestL sim levels L P count vCap eCap < 2^w →
    count = H.m ∧ 0 < count ∧ src+queryLengths H < 2^w ∧ queryHeap H guestL < 2^w ∧
      handle+1+count ≤ base ∧ base+1+count+2*L+H.m*L+1+count*step ≤ bound ∧
      bound+queryWeights H guestL < 2^w := by
  intro H count src base step bound hfit
  have hc : count = H.m := by simp only [count,fixedPointLastLevelTool,ite_eq_left hne,H]
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  obtain ⟨e,he⟩ := hne
  have hf := (representativeGraph_shortest (ℓ := ℓ) he).1
  have hmPos : 0 < H.m := Finset.card_pos.mpr ⟨_,hf⟩
  have hn : H.n ≤ 2*G.m :=
    (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left 2 hm)
  exact ⟨hc,hc.symm ▸ hmPos,representativePackedInitSpace_bounds G H guest D guestL sim
    levels L P count vCap eCap handle w hm hn hc.le (hmPos.trans_le hm) hfit⟩

/-- The non-loop initializer uses the caller length table to compute
the same guest format and round reservation as the packed controller. -/
@[expose] noncomputable def representativePackedRuntimeSpace (G : MGraph) (guest : Program)
    (C : ℝ) (c₀ vCap eCap : ℕ) (mem : ℕ → ℕ) (args : List ℕ) : ℕ :=
  let L := args.getD 2 0
  let Q := args.getD 3 0
  let ℓ := MinRatio.readEdgeValues mem (args.getD 1 0) 4 L Q G.E
  let H := representativeGraph G ℓ
  let N := roundQueryLimbs C H (LSF.safeLen H ℓ)
  representativePackedInitSpace G H guest ⌈max 1 C⌉₊ N
    (WideWord.lsstLSimMin c₀ H.n H.m N 1) (Nat.clog 2 H.n)
    L (weightPrecision C H) H.m vCap eCap

/-- The runtime bound on the representative initializer leaves room
for the controller and its guest-prefix copy. -/
theorem representativePackedRuntimeSpace_bound (G : MGraph) (guest : Program) (C : ℝ)
    (c₀ vCap eCap g lengths L Q handle w : ℕ) (mem : ℕ → ℕ)
    (hfit : handle+representativePackedRuntimeSpace G guest C c₀ vCap eCap mem
      [g,lengths,L,Q,handle] < 2^w) :
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L Q G.E
    let H := representativeGraph G ℓ
    let N := roundQueryLimbs C H (LSF.safeLen H ℓ)
    let sim := WideWord.lsstLSimMin c₀ H.n H.m N 1
    let bound := handle+11*G.m+vCap+1+queryWeights H N+
      stagedPackedCollectionSpace H guest ⌈max 1 C⌉₊ N sim (Nat.clog 2 H.n)
        L (weightPrecision C H) H.m vCap eCap
    bound+queryWeights H N < 2^w := by
  simpa only [representativePackedRuntimeSpace,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,representativePackedInitSpace,Nat.add_assoc] using hfit

/-- Reserve a non-loop initializer before reading its length table.
Using unit lengths fixes the representative counts, and the guest limb
bound covers the width selected later by the initializer. -/
@[expose] noncomputable def representativePackedSpaceBound (G : MGraph) (guest : Program)
    (C : ℝ) (c₀ L vCap eCap : ℕ) : ℕ :=
  let H := representativeGraph G (fun _ => 1)
  let D := ⌈max 1 C⌉₊
  let N := representativeGuestWidthBound D L G.m
  representativePackedInitSpace G H guest D N
    (WideWord.lsstLSimMin c₀ H.n H.m N 1) (Nat.clog 2 H.n)
    L (weightPrecision C H) H.m vCap eCap

/-- Increasing the reserved guest width suffices for every length
table on a connected non-loop input with the same caller format. -/
theorem representativePackedInitSpace_le_bound (G : MGraph) (guest : Program) (C : ℝ)
    (c₀ L vCap eCap N : ℕ) (ℓ : ℕ → ℝ) (hG : G.IsValid) (hne : (nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hN : N ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m) :
    let H := representativeGraph G ℓ
    representativePackedInitSpace G H guest ⌈max 1 C⌉₊ N
      (WideWord.lsstLSimMin c₀ H.n H.m N 1) (Nat.clog 2 H.n)
      L (weightPrecision C H) H.m vCap eCap ≤
      representativePackedSpaceBound G guest C c₀ L vCap eCap := by
  intro H
  let H' := representativeGraph G (fun _ => 1)
  let D := ⌈max 1 C⌉₊
  let N' := representativeGuestWidthBound D L G.m
  have hn : H.n = H'.n := congrArg Finset.card
    ((representativeGraph_vertices_eq ℓ hG hne hconn).trans
      (representativeGraph_vertices_eq (fun _ => 1) hG hne hconn).symm)
  have hm : H.m = H'.m := (representativeGraph_m G ℓ).trans
    (representativeGraph_m G (fun _ => 1)).symm
  have hp : weightPrecision C H = weightPrecision C H' := by
    simp only [weightPrecision,integerScale,hn,hm]
  have hs := packedSimWidth_mono (c := c₀) (n := H.n) (n' := H.n) (m := H.m) le_rfl hN
  have hr := stagedPackedRoundSpace_mono_guest H guest D (Nat.clog 2 H.n) L
    (weightPrecision C H) H.n vCap eCap hN hs
  have he := stagedPackedRoundSpace_congr_counts (H := H) (H' := H') guest D N'
    (WideWord.lsstLSimMin c₀ H.n H.m N' 1) (Nat.clog 2 H.n) L
    (weightPrecision C H) H.n vCap eCap hn hm
  have hsum := Nat.mul_le_mul_left H.m (hr.trans_eq he)
  have hmul := Nat.mul_le_mul_left H.m hN
  change representativePackedInitSpace G H guest D N
    (WideWord.lsstLSimMin c₀ H.n H.m N 1) (Nat.clog 2 H.n) L (weightPrecision C H) H.m vCap eCap ≤
    representativePackedInitSpace G H' guest D N'
      (WideWord.lsstLSimMin c₀ H'.n H'.m N' 1) (Nat.clog 2 H'.n) L (weightPrecision C H') H'.m vCap eCap
  simp only [D,N',representativePackedInitSpace, stagedPackedCollectionSpace,
    queryWeights,queryLengths,hp,hn,hm] at hsum hmul ⊢
  exact by omega

/-- The reserved region covers the next round and leaves one stride for
each remaining round. -/
theorem stagedRoundReservation_step {cursor j count bound step : ℕ}
    (hj : j < count) (h : cursor+(count-j)*step ≤ bound) :
    cursor+step ≤ bound ∧ (cursor+step)+(count-(j+1))*step ≤ bound := by
  have hcount : count-j = count-(j+1)+1 := by omega
  rw [hcount,Nat.add_mul,Nat.one_mul] at h
  omega

/-- Apply the reservation step to the strided numeric workspace. -/
theorem stagedPublishedRoundSpace_step (H : MGraph) (guest : Program)
    (D guestL sim levels L count vCap eCap cursor j bound : ℕ)
    (hj : j < count) :
    let step := stagedPublishedRoundSpace H guest D guestL sim levels L count vCap eCap
    cursor+(count-j)*step ≤ bound →
    cursor+step ≤ bound ∧ (cursor+step)+(count-(j+1))*step ≤ bound :=
  stagedRoundReservation_step hj

/-- Run the controller with a reservation for every remaining iteration.
The reservation passes through the call alongside the collection invariant. -/
theorem stagedControllerRounds_reserved
    {w entry vCap eCap h L P caller base count handle bound budget step stride : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) (hbound : bound < 2^w) :
    let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem
    let Reserved := fun j (st : State) => Inv j st ∧ st.regs 0+(count-j)*step ≤ bound
    (∀ j < count, ∀ st, Reserved j st → (∀ r, st.regs r < 2^w) → st.regs 2 = j →
      MeetsContract w p entry (stagedControllerRoundContract st (Reserved (j+1)) j budget)) →
    Triple w p (fun st => Reserved 0 st ∧ ∀ r, st.regs r < 2^w)
      (lastLevelRoundsBody entry publishedRoundArgs) (normalPost (Inv count))
      (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) := by
  intro Inv Reserved hstep
  let J := fun j (st : State) => Reserved j st ∧ ∀ r, st.regs r < 2^w
  have hloop := lastLevelRounds_triple (p := p) (entry := entry) (args := publishedRoundArgs)
    count budget J hw hcount
    (fun st hs => by
      refine ⟨⟨?_,?_⟩,?_⟩
      · simpa [Inv,stagedRoundStateAtStride,Function.update] using hs.1.1
      · simpa only [Function.update_of_ne (by decide : 0 ≠ 2)] using hs.1.2
      · intro r
        by_cases hr : r = 2
        · subst r
          simp [show 0 < 2^w by omega]
        · simpa only [Function.update_of_ne hr] using hs.2 r)
    (fun _ _ hs => hs.1.1.1)
    (fun j hj st hs hidx => by
      refine ⟨_,_,hstep j hj st hs.1 hs.2 hidx,publishedRoundArgs_eval w st,?_,⟨rfl,rfl⟩,
        le_rfl,?_⟩
      · intro a ha
        obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
        exact hs.2 _
      · intro ret out pos hr
        have hn := hr pos
        have hret : ret ≤ bound := by
          have h := hn.1.2.2.2.2.1
          simpa [Function.update] using h
        exact ⟨hn,(stagedController_nextWords st out hs.2 (hret.trans_lt hbound) (by omega)).1⟩)
  refine hloop.conseq (fun _ hs => hs) ?_ (fun _ _ => le_rfl)
  intro o st hs
  cases o with
  | normal => exact hs.1.1
  | returned _ => exact hs

/-- The round loop changes only its cursor and index. Each call can
therefore use the fixed controller registers loaded by initialization. -/
theorem stagedControllerRounds_fixedRegisters
    {w entry vCap eCap h L P caller base count handle bound budget step stride : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem registers : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) (hbound : bound < 2^w) :
    let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem
    let Reserved := fun j (st : State) => Inv j st ∧ st.regs 0+(count-j)*step ≤ bound
    let Fixed := fun st : State => ∀ r, 4 ≤ r → st.regs r = registers r
    (∀ j < count, ∀ st, Reserved j st → (∀ r, st.regs r < 2^w) → Fixed st → st.regs 2 = j →
      MeetsContract w p entry (stagedControllerRoundContract st (Reserved (j+1)) j budget)) →
    Triple w p (fun st => Reserved 0 st ∧ (∀ r, st.regs r < 2^w) ∧ Fixed st)
      (lastLevelRoundsBody entry publishedRoundArgs) (normalPost (Inv count))
      (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) := by
  intro Inv Reserved Fixed hstep
  let J := fun j (st : State) => Reserved j st ∧ (∀ r, st.regs r < 2^w) ∧ Fixed st
  have hloop := lastLevelRounds_triple (p := p) (entry := entry) (args := publishedRoundArgs)
    count budget J hw hcount
    (fun st hs => by
      refine ⟨⟨?_,?_⟩,?_,?_⟩
      · simpa [Inv,stagedRoundStateAtStride,Function.update] using hs.1.1
      · simpa only [Function.update_of_ne (by decide : 0 ≠ 2)] using hs.1.2
      · intro r
        by_cases hr : r = 2
        · subst r
          simp [show 0 < 2^w by omega]
        · simpa only [Function.update_of_ne hr] using hs.2.1 r
      · intro r hr
        simpa only [Function.update_of_ne (show r ≠ 2 by omega)] using hs.2.2 r hr)
    (fun _ _ hs => hs.1.1.1)
    (fun j hj st hs hidx => by
      refine ⟨_,_,hstep j hj st hs.1 hs.2.1 hs.2.2 hidx,publishedRoundArgs_eval w st,?_,⟨rfl,rfl⟩,
        le_rfl,?_⟩
      · intro a ha
        obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
        exact hs.2.1 _
      · intro ret out pos hr
        have hn := hr pos
        have hret : ret ≤ bound := by
          have h := hn.1.2.2.2.2.1
          simpa [Function.update] using h
        refine ⟨hn,(stagedController_nextWords st out hs.2.1 (hret.trans_lt hbound) (by omega)).1,?_⟩
        intro r hge
        simpa only [Function.update_of_ne (show r ≠ 0 by omega),
          Function.update_of_ne (show r ≠ 2 by omega)] using hs.2.2 r hge)
  refine hloop.conseq (fun _ hs => hs) ?_ (fun _ _ => le_rfl)
  intro o st hs
  cases o with
  | normal => exact hs.1.1
  | returned _ => exact hs

/-- Run the compact controller using the contract of each live round.
The controller carries the initialized registers and remaining reservation
through the loop and publishes the completed branch table. -/
theorem stagedCompactController_of_rounds
    {w init weights round copy vCap eCap h L P caller guestL sim src handle bound budget step : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C ρ B : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hnl : (nonLoopEdges G).Nonempty) (hw : 1 < 2^w)
    (hL : st.regs 127 = L) (hP : st.regs 95 = P) (h151 : st.regs 151 = handle)
    (hguestL : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hfit : bound < 2^w)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L) :
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base s.1 handle bound L G.E s.2 ρ query st.mem
    let loopCost := (argsSize publishedRoundArgs+budget+10)*s.1+7
    st.regs 72 = H.n → st.regs 73 = H.m → 0 < H.m → queryHeap H guestL < 2^w →
    handle+1+s.1 ≤ base → ZeroFrom st.mem base →
    base+1+s.1+2*L+H.m*L+1+s.1*step ≤ bound →
    (∀ r, st.regs r < 2^w) →
    (∀ prepared : State, prepared.regs 81 = L → prepared.regs 82 = P →
      prepared.regs 91 = L → prepared.regs 104 = L →
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → prepared.regs r = st.regs r) →
      ∀ j < s.1, ∀ current : State, Inv j current →
        current.regs 0+(s.1-j)*step ≤ bound →
        (∀ r, current.regs r < 2^w) →
        (∀ r, 4 ≤ r → current.regs r = prepared.regs r) →
        current.regs 2 = j →
        MeetsContract w p round
          (stagedControllerRoundContract current
            (fun next => Inv (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound)
            j budget)) →
    ∃ o out cost, Runs w p ω (stagedCompactCollectionThen init weights round copy) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+s.1 ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle s.1 s.1 limit vCap eCap h L caller G.E s.2 ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ collectionHeaderAddress.size+20+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
          (17*(s.1+1)+19)+17) := by
  intro H base s Inv loopCost hn hm hmPos hheap hsep hz hinitEnd hwords hround
  apply stagedCompactPreparedController_runs st G ℓ oracle C ρ B query hi hweights hcopy hnl hw
    hL hP h151 hguestL hsim hsrc hfit hB hwidth hn hm hmPos hheap hsep hz hinitEnd hwords
  intro prepared h81 h82 h91 hstride hregs
  have hc : s.1 < 2^w := by omega
  simpa only [Nat.sub_zero] using
    (stagedControllerRounds_fixedRegisters H ρ query st.mem prepared.regs hw hc hfit
      (fun j hj current hreserve hword hfixed hindex =>
        hround prepared h81 h82 h91 hstride hregs j hj current hreserve.1 hreserve.2 hword hfixed hindex))

/-- The final round allocation bounds the relocated guest region,
the destination array, and the scratch used by the numeric pass. -/
theorem stagedAppendModel_guestRoom (H : MGraph) (guest : Program)
    (D guestL sim staging levels L w : ℕ) :
    let guestEnd := staging+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    let parents := guestEnd+H.m+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let old := tails+2*H.m+H.m*L
    let heap := old+H.m*L+2*L+H.n*L
    let endStretch := heap+(H.n-1)*L+H.m*edgeStretchSpace L
    endStretch < 2^w →
    guestEnd ≤ 2^w ∧ H.n+1 ≤ heap ∧ staging ≤ heap := by
  intro guestEnd parents adj tails old heap endStretch hfit
  have hGuestHeap : guestEnd ≤ heap := by
    dsimp only [heap,old,tails,adj,parents]
    omega
  have hheap : heap ≤ endStretch := by dsimp only [endStretch]; omega
  have hbase : staging+1 ≤ guestEnd := by
    dsimp only [guestEnd]
    exact Nat.add_le_add_right (Nat.le_add_right _ _) 1 |>.trans (Nat.le_add_right _ _)
  refine ⟨hGuestHeap.trans (hheap.trans hfit.le),?_,(Nat.le_succ _).trans (hbase.trans hGuestHeap)⟩
  have hpos : 1 ≤ guestEnd := (Nat.succ_le_succ (Nat.zero_le _)).trans hbase
  dsimp only [heap,old,tails,adj,parents]
  omega

/-- The cursor returned by a published round is its incoming cursor
plus the reserved stride, including the next weight pointer word. -/
theorem stagedPublishedRoundSpace_cursor (H : MGraph) (guest : Program)
    (D guestL sim levels L count vCap eCap staging : ℕ) :
    let guestEnd := staging+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    let parents := guestEnd+H.m+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let old := tails+2*H.m+H.m*L
    let heap := old+H.m*L+2*L+H.n*L
    let numericEnd := heap+(H.n-1)*L+H.m*edgeStretchSpace L+H.m*narrowWeightSpace L
    let tree := numericEnd+2*L+3*count+4
    let addresses := tree+dynGraphSize vCap eCap+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    stop+1 = staging+stagedPublishedRoundSpace H guest D guestL sim levels L count vCap eCap := by
  dsimp only [stagedPublishedRoundSpace]
  omega

/-- The packed reservation bounds the selection, arithmetic, and
publication addresses and accounts for the returned descriptor word. -/
theorem stagedPackedRoundSpace_bounds (H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap staging bound w : ℕ) :
    let K := L+(P+levels+7)/4
    let guestEnd := staging+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    let parents := guestEnd+H.m+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let old := tails+2*H.m+H.m*K
    let heap := old+H.m*K+2*K+H.n*K
    let numericEnd := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    let packedEnd := numericEnd+H.m*L+H.m*L
    let tree := packedEnd+2*L+3*count+4
    let addresses := tree+dynGraphSize vCap eCap+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    staging+stagedPackedRoundSpace H guest D guestL sim levels L P count vCap eCap ≤ bound →
    bound < 2^w →
    stop+1 = staging+stagedPackedRoundSpace H guest D guestL sim levels L P count vCap eCap ∧
    guestEnd ≤ 2^w ∧ parents < 2^w ∧ K < 2^w ∧ heap < 2^w ∧
    packedEnd < 2^w ∧ stop+1 ≤ bound := by
  intro K guestEnd parents adj tails old heap numericEnd packedEnd tree addresses stop hfit hword
  have he : stop+1 =
      staging+stagedPackedRoundSpace H guest D guestL sim levels L P count vCap eCap := by
    dsimp only [stop,addresses,tree,packedEnd,numericEnd,heap,old,tails,adj,parents,guestEnd,
      K,stagedPackedRoundSpace]
    omega
  have hs : stop+1 ≤ bound := he ▸ hfit
  have hp : packedEnd ≤ stop := by
    calc
      packedEnd ≤ tree := by
        dsimp only [tree]
        exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
      tree ≤ addresses := by
        dsimp only [addresses]
        exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
      addresses ≤ stop := by
        dsimp only [stop]
        exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hn : heap ≤ packedEnd := by
    have h₁ : heap ≤ numericEnd := by
      dsimp only [numericEnd]
      exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact h₁.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hh : parents ≤ heap := by
    calc
      parents ≤ adj := Nat.le_add_right _ _
      adj ≤ tails := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      tails ≤ old := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      old ≤ heap := (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hg : guestEnd ≤ parents := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hk : K ≤ heap :=
    (Nat.le_mul_of_pos_left K (by decide : 0 < 2)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
  have hpackedWord : packedEnd < 2^w :=
    hp.trans_lt ((Nat.lt_succ_self _).trans_le (hs.trans hword.le))
  have hheapWord : heap < 2^w := hn.trans_lt hpackedWord
  exact ⟨he,hg.trans (hh.trans hheapWord.le),hh.trans_lt hheapWord,hk.trans_lt hheapWord,
    hheapWord,hpackedWord,hs⟩

/-- The vertex-count reservation bounds selection and leaves enough
space for the remaining rounds even when the tree uses fewer records. -/
theorem stagedPackedRoundSpace_reserved (H : MGraph) (guest : Program)
    (D guestL sim levels L P vCap eCap cursor j count bound w : ℕ)
    (hj : j < count) (hbound : bound < 2^w)
    (hreserve : cursor+(count-j)*stagedPackedRoundSpace H guest D guestL sim levels
      L P H.n vCap eCap ≤ bound) :
    let step := stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap
    let guestEnd := cursor+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    guestEnd ≤ 2^w ∧ guestEnd+H.m+H.n < 2^w ∧ H.n+1 < 2^w ∧
    ∀ k ≤ H.n,
      let stopNext := cursor+stagedPackedRoundSpace H guest D guestL sim levels L P k vCap eCap
      stopNext ≤ cursor+step ∧ stopNext+(count-(j+1))*step ≤ bound := by
  intro step guestEnd
  obtain ⟨hstep,hnext⟩ := stagedRoundReservation_step hj hreserve
  obtain ⟨_,hguest,hparents,_,_,_,_⟩ :=
    stagedPackedRoundSpace_bounds H guest D guestL sim levels L P H.n vCap eCap cursor bound w
      hstep hbound
  have hone : 1 ≤ guestEnd := by
    dsimp only [guestEnd]
    exact (Nat.le_add_left 1 _).trans (Nat.le_add_right _ _)
  refine ⟨hguest,hparents,lt_of_le_of_lt ?_ hparents,?_⟩
  · simpa only [Nat.add_comm H.n 1] using
      Nat.add_le_add_right (hone.trans (Nat.le_add_right guestEnd H.m)) H.n
  · intro k hk stopNext
    have hle : stopNext ≤ cursor+step := Nat.add_le_add_left
      (stagedPackedRoundSpace_mono_count H guest D guestL sim levels L P vCap eCap hk) cursor
    exact ⟨hle,(Nat.add_le_add_right hle _).trans hnext⟩

/-- After append, the descriptor word fits in this round's reservation
and the remaining rounds still fit in the original allocation. -/
theorem stagedPackedAppend_reservation (H : MGraph) (guest : Program)
    (D guestL sim levels L P vCap eCap cursor j rounds treeCount bound w : ℕ)
    (hj : j < rounds) (hcount : treeCount ≤ H.n) (hbound : bound < 2^w)
    (hreserve : cursor+(rounds-j)*stagedPackedRoundSpace H guest D guestL sim levels
      L P H.n vCap eCap ≤ bound) :
    let step := stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap
    let stop := cursor+stagedPackedRoundSpace H guest D guestL sim levels L P treeCount vCap eCap-1
    stop+1 ≤ cursor+step ∧ stop+1 ≤ bound ∧ stop < 2^w ∧
      stop+1+(rounds-(j+1))*step ≤ bound := by
  intro step stop
  obtain ⟨_,_,_,hnext⟩ := stagedPackedRoundSpace_reserved H guest D guestL sim levels
    L P vCap eCap cursor j rounds bound w hj hbound hreserve
  obtain ⟨hstep,hrest⟩ := hnext treeCount hcount
  have hstop : stop+1 ≤ cursor+stagedPackedRoundSpace H guest D guestL sim levels
      L P treeCount vCap eCap := by
    have hpos : 0 < stagedPackedRoundSpace H guest D guestL sim levels L P treeCount vCap eCap := by
      unfold stagedPackedRoundSpace
      exact Nat.zero_lt_succ _
    dsimp only [stop]
    omega
  have hremaining := (Nat.add_le_add_right hstop _).trans hrest
  have hfit := (Nat.le_add_right (stop+1) _).trans hremaining
  exact ⟨hstop.trans hstep,hfit,(Nat.lt_succ_self _).trans_le (hfit.trans hbound.le),hremaining⟩

/-- The reserved arithmetic arrays give enough word range for the
sum used to compute scratch width and for the traversal row count. -/
theorem stagedPackedRoundSpace_precisionWords (H : MGraph) (guest : Program)
    (D guestL sim levels L P count vCap eCap cursor bound w : ℕ)
    (hL : 0 < L) (hm : 0 < H.m)
    (hspace : cursor+stagedPackedRoundSpace H guest D guestL sim levels L P count vCap eCap ≤ bound)
    (hbound : bound < 2^w) :
    P+levels+7 < 2^w ∧ levels+1 < 2^w := by
  let K := L+(P+levels+7)/4
  let guestEnd := cursor+queryOriginals H guestL+1+
    2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
  let tails := guestEnd+H.m+H.n+stagedTraversalReserve H.n levels+H.n+6*H.n
  let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
  obtain ⟨_,_,_,_,hheap,_,_⟩ :=
    stagedPackedRoundSpace_bounds H guest D guestL sim levels L P count vCap eCap cursor bound w hspace hbound
  change heap < 2^w at hheap
  have hk : P+levels+7 ≤ 4*K := by dsimp only [K]; omega
  have hmK : K ≤ H.m*K := Nat.le_mul_of_pos_left _ hm
  have hspan : 4*K ≤ heap := by
    have hsum : K+K+2*K ≤ H.m*K+H.m*K+2*K :=
      Nat.add_le_add_right (Nat.add_le_add hmK hmK) _
    have hprefix : H.m*K+H.m*K+2*K ≤ tails+2*H.m+H.m*K+H.m*K+2*K :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left _ _) _) _
    exact (show 4*K = K+K+2*K by ring) ▸ (hsum.trans (hprefix.trans (Nat.le_add_right _ _)))
  have hp := (hk.trans hspan).trans_lt hheap
  exact ⟨hp,lt_of_le_of_lt (by omega) hp⟩

/-- The new branch is allocated after the collection table and the
live numeric blocks, so publication writes a slot in the old prefix. -/
theorem stagedAppendModel_slotBounds
    {H : MGraph} {vCap eCap h L P caller base count handle bound j heap : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} {st : State}
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hj : j < count) (hheap : st.regs 0 ≤ heap) :
    let start := heap+(H.n-1)*L
    let numericEnd := start+H.m*edgeStretchSpace L+H.m*narrowWeightSpace L
    base+1+count ≤ numericEnd ∧ base+1+j < numericEnd+2*L+3*count ∧
      st.regs 0 ≤ start := by
  intro start numericEnd
  have hfloor := hs.2.2.2.1
  dsimp only [start,numericEnd]
  omega

/-- The rebuilt stretch and weight blocks use the model scale once
the controller's integer scale is decoded. -/
theorem stagedAppendModel_numericBlocks (H : MGraph) (C : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ) (h L P j scale heap : ℕ)
    (hscale : (scale : ℝ) = roundedScale C H) :
    let start := heap+(H.n-1)*L
    let afterStretch := start+H.m*edgeStretchSpace L
    (∀ i < H.m,
      (Valid mem (roundStretchAddr start L i) h L ∧
        fixVal mem (roundStretchAddr start L i) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
      (Valid mem (roundWeightAddr afterStretch L i) h L ∧
        fixVal mem (roundWeightAddr afterStretch L i) h L P =
          weights P (scale : ℝ) query (j+1) (edgeName H i))) →
    (∀ i < H.m, Valid mem (roundStretchAddr start L i) h L ∧
      fixVal mem (roundStretchAddr start L i) h L P =
        query (weights P (roundedScale C H) query j) (edgeName H i)) ∧
    (∀ i < H.m, Valid mem (roundWeightAddr afterStretch L i) h L ∧
      fixVal mem (roundWeightAddr afterStretch L i) h L P =
        weights P (roundedScale C H) query (j+1) (edgeName H i)) := by
  intro start afterStretch hblocks
  rw [hscale] at hblocks
  exact ⟨fun i hi => (hblocks i hi).1,fun i hi => (hblocks i hi).2⟩

/-- Turn the allocation and layout returned by append into the run and
postcondition required by the published round. -/
theorem stagedAppendModel_roundPost
    {w unit restore init scatter publish : ℕ} {p : Program} {ω : ℕ → Bool}
    {H T : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget
      stagingEnd dest treeCount branchPtr appendBudget step : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged numeric : State) (args : List ℕ)
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count) (hstart : st.regs 0 ≤ start)
    (hstop : start+H.m*narrowWeightSpace L ≤ stop) (hbound : stop+1 ≤ bound)
    (hstride : stop+1 = st.regs 0+step)
    (hreserve : st.regs 0+(count-j)*step ≤ bound)
    (hword : bound < 2^w)
    (hstage : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (htree : retainedStagedTreeAt H T stagingEnd dest treeCount staged.mem numeric.mem)
    (hcursor : st.regs 0 ≤ stagingEnd)
    (hvalues : ∀ i < H.m, Valid numeric.mem (roundWeightAddr start L i) h L ∧
      fixVal numeric.mem (roundWeightAddr start L i) h L P = weights P ρ query (j+1) (edgeName H i))
    (happend : ∃ layout out cl cost,
      Runs w p ω installStagedOutputLayout numeric .normal layout cl ∧
      layout.mem = numeric.mem ∧
      cl ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 ∧
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      layout .normal out cost ∧ out.regs 54 = stop ∧ out.regs 38 = start+narrowWeightSpace L-L ∧
      ZeroFrom out.mem stop ∧ out.mem (base+1+j) = branchPtr ∧
      BranchWithin out.mem branchPtr (base+1+count) stop vCap eCap L E ∧
      MinRatio.LSFAt out.mem branchPtr vCap eCap h L caller E (branches j) ∧
      (∀ a < start+H.m*narrowWeightSpace L, a ≠ base+1+j → out.mem a = numeric.mem a) ∧
      cost ≤ appendBudget) :
    let Next := fun st' =>
      stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem (j+1) st' ∧
      st'.regs 0+(count-(j+1))*step ≤ bound
    ∃ layout out cl cost,
      Runs w p ω installStagedOutputLayout numeric .normal layout cl ∧
      cl ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 ∧
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      layout .normal out cost ∧ out.regs 54 = stop ∧ out.regs 38 = start+narrowWeightSpace L-L ∧
      stop+1 < 2^w ∧ ZeroFrom out.mem stop ∧
      (stagedControllerRoundContract st Next j budget).post args st.mem (stop+1)
        (Function.update out.mem stop (out.regs 38)) ∧ cost ≤ appendBudget := by
  obtain ⟨layout,out,cl,cost,hlayout,_,hcl,hr,h54,h38,hzero,hptr,hspan,hbranch,hframe,hcost⟩ :=
    happend
  refine ⟨layout,out,cl,cost,hlayout,hcl,hr,h54,h38,hbound.trans_lt hword,hzero,
    ?_,hcost⟩
  intro pos
  refine ⟨?_,?_⟩
  · exact stagedController_appendPost (budget := budget) st out args st.mem hs hm hj hstart hstop hbound hstage
      (retainedStagedTreeAt_frame htree hcursor) hframe hzero (hptr.symm ▸ hspan)
      (hptr.symm ▸ hbranch) hvalues h38 pos
  · have hcount : count-j = count-(j+1)+1 := by omega
    rw [hcount,Nat.add_mul,Nat.one_mul] at hreserve
    simp only [Function.update_of_ne (by decide : 0 ≠ 2),Function.update_self]
    omega

/-- Publish the compact weight descriptor and reserve space for the
remaining rounds after appending the model branch. -/
theorem stagedPackedAppendModel_roundPost
    {w unit restore init scatter publish : ℕ} {p : Program} {ω : ℕ → Bool}
    {H T : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget
      stagingEnd dest treeCount branchPtr appendBudget step oldStride : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged packed : State) (args : List ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound oldStride E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count) (hstart : st.regs 0 ≤ start)
    (hstop : start+H.m*L ≤ stop) (hbound : stop+1 ≤ bound)
    (hnext : stop+1+(count-(j+1))*step ≤ bound)
    (hword : bound < 2^w)
    (hstage : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (htree : retainedStagedTreeAt H T stagingEnd dest treeCount staged.mem packed.mem)
    (hcursor : st.regs 0 ≤ stagingEnd)
    (hvalues : ∀ i < H.m, Valid packed.mem (start+i*L) h L ∧
      fixVal packed.mem (start+i*L) h L P = weights P ρ query (j+1) (edgeName H i))
    (happend : ∃ out cost,
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      packed .normal out cost ∧ out.regs 54 = stop ∧ out.regs 38 = start ∧
      ZeroFrom out.mem stop ∧ out.mem (base+1+j) = branchPtr ∧
      BranchWithin out.mem branchPtr (base+1+count) stop vCap eCap L E ∧
      MinRatio.LSFAt out.mem branchPtr vCap eCap h L caller E (branches j) ∧
      (∀ a < start+H.m*L, a ≠ base+1+j → out.mem a = packed.mem a) ∧
      cost ≤ appendBudget) :
    let Next := fun st' =>
      stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound L E branches ρ query mem (j+1) st' ∧
      st'.regs 0+(count-(j+1))*step ≤ bound
    ∃ out cost,
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      packed .normal out cost ∧ out.regs 54 = stop ∧ out.regs 38 = start ∧
      stop+1 < 2^w ∧ ZeroFrom out.mem stop ∧
      (stagedControllerRoundContract st Next j budget).post args st.mem (stop+1)
        (Function.update out.mem stop (out.regs 38)) ∧ cost ≤ appendBudget := by
  obtain ⟨out,cost,hr,h54,h38,hzero,hptr,hspan,hbranch,hframe,hcost⟩ :=
    happend
  refine ⟨out,cost,hr,h54,h38,hbound.trans_lt hword,hzero,
    ?_,hcost⟩
  intro pos
  refine ⟨?_,?_⟩
  · exact stagedController_packedAppendPost (budget := budget) st out args st.mem hs hm hj hstart hstop hbound
      (fun a ha => (retainedStagedTreeAt_frame htree hcursor a ha).trans (hstage a ha)) hframe hzero (hptr.symm ▸ hspan)
      (hptr.symm ▸ hbranch) hvalues h38 pos
  · simpa only [Function.update_of_ne (by decide : 0 ≠ 2),Function.update_self] using hnext

/-- Combine the rebuild, output layout, and branch append bounds with
the controller's staging cost for Definition 5.8 (pages 19–20). -/
theorem stagedAppendModel_linkBudget
    {w unit restore init scatter publish j budget guestL : ℕ}
    {p : Program} {ω : ℕ → Bool} {H : MGraph}
    (controller staged numeric layout : State) (Next : State → Prop) (args : List ℕ)
    (rebuild prepareOutputs : Stmt) (cn cl rebuildBudget layoutBudget appendBudget stop weights : ℕ)
    (hr : Runs w p ω rebuild staged .normal numeric cn) (hcn : cn ≤ rebuildBudget)
    (hlayout : Runs w p ω prepareOutputs numeric .normal layout cl) (hcl : cl ≤ layoutBudget)
    (happend : ∃ out cb,
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
        layout .normal out cb ∧ out.regs 54 = stop ∧ out.regs 38 = weights ∧
      stop+1 < 2^w ∧ ZeroFrom out.mem stop ∧
      (stagedControllerRoundContract controller Next j budget).post args controller.mem (stop+1)
        (Function.update out.mem stop weights) ∧ cb ≤ appendBudget) :
    let setup := 21+17*queryWeights H guestL+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
    rebuildBudget+layoutBudget+
      appendBudget+setup ≤ budget →
    ∃ mid layout out rebuildCost cl cb,
      Runs w p ω rebuild staged .normal mid rebuildCost ∧
      Runs w p ω prepareOutputs mid .normal layout cl ∧
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
        layout .normal out cb ∧ out.regs 54 = stop ∧ out.regs 38 = weights ∧
      stop+1 < 2^w ∧ ZeroFrom out.mem stop ∧
      (stagedControllerRoundContract controller Next j budget).post args controller.mem (stop+1)
        (Function.update out.mem stop weights) ∧ rebuildCost+cl+cb+setup ≤ budget := by
  intro setup hbudget
  obtain ⟨out,cb,happend,hstop,hweights,hword,hzero,hpost,hcb⟩ :=
    happend
  exact ⟨numeric,layout,out,cn,cl,cb,hr,hlayout,happend,hstop,hweights,hword,hzero,hpost,by omega⟩

end MinCostFlow.LastLevelProgram
