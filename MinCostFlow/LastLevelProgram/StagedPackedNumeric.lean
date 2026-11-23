module

public import MinCostFlow.LastLevelProgram.PackedNumericPhases

public import MinCostFlow.LastLevelProgram.StagedRoundInputs
public import MinCostFlow.LastLevelProgram.StagedAppendModel
import MinCostFlow.LastLevelProgram.OutputCapacity
public import MinCostFlow.LastLevelProgram.StagedRebuildProof
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LastLevelProgram.RepresentativeScan
import MinCostFlow.LastLevelProgram.CollectionFormat
import Mathlib.Tactic

/-!
# Inputs for the packed last-level round

Definition 5.8 (pages 19–20) uses the controller's live state to select
the tree, run fixed-point arithmetic, and publish the next branch.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Carry the caller's length blocks through staging and expose the
positive compact numerators used by widened arithmetic. -/
theorem packedNumericLengthSources {G : MGraph} {original staged : ℕ → ℕ}
    (src L Q eCap handle cursor guestL : ℕ) (hG : G.IsValid)
    (hcap : ∀ e ∈ G.E, e < eCap) (hspan : src+eCap*L ≤ handle)
    (hhandle : handle ≤ cursor) (hframe : ∀ a < handle, staged a = original a)
    (hvalid : ∀ e ∈ G.E, Valid original (src+e*L) 4 L)
    (hpos : ∀ e ∈ G.E, 0 < MinRatio.readEdgeValues original src 4 L Q G.E e) :
    let ℓ := MinRatio.readEdgeValues original src 4 L Q G.E
    let H := representativeGraph G ℓ
    let len := queryNumerator Q ∘ LSF.safeLen H ℓ
    (∀ e ∈ H.E, src+e*L+L ≤ cursor+queryWeights H guestL ∧ Valid staged (src+e*L) 4 L) ∧
    (∀ i < H.m, intVal staged (src+edgeName H i*L) 4 L = len (edgeName H i)) ∧
    (∀ i < H.m, 0 < len (edgeName H i) ∧ Fits 4 L (len (edgeName H i))) := by
  intro ℓ H len
  obtain ⟨hsource,_⟩ := stagedController_callerLengthNumerators G original src L Q hG hvalid hpos
  have hsub := (representativeGraph_subgraph hG ℓ).2.1
  have hend (e : ℕ) (he : e ∈ H.E) : src+e*L+L ≤ handle := by
    have hp := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hcap e (hsub he)))
    rw [Nat.succ_mul] at hp
    exact (show src+e*L+L ≤ src+eCap*L by omega).trans hspan
  have hblock (e : ℕ) (he : e ∈ H.E) :
      Valid staged (src+e*L) 4 L ∧ intVal staged (src+e*L) 4 L = len e ∧ 0 < len e := by
    obtain ⟨hv,hval,hpositive⟩ := hsource e he
    have heq (k : ℕ) (hk : k < L) := hframe (src+e*L+k) (by have := hend e he; omega)
    exact ⟨fun k hk => (heq k hk).trans_lt (hv k hk),(intVal_congr heq).trans hval,hpositive⟩
  refine ⟨fun e he => ⟨(hend e he).trans (hhandle.trans (Nat.le_add_right _ _)),(hblock e he).1⟩,
    fun i hi => (hblock _ (edgeName_mem hi)).2.1,?_⟩
  intro i hi
  obtain ⟨hv,he,hp⟩ := hblock _ (edgeName_mem hi)
  exact ⟨hp,he ▸ intVal_fits hv⟩

/-- The staged prefix supplies both host block tables read by numeric preparation. -/
theorem packedNumeric_sources
    {w vCap eCap L P Q base count handle bound j guestL scale stride src : ℕ}
    {G : MGraph} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} (st staged : State)
    (hG : G.IsValid) (hcap : ∀ e ∈ G.E, e < eCap)
    (hspan : src+eCap*L ≤ handle) (hhandle : handle ≤ base)
    (hvalid : ∀ e ∈ G.E, Valid mem (src+e*L) 4 L)
    (hpos : ∀ e ∈ G.E, 0 < MinRatio.readEdgeValues mem src 4 L Q G.E e)
    (hstrideGe : L ≤ stride)
    (hframe : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (hscale : (scale : ℝ) = ρ) (hstride : st.regs 104 = stride)
    (hwords : ∀ r, st.regs r < 2^w) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L Q G.E
    let H := representativeGraph G ℓ
    let len := queryNumerator Q ∘ LSF.safeLen H ℓ ∘ edgeName H
    let source := st.mem (st.regs 0-1)
    let stagingEnd := st.regs 0+queryWeights H guestL
    stagedRoundStateAtStride H vCap eCap 4 L P Q base count handle bound
      stride G.E branches ρ query mem j st →
    (∀ e ∈ H.E, src+e*L+L ≤ stagingEnd ∧ Valid staged.mem (src+e*L) 4 L) ∧
    (∀ i < H.m, intVal staged.mem (src+edgeName H i*L) 4 L = len i) ∧
    (∀ i < H.m, 0 < len i ∧ Fits 4 L (len i)) ∧
    (∀ i < H.m, source+i*stride+L ≤ stagingEnd ∧ Valid staged.mem (source+i*stride) 4 L) ∧
    ∀ i < H.m, fixVal staged.mem (source+i*stride) 4 L P =
      weights P ((scale : ℤ) : ℝ) query j (edgeName H i) := by
  intro ℓ H len source stagingEnd hs
  have ⟨_,_,_,hcur,_,_,hprefix,_,_,_⟩ := hs
  have hbase : base ≤ st.regs 0 := (Nat.le_add_right base 1).trans ((Nat.le_add_right _ count).trans hcur)
  have hf (a : ℕ) (ha : a < handle) : staged.mem a = mem a := by
    have hab := ha.trans_le hhandle
    exact (hframe a (hab.trans_le hbase)).trans (hprefix a hab)
  obtain ⟨hl,hn,hfit⟩ := packedNumericLengthSources src L Q eCap handle (st.regs 0)
    guestL hG hcap hspan (hhandle.trans hbase) hf hvalid hpos
  obtain ⟨_,_,_,hw,hvalue⟩ := stagedController_numericWeights (guestL := guestL)
    st staged hs hstrideGe hframe hscale hstride hwords
  exact ⟨hl,hn,hfit,hw,hvalue⟩

/-- The packed arithmetic uses caller length numerators and the same
integer scale as the canonical round. -/
theorem packedNumeric_modelStretches
    (G T : MGraph) (mem : ℕ → ℕ) (src L Q : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ)
    (j : ℕ) (hG : G.IsValid)
    (hvalid : ∀ e ∈ G.E, Valid mem (src+e*L) 4 L)
    (hpos : ∀ e ∈ G.E, 0 < MinRatio.readEdgeValues mem src 4 L Q G.E e) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L Q G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator Q ∘ LSF.safeLen H ℓ
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    ∀ i < H.m, roundStretch P (treeStretch (indexedGraph H).toMGraph T
      (fun e => (len (edgeName H e) : ℝ)/(2 : ℝ)^Q) i) = query v (edgeName H i) := by
  intro ℓ H P query v len htree horacle
  have hH : H.IsValid := representativeGraph_valid G ℓ
  exact stagedController_encodedStretches oracle Q P hH htree horacle
    (stagedController_callerLengthNumerators G mem src L Q hG hvalid hpos).2

/-- The runtime precondition supplies the scale and aggregate weight bounds
needed by the widened arithmetic pass. -/
theorem packedNumeric_capacity_of_runtimePre
    {w L vCap eCap multiplier g src heap : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (mem : ℕ → ℕ) (levels : ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let N := L+(P+levels+7)/4
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G
      vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,heap] mem →
    0 < L ∧ P ≤ 4*L ∧ 2*(2 : ℝ)^P < capacity 4 L ∧
      0 < scale ∧ Fits 4 N scale ∧ Fits 4 N (scale*(2 : ℤ)^P) ∧
      2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity 4 N := by
  intro ℓ H P scale N hpre
  obtain ⟨g',src',heap',heq,hbits,_,hbase,hcap⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  obtain ⟨g',src',heap',heq,hgraph,_,_,_,hpos⟩ := hbase
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  obtain ⟨e,he⟩ := hne
  have heH := (representativeGraph_shortest (ℓ := ℓ) he).1
  have hsub := (representativeGraph_subgraph hgraph.1 ℓ).2.1
  have hGne : G.E.Nonempty := ⟨_,hsub heH⟩
  have hm : 0 < H.m := Finset.card_pos.mpr ⟨_,heH⟩
  have hlen : ∀ e ∈ G.E, 0 < ℓ e := by simpa only [hbits] using hpos
  have hwidth : ∀ e ∈ G.E,
      2*(2 : ℝ)^P*MinRatio.lastLevelStretchBound G ℓ e < capacity 4 L := by
    simpa only [hbits] using hcap
  obtain ⟨hL,hP,hunit,hscale,hdenom⟩ :=
    canonicalRound_scaleCapacity G H ℓ C L levels hm hGne hlen hwidth
  have hscalePos : 0 < scale := by
    have hr : 0 < roundedScale C H :=
      (mul_pos zero_lt_two (SparseCore.lastRho_pos hm)).trans_le (roundedScale_bounds C H).1
    change (0 : ℝ) < (integerScale ⌈max 1 C⌉₊ H : ℝ) at hr
    change (0 : ℤ) < (integerScale ⌈max 1 C⌉₊ H : ℤ)
    exact_mod_cast hr
  exact ⟨hL,hP,hunit,hscalePos,hscale,hdenom,
    widenedWeightCapacity G H ℓ L P levels (Finset.card_le_card hsub) hGne hlen hwidth⟩

/-- Stretch capacity remains valid when the machine uses a coarser grid. -/
theorem packedRuntimePre_of_finer
    {w L vCap eCap multiplier g src heap P stretchPrecision : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ) (tool : Chain.LastLevelTool)
    (G : MGraph) (mem : ℕ → ℕ) (hP : P ≤ stretchPrecision)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier
      stretchPrecision allocation).initPre [g,src,L,fmt.precision,heap] mem) :
    (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,src,L,fmt.precision,heap] mem := by
  obtain ⟨graph,lengths,handle,hargs,hbits,hprec,hbase,hcap⟩ := hpre
  refine ⟨graph,lengths,handle,hargs,hbits,hprec,hbase,?_⟩
  dsimp only
  intro e he
  let len := MinRatio.readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E
  have hcapE := hcap e he
  have hB : 0 < MinRatio.lastLevelStretchBound G len e := by
    obtain ⟨graph',lengths',handle',hargs',_,_,_,_,hpos⟩ := hbase
    simp only [List.cons.injEq,and_true] at hargs'
    obtain ⟨rfl,rfl,rfl⟩ := hargs'
    have hsum : 0 ≤ ∑ f ∈ G.E, len f := Finset.sum_nonneg (fun f hf => (hpos f hf).le)
    unfold MinRatio.lastLevelStretchBound
    linarith only [div_nonneg hsum (hpos e he).le]
  have hpow : (2 : ℝ)^P ≤ (2 : ℝ)^stretchPrecision := pow_le_pow_right₀ (by norm_num) hP
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hB.le).trans_lt hcapE

/-- A caller may check the stretch capacity on a finer grid than the
controller uses. The actual grid then fits the initial unit weights and
the widened arithmetic for each round. -/
theorem packedNumeric_capacity_of_finer_runtimePre
    {w L vCap eCap multiplier g src heap stretchPrecision : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (mem : ℕ → ℕ) (levels : ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let N := L+(P+levels+7)/4
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G
      vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,heap] mem →
    0 < L ∧ P ≤ 4*L ∧ 2*(2 : ℝ)^P < capacity 4 L ∧
      0 < scale ∧ Fits 4 N scale ∧ Fits 4 N (scale*(2 : ℤ)^P) ∧
      2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity 4 N := by
  intro ℓ H P scale N hP hpre
  apply packedNumeric_capacity_of_runtimePre fmt allocation oracle C G mem levels hne
  exact packedRuntimePre_of_finer fmt allocation _ G mem hP hpre

/-- The live round's weight guarantees in the integer scale and edge
order used by the packed arithmetic and output passes. -/
theorem packedNumeric_modelBounds
    {w L vCap eCap multiplier g src heap j : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (mem : ℕ → ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C)
    (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let query := stretchQuery oracle H ℓ P
    let v := weights P (scale : ℝ) query
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G
      vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,heap] mem →
    j < H.m →
    (∀ e ∈ H.E, 1 ≤ v (j+1) e) ∧
    (∑ e ∈ H.E, v (j+1) e) ≤ 2*H.m ∧
    ∃ B : ℝ, 2*(2 : ℝ)^P*B < capacity 4 L ∧
      (∀ i < H.m, 0 ≤ query (v j) (edgeName H i) ∧ query (v j) (edgeName H i) ≤ B) ∧
      ∀ i < H.m, 0 ≤ v (j+1) (edgeName H i) ∧ v (j+1) (edgeName H i) ≤ B := by
  intro ℓ H P scale query v hpre hj
  have hscale : (scale : ℝ) = roundedScale C H := by
    change ((integerScale ⌈max 1 C⌉₊ H : ℤ) : ℝ) = (integerScale ⌈max 1 C⌉₊ H : ℝ)
    rw [Int.cast_natCast]
  obtain ⟨_,_,hmin,hsum,B,hfit,hstretch,hweight⟩ :=
    canonicalRound_modelInputs_of_runtimePre fmt allocation oracle C G mem hOracle hne hpre hj
  dsimp only [v]
  rw [hscale]
  exact ⟨hmin,hsum,B,hfit,fun i hi => hstretch _ (edgeName_mem hi),
    fun i hi => hweight _ (edgeName_mem hi)⟩

/-- Decode the exact stretches of the selected tree from the runtime
caller blocks at each live iteration. -/
theorem packedNumeric_modelStretches_of_initPre
    {w L vCap eCap multiplier g src heap j : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C γ : ℝ) (G T : MGraph) (mem : ℕ → ℕ) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,heap] mem →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    ∀ i < H.m, roundStretch P (treeStretch (indexedGraph H).toMGraph T
      (fun e => (len e : ℝ)/(2 : ℝ)^fmt.precision) i) =
      query (weights P (scale : ℝ) query j) (edgeName H i) := by
  intro ℓ H P scale query v len hpre htree horacle
  have hscale : (scale : ℝ) = roundedScale C H := Int.cast_natCast _
  rw [hscale]
  obtain ⟨hgraph,_,hblocks⟩ := runtimeEndpoints_inputs_of_initPre fmt _ allocation G mem hpre
  exact packedNumeric_modelStretches G T mem src L fmt.precision oracle C γ j hgraph.1
    (fun e he => (hblocks e he).2.1) (fun e he => (hblocks e he).2.2.2) htree horacle

/-- The runtime precondition and selected canonical tree discharge the
model premises of the widened arithmetic procedure. -/
theorem packedNumeric_liveModel
    {w L vCap eCap multiplier g src heap j : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C γ : ℝ) (G T : MGraph) (mem : ℕ → ℕ) (levels : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,heap] mem →
    j < H.m →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    0 < scale ∧ 2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity 4 (L+(P+levels+7)/4) ∧
    (∀ e ∈ H.E, 1 ≤ weights P (scale : ℝ) query (j+1) e) ∧
    (∑ e ∈ H.E, weights P (scale : ℝ) query (j+1) e) ≤ 2*H.m ∧
    ∀ i < H.m, roundStretch P (treeStretch (indexedGraph H).toMGraph T
      (fun e => (len e : ℝ)/(2 : ℝ)^fmt.precision) i) =
      query (weights P (scale : ℝ) query j) (edgeName H i) := by
  intro ℓ H P scale query v len hpre hj ht ho
  obtain ⟨_,_,_,hscale,_,_,hwidth⟩ :=
    packedNumeric_capacity_of_runtimePre fmt allocation oracle C G mem levels hne hpre
  obtain ⟨hmin,hsum,_⟩ := packedNumeric_modelBounds fmt allocation oracle C G mem hOracle hne hpre hj
  exact ⟨hscale,hwidth,hmin,hsum,
    packedNumeric_modelStretches_of_initPre fmt allocation oracle C γ G T mem hpre ht ho⟩

/-- Link the installed numeric procedure for a live round directly
from the runtime input and the tree returned by the canonical selector. -/
theorem packedNumeric_live_meetsContract
    {w L vCap eCap multiplier g src handle numeric stretch update tables stretches narrow widen copy copyLimbs
      traverse distance ancestors edgeQuery distanceStep ancestorRow add ancestorLookup stretchEdge
      path stretchLength sub neg fixedDiv extend weightStep mul integerDiv : ℕ}
    {p : Program} (fmt : Format w) (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ)
    (G T : MGraph) (mem : ℕ → ℕ) (cursor levels j : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hbits : 14 ≤ w) (hw : 6 < 2^w) (hcopy : p.HasAt copy [copyWords]) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H
    let N := L+(P+levels+7)/4
    let parents := cursor+1+H.m+H.n
    let edges := parents+(levels+1)*H.n
    let depths := edges+H.n
    let queue := depths+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let records := adj+H.n
    let tails := records+6*H.n
    let heads := tails+H.m
    let lengths := tails+2*H.m
    let old := lengths+H.m*N
    let denom := old+H.m*N+N
    let dist := old+H.m*N+2*N
    let heap := dist+H.n*N
    p.procs[numeric]? = some (stretchWeightRoundBody stretch update) →
    p.procs[stretch]? = some (treeStretchRoundBody tables stretches) →
    p.procs[tables]? = some (buildTreeTablesBody traverse distance ancestors) →
    p.procs[traverse]? = some traverseTreeQueueBody →
    p.procs[distance]? = some (rootedDistanceBody distanceStep) →
    p.procs[distanceStep]? = some (rootDistanceStepBody add copy) →
    p.HasAt add (Num.addCarryModule add 4) →
    p.procs[ancestors]? = some (rootedAncestorTableBody ancestorRow) →
    p.procs[ancestorRow]? = some ancestorRowBody →
    p.procs[stretches]? = some (rootedStretchRoundBody edgeQuery) →
    p.procs[edgeQuery]? = some (edgeStretchQueryBody ancestorLookup stretchEdge) →
    p.procs[ancestorLookup]? = some rootedTreeAncestorBody →
    p.procs[stretchEdge]? = some (edgeStretchBody path stretchLength) →
    p.procs[path]? = some (pathLengthBody sub add) →
    p.procs[stretchLength]? = some (stretchFromLengthBody add neg fixedDiv) →
    p.HasAt sub (Num.subtractModule sub 4) →
    p.HasAt neg (Num.negateCarryModule neg 4) →
    p.HasAt fixedDiv (Num.fixedDivideModule fixedDiv 4) →
    p.procs[update]? = some (weightRoundBody narrow) →
    p.procs[narrow]? = some (narrowWeightBody widen copyLimbs) →
    p.procs[widen]? = some (widenWeightBody extend weightStep) →
    p.HasAt extend (Num.signExtendModule extend 4) →
    p.procs[weightStep]? = some (weightUpdateBody mul integerDiv add) →
    p.HasAt mul (Num.fixedMultiplyModule mul 4) →
    p.HasAt integerDiv (Num.integerDivideModule integerDiv 4) →
    p.HasAt copyLimbs (Num.copyModule copyLimbs) →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,handle] mem →
    j < H.m →
    (indexedGraph H).Valid →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    heap+(H.n-1)*N+H.m*edgeStretchSpace N+H.m*narrowWeightSpace N < 2^w →
    MeetsContract w p numeric (stretchWeightRoundContract w 4 fmt.precision (indexedGraph H).toMGraph
      T H 0 len adj parents edges depths queue H.n levels dist lengths N heap tails heads P
      old N denom j scale query) := by
  intro ℓ H P scale query v len N parents edges depths queue adj records tails heads lengths old denom dist heap
    hn hs htab htrav hdist hstep hadd hanc hrow hstr hquery hlookup hedge hpath hlength
    hsub hneg hdiv hu hnar hwid hext hweight hmul hidiv hlimbs hpre hj hv ht ho hroom
  obtain ⟨hscale,hcap,hmin,hsum,hstretch⟩ :=
    packedNumeric_liveModel fmt allocation oracle C γ G T mem levels hOracle hne hpre hj ht ho
  exact packedNumericProcedures_meetContract H T len cursor levels L P j scale query hv ht
    hbits hw (Nat.zero_lt_of_lt hj) hcopy hn hs htab htrav hdist hstep hadd hanc hrow hstr
    hquery hlookup hedge hpath hlength hsub hneg hdiv hu hnar hwid hext hweight hmul hidiv hlimbs
    hscale hcap hmin hsum hstretch hroom

set_option maxHeartbeats 600000 in
/-- The fixed arithmetic module supplies every procedure used by the
live packed numeric round. -/
theorem packedRoundArithmeticModule_live_meetsContract
    {w L vCap eCap multiplier g src handle b stretchPrecision : ℕ} {p : Program}
    (fmt : Format w) (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ)
    (G T : MGraph) (mem : ℕ → ℕ) (cursor levels j : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hbits : 14 ≤ w) (hw : 6 < 2^w) (hp : p.HasAt b (packedRoundArithmeticModule b)) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let scale := (integerScale ⌈max 1 C⌉₊ H : ℤ)
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H
    let N := L+(P+levels+7)/4
    let parents := cursor+1+H.m+H.n
    let edges := parents+(levels+1)*H.n
    let depths := edges+H.n
    let queue := depths+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let records := adj+H.n
    let tails := records+6*H.n
    let heads := tails+H.m
    let lengths := tails+2*H.m
    let old := lengths+H.m*N
    let denom := old+H.m*N+N
    let dist := old+H.m*N+2*N
    let heap := dist+H.n*N
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] mem →
    j < H.m →
    (indexedGraph H).Valid →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    heap+(H.n-1)*N+H.m*edgeStretchSpace N+H.m*narrowWeightSpace N < 2^w →
    MeetsContract w p b (stretchWeightRoundContract w 4 fmt.precision (indexedGraph H).toMGraph
      T H 0 len adj parents edges depths queue H.n levels dist lengths N heap tails heads P
      old N denom j scale query) := by
  intro ℓ H P scale query v len N parents edges depths queue adj records tails heads lengths old denom dist heap
  obtain ⟨hcopy,hadd,hsub,hneg,hext,hdiv,hmul,hidiv,hlimbs⟩ := packedRoundArithmeticModule_helpers hp
  have atIndex (i : ℕ) (hi : i < 104) :=
    hp.get (i := i) (by rwa [packedRoundArithmeticModule_length])
  intro hP hpre
  have hpreLive := packedRuntimePre_of_finer fmt allocation _ G mem hP hpre
  exact packedNumeric_live_meetsContract fmt allocation oracle C γ G T mem cursor levels j
    hOracle hne hbits hw hcopy
    (atIndex 0 (by decide)) (atIndex 1 (by decide)) (atIndex 2 (by decide))
    (atIndex 3 (by decide)) (atIndex 4 (by decide)) (atIndex 5 (by decide)) hadd
    (atIndex 6 (by decide)) (atIndex 7 (by decide)) (atIndex 8 (by decide))
    (atIndex 9 (by decide)) (atIndex 10 (by decide)) (atIndex 11 (by decide))
    (atIndex 12 (by decide)) (atIndex 15 (by decide)) hsub hneg hdiv
    (atIndex 13 (by decide)) (atIndex 30 (by decide)) (atIndex 14 (by decide)) hext
    (atIndex 31 (by decide)) hmul hidiv hlimbs hpreLive

/-- The selected tree and caller precondition supply the arithmetic
contract and the compact output bounds at the same controller grid. -/
theorem packedRoundArithmeticModule_live_bounds
    {w L vCap eCap multiplier g src handle b stretchPrecision : ℕ} {p : Program}
    (fmt : Format w) (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ)
    (G T : MGraph) (mem : ℕ → ℕ) (cursor levels j : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hbits : 14 ≤ w) (hw : 6 < 2^w) (hp : p.HasAt b (packedRoundArithmeticModule b)) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let D := ⌈max 1 C⌉₊
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let len := queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H
    let K := L+(P+levels+7)/4
    let parents := cursor+1+H.m+H.n
    let edges := parents+(levels+1)*H.n
    let depths := edges+H.n
    let queue := depths+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let heads := tails+H.m
    let lengths := tails+2*H.m
    let old := lengths+H.m*K
    let denom := old+H.m*K+K
    let dist := old+H.m*K+2*K
    let heap := dist+H.n*K
    let stop := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] mem →
    j < H.m →
    (indexedGraph H).Valid →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    0 < L ∧ Fits 4 K (integerScale D H : ℤ) ∧ Fits 4 K (integerScale D H*(2 : ℤ)^P) ∧
    (∃ B : ℝ, 2*(2 : ℝ)^P*B < capacity 4 L ∧
      (∀ i < H.m, 0 ≤ query v (edgeName H i) ∧ query v (edgeName H i) ≤ B) ∧
      ∀ i < H.m, 0 ≤ weights P (roundedScale C H) query (j+1) (edgeName H i) ∧
        weights P (roundedScale C H) query (j+1) (edgeName H i) ≤ B) ∧
    (stop < 2^w →
      MeetsContract w p b (stretchWeightRoundContract w 4 fmt.precision (indexedGraph H).toMGraph
        T H 0 len adj parents edges depths queue H.n levels dist lengths K heap tails heads P
        old K denom j (integerScale D H : ℤ) query)) := by
  intro ℓ H P D query v len K parents edges depths queue adj tails heads lengths old denom dist heap
    stop hP hpre hj hv ht ho
  have hpreLive := packedRuntimePre_of_finer fmt allocation _ G mem hP hpre
  obtain ⟨hL,_,_,_,hscale,hdenom,_⟩ :=
    packedNumeric_capacity_of_runtimePre fmt allocation oracle C G mem levels hne hpreLive
  obtain ⟨_,_,B,hfit,hstretch,hweight⟩ :=
    packedNumeric_modelBounds fmt allocation oracle C G mem hOracle hne hpreLive hj
  have hcast : ((integerScale D H : ℤ) : ℝ) = roundedScale C H := Int.cast_natCast _
  rw [hcast] at hstretch hweight
  exact ⟨hL,hscale,hdenom,⟨B,hfit,hstretch,hweight⟩,
    packedRoundArithmeticModule_live_meetsContract fmt allocation oracle C γ G T mem cursor levels j
      hOracle hne hbits hw hp hP hpre hj hv ht ho⟩

/-- A selected tree on the non-loop representatives fits the vertex
tables used by the packed rebuild. -/
theorem packedNumeric_treeBounds (G T : MGraph) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hG : G.IsValid) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    LSF.IsLSST I.toMGraph (LSF.safeLen H ℓ ∘ edgeName H) (v ∘ edgeName H) γ T →
    I.Valid ∧ 0 < H.m ∧
      (∀ a ∈ I.toMGraph.V, ∀ b ∈ I.toMGraph.V, I.toMGraph.Connected a b) ∧
      T.E.card ≤ H.n ∧ T.V.card ≤ H.n ∧ H.n ≤ H.m+1 ∧
      (∀ i ∈ T.E, i < H.m) := by
  intro H I ht
  obtain ⟨hv,hm,hc⟩ := stagedController_compactGraph G ℓ hG hne hconn
  obtain ⟨he,hv',hindex,hnm⟩ := stagedController_selectedTreeBounds H T _ _ γ hv hc ht
  exact ⟨hv,hm,hc,he ▸ Nat.le_succ _,hv'.le,hnm,hindex⟩

/-- The branch slot belongs to the existing collection, below the fresh
records allocated after the packed numeric blocks. -/
theorem packedNumeric_appendSlot
    {H : MGraph} {vCap eCap h L P caller base count handle bound stride j : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} {st : State} {start : ℕ}
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hj : j < count) (hstart : st.regs 0 ≤ start) (treeCount : ℕ) :
    let finish := start+H.m*L+H.m*L
    base+1+count ≤ finish ∧ base+1+j < finish+2*L+3*treeCount := by
  intro finish
  have hfloor := hs.2.2.2.1
  dsimp only [finish]
  omega

/-- Branch append consumes the packed stretches at the model scale.
The next weight block starts directly after the stretch block. -/
theorem packedNumeric_appendBlocks (H : MGraph) (C : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ) (packed : State) (L P j scale start : ℕ)
    (hscale : (scale : ℝ) = roundedScale C H)
    (hstretches : ∀ i < H.m, Valid packed.mem (start+i*L) 4 L ∧
      fixVal packed.mem (start+i*L) 4 L P =
        query (weights P ((scale : ℤ) : ℝ) query j) (edgeName H i))
    (hweights : ∀ i < H.m, Valid packed.mem (start+H.m*L+i*L) 4 L ∧
      fixVal packed.mem (start+H.m*L+i*L) 4 L P =
        weights P ((scale : ℤ) : ℝ) query (j+1) (edgeName H i)) :
    (∀ i < H.m, Valid packed.mem (start+i*L) 4 L ∧
      fixVal packed.mem (start+i*L) 4 L P =
        query (weights P (roundedScale C H) query j) (edgeName H i)) ∧
    (∀ i < H.m, Valid packed.mem (start+H.m*L+i*L) 4 L ∧
      fixVal packed.mem (start+H.m*L+i*L) 4 L P =
        weights P (roundedScale C H) query (j+1) (edgeName H i)) := by
  rw [Int.cast_natCast, hscale] at hstretches hweights
  exact ⟨hstretches,hweights⟩

/-- The controller invariant preserves the prepared endpoint and length
tables through each round. The staged guest prefix is copied from those
same tables. -/
theorem packedController_guestPrefix
    {vCap eCap h L P caller base count handle bound j stride src guestL : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} {st staged : State}
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hbase : src+queryWeights H guestL = base)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i)) :
    ∀ i < queryWeights H guestL, st.mem (src+i) = mem (src+i) ∧
      staged.mem (st.regs 0+i) = mem (src+i) := by
  obtain ⟨_,_,_,_,_,_,hframe,_,_,_⟩ := hs
  intro i hi
  have he := hframe (src+i) (by omega)
  exact ⟨he,(hcopy i hi).trans he⟩

/-- The original graph and name tables survive each round below the
collection base. Branch append can read them in the live controller state. -/
theorem packedController_appendTables
    {vCap eCap h L P caller base count handle bound j stride g vertices indices names repNames guestL : ℕ}
    {G H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} {st staged : State}
    (ℓ : ℕ → ℝ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hg : DynSpanner.Program.DynGraphAt mem g vCap eCap G)
    (hgraph : g+DynSpanner.Program.dynGraphSize vCap eCap ≤ base)
    (hvEnd : vertices+H.n ≤ base) (hiEnd : indices+G.m ≤ base) (hnEnd : names+G.m ≤ base)
    (hv : ∀ i < H.n, mem (vertices+i) = vertexName H i)
    (hi : ∀ i < G.m, mem (indices+i) = branchStretchIndex G ℓ (edgeName G i))
    (hn : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hrEnd : repNames+H.m ≤ base)
    (hr : ∀ i < H.m, mem (repNames+i) = edgeName H i)
    (hstage : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (ht : ∀ i < H.m, staged.mem (st.regs 0+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, staged.mem (st.regs 0+(H.m+i)) = (indexedGraph H).head i) :
    DynSpanner.Program.DynGraphAt st.mem g vCap eCap G ∧
    (∀ i < H.n, st.mem (vertices+i) = vertexName H i) ∧
    (∀ i < G.m, st.mem (indices+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
    (∀ i < G.m, st.mem (names+i) = edgeName G i) ∧
    repNames+H.m ≤ st.regs 0+queryWeights H guestL ∧
    vertices+H.n ≤ st.regs 0+queryWeights H guestL ∧
    (∀ i < H.m, staged.mem (repNames+i) = edgeName H i ∧
      staged.mem (st.regs 0+i) = (indexedGraph H).tail i ∧
      staged.mem (st.regs 0+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.n, staged.mem (vertices+i) = vertexName H i) := by
  obtain ⟨_,_,_,hcur,_,_,hframe,_,_,_⟩ := hs
  have hb : base ≤ st.regs 0 := by omega
  have hv' (i : ℕ) (hi : i < H.n) := (hframe (vertices+i) (by omega)).trans (hv i hi)
  obtain ⟨hr',hvEnd',hp,hv''⟩ := stagedController_appendNames H st.mem staged.mem repNames vertices
    (st.regs 0) guestL hstage (hrEnd.trans hb) (hvEnd.trans hb)
    (fun i hi => (hframe _ (by omega)).trans (hr i hi)) hv' ht hh
  exact ⟨representativeGraph_frame hg (fun a _ ha => hframe a (ha.trans_le hgraph)),
    hv',
    fun i hi' => (hframe _ (by omega)).trans (hi i hi'),
    fun i hi' => (hframe _ (by omega)).trans (hn i hi'),hr',hvEnd',hp,hv''⟩

/-- Recover the endpoint arrays and encoded lengths in the controller
memory before staging the next selector call. -/
theorem packedController_selectorTables
    {vCap eCap h L P caller base count handle bound j stride src guestL Q : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} {st : State}
    (len : ℕ → ℝ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hbase : src+queryWeights H guestL = base)
    (ht : ∀ i < H.m, mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i))))) :
    (∀ i < H.m, st.mem (src+i) = (indexedGraph H).tail i) ∧
    (∀ i < H.m, st.mem (src+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.m, ListAt st.mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i))))) := by
  obtain ⟨_,_,_,_,_,_,hframe,_,_,_⟩ := hs
  have hb : base = src+2*H.m+H.m*guestL := by
    rw [← hbase]
    unfold queryWeights queryLengths
    omega
  refine ⟨fun i hi => (hframe _ (by omega)).trans (ht i hi),
    fun i hi => (hframe _ (by omega)).trans (hh i hi),?_⟩
  intro i hi k hk
  have hm := Nat.mul_le_mul_right guestL (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  have hk' : k < guestL := by simpa only [encodeLimbs_length] using hk
  exact (hframe _ (by simpa only [queryLengths] using (show src+2*H.m+i*guestL+k < base by omega))).trans (hlen i hi k hk)

/-- The live round can call the canonical selector using the original
prepared endpoint and length tables preserved by the controller. -/
theorem packedController_selectorCall
    {w vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ) (len : ℕ → ℝ) (C : ℝ)
    (hready : GraphQueryReady C H len (weights P ρ query j))
    (hguestL : guestL = roundQueryLimbs C H len)
    (hguestQ : Q = roundQueryPrecision C H len)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (hbase : src+queryWeights H guestL = base)
    (ht : ∀ i < H.m, mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i)))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hprec : P+guestL < 2^w)
    (guest : Program) (D : ℕ)
    (hspace : st.regs 0+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL) ≤ 2^w) :
    let cursor := st.regs 0
    let source := st.mem (cursor-1)
    let input := stagedGuestArgs H guestL sim cursor source stride P Q ++ List.replicate 7 0 ++ [L]
    evalArgs w staged convertedGuestCallArgs = some input ∧ (∀ a ∈ input, a < 2^w) ∧
    convertedSelectorReady w H guestL sim cursor source stride P Q L (queryNumerator Q ∘ len)
      (queryNumerator Q ∘ weights P ρ query j) input staged.mem ∧
    staged.regs 0 = H.n ∧ staged.regs 1 = H.m ∧ staged.regs 2 = guestL ∧ staged.regs 3 = sim ∧
    (∀ i < H.m, staged.mem (cursor+i) = (indexedGraph H).tail i) ∧
    (∀ i < H.m, staged.mem (cursor+(H.m+i)) = (indexedGraph H).head i) := by
  obtain ⟨ht',hh',hlen'⟩ := packedController_selectorTables len hs hbase ht hh hlen
  obtain ⟨he,ha,hr⟩ := stagedController_canonicalSelectorCall st staged pos len C hready hguestL hguestQ hs
    hstrideGe hkeep hcursor hweight hn hm hguest hsim hstride hP hQ hhost hbound hwords
    hcopy hframe ht' hh' hlen' hw hL hprec guest D hspace

  obtain ⟨h0,h1,h2,h3⟩ := stagedController_graphRegisters st staged pos hkeep
  obtain ⟨hTail,hHead,_⟩ := stagedGuestPrefix_arrays H guestL src (st.regs 0)
    (queryNumerator Q ∘ len) st.mem staged.mem hcopy ht' hh' hlen'
  exact ⟨he,ha,hr,h0.trans hn,h1.trans hm,h2.trans hguest,h3.trans hsim,hTail,hHead⟩

/-- Run low-stretch tree selection and deduplication on the staged
controller input, retaining the compact tree for arithmetic. -/
theorem packedController_treeSelection_runs
    {w select dedup guestCost levels vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {p : Program} {ω : ℕ → Bool} {H T : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ) (len : ℕ → ℝ) (C : ℝ)
    (hready : GraphQueryReady C H len (weights P ρ query j))
    (hguestL : guestL = roundQueryLimbs C H len)
    (hguestQ : Q = roundQueryPrecision C H len)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (hbase : src+queryWeights H guestL = base)
    (ht : ∀ i < H.m, mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i)))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hprec : P+guestL < 2^w)
    (guest : Program) (D : ℕ)
    (hstagedWords : ∀ r, staged.regs r < 2^w)
    (hq : st.regs 0+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL) ≤ 2^w →
      MeetsContract w p select
      (convertedTreeSelectorContract w guest D H T guestL sim (st.regs 0) guestCost
        (st.mem (st.regs 0-1)) stride L P Q (queryNumerator Q ∘ len)
        (queryNumerator Q ∘ weights P ρ query j)))
    (hd : p.procs[dedup]? = some dedupSelectedTreeBody)
    (hv : (indexedGraph H).Valid)
    (hc : ∀ a ∈ (indexedGraph H).toMGraph.V, ∀ b ∈ (indexedGraph H).toMGraph.V,
      (indexedGraph H).toMGraph.Connected a b)
    (γ : ℝ) (htree : LSF.IsLSST (indexedGraph H).toMGraph
      (len ∘ edgeName H) (weights P ρ query j ∘ edgeName H) γ T) :
    let cursor := st.regs 0
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    let guestEnd := cursor+queryOriginals H guestL+1+2^width
    j < count →
    cursor+(count-j)*stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap ≤ bound →
    ∃ selected cost, Runs w p ω (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      staged .normal selected cost ∧
      selectedTreeAt H T (cursor+queryWeights H guestL) (guestEnd+H.m)
        (selected.regs 13) staged.mem selected.mem ∧
      selected.regs 12 = cursor+queryOriginals H guestL+2^width ∧
      selected.regs 13 ≤ H.n ∧ (∀ r, selected.regs r < 2^w) ∧
      (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r) ∧
      selected.regs 0 = H.n ∧ selected.regs 1 = H.m ∧ selected.regs 5 = cursor ∧
      (∀ i < H.m, staged.mem (cursor+i) = (indexedGraph H).tail i) ∧
      (∀ i < H.m, staged.mem (cursor+(H.m+i)) = (indexedGraph H).head i) ∧
      cost ≤ argsSize convertedGuestCallArgs +
        convertedTreeSelectorCost w guest D H guestL sim guestCost +
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
        40*H.n+17 := by
  intro cursor width guestEnd hj hreserve
  obtain ⟨hspace,hroom,hword,_⟩ := stagedPackedRoundSpace_reserved H guest D guestL sim levels L P
    vCap eCap cursor j count bound w hj hbound hreserve
  obtain ⟨he,ha,hr,h0,h1,h2,h3,ht',hh'⟩ :=
    packedController_selectorCall st staged pos len C hready hguestL hguestQ hs
      hstrideGe hkeep hcursor hweight hn hm hguest hsim hstride hP hQ hhost hbound hwords
      hcopy hframe hbase ht hh hlen hw hL hprec guest D hspace
  obtain ⟨selected,cost,hRun,hTree,hCursor,hCount,hWords,hKeep,hCost⟩ :=
    packedTreeSelection_runs staged H T _ _ _ _ γ _ (hq hspace) he ha hr htree ht' hh'
      h0 h1 h2 h3 hcursor hd (by omega) hv hc hstagedWords hroom hword
  exact ⟨selected,cost,hRun,hTree,hCursor,hCount,hWords,hKeep,
    (hKeep 0 (by decide) (by decide)).trans h0,
    (hKeep 1 (by decide) (by decide)).trans h1,
    (hKeep 5 (by decide) (by decide)).trans hcursor,ht',hh',hCost⟩

/-- Selection keeps the numeric inputs from the controller's argument
list, with the weight address installed separately by staging. -/
theorem packedController_selectedNumericRegisters
    (st staged selected : State) (pos : ℕ)
    (hstaged : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hselected : ∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r)
    (hweight : staged.regs 31 = st.mem (st.regs 0-1)) :
    selected.regs 14 = st.regs 86 ∧ selected.regs 19 = st.regs 91 ∧
      selected.regs 23 = st.regs 95 ∧ selected.regs 27 = st.regs 99 ∧
      selected.regs 28 = st.regs 100 ∧ selected.regs 31 = st.mem (st.regs 0-1) ∧
      selected.regs 32 = st.regs 104 ∧ selected.regs 35 = st.regs 107 := by
  refine ⟨?_,?_,?_,?_,?_,(hselected 31 (by decide) (by decide)).trans hweight,?_,?_⟩
  all_goals
    rw [hselected _ (by decide) (by decide), hstaged _ (by decide) (by decide) (by decide) (by decide)]
    rfl

/-- Run the widened arithmetic and compact packing for the selected
tree, using the runtime format and the preserved caller tables. -/
theorem packedController_selectedNumeric_runs
    {w arithmetic buffer L vCap eCap multiplier g src handle stretchPrecision : ℕ}
    {guest p : Program} {ω : ℕ → Bool} (fmt : Format w) (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ)
    (G T : MGraph) (mem : ℕ → ℕ) (staged selected : State)
    (cursor guestL width levels names weightSrc bound sim j : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hbits : 14 ≤ w) (hw : 6 < 2^w)
    (harith : p.HasAt arithmetic (packedRoundArithmeticModule arithmetic))
    (hbuffer : p.HasAt buffer (packedRoundBufferModule buffer arithmetic)) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let D := ⌈max 1 C⌉₊
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let next := weights P (roundedScale C H) query (j+1)
    let treeCount := selected.regs 13
    let treeCursor := cursor+queryOriginals H guestL+2^width
    let dest := treeCursor+1+H.m
    let stagingEnd := cursor+queryWeights H guestL
    let K := L+(P+levels+7)/4
    let adj := dest+H.n+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
    let stop := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] mem →
    j < H.m → bound < 2^w → H.n ≤ 2^(levels+1) →
    width = paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL) →
    cursor+(H.m-j)*stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap ≤ bound →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T →
    selectedTreeAt H T stagingEnd dest treeCount staged.mem selected.mem →
    selected.regs 12 = treeCursor →
    selected.regs 0 = H.n → selected.regs 1 = H.m → selected.regs 5 = cursor →
    selected.regs 14 = levels → selected.regs 19 = L → selected.regs 23 = P →
    selected.regs 27 = src → selected.regs 28 = names → selected.regs 31 = weightSrc →
    selected.regs 32 = L → selected.regs 35 = integerScale D H →
    (∀ r, selected.regs r < 2^w) →
    (∀ i < H.m, staged.mem (cursor+i) = (indexedGraph H).tail i) →
    (∀ i < H.m, staged.mem (cursor+(H.m+i)) = (indexedGraph H).head i) →
    names+H.m ≤ stagingEnd → (∀ i < H.m, staged.mem (names+i) = edgeName H i) →
    handle ≤ cursor → (∀ a < handle, staged.mem a = mem a) →
    (∀ i < H.m, weightSrc+i*L+L ≤ stagingEnd ∧ Valid staged.mem (weightSrc+i*L) 4 L) →
    (∀ i < H.m, fixVal staged.mem (weightSrc+i*L) 4 L P = v (edgeName H i)) →
    ∃ computed packed cn cp,
      Runs w p ω (prepareAndRunWideStagedNumericBody (arithmetic+16) buffer (buffer+1)
        (buffer+2) (buffer+3) arithmetic) selected .normal computed cn ∧
      Runs w p ω (publishableWideOutputs (buffer+6)) computed .normal packed cp ∧
      packed.regs 16 = stop+H.m*L+H.m*L ∧
      packed.regs 36 = stop ∧ packed.regs 37 = L ∧
      packed.regs 38 = stop+H.m*L ∧ packed.regs 39 = L ∧
      (∀ r, r ≠ 15 → r ≠ 16 → r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34,36,37,38,39] : List ℕ) →
        packed.regs r = selected.regs r) ∧
      ZeroFrom packed.mem (stop+H.m*L+H.m*L) ∧
      (∀ a < stagingEnd, packed.mem a = staged.mem a) ∧
      stagingEnd ≤ dest ∧ dest+H.n ≤ packed.regs 16 ∧ cursor ≤ stop ∧
      retainedStagedTreeAt H T stagingEnd dest treeCount staged.mem packed.mem ∧
      (∀ i < H.m, Valid packed.mem (stop+i*L) 4 L ∧
        fixVal packed.mem (stop+i*L) 4 L P = query v (edgeName H i)) ∧
      (∀ i < H.m, Valid packed.mem (stop+H.m*L+i*L) 4 L ∧
        fixVal packed.mem (stop+H.m*L+i*L) 4 L P = next (edgeName H i)) ∧
      cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom 24)+112*treeCount+stagedNumericFactor K levels*(H.m+1)+13+
        (stagedScratchWidthExpr.size+
          argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
            [.reg 64])+37+34*H.m+(2*((30*K+90)*H.m+20)+56*K+72))+1 ∧
      cp ≤ 2*((35*L+60)*H.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro ℓ H P D query v next treeCount treeCursor dest stagingEnd K adj tails heap stop hP hpre hj hbound hlevels
    hwidth hreserve htree horacle hselected h12 h0 h1 h5 h14 h19 h23 h27 h28 h31 h32 h35
    hwords ht hh hnEnd hnames hhandle hframe hweights hweight
  obtain ⟨hgraph,_,hblocks⟩ := runtimeEndpoints_inputs_of_initPre fmt _ allocation G mem hpre
  obtain ⟨hv,hm,hconnected,hE,hV,hnm,_⟩ := packedNumeric_treeBounds G T ℓ v γ
    hgraph.1 hne hconn htree
  have hn : 0 < H.n := hv.1
  obtain ⟨hL,hscale,hdenom,⟨B,hfit,hs,hwgt⟩,hcontract⟩ :=
    packedRoundArithmeticModule_live_bounds fmt allocation oracle C γ G T mem treeCursor levels j
      hOracle hne hbits hw harith hP hpre hj hv htree horacle
  have hspan : src+eCap*L ≤ handle := by
    obtain ⟨g',src',handle',hargs,_,_,hbase,_⟩ := hpre
    simp only [List.cons.injEq,and_true,true_and] at hargs
    obtain ⟨rfl,rfl,rfl⟩ := hargs
    obtain ⟨g',src',handle',hargs,_,_,hspan,_,_⟩ := hbase
    simp only [List.cons.injEq,and_true] at hargs
    obtain ⟨rfl,rfl,rfl⟩ := hargs
    exact hspan
  obtain ⟨hlengths,hlen,hLenFit⟩ :=
    packedNumericLengthSources src L fmt.precision eCap handle cursor guestL hgraph.1
      hgraph.2.2.1 hspan hhandle hframe
      (fun e he => (hblocks e he).2.1) (fun e he => (hblocks e he).2.2.2)
  have hcast : (((integerScale D H : ℕ) : ℤ) : ℝ) = roundedScale C H := Int.cast_natCast _
  have hcontract' := hcontract
  rw [← h12] at hcontract'
  have hdestEq : dest = cursor+queryOriginals H guestL+1+2^width+H.m := by
    dsimp only [dest,treeCursor]
    omega
  obtain ⟨computed,packed,cn,cp,hnr,hpr,h16,h36,h37,h38,h39,hkeep,hzero,hprefix,
    hsep,hdest,hcursor,htree',hstretches,hnext,hcn,hcp⟩ :=
    selectedWideNumeric_publish_runs (ω := ω) (Q := fmt.precision) guest staged selected H T H
      cursor guestL width levels src names weightSrc L L P (integerScale D H) treeCount D sim
      j H.m vCap eCap bound hwidth hj hbound hreserve (hdestEq ▸ hselected) h12 harith hbuffer
      (by omega) hn h0 h1 h5 h14 h19 h23 h27 h28 h31 h32 h35 hwords ht hh
      (LSF.safeLen H ℓ ∘ edgeName H) (v ∘ edgeName H) γ hw hv hconnected htree
      hE hV hnm rfl hlevels (queryNumerator fmt.precision ∘ LSF.safeLen H ℓ ∘ edgeName H)
      query hL hm rfl B B (by simpa only [hcast] using hs) (by simpa only [hcast] using hwgt)
      hfit hfit hLenFit hlen (by simpa only [hcast] using hweight)
      hnEnd hnames hlengths hweights hscale hdenom hcontract'
  rw [h12] at h16 h36 h38 hzero hdest hsep hcursor htree' hstretches hnext
  rw [hcast] at hstretches hnext
  exact ⟨computed,packed,cn,cp,hnr,hpr,h16,h36,h37,h38,h39,hkeep,hzero,hprefix,
    hsep,hdest,hcursor,htree',hstretches,hnext,hcn,hcp⟩

/-- The compact numeric pass leaves the addresses and dimensions used
by branch append in their controller argument slots. -/
theorem packedController_appendRegisters (st staged selected packed : State) (pos : ℕ)
    (hstaged : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hselected : ∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r)
    (hpacked : ∀ r, r ≠ 15 → r ≠ 16 →
      r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34,36,37,38,39] : List ℕ) →
      packed.regs r = selected.regs r) :
    packed.regs 40 = st.regs 150 ∧ packed.regs 41 = st.regs 113 ∧
      packed.regs 42 = st.regs 114 ∧ packed.regs 43 = st.regs 115 ∧
      packed.regs 44 = st.regs 116 ∧ packed.regs 55 = st.regs 127 ∧
      packed.regs 56 = st.regs 3 ∧ packed.regs 57 = st.regs 2 ∧
      packed.regs 59 = st.regs 131 ∧ packed.regs 61 = st.regs 133 ∧
      packed.regs 62 = st.regs 134 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    rw [hpacked _ (by decide) (by decide) (by decide), hselected _ (by decide) (by decide),
      hstaged _ (by decide) (by decide) (by decide) (by decide)]
    rfl

/-- Link the installed round using the staged controller memory and
its live words. The caller's precondition fixes the argument vector. -/
theorem stagedPackedControllerRound_linkStaged
    {w entry D initGraph
      vCap eCap h L P caller base count handle bound guestL sim src j budget stride : ℕ}
    {p guest : Program} {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} (st : State) (Next : State → Prop)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base) (hw : 1 < 2^w)
    (hheap : queryHeap H guestL < 2^w) (hfit : bound+queryWeights H guestL < 2^w)
    (hp : p.HasAt entry (packedSelectedRoundModule guest D entry initGraph))
    (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w) :
    let C := stagedControllerRoundContract st Next j budget
    let args := (List.range 70).map (st.regs ∘ roundControllerRegister)
    (∀ pos ω staged, staged.regs 5 = st.regs 0 →
        staged.regs 8 = st.mem (st.regs 0-1) → staged.regs 31 = st.mem (st.regs 0-1) →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args st.mem pos).regs r) →
        (∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i)) →
        (∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a →
          staged.mem a = st.mem a) →
        (∀ r, staged.regs r < 2^w) →
      ∃ mid ready out cn cl cb stop weights,
        Runs w p ω
          (.seq (stagedTreeSelectionBody (entry+130) (entry+129) convertedGuestCallArgs)
            (prepareAndRunWideStagedNumericBody (entry+17) (entry+105) (entry+106)
              (entry+107) (entry+108) (entry+1)))
          staged .normal mid cn ∧
        Runs w p ω (publishableWideOutputs (entry+111)) mid .normal ready cl ∧
        Runs w p ω (stagedBranchAppendBody (entry+107) (entry+115) initGraph (entry+117) (entry+122))
          ready .normal out cb ∧
        out.regs 54 = stop ∧ out.regs 38 = weights ∧ stop+1 < 2^w ∧
        ZeroFrom out.mem stop ∧
        C.post args st.mem (stop+1) (Function.update out.mem stop weights) ∧
        cn+cl+cb+21+17*queryWeights H guestL+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args st.mem) →
    MeetsContract w p entry C := by
  intro C args hrun
  obtain ⟨hround,_⟩ := packedSelectedRoundModule_entries hp
  obtain ⟨he,harith,_,_,_⟩ := packedRoundModule_entries hround
  have hcopy := (packedRoundArithmeticModule_helpers harith).1
  apply stagedPackedControllerRound_link st Next hs hn hm hguest hsim hsrc hbase hw hheap hfit he
    (copyWords_meetsContract hcopy)
  intro inputArgs input pos ω _ hpre staged h5 h8 h31 h70 hkeep hcopied hframe
  obtain ⟨rfl,rfl⟩ := hpre
  exact hrun pos ω staged h5 h8 h31 hkeep hcopied hframe
    (packedStagedWords hs hbound hwords h5 h8 h31 h70 hkeep)

end MinCostFlow.LastLevelProgram
