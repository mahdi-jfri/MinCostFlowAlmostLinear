module

public import MinCostFlow.LastLevelProgram.LSSTCost
public import MinCostFlow.LastLevelProgram.LoopOnlyBranch
import Mathlib.Data.Nat.Size

/-!
# Space for the packed runtime dispatcher

Definition 5.8 (pages 19–20) either publishes the empty branch or
rebuilds the collection from the non-loop representatives. The allocation
is fixed before either branch reads the caller's memory.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num SparseCore MinRatio DynSpanner.Program

/-- Registers carrying prepared inputs into the collection controller.
Other registers are scratch or initialized by the controller itself. -/
@[expose] def packedControllerInputRegisters : List ℕ :=
  [72,73,74,75,83,86,95,99,100,107,113,114,115,116,127,131,133,134,141,145,150,151]

/-- A controller call places prepared inputs in their original slots and
starts with zero in every other register. -/
def packedControllerInputArgs : List Expr :=
  (List.range 152).map fun r => if r ∈ packedControllerInputRegisters then .reg r else .const 0

/-- The argument list reads only the registers of the prepared input. -/
theorem packedControllerInputArgs_eval (w : ℕ) (st : State) :
    evalArgs w st packedControllerInputArgs =
      some ((List.range 152).map fun r => if r ∈ packedControllerInputRegisters then st.regs r else 0) := by
  unfold packedControllerInputArgs
  generalize List.range 152 = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : r ∈ packedControllerInputRegisters
    · simp only [List.map_cons, evalArgs, ite_eq_left hr, Expr.eval, ih]
    · simp only [List.map_cons, evalArgs, ite_eq_right hr, Expr.eval, ite_eq_left (Nat.two_pow_pos w), ih]

/-- The controller receives all prepared input values, and its other
registers start at zero even when the initializer used them as scratch. -/
theorem packedControllerInput_startState (st : State) (r : ℕ) :
    let args := (List.range 152).map fun i => if i ∈ packedControllerInputRegisters then st.regs i else 0
    (startState args st.mem st.pos).regs r =
      if r ∈ packedControllerInputRegisters then st.regs r else 0 := by
  intro args
  have hlt (hr : r ∈ packedControllerInputRegisters) : r < 152 := by
    simp only [packedControllerInputRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  change args.getD r 0 = _
  by_cases hr : r < 152
  · simp [args, List.getD, hr]
  · have hn : r ∉ packedControllerInputRegisters := fun h => hr (hlt h)
    simp [args, List.getD, hr, hn]

/-- The controller call needs word bounds only for the prepared input
registers. Its result and memory are those of the controller body. -/
theorem packedControllerCall_runs
    {w entry result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (body : Stmt) (hp : p.procs[entry]? = some body)
    (hwords : ∀ r ∈ packedControllerInputRegisters, st.regs r < 2^w)
    (Post : ℕ → (ℕ → ℕ) → Prop) (budget : ℕ)
    (hbody : ∀ entered : State,
      entered.mem = st.mem → entered.pos = st.pos →
      (∀ r ∈ packedControllerInputRegisters, entered.regs r = st.regs r) →
      (∀ r, entered.regs r < 2^w) →
      ∃ ret out cost, Runs w p ω body entered (.returned ret) out cost ∧
        Post ret out.mem ∧ cost ≤ budget) :
    ∃ ret out cost, Runs w p ω
        (.seq (.call result entry packedControllerInputArgs) (.ret (.reg result)))
        st (.returned ret) out cost ∧
      Post ret out.mem ∧ cost ≤ budget+argsSize packedControllerInputArgs+4 := by
  let args := (List.range 152).map fun r => if r ∈ packedControllerInputRegisters then st.regs r else 0
  let entered := startState args st.mem st.pos
  have hregs (r : ℕ) : entered.regs r =
      if r ∈ packedControllerInputRegisters then st.regs r else 0 :=
    packedControllerInput_startState st r
  obtain ⟨ret,out,cost,hr,hpost,hcost⟩ := hbody entered rfl rfl
    (fun r hr => (hregs r).trans (ite_eq_left hr))
    (fun r => by
      rw [hregs r]
      split
      · exact hwords r ‹_›
      · exact Nat.two_pow_pos w)
  let resumed := {out with regs := Function.update st.regs result ret}
  have hcall : Runs w p ω (.call result entry packedControllerInputArgs) st .normal resumed
      (argsSize packedControllerInputArgs+cost+1) :=
    runs_call_iff.mpr ⟨args,body,.returned ret,out,cost,packedControllerInputArgs_eval w st,
      hp,hr,rfl,rfl,rfl⟩
  have hret : Runs w p ω (.ret (.reg result)) resumed (.returned ret) resumed 2 :=
    runs_ret_iff.mpr ⟨ret,by simp [resumed,Expr.eval],rfl,rfl,rfl⟩
  exact ⟨ret,resumed,_,runs_seq_iff.mpr (Or.inr
    ⟨resumed,_,2,hcall,hret,rfl⟩),hpost,by omega⟩

/-- Bound the scalar intermediates of format setup before the first
guest call. The packed addresses are bounded separately by allocation. -/
@[expose] def packedFormatScalarBound (H : MGraph) (d c L caller grid Q N sim : ℕ) : ℕ :=
  16+d+c+H.n+4+16*H.m+8+(2*integerScale d H+2)+
    (4*L+max caller grid+(2*H.m).size+2)+Q+N+(caller+N)+sim

/-- A word that holds the scalar bound holds every format intermediate. -/
theorem packedFormatScalarBound_fields (H : MGraph) (d c L caller grid Q N sim w : ℕ)
    (h : packedFormatScalarBound H d c L caller grid Q N sim < 2^w) :
    16 < 2^w ∧ d < 2^w ∧ c < 2^w ∧ H.n+4 < 2^w ∧ 16*H.m+8 < 2^w ∧
      2*integerScale d H+2 < 2^w ∧ 4*L+max caller grid+(2*H.m).size+2 < 2^w ∧
      Q < 2^w ∧ N < 2^w ∧ caller+N < 2^w ∧ sim < 2^w ∧ grid+N < 2^w := by
  unfold packedFormatScalarBound at h
  have hgrid : grid ≤ max caller grid := le_max_right _ _
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The finite scalar bound fits a sufficiently large host word. -/
theorem packedFormatScalarBound_fits (H : MGraph) (d c L caller grid Q N sim : ℕ) :
    ∃ w, packedFormatScalarBound H d c L caller grid Q N sim < 2^w :=
  ⟨_,Nat.lt_two_pow_self⟩

/-- Bound the scalar preparation from the original graph dimensions
and caller width before reading the representative lengths. -/
theorem packedFormatScalarBound_le
    (G : MGraph) (ℓ : ℕ → ℝ) (C : ℝ) (d c L P : ℕ)
    (hG : G.IsValid) (hD : d = ⌈max 1 C⌉₊) :
    let H := representativeGraph G ℓ
    let len := LSF.safeLen H ℓ
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    let B := representativeGuestWidthBound d L G.m
    0 < H.m → N ≤ B →
    packedFormatScalarBound H d c L P (weightPrecision C H) Q N
      (WideWord.lsstLSimMin c H.n H.m N 1) ≤
    packedFormatScalarBound G d c L P ((1024*d).size+3*(G.m+1).size) B B
      (WideWord.lsstLSimMin c G.n G.m B 1) := by
  intro H len Q N B hpos hN
  have hsub := representativeGraph_subgraph hG ℓ
  have hn : H.n ≤ G.n := Finset.card_le_card hsub.1
  have hm : H.m ≤ G.m := Finset.card_le_card hsub.2.1
  have hQ : Q ≤ N := by
    change Q ≤ graphQueryLimbs H Q (2*H.m*2^Q) len
    rw [graphQueryLimbs_eq_maxSize]
    have hsize : (2*H.m*2^Q).size = (2*H.m).size+Q := by
      rw [← Nat.shiftLeft_eq,Nat.size_shiftLeft (by omega : 2*H.m ≠ 0)]
    rw [hsize]
    have h := le_max_left ((2*H.m).size+Q)
      (H.E.sup fun e => (queryNumerator Q (len e)).natAbs.size)
    omega
  have hg : weightPrecision C H ≤ (1024*d).size+3*(G.m+1).size := by
    rw [hD]
    exact (representativeGraph_weightPrecision_le C G ℓ).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3
        (Nat.size_le_size (Nat.succ_le_succ hm))) _)
  have hscale : integerScale d H ≤ integerScale d G := by
    unfold integerScale
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hm)
      (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.log_mono_right (Nat.add_le_add_right hn 2))) _)
  have hs := packedSimWidth_mono (c := c) (n := H.n) (n' := G.n) hm hN
  have hsize := Nat.size_le_size (Nat.mul_le_mul_left 2 hm)
  have hgrid := max_le_max_left P hg
  unfold packedFormatScalarBound
  omega

/-- A caller can choose the host word width before seeing the input
length values. Only the graph dimensions and caller limb count enter
the scalar bound. -/
theorem packedFormatScalarBound_of_initPre
    {w L vCap eCap multiplier P g lengths heap : ℕ}
    (fmt : Format w) (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (C : ℝ) (c : ℕ) (mem : ℕ → ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,lengths,L,fmt.precision,heap] mem) :
    let d := ⌈max 1 C⌉₊
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let len := LSF.safeLen H ℓ
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    let B := representativeGuestWidthBound d L G.m
    packedFormatScalarBound G d c L (4*L) ((1024*d).size+3*(G.m+1).size) B B
      (WideWord.lsstLSimMin c G.n G.m B 1) < 2^w →
    packedFormatScalarBound H d c L fmt.precision (weightPrecision C H) Q N
      (WideWord.lsstLSimMin c H.n H.m N 1) < 2^w := by
  intro d ℓ H len Q N B hword
  obtain ⟨hgraph,_,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool allocation G mem hpre
  have hwidth : fmt.precision ≤ 4*L := hpre.choose_spec.choose_spec.choose_spec.2.2.1
  have hN := (representativePackedCost_dimensions_of_initPre fmt tool allocation C G mem hne hpre).1
  obtain ⟨e,he⟩ := hne
  have hm : 0 < H.m := Finset.card_pos.mpr ⟨_,(representativeGraph_shortest (ℓ := ℓ) he).1⟩
  refine (packedFormatScalarBound_le G ℓ C d c L fmt.precision hgraph.1 rfl hm hN).trans_lt ?_
  refine Nat.lt_of_le_of_lt ?_ hword
  dsimp only [packedFormatScalarBound, B]
  have hmax := max_le_max_right ((1024*d).size+3*(G.m+1).size) hwidth
  omega

/-- Host word capacity needed for scalar format setup and the encoded
endpoint triples. This bound depends only on caller dimensions. -/
@[expose] def packedRuntimeWordBound (G : MGraph) (d c L vCap eCap : ℕ) : ℕ :=
  let B := representativeGuestWidthBound d L G.m
  max (max (2^14) (vCap*vCap*eCap))
    (packedFormatScalarBound G d c L (4*L) ((1024*d).size+3*(G.m+1).size) B B
      (WideWord.lsstLSimMin c G.n G.m B 1))

/-- The prepared controller inputs fit using the graph layout, caller
frame, and allocation bounds. Other caller memory need not hold words. -/
theorem packedControllerInput_words
    {w g lengths heap vCap eCap L P d c Q N sim : ℕ} {input : ℕ → ℕ}
    (G H : MGraph) (grid : ℕ) (ready : State)
    (hg : DynGraphAt input g vCap eCap G)
    (hgEnd : g+dynGraphSize vCap eCap ≤ heap) (hlen : lengths ≤ heap)
    (haddr : heap+11*G.m+vCap+1 < 2^w)
    (hscalar : packedFormatScalarBound H d c L P grid Q N sim < 2^w)
    (h72 : ready.regs 72 = H.n) (h73 : ready.regs 73 = H.m)
    (h74 : ready.regs 74 = N) (h75 : ready.regs 75 = sim)
    (h83 : ready.regs 83 = Q) (h86 : ready.regs 86 = Nat.clog 2 H.n)
    (h95 : ready.regs 95 = grid) (h99 : ready.regs 99 = lengths)
    (h100 : ready.regs 100 = heap+2*G.m) (h107 : ready.regs 107 = integerScale d H)
    (h113 : ready.regs 113 = vCap) (h114 : ready.regs 114 = eCap)
    (h115 : ready.regs 115 = G.n) (h116 : ready.regs 116 = dgVListBase g vCap)
    (h127 : ready.regs 127 = L) (h131 : ready.regs 131 = heap+4*G.m)
    (h133 : ready.regs 133 = G.m) (h134 : ready.regs 134 = heap)
    (h141 : ready.regs 141 = heap+11*G.m+vCap+1) (h145 : ready.regs 145 = P)
    (h150 : ready.regs 150 = heap+7*G.m) (h151 : ready.regs 151 = heap) :
    ∀ r ∈ packedControllerInputRegisters, ready.regs r < 2^w := by
  obtain ⟨_,_,_,hn,hm,hscale,hwidth,hQ,hN,hPN,hsim,hgrid⟩ :=
    packedFormatScalarBound_fields H d c L P grid Q N sim w hscalar
  have hnG : G.n ≤ vCap := by
    exact (Finset.card_le_card (t := Finset.range vCap) (fun v hv =>
      Finset.mem_range.mpr (hg.2.1 v hv))).trans (Finset.card_range _).le
  have hlevel : Nat.clog 2 H.n ≤ H.n := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hVList : dgVListBase g vCap ≤ heap := by
    simp only [dgVListBase,dynGraphSize] at hgEnd ⊢
    omega
  have hE : eCap ≤ heap := by simp only [dynGraphSize] at hgEnd; omega
  intro r hr
  simp only [packedControllerInputRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [h72,h73,h74,h75,h83,h86,h95,h99,h100,h107,h113,h114,h115,h116,
      h127,h131,h133,h134,h141,h145,h150,h151] <;> omega

/-- Reserve space for the route selected by the runtime dispatcher. -/
@[expose] noncomputable def packedRuntimeAllocation (G : MGraph) (guest : Program)
    (C : ℝ) (c₀ L vCap eCap : ℕ) (_ : ℕ) (_ : List ℕ) : ℕ :=
  if (nonLoopEdges G).Nonempty then
    max (representativePackedSpaceBound G guest C c₀ L vCap eCap)
      (packedRuntimeWordBound G ⌈max 1 C⌉₊ c₀ L vCap eCap)
  else
    loopOnlySpace vCap eCap L

/-- On a connected non-loop input, the dispatcher's reservation covers
all tables used by the initializer at the runtime-selected format. -/
theorem packedRuntimeAllocation_nonLoop_bound
    {w L vCap eCap multiplier P g src heap : ℕ} (fmt : Format w)
    (tool : Chain.LastLevelTool) (G : MGraph) (guest : Program) (C : ℝ) (c₀ : ℕ)
    (mem : ℕ → ℕ) (hne : (nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    let alloc := packedRuntimeAllocation G guest C c₀ L vCap eCap
    let D := MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc
    let args := [g,src,L,fmt.precision,heap]
    D.initPre args mem → heap+D.initSpace args mem < 2^w →
    heap+representativePackedRuntimeSpace G guest C c₀ vCap eCap mem args < 2^w := by
  intro alloc D args hpre hroom
  have hspace := representativePackedRuntimeSpace_le_of_initPre fmt tool alloc G guest C c₀
    mem hne hconn hpre
  have hfit : heap+representativePackedSpaceBound G guest C c₀ L vCap eCap < 2^w := by
    change heap+alloc 1 args < 2^w at hroom
    simp only [alloc,packedRuntimeAllocation,ite_eq_left hne] at hroom
    exact (Nat.add_le_add_left (le_max_left _ _) heap).trans_lt hroom
  exact (Nat.add_le_add_left hspace heap).trans_lt hfit

/-- The reserved host word capacity suffices for the packed key and
all scalar intermediates at the live input format. -/
theorem packedRuntimeAllocation_nonLoop_words
    {w L vCap eCap multiplier P g lengths heap : ℕ} (fmt : Format w)
    (tool : Chain.LastLevelTool) (G : MGraph) (guest : Program) (C : ℝ) (c : ℕ)
    (mem : ℕ → ℕ) (hne : (nonLoopEdges G).Nonempty) :
    let alloc := packedRuntimeAllocation G guest C c L vCap eCap
    let D := lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc
    let args := [g,lengths,L,fmt.precision,heap]
    let d := ⌈max 1 C⌉₊
    let ℓ := readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let len := LSF.safeLen H ℓ
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    D.initPre args mem → heap+D.initSpace args mem < 2^w →
    14 ≤ w ∧ vCap*vCap*eCap ≤ 2^w ∧
    packedFormatScalarBound H d c L fmt.precision (weightPrecision C H) Q N
      (WideWord.lsstLSimMin c H.n H.m N 1) < 2^w := by
  intro alloc D args d ℓ H len Q N hpre hroom
  change heap+alloc 1 args < 2^w at hroom
  simp only [alloc,packedRuntimeAllocation,ite_eq_left hne] at hroom
  have hword : packedRuntimeWordBound G d c L vCap eCap < 2^w :=
    ((le_max_right _ _).trans (Nat.le_add_left _ _)).trans_lt hroom
  have hcapacity : max (2^14) (vCap*vCap*eCap) < 2^w :=
    (le_max_left _ _).trans_lt hword
  have hw : 14 ≤ w := by
    by_contra! h
    have hpow : 2^w ≤ 2^14 := Nat.pow_le_pow_right (by decide) h.le
    exact (not_lt_of_ge hpow) ((le_max_left _ _).trans_lt hcapacity)
  exact ⟨hw, ((le_max_right _ _).trans_lt hcapacity).le,
    packedFormatScalarBound_of_initPre fmt tool alloc G C c mem hne hpre
      ((le_max_right _ _).trans_lt hword)⟩

/-- The allocation promised by dispatch supplies the endpoint, guest,
and packed controller bounds for the selected non-loop initializer. -/
theorem packedRuntimeAllocation_controllerBounds
    {w L vCap eCap multiplier P g lengths heap : ℕ} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (guest : Program) (C : ℝ) (c₀ : ℕ)
    (mem : ℕ → ℕ) (hne : (nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    let alloc := packedRuntimeAllocation G guest C c₀ L vCap eCap
    let tool := fixedPointLastLevelTool oracle C
    let D := MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc
    let args := [g,lengths,L,fmt.precision,heap]
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let N := roundQueryLimbs C H (LSF.safeLen H ℓ)
    let sim := WideWord.lsstLSimMin c₀ H.n H.m N 1
    let k := Nat.clog 2 H.n
    let src := heap+11*G.m+vCap+1
    let base := src+queryWeights H N
    let step := stagedPackedRoundSpace H guest ⌈max 1 C⌉₊ N sim k L (weightPrecision C H) H.n vCap eCap
    let bound := base+stagedPackedCollectionSpace H guest ⌈max 1 C⌉₊ N sim k
      L (weightPrecision C H) H.m vCap eCap
    D.initPre args mem → heap+D.initSpace args mem < 2^w →
    0 < H.m ∧ src+queryLengths H < 2^w ∧ queryHeap H N < 2^w ∧
      base < 2^w ∧ heap+1+H.m ≤ base ∧
      base+1+H.m+2*L+H.m*L+1+H.m*step ≤ bound ∧
      bound+queryWeights H N < 2^w ∧ bound ≤ heap+D.initSpace args mem := by
  intro alloc tool D args ℓ H N sim k src base step bound hpre hroom
  have hword := packedRuntimeAllocation_nonLoop_bound fmt tool G guest C c₀ mem hne hconn hpre hroom
  have halloc := representativePackedRuntimeSpace_le_of_initPre fmt tool alloc G guest C c₀
    mem hne hconn hpre
  obtain ⟨hgraph,_,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool alloc G mem hpre
  have hc : (tool.build G ℓ).1 = H.m := by simp only [tool,fixedPointLastLevelTool,ite_eq_left hne,H]
  obtain ⟨_,hm,hsrc,hheap,hbase,hstep,hbound⟩ :=
    representativePackedInitSpace_modelBounds G ℓ oracle C guest ⌈max 1 C⌉₊ N sim k L
      (weightPrecision C H) vCap eCap heap w hgraph.1 hne (hc.symm ▸ hword)
  rw [hc] at hm hbase hstep hbound
  have hbaseFit : base < 2^w := by
    exact (show base ≤ bound by omega).trans_lt
      ((Nat.le_add_right bound (queryWeights H N)).trans_lt hbound)
  refine ⟨hm,hsrc,hheap,hbaseFit,hbase,hstep,hbound,?_⟩
  have hfit : bound+queryWeights H N ≤ heap+D.initSpace args mem := by
    change bound+queryWeights H N ≤ heap+alloc 1 args
    have hsum := Nat.add_le_add_left halloc heap
    simp only [alloc,packedRuntimeAllocation,ite_eq_left hne]
    refine Nat.le_trans ?_ (Nat.add_le_add_left (le_max_left _ _) heap)
    simpa only [bound,base,src,
      representativePackedRuntimeSpace,representativePackedInitSpace,ℓ,H,N,sim,k,
      List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.add_assoc] using hsum
  exact (Nat.le_add_right _ _).trans hfit

/-- The loop-only dispatcher and its readout implement the runtime
contract at the shared allocation function. -/
theorem packedRuntime_implements_loopOnly
    {w bOps bEdge bSplit bBatch copy header vCap eCap L Q init op loops general : ℕ}
    {p : Program} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (G : MGraph)
    (guest : Program) (c₀ : ℕ)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps)) (hops : p.HasAt bOps dgOpsProcs)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header
      (branchHeaderContract w vCap eCap 4 L fmt.precision G.E (loopOnlyLSF G)))
    (hw : 16 ≤ 2^w) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty)
    (hinit : p.procs[init]? = some (dispatchRuntimeInit loops general))
    (hproc : p.procs[loops]? = some (loopOnlyInit (bBatch+dgIdxInitFromLists) copy header))
    (hop : p.procs[op]? = some readoutBody) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap
        (loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2) Q (packedRuntimeAllocation G guest C c₀ L vCap eCap)) := by
  have halloc : packedRuntimeAllocation G guest C c₀ L vCap eCap =
      fun _ _ => loopOnlySpace vCap eCap L := by
    funext i args
    simp only [packedRuntimeAllocation,ite_eq_right hloops]
  rw [halloc]
  exact dispatchRuntime_implements_loopOnly fmt oracle C G hbatch hedge hops hc hh hw hloops
    hinit hproc hop

/-- Add the verified phase bounds in the order used by the
non-loop initializer. -/
theorem packedRuntime_initCost_le (guest : Program) (c₀ : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep names indices format levels loop rebuild : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hG : G.IsValid) :
    let H := representativeGraph G ℓ
    let modelBudget := (fixedPointLastLevelTool oracle C).cost G+1
    let D := ⌈max 1 C⌉₊
    0 < H.m →
    prep ≤ runtimeEndpointMultiplier L G.m*(G.m+1) →
    names+indices ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*modelBudget →
    format ≤ representativeGuestSetupMultiplier D L G.m*(G.m+1) →
    loop ≤ (representativePackedRoundMultiplier guest c₀ D K L G.n G.m +
      (argsSize publishedRoundArgs+10)+7)*modelBudget →
    levels ≤ 40*(G.n+2).size+22 →
    rebuild ≤ collectionHeaderAddress.size+20+
      (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loop+
        (17*(H.m+1)+19)+17) →
    prep+names+indices+format+levels+rebuild+5 ≤
      representativePackedRuntimeMultiplier guest c₀ D K L G.n G.m*modelBudget := by
  intro H modelBudget D hm hprep htables hformat hloop hlevels hreb
  have hsum := representativePackedSetupRoundsCost_le guest c₀ K C oracle G ℓ L prep
    (names+indices) format loop hnl hm hprep htables hformat hloop
  have hcard : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have htotal := representativePackedRuntimeCost_le guest c₀ K C oracle G ℓ L prep
    (names+indices) format loop levels hnl hsum hlevels hcard hm
  dsimp only [H,modelBudget,D] at hreb ⊢
  omega

/-- Convert the packed initializer's phase budget to the dispatch budget. -/
theorem packedRuntime_dispatchCost_le (guest : Program) (c₀ : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (G : MGraph) (ℓ : ℕ → ℝ)
    (L prep names indices format levels loop rebuild : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hG : G.IsValid) :
    let H := representativeGraph G ℓ
    let modelBudget := (fixedPointLastLevelTool oracle C).cost G+1
    let D := ⌈max 1 C⌉₊
    0 < H.m →
    prep ≤ runtimeEndpointMultiplier L G.m*(G.m+1) →
    names+indices ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*modelBudget →
    format ≤ representativeGuestSetupMultiplier D L G.m*(G.m+1) →
    loop ≤ (representativePackedRoundMultiplier guest c₀ D K L G.n G.m +
      (argsSize publishedRoundArgs+10)+7)*modelBudget →
    levels ≤ 40*(G.n+2).size+22 →
    rebuild ≤ collectionHeaderAddress.size+20+
      (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loop+
        (17*(H.m+1)+19)+17) →
    prep+names+indices+format+levels+rebuild+5+29*G.m+80 ≤
      representativePackedDispatchMultiplier guest c₀ D K L G.n G.m*modelBudget := by
  intro H modelBudget D hm hp ht hf hr hl hb
  exact representativePackedDispatchCost_le guest c₀ K C oracle G L _ hnl
    (packedRuntime_initCost_le guest c₀ K C oracle G ℓ L prep names indices format levels loop rebuild
      hnl hG hm hp ht hf hr hl hb)

end MinCostFlow.LastLevelProgram
