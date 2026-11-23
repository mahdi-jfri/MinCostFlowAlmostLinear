module

public import MinCostFlow.LastLevelProgram.StagedBranchPublication

public import MinCostFlow.LastLevelProgram.StagedOutputLayout
public import MinCostFlow.LastLevelProgram.Denominator
public import MinCostFlow.LastLevelProgram.StagedGuestWeights
import MinCostFlow.LastLevelProgram.StretchEncoding
public import MinCostFlow.LastLevelProgram.UnitWeights
public import MinCostFlow.LastLevelProgram.RoundLoop
public import MinCostFlow.LastLevelProgram.GuestSimulationWidth
public import MinCostFlow.LastLevelProgram.GuestFormatSetup
public import MinCostFlow.LastLevelProgram.ScaleWord
public import WordRAM.CopyWords
import Mathlib.Tactic

/-!
# Appending the staged last-level branch

Definition 5.8 (pages 19–20) publishes one low-stretch branch per
round. The unit, graph records, and branch readout are allocated in
order after the compact round outputs.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num WideWord SparseCore

/-- The controller keeps the fixed round inputs above its loop
registers. It supplies the live collection base, index, and cursor. -/
def roundControllerRegister (r : ℕ) : ℕ :=
  if r = 56 then 3 else if r = 57 then 2 else if r = 68 then 0 else if r = 40 then 150 else 72+r

/-- The published round consumes seventy runtime registers. -/
def publishedRoundArgs : List Expr :=
  (List.range 70).map (Expr.reg ∘ roundControllerRegister)

private theorem controllerArgs_eval (w : ℕ) (st : State) (rs : List ℕ) (address : ℕ → ℕ) :
    evalArgs w st (rs.map (Expr.reg ∘ address)) =
      some (rs.map (st.regs ∘ address)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,evalArgs,Function.comp_apply,Expr.eval,ih]

/-- Every argument is read from a controller register. In particular,
the call sees the current cursor and round index on each iteration. -/
theorem publishedRoundArgs_eval (w : ℕ) (st : State) :
    evalArgs w st publishedRoundArgs =
      some ((List.range 70).map (st.regs ∘ roundControllerRegister)) :=
  controllerArgs_eval w st _ _

/-- The initial weight setup receives the cursor after the collection
header as its heap. Its other inputs use the same controller registers
as later rounds. -/
def weightControllerRegister (r : ℕ) : ℕ :=
  if r = 16 then 0 else roundControllerRegister r

/-- Pass the cursor, edge count, precision, width, and stride to
initial weight setup in their designated slots. -/
def initialWeightControllerArgs : List Expr :=
  (List.range 56).map (Expr.reg ∘ weightControllerRegister)

/-- Initial weight setup evaluates only runtime register arguments. -/
theorem initialWeightControllerArgs_eval (w : ℕ) (st : State) :
    evalArgs w st initialWeightControllerArgs =
      some ((List.range 56).map (st.regs ∘ weightControllerRegister)) :=
  controllerArgs_eval w st _ _

/-- The initial weight call sees the current heap and the runtime
weight format supplied by the controller. -/
theorem initialWeightController_startState (st : State) (mem : ℕ → ℕ) (pos : ℕ) :
    let entered := startState ((List.range 56).map (st.regs ∘ weightControllerRegister)) mem pos
    entered.regs 16 = st.regs 0 ∧ entered.regs 1 = st.regs 73 ∧
    entered.regs 23 = st.regs 95 ∧ entered.regs 32 = st.regs 104 ∧
    entered.regs 55 = st.regs 127 := by
  simp [startState,weightControllerRegister,roundControllerRegister,List.getD]

/-- At round entry, the collection and live loop registers have
their designated positions in the published round body. -/
theorem publishedRoundArgs_startState (st : State) (mem : ℕ → ℕ) (pos : ℕ) :
    let entered := startState ((List.range 70).map (st.regs ∘ roundControllerRegister)) mem pos
    entered.regs 56 = st.regs 3 ∧ entered.regs 57 = st.regs 2 ∧
    entered.regs 68 = st.regs 0 := by
  simp [startState,roundControllerRegister,List.getD]

/-- The persistent guest prefix starts with the two endpoint arrays,
so the packed lengths begin two edge counts past its base. -/
def collectionGuestFormatArgs : List Expr :=
  [.reg 100,.reg 99,.reg 144,.reg 145,.reg 73,.reg 95,.reg 142,
    .bin .add (.reg 141) (.bin .mul (.const 2) (.reg 73))]

/-- The guest format call receives runtime source width and precision
and writes lengths in the persistent prefix's designated region. -/
theorem collectionGuestFormatArgs_eval {w : ℕ} (st : State) (G : MGraph)
    (names lengths L P grid precCell prefixBase : ℕ)
    (hn : st.regs 100 = names) (ha : st.regs 99 = lengths)
    (hL : st.regs 144 = L) (hP : st.regs 145 = P) (hm : st.regs 73 = G.m)
    (hg : st.regs 95 = grid) (hc : st.regs 142 = precCell) (hb : st.regs 141 = prefixBase)
    (hw : 2 < 2^w) (hfit : prefixBase+queryLengths G < 2^w) :
    evalArgs w st collectionGuestFormatArgs =
      some [names,lengths,L,P,G.m,grid,precCell,prefixBase+queryLengths G] := by
  have hmul : 2*G.m < 2^w := (Nat.le_add_left _ _).trans_lt hfit
  change prefixBase + 2*G.m < 2^w at hfit
  simp only [collectionGuestFormatArgs,evalArgs,Expr.eval,BinOp.eval,hn,ha,hL,hP,hm,hg,hc,hb,
    queryLengths,hw,hmul,hfit,ite_eq_left]

/-- Keep the guest width returned by format setup and load its
precision from the reserved precision cell. -/
def collectionGuestFormat (entry : ℕ) (args : List Expr) : Stmt :=
  .seq (.call 74 entry args) (.assign 83 (.load (.reg 142)))

/-- The runtime controller receives the graph-derived format, and the
packed lengths remain in memory for staging each round. -/
theorem collectionGuestFormat_runs
    {w entry cap names lengths L P dst guest : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (C : ℝ) (name : ℕ → ℕ) (args : List Expr)
    (haddr : st.regs 142 = dst)
    (hc : MeetsContract w p entry (setupAndPackGuestContract w cap names lengths L P dst guest G C name))
    (vs : List ℕ) (he : evalArgs w st args = some vs) (hwords : ∀ a ∈ vs, a < 2^w)
    (hpre : (setupAndPackGuestContract w cap names lengths L P dst guest G C name).pre vs st.mem) :
    let K := setupAndPackGuestContract w cap names lengths L P dst guest G C name
    ∃ out cost, Runs w p ω (collectionGuestFormat entry args) st .normal out cost ∧
      K.post vs st.mem (out.regs 74) out.mem ∧ out.regs 83 = out.mem dst ∧
      (∀ r, r ≠ 74 → r ≠ 83 → out.regs r = st.regs r) ∧
      cost ≤ argsSize args+K.cost vs st.mem+5 := by
  intro K
  obtain ⟨mid,c,ret,hr,hpost,hr74,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 74) hc he hwords hpre ω
  let out := {mid with regs := Function.update mid.regs 83 (mid.mem dst)}
  have hload : Runs w p ω (.assign 83 (.load (.reg 142))) mid .normal out 3 :=
    runs_assign_iff.mpr ⟨mid.mem dst,by simp [Expr.eval,(hregs _ (by decide)).trans haddr],
      rfl,rfl,rfl⟩
  have h74 : out.regs 74 = ret := by simpa [out,Function.update] using hr74
  exact ⟨out,c+4,runs_seq_iff.mpr (Or.inr ⟨mid,c,3,hr,hload,rfl⟩),
    h74.symm ▸ hpost,by simp [out],fun r h74' h83 =>
      (Function.update_of_ne h83 ..).trans (hregs r h74'),by dsimp only [K]; omega⟩

/-- Compute the simulation width from the representative edge count
and the graph-derived guest limb count. -/
def collectionSimulationWidth (entry : ℕ) (c : Expr) : Stmt :=
  .call 75 entry [.reg 73,.reg 74,c]

/-- Store the guest simulation width where each round call reads it. -/
theorem collectionSimulationWidth_runs {w n entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (ce : Expr) (m L c : ℕ)
    (hm : st.regs 73 = m) (hL : st.regs 74 = L) (he : ce.eval w st = some c)
    (hc : MeetsContract w p entry (guestSimulationWidthContract w n))
    (hwords : ∀ a ∈ [m,L,c], a < 2^w)
    (hpre : (guestSimulationWidthContract w n).pre [m,L,c] st.mem) :
    ∃ out cost, Runs w p ω (collectionSimulationWidth entry ce) st .normal out cost ∧
      out.regs 75 = lsstLSimMin c n m L 1 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 75 → out.regs r = st.regs r) ∧
      cost ≤ ce.size+40*(Nat.log 2 (4*m+2)+Nat.log 2 (16*m+6)+2)+68 := by
  have ha : evalArgs w st [.reg 73,.reg 74,ce] = some [m,L,c] := by
    simp [evalArgs,Expr.eval,hm,hL,he]
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 75) hc ha hwords hpre ω
  obtain ⟨m',L',c',heq,hs,hmem⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  simp [guestSimulationWidthContract,argsSize,Expr.size] at hcost
  exact ⟨out,cost,hr,hret.trans hs,hmem,hregs,by omega⟩

/-- Compute the integer update scale and its bit precision before
the first round. Both are read by the published round body. -/
def collectionWeightScale (scale precision : ℕ) (constant : Expr) : Stmt :=
  .seq (.call 107 scale [.reg 72,.reg 73,constant])
    (.call 95 precision [.reg 107])

/-- The controller stores the scale and precision of the fixed-point
model, leaving the prepared graph in memory. -/
theorem collectionWeightScale_runs {w scale precision : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (C : ℝ) (constant : Expr)
    (hn : st.regs 72 = G.n) (hm : st.regs 73 = G.m)
    (he : constant.eval w st = some ⌈max 1 C⌉₊)
    (hs : MeetsContract w p scale (scaleWordContract w G))
    (hp : MeetsContract w p precision (precisionWordContract w))
    (hwords : ∀ a ∈ [G.n,G.m,⌈max 1 C⌉₊], a < 2^w)
    (hpre : (scaleWordContract w G).pre [G.n,G.m,⌈max 1 C⌉₊] st.mem)
    (hpos : 0 < integerScale ⌈max 1 C⌉₊ G)
    (hfit : 2*integerScale ⌈max 1 C⌉₊ G+2 < 2^w) :
    ∃ out cost, Runs w p ω (collectionWeightScale scale precision constant) st .normal out cost ∧
      out.regs 107 = integerScale ⌈max 1 C⌉₊ G ∧ out.regs 95 = weightPrecision C G ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 107 → r ≠ 95 → out.regs r = st.regs r) ∧
      cost ≤ constant.size+40*(Nat.log 2 (G.n+2)+1)+40*weightPrecision C G+92 := by
  let D := ⌈max 1 C⌉₊
  let v := integerScale D G
  have ha : evalArgs w st [.reg 72,.reg 73,constant] = some [G.n,G.m,D] := by
    simp only [evalArgs,Expr.eval,hn,hm,he,D]
  obtain ⟨mid,cs,ret,hr,hpost,hr107,hregs,hcs⟩ :=
    runs_call_of_meetsContract (r := 107) hs ha hwords hpre ω
  obtain ⟨d,hd,hret,hm'⟩ := hpost
  have hD : d = D := by simpa only [List.cons.injEq,and_true,true_and] using hd.symm
  cases hD
  have hv : mid.regs 107 = v := hr107.trans hret
  have hb : evalArgs w mid [.reg 107] = some [v] := by simp [evalArgs,Expr.eval,hv]
  have hvword : v < 2^w := by dsimp [v,D]; omega
  obtain ⟨out,cp,ret',hr',hpost',hr95,hregs',hcp⟩ :=
    runs_call_of_meetsContract (r := 95) hp hb
      (fun a ha' => (show a = v by simpa using ha').symm ▸ hvword)
      ⟨v,rfl,hpos,hfit⟩ ω
  obtain ⟨x,hx,hret',hm''⟩ := hpost'
  have hx' : x = v := by simpa using hx.symm
  cases hx'
  have hprec : (2*v).size = weightPrecision C G := precisionWord_eq_model C G
  simp [scaleWordContract,argsSize,Expr.size] at hcs
  change cp ≤ 1+(40*(2*v).size+35)+1 at hcp
  exact ⟨out,cs+cp+1,runs_seq_iff.mpr (Or.inr ⟨mid,cs,cp,hr,hr',rfl⟩),
    (hregs' _ (by decide)).trans hv,hr95.trans (hret'.trans hprec),hm''.trans hm',
    fun r h107 h95 => (hregs' r h95).trans (hregs r h107),by omega⟩

/-- Give the host update and guest converter the same weight stride
and grid. Register 127 holds the runtime host limb count. -/
def installCollectionWeightFormat : Stmt :=
  let stride := narrowWeightSpaceExpr (.reg 127)
  stagedAddressAssignments [81,82,91,104] [stride,.reg 95,.reg 127,stride]

/-- The controller initializes every alias of the format used by
the host update and guest conversion without modifying memory. -/
theorem installCollectionWeightFormat_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P : ℕ) (hL : st.regs 127 = L) (hP : st.regs 95 = P)
    (hfit : narrowWeightSpace L < 2^w) :
    let stride := narrowWeightSpace L
    ∃ out cost, Runs w p ω installCollectionWeightFormat st .normal out cost ∧
      out.regs 81 = stride ∧ out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = stride ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 2*(narrowWeightSpaceExpr (.reg 127)).size+11 := by
  intro stride
  let rs := [81,82,91,104]
  let se := narrowWeightSpaceExpr (.reg 127)
  let es := [se,.reg 95,.reg 127,se]
  have he (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid es = some [stride,P,L,stride] := by
    have hl := (hf 127 (by decide)).trans hL
    have hp := (hf 95 (by decide)).trans hP
    have hs := narrowWeightSpaceExpr_eval (le := .reg 127) L (congrArg some hl) hfit
    simp only [es,evalArgs,hs,show se = narrowWeightSpaceExpr (.reg 127) from rfl,Expr.eval,hl,hp,stride]
  obtain ⟨out,cost,hr,hm,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs es [stride,P,L,stride] (by decide) he
  have hbudget : cost ≤ 2*se.size+11 := by
    simp only [es,rs,argsSize_cons,argsSize_nil,Expr.size_reg,List.length_cons,List.length_nil] at hcost
    omega
  refine ⟨out,cost,hr,?_,?_,?_,?_,hm,?_,hbudget⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h81 h82 h91 h104
  simp [h81,h82,h91,h104]

/-- Use the runtime host limb count as the stride of the packed weights. -/
def installCompactCollectionWeightFormat : Stmt :=
  let stride := (Expr.reg 127)
  stagedAddressAssignments [81,82,91,104] [stride,.reg 95,.reg 127,stride]

/-- The controller initializes every alias of the format used by
the host update and guest conversion without modifying memory. -/
theorem installCompactCollectionWeightFormat_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P : ℕ) (hL : st.regs 127 = L) (hP : st.regs 95 = P) :
    let stride := L
    ∃ out cost, Runs w p ω installCompactCollectionWeightFormat st .normal out cost ∧
      out.regs 81 = stride ∧ out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = stride ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 13 := by
  intro stride
  let rs := [81,82,91,104]
  let se := Expr.reg 127
  let es := [se,.reg 95,.reg 127,se]
  have he (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid es = some [stride,P,L,stride] := by
    have hl := (hf 127 (by decide)).trans hL
    have hp := (hf 95 (by decide)).trans hP
    simp [es,se,evalArgs,Expr.eval,hl,hp,stride]
  obtain ⟨out,cost,hr,hm,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs es [stride,P,L,stride] (by decide) he
  have hbudget : cost ≤ 13 := by
    simp only [es,se,rs,argsSize_cons,argsSize_nil,Expr.size_reg,List.length_cons,List.length_nil] at hcost
    omega
  refine ⟨out,cost,hr,?_,?_,?_,?_,hm,?_,hbudget⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h81 h82 h91 h104
  simp [h81,h82,h91,h104]

/-- On a graph with a non-loop edge, the fixed-point tool publishes
one branch for each representative edge. -/
def installCollectionCount : Stmt :=
  .assign 1 (.reg 73)

/-- The count used by the collection header is the model's count.
The representative edge count remains available to the round calls. -/
theorem installCollectionCount_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ)
    (hnl : (nonLoopEdges G).Nonempty) (hm : st.regs 73 = (representativeGraph G ℓ).m) :
    ∃ out, Runs w p ω installCollectionCount st .normal out 2 ∧
      out.regs 1 = ((fixedPointLastLevelTool oracle C).build G ℓ).1 ∧
      out.mem = st.mem ∧ ∀ r, r ≠ 1 → out.regs r = st.regs r := by
  let out := {st with regs := Function.update st.regs 1 ((representativeGraph G ℓ).m)}
  refine ⟨out,runs_assign_iff.mpr ⟨_,congrArg some hm,rfl,rfl,rfl⟩,?_,rfl,?_⟩
  · simp [out,fixedPointLastLevelTool,hnl]
  · intro r hr
    exact Function.update_of_ne hr ..

/-- Start the collection immediately after the persistent endpoints
and guest length blocks. -/
def collectionHeaderAddress : Expr :=
  .bin .add (.reg 141)
    ((canonicalGuestArgsExpr (.reg 72) (.reg 73) (.reg 74) (.reg 75)).getD 5 (.const 0))

/-- The header starts in fresh memory after the packed guest prefix.
The assignment preserves every prepared controller input. -/
theorem installCollectionHeaderAddress_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (L sim src : ℕ)
    (hn : st.regs 72 = G.n) (hm : st.regs 73 = G.m)
    (hL : st.regs 74 = L) (hs : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hguest : queryHeap G L < 2^w) (hfit : src+queryWeights G L < 2^w) :
    let base := src+queryWeights G L
    ∃ out, Runs w p ω (.assign 3 collectionHeaderAddress) st .normal out
      (collectionHeaderAddress.size+1) ∧
      out.regs 3 = base ∧ out.mem = st.mem ∧
      ∀ r, r ≠ 3 → out.regs r = st.regs r := by
  intro base
  let out := {st with regs := Function.update st.regs 3 base}
  have hargs := canonicalGuestArgsExpr_eval (w := w) (st := st) G L sim
    (n := .reg 72) (m := .reg 73) (limbs := .reg 74) (sim := .reg 75)
    (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hguest
  have hoff : (((canonicalGuestArgsExpr (.reg 72) (.reg 73) (.reg 74) (.reg 75)).getD 5
      (.const 0))).eval w st = some (queryWeights G L) := evalArgs_getD hargs 5
  have he : collectionHeaderAddress.eval w st = some base := by
    simp only [collectionHeaderAddress,Expr.eval,BinOp.eval,hsrc,hoff,hfit,ite_eq_left,base]
  exact ⟨out,runs_assign_iff.mpr ⟨base,he,rfl,rfl,rfl⟩,by simp [out],rfl,
    fun r hr => Function.update_of_ne hr ..⟩

/-- Install the common stride, then set the collection count and
its base from the prepared graph and guest format. -/
def finishCollectionSetupWith (format : Stmt) : Stmt :=
  .seq format (.seq installCollectionCount (.assign 3 collectionHeaderAddress))

/-- Finish setup for weights stored in arithmetic workspaces. -/
def finishCollectionSetup : Stmt := finishCollectionSetupWith installCollectionWeightFormat

/-- Finish setup for compact caller-width weights. -/
def finishCompactCollectionSetup : Stmt :=
  finishCollectionSetupWith installCompactCollectionWeightFormat

/-- The final setup writes only controller registers and supplies the
collection initializer with the model count and a prefix-end address. -/
private theorem finishCollectionSetupWith_runs {w stride formatCost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P guestL sim src : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (format : Stmt)
    (hformat : ∃ out cost, Runs w p ω format st .normal out cost ∧
      out.regs 81 = stride ∧ out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = stride ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ formatCost) :
    let H := representativeGraph G ℓ
    st.regs 72 = H.n → st.regs 73 = H.m →
    st.regs 74 = guestL → st.regs 75 = sim → st.regs 141 = src →
    queryHeap H guestL < 2^w → src+queryWeights H guestL < 2^w →
    ∃ out cost, Runs w p ω (finishCollectionSetupWith format) st .normal out cost ∧
      out.regs 1 = ((fixedPointLastLevelTool oracle C).build G ℓ).1 ∧
      out.regs 3 = src+queryWeights H guestL ∧ out.regs 81 = stride ∧
      out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = stride ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ formatCost+collectionHeaderAddress.size+5 := by
  intro H hn hm hg hsim hsrc hguest hfit
  obtain ⟨mid,c,hr,h81,h82,h91,h104,hmem,hregs,hcost⟩ :=
    hformat
  obtain ⟨ready,hcount,h1,hmem',hregs'⟩ :=
    installCollectionCount_runs (p := p) (ω := ω) mid oracle C G ℓ hnl
      ((hregs _ (by decide)).trans hm)
  have keep (r : ℕ) (h₁ : r ≠ 1) (hr' : r ∉ ([81,82,91,104] : List ℕ)) :
      ready.regs r = st.regs r := (hregs' r h₁).trans (hregs r hr')
  obtain ⟨out,haddr,h3,hmem'',hregs''⟩ :=
    installCollectionHeaderAddress_runs (p := p) (ω := ω) ready H guestL sim src
      ((keep _ (by decide) (by decide)).trans hn) ((keep _ (by decide) (by decide)).trans hm)
      ((keep _ (by decide) (by decide)).trans hg) ((keep _ (by decide) (by decide)).trans hsim)
      ((keep _ (by decide) (by decide)).trans hsrc) hguest hfit
  have htail := runs_seq_iff.mpr (Or.inr ⟨ready,2,collectionHeaderAddress.size+1,hcount,haddr,rfl⟩)
  have hback (r : ℕ) (h₁ : r ≠ 1) (h₃ : r ≠ 3) : out.regs r = mid.regs r :=
    (hregs'' r h₃).trans (hregs' r h₁)
  refine ⟨out,c+(2+(collectionHeaderAddress.size+1)+1)+1,
    runs_seq_iff.mpr (Or.inr ⟨mid,c,_,hr,htail,rfl⟩), (hregs'' _ (by decide)).trans h1,h3,
    (hback _ (by decide) (by decide)).trans h81,(hback _ (by decide) (by decide)).trans h82,
    (hback _ (by decide) (by decide)).trans h91,(hback _ (by decide) (by decide)).trans h104,
    hmem''.trans (hmem'.trans hmem),?_,by omega⟩
  intro r hr'
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
  exact (hregs'' r hr'.2.1).trans (keep r hr'.1 (by simpa using hr'.2.2))

/-- The final setup writes only controller registers and supplies the
collection initializer with the model count and a prefix-end address. -/
theorem finishCollectionSetup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P guestL sim src : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hL : st.regs 127 = L) (hP : st.regs 95 = P)
    (hstride : narrowWeightSpace L < 2^w) :
    let H := representativeGraph G ℓ
    st.regs 72 = H.n → st.regs 73 = H.m →
    st.regs 74 = guestL → st.regs 75 = sim → st.regs 141 = src →
    queryHeap H guestL < 2^w → src+queryWeights H guestL < 2^w →
    ∃ out cost, Runs w p ω finishCollectionSetup st .normal out cost ∧
      out.regs 1 = ((fixedPointLastLevelTool oracle C).build G ℓ).1 ∧
      out.regs 3 = src+queryWeights H guestL ∧ out.regs 81 = narrowWeightSpace L ∧
      out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = narrowWeightSpace L ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 2*(narrowWeightSpaceExpr (.reg 127)).size+collectionHeaderAddress.size+16 := by
  intro H hn hm hg hsim hsrc hguest hfit
  obtain ⟨out,cost,hr,h1,h3,h81,h82,h91,h104,hmem,hkeep,hcost⟩ :=
    finishCollectionSetupWith_runs (p := p) (ω := ω) st oracle C G ℓ L P guestL sim src hnl
      installCollectionWeightFormat (installCollectionWeightFormat_runs st L P hL hP hstride)
      hn hm hg hsim hsrc hguest hfit
  exact ⟨out,cost,hr,h1,h3,h81,h82,h91,h104,hmem,hkeep,by omega⟩

/-- The final setup writes only controller registers and supplies the
collection initializer with the model count and a prefix-end address. -/
theorem finishCompactCollectionSetup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P guestL sim src : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hL : st.regs 127 = L) (hP : st.regs 95 = P)
    :
    let H := representativeGraph G ℓ
    st.regs 72 = H.n → st.regs 73 = H.m →
    st.regs 74 = guestL → st.regs 75 = sim → st.regs 141 = src →
    queryHeap H guestL < 2^w → src+queryWeights H guestL < 2^w →
    ∃ out cost, Runs w p ω finishCompactCollectionSetup st .normal out cost ∧
      out.regs 1 = ((fixedPointLastLevelTool oracle C).build G ℓ).1 ∧
      out.regs 3 = src+queryWeights H guestL ∧ out.regs 81 = L ∧
      out.regs 82 = P ∧ out.regs 91 = L ∧ out.regs 104 = L ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ collectionHeaderAddress.size+19 := by
  intro H hn hm hg hsim hsrc hguest hfit
  obtain ⟨out,cost,hr,h1,h3,h81,h82,h91,h104,hmem,hkeep,hcost⟩ :=
    finishCollectionSetupWith_runs (p := p) (ω := ω) st oracle C G ℓ L P guestL sim src hnl
      installCompactCollectionWeightFormat (installCompactCollectionWeightFormat_runs st L P hL hP)
      hn hm hg hsim hsrc hguest hfit
  exact ⟨out,cost,hr,h1,h3,h81,h82,h91,h104,hmem,hkeep,by omega⟩

/-- Rebuild the collection using the runtime controller argument lists. -/
def stagedCollectionBody (init weights round : ℕ) : Stmt :=
  rebuildPreparedCollectionBody init weights round initialWeightControllerArgs publishedRoundArgs

/-- The reserved collection supplies a fresh heap for the initial
weights. Their initializer preserves the header and returns the loop cursor. -/
theorem stagedCollectionThen_runs
    {w init weights round h P : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (base count L stride m loopCost finishCost : ℕ) (B : ℝ)
    (finish : Stmt) (Inv Ready : State → Prop) (Post : Outcome → State → Prop)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hb : st.regs 3 = base) (hn : st.regs 1 = count) (hm : st.regs 73 = m)
    (hP : st.regs 95 = P) (hs : st.regs 104 = stride) (hL : st.regs 127 = L)
    (hregs : ∀ r, st.regs r < 2^w) (hw : 1 < 2^w) (hstride : L ≤ stride)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L)
    (hz : ZeroFrom st.mem base)
    (hfit : base+1+count+2*L+m*stride+1 < 2^w)
    (hInv : ∀ next out pos,
      let dst := base+1+count+2*L
      let stop := dst+m*stride
      next = stop+1 → out stop = dst → ZeroFrom out next →
      out base = count → (∀ a < base, out a = st.mem a) →
      (∀ i < m, Valid out (dst+i*stride) h L ∧ fixVal out (dst+i*stride) h L P = 1) →
      Inv ⟨out,Function.update st.regs 0 next,pos⟩)
    (hloop : Triple w p Inv (lastLevelRoundsBody round publishedRoundArgs)
      (normalPost Ready) (fun _ => loopCost))
    (hfinish : Triple w p Ready finish Post (fun _ => finishCost)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round
      initialWeightControllerArgs publishedRoundArgs finish) st o out cost ∧ Post o out ∧
      cost ≤ argsSize initialWeightControllerArgs+((17*L+27)*m+56*L+111)+loopCost+finishCost+17 := by
  apply rebuildCollectionThen_runs st base count ((17*L+27)*m+56*L+111) loopCost finishCost
    finish Ready Post Inv (stagedInitialWeightContract w h P B)
    hi hweights hb hn (by omega) hz _ hloop hfinish
  intro ret mem pos hp
  obtain ⟨b,c,he,hret,hcount,hframe,hzero⟩ := hp
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl⟩ := he
  let ready : State := ⟨mem,Function.update st.regs 0 ret,pos⟩
  let args := (List.range 56).map (ready.regs ∘ weightControllerRegister)
  obtain ⟨hr16,hr1,hr23,hr32,hr55⟩ := initialWeightController_startState ready mem pos
  change args.getD 16 0 = ready.regs 0 at hr16
  change args.getD 1 0 = ready.regs 73 at hr1
  change args.getD 23 0 = ready.regs 95 at hr23
  change args.getD 32 0 = ready.regs 104 at hr32
  change args.getD 55 0 = ready.regs 127 at hr55
  simp only [ready,Function.update_self] at hr16
  simp [ready,Function.update_of_ne,hm] at hr1
  simp [ready,Function.update_of_ne,hP] at hr23
  simp [ready,Function.update_of_ne,hs] at hr32
  simp [ready,Function.update_of_ne,hL] at hr55
  have hrFit : ret < 2^w := by omega
  have hpw := hregs 95
  have hsw := hregs 104
  have hmw := hregs 73
  refine ⟨args,initialWeightControllerArgs_eval w ready,?_,?_,?_,?_⟩
  · intro a ha
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    dsimp [ready,Function.comp_apply]
    by_cases hr : weightControllerRegister r = 0
    · simpa [hr] using hrFit
    · rw [Function.update_of_ne hr]
      exact hregs _
  · exact ⟨L,ret,stride,m,hr55,hr23,hr16,hr32,hr1,hw,hP ▸ hpw,hs ▸ hsw,hm ▸ hmw,hstride,
      hB,hwidth,fun a ha => hzero a (by omega),by omega⟩
  · simp [stagedInitialWeightContract,hr55,hr1]
  · intro next out pos' hout
    change (stagedInitialWeightContract w h P B).post args mem next out at hout
    simp only [stagedInitialWeightContract,hr16,hret] at hout
    change args.getD 55 0 = L at hr55
    change args.getD 1 0 = m at hr1
    change args.getD 32 0 = stride at hr32
    rw [hr55,hr1,hr32] at hout
    obtain ⟨hn',hptr,hfresh,hkeep,hval⟩ := hout
    exact hInv next out pos' hn' hptr hfresh ((hkeep base (by omega)).trans hcount)
      (fun a ha => (hkeep a (by omega)).trans (hframe a ha)) hval

/-- Store the compact weight base after publishing a branch. The next
round reads the weights at caller-width stride from that descriptor. -/
theorem stagedPackedRound_memory
    {numeric appended : ℕ → ℕ}
    {cursor start collection count stop vCap eCap h L P caller j : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hm : 0 < H.m) (hj : j < count) (htable : collection+1+count ≤ cursor)
    (hcursor : cursor ≤ start)
    (hprefix : CollectionPrefix numeric collection count j cursor vCap eCap h L caller E branches)
    (hstop : start+H.m*L ≤ stop)
    (happend : ∀ a < start+H.m*L, a ≠ collection+1+j → appended a = numeric a)
    (hzero : ZeroFrom appended stop)
    (hspan : BranchWithin appended (appended (collection+1+j)) (collection+1+count) stop vCap eCap L E)
    (hbranch : MinRatio.LSFAt appended (appended (collection+1+j)) vCap eCap h L caller E (branches j))
    (hvalues : ∀ i < H.m, Valid numeric (start+i*L) h L ∧
      fixVal numeric (start+i*L) h L P = weights P ρ query (j+1) (edgeName H i)) :
    let out := Function.update appended stop start
    out ((stop+1)-1) = start ∧ start+(H.m-1)*L+L ≤ stop ∧ ZeroFrom out (stop+1) ∧
    (∀ a < cursor, a ≠ collection+1+j → out a = numeric a) ∧
    CollectionPrefix out collection count (j+1) (stop+1) vCap eCap h L caller E branches ∧
    ∀ e ∈ H.E, Valid out (out ((stop+1)-1)+edgeIndex H e*L) h L ∧
      fixVal out (out ((stop+1)-1)+edgeIndex H e*L) h L P = weights P ρ query (j+1) e := by
  intro out
  have hkeep a (ha : a < stop) : out a = appended a := Function.update_of_ne (ne_of_lt ha) ..
  have hframe a (ha : a < cursor) (hne : a ≠ collection+1+j) : out a = numeric a :=
    (hkeep a (by omega)).trans (happend a (by omega) hne)
  have hmul : (H.m-1)*L+L = H.m*L := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
  have hend : start+(H.m-1)*L+L ≤ stop := by rwa [Nat.add_assoc,hmul]
  have hnew := publishedBranch_cursorWrite (value := start) (by omega) hspan hbranch
  refine ⟨by simp [out],hend,?_,hframe,
    collectionPrefix_succ hprefix hj (by omega) htable hframe hnew,?_⟩
  · intro a ha
    exact (Function.update_of_ne (by omega : a ≠ stop) ..).trans (hzero a (by omega))
  · apply stagedRoundWeightCursor_model H ρ query (Function.update_self ..) hkeep hend
    intro i hi
    have hle := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hle
    have hagree k (hk : k < L) : appended (start+i*L+k) = numeric (start+i*L+k) :=
      happend _ (by omega) (by omega)
    exact ⟨fun k hk => (hagree k hk).trans_lt ((hvalues i hi).1 k hk),
      by simpa only [fixVal,intVal_congr hagree] using (hvalues i hi).2⟩

/-- The memory and controller words carried between last-level rounds.
The cursor bounds the collection and follows the descriptor of the
current strided weight table. -/
noncomputable def stagedRoundStateAtStride (H : MGraph) (vCap eCap h L P caller base count
    handle bound stride : ℕ) (E : Finset ℕ) (branches : ℕ → LSF)
    (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ) (j : ℕ) (st : State) : Prop :=
  let cursor := st.regs 0
  let weight := st.mem (cursor-1)
  st.regs 1 = count ∧ st.regs 3 = base ∧ st.regs 151 = handle ∧
  base+1+count ≤ cursor ∧ cursor ≤ bound ∧ ZeroFrom st.mem cursor ∧
  (∀ a < base, st.mem a = mem a) ∧
  CollectionPrefix st.mem base count j cursor vCap eCap h L caller E branches ∧
  weight+(H.m-1)*stride+L ≤ cursor-1 ∧
  ∀ e ∈ H.E, Valid st.mem (weight+edgeIndex H e*stride) h L ∧
    fixVal st.mem (weight+edgeIndex H e*stride) h L P = weights P ρ query j e

/-- Round invariant for weights kept in their arithmetic workspaces. -/
noncomputable def stagedRoundState (H : MGraph) (vCap eCap h L P caller base count
    handle bound : ℕ) (E : Finset ℕ) (branches : ℕ → LSF)
    (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ) (j : ℕ) (st : State) : Prop :=
  stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
    (narrowWeightSpace L) E branches ρ query mem j st

/-- Resetting the loop index leaves the collection, input, and cursor intact. -/
theorem stagedRoundState_resetIndex {H : MGraph} {vCap eCap h L P caller base count handle bound j : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} {st : State}
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st) :
    stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j
      {st with regs := Function.update st.regs 2 0} := by
  simpa [stagedRoundState,stagedRoundStateAtStride,Function.update] using hs

/-- Unit initialization supplies the first model weights, the cursor
descriptor, and the empty collection prefix for the round loop. -/
theorem stagedInitialRound_state {vCap eCap h L P base count stride next : ℕ}
    {E : Finset ℕ} (branches : ℕ → LSF) (H : MGraph)
    (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hnext : next = base+1+count+2*L+H.m*stride+1)
    (hptr : mem (next-1) = base+1+count+2*L)
    (hcount : mem base = count) (hstride : L ≤ stride) (hm : 0 < H.m)
    (hunit : ∀ i < H.m, Valid mem (base+1+count+2*L+i*stride) h L ∧
      fixVal mem (base+1+count+2*L+i*stride) h L P = 1) :
    base+1+count ≤ next ∧
    mem (next-1)+(H.m-1)*stride+L ≤ next-1 ∧
    CollectionPrefix mem base count 0 next vCap eCap h L P E branches ∧
    ∀ e ∈ H.E,
      Valid mem (mem (next-1)+edgeIndex H e*stride) h L ∧
      fixVal mem (mem (next-1)+edgeIndex H e*stride) h L P = weights P ρ query 0 e := by
  refine ⟨by omega, ?_, ⟨Nat.zero_le _,hcount,?_⟩,?_⟩
  · have hmul : H.m*stride = (H.m-1)*stride+stride := by
      conv_lhs => rw [show H.m = H.m-1+1 by omega]
      rw [Nat.add_mul,Nat.one_mul]
    rw [hptr,hnext,hmul,Nat.add_sub_cancel]
    omega
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)
  · intro e he
    rw [hptr]
    exact hunit _ (edgeIndex_live he).1

/-- The word returned by the unit-weight initializer seeds the staged
controller invariant at iteration zero. -/
theorem stagedRoundStateAtStride_initial {H : MGraph} {vCap eCap h L P caller base count handle bound next stride : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    (st : State) (out : ℕ → ℕ) (pos : ℕ)
    (h1 : st.regs 1 = count) (h3 : st.regs 3 = base) (h151 : st.regs 151 = handle)
    (hm : 0 < H.m) (hstride : L ≤ stride)
    (hnext : next = base+1+count+2*L+H.m*stride+1)
    (hptr : out (next-1) = base+1+count+2*L)
    (hbound : next ≤ bound) (hzero : ZeroFrom out next)
    (hframe : ∀ a < base, out a = st.mem a) (hcount : out base = count)
    (hunit : ∀ i < H.m, Valid out (base+1+count+2*L+i*stride) h L ∧
      fixVal out (base+1+count+2*L+i*stride) h L P = 1) :
    stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query st.mem 0
      ⟨out,Function.update st.regs 0 next,pos⟩ := by
  obtain ⟨hspan,hweightsEnd,hprefix,hvals⟩ :=
    stagedInitialRound_state (vCap := vCap) (eCap := eCap) (E := E)
      branches H ρ query out hnext hptr hcount hstride hm hunit
  have hprefix' : CollectionPrefix out base count 0 next vCap eCap h L caller E branches :=
    ⟨hprefix.1,hprefix.2.1,fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
  simpa [stagedRoundStateAtStride,Function.update] using
    (show st.regs 1 = count ∧ st.regs 3 = base ∧ st.regs 151 = handle ∧
      base+1+count ≤ next ∧ next ≤ bound ∧ ZeroFrom out next ∧
      (∀ a < base, out a = st.mem a) ∧
      CollectionPrefix out base count 0 next vCap eCap h L caller E branches ∧
      out (next-1)+(H.m-1)*stride+L ≤ next-1 ∧
      (∀ e ∈ H.E, Valid out (out (next-1)+edgeIndex H e*stride) h L ∧
        fixVal out (out (next-1)+edgeIndex H e*stride) h L P = weights P ρ query 0 e)
      from ⟨h1,h3,h151,hspan,hbound,hzero,hframe,hprefix',hweightsEnd,hvals⟩)

/-- The word returned by the unit-weight initializer seeds the staged
controller invariant at iteration zero. -/
theorem stagedRoundState_initial {H : MGraph} {vCap eCap h L P caller base count handle bound next : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    (st : State) (out : ℕ → ℕ) (pos : ℕ)
    (h1 : st.regs 1 = count) (h3 : st.regs 3 = base) (h151 : st.regs 151 = handle)
    (hm : 0 < H.m)
    (hnext : next = base+1+count+2*L+H.m*narrowWeightSpace L+1)
    (hptr : out (next-1) = base+1+count+2*L)
    (hbound : next ≤ bound) (hzero : ZeroFrom out next)
    (hframe : ∀ a < base, out a = st.mem a) (hcount : out base = count)
    (hunit : ∀ i < H.m, Valid out (base+1+count+2*L+i*narrowWeightSpace L) h L ∧
      fixVal out (base+1+count+2*L+i*narrowWeightSpace L) h L P = 1) :
    stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query st.mem 0
      ⟨out,Function.update st.regs 0 next,pos⟩ :=
  stagedRoundStateAtStride_initial st out pos h1 h3 h151 hm
    (by unfold narrowWeightSpace; omega) hnext hptr hbound hzero hframe hcount hunit

/-- Advance the round invariant while allowing the output table to use a
different stride from the input table. -/
theorem stagedRoundStateAtStride_next {H : MGraph} {vCap eCap h L P caller base count handle bound j next oldStride stride : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem out : ℕ → ℕ} {st : State} (pos : ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound oldStride E branches ρ query mem j st)
    (hgrowth : st.regs 0 ≤ next) (hbound : next ≤ bound) (hzero : ZeroFrom out next)
    (hframe : ∀ a < base, out a = st.mem a)
    (hprefix : CollectionPrefix out base count (j+1) next vCap eCap h L caller E branches)
    (hweightEnd : out (next-1)+(H.m-1)*stride+L ≤ next-1)
    (hweights : ∀ e ∈ H.E, Valid out (out (next-1)+edgeIndex H e*stride) h L ∧
      fixVal out (out (next-1)+edgeIndex H e*stride) h L P = weights P ρ query (j+1) e) :
    stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem (j+1)
      ⟨out,Function.update (Function.update st.regs 0 next) 2 (j+1),pos⟩ := by
  obtain ⟨h1,h3,h151,hspan,_,_,hmem,_,_,_⟩ := hs
  simp only [stagedRoundStateAtStride]
  simpa [Function.update] using
    (And.intro h1 ⟨h3,h151,hspan.trans hgrowth,hbound,hzero,
      fun a ha => (hframe a ha).trans (hmem a ha),hprefix,hweightEnd,hweights⟩)

/-- Advance the invariant for weights stored in the arithmetic workspace. -/
theorem stagedRoundState_next {H : MGraph} {vCap eCap h L P caller base count handle bound j next : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem out : ℕ → ℕ} {st : State} (pos : ℕ)
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hgrowth : st.regs 0 ≤ next) (hbound : next ≤ bound) (hzero : ZeroFrom out next)
    (hframe : ∀ a < base, out a = st.mem a)
    (hprefix : CollectionPrefix out base count (j+1) next vCap eCap h L caller E branches)
    (hweightEnd : out (next-1)+(H.m-1)*narrowWeightSpace L+L ≤ next-1)
    (hweights : ∀ e ∈ H.E, Valid out (out (next-1)+edgeIndex H e*narrowWeightSpace L) h L ∧
      fixVal out (out (next-1)+edgeIndex H e*narrowWeightSpace L) h L P = weights P ρ query (j+1) e) :
    stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem (j+1)
      ⟨out,Function.update (Function.update st.regs 0 next) 2 (j+1),pos⟩ :=
  stagedRoundStateAtStride_next pos hs hgrowth hbound hzero hframe hprefix hweightEnd hweights

/-- After the last round, the invariant supplies the full collection
and the original handle to the publication procedure. -/
theorem stagedRoundStateAtStride_publish
    {w copy vCap eCap h L P caller base count handle bound stride : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hw : 1 < 2^w) (hsep : handle+1+count ≤ base) (hfit : bound < 2^w) :
    Triple w p (stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride
      E branches ρ query mem count) (publishRuntimeCollection copy)
      (fun o out => ∃ limit, o = .returned limit ∧ handle+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle count count limit vCap eCap h L caller E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = mem a))
      (fun _ => 17*(count+1)+19) := by
  apply (publishRuntimeCollection_triple (w := w) (copy := copy) (bound := bound)
    (vCap := vCap) (eCap := eCap) (h := h) (L := L) (P := caller) (E := E)
    (branches := branches) mem hc hw hsep).conseq
  · intro st hs
    obtain ⟨h1,h3,h151,hspan,hbound,hzero,hframe,hprefix,_,_⟩ := hs
    exact ⟨h3,h151,h1,hspan,hbound,hbound.trans_lt hfit,hprefix,hzero,
      fun a ha => hframe a (by omega)⟩
  · exact fun _ _ hp => hp
  · exact fun _ _ => le_rfl

/-- After the last round, the invariant supplies the full collection
and the original handle to the publication procedure. -/
theorem stagedRoundState_publish
    {w copy vCap eCap h L P caller base count handle bound : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hw : 1 < 2^w) (hsep : handle+1+count ≤ base) (hfit : bound < 2^w) :
    Triple w p (stagedRoundState H vCap eCap h L P caller base count handle bound
      E branches ρ query mem count) (publishRuntimeCollection copy)
      (fun o out => ∃ limit, o = .returned limit ∧ handle+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle count count limit vCap eCap h L caller E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = mem a))
      (fun _ => 17*(count+1)+19) :=
  stagedRoundStateAtStride_publish H ρ query mem hc hw hsep hfit

/-- Iterate the installed round with the concrete collection and weight
invariant, using the controller's seventy-word argument list. -/
theorem stagedControllerRoundsAtStride_triple
    {w entry vCap eCap h L P caller base count handle bound budget stride : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) :
    let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem
    (∀ j < count, ∀ st, Inv j st → st.regs 2 = j →
      let args := (List.range 70).map (st.regs ∘ roundControllerRegister)
      ∃ C : Contract, MeetsContract w p entry C ∧
        (∀ a ∈ args, a < 2^w) ∧ C.pre args st.mem ∧ C.cost args st.mem ≤ budget ∧
        ∀ ret out pos, C.post args st.mem ret out →
          Inv (j+1) ⟨out,Function.update (Function.update st.regs 0 ret) 2 (j+1),pos⟩) →
    Triple w p (Inv 0) (lastLevelRoundsBody entry publishedRoundArgs)
      (normalPost (Inv count)) (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) := by
  intro Inv hstep
  apply lastLevelRounds_triple count budget Inv hw hcount
    (fun _ h => by simpa [Inv,stagedRoundStateAtStride,Function.update] using h) (fun _ _ h => h.1)
  intro j hj st hinv hidx
  obtain ⟨C,hc,hwords,hpre,hcost,hpost⟩ := hstep j hj st hinv hidx
  exact ⟨C,_,hc,publishedRoundArgs_eval w st,hwords,hpre,hcost,hpost⟩

/-- Iterate the installed round with the concrete collection and weight
invariant, using the controller's seventy-word argument list. -/
theorem stagedControllerRounds_triple
    {w entry vCap eCap h L P caller base count handle bound budget : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) :
    let Inv := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem
    (∀ j < count, ∀ st, Inv j st → st.regs 2 = j →
      let args := (List.range 70).map (st.regs ∘ roundControllerRegister)
      ∃ C : Contract, MeetsContract w p entry C ∧
        (∀ a ∈ args, a < 2^w) ∧ C.pre args st.mem ∧ C.cost args st.mem ≤ budget ∧
        ∀ ret out pos, C.post args st.mem ret out →
          Inv (j+1) ⟨out,Function.update (Function.update st.regs 0 ret) 2 (j+1),pos⟩) →
    Triple w p (Inv 0) (lastLevelRoundsBody entry publishedRoundArgs)
      (normalPost (Inv count)) (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) :=
  stagedControllerRoundsAtStride_triple H ρ query mem hw hcount

/-- Finish the runtime setup and rebuild the collection. -/
def stagedPreparedCollectionBody (init weights round : ℕ) : Stmt :=
  .seq finishCollectionSetup (stagedCollectionBody init weights round)

/-- Set the weight format, round count, and header address before rebuilding
and publishing the collection. -/
def stagedPreparedCollectionThen (init weights round : ℕ) (finish : Stmt) : Stmt :=
  .seq finishCollectionSetup
    (rebuildCollectionThen init weights round initialWeightControllerArgs publishedRoundArgs finish)

/-- The final setup preserves the packed guest prefix and passes the model's
branch count to the rebuild and publication phases. -/
theorem stagedPreparedCollectionThen_runs
    {w init weights round : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P guestL sim src budget : ℕ)
    (finish : Stmt) (Post : Outcome → State → Prop)
    (hnl : (nonLoopEdges G).Nonempty) (hL : st.regs 127 = L) (hP : st.regs 95 = P)
    (hstride : narrowWeightSpace L < 2^w) :
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let branches := (fixedPointLastLevelTool oracle C).build G ℓ
    st.regs 72 = H.n → st.regs 73 = H.m →
    st.regs 74 = guestL → st.regs 75 = sim → st.regs 141 = src →
    queryHeap H guestL < 2^w → base < 2^w →
    (∀ ready : State, ready.regs 1 = branches.1 → ready.regs 3 = base →
      ready.regs 81 = narrowWeightSpace L → ready.regs 82 = P →
      ready.regs 91 = L → ready.regs 104 = narrowWeightSpace L →
      ready.mem = st.mem →
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → ready.regs r = st.regs r) →
      ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round
        initialWeightControllerArgs publishedRoundArgs finish) ready o out cost ∧ Post o out ∧
        cost ≤ budget) →
    ∃ o out cost, Runs w p ω (stagedPreparedCollectionThen init weights round finish) st o out cost ∧
      Post o out ∧
      cost ≤ 2*(narrowWeightSpaceExpr (.reg 127)).size+collectionHeaderAddress.size+17+budget := by
  intro H base branches hn hm hg hs hsrc hguest hfit hnext
  obtain ⟨ready,cs,hrs,hcount,hbase,h81,h82,h91,h104,hmem,hregs,hcs⟩ :=
    finishCollectionSetup_runs (p := p) (ω := ω) st oracle C G ℓ L P guestL sim src
      hnl hL hP hstride hn hm hg hs hsrc hguest hfit
  obtain ⟨o,out,cr,hrr,hpost,hcr⟩ :=
    hnext ready hcount hbase h81 h82 h91 h104 hmem hregs
  exact ⟨o,out,cs+cr+1,runs_seq_iff.mpr (Or.inr ⟨ready,cs,cr,hrs,hrr,rfl⟩),
    hpost,by omega⟩

/-- Extend the caller's collection with a branch computed on the model
grid. The stored quotient has the same value at both precisions. -/
theorem collectionPrefix_succ_of_grid
    {mem out : ℕ → ℕ}
    {collection count filled limit next vCap eCap h L grid caller : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (hp : CollectionPrefix mem collection count filled limit vCap eCap h L caller E branches)
    (hf : filled < count) (hle : limit ≤ next) (hroom : collection+1+count ≤ limit)
    (hframe : ∀ a < limit, a ≠ collection+1+filled → out a = mem a)
    (hnew : let base := out (collection+1+filled)
      BranchWithin out base (collection+1+count) next vCap eCap L E ∧
        MinRatio.LSFAt out base vCap eCap h L grid E (branches filled)) :
    CollectionPrefix out collection count (filled+1) next vCap eCap h L caller E branches := by
  exact collectionPrefix_succ hp hf hle hroom hframe
    ⟨hnew.1,lsfAt_changePrecision hnew.2 caller⟩

/-- Finish compact collection setup and rebuild at the caller's handle. -/
def stagedCompactCollectionThen (init weights round copy : ℕ) : Stmt :=
  .seq finishCompactCollectionSetup
    (rebuildCollectionThen init weights round initialWeightControllerArgs publishedRoundArgs
      (publishRuntimeCollection copy))

end MinCostFlow.LastLevelProgram
