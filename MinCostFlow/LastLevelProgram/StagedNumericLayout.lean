module

public import MinCostFlow.LastLevelProgram.StagedTraversal
import WordRAM.Logic
import WordRAM.Link
import Mathlib.Tactic

/-!
# Runtime addresses for the staged numeric pass

The rebuild of Definition 5.8 (pages 19–20) places its numeric inputs
after the selected tree's incidence records and reserves the distance array.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF WideWord

/-- Compute the numeric addresses from the guest cursor, graph counts,
traversal levels, and the host limb count. -/
def stagedNumericLayoutArgs (n m levels cursor limbs : Expr) : List Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let dest := add (add cursor (.const 1)) m
  let adj := add (add dest n) (stagedTraversalReserveExpr n levels)
  let records := add adj n
  let tails := add records (mul (.const 6) n)
  let heads := add tails m
  let lengths := add heads m
  let block := mul m limbs
  let old := add lengths block
  let denom := add (add old block) limbs
  let dist := add denom limbs
  let heap := add dist (mul n limbs)
  [tails,heads,lengths,old,denom,dist,heap]

/-- All intermediate address arithmetic fits as soon as the reserved
numeric allocation and its small constants fit the host word. -/
theorem stagedNumericLayoutArgs_eval {w : ℕ} {st : State} {ne me ke ce le : Expr}
    (n m levels cursor L : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hk : ke.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hL : le.eval w st = some L) (hnPos : 0 < n)
    (hw : 6 < 2^w) :
    let dest := cursor+1+m
    let adj := dest+n+stagedTraversalReserve n levels
    let records := adj+n
    let tails := records+6*n
    let heads := tails+m
    let lengths := heads+m
    let old := lengths+m*L
    let denom := old+m*L+L
    let dist := denom+L
    let heap := dist+n*L
    heap < 2^w →
    evalArgs w st (stagedNumericLayoutArgs ne me ke ce le) =
      some [tails,heads,lengths,old,denom,dist,heap] := by
  intro dest adj records tails heads lengths old denom dist heap hfit
  have hdist : dist < 2^w := (Nat.le_add_right _ _).trans_lt hfit
  have hdenom : denom < 2^w := (Nat.le_add_right _ _).trans_lt hdist
  have hweightEnd : old+m*L < 2^w := (Nat.le_add_right _ _).trans_lt hdenom
  have hold : old < 2^w := (Nat.le_add_right _ _).trans_lt hweightEnd
  have hlengths : lengths < 2^w := (Nat.le_add_right _ _).trans_lt hold
  have hheads : heads < 2^w := (Nat.le_add_right _ _).trans_lt hlengths
  have htails : tails < 2^w := (Nat.le_add_right _ _).trans_lt hheads
  have hrecords : records < 2^w := (Nat.le_add_right _ _).trans_lt htails
  have hadj : adj < 2^w := (Nat.le_add_right _ _).trans_lt hrecords
  have hparents : dest+n < 2^w := (Nat.le_add_right _ _).trans_lt hadj
  have hdest : dest < 2^w := (Nat.le_add_right _ _).trans_lt hparents
  have hcursor : cursor+1 < 2^w := (Nat.le_add_right _ _).trans_lt hdest
  have hres : stagedTraversalReserve n levels < 2^w := (Nat.le_add_left _ _).trans_lt hadj
  have hreserve := stagedTraversalReserveExpr_eval n levels hn hk hnPos hres
  have hone : 1 < 2^w := by omega
  have hincidence : 6*n < 2^w := (Nat.le_add_left _ _).trans_lt htails
  have hblock : m*L < 2^w := (Nat.le_add_left _ _).trans_lt hold
  have hdistBlock : n*L < 2^w := (Nat.le_add_left _ _).trans_lt hfit
  simp only [stagedNumericLayoutArgs,evalArgs,Expr.eval,BinOp.eval,hn,hm,hc,hL,hreserve,
    hone,hw,hcursor,ite_eq_left]
  simp only [heap,dist,denom,old,lengths,heads,tails,records,adj,dest] at *
  simp only [hdest,hparents,hadj,hrecords,hincidence,htails,hheads,hlengths,hblock,hold,
    hweightEnd,hdenom,hdist,hdistBlock,hfit,ite_eq_left]

/-- Evaluate a list of address expressions into distinct scratch registers. -/
def stagedAddressAssignments : List ℕ → List Expr → Stmt
  | r :: rs, e :: es => .seq (.assign r e) (stagedAddressAssignments rs es)
  | _, _ => .nop

/-- The address assignment sequence preserves memory and updates only its destinations. -/
theorem addressAssignments_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (rs : List ℕ) (es : List Expr) (vs : List ℕ)
    (hlen : rs.length = es.length)
    (he : ∀ mid, (∀ r, r ∉ rs → mid.regs r = st.regs r) → evalArgs w mid es = some vs) :
    ∃ out cost, Runs w p ω (stagedAddressAssignments rs es) st .normal out cost ∧
      out.mem = st.mem ∧ out.regs =
        (rs.zip vs).foldl (fun regs pair => Function.update regs pair.1 pair.2) st.regs ∧
      cost ≤ argsSize es+2*rs.length+1 := by
  induction rs generalizing st es vs with
  | nil =>
    cases es with
    | cons e es => simp at hlen
    | nil =>
      have hv : vs = [] := by
        simpa [evalArgs,eq_comm] using he st (fun _ _ => rfl)
      subst vs
      exact ⟨st,1,runs_nop_iff.mpr ⟨rfl,rfl,rfl⟩,rfl,rfl,by decide⟩
  | cons r rs ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      have h := he st (fun _ _ => rfl)
      cases hx : e.eval w st <;> cases hxs : evalArgs w st es <;>
        simp [evalArgs,hx,hxs] at h
      rename_i x xs
      subst vs
      let mid := {st with regs := Function.update st.regs r x}
      have htail (next : State) (hf : ∀ j, j ∉ rs → next.regs j = mid.regs j) :
          evalArgs w next es = some xs := by
        have hfull := he next (fun j hj => by
          have hjr : j ≠ r := fun h => hj (by simp [h])
          have hjrs : j ∉ rs := fun h => hj (List.mem_cons_of_mem _ h)
          rw [hf j hjrs]
          simp [mid,Function.update,hjr])
        cases hy : e.eval w next <;> cases hes : evalArgs w next es <;>
          simp [evalArgs,hy,hes] at hfull
        exact congrArg some hfull.2
      obtain ⟨out,c,hr,hm,hregs,hc⟩ := ih mid es xs (by simpa using hlen) htail
      refine ⟨out,e.size+1+c+1,?_,hm,hregs,?_⟩
      · exact runs_seq_iff.mpr (Or.inr ⟨mid,e.size+1,c,
          runs_assign_iff.mpr ⟨x,hx,rfl,rfl,rfl⟩,hr,rfl⟩)
      · simp only [argsSize,List.length_cons]
        omega

/-- Install the addresses and set the packed host-weight stride to the
host limb count. The input registers are left untouched. -/
def installStagedNumericLayoutFrom (widthReg : ℕ) : Stmt :=
  stagedAddressAssignments [21,22,18,26,25,17,20,24]
    (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg widthReg) ++ [.reg widthReg])

/-- The numeric layout setup writes only the designated registers.
The allocation size and addresses are derived from runtime inputs. -/
theorem installStagedNumericLayoutFrom_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m levels cursor L widthReg : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hk : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hL : st.regs widthReg = L) (hnPos : 0 < n) (hw : 6 < 2^w)
    (hwidthReg : widthReg ∉ ([21,22,18,26,25,17,20,24] : List ℕ)) :
    let dest := cursor+1+m
    let adj := dest+n+stagedTraversalReserve n levels
    let tails := adj+n+6*n
    let heads := tails+m
    let lengths := heads+m
    let old := lengths+m*L
    let denom := old+m*L+L
    let dist := denom+L
    let heap := dist+n*L
    heap < 2^w →
    ∃ out cost, Runs w p ω (installStagedNumericLayoutFrom widthReg) st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 21 = tails ∧ out.regs 22 = heads ∧
      out.regs 18 = lengths ∧ out.regs 26 = old ∧ out.regs 25 = denom ∧
      out.regs 17 = dist ∧ out.regs 20 = heap ∧ out.regs 24 = L ∧
      (∀ r, r ∉ ([21,22,18,26,25,17,20,24] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize
        (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg widthReg) ++ [.reg widthReg])+17 := by
  intro dest adj tails heads lengths old denom dist heap hfit
  let rs := [21,22,18,26,25,17,20,24]
  let es := stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg widthReg)
  have he (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid (es ++ [.reg widthReg]) =
        some [tails,heads,lengths,old,denom,dist,heap,L] := by
    have heL : mid.regs widthReg = L := (hf _ hwidthReg).trans hL
    have haddr : evalArgs w mid es = some [tails,heads,lengths,old,denom,dist,heap] :=
      stagedNumericLayoutArgs_eval (ne := .reg 0) (me := .reg 1) (ke := .reg 14)
        (ce := .reg 12) (le := .reg widthReg) n m levels cursor L
        (congrArg some ((hf _ (by decide)).trans hn))
        (congrArg some ((hf _ (by decide)).trans hm))
        (congrArg some ((hf _ (by decide)).trans hk))
        (congrArg some ((hf _ (by decide)).trans hc))
        (congrArg some heL) hnPos hw hfit
    exact Link.evalArgs_append haddr (by simp [evalArgs,Expr.eval,heL])
  obtain ⟨out,c,hr,hmem,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs (es ++ [.reg widthReg])
      [tails,heads,lengths,old,denom,dist,heap,L] (by rfl) he
  refine ⟨out,c,hr,hmem,?_,?_,?_,?_,?_,?_,?_,?_,?_,hcost⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h21 h22 h18 h26 h25 h17 h20 h24
  simp [h21,h22,h18,h26,h25,h17,h20,h24]

/-- The scratch width covers the root distances at the model precision,
using the caller width and the binary-lifting depth already in registers. -/
def stagedScratchWidthExpr : Expr :=
  .bin .add (.reg 19)
    (.bin .div (.bin .add (.bin .add (.reg 23) (.reg 14)) (.const 7)) (.const 4))

/-- Compute the scratch width without changing the caller format. -/
theorem stagedScratchWidthExpr_eval {w : ℕ} (st : State) (L P levels : ℕ)
    (hL : st.regs 19 = L) (hP : st.regs 23 = P) (hlevels : st.regs 14 = levels)
    (hsmall : 7 < 2^w) (hroom : P+levels+7 < 2^w)
    (hfit : L+(P+levels+7)/4 < 2^w) :
    stagedScratchWidthExpr.eval w st = some (L+(P+levels+7)/4) := by
  unfold stagedScratchWidthExpr
  eval_expr

/-- Compute the wider width and install the numeric scratch addresses. -/
def installWideStagedNumericLayout : Stmt :=
  .seq (.assign 64 stagedScratchWidthExpr) (installStagedNumericLayoutFrom 64)

/-- The widened layout preserves the caller width while setting the
numeric width, addresses, and stride from the reserved scratch region. -/
theorem installWideStagedNumericLayout_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m levels cursor L P : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hk : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hL : st.regs 19 = L) (hP : st.regs 23 = P)
    (hnPos : 0 < n) (hw : 7 < 2^w) (hroom : P+levels+7 < 2^w)
    (hwidth : L+(P+levels+7)/4 < 2^w) :
    let K := L+(P+levels+7)/4
    let dest := cursor+1+m
    let adj := dest+n+stagedTraversalReserve n levels
    let tails := adj+n+6*n
    let heads := tails+m
    let lengths := heads+m
    let old := lengths+m*K
    let denom := old+m*K+K
    let dist := denom+K
    let heap := dist+n*K
    heap < 2^w →
    ∃ out cost, Runs w p ω installWideStagedNumericLayout st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 21 = tails ∧ out.regs 22 = heads ∧
      out.regs 18 = lengths ∧ out.regs 26 = old ∧ out.regs 25 = denom ∧
      out.regs 17 = dist ∧ out.regs 20 = heap ∧ out.regs 24 = K ∧
      (∀ r, r ∉ ([64,21,22,18,26,25,17,20,24] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ stagedScratchWidthExpr.size+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
          [.reg 64])+19 := by
  intro K dest adj tails heads lengths old denom dist heap hfit
  let mid := {st with regs := Function.update st.regs 64 K}
  have hassign : Runs w p ω (.assign 64 stagedScratchWidthExpr) st .normal mid
      (stagedScratchWidthExpr.size+1) :=
    runs_assign_iff.mpr ⟨K,stagedScratchWidthExpr_eval st L P levels hL hP hk hw hroom hwidth,rfl,rfl,rfl⟩
  obtain ⟨out,c,hr,hmem,h21,h22,h18,h26,h25,h17,h20,h24,hregs,hcost⟩ :=
    installStagedNumericLayoutFrom_runs (ω := ω) mid n m levels cursor K 64
      (by simpa [mid,Function.update] using hn) (by simpa [mid,Function.update] using hm)
      (by simpa [mid,Function.update] using hk) (by simpa [mid,Function.update] using hc)
      (by simp [mid]) hnPos ((by decide : 6 < 7).trans hw) (by decide) hfit
  refine ⟨out,stagedScratchWidthExpr.size+1+c+1,?_,hmem,h21,h22,h18,h26,h25,h17,h20,h24,?_,by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,c,hassign,hr,rfl⟩)
  · intro r h
    have h64 : r ≠ 64 := fun he => h (by simp [he])
    have hrest : r ∉ ([21,22,18,26,25,17,20,24] : List ℕ) :=
      fun hm => h (List.mem_cons_of_mem _ hm)
    exact (hregs r hrest).trans (by simp [mid,h64])

/-- Install the layout for the caller-width numeric pass. -/
def installStagedNumericLayout : Stmt := installStagedNumericLayoutFrom 19

/-- The numeric layout setup writes only the designated registers.
The allocation size and addresses are derived from runtime inputs. -/
theorem installStagedNumericLayout_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m levels cursor L : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hk : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hL : st.regs 19 = L) (hnPos : 0 < n) (hw : 6 < 2^w) :
    let dest := cursor+1+m
    let adj := dest+n+stagedTraversalReserve n levels
    let tails := adj+n+6*n
    let heads := tails+m
    let lengths := heads+m
    let old := lengths+m*L
    let denom := old+m*L+L
    let dist := denom+L
    let heap := dist+n*L
    heap < 2^w →
    ∃ out cost, Runs w p ω installStagedNumericLayout st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 21 = tails ∧ out.regs 22 = heads ∧
      out.regs 18 = lengths ∧ out.regs 26 = old ∧ out.regs 25 = denom ∧
      out.regs 17 = dist ∧ out.regs 20 = heap ∧ out.regs 24 = L ∧
      (∀ r, r ∉ ([21,22,18,26,25,17,20,24] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize
        (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 19) ++ [.reg 19])+17 := by
  exact installStagedNumericLayoutFrom_runs st n m levels cursor L 19 hn hm hk hc hL hnPos hw
    (by decide)

/-- Install the runtime pointers and populate the corresponding inputs. -/
def installAndPrepareStagedNumericBody (copy lengths weights prepare : ℕ) : Stmt :=
  .seq installStagedNumericLayout (stagedNumericPreparationBody copy lengths weights prepare)

/-- Runtime layout setup and numeric input preparation leave the round
ready to allocate its root distances and to compute updated weights. -/
theorem installAndPrepareStagedNumeric_runs {w h P cap copy pack packWeights prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (staging cursor levels src names L : ℕ) (len : ℕ → ℤ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hp : MeetsContract w p pack (packValuesContract w cap G))
    (hStage : st.regs 5 = staging) (hSrc : st.regs 27 = src)
    (hNames : st.regs 28 = names) (hL : st.regs 19 = L) (hm : st.regs 1 = G.m)
    (hn : st.regs 0 = G.n) (hk : st.regs 14 = levels) (hCursor : st.regs 12 = cursor)
    (hnPos : 0 < G.n) (hw : 6 < 2^w) (hlimbs : L < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hat : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hl : ∀ e ∈ G.E, Num.Valid st.mem (src+e*L) h L ∧
      Num.intVal st.mem (src+e*L) h L = len e)
    (weightSrc weightStride scale : ℕ)
    (hpack : MeetsContract w p packWeights (packHostWeightsContract w h P))
    (hprep : MeetsContract w p prepare (denominatorContract w h))
    (hWeight : st.regs 31 = weightSrc) (hStride : st.regs 32 = weightStride)
    (hScale : st.regs 35 = scale)
    (hP : st.regs 23 = P) (hwordStride : weightStride < 2^w)
    (hLS : L ≤ weightStride)
    (hvalid : ∀ i < G.m, Num.Valid st.mem (weightSrc+i*weightStride) h L)
    (hscaleFit : scale < 2^w) (hPFit : P < 2^w)
    (hfit : Num.Fits h L (scale : ℤ))
    (hscaled : Num.Fits h L ((scale : ℤ)*(2 : ℤ)^P))
    :
    let dest := cursor+1+G.m
    let adj := dest+G.n+stagedTraversalReserve G.n levels
    let dst := adj+G.n+6*G.n
    let lengths := dst+2*G.m
    let old := lengths+G.m*L
    let denom := old+G.m*L+L
    let dist := old+G.m*L+2*L
    let heap := dist+G.n*L
    staging+2*G.m ≤ dst → (src ≤ dst ∧ ∀ e ∈ G.E, src+e*L+L ≤ dst) → names+G.m ≤ dst →
    weightSrc+(G.m-1)*weightStride+L ≤ dst → ZeroFrom st.mem dst → heap < 2^w →
    ∃ out cost, Runs w p ω (installAndPrepareStagedNumericBody copy pack packWeights prepare)
      st .normal out cost ∧
      ListAt out.mem dst (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (dst+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ i < G.m, Num.Valid out.mem (lengths+i*L) h L ∧
        Num.intVal out.mem (lengths+i*L) h L = len (edgeName G i)) ∧
      (∀ i < G.m, Num.Valid out.mem (old+i*L) h L ∧
        Num.fixVal out.mem (old+i*L) h L P =
          Num.fixVal st.mem (weightSrc+i*weightStride) h L P) ∧
      Num.Valid out.mem denom h L ∧
      Num.intVal out.mem denom h L = (scale : ℤ)*(2 : ℤ)^P ∧
      out.regs 34 = dist ∧ ZeroFrom out.mem dist ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      out.regs 21 = dst ∧ out.regs 22 = dst+G.m ∧ out.regs 18 = lengths ∧
      out.regs 26 = old ∧ out.regs 25 = denom ∧ out.regs 17 = dist ∧ out.regs 20 = heap ∧
      out.regs 24 = L ∧
      (∀ r, r ∉ ([21,22,18,26,25,17,20,24,29,30,33,34] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ (17*L+75)*G.m+(35*L+60)*G.m+56*L+137+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 19) ++
          [.reg 19]) := by
  intro dest adj dst lengths old denom dist heap hsep hsrc hnames hsepWeight hz hroom
  have hlenEq : dst+G.m+G.m = lengths := by dsimp [lengths]; omega
  have hdistEq : old+G.m*L+L+L = dist := by dsimp [dist]; omega
  have hroom' : old < 2^w := by dsimp [heap,dist] at hroom; omega
  have hroomAll : dist < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  have hlayoutFit : (dst+G.m+G.m+G.m*L+G.m*L+L+L)+G.n*L < 2^w := by
    rw [hlenEq]
    change (old+G.m*L+L+L)+G.n*L < 2^w
    rwa [hdistEq]
  obtain ⟨mid,cl,hlayout,hmem,htails,hheads,hlen,hold,hden,hdist,hheap,hstride,hregs,hcl⟩ :=
    installStagedNumericLayout_runs (p := p) (ω := ω) st G.n G.m levels cursor L
      hn hm hk hCursor hL hnPos hw hlayoutFit
  rw [hlenEq] at hlen hold hden hdist hheap
  change mid.regs 17 = old+G.m*L+L+L at hdist
  change mid.regs 20 = old+G.m*L+L+L+G.n*L at hheap
  rw [hdistEq] at hdist hheap
  have hreg (r : ℕ) (hr : r ∉ ([21,22,18,26,25,17,20,24] : List ℕ)) :=
    hregs r hr
  obtain ⟨out,cp,hprepRun,ht',hh',hl',hw',hd',hdv,hend,hzero,hframe,hpreRegs,hcp⟩ :=
    stagedNumericPreparation_runs (ω := ω) mid G staging dst src names L len hc hp
      ((hreg _ (by decide)).trans hStage) htails hlen
      ((hreg _ (by decide)).trans hSrc) ((hreg _ (by decide)).trans hNames)
      ((hreg _ (by decide)).trans hL) ((hreg _ (by decide)).trans hm)
      (by omega) hlimbs hsep hsrc hnames hroom'
      (by rw [hmem]; exact ht) (by rw [hmem]; exact hh) (by rw [hmem]; exact hat)
      hcap (by rw [hmem]; exact hl) (by rw [hmem]; exact hz)
      weightSrc weightStride scale hpack hprep
      ((hreg _ (by decide)).trans hWeight) ((hreg _ (by decide)).trans hStride)
      hold ((hreg _ (by decide)).trans hScale) ((hreg _ (by decide)).trans hP)
      hwordStride hsepWeight hLS (by rw [hmem]; exact hvalid)
      hscaleFit hPFit hfit hscaled hroomAll
  refine ⟨out,cl+cp+1,runs_seq_iff.mpr (Or.inr ⟨mid,cl,cp,hlayout,hprepRun,rfl⟩),
    ht',hh',hl',?_,hd',hdv,hend,hzero,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by omega⟩
  · simpa only [hmem] using hw'
  · simpa only [hmem] using hframe
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans htails
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hheads
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hlen
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hold
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hden
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hdist
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hheap
  · exact (hpreRegs _ (by decide) (by decide) (by decide) (by decide)).trans hstride
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h21,h22,h18,h26,h25,h17,h20,h24,h29,h30,h33,h34⟩ := hr
    exact (hpreRegs r h29 h30 h33 h34).trans
      (hregs r (by simp [h21,h22,h18,h26,h25,h17,h20,h24]))

/-- The prepared host buffers and retained tree give the numeric
precondition with all disjointness bounds supplied by the allocation. -/
theorem stretchWeight_pre_of_preparedLayout {w h Q : ℕ} (G T H : MGraph)
    (kept : List ℕ) (len : ℕ → ℤ)
    (staging cursor levels N P j B : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (mem out : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hdecode : decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T)
    (hnd : kept.Nodup) (hsize : kept.length ≤ G.n) (hw : 2 < 2^w)
    (hn : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hm : H.m = G.m)
    (hBounds : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h N : ℤ)) :
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*N
    let denom := old+G.m*N+N
    let dist := old+G.m*N+2*N
    let heap := dist+G.n*N
    (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
      adj records).post [dest,staging,staging+G.m,adj,records,kept.length] mem 0 out →
    (∀ a, dest+G.n ≤ a → a < records → mem a = 0) →
    ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    (∀ i < G.m, Num.Valid mem (lengths+i*N) h N ∧ Num.intVal mem (lengths+i*N) h N = len i) →
    Num.Valid mem denom h N → Num.intVal mem denom h N = scale*(2 : ℤ)^P →
    (∀ i < H.m, Num.Valid mem (old+i*N) h N ∧
      Num.fixVal mem (old+i*N) h N P = weights P (scale : ℝ) query j (edgeName H i)) →
    ZeroFrom mem dist → heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w →
    (stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query).pre
      [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,N,heap,tails,heads,P,G.m,
        old,N,denom,edgeStretchSpace N] out := by
  intro dest parents edges depths queue adj records tails heads lengths old denom dist heap
    hpost hz ht hh hlen hden hdenVal hweights hzero hroom
  have hTL : tails ≤ lengths := Nat.le_add_right _ _
  have hHO : heads+G.m = lengths := by dsimp [heads,lengths]; omega
  have hLO : lengths+G.m*N = old := rfl
  have hOD : old ≤ dist := by dsimp [dist]; omega
  have hDenDist : denom+N ≤ dist := by dsimp [denom,dist]; omega
  have hOld (i : ℕ) (hi : i < H.m) : tails ≤ old+i*N ∧ old+i*N+N ≤ dist := by
    have h₁ : tails ≤ old+i*N := hTL.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have h₂ : (i+1)*N ≤ G.m*N := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,Nat.one_mul] at h₂
    exact ⟨h₁,by dsimp [dist]; omega⟩
  exact stretchWeight_pre_of_stagedAdjacency G T H kept len staging dest levels dist lengths
    N heap tails heads P old N denom j B scale query mem out ℓ v γ hv hconn htree hdecode
    hnd hsize hw hn hRows ht hh hlen hBounds hCap ⟨hden,hdenVal⟩ hweights hpost hz
    le_rfl (Nat.le_add_right _ _) hTL hOld
    (hTL.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))
    hDenDist ((Nat.le_add_right _ _).trans (hHO.le.trans ((Nat.le_add_right _ _).trans hOD)))
    (hHO.le.trans ((Nat.le_add_right _ _).trans hOD))
    (hLO.le.trans hOD) hzero le_rfl hroom

/-- The combined numeric call's computed addresses and stride fit
if the last workspace cell fits. Precision and levels are input words. -/
theorem stagedNumericWords_fit (w n m cursor levels N P : ℕ)
    (hm : 0 < m) (hlevel : levels < 2^w) (hprec : P < 2^w) :
    let dest := cursor+1+m
    let parents := dest+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    let records := adj+n
    let tails := records+6*n
    let heads := tails+m
    let lengths := tails+2*m
    let old := lengths+m*N
    let denom := old+m*N+N
    let dist := old+m*N+2*N
    let heap := dist+n*N
    heap+(n-1)*N+m*edgeStretchSpace N < 2^w →
    ∀ x ∈ [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,N,heap,tails,heads,P,m,
      old,N,denom,edgeStretchSpace N], x < 2^w := by
  intro dest parents edges depths queue adj records tails heads lengths old denom dist heap hroom
  have hHeap : heap < 2^w := by omega
  have hDist : dist < 2^w := (Nat.le_add_right _ _).trans_lt hHeap
  have hDen : denom < 2^w := by dsimp [denom,dist] at *; omega
  have hOld : old < 2^w :=
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans_lt hDen
  have hLengths : lengths < 2^w := (Nat.le_add_right _ _).trans_lt hOld
  have hTails : tails < 2^w := (Nat.le_add_right _ _).trans_lt hLengths
  have hHeads : heads < 2^w := by dsimp [heads,lengths] at *; omega
  have hRecords : records < 2^w := (Nat.le_add_right _ _).trans_lt hTails
  have hAdj : adj < 2^w := (Nat.le_add_right _ _).trans_lt hRecords
  obtain ⟨_,_,_,hqueue⟩ := stagedTraversalReserve_layout parents n levels
  have hQueue : queue < 2^w := (Nat.le_add_right _ _).trans_lt (hqueue.trans hAdj)
  have hDepths : depths < 2^w := (Nat.le_add_right _ _).trans_lt hQueue
  have hEdges : edges < 2^w := (Nat.le_add_right _ _).trans_lt hDepths
  have hParents : parents < 2^w := (Nat.le_add_right _ _).trans_lt hEdges
  have hN : N < 2^w := (Nat.le_add_left _ _).trans_lt hDen
  have hn : n < 2^w := (Nat.le_add_left _ _).trans_lt hParents
  have hM : m < 2^w := (Nat.le_add_left _ _).trans_lt
    ((Nat.le_add_right _ _).trans_lt hParents)
  have hBlock : m*edgeStretchSpace N < 2^w := (Nat.le_add_left _ _).trans_lt hroom
  have hStride : edgeStretchSpace N < 2^w := (Nat.le_mul_of_pos_left _ hm).trans_lt hBlock
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | assumption | exact Nat.two_pow_pos _

/-- Run the numeric pass on prepared inputs, deriving its memory and
word preconditions from the concrete staged allocation. -/
theorem preparedStagedNumericRound_runs {w h Q adjacency numeric insert : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (L staging cursor levels count widthReg : ℕ) (hwidthReg : widthReg ≠ 15)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (N P j B : ℕ) (len : ℕ → ℤ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hN : st.regs widthReg = N) (hP : st.regs 23 = P) (hs : st.regs 24 = N)
    (hNPos : 0 < N) (hmPos : 0 < G.m)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) (hlevels : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hprec : P < 2^w)
    (hBounds : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h N : ℤ)) :
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*N
    let denom := old+G.m*N+N
    let dist := old+G.m*N+2*N
    let heap := dist+G.n*N
    let words := [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,N,heap,
      tails,heads,P,G.m,old,N,denom,edgeStretchSpace N]
    let C := stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query
    MeetsContract w p numeric C →
    st.regs 17 = dist → st.regs 18 = lengths → st.regs 20 = heap →
    st.regs 21 = tails → st.regs 22 = heads → st.regs 26 = old → st.regs 25 = denom →
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest →
    (∀ a, dest+G.n ≤ a → a < records → st.mem a = 0) →
    ListAt st.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt st.mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    (∀ i < G.m, Num.Valid st.mem (lengths+i*N) h N ∧ Num.intVal st.mem (lengths+i*N) h N = len i) →
    Num.Valid st.mem denom h N → Num.intVal st.mem denom h N = scale*(2 : ℤ)^P →
    (∀ i < H.m, Num.Valid st.mem (old+i*N) h N ∧
      Num.fixVal st.mem (old+i*N) h N P = weights P (scale : ℝ) query j (edgeName H i)) →
    ZeroFrom st.mem dist → heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (stagedNumericBodyFrom adjacency numeric widthReg) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < adj, mid.mem a = st.mem a) ∧
      (∀ a < parents, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom widthReg)+112*count+stagedNumericFactor N levels*(G.m+1)+13 := by
  intro dest parents edges depths queue adj records tails heads lengths old denom dist heap words C
    hC hd hLen hheap htReg hhReg ho hb hTree hsep hz htMem hhMem hlen hden hdenVal hweights
    hzero hroom
  have hrecords : records+6*G.n < 2^w := by
    change tails < 2^w
    have h₁ : tails ≤ lengths := Nat.le_add_right _ _
    have h₂ : lengths ≤ old := Nat.le_add_right _ _
    have h₃ : old ≤ dist := by dsimp [dist]; omega
    have h₄ : dist ≤ heap := Nat.le_add_right _ _
    exact (h₁.trans (h₂.trans (h₃.trans h₄))).trans_lt (by omega)
  have hword : ∀ x ∈ words, x < 2^w :=
    stagedNumericWords_fit w G.n G.m cursor levels N P hmPos
      (Nat.lt_succ_self _ |>.trans hRows) hprec hroom
  have hrun := stagedNumericRound_runs (ω := ω) st G T H L staging cursor levels count widthReg hwidthReg
    mem ℓ v γ he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos
    dist lengths N heap tails heads P old N denom j len scale query
    hd hLen hN hheap htReg hhReg hP ho hs hb hNPos hE hV hnm heq
    hC hword hTree hsep hrecords (by
    intro kept mid hcount hnd hdecode hpost
    obtain ⟨xs,hxs,hsize,_⟩ := hTree
    have hkSize : kept.length ≤ G.n := hcount ▸ (hxs.symm ▸ hsize)
    rw [hcount] at hpost
    exact stretchWeight_pre_of_preparedLayout G T H kept len staging cursor levels N P j B
      scale query st.mem mid ℓ v γ hv hconn htree hdecode hnd hkSize (by omega)
      hlevels hRows heq hBounds hCap hpost hz htMem hhMem hlen hden hdenVal
      hweights hzero hroom)
  obtain ⟨mid,out,cost,hr,hpost,hmid,hregs,hcost⟩ := hrun
  refine ⟨mid,out,cost,hr,hpost,hmid,?_,hregs,hcost⟩
  intro a ha
  exact (hpost.2.2.2.2 a ha).trans (hmid a (ha.trans_le (Nat.le_add_right _ _)))

/-- Numeric preparation starts after the incidence records. Its prefix
frame preserves the retained tree and the zero cells needed by traversal. -/
theorem retainedTree_of_numericPreparation {G T : MGraph} {base dest count levels : ℕ}
    {mem before after : ℕ → ℕ}
    (hTree : selectedTreeAt G T base dest count mem before)
    (hbase : base ≤ dest)
    (hframe : ∀ a < dest+G.n+stagedTraversalReserve G.n levels+G.n+6*G.n,
      after a = before a) :
    retainedStagedTreeAt G T base dest count mem after ∧
      ∀ a, dest+G.n ≤ a →
        a < dest+G.n+stagedTraversalReserve G.n levels+G.n → after a = 0 := by
  have hdest : dest+G.n ≤ dest+G.n+stagedTraversalReserve G.n levels+G.n+6*G.n := by omega
  have hzero : ZeroFrom before (dest+G.n) := by
    obtain ⟨_,_,_,_,_,_,_,hz⟩ := hTree
    exact hz
  refine ⟨retainedStagedTreeAt_of_frame hTree (by omega) hdest hframe,?_⟩
  intro a ha hb
  exact (hframe a (hb.trans_le (Nat.le_add_right _ _))).trans (hzero a ha)

/-- Prepare host buffers, build tree incidences, and compute the next
round of stretches and weights. -/
def prepareAndRunStagedNumericBody (copy pack packWeights prepare adjacency numeric : ℕ) : Stmt :=
  .seq (installAndPrepareStagedNumericBody copy pack packWeights prepare)
    (stagedNumericBody adjacency numeric)

/-- A selected tree and the source numeric arrays suffice for the
complete staged numeric run, with the packing costs included. -/
theorem prepareAndRunStagedNumeric_runs {w h Q adjacency numeric insert cap copy pack packWeights prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (L staging cursor levels count : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (N P j B src names weightSrc weightStride scale : ℕ) (len : ℕ → ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hN : st.regs 19 = N) (hP : st.regs 23 = P)
    (hNPos : 0 < N) (hmPos : 0 < G.m)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) (hlevels : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hprec : P < 2^w)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hpack : MeetsContract w p pack (packValuesContract w cap G))
    (hpackWeights : MeetsContract w p packWeights (packHostWeightsContract w h P))
    (hprepare : MeetsContract w p prepare (denominatorContract w h))
    (hsrcReg : st.regs 27 = src) (hnamesReg : st.regs 28 = names)
    (hweightReg : st.regs 31 = weightSrc) (hstrideReg : st.regs 32 = weightStride)
    (hscaleReg : st.regs 35 = scale) (hscaleFit : scale < 2^w)
    (hstrideFit : weightStride < 2^w) (hstride : N ≤ weightStride)
    (hat : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hlen : ∀ e ∈ G.E, Num.Valid st.mem (src+e*N) h N ∧
      Num.intVal st.mem (src+e*N) h N = len e)
    (hvalid : ∀ i < G.m, Num.Valid st.mem (weightSrc+i*weightStride) h N)
    (hfit : Num.Fits h N (scale : ℤ)) (hscaled : Num.Fits h N ((scale : ℤ)*(2 : ℤ)^P))
    (hBounds : ∀ i < G.m, 0 < len (edgeName G i) ∧ len (edgeName G i) ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h N : ℤ)) :
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*N
    let denom := old+G.m*N+N
    let dist := old+G.m*N+2*N
    let heap := dist+G.n*N
    let words := [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,N,heap,
      tails,heads,P,G.m,old,N,denom,edgeStretchSpace N]
    let C := stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T H 0 (len ∘ edgeName G)
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query
    MeetsContract w p numeric C →
    selectedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest →
    (src ≤ tails ∧ ∀ e ∈ G.E, src+e*N+N ≤ tails) → names+G.m ≤ tails → weightSrc+(G.m-1)*weightStride+N ≤ tails →
    (∀ i < H.m, Num.fixVal st.mem (weightSrc+i*weightStride) h N P =
      weights P (scale : ℝ) query j (edgeName H i)) →
    heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (prepareAndRunStagedNumericBody copy pack packWeights prepare adjacency numeric) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < parents, out.mem a = st.mem a) ∧
      out.regs 12 = cursor ∧ out.regs 13 = count ∧ out.regs 20 = heap ∧
      (∀ r, r < 12 ∨ 36 ≤ r ∨ r = 14 ∨ r = 19 ∨ r = 23 ∨ r = 28 →
        out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize stagedNumericArgs+112*count+stagedNumericFactor N levels*(G.m+1)+14+
        (17*N+75)*G.m+(35*N+60)*G.m+56*N+137+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 19) ++
          [.reg 19]) := by
  intro dest parents edges depths queue adj records tails heads lengths old denom dist heap words C
    hC hTree hsep hsrc hnames hweightSep hweights hroom
  have hprefix : 2*G.m ≤ queryWeights G L := by unfold queryWeights queryLengths; omega
  have hdest : dest+G.n ≤ tails := by
    change dest+G.n ≤ dest+G.n+stagedTraversalReserve G.n levels+G.n+6*G.n
    omega
  have hz : ZeroFrom st.mem (dest+G.n) := by
    obtain ⟨_,_,_,_,_,_,_,hz⟩ := hTree
    exact hz
  have hwords := stagedNumericWords_fit w G.n G.m cursor levels N P hmPos
    ((Nat.lt_succ_self _).trans hRows) hprec hroom
  have hNFit : N < 2^w := hwords N (by simp)
  have hheap : heap < 2^w := by omega
  have hstage (i : ℕ) (hi : i < G.m) :
      st.mem (staging+i) = (indexedGraph G).tail i := by
    obtain ⟨_,_,_,_,_,_,hf,_⟩ := hTree
    exact (hf _ (by omega)).trans (ht i hi)
  have hhead (i : ℕ) (hi : i < G.m) :
      st.mem (staging+(G.m+i)) = (indexedGraph G).head i := by
    obtain ⟨_,_,_,_,_,_,hf,_⟩ := hTree
    exact (hf _ (by omega)).trans (hh i hi)
  obtain ⟨ready,cp,hprep,ht',hh',hlen',hw',hd',hdv,_,hz',hf,htR,hhR,hlR,hoR,hdR,hdiR,hhpR,
    hsR,hr,hcp⟩ :=
    installAndPrepareStagedNumeric_runs (ω := ω) st G staging cursor levels src names N len
      hcopy hpack ha hsrcReg hnamesReg hN hm hn hl hc hnPos hw hNFit
      hstage hhead hat hcap hlen weightSrc weightStride scale hpackWeights hprepare
      hweightReg hstrideReg hscaleReg hP hstrideFit hstride hvalid hscaleFit hprec hfit hscaled
      (by omega) hsrc hnames hweightSep (fun a ha => hz a (hdest.trans ha)) hheap
  obtain ⟨hretained,hfresh⟩ := retainedTree_of_numericPreparation hTree hsep hf
  have hmem (i : ℕ) (hi : i < H.m) :
      Num.Valid ready.mem (old+i*N) h N ∧
      Num.fixVal ready.mem (old+i*N) h N P = weights P (scale : ℝ) query j (edgeName H i) :=
    let h := hw' i (by omega)
    ⟨h.1,h.2.trans (hweights i hi)⟩
  obtain ⟨mid,out,cr,hrun,hpost,hmid,_,houtRegs,hcr⟩ :=
    preparedStagedNumericRound_runs (ω := ω) ready G T H L staging cursor levels count 19 (by decide) mem ℓ v γ
      he hi hw hv hconn htree ht hh ((hr _ (by decide)).trans hn)
      ((hr _ (by decide)).trans hm) ((hr _ (by decide)).trans ha)
      ((hr _ (by decide)).trans hc) ((hr _ (by decide)).trans hl) ((hr _ (by decide)).trans hk)
      hnPos N P j B (len ∘ edgeName G) (scale : ℤ) query ((hr _ (by decide)).trans hN)
      ((hr _ (by decide)).trans hP) hsR hNPos hmPos hE hV hnm heq hlevels hRows hprec
      hBounds hCap hC hdiR hlR hhpR htR hhR hoR hdR hretained hsep hfresh ht' hh' hlen'
      hd' hdv hmem hz' hroom
  refine ⟨mid,out,cp+cr+1,runs_seq_iff.mpr (Or.inr ⟨ready,cp,cr,hprep,hrun,rfl⟩),
    hpost,?_,?_,?_,?_,?_,by dsimp only [stagedNumericArgs]; omega⟩
  · intro a ha
    have haAdj : a < adj := ha.trans_le (Nat.le_add_right _ _)
    have haTails : a < tails := haAdj.trans_le
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (hpost.2.2.2.2 a ha).trans ((hmid a haAdj).trans (hf a haTails))
  · exact (houtRegs _ (by decide) (by decide)).trans
      ((hr _ (by decide)).trans hc)
  · exact (houtRegs _ (by decide) (by decide)).trans
      ((hr _ (by decide)).trans hk)
  · exact (houtRegs _ (by decide) (by decide)).trans hhpR
  · intro r hkeep
    exact (houtRegs r (by omega) (by omega)).trans (hr r (by simp; omega))

/-- Select the staged guest tree, then prepare the numeric inputs and
compute the rounded stretches and next weights. -/
def stagedRebuildRoundBody (query dedup copy pack packWeights prepare adjacency numeric : ℕ)
    (args : List Expr) : Stmt :=
  .seq (stagedTreeSelectionBody query dedup args)
    (prepareAndRunStagedNumericBody copy pack packWeights prepare adjacency numeric)

/-- The two parts of the rebuild round share the retained edge count,
guest cursor, and source registers without an intermediate return. -/
theorem stagedRebuildRound_runs {w query dedup copy pack packWeights prepare adjacency numeric : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (guest : Program) (D : ℕ) (G T : MGraph)
    (L sim staging : ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ) (args : List Expr) (vs : List ℕ)
    (ready : List ℕ → (ℕ → ℕ) → Prop) (budget : ℕ)
    (hq : MeetsContract w p query
      { pre := ready
        post := fun _ => stagedGuestResult guest D G T L sim staging
        cost := fun _ _ => budget })
    (he : evalArgs w st args = some vs) (hwords : ∀ x ∈ vs, x < 2^w)
    (hready : ready vs st.mem)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (ha : st.regs 5 = staging) :
    let base := staging+queryOriginals G L+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let marks := base+2^width
    let dest := marks+G.m
    let C := dedupSelectedTreeContract w G ℓ v γ
      (base+queryOriginals G L) (base+queryBridges G L) (base+queryHeader G L)
      marks (marks+G.m) staging (staging+G.m)
    MeetsContract w p dedup C → dest+G.n < 2^w → G.n+1 < 2^w →
    ∀ (post : State → Prop) (numericBudget : ℕ),
    (∀ selected, selectedTreeAt G T (staging+queryWeights G L) dest
        (selected.regs 13) st.mem selected.mem →
      selected.regs 12 = staging+queryOriginals G L+2^width →
      (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = st.regs r) →
      ∃ out cost, Runs w p ω
        (prepareAndRunStagedNumericBody copy pack packWeights prepare adjacency numeric)
        selected .normal out cost ∧ post out ∧ cost ≤ numericBudget) →
    ∃ out cost, Runs w p ω
      (stagedRebuildRoundBody query dedup copy pack packWeights prepare adjacency numeric args)
      st .normal out cost ∧ post out ∧
      cost ≤ argsSize args+budget+
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+
        40*G.n+numericBudget+18 := by
  intro base width marks dest C hd hroom hword post numericBudget hnumeric
  obtain ⟨selected,cs,hr,hTree,hcursor,hregs,hcs⟩ :=
    stagedTreeSelection_runs (ω := ω) st guest D G T L sim staging ℓ v γ args vs ready budget
      hq he hwords hready htree ht hh hn hm hL hs ha hd hroom hword
  obtain ⟨out,cn,hrun,hpost,hcn⟩ := hnumeric selected hTree hcursor hregs
  exact ⟨out,cs+cn+1,runs_seq_iff.mpr (Or.inr ⟨selected,cs,cn,hr,hrun,rfl⟩),
    hpost,by omega⟩

/-- Run the staged rebuild and return the allocation endpoint reported
by the numeric pass. The guest arguments are the first twelve registers. -/
def stagedRebuildRoundEntry
    (select dedup copy pack packWeights prepare adjacency numeric : ℕ) : Stmt :=
  .seq (stagedRebuildRoundBody select dedup copy pack packWeights prepare adjacency numeric
      ((List.range' 0 12).map Expr.reg))
    (.ret (.reg 16))

/-- Export the numeric pass's endpoint through a callable round
interface. The postcondition can retain the stretches and next weights. -/
theorem stagedRebuildRoundEntry_meetsContract {w entry select dedup copy pack packWeights
    prepare adjacency numeric : ℕ} {p : Program}
    (he : p.procs[entry]? = some
      (stagedRebuildRoundEntry select dedup copy pack packWeights prepare adjacency numeric))
    (ready : List ℕ → (ℕ → ℕ) → Prop)
    (post : List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop)
    (budget : List ℕ → (ℕ → ℕ) → ℕ)
    (hrun : ∀ args mem pos ω, (∀ x ∈ args, x < 2^w) → ready args mem →
      ∃ out cost, Runs w p ω
        (stagedRebuildRoundBody select dedup copy pack packWeights prepare adjacency numeric
          ((List.range' 0 12).map Expr.reg))
        (startState args mem pos) .normal out cost ∧
        post args mem (out.regs 16) out.mem ∧ cost ≤ budget args mem) :
    MeetsContract w p entry
      { pre := ready, post := post, cost := fun args mem => budget args mem+3 } := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨out,cost,hr,hpost,hcost⟩ := hrun args mem pos ω hwords hpre
  have hret : Runs w p ω (.ret (.reg 16)) out (.returned (out.regs 16)) out 2 :=
    runs_ret_iff.mpr ⟨out.regs 16,rfl,rfl,rfl,rfl⟩
  exact ⟨.returned (out.regs 16),out,cost+2+1,
    runs_seq_iff.mpr (Or.inr ⟨out,cost,2,hr,hret,rfl⟩),hpost,by dsimp only; omega⟩

/-- The first compact stretch block is at the end of the first edge
workspace. Subsequent blocks use the same stride. -/
theorem stagedStretchAddr_eq (start L i : ℕ) :
    roundStretchAddr start L i =
      start+edgeStretchSpace L-L+i*edgeStretchSpace L := by
  have hWidth : L ≤ edgeStretchSpace L := by unfold edgeStretchSpace; omega
  unfold roundStretchAddr
  rw [Nat.add_mul,Nat.one_mul]
  have hBase : L ≤ start+edgeStretchSpace L := hWidth.trans (Nat.le_add_left _ _)
  omega

/-- The first updated weight block and the weight stride describe the
same addresses as the numeric pass's indexed output. -/
theorem stagedWeightAddr_eq (start L i : ℕ) :
    roundWeightAddr start L i =
      start+narrowWeightSpace L-L+i*narrowWeightSpace L := by
  have hWidth : L ≤ narrowWeightSpace L := by
    unfold narrowWeightSpace widenWeightSpace
    omega
  unfold roundWeightAddr
  rw [Nat.add_mul,Nat.one_mul]
  have hBase : L ≤ start+narrowWeightSpace L := hWidth.trans (Nat.le_add_left _ _)
  omega

/-- Read the numeric postcondition as two strided arrays. The stretch
publisher consumes the first, and the next rebuild round consumes the second. -/
theorem stagedNumericOutput_arrays {w h Q : ℕ} (G T H : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (args : List ℕ) (mem out : ℕ → ℕ) (ret : ℕ) :
    let C := stretchWeightRoundContract w h Q G T H 0 len adj parents edges depths queue
      n levels dist lengths L heap tails heads P old stride denom j scale query
    let start := heap+(n-1)*L
    let afterStretch := start+G.m*edgeStretchSpace L
    let stretch := start+edgeStretchSpace L-L
    let weight := afterStretch+narrowWeightSpace L-L
    C.post args mem ret out →
    ret = afterStretch+H.m*narrowWeightSpace L ∧ ZeroFrom out ret ∧
    (∀ i < H.m, Num.Valid out (stretch+i*edgeStretchSpace L) h L ∧
      Num.fixVal out (stretch+i*edgeStretchSpace L) h L P =
        query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
    ∀ i < H.m, Num.Valid out (weight+i*narrowWeightSpace L) h L ∧
      Num.fixVal out (weight+i*narrowWeightSpace L) h L P =
        weights P (scale : ℝ) query (j+1) (edgeName H i) := by
  intro C start afterStretch stretch weight hpost
  obtain ⟨hret,hzero,_,hblocks,_⟩ := hpost
  exact ⟨hret,hzero,fun i hi => stagedStretchAddr_eq start L i ▸ (hblocks i hi).2,
    fun i hi => stagedWeightAddr_eq afterStretch L i ▸ (hblocks i hi).1⟩

/-- The last next-round weight block ends at the numeric allocation
boundary. The cursor descriptor may be written at that boundary or later. -/
theorem stagedNumericOutput_lastWeightEnd (start m L : ℕ) (hm : 0 < m) :
    start+narrowWeightSpace L-L+(m-1)*narrowWeightSpace L+L =
      start+m*narrowWeightSpace L := by
  have hL : L ≤ narrowWeightSpace L := by
    unfold narrowWeightSpace widenWeightSpace
    omega
  have hmul : m*narrowWeightSpace L = (m-1)*narrowWeightSpace L+narrowWeightSpace L := by
    conv_lhs => rw [show m = m-1+1 by omega]
    rw [Nat.add_mul,Nat.one_mul]
  omega

/-- Every compact output block ends within the corresponding
allocation, so allocations made at the returned cursor preserve it. -/
theorem stagedNumericOutput_blockEnds (start m L i : ℕ) (hi : i < m) :
    let afterStretch := start+m*edgeStretchSpace L
    roundStretchAddr start L i + L ≤ afterStretch ∧
    roundWeightAddr afterStretch L i + L ≤ afterStretch+m*narrowWeightSpace L := by
  intro afterStretch
  have hs : L ≤ edgeStretchSpace L := by unfold edgeStretchSpace; omega
  have hw : L ≤ narrowWeightSpace L := by unfold narrowWeightSpace widenWeightSpace; omega
  rw [stagedStretchAddr_eq,stagedWeightAddr_eq]
  have hsm := Nat.mul_le_mul_right (edgeStretchSpace L) (Nat.succ_le_of_lt hi)
  have hwm := Nat.mul_le_mul_right (narrowWeightSpace L) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hsm hwm
  dsimp only [afterStretch]
  omega

end MinCostFlow.LastLevelProgram
