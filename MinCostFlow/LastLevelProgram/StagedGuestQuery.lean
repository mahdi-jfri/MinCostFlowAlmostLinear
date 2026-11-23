module

public import MinCostFlow.LastLevelProgram.StagedGuestSelection
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Calling the staged guest and building traversal tables

The Definition 5.8 rebuild (pages 19–20) calls the guest, deduplicates the selected tree, and builds its traversal tables.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord LSF

/-- The query returns its last reserved cell and publishes the tree
in the translated tables, preserving the staged input prefix. -/
def stagedGuestResult (guest : Program) (D : ℕ) (G T : MGraph) (L sim staging : ℕ)
    (mem : ℕ → ℕ) (cursor : ℕ) (out : ℕ → ℕ) : Prop :=
  let heap := staging+queryOriginals G L
  let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
  let base := heap+1
  cursor = heap+2^width ∧ out (base+queryHeader G L) ≤ G.n ∧
    out (base+queryHeader G L+1) ≤ G.n ∧
    treeFromOutput G out (base+queryOriginals G L) (base+queryBridges G L)
      (base+queryHeader G L) = T ∧
    (∀ a < staging+queryWeights G L, out a = mem a) ∧ ZeroFrom out (base+2^width)


/-- The staged query takes the graph counts, guest format, staging
pointer, and the strided weight source. Unused slots are zero. -/
def stagedGuestArgs (G : MGraph) (L sim staging src stride P Q : ℕ) : List ℕ :=
  [G.n,G.m,L,sim,0,staging,0,0,src,stride,P,Q]

/-- The staged inputs consist of compact endpoints and lengths, followed
by a fresh region in which the query packs the strided weights. -/
def stagedGuestReady (w : ℕ) (G : MGraph) (L sim staging src stride P Q : ℕ)
    (len wt : ℕ → ℤ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  args = stagedGuestArgs G L sim staging src stride P Q ∧
    (packGuestWeightsContract w P Q).pre [src,stride,L,G.m,Q-P,staging+queryWeights G L] mem ∧
    (∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i) ∧
    (∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i) ∧
    (∀ i < G.m, ListAt mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) ∧
    ∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal mem (src+i*stride) 1 L P)

/-- Count width selection, the weight copy, argument evaluation, and
relocation of the canonical guest run. -/
def stagedGuestQueryCost (w : ℕ) (guest : Program) (D : ℕ) (G : MGraph)
    (L sim guestCost : ℕ) : ℕ :=
  let R := (Program.mk (lsstModule guest 0 1)).regBound
  let treeArgs := stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3)
    (.reg 4) (.reg 5) (.reg 6)
  argsSize stagedWeightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
    17*(queryOriginals G L+1)+(R+6)*guestCost+6+stagedGuestCursorExpr.size +
    (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] (fun _ => 0) +
    argsSize paddedWidthArgs + 3

/-- Install the staged call using the actual run of the canonical
Theorem 2.2 guest and the allocated host region. -/
theorem selectAndQueryPaddedTree_meetsContract {w entry pack query select P Q : ℕ} {p : Program}
    (G : MGraph) (guest : Program) (c₀ D : ℕ) (K : ℝ) (hK : max K 0 ≤ (D : ℝ))
    (len wt : ℕ → ℤ) (src stride L staging guestCost : ℕ) (guestOut : State)
    (hentry : p.procs[entry]? = some (selectAndQueryPaddedTreeBody guest select pack query))
    (hselect : MeetsContract w p select (selectPaddedGuestWidthContract w guest D))
    (hc : 1 ≤ c₀) (hG : (indexedGraph G).Valid)
    (hinstalled : p.HasAt query (relocatedTreeProcedures guest query))
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q))
    (hn : 0 < G.n) (hm : 0 < G.m) (hD : 0 < D) (hL : 0 < L) :
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let minimum := max 5 (Nat.log 2 (queryHeap G L + lsstSpace guest K G.n G.m sim 1) + 1)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    Runs minimum ⟨lsstModule guest 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2^minimum, moved (base+a) = guestOut.mem a) →
      treeFromOutput G moved (base+queryOriginals G L)
        (base+queryBridges G L) (base+queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L+1) ≤ G.n →
    staging+queryOriginals G L+1+2^width ≤ 2^w →
    MeetsContract w p entry
      { pre := stagedGuestReady w G L sim staging src stride P Q len wt
        post := fun _ => stagedGuestResult guest D G tree L sim staging
        cost := fun _ _ => stagedGuestQueryCost w guest D G L sim guestCost } := by
  intro sim width minimum callArgs tree hrun hdecode hcount hbridges hspace
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hpack,htail,hhead,hlen,hwt⟩ := hpre
  have hd : Q < 2^w := hwords Q (by simp [stagedGuestArgs])
  have hdest : staging+queryWeights G L < 2^w := by
    exact (Nat.add_le_add_left (Nat.le_add_right (queryWeights G L) (G.m*L)) staging).trans_lt
      ((Nat.lt_succ_self _).trans_le ((Nat.le_add_right _ _).trans hspace))
  have hwa : ∀ x ∈ [src,stride,L,G.m,Q-P,staging+queryWeights G L], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwords _ (by simp [stagedGuestArgs])
    · exact hwords _ (by simp [stagedGuestArgs])
    · exact hwords _ (by simp [stagedGuestArgs])
    · exact hwords _ (by simp [stagedGuestArgs])
    · omega
    · exact hdest
  exact selectAndQueryPaddedTree_runs
    (startState (stagedGuestArgs G L sim staging src stride P Q) mem pos)
    guest c₀ D K hK len wt src stride L staging guestCost guestOut hselect hc hG hinstalled hp
    hrun hdecode hcount hbridges hwa hpack rfl rfl rfl rfl rfl hn hm hD
    rfl rfl rfl rfl hspace hL htail hhead hlen hwt

/-- The cursor stays in register twelve for the deduplication call. -/
def stagedTreeSelectionBody (query dedup : ℕ) (args : List Expr) : Stmt :=
  .seq (.call 12 query args) (dedupStagedTreeBody dedup)

/-- A staged guest query and the verified deduplication call together
produce the retained tree representation consumed by traversal. -/
theorem stagedTreeSelection_runs {w query dedup : ℕ} {p : Program} {ω : ℕ → Bool}
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
      marks dest staging (staging+G.m)
    MeetsContract w p dedup C → dest+G.n < 2^w → G.n+1 < 2^w →
    ∃ out cost, Runs w p ω (stagedTreeSelectionBody query dedup args) st .normal out cost ∧
      selectedTreeAt G T (staging+queryWeights G L) dest (out.regs 13) st.mem out.mem ∧
      out.regs 12 = staging+queryOriginals G L+2^width ∧
      (∀ r, r ≠ 12 → r ≠ 13 → out.regs r = st.regs r) ∧
      cost ≤ argsSize args + budget +
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
        40*G.n+17 := by
  intro base width marks dest C hd hroom hword
  suffices h : ∃ o out cost, Runs w p ω (stagedTreeSelectionBody query dedup args) st o out cost ∧
      (o = .normal ∧ selectedTreeAt G T (staging+queryWeights G L) dest (out.regs 13) st.mem out.mem ∧
        out.regs 12 = staging+queryOriginals G L+2^width ∧
        (∀ r, r ≠ 12 → r ≠ 13 → out.regs r = st.regs r)) ∧
      cost ≤ argsSize args + budget +
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
        40*G.n+17 by
    obtain ⟨o,out,cost,hr,⟨rfl,hpost⟩,hc⟩ := h
    exact ⟨out,cost,hr,hpost.1,hpost.2.1,hpost.2.2,hc⟩
  apply runs_start_le
  unfold stagedTreeSelectionBody
  refine runs_seq_call_le hq he hwords hready ?_
  intro cursor mid pos hpost
  obtain ⟨hcursor,hcount,_,hdecoded,hframe,hzero⟩ := hpost
  let next := State.mk mid (Function.update st.regs 12 cursor) pos
  obtain ⟨out,cost,kept,hr,hret,hlen,hnd,hlist,heq,hf,hz,hregs,hc⟩ :=
    dedupStagedTree_runs (ω := ω) next guest D G T L sim staging ℓ v γ st.mem
      htree ht hh hframe hd
      (by simp [next,Function.update,hn]) (by simp [next,Function.update,hm])
      (by simp [next,Function.update,hL]) (by simp [next,Function.update,hs])
      (by simp [next,Function.update,ha]) (by simpa [next,width] using hcursor)
      hdecoded hcount hzero hroom hword
  refine ⟨.normal,out,cost,hr,⟨rfl,⟨kept,hret,hlen,hnd,hlist,heq,hf,hz⟩,?_,?_⟩,by dsimp only; omega⟩
  · exact (hregs 12 (by decide)).trans (by simpa [next,width] using hcursor)
  · intro r hr₁ hr₂
    exact (hregs r hr₂).trans (by simp [next,Function.update,hr₁])

/-- The selection entry forwards the twelve staged query words unchanged. -/
def stagedTreeSelectionEntry (query dedup : ℕ) : Stmt :=
  .seq (stagedTreeSelectionBody query dedup ((List.range' 0 12).map Expr.reg)) (.ret (.reg 13))

/-- Install selection as a procedure. It forwards the prepared query and
exposes the retained tree layout and its allocation frame to traversal. -/
theorem stagedTreeSelection_meetsContract {w entry query dedup : ℕ} {p : Program}
    (guest : Program) (D : ℕ) (G T : MGraph)
    (L sim staging src stride P Q budget : ℕ) (len wt : ℕ → ℤ)
    (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[entry]? = some (stagedTreeSelectionEntry query dedup))
    (hq : MeetsContract w p query
      { pre := stagedGuestReady w G L sim staging src stride P Q len wt
        post := fun _ => stagedGuestResult guest D G T L sim staging
        cost := fun _ _ => budget })
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T) :
    let base := staging+queryOriginals G L+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let marks := base+2^width
    let dest := marks+G.m
    let C := dedupSelectedTreeContract w G ℓ v γ
      (base+queryOriginals G L) (base+queryBridges G L) (base+queryHeader G L)
      marks dest staging (staging+G.m)
    MeetsContract w p dedup C → dest+G.n < 2^w → G.n+1 < 2^w →
    MeetsContract w p entry
      { pre := stagedGuestReady w G L sim staging src stride P Q len wt
        post := fun _ mem count out => selectedTreeAt G T (staging+queryWeights G L) dest count mem out
        cost := fun _ _ => 12 + budget +
          argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
          40*G.n+20 } := by
  intro base width marks dest C hd hroom hword
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hready
  have hreadyCopy := hready
  obtain ⟨rfl,_,ht,hh,_,_⟩ := hreadyCopy
  let vs := stagedGuestArgs G L sim staging src stride P Q
  let st := startState vs mem pos
  have hargs : evalArgs w st ((List.range' 0 12).map Expr.reg) = some vs :=
    evalArgs_registerRange st 0 vs (by intro i _; simp [st,startState])
  obtain ⟨out,cost,hr,hpost,_,_,hc⟩ :=
    stagedTreeSelection_runs (ω := ω) st guest D G T L sim staging ℓ v γ _ vs _ budget
      hq hargs hwords hready htree ht hh rfl rfl rfl rfl rfl hd hroom hword
  have hret : Runs w p ω (.ret (.reg 13)) out (.returned (out.regs 13)) out 2 :=
    runs_ret_iff.mpr ⟨out.regs 13,rfl,rfl,rfl,rfl⟩
  refine ⟨.returned (out.regs 13),out,cost+2+1,
    runs_seq_iff.mpr (Or.inr ⟨out,cost,2,hr,hret,rfl⟩),hpost,?_⟩
  have hsize : argsSize ((List.range' 0 12).map Expr.reg) = 12 := by decide
  rw [hsize] at hc
  dsimp only
  omega

/-- Reserve one parent row per binary level, three traversal arrays, and
the separating word required by the traversal contract. -/
def stagedTraversalReserve (n levels : ℕ) : ℕ :=
  (levels+4)*n+1

/-- Compute the traversal reservation from the runtime vertex and level counts. -/
def stagedTraversalReserveExpr (n levels : Expr) : Expr :=
  .bin .add (.bin .mul (.bin .add levels (.const 4)) n) (.const 1)

/-- The reservation expression fits whenever its size fits and at least
one vertex is present. -/
theorem stagedTraversalReserveExpr_eval {w : ℕ} {st : State} {ne ke : Expr}
    (n levels : ℕ) (hn : ne.eval w st = some n) (hk : ke.eval w st = some levels)
    (hnPos : 0 < n) (hfit : stagedTraversalReserve n levels < 2^w) :
    (stagedTraversalReserveExpr ne ke).eval w st = some (stagedTraversalReserve n levels) := by
  have hprod : (levels+4)*n < 2^w := by unfold stagedTraversalReserve at hfit; omega
  have hlevels : levels+4 < 2^w := (Nat.le_mul_of_pos_right _ hnPos).trans_lt hprod
  have hfour : 4 < 2^w := by omega
  have hone : 1 < 2^w := by omega
  simp only [stagedTraversalReserveExpr,Expr.eval,BinOp.eval,hn,hk,hfour,hlevels,hprod,hone,
    stagedTraversalReserve,ite_eq_left]
  simp [stagedTraversalReserve] at hfit
  simp [hfit]

/-- The parent rows, edges, depths, and queue fit in the reservation in
the order required by the tree traversal and ancestor table procedures. -/
theorem stagedTraversalReserve_layout (start n levels : ℕ) :
    let edges := start+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let floor := start+stagedTraversalReserve n levels
    start+(levels+1)*n ≤ edges ∧ edges+n ≤ depths ∧ depths+n ≤ queue ∧
      queue+n < floor := by
  dsimp [stagedTraversalReserve]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- The adjacency call uses the retained edges, staged endpoints, and
fresh head and incidence record arrays. -/
def stagedAdjacencyArgs (n m staging cursor reserve count : Expr) : List Expr :=
  let dest := Expr.bin .add (Expr.bin .add cursor (.const 1)) m
  let adj := Expr.bin .add (Expr.bin .add dest n) reserve
  [dest,staging,.bin .add staging m,adj,.bin .add adj n,count]

/-- The allocation layout determines the exact arguments of the adjacency
pass. The caller retains the guest cursor and the deduplicated count. -/
theorem stagedAdjacencyArgs_eval {w : ℕ} {st : State} {ne me ae ce re ke : Expr}
    (n m staging cursor reserve count : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (ha : ae.eval w st = some staging) (hc : ce.eval w st = some cursor)
    (hr : re.eval w st = some reserve) (hk : ke.eval w st = some count)
    (hstage : staging+m < 2^w) (hroom : cursor+1+m+n+reserve+n < 2^w) :
    let dest := cursor+1+m
    let adj := dest+n+reserve
    evalArgs w st (stagedAdjacencyArgs ne me ae ce re ke) =
      some [dest,staging,staging+m,adj,adj+n,count] := by
  intro dest adj
  have hone : 1 < 2^w := by omega
  have hmarks : cursor+1 < 2^w := by omega
  have hdest : cursor+1+m < 2^w := by omega
  have hretained : cursor+1+m+n < 2^w := by omega
  have hadj : cursor+1+m+n+reserve < 2^w := by omega
  simp only [stagedAdjacencyArgs,evalArgs,Expr.eval,BinOp.eval,hn,hm,ha,hc,hr,hk,
    hone,hmarks,hdest,hretained,hadj,hstage,hroom,ite_eq_left,adj,dest]

/-- Build the incidence lists from the retained tree. The returned state
keeps the runtime graph and layout registers available to the stretch pass. -/
theorem stagedAdjacency_runs {w entry insert result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (L staging cursor levels count : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[entry]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hlevels : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n) :
    let reserve := stagedTraversalReserve G.n levels
    let dest := cursor+1+G.m
    let adj := dest+G.n+reserve
    let records := adj+G.n
    let args := stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest → records+6*G.n < 2^w →
    ∃ out cost kept, Runs w p ω (.call result entry args) st .normal out cost ∧
      count = kept.length ∧ kept.Nodup ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
      (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
        adj records).post [dest,staging,staging+G.m,adj,records,count] st.mem 0 out.mem ∧
      (∀ a < adj, out.mem a = st.mem a) ∧
      (∀ a ≥ records+6*G.n, out.mem a = st.mem a) ∧
      out.regs = Function.update st.regs result 0 ∧
      cost ≤ argsSize args+112*count+11 := by
  intro reserve dest adj records args hTree hsep hroom
  obtain ⟨kept,hlen,hnd,htreeEq,hpre⟩ :=
    adjacency_pre_of_stagedTree G T L staging dest reserve count mem st.mem ht hh hTree hsep hroom
  have hcount : count ≤ G.n := by
    obtain ⟨xs,he,hs,_⟩ := hTree
    exact he ▸ hs
  have hprefix : G.m ≤ queryWeights G L := by
    unfold queryWeights queryLengths
    omega
  have hd : dest < 2^w := by dsimp [records,adj] at hroom; omega
  have hstage : staging+G.m < 2^w :=
    (Nat.add_le_add_left hprefix staging).trans_lt (hsep.trans_lt hd)
  have hrec : records < 2^w := by omega
  have hadj : adj < 2^w := (Nat.le_add_right _ _).trans_lt hrec
  have hcnt : count < 2^w := hcount.trans_lt (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans_lt hadj)
  have hreserve : reserve < 2^w := by
    exact (Nat.le_add_left _ _).trans_lt hadj
  have heReserve : (stagedTraversalReserveExpr (.reg 0) (.reg 14)).eval w st = some reserve :=
    stagedTraversalReserveExpr_eval (ne := .reg 0) (ke := .reg 14)
      G.n levels (congrArg some hn) (congrArg some hlevels) hnPos hreserve
  have hargs : evalArgs w st args = some [dest,staging,staging+G.m,adj,records,count] :=
    stagedAdjacencyArgs_eval (ne := .reg 0) (me := .reg 1) (ae := .reg 5)
      (ce := .reg 12) (re := stagedTraversalReserveExpr (.reg 0) (.reg 14)) (ke := .reg 13) G.n G.m staging cursor reserve count
      (congrArg some hn) (congrArg some hm) (congrArg some ha)
      (congrArg some hc) heReserve (congrArg some hk) hstage hrec
  have hadjC := selectedAdjacency_meetsContract kept dest staging (staging+G.m)
    adj records he hi hw hv hconn (htreeEq ▸ htree)
  obtain ⟨out,cost,ret,hr,hpost,hret,hother,hcost⟩ := runs_call_of_meetsContract
    (r := result) hadjC hargs (by wram_words) hpre ω
  have hret0 : ret = 0 := hpost.1
  rw [hret0] at hpost
  have hindex : ∀ e ∈ kept, e < G.m := by
    have ht : IsLSST (indexedGraph G).toMGraph ℓ v γ
        (decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept []) :=
      htreeEq ▸ htree
    exact (connectedDecodedTree_originals hv hconn ht).2
  have hf := selectedAdjacency_frame kept dest staging (staging+G.m) adj records
    hv hindex le_rfl hpost
  refine ⟨out,cost,kept,hr,hlen,hnd,htreeEq,hpost,
    fun a ha => hf a (Or.inl ha),?_,?_,?_⟩
  · intro a ha
    have hcount := hlen ▸ hcount
    have hbound : records+6*kept.length ≤ a :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hcount) records).trans ha
    exact hf a (Or.inr hbound)
  · funext r
    by_cases h : r = result
    · subst r
      simpa using hret.trans hret0
    · simpa [Function.update,h] using hother r h
  · change cost ≤ argsSize args + 112*kept.length + 10 + 1 at hcost
    rw [← hlen] at hcost
    omega

/-- The staged adjacency lists and the fresh traversal reservation
satisfy the queue traversal's precondition at compact root zero. -/
theorem traversal_pre_of_stagedAdjacency {w : ℕ} (G T : MGraph)
    (staging dest levels : ℕ) (kept : List ℕ) (mem out : ℕ → ℕ)
    (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hdecode : decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T)
    (hnd : kept.Nodup) (hsize : kept.length ≤ G.n)
    (hw : 2 < 2^w) :
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
      adj records).post [dest,staging,staging+G.m,adj,records,kept.length] mem 0 out →
    (∀ a, dest+G.n ≤ a → a < records → mem a = 0) → records+6*G.n < 2^w →
    (traverseTreeQueueContract w T 0).pre [adj,parents,edges,depths,queue,0] out := by
  intro parents edges depths queue adj records hpost hz hroom
  have hroot := indexedLSST_rooted_zero hv htree
  have hindex := (connectedDecodedTree_originals hv hconn (hdecode.symm ▸ htree)).2
  obtain ⟨hPE,hED,hDQ,hQF⟩ := stagedTraversalReserve_layout parents G.n levels
  have hPE' : parents+G.n ≤ edges :=
    Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) parents
  have hroom' : records+6*kept.length < 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsize) records).trans_lt hroom
  have hd : mem (depths+0) = 0 := by
    apply hz
    · dsimp [depths,edges,parents]
      omega
    · dsimp [records,queue] at hQF ⊢
      omega
  have ha : ∀ x < G.n, mem (adj+x) = 0 := by
    intro x hx
    exact hz _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) (by
      dsimp [records]; omega)
  exact traverseTreeQueue_pre_of_selected kept dest staging (staging+G.m) adj records
    parents edges depths queue adj hnd hroot.isForest hindex hdecode hpost hw
    hPE' hED hDQ hQF le_rfl le_rfl hroom' hd ha

/-- The traversal receives the adjacency heads and the reserved
parent, edge, depth, and queue arrays. -/
def stagedTraversalArgs (n m levels cursor : Expr) : List Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let dest := add (add cursor (.const 1)) m
  let parents := add dest n
  let edges := add parents (mul (add levels (.const 1)) n)
  let depths := add edges n
  let queue := add depths n
  let adj := add parents (stagedTraversalReserveExpr n levels)
  [adj,parents,edges,depths,queue,.const 0]

/-- Runtime traversal arguments coincide with the reserved layout used
by the staged adjacency pass and the binary lifting tables. -/
theorem stagedTraversalArgs_eval {w : ℕ} {st : State} {ne me le ce : Expr}
    (n m levels cursor : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hl : le.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hnPos : 0 < n) (hfit : cursor+1+m+n+stagedTraversalReserve n levels < 2^w) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    evalArgs w st (stagedTraversalArgs ne me le ce) =
      some [adj,parents,edges,depths,queue,0] := by
  intro parents edges depths queue adj
  obtain ⟨_,_,_,hq⟩ := stagedTraversalReserve_layout parents n levels
  have hqFit : queue+n < 2^w := hq.trans hfit
  have hrow : (levels+1)*n < 2^w := by dsimp [queue,depths,edges] at hqFit; omega
  have hlevel : levels+1 < 2^w := (Nat.le_mul_of_pos_right _ hnPos).trans_lt hrow
  have hres : stagedTraversalReserve n levels < 2^w := by
    exact (Nat.le_add_left _ _).trans_lt hfit
  have hReserve := stagedTraversalReserveExpr_eval n levels hn hl hnPos hres
  have h0 := Nat.two_pow_pos w
  have h1 : 1 < 2^w := by omega
  have hmark : cursor+1 < 2^w := by omega
  have hdest : cursor+1+m < 2^w := by omega
  have hp : parents < 2^w := by dsimp [parents]; omega
  have he : edges < 2^w := by dsimp [queue,depths] at hqFit; omega
  have hd : depths < 2^w := by dsimp [queue] at hqFit; omega
  have hq' : queue < 2^w := by omega
  simp only [stagedTraversalArgs,evalArgs,Expr.eval,BinOp.eval,hn,hm,hl,hc,hReserve,
    h0,h1,hmark,hdest,ite_eq_left]
  simp only [parents,edges,depths,queue,adj] at hp he hd hq' ⊢
  simp only [hp,he,hd,hq',hlevel,hrow,hfit,ite_eq_left]

/-- Run the queue traversal from compact root zero. Its postcondition
provides the parent, edge, depth, and discovery order tables. -/
theorem stagedTraversal_runs {w entry result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (T : MGraph) (n m levels cursor : ℕ)
    (he : p.procs[entry]? = some traverseTreeQueueBody) (hroot : IsRootedTree T 0)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hl : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hnPos : 0 < n) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    let words := [adj,parents,edges,depths,queue,0]
    let args := stagedTraversalArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12)
    adj < 2^w →
    (traverseTreeQueueContract w T 0).pre words st.mem →
    ∃ out cost, Runs w p ω (.call result entry args) st .normal out cost ∧
      (traverseTreeQueueContract w T 0).post words st.mem (out.regs result) out.mem ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧
      cost ≤ argsSize args+114*T.E.card+35*T.V.card+24 := by
  intro parents edges depths queue adj words args hfit hpre
  have hargs : evalArgs w st args = some words :=
    stagedTraversalArgs_eval (ne := .reg 0) (me := .reg 1) (le := .reg 14) (ce := .reg 12)
      n m levels cursor (congrArg some hn) (congrArg some hm)
      (congrArg some hl) (congrArg some hc) hnPos hfit
  have hq : queue < 2^w := by
    obtain ⟨_,_,_,h⟩ := stagedTraversalReserve_layout parents n levels
    exact (Nat.le_add_right _ _).trans_lt (h.trans hfit)
  have hd : depths < 2^w := (Nat.le_add_right _ _).trans_lt hq
  have he' : edges < 2^w := (Nat.le_add_right _ _).trans_lt hd
  have hp : parents < 2^w := (Nat.le_add_right _ _).trans_lt he'
  have hwords : ∀ a ∈ words, a < 2^w := by
    intro a ha
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfit
    · exact hp
    · exact he'
    · exact hd
    · exact hq
    · exact Nat.two_pow_pos _
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ := runs_call_of_meetsContract
    (r := result) (traverseTreeQueue_meetsContract hroot he) hargs hwords hpre ω
  refine ⟨out,cost,hr,hret.symm ▸ hpost,hregs,?_⟩
  change cost ≤ argsSize args + (114*T.E.card+35*T.V.card+23) + 1 at hcost
  omega

end MinCostFlow.LastLevelProgram
