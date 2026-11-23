module

public import MinCostFlow.LastLevelProgram.StagedGuestQuery
public import MinCostFlow.LastLevelProgram.PackGuestLengths
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import WordRAM.Link

/-!
# Guest weights from the staged host round

The low-stretch tree call of Definition 5.8 (pages 19–20) reads
one-bit limbs. Convert the host's strided four-bit weight blocks directly
into the low-stretch tree input region at the selected guest precision.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num WideWord

/-- The weight converter takes both limb counts, both precisions,
and the source stride from runtime registers. -/
def stagedGuestWeightsArgs : List Expr :=
  let offsets := canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)
  [.reg 8,.bin .add (.reg 5) (offsets.getD 5 (.const 0)),.reg 9,.reg 19,
    .reg 10,.reg 11,.reg 2,.reg 1]

/-- The converter's destination is the guest weight region, immediately
after the staged length blocks. -/
theorem stagedGuestWeightsArgs_eval {w : ℕ} {st : State} (G : MGraph)
    (L sim staging src stride hostL P Q : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (ha : st.regs 5 = staging)
    (hsrc : st.regs 8 = src) (hstride : st.regs 9 = stride) (hhost : st.regs 19 = hostL)
    (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hheap : queryHeap G L < 2^w) (hdest : staging+queryWeights G L < 2^w) :
    evalArgs w st stagedGuestWeightsArgs =
      some [src,staging+queryWeights G L,stride,hostL,P,Q,L,G.m] := by
  have hargs := canonicalGuestArgsExpr_eval (st := st) G L sim
    (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
    (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hheap
  have hweight :
      (((canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5
        (.const 0))).eval w st = some (queryWeights G L) := evalArgs_getD hargs 5
  simp only [stagedGuestWeightsArgs,evalArgs,Expr.eval,BinOp.eval,hm,hL,ha,hsrc,hstride,
    hhost,hP,hQ,hweight,hdest,ite_eq_left]

/-- Populate the query's weight region from the current host round,
leaving the endpoints and lengths in place. -/
theorem stagedGuestWeights_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (L sim staging src stride hostL P Q : ℕ)
    (hc : MeetsContract w p entry (packGuestStridedContract w))
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (ha : st.regs 5 = staging)
    (hsrc : st.regs 8 = src) (hstride : st.regs 9 = stride) (hhost : st.regs 19 = hostL)
    (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hheap : queryHeap G L < 2^w) (hdest : staging+queryWeights G L < 2^w) :
    let dst := staging+queryWeights G L
    let args := [src,dst,stride,hostL,P,Q,L,G.m]
    (∀ a ∈ args, a < 2^w) → (packGuestStridedContract w).pre args st.mem →
    ∃ out cost, Runs w p ω (.call 6 entry stagedGuestWeightsArgs) st .normal out cost ∧
      (∀ i < G.m, ListAt out.mem (dst+i*L)
        (encodeLimbs 1 L (queryNumerator Q (fixVal st.mem (src+i*stride) 4 hostL P)))) ∧
      (∀ a, a < dst ∨ dst+G.m*L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 6 → out.regs r = st.regs r) ∧
      cost ≤ argsSize stagedGuestWeightsArgs+(80*L+37)*G.m+11 := by
  intro dst args hwords hpre
  have hargs := stagedGuestWeightsArgs_eval (w := w) (st := st)
    G L sim staging src stride hostL P Q hn hm hL hs ha hsrc hstride hhost hP hQ hheap hdest
  obtain ⟨out,cost,ret,hrun,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 6) hc hargs hwords hpre ω
  obtain ⟨a,b,d,H,P',Q',N,m,heq,_,henc,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change cost ≤ argsSize stagedGuestWeightsArgs+((80*L+37)*G.m+10)+1 at hcost
  exact ⟨out,cost,hrun,henc,hframe,hregs,by omega⟩

/-- After host conversion the endpoint, length, and weight arrays form
the canonical low-stretch input prefix. The guest workspace stays fresh. -/
theorem queryPrefix_of_convertedWeights
    {G : MGraph} {mem out : ℕ → ℕ} (len wt : ℕ → ℤ)
    (L staging src stride hostL P Q : ℕ) (hL : 0 < L)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (staging+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i))))
    (hwt : ∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (fixVal mem (src+i*stride) 4 hostL P))
    (hz : ZeroFrom mem (staging+queryOriginals G L+1))
    (henc : ∀ i < G.m, ListAt out (staging+queryWeights G L+i*L)
      (encodeLimbs 1 L (queryNumerator Q (fixVal mem (src+i*stride) 4 hostL P))))
    (hframe : ∀ a, a < staging+queryWeights G L ∨
      staging+queryWeights G L+G.m*L ≤ a → out a = mem a) :
    (∀ i < queryOriginals G L, out (staging+i) = queryMemory G L len wt i) ∧
    ZeroFrom out (staging+queryOriginals G L+1) := by
  have hlen : 2*G.m ≤ queryLengths G := le_rfl
  have hprefix : queryLengths G ≤ queryWeights G L := Nat.le_add_right _ _
  refine ⟨queryMemory_prefix_of_arrays G hL len wt out ?_ ?_ ?_ ?_,?_⟩
  · intro i hi
    exact (hframe (staging+i) (Or.inl (by omega))).trans (ht i hi)
  · intro i hi
    exact (hframe (staging+(G.m+i)) (Or.inl (by omega))).trans (hh i hi)
  · intro i hi k hk
    have hk' : k < L := by simpa using hk
    have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hb
    rw [hframe _ (Or.inl (by unfold queryWeights; omega))]
    exact hl i hi k hk
  · intro i hi
    rw [hwt i hi]
    exact henc i hi
  · intro a ha
    exact (hframe a (Or.inr (by unfold queryOriginals at ha; omega))).trans (hz a ha)

/-- The converted prefix discharges the relocated tree call's input
contract at the runtime-selected guest width. -/
theorem relocatedTreeAtWidth_pre_of_convertedPrefix
    {G : MGraph} {out : ℕ → ℕ} (guest : Program)
    (c₀ width L staging guestCost : ℕ) (len wt : ℕ → ℤ) (tree : MGraph)
    (hprefix : ∀ i < queryOriginals G L, out (staging+i) = queryMemory G L len wt i)
    (hz : ZeroFrom out (staging+queryOriginals G L+1)) :
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    (relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree).pre
      (relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)) out := by
  intro heap R sim args
  exact ⟨rfl,hprefix,Nat.le_succ _,hz⟩

/-- The guest heap starts after the packed input prefix. The converter
returns zero, so compute this address from the layout registers. -/
def stagedConvertedTreeArgs (R : ℕ) : List Expr :=
  let offsets := canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)
  stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 4) (.reg 5)
    (.bin .add (.reg 5) (offsets.getD 8 (.const 0)))

/-- The tree call uses the converted layout and leaves the staging
prefix intact. Its output is the width-independent canonical tree. -/
theorem stagedConvertedTree_runs {w entry width c₀ : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (guest : Program)
    (G tree : MGraph) (L staging guestCost : ℕ) (len wt : ℕ → ℤ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = lsstLSimMin c₀ G.n G.m L 1)
    (hw : st.regs 4 = width) (ha : st.regs 5 = staging)
    (hguest : queryHeap G L < 2^w) :
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let actual := relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)
    heap+1+2^width ≤ 2^w → (∀ a ∈ actual, a < 2^w) →
    (∀ i < queryOriginals G L, st.mem (staging+i) = queryMemory G L len wt i) →
    ZeroFrom st.mem (heap+1) →
    MeetsContract w p entry
      (relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree) →
    ∃ out cost, Runs w p ω (.call 7 entry (stagedConvertedTreeArgs R)) st .normal out cost ∧
      treeFromOutput G out.mem (heap+1+queryOriginals G L)
        (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
      out.mem (heap+1+queryHeader G L) ≤ G.n ∧ out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
      (∀ a < heap+1, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap+1+2^width) ∧
      (∀ r, r ≠ 7 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedConvertedTreeArgs R)+17*(queryOriginals G L+1)+(R+6)*guestCost+2 := by
  intro heap R sim args actual hspace hwords hprefix hz hcall
  have hcanon := canonicalGuestArgsExpr_eval (w := w) (st := st) G L sim
    (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
    (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hguest
  have ho : (((canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 8
      (.const 0))).eval w st = some (queryOriginals G L) := evalArgs_getD hcanon 8
  have hheap : heap < 2^w := (Nat.lt_succ_self heap).trans_le ((Nat.le_add_right _ _).trans hspace)
  have he : evalArgs w st (stagedConvertedTreeArgs R) = some actual := by
    apply stagedTreeArgsExpr_eval R G L sim width staging heap
      (ne := .reg 0) (me := .reg 1) (le := .reg 2) (se := .reg 3)
      (we := .reg 4) (ae := .reg 5)
      (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs)
      (congrArg some hw) (congrArg some ha) _ hguest hspace
    simp only [Expr.eval,BinOp.eval,ha,ho,show staging+queryOriginals G L = heap from rfl,
      hheap,ite_eq_left]
  obtain ⟨out,cost,ret,hrun,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 7) hcall he hwords
      (relocatedTreeAtWidth_pre_of_convertedPrefix guest c₀ width L staging guestCost len wt tree
        hprefix hz) ω
  obtain ⟨_,ht,hcount,hbridges,hframe,hzero⟩ := hpost
  change cost ≤ argsSize (stagedConvertedTreeArgs R)+
    (17*(queryOriginals G L+1)+(R+6)*guestCost+1)+1 at hcost
  exact ⟨out,cost,hrun,ht,hcount,hbridges,hframe,hzero,hregs,by omega⟩

/-- Convert the host weights and then invoke the relocated tree procedure. -/
def stagedConvertAndTreeBody (R convert tree : ℕ) : Stmt :=
  .seq (.call 6 convert stagedGuestWeightsArgs) (.call 7 tree (stagedConvertedTreeArgs R))

/-- The composed step preserves all inputs below the guest weight table
and returns the tree in the relocated output region. -/
theorem stagedConvertAndTree_runs {w convert entry width c₀ : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (guest : Program) (G tree : MGraph)
    (L staging guestCost src stride hostL P Q : ℕ) (len wt : ℕ → ℤ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = lsstLSimMin c₀ G.n G.m L 1) (hw : st.regs 4 = width)
    (ha : st.regs 5 = staging) (hsrc : st.regs 8 = src) (hst : st.regs 9 = stride)
    (hhL : st.regs 19 = hostL) (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hguest : queryHeap G L < 2^w) (hLpos : 0 < L) :
    let heap := staging+queryOriginals G L
    let dst := staging+queryWeights G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let actual := relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)
    let packed := [src,dst,stride,hostL,P,Q,L,G.m]
    heap+1+2^width ≤ 2^w → (∀ a ∈ actual, a < 2^w) →
    (∀ a ∈ packed, a < 2^w) → (packGuestStridedContract w).pre packed st.mem →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) = queryNumerator Q (fixVal st.mem (src+i*stride) 4 hostL P)) →
    ZeroFrom st.mem (heap+1) →
    MeetsContract w p convert (packGuestStridedContract w) →
    MeetsContract w p entry
      (relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree) →
    ∃ out cost, Runs w p ω (stagedConvertAndTreeBody R convert entry) st .normal out cost ∧
      treeFromOutput G out.mem (heap+1+queryOriginals G L)
        (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
      out.mem (heap+1+queryHeader G L) ≤ G.n ∧ out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
      (∀ a < dst, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap+1+2^width) ∧
      (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) ∧
      cost ≤ argsSize stagedGuestWeightsArgs + (80*L+37)*G.m +
        argsSize (stagedConvertedTreeArgs R)+17*(queryOriginals G L+1)+(R+6)*guestCost+14 := by
  intro heap dst R sim args actual packed hspace hwords hpw hpre ht hh hlen hwt hz hc hcall
  have hdst : dst < 2^w := hpw dst (by simp [packed])
  obtain ⟨mid,cc,hrc,henc,hframe,hregs,hcc⟩ :=
    stagedGuestWeights_runs (ω := ω) st G L sim staging src stride hostL P Q hc
      hn hm hL hs ha hsrc hst hhL hP hQ hguest hdst hpw hpre
  obtain ⟨hprefix,hfresh⟩ :=
    queryPrefix_of_convertedWeights len wt L staging src stride hostL P Q hLpos
      ht hh hlen hwt hz henc hframe
  obtain ⟨out,ct,hrt,htree,hcnt,hbridge,hkeep,hzero,hregs',hct⟩ :=
    stagedConvertedTree_runs (ω := ω) mid guest G tree L staging guestCost len wt
      ((hregs _ (by decide)).trans hn) ((hregs _ (by decide)).trans hm)
      ((hregs _ (by decide)).trans hL) ((hregs _ (by decide)).trans hs)
      ((hregs _ (by decide)).trans hw) ((hregs _ (by decide)).trans ha)
      hguest hspace hwords hprefix hfresh hcall
  have hle : dst ≤ heap+1 := by
    unfold heap dst queryOriginals
    omega
  exact ⟨out,cc+ct+1,runs_seq_iff.mpr (Or.inr ⟨mid,cc,ct,hrc,hrt,rfl⟩),htree,hcnt,hbridge,
    fun a ha' => (hkeep a (ha'.trans_le hle)).trans (hframe a (Or.inl ha')),hzero,
    fun r h6 h7 => (hregs' r h7).trans (hregs r h6),by dsimp only [R] at *; omega⟩

/-- Return the last reserved guest address after a converted tree call. -/
def stagedConvertedGuestCursor : Expr :=
  let offsets := canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)
  .bin .add (.bin .add (.reg 5) (offsets.getD 8 (.const 0)))
    (.bin .shiftLeft (.const 1) (.reg 4))

/-- The returned cursor bounds the complete relocated tree workspace. -/
theorem stagedConvertedGuestCursor_eval {w : ℕ} (st : State) (G : MGraph)
    (L sim width staging : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (hw : st.regs 4 = width) (ha : st.regs 5 = staging)
    (hguest : queryHeap G L < 2^w)
    (hspace : staging+queryOriginals G L+1+2^width ≤ 2^w) :
    stagedConvertedGuestCursor.eval w st = some (staging+queryOriginals G L+2^width) := by
  have hcanon := canonicalGuestArgsExpr_eval (w := w) (st := st) G L sim
    (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
    (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hguest
  have ho : (((canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 8
      (.const 0))).eval w st = some (queryOriginals G L) := evalArgs_getD hcanon 8
  have hmod : 2^width < 2^w := by omega
  have h1 : 1 < 2^w := (Nat.one_le_pow _ _ (by decide)).trans_lt hmod
  have hret : staging+queryOriginals G L+2^width < 2^w := by omega
  have hheap : staging+queryOriginals G L < 2^w := (Nat.le_add_right _ _).trans_lt hret
  simp only [stagedConvertedGuestCursor,Expr.eval,BinOp.eval,ha,ho,hw,h1,hheap,hmod,hret,
    Nat.shiftLeft_eq,Nat.one_mul,ite_eq_left]

/-- Export the cursor through the same return convention as the staged
selector that packs one-bit weights. -/
def stagedConvertedTreeReturn (R convert tree : ℕ) : Stmt :=
  .seq (stagedConvertAndTreeBody R convert tree) (.ret stagedConvertedGuestCursor)

/-- Returning the guest cursor preserves the tree result memory. -/
theorem stagedConvertedTreeReturn_runs {w R convert tree : ℕ}
    {p : Program} {ω : ℕ → Bool} (st out : State) (cost cursor : ℕ)
    (hr : Runs w p ω (stagedConvertAndTreeBody R convert tree) st .normal out cost)
    (hc : stagedConvertedGuestCursor.eval w out = some cursor) :
    Runs w p ω (stagedConvertedTreeReturn R convert tree) st (.returned cursor) out
      (cost+stagedConvertedGuestCursor.size+2) := by
  have hret : Runs w p ω (.ret stagedConvertedGuestCursor) out (.returned cursor) out
      (stagedConvertedGuestCursor.size+1) :=
    runs_ret_iff.mpr ⟨cursor,hc,rfl,rfl,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨out,cost,_,hr,hret,by omega⟩)

/-- The converted tree returns the same tree-table interface that
the subsequent deduplication pass consumes. -/
theorem stagedConvertedTree_result {w convert entry : ℕ}
    {p : Program} {ω : ℕ → Bool} (st out : State)
    (guest : Program) (D : ℕ) (G T : MGraph) (L sim staging cost : ℕ)
    (hn : out.regs 0 = G.n) (hm : out.regs 1 = G.m) (hL : out.regs 2 = L)
    (hs : out.regs 3 = sim) (ha : out.regs 5 = staging)
    (hguest : queryHeap G L < 2^w) :
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let heap := staging+queryOriginals G L
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let cursor := heap+2^width
    out.regs 4 = width → heap+1+2^width ≤ 2^w →
    Runs w p ω (stagedConvertAndTreeBody R convert entry) st .normal out cost →
    out.mem (heap+1+queryHeader G L) ≤ G.n →
    out.mem (heap+1+queryHeader G L+1) ≤ G.n →
    treeFromOutput G out.mem (heap+1+queryOriginals G L)
      (heap+1+queryBridges G L) (heap+1+queryHeader G L) = T →
    (∀ a < staging+queryWeights G L, out.mem a = st.mem a) →
    ZeroFrom out.mem (heap+1+2^width) →
    Runs w p ω (stagedConvertedTreeReturn R convert entry) st (.returned cursor) out
      (cost+stagedConvertedGuestCursor.size+2) ∧
    stagedGuestResult guest D G T L sim staging st.mem cursor out.mem := by
  intro R heap width cursor hw hspace hr hcount hbridges htree hframe hzero
  have he := stagedConvertedGuestCursor_eval out G L sim width staging hn hm hL hs hw ha hguest hspace
  exact ⟨stagedConvertedTreeReturn_runs st out cost cursor hr he,
    rfl,hcount,hbridges,htree,hframe,hzero⟩

/-- Select the padded guest width without changing the host input
tables or the runtime precision registers. -/
theorem stagedConvertedWidth_runs {w select : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (guest : Program) (D : ℕ) (G : MGraph) (L sim staging : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (hnPos : 0 < G.n) (hmPos : 0 < G.m)
    (hsPos : 0 < sim) (hD : 0 < D)
    (hc : MeetsContract w p select (selectPaddedGuestWidthContract w guest D)) :
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let args := [G.n,G.m,sim,queryHeap G L]
    staging+queryOriginals G L+1+2^width ≤ 2^w →
    ∃ out cost, Runs w p ω (.call 4 select paddedWidthArgs) st .normal out cost ∧
      out.regs 4 = width ∧ out.mem = st.mem ∧ (∀ r, r ≠ 4 → out.regs r = st.regs r) ∧
      queryHeap G L < 2^w ∧ width ≤ w ∧ 4 ≤ 2^w ∧
      cost ≤ argsSize paddedWidthArgs+(selectPaddedGuestWidthContract w guest D).cost args st.mem+1 := by
  intro width args hspace
  obtain ⟨hpre,hguest,hwidth,hfour⟩ :=
    stagedGuestWidth_fit guest D G L sim staging hnPos hmPos hsPos hD st.mem hspace
  have he : evalArgs w st paddedWidthArgs = some args := by
    have hcanon := canonicalGuestArgsExpr_eval (w := w) (st := st) G L sim
      (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
      (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hguest
    have hheap := evalArgs_getD hcanon 11
    simp only [paddedWidthArgs,args,evalArgs,Expr.eval,hn,hm,hs,hheap]
    rfl
  have hwords : ∀ a ∈ args, a < 2^w := by
    obtain ⟨n,m,S,H,heq,_,_,_,_,hnfit,hsfit,_,_⟩ := hpre
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
    have hmFit : G.m < 2^w := by
      unfold queryHeap queryHeader queryBridges queryOriginals queryWeights queryLengths at hguest
      omega
    intro a ha
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨out,cost,ret,hrun,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 4) hc he hwords hpre ω
  obtain ⟨n,m,S,H,heq,hr,hmem⟩ := hpost
  simp only [args,List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
  exact ⟨out,cost,hrun,hret.trans hr,hmem,hregs,hguest,hwidth,hfour,hcost⟩

/-- Select the padded guest width, convert the host weights, and return
the cursor of the true low-stretch tree call. -/
def selectAndQueryConvertedTreeBody (guest : Program) (select convert tree : ℕ) : Stmt :=
  .seq (.call 4 select paddedWidthArgs)
    (stagedConvertedTreeReturn (Program.mk (lsstModule guest 0 1)).regBound convert tree)

/-- Width selection and the converted guest return share the same
staging memory. The selector's cost includes both machine phases. -/
theorem selectAndQueryConvertedTree_runs {w select convert tree : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (guest : Program) (D : ℕ)
    (G T : MGraph) (L sim staging budget : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (hnPos : 0 < G.n) (hmPos : 0 < G.m)
    (hsPos : 0 < sim) (hD : 0 < D)
    (hc : MeetsContract w p select (selectPaddedGuestWidthContract w guest D)) :
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    staging+queryOriginals G L+1+2^width ≤ 2^w →
    (∀ ready : State, ready.regs 4 = width → ready.mem = st.mem →
      (∀ r, r ≠ 4 → ready.regs r = st.regs r) →
      queryHeap G L < 2^w → width ≤ w → 4 ≤ 2^w →
      ∃ o out cost, Runs w p ω (stagedConvertedTreeReturn R convert tree) ready o out cost ∧
        stagedGuestResult guest D G T L sim staging ready.mem o.value out.mem ∧ cost ≤ budget) →
    ∃ o out cost, Runs w p ω (selectAndQueryConvertedTreeBody guest select convert tree)
      st o out cost ∧ stagedGuestResult guest D G T L sim staging st.mem o.value out.mem ∧
      cost ≤ argsSize paddedWidthArgs +
        (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] st.mem +
        budget+2 := by
  intro width R hspace hnext
  obtain ⟨ready,cw,hr,hw,hmem,hregs,hguest,hwFit,hfour,hcw⟩ :=
    stagedConvertedWidth_runs (ω := ω) st guest D G L sim staging
      hn hm hL hs hnPos hmPos hsPos hD hc hspace
  obtain ⟨o,out,ct,ht,hpost,hct⟩ := hnext ready hw hmem hregs hguest hwFit hfour
  exact ⟨o,out,cw+ct+1,runs_seq_iff.mpr (Or.inr ⟨ready,cw,ct,hr,ht,rfl⟩),
    hmem ▸ hpost,by omega⟩

/-- The four-bit selector runs width selection, host conversion, and
tree selection with their explicit machine costs. -/
theorem selectAndQueryConvertedTree_verified
    {w select convert entry c₀ D : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (guest : Program) (G tree : MGraph)
    (L staging guestCost src stride hostL P Q : ℕ) (len wt : ℕ → ℤ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = lsstLSimMin c₀ G.n G.m L 1)
    (ha : st.regs 5 = staging) (hsrc : st.regs 8 = src) (hst : st.regs 9 = stride)
    (hhL : st.regs 19 = hostL) (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hnPos : 0 < G.n) (hmPos : 0 < G.m) (hLpos : 0 < L) (hD : 0 < D)
    (hc₀ : 1 ≤ c₀)
    (hselect : MeetsContract w p select (selectPaddedGuestWidthContract w guest D))
    (hconvert : MeetsContract w p convert (packGuestStridedContract w)) :
    let heap := staging+queryOriginals G L
    let dst := staging+queryWeights G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let actual := relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)
    let packed := [src,dst,stride,hostL,P,Q,L,G.m]
    let budget := argsSize stagedGuestWeightsArgs + (80*L+37)*G.m +
      argsSize (stagedConvertedTreeArgs R)+17*(queryOriginals G L+1)+(R+6)*guestCost+
      stagedConvertedGuestCursor.size+16
    heap+1+2^width ≤ 2^w → (∀ a ∈ actual, a < 2^w) →
    (∀ a ∈ packed, a < 2^w) → (packGuestStridedContract w).pre packed st.mem →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) = queryNumerator Q (fixVal st.mem (src+i*stride) 4 hostL P)) →
    ZeroFrom st.mem (heap+1) →
    MeetsContract w p entry
      (relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree) →
    ∃ o out cost, Runs w p ω (selectAndQueryConvertedTreeBody guest select convert entry)
      st o out cost ∧ stagedGuestResult guest D G tree L sim staging st.mem o.value out.mem ∧
      cost ≤ argsSize paddedWidthArgs +
        (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] st.mem +
        budget+2 := by
  intro heap dst R sim width args actual packed budget hspace hwords hpw hpre
    ht hh hlen hwt hz hcall
  have hsim : 0 < sim := by
    dsimp only [sim]
    rw [lsstLSimMin_one_eq c₀ G.n G.m L hc₀]
    exact Nat.mul_pos (by omega) (by omega)
  apply selectAndQueryConvertedTree_runs st guest D G tree L sim staging budget
    hn hm hL hs hnPos hmPos hsim hD hselect hspace
  intro ready hw hmem hregs hguest _ _
  obtain ⟨out,cost,hr,htree,hcount,hbridges,hframe,hzero,hregs',hcost⟩ :=
    stagedConvertAndTree_runs (ω := ω) ready guest G tree L staging guestCost src stride hostL P Q len wt
      ((hregs _ (by decide)).trans hn) ((hregs _ (by decide)).trans hm)
      ((hregs _ (by decide)).trans hL) ((hregs _ (by decide)).trans hs) hw
      ((hregs _ (by decide)).trans ha) ((hregs _ (by decide)).trans hsrc)
      ((hregs _ (by decide)).trans hst) ((hregs _ (by decide)).trans hhL)
      ((hregs _ (by decide)).trans hP) ((hregs _ (by decide)).trans hQ)
      hguest hLpos hspace hwords hpw (hmem.symm ▸ hpre) (hmem.symm ▸ ht)
      (hmem.symm ▸ hh) (hmem.symm ▸ hlen) (hmem.symm ▸ hwt) (hmem.symm ▸ hz) hconvert hcall
  have keep (r : ℕ) (h6 : r ≠ 6) (h7 : r ≠ 7) (h4 : r ≠ 4) :
      out.regs r = st.regs r := (hregs' r h6 h7).trans (hregs r h4)
  obtain ⟨hret,hresult⟩ :=
    stagedConvertedTree_result ready out guest D G tree L sim staging cost
      ((keep _ (by decide) (by decide) (by decide)).trans hn)
      ((keep _ (by decide) (by decide) (by decide)).trans hm)
      ((keep _ (by decide) (by decide) (by decide)).trans hL)
      ((keep _ (by decide) (by decide) (by decide)).trans hs)
      ((keep _ (by decide) (by decide) (by decide)).trans ha)
      hguest ((hregs' _ (by decide) (by decide)).trans hw)
      hspace hr hcount hbridges htree hframe hzero
  exact ⟨.returned (heap+2^width),out,_,hret,hresult,by dsimp only [budget,R] at *; omega⟩

/-- Pass the staged guest inputs, using zero for the reserved argument
slots. Register nineteen contains the host limb count. -/
def convertedGuestCallArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.const 0,.reg 5,.const 0,.const 0,
    .reg 8,.reg 9,.reg 10,.reg 11] ++ List.replicate 7 (.const 0) ++ [.reg 19]

/-- The selected arguments encode the exact converted selector input. -/
theorem convertedGuestCallArgs_eval {w : ℕ} {st : State}
    (G : MGraph) (L sim staging src stride P Q hostL : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hsim : st.regs 3 = sim) (hstage : st.regs 5 = staging) (hsrc : st.regs 8 = src)
    (hstride : st.regs 9 = stride) (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hhost : st.regs 19 = hostL) (hw : 0 < 2^w) :
    evalArgs w st convertedGuestCallArgs =
      some (stagedGuestArgs G L sim staging src stride P Q ++ List.replicate 7 0 ++ [hostL]) := by
  simp [convertedGuestCallArgs,stagedGuestArgs,evalArgs,Expr.eval,
    hn,hm,hL,hsim,hstage,hsrc,hstride,hP,hQ,hhost,hw]

/-- The converted selector receives the host width after the twelve
guest arguments and seven reserved register slots. -/
theorem convertedGuest_startState (G : MGraph) (L sim staging src stride P Q hostL : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) :
    let args := stagedGuestArgs G L sim staging src stride P Q ++ List.replicate 7 0 ++ [hostL]
    let st := startState args mem pos
    st.regs 0 = G.n ∧ st.regs 1 = G.m ∧ st.regs 2 = L ∧ st.regs 3 = sim ∧
    st.regs 5 = staging ∧ st.regs 8 = src ∧ st.regs 9 = stride ∧
    st.regs 10 = P ∧ st.regs 11 = Q ∧ st.regs 19 = hostL ∧ st.mem = mem := by
  simp [stagedGuestArgs,startState]

/-- The converted selector reads the copied endpoints and lengths, and
packs only the live strided host weight blocks. -/
def convertedSelectorReady (w : ℕ) (G : MGraph)
    (L sim staging src stride P Q hostL : ℕ) (len wt : ℕ → ℤ)
    (input : List ℕ) (mem : ℕ → ℕ) : Prop :=
  input = stagedGuestArgs G L sim staging src stride P Q ++ List.replicate 7 0 ++ [hostL] ∧
  (packGuestStridedContract w).pre [src,staging+queryWeights G L,stride,hostL,P,Q,L,G.m] mem ∧
  (∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i) ∧
  (∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i) ∧
  (∀ i < G.m, ListAt mem (staging+queryLengths G+i*L)
    (encodeLimbs 1 L (len (edgeName G i)))) ∧
  (∀ i < G.m, wt (edgeName G i) = queryNumerator Q (fixVal mem (src+i*stride) 4 hostL P)) ∧
  ZeroFrom mem (staging+queryOriginals G L+1)

/-- The padded workspace bound makes the relocated selector arguments
fit on the host. The simulation register is checked in the guest width. -/
theorem stagedController_relocatedWords (guest : Program) (H : MGraph)
    (D L sim staging R w : ℕ) (hm : 0 < H.m) :
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H L)
    let heap := staging+queryOriginals H L
    let args := [H.n,H.m,0,H.m,queryLengths H,queryWeights H L,L,sim,
      queryOriginals H L,queryBridges H L,queryHeader H L,queryHeap H L]
    heap+1+2^width ≤ 2^w →
    ∀ a ∈ relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals H L), a < 2^w := by
  intro width heap args hfit
  have hheap : queryHeap H L < 2^width :=
    (Nat.le_add_right _ _).trans_lt (guestAllocation_lt_paddedModulus guest D H.n H.m sim (queryHeap H L))
  have hsim : sim < 2^width := by
    have hw := guestAllocation_lt_paddedModulus guest D H.n H.m sim (queryHeap H L)
    have hsimSpace : sim ≤ (2+3*(4*H.m))*sim :=
      Nat.le_mul_of_pos_left _ (by omega)
    change _ < 2^width at hw
    unfold guestWorkspace at hw
    omega
  have hL : L ≤ H.m*L := Nat.le_mul_of_pos_left _ hm
  apply relocatedTreeArgs_words (guestWidth := width) (by
    intro r
    by_cases hr : r < args.length
    · have hmem : args[r] ∈ args := List.getElem_mem hr
      have hword : args[r] < 2^width := by
        simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
        all_goals rw [h]
        all_goals first | exact hheap | exact hsim | (simp only [queryHeap,queryHeader,queryBridges,queryOriginals,queryWeights,queryLengths] at hheap ⊢; omega)
      simpa only [List.getD_eq_getElem args 0 hr] using hword
    · rw [List.getD_eq_default args 0 (Nat.le_of_not_gt hr)]
      exact Nat.two_pow_pos _) (by omega) hfit
  dsimp [heap]
  omega

/-- The converter's destination follows the copied prefix, and the
remaining converter arguments already occur in the selector call. -/
theorem stagedController_packedWords (H : MGraph) (w L sim staging src stride P Q hostL : ℕ)
    (hargs : ∀ a ∈ stagedGuestArgs H L sim staging src stride P Q ++
      List.replicate 7 0 ++ [hostL], a < 2^w)
    (hheap : staging+queryOriginals H L < 2^w) :
    ∀ a ∈ [src,staging+queryWeights H L,stride,hostL,P,Q,L,H.m], a < 2^w := by
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inl =>
    have hle : staging+queryWeights H L ≤ staging+queryOriginals H L :=
      Nat.add_le_add_left (Nat.le_add_right _ _) _
    exact hle.trans_lt hheap
  all_goals exact hargs _ (by simp [stagedGuestArgs])

/-- Cost of selecting the guest width, packing the weights, and running the tree call. -/
def convertedTreeSelectorCost (w : ℕ) (guest : Program) (D : ℕ) (G : MGraph)
    (L sim guestCost : ℕ) : ℕ :=
  let R := (Program.mk (lsstModule guest 0 1)).regBound
  let budget := argsSize stagedGuestWeightsArgs + (80*L+37)*G.m +
    argsSize (stagedConvertedTreeArgs R)+17*(queryOriginals G L+1)+(R+6)*guestCost+
    stagedConvertedGuestCursor.size+16
  argsSize paddedWidthArgs +
    (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] (fun _ => 0) +
    budget+2

/-- The caller pays a linear edge scan, the relocated guest run, and
the cost of selecting the guest word width. -/
theorem convertedTreeSelectorCost_eq (w : ℕ) (guest : Program) (D : ℕ)
    (G : MGraph) (L sim guestCost : ℕ) :
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    convertedTreeSelectorCost w guest D G L sim guestCost =
      (114*L+71)*G.m+(R+6)*guestCost+
      (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] (fun _ => 0)+
      (argsSize paddedWidthArgs+argsSize stagedGuestWeightsArgs+
        argsSize (stagedConvertedTreeArgs R)+stagedConvertedGuestCursor.size+35) := by
  dsimp only [convertedTreeSelectorCost, queryOriginals, queryWeights, queryLengths]
  ring

/-- Bound the selector's width calculation using the original graph
counts and an upper bound on the guest limb count. -/
theorem convertedTreeSelector_widthCost_le (w : ℕ) (guest : Program) (D : ℕ)
    (G : MGraph) (L sim n m limbs simMax : ℕ)
    (hn : G.n ≤ n) (hm : G.m ≤ m) (hL : L ≤ limbs) (hs : sim ≤ simMax) :
    let heapMax := (2+2*limbs)*m+3*n+2
    (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] (fun _ => 0) ≤
      guestWorkspaceCost guest D n simMax+40*paddedGuestWidth guest D n m simMax heapMax+65 := by
  intro heapMax
  have hheap : queryHeap G L ≤ heapMax := by
    unfold queryHeap queryHeader queryBridges queryOriginals queryWeights queryLengths
    have hcount : G.m*L ≤ m*limbs := Nat.mul_le_mul hm hL
    dsimp [heapMax]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm limbs m, Nat.two_mul (m*limbs)]
    omega
  have hwidth := paddedGuestWidth_mono guest (D := D) le_rfl hn hm hs hheap
  have hnSize := Nat.size_le_size (Nat.add_le_add_right hn 2)
  have hsSize := Nat.size_le_size (Nat.add_le_add_right hs 4)
  have hwork : guestWorkspaceCost guest D G.n sim ≤ guestWorkspaceCost guest D n simMax := by
    unfold guestWorkspaceCost
    gcongr
  exact (selectPaddedGuestWidth_cost_le w guest D G.n G.m sim (queryHeap G L) _).trans
    (Nat.add_le_add_right (Nat.add_le_add hwork (Nat.mul_le_mul_left 40 hwidth)) 65)

/-- Charge a converted selection to the original edge count given
a linear bound on the guest run and upper bounds on its runtime sizes. -/
theorem convertedTreeSelectorCost_le (w : ℕ) (guest : Program) (D : ℕ)
    (G : MGraph) (L sim guestCost n m limbs simMax guestFactor : ℕ)
    (hn : G.n ≤ n) (hm : G.m ≤ m) (hL : L ≤ limbs) (hs : sim ≤ simMax)
    (hguest : guestCost ≤ guestFactor*(m+1)) :
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let heapMax := (2+2*limbs)*m+3*n+2
    convertedTreeSelectorCost w guest D G L sim guestCost ≤
      ((114*limbs+71)+(R+6)*guestFactor+guestWorkspaceCost guest D n simMax+
        40*paddedGuestWidth guest D n m simMax heapMax+argsSize paddedWidthArgs+
        argsSize stagedGuestWeightsArgs+argsSize (stagedConvertedTreeArgs R)+
        stagedConvertedGuestCursor.size+100)*(m+1) := by
  intro R heapMax
  have hwidth := convertedTreeSelector_widthCost_le w guest D G L sim n m limbs simMax hn hm hL hs
  have hscan : (114*L+71)*G.m ≤ (114*limbs+71)*(m+1) := by
    exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 114 hL) 71)
      (hm.trans (Nat.le_succ _))
  have hrun := Nat.mul_le_mul_left (R+6) hguest
  rw [convertedTreeSelectorCost_eq]
  simp only [Nat.add_mul]
  rw [← Nat.mul_assoc] at hrun
  simp only [Nat.add_mul] at hrun hscan
  have hpay (x : ℕ) : x ≤ x*(m+1) :=
    Nat.le_mul_of_pos_right x (Nat.succ_pos m)
  have h₁ := hpay (guestWorkspaceCost guest D n simMax)
  have h₂ := hpay (40*paddedGuestWidth guest D n m simMax heapMax)
  have h₃ := hpay (argsSize paddedWidthArgs)
  have h₄ := hpay (argsSize stagedGuestWeightsArgs)
  have h₅ := hpay (argsSize (stagedConvertedTreeArgs R))
  have h₆ := hpay stagedConvertedGuestCursor.size
  have h₇ := hpay 100
  dsimp only [R,heapMax] at *
  omega

/-- The staged selector packs model weights, returns the selected compact tree,
and preserves the input region used by the numeric pass. -/
def convertedTreeSelectorContract (w : ℕ) (guest : Program) (D : ℕ)
    (G tree : MGraph) (L sim staging guestCost src stride hostL P Q : ℕ)
    (len wt : ℕ → ℤ) : Contract where
  pre := convertedSelectorReady w G L sim staging src stride P Q hostL len wt
  post := fun _ => stagedGuestResult guest D G tree L sim staging
  cost := fun _ _ => convertedTreeSelectorCost w guest D G L sim guestCost

/-- Install the converted selector at the index used by the rebuild round. -/
theorem selectAndQueryConvertedTree_meetsContract
    {w selector select convert entry c₀ D workspace padded log block : ℕ} {p : Program} {K : ℝ}
    (guest : Program) (G tree : MGraph) (L staging guestCost src stride hostL P Q : ℕ)
    (len wt : ℕ → ℤ)
    (he : p.procs[selector]? = some (selectAndQueryConvertedTreeBody guest select convert entry))
    (hn : 0 < G.n) (hm : 0 < G.m) (hL : 0 < L) (hD : 0 < D) (hc₀ : 1 ≤ c₀)
    (hselectBody : p.procs[select]? = some (selectPaddedGuestWidthBody workspace padded))
    (hworkspace : p.procs[workspace]? = some (guestWorkspaceBody guest D log))
    (hpadded : p.procs[padded]? = some (paddedGuestWidthBody log))
    (hlog : p.HasAt log (Scaling.Machine.clogTwoModule log))
    (hconvertBody : p.procs[convert]? = some (packGuestStridedBody block))
    (hblock : MeetsContract w p block (conversionBlockContract w))
    (htreeProcs : p.HasAt entry (relocatedTreeProcedures guest entry))
    (hK : max K 0 ≤ (D : ℝ)) :
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let heap := staging+queryOriginals G L
    heap+1+2^width ≤ 2^w →
    (p.HasAt entry (relocatedTreeProcedures guest entry) → max K 0 ≤ (D : ℝ) →
      width ≤ w → heap+1+2^width ≤ 2^w → 4 ≤ 2^w →
      MeetsContract w p entry
      (relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree)) →
    MeetsContract w p selector
      (convertedTreeSelectorContract w guest D G tree L sim staging guestCost src stride
        hostL P Q len wt) := by
  intro sim width heap hspace hcall
  let R := (Program.mk (lsstModule guest 0 1)).regBound
  have hwidth : width ≤ w := by
    by_contra! hlt
    have hpow : 2^w < (2 : ℕ)^width := Nat.pow_lt_pow_right (by decide) hlt
    omega
  have hfour : 4 ≤ 2^w := by
    have hwmin : 5 ≤ width := by
      unfold width paddedGuestWidth
      exact le_max_left _ _
    have hpow : (2 : ℕ)^5 ≤ 2^width := Nat.pow_le_pow_right (by decide) hwmin
    omega
  have hselect := selectPaddedGuestWidth_meetsContract guest D hselectBody
    (guestWorkspace_meetsContract (w := w) guest D hworkspace hlog)
    (paddedGuestWidth_meetsContract hpadded hlog)
  have hconvert := packGuestStrided_meetsContract hconvertBody
    (guestLengthBlock_meetsContract hblock)
  apply meetsContract_of_runs he
  intro input mem pos ω hinput hpre
  obtain ⟨rfl,hpack,ht,hh,hlen,hwt,hzero⟩ := hpre
  have hwords := stagedController_relocatedWords guest G D L sim staging R w hm hspace
  have hpw := stagedController_packedWords G w L sim staging src stride P Q hostL hinput
    (show heap < 2^w from ((Nat.lt_succ_self heap).trans_le (Nat.le_add_right _ _)).trans_le hspace)
  obtain ⟨hr0,hr1,hr2,hr3,hr5,hr8,hr9,hr10,hr11,hr19,_⟩ :=
    convertedGuest_startState G L sim staging src stride P Q hostL mem pos
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    selectAndQueryConvertedTree_verified (ω := ω) _ guest G tree L staging guestCost
      src stride hostL P Q len wt hr0 hr1 hr2 hr3 hr5 hr8 hr9 hr19 hr10 hr11
      hn hm hL hD hc₀ hselect hconvert hspace hwords hpw hpack ht hh hlen hwt hzero (hcall htreeProcs hK hwidth hspace hfour)
  exact ⟨o,out,cost,hrun,hpost,hcost⟩

/-- Positive model weights that fit the graph-derived guest format
discharge the strided converter's block checks. -/
theorem packGuestStrided_pre_of_weights {w : ℕ} (G : MGraph)
    (mem : ℕ → ℕ) (v : ℕ → ℝ) (src dst stride L P Q N : ℕ)
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P+N < 2^w) (hQ : Q < 2^w)
    (hm : G.m < 2^w) (hstride : L ≤ stride) (hsrc : ∀ i < G.m, src+i*stride+L ≤ dst)
    (hroom : dst+G.m*N < 2^w)
    (hweights : ∀ i < G.m, Valid mem (src+i*stride) 4 L ∧
      fixVal mem (src+i*stride) 4 L P = v (edgeName G i))
    (hpos : ∀ e ∈ G.E, 0 ≤ v e)
    (hfit : ∀ e ∈ G.E, Fits 1 N (queryNumerator Q (v e))) :
    (packGuestStridedContract w).pre [src,dst,stride,L,P,Q,N,G.m] mem := by
  refine ⟨src,dst,stride,L,P,Q,N,G.m,rfl,hw,hL,hP,hQ,hm,hstride,hsrc,hroom,?_⟩
  intro i hi
  obtain ⟨hv,he⟩ := hweights i hi
  have hp := hpos _ (edgeName_mem hi)
  rw [← he,fixVal] at hp
  have hd : (0 : ℝ) < (2 : ℝ)^P := by positivity
  refine ⟨hv,?_,he.symm ▸ hfit _ (edgeName_mem hi)⟩
  have hnum := (le_div_iff₀ hd).mp hp
  rw [zero_mul] at hnum
  exact_mod_cast hnum

end MinCostFlow.LastLevelProgram
