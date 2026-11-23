module

public import MinCostFlow.LastLevelProgram.RelocatedTreeCall
public import MinCostFlow.LastLevelProgram.SelectTreeCall
public import MinCostFlow.LastLevelProgram.SelectedTraversal
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Selecting the guest width before a staged tree query

The last-level rebuild of Definition 5.8 (pages 19–20) computes the
width from the graph and guest format before calling Theorem 2.2.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord LSF

/-- Pass the counts, simulation width, and guest heap endpoint to the
width selector. -/
def paddedWidthArgs : List Expr :=
  [.reg 0,.reg 1,.reg 3,
    (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 11 (.const 0)]

/-- Pack each strided weight at the guest precision into the reserved
weight region immediately after the staged lengths. -/
def stagedWeightArgs : List Expr :=
  let offsets := canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)
  [.reg 8,.reg 9,.reg 2,.reg 1,.bin .sub (.reg 11) (.reg 10),
    .bin .add (.reg 5) (offsets.getD 5 (.const 0))]

/-- The packer receives the source stride, runtime precision difference,
and destination computed from the same offsets as the tree query. -/
theorem stagedWeightArgs_eval {w : ℕ} {st : State} (G : MGraph)
    (L sim staging src stride P Q : ℕ)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (ha : st.regs 5 = staging)
    (hsrc : st.regs 8 = src) (hstride : st.regs 9 = stride)
    (hP : st.regs 10 = P) (hQ : st.regs 11 = Q)
    (hheap : queryHeap G L < 2^w) (hdiff : Q-P < 2^w)
    (hdest : staging+queryWeights G L < 2^w) :
    evalArgs w st stagedWeightArgs = some [src,stride,L,G.m,Q-P,staging+queryWeights G L] := by
  have hargs := canonicalGuestArgsExpr_eval (st := st) G L sim
    (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
    (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs) hheap
  have hWeights :
      (((canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5
        (.const 0))).eval w st = some (queryWeights G L) := evalArgs_getD hargs 5
  simp only [stagedWeightArgs,evalArgs,Expr.eval,BinOp.eval,hm,hL,ha,hsrc,hstride,
    hP,hQ,hWeights,hdiff,hdest,ite_eq_left]

/-- The staged graph fixes the translated base. The table offsets within
that region are independent of the guest width and the returned cursor. -/
def stagedTreeTableArgs (n m limbs sim staging : Expr) : List Expr :=
  let offsets := canonicalGuestArgsExpr n m limbs sim
  let atIndex := fun i => offsets.getD i (.const 0)
  let base := Expr.bin .add (Expr.bin .add staging (atIndex 8)) (.const 1)
  [Expr.bin .add base (atIndex 8), Expr.bin .add base (atIndex 9),
    Expr.bin .add base (atIndex 10)]

/-- The tree's original edge names, bridge records, and header addresses
are words whenever the relocated result region fits. -/
theorem stagedTreeTableArgs_eval {w : ℕ} {st : State} {ne me le se ae : Expr}
    (G : MGraph) (L sim staging : ℕ)
    (hn : ne.eval w st = some G.n) (hm : me.eval w st = some G.m)
    (hL : le.eval w st = some L) (hs : se.eval w st = some sim)
    (ha : ae.eval w st = some staging)
    (hfit : staging+queryOriginals G L+1+queryHeap G L < 2^w) :
    let base := staging+queryOriginals G L+1
    evalArgs w st (stagedTreeTableArgs ne me le se ae) =
      some [base+queryOriginals G L,base+queryBridges G L,base+queryHeader G L] := by
  intro base
  have hh : queryHeap G L < 2^w := by omega
  have hargs := canonicalGuestArgsExpr_eval G L sim hn hm hL hs hh
  have hOriginal :
      ((canonicalGuestArgsExpr ne me le se).getD 8 (.const 0)).eval w st =
        some (queryOriginals G L) := evalArgs_getD hargs 8
  have hBridge :
      ((canonicalGuestArgsExpr ne me le se).getD 9 (.const 0)).eval w st =
        some (queryBridges G L) := evalArgs_getD hargs 9
  have hHeader :
      ((canonicalGuestArgsExpr ne me le se).getD 10 (.const 0)).eval w st =
        some (queryHeader G L) := evalArgs_getD hargs 10
  have hprefix : staging+queryOriginals G L < 2^w := by omega
  have hbase : base < 2^w := by dsimp [base]; omega
  have hone : 1 < 2^w := by omega
  have hlast : base+queryHeader G L < 2^w := by
    unfold queryHeap at hfit
    dsimp [base]
    omega
  have hbridges : base+queryBridges G L < 2^w := by
    unfold queryHeader at hlast
    omega
  have horiginals : base+queryOriginals G L < 2^w := by
    unfold queryBridges at hbridges
    omega
  simp only [stagedTreeTableArgs,evalArgs,Expr.eval,BinOp.eval,ha,hOriginal,hBridge,hHeader,
    hprefix,hone,ite_eq_left]
  simp only [base,hbase,horiginals,hbridges,hlast,ite_eq_left]

/-- Select the width into register four, then pack and query the tree. -/
def selectAndQueryPaddedTreeBody (guest : Program) (select pack query : ℕ) : Stmt :=
  let R := (Program.mk (lsstModule guest 0 1)).regBound
  let treeArgs := stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3)
    (.reg 4) (.reg 5) (.reg 6)
  .seq (.call 4 select paddedWidthArgs)
    (packAndQueryTreeBody pack query 6 7 stagedWeightArgs treeArgs stagedGuestCursorExpr)

/-- The input layout endpoint and every original-edge, bridge, and header
cell lie strictly before the end of the padded relocation region. -/
theorem stagedTreeTables_fit {w : ℕ} (guest : Program) (D : ℕ) (G : MGraph)
    (L sim staging : ℕ) :
    let base := staging+queryOriginals G L+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    base+2^width ≤ 2^w → base+queryHeap G L < 2^w := by
  intro base width hregion
  have halloc := guestAllocation_lt_paddedModulus guest D G.n G.m sim (queryHeap G L)
  change queryHeap G L+guestWorkspace guest D G.n G.m sim < 2^width at halloc
  omega

/-- A fitting relocated region provides the word bounds for computing its
width and evaluating the guest layout offsets. -/
theorem stagedGuestWidth_fit {w : ℕ} (guest : Program) (D : ℕ) (G : MGraph)
    (L sim staging : ℕ) (hn : 0 < G.n) (hm : 0 < G.m)
    (hs : 0 < sim) (hD : 0 < D) (mem : ℕ → ℕ) :
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    staging+queryOriginals G L+1+2^width ≤ 2^w →
    (selectPaddedGuestWidthContract w guest D).pre [G.n,G.m,sim,queryHeap G L] mem ∧
      queryHeap G L < 2^w ∧ width ≤ w ∧ 4 ≤ 2^w := by
  intro width hspace
  have halloc := guestAllocation_lt_paddedModulus guest D G.n G.m sim (queryHeap G L)
  change queryHeap G L+guestWorkspace guest D G.n G.m sim < 2^width at halloc
  have htable := stagedTreeTables_fit guest D G L sim staging hspace
  have hmod : 2^width < 2^w := by omega
  have hw : width < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hmod
  have hmin : 5 ≤ width := le_max_left _ _
  have hfit : 4 ≤ 2^w := by
    exact (show (4:ℕ) ≤ 2^5 by decide).trans
      ((Nat.pow_le_pow_right (by decide) hmin).trans hmod.le)
  have hwork : guestWorkspace guest D G.n G.m sim < 2^w := by omega
  have hnFit : G.n+4 < 2^w := by
    unfold guestWorkspace at hwork
    omega
  have hsFit : sim+6 < 2^w := by
    unfold guestWorkspace simDecodeSpace at hwork
    dsimp only at hwork
    omega
  have hprefix : 0 < queryOriginals G L := by
    unfold queryOriginals queryWeights queryLengths
    omega
  refine ⟨⟨G.n,G.m,sim,queryHeap G L,rfl,hn,hm,hs,hD,hnFit,hsFit,by omega,?_⟩,
    by omega,hw.le,hfit⟩
  exact Nat.lt_two_pow_self.trans hmod

/-- The fixed staged query calls the guest at the computed width and returns
the canonical tree in the translated result tables. -/
theorem selectAndQueryPaddedTree_runs {w pack query select P Q : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph}
    (st : State) (guest : Program) (c₀ D : ℕ) (K : ℝ) (hK : max K 0 ≤ (D : ℝ)) (len wt : ℕ → ℤ)
    (src stride L staging guestCost : ℕ) (guestOut : State)
    (hselect : MeetsContract w p select (selectPaddedGuestWidthContract w guest D))
    (hc : 1 ≤ c₀) (hG : (indexedGraph G).Valid)
    (hinstalled : p.HasAt query (relocatedTreeProcedures guest query))
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q)) :
    let wa := [src,stride,L,G.m,Q-P,staging+queryWeights G L]
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let minimum := max 5 (Nat.log 2 (queryHeap G L + lsstSpace guest K G.n G.m sim 1) + 1)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let treeArgs := stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3)
      (.reg 4) (.reg 5) (.reg 6)
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    Runs minimum ⟨lsstModule guest 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2^minimum, moved (base+a) = guestOut.mem a) →
      treeFromOutput G moved (base+queryOriginals G L)
        (base+queryBridges G L) (base+queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L+1) ≤ G.n →
    (∀ x ∈ wa, x < 2^w) →
    (packGuestWeightsContract w P Q).pre wa st.mem →
    st.regs 0 = G.n → st.regs 1 = G.m → st.regs 2 = L → st.regs 3 = sim →
    st.regs 5 = staging →
    0 < G.n → 0 < G.m → 0 < D →
    st.regs 8 = src → st.regs 9 = stride → st.regs 10 = P → st.regs 11 = Q →
    heap+1+2^width ≤ 2^w → 0 < L →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal st.mem (src+i*stride) 1 L P)) →
    ∃ o out cost, Runs w p ω (selectAndQueryPaddedTreeBody guest select pack query)
      st o out cost ∧
      (o.value = heap+2^width ∧ out.mem (heap+1+queryHeader G L) ≤ G.n ∧
        out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
        treeFromOutput G out.mem (heap+1+queryOriginals G L)
          (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
        (∀ a < staging+queryWeights G L, out.mem a = st.mem a) ∧
        ZeroFrom out.mem (heap+1+2^width)) ∧
      cost ≤ argsSize stagedWeightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
        17*(queryOriginals G L+1)+(R+6)*guestCost+6+stagedGuestCursorExpr.size +
        (selectPaddedGuestWidthContract w guest D).cost [G.n,G.m,sim,queryHeap G L] st.mem +
        argsSize paddedWidthArgs + 3 := by
  intro wa heap R sim width minimum args treeArgs tree hrun hdecode hcount hbridges
    hww hpre hn hm hL hs ha hnPos hmPos hD hsrc hstride hP hQ hspace hpos
    htail hhead hlen hwt
  have hsimPos : 0 < sim := by
    dsimp only [sim]
    rw [lsstLSimMin_one_eq c₀ G.n G.m L hc]
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨hwidthPre,hguest,hwidth,hfour⟩ :=
    stagedGuestWidth_fit guest D G L sim staging hnPos hmPos hsimPos hD st.mem hspace
  have hfit := hwidthPre
  obtain ⟨n,m,S,H,he,_,_,_,_,hnFit,hsFit,_,_⟩ := hfit
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hmFit : G.m < 2^w := by
    unfold queryHeap queryHeader queryBridges queryOriginals queryWeights queryLengths at hguest
    omega
  have hEval : evalArgs w st paddedWidthArgs = some [G.n,G.m,sim,queryHeap G L] := by
    have hargs := canonicalGuestArgsExpr_eval (st := st) G L sim
      (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
      (by simpa only [Expr.eval,Option.some.injEq] using hn) (by simpa only [Expr.eval,Option.some.injEq] using hm)
      (by simpa only [Expr.eval,Option.some.injEq] using hL) (by simpa only [Expr.eval,Option.some.injEq] using hs) hguest
    have hHeap := evalArgs_getD hargs 11
    simp only [paddedWidthArgs,evalArgs,Expr.eval,hn,hm,hs,hHeap]
    rfl
  apply runs_start_le
  unfold selectAndQueryPaddedTreeBody
  refine runs_seq_call_le hselect hEval (by wram_words) hwidthPre ?_
  intro ret mem pos hpst
  obtain ⟨n,m,S,H,he,hret,hmem⟩ := hpst
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  subst ret
  subst mem
  let next := State.mk st.mem (Function.update st.regs 4 width) pos
  have hdiff : Q-P < 2^w := hww _ (by simp [wa])
  have hdest : staging+queryWeights G L < 2^w := hww _ (by simp [wa])
  have hwa : evalArgs w next stagedWeightArgs = some wa := by
    apply stagedWeightArgs_eval G L sim staging src stride P Q
      _ _ _ _ _ _ _ _ _ hguest hdiff hdest
    all_goals simp [next,Function.update,hn,hm,hL,hs,ha,hsrc,hstride,hP,hQ]
  obtain ⟨o,out,c,hr,ho,hcst⟩ :=
    packAndQueryPaddedTree_runs next guest c₀ D K hK len wt src stride L staging guestCost
      guestOut hc hG hinstalled hp hrun hdecode hcount hbridges hwa
      hww hpre (by simp [next,Function.update,hn]) (by simp [next,Function.update,hm])
      (by simp [next,Function.update,hL]) (by simp [next,Function.update,hs,sim])
      (by simp [next,width,sim]) (by simp [next,Function.update,ha]) hguest hspace hwidth hfour
      hpos htail hhead hlen hwt
  exact ⟨o,out,c,hr,ho,by dsimp only [treeArgs,R,sim] at hcst ⊢; omega⟩

/-- Deduplication reads the selected edge indices and the header count.
Its marks and destination follow the last cell reserved by the guest. -/
def stagedDedupArgs (n m limbs sim staging cursor : Expr) : List Expr :=
  let tables := stagedTreeTableArgs n m limbs sim staging
  let marks := Expr.bin .add cursor (.const 1)
  [tables.getD 0 (.const 0), marks, .bin .add marks m,
    .load (tables.getD 2 (.const 0))]

/-- Evaluate the deduplication arguments from the staged tree tables and
the allocation cursor returned by the relocated call. -/
theorem stagedDedupArgs_eval {w : ℕ} {st : State} {ne me le se ae ce : Expr}
    (G : MGraph) (L sim staging cursor : ℕ)
    (hn : ne.eval w st = some G.n) (hm : me.eval w st = some G.m)
    (hL : le.eval w st = some L) (hs : se.eval w st = some sim)
    (ha : ae.eval w st = some staging) (hc : ce.eval w st = some cursor)
    (hfit : staging+queryOriginals G L+1+queryHeap G L < 2^w)
    (hroom : cursor+1+G.m < 2^w) :
    let base := staging+queryOriginals G L+1
    evalArgs w st (stagedDedupArgs ne me le se ae ce) =
      some [base+queryOriginals G L,cursor+1,cursor+1+G.m,
        st.mem (base+queryHeader G L)] := by
  intro base
  have ht := stagedTreeTableArgs_eval G L sim staging hn hm hL hs ha hfit
  have hSelected : ((stagedTreeTableArgs ne me le se ae).getD 0 (.const 0)).eval w st =
      some (base+queryOriginals G L) := evalArgs_getD ht 0
  have hHeader : ((stagedTreeTableArgs ne me le se ae).getD 2 (.const 0)).eval w st =
      some (base+queryHeader G L) := evalArgs_getD ht 2
  have hmarks : cursor+1 < 2^w := by omega
  have hone : 1 < 2^w := by omega
  simp only [stagedDedupArgs,evalArgs,Expr.eval,BinOp.eval,hc,hm,hSelected,hHeader,
    hmarks,hone,hroom,ite_eq_left,Option.map_some]

/-- The staged endpoint arrays and translated tree output supply the
deduplication precondition. The marks start in fresh memory immediately
after the guest region. -/
theorem dedup_pre_of_stagedQuery {w : ℕ} (guest : Program) (D : ℕ)
    (G T : MGraph) (L sim staging : ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (mem out : ℕ → ℕ)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hframe : ∀ a < staging+queryWeights G L, out a = mem a) :
    let base := staging+queryOriginals G L+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let selected := base+queryOriginals G L
    let bridges := base+queryBridges G L
    let header := base+queryHeader G L
    let marks := base+2^width
    let dest := marks+G.m
    let C := dedupSelectedTreeContract w G ℓ v γ selected bridges header
      marks dest staging (staging+G.m)
    treeFromOutput G out selected bridges header = T →
    out header ≤ G.n → ZeroFrom out marks →
    dest+G.n < 2^w → G.n+1 < 2^w →
    C.pre [selected,marks,dest,out header] out ∧
      C.cost [selected,marks,dest,out header] out ≤ 40*G.n+14 := by
  intro base width selected bridges header marks dest C hdecoded hcount hzero hroom hn
  have halloc := guestAllocation_lt_paddedModulus guest D G.n G.m sim (queryHeap G L)
  change queryHeap G L+guestWorkspace guest D G.n G.m sim < 2^width at halloc
  have htable : queryOriginals G L+G.n < 2^width := by
    unfold queryHeap queryHeader queryBridges at halloc
    omega
  have hprefix : 2*G.m ≤ queryWeights G L := by
    unfold queryWeights queryLengths
    omega
  have hprebase : staging+queryWeights G L ≤ base := by
    unfold base queryOriginals
    omega
  have hsep : staging+2*G.m ≤ marks := by
    dsimp [marks]
    omega
  refine ⟨⟨rfl,hdecoded.symm ▸ htree,by omega,?_,by rfl,by omega,
    by omega,by omega,?_,?_,fun e _ => hzero _ (Nat.le_add_right _ _)⟩,?_⟩
  · dsimp [selected,marks]
    omega
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    simpa using (hframe (staging+i) (by omega)).trans (ht i hi')
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    simpa [Nat.add_assoc] using
      (hframe (staging+(G.m+i)) (by omega)).trans (hh i hi')
  · change 40*out header+14 ≤ 40*G.n+14
    omega

/-- Read the staged result and record the number of retained tree edges. -/
def dedupStagedTreeBody (dedup : ℕ) : Stmt :=
  .call 13 dedup (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3)
    (.reg 5) (.reg 12))

/-- Deduplication leaves the compact tree for traversal and preserves
the staged graph and everything preceding it. -/
theorem dedupStagedTree_runs {w dedup : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (guest : Program) (D : ℕ) (G T : MGraph)
    (L sim staging : ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (mem : ℕ → ℕ)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hframe : ∀ a < staging+queryWeights G L, st.mem a = mem a) :
    let base := staging+queryOriginals G L+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let selected := base+queryOriginals G L
    let bridges := base+queryBridges G L
    let header := base+queryHeader G L
    let marks := base+2^width
    let dest := marks+G.m
    let C := dedupSelectedTreeContract w G ℓ v γ selected bridges header
      marks dest staging (staging+G.m)
    MeetsContract w p dedup C →
    st.regs 0 = G.n → st.regs 1 = G.m → st.regs 2 = L → st.regs 3 = sim →
    st.regs 5 = staging → st.regs 12 = staging+queryOriginals G L+2^width →
    treeFromOutput G st.mem selected bridges header = T →
    st.mem header ≤ G.n → ZeroFrom st.mem marks →
    dest+G.n < 2^w → G.n+1 < 2^w →
    ∃ out cost, ∃ kept : List ℕ, Runs w p ω (dedupStagedTreeBody dedup) st .normal out cost ∧
      out.regs 13 = kept.length ∧ kept.length ≤ G.n ∧ kept.Nodup ∧ ListAt out.mem dest kept ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
      (∀ a < staging+queryWeights G L, out.mem a = mem a) ∧
      ZeroFrom out.mem (dest+G.n) ∧
      (∀ r, r ≠ 13 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3)
        (.reg 5) (.reg 12)) + 40*G.n+15 := by
  intro base width selected bridges header marks dest C hd hn hm hL hs ha hc
    hdecoded hcount hzero hroom hword
  obtain ⟨hpre,hcost⟩ := dedup_pre_of_stagedQuery guest D G T L sim staging ℓ v γ
    mem st.mem htree ht hh hframe hdecoded hcount hzero hroom hword
  have hregion : base+2^width ≤ 2^w := by dsimp [dest,marks] at hroom; omega
  have htable := stagedTreeTables_fit guest D G L sim staging hregion
  have hsep : staging+queryWeights G L ≤ marks := by
    have hh : staging+queryWeights G L ≤ base := by
      dsimp only [base]
      unfold queryOriginals
      omega
    exact hh.trans (Nat.le_add_right _ _)
  have hdFit : staging+queryOriginals G L+2^width+1+G.m < 2^w := by
    dsimp [marks,base,dest] at hroom
    omega
  have hargs : evalArgs w st (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3)
      (.reg 5) (.reg 12)) = some [selected,marks,dest,st.mem header] := by
    simpa only [selected,marks,base,dest,header,Nat.add_right_comm] using
      stagedDedupArgs_eval (st := st) (ne := .reg 0) (me := .reg 1) (le := .reg 2)
        (se := .reg 3) (ae := .reg 5) (ce := .reg 12)
        G L sim staging (staging+queryOriginals G L+2^width)
        (congrArg some hn) (congrArg some hm) (congrArg some hL) (congrArg some hs)
        (congrArg some ha) (congrArg some hc) htable hdFit
  have hselected : selected < 2^w := by
    dsimp [selected,base]
    unfold queryHeap queryHeader queryBridges at htable
    omega
  have hmarks : marks < 2^w := by dsimp [dest] at hroom; omega
  have hdest : dest < 2^w := by omega
  have hcnt : st.mem header < 2^w := by omega
  obtain ⟨out,cost,ret,hr,hpost,hretReg,hregs,hcst⟩ :=
    runs_call_of_meetsContract (r := 13) hd hargs (by wram_words) hpre ω
  obtain ⟨kept,hret,hlen,hnd,hlist,heq,hf⟩ := hpost
  refine ⟨out,cost,kept,hr,hretReg.trans hret,?_,hnd,hlist,heq.trans hdecoded,?_,?_,hregs,?_⟩
  · exact (hret ▸ hlen).trans hcount
  · intro a ha
    exact (hf a (Or.inl (ha.trans_le hsep))).trans (hframe a ha)
  · intro a ha
    exact (hf a (Or.inr (by omega))).trans (hzero a (by dsimp [dest] at ha; omega))

  · have hb : C.cost [selected,marks,dest,st.mem header] st.mem ≤ 40*G.n+14 := hcost
    omega

/-- The retained edge array and the input prefix survive numeric
preparation, which writes beyond the reserved incidence region. -/
def retainedStagedTreeAt (G T : MGraph) (base dest count : ℕ) (mem out : ℕ → ℕ) : Prop :=
  ∃ kept : List ℕ, count = kept.length ∧ kept.length ≤ G.n ∧ kept.Nodup ∧
    ListAt out dest kept ∧
    decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
    ∀ a < base, out a = mem a

/-- Numeric work that retains the staged tree also retains every word
below the incoming cursor. This is the frame used by branch publication. -/
theorem retainedStagedTreeAt_frame {G T : MGraph} {base dest count cursor : ℕ}
    {mem out : ℕ → ℕ} (hTree : retainedStagedTreeAt G T base dest count mem out)
    (hcursor : cursor ≤ base) :
    ∀ a < cursor, out a = mem a := by
  obtain ⟨_,_,_,_,_,_,hframe⟩ := hTree
  exact fun a ha => hframe a (ha.trans_le hcursor)

/-- Allocating the unit block preserves the tree and its input prefix
when both fit below the numeric allocation end. -/
theorem retainedStagedTreeAt_congr {G T : MGraph} {base dest count limit : ℕ}
    {mem mid out : ℕ → ℕ}
    (hTree : retainedStagedTreeAt G T base dest count mem mid)
    (hbase : base ≤ limit) (hdest : dest+G.n ≤ limit)
    (hframe : ∀ a < limit, out a = mid a) :
    retainedStagedTreeAt G T base dest count mem out := by
  obtain ⟨kept,hcount,hsize,hnd,hlist,hdecode,hprefix⟩ := hTree
  have hspan : dest+kept.length ≤ limit := by omega
  exact ⟨kept,hcount,hsize,hnd,
    hlist.congr (fun a ha hb => hframe a (hb.trans_le hspan)),hdecode,
    fun a ha => (hframe a (ha.trans_le hbase)).trans (hprefix a ha)⟩

/-- The selected tree remains available after writing past its array. -/
theorem retainedStagedTreeAt_of_frame {G T : MGraph} {base dest count limit : ℕ}
    {mem mid out : ℕ → ℕ}
    (hTree : selectedTreeAt G T base dest count mem mid)
    (hbase : base ≤ limit) (hdest : dest+G.n ≤ limit)
    (hframe : ∀ a < limit, out a = mid a) :
    retainedStagedTreeAt G T base dest count mem out := by
  obtain ⟨kept,he,hsize,hnd,hlist,hdecode,hf,_⟩ := hTree
  refine ⟨kept,he,hsize,hnd,?_,hdecode,fun a ha => (hframe a (ha.trans_le hbase)).trans (hf a ha)⟩
  intro i hi
  exact (hframe _ (by omega)).trans (hlist i hi)

/-- The deduplicated edge list and the preserved staged endpoints supply
the traversal input. Heads and records occupy consecutive fresh arrays. -/
theorem adjacency_pre_of_stagedTree {w : ℕ} (G T : MGraph)
    (L staging dest reserve count : ℕ) (mem out : ℕ → ℕ)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hTree : retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem out)
    (hsep : staging+queryWeights G L ≤ dest)
    (hroom : dest+G.n+reserve+G.n+6*G.n < 2^w) :
    let adj := dest+G.n+reserve
    let records := adj+G.n
    ∃ kept : List ℕ, count = kept.length ∧ kept.Nodup ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
      (selectedAdjacencyContract w (indexedGraph G) kept
        dest staging (staging+G.m) adj records).pre
        [dest,staging,staging+G.m,adj,records,count] out := by
  intro adj records
  have hprefix : 2*G.m ≤ queryWeights G L := by
    unfold queryWeights queryLengths
    omega
  have halloc : dest+G.n ≤ adj := Nat.le_add_right _ _
  have hbase : staging+queryWeights G L ≤ adj :=
    hsep.trans ((Nat.le_add_right _ _).trans halloc)
  obtain ⟨kept,he,hsize,hnd,hlist,hdecode,hframe⟩ := hTree
  have hrec : records+6*kept.length < 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsize) records).trans_lt hroom
  refine ⟨kept,he,hnd,hdecode,by rw [he],?_,?_,?_,le_rfl,hrec,hlist,?_,?_⟩
  · exact (Nat.add_le_add_left hsize dest).trans halloc
  · change staging+G.m ≤ adj
    omega
  · change staging+G.m+G.m ≤ adj
    omega
  · intro i hi
    have hi' : i < G.m := by simpa [indexedGraph] using hi
    exact (hframe _ (by omega)).trans (by simpa using ht i hi')
  · intro i hi
    have hi' : i < G.m := by simpa [indexedGraph] using hi
    exact (hframe _ (by omega)).trans (by simpa [Nat.add_assoc] using hh i hi')

end MinCostFlow.LastLevelProgram
