module

public import MinCostFlow.HierPaths.BuildProgInjectData
public import MinCostFlow.HierPaths.BuildProgInjectRoute
public import MinCostFlow.HierPaths.BuildProgInjectTables

/-!
# Applying the final injection

The adapter writes the original child order, then appends one matching
row to each child graph and retains the shortened walks in the arena.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments give the graph and its saved child tables, the reserved
slots, the matched reply, and its arena end. -/
def buildInjectFinishProc (fTables fFinish : ℕ) : Stmt :=
  .seq (.call 12 fTables [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8])
    (.seq (.call 13 fFinish [.reg 9,.reg 8,.reg 1,.reg 2,.bin .add (.reg 0) (.const 2),
      .load (.reg 0),.reg 10,.reg 11,.reg 6])
      (.ret (.reg 13)))

theorem buildInjectFinishProc_noRand (fTables fFinish : ℕ) :
    (buildInjectFinishProc fTables fFinish).NoRand := by
  simp [buildInjectFinishProc,Stmt.NoRand]

/-- Runtime addresses of the injection write-back. -/
def injectFinishArgs (D : ChoiceLoopData) (slot rep top : ℕ) : List ℕ :=
  [D.addrs.host,D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,
    D.geometry.slotWords,D.addrs.replies,rep,D.base.pathBound,top]

/-- The application adapter uses the same row postcondition as a game round. -/
def buildInjectFinishContract (w : ℕ) (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) : Contract where
  pre args mem := ∃ slot rep top, args = injectFinishArgs D slot rep top ∧
    (buildInjectTablesContract w).pre
      [D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,
        D.geometry.slotWords,D.addrs.replies] mem ∧
    D.addrs.host < D.addrs.graphs ∧ D.addrs.host < D.addrs.offsets ∧ D.addrs.host < D.addrs.replies ∧
    D.addrs.host+2 < 2^w ∧ mem D.addrs.host = D.base.host.n ∧ D.base.host.n < 2^w ∧
    Ms.length = D.count ∧
    (∀ mid, (buildInjectTablesContract w).post
      [D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,
        D.geometry.slotWords,D.addrs.replies] mem 0 mid →
      (buildFinishBatchContract w (D.injectionData sts Ms emb)).pre
        [rep,D.addrs.replies,D.addrs.graphs,D.addrs.offsets,D.addrs.host+2,D.base.host.n,
          D.base.pathBound,top,Ms.length] mid)
  post args mem v after := ∃ slot rep top mid,
    args = injectFinishArgs D slot rep top ∧
    (buildInjectTablesContract w).post
      [D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,
        D.geometry.slotWords,D.addrs.replies] mem 0 mid ∧
    (buildFinishBatchContract w (D.injectionData sts Ms emb)).post
      [rep,D.addrs.replies,D.addrs.graphs,D.addrs.offsets,D.addrs.host+2,D.base.host.n,
        D.base.pathBound,top,Ms.length] mid v after
  cost args mem := 60*D.count+16 +
    (buildFinishBatchContract w (D.injectionData sts Ms emb)).cost args mem + 90

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Restore the child tables and apply the full matching in bounded time. -/
theorem buildInjectFinishProc_meetsContract {w f fTables fFinish : ℕ} {p : Program}
    {D : ChoiceLoopData} {sts : ℕ → ChildState} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hf : p.procs[f]? = some (buildInjectFinishProc fTables fFinish))
    (ht : p.procs[fTables]? = some buildInjectTablesProc)
    (hFinish : MeetsContract w p fFinish (buildFinishBatchContract w (D.injectionData sts Ms emb))) :
    MeetsContract w p f (buildInjectFinishContract w D sts Ms emb) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨slot,rep,top,rfl,hPre,hAG,hAO,hAI,hAddr,hN,hWord,hCount,hFit⟩ := hPre
  let ta := [D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,
    D.geometry.slotWords,D.addrs.replies]
  have hTwo : 2 < 2^w := by omega
  have hA := hWords (D.addrs.host) (by simp [injectFinishArgs])
  have hG := hWords (D.addrs.graphs) (by simp [injectFinishArgs])
  have hO := hWords (D.addrs.offsets) (by simp [injectFinishArgs])
  have hI := hWords (D.addrs.replies) (by simp [injectFinishArgs])
  have hF := hWords D.first (by simp [injectFinishArgs])
  have hS := hWords D.base.childSize (by simp [injectFinishArgs])
  have hK := hWords D.count (by simp [injectFinishArgs])
  have hR := hWords rep (by simp [injectFinishArgs])
  have hT := hWords top (by simp [injectFinishArgs])
  have hP := hWords D.base.pathBound (by simp [injectFinishArgs])
  have hSpan := hWords D.geometry.slotWords (by simp [injectFinishArgs])
  have hSlot := hWords slot (by simp [injectFinishArgs])
  refine runs_start_le ?_
  unfold buildInjectFinishProc
  refine runs_seq_call_le (buildInjectTablesProc_meetsContract ht) (vs := ta) ?_ ?_ hPre ?_
  · simp [evalArgs,Expr.eval,startState,injectFinishArgs,ta]
  · intro a ha
    exact hWords a (by simp [injectFinishArgs,ta] at ha ⊢; tauto)
  intro u mid pos₁ hPost
  have hTables : (buildInjectTablesContract w).post ta mem 0 mid := hPost
  have hUnchanged : mid D.addrs.host = mem D.addrs.host := by
    obtain ⟨_,_,_,_,_,_,_,_,he,hFrame,_,_,_⟩ := hTables
    simp only [ta,List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    exact hFrame.2 _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hN' := hUnchanged.trans hN
  refine runs_seq_call_le hFinish
    (vs := [rep,D.addrs.replies,D.addrs.graphs,D.addrs.offsets,D.addrs.host+2,D.base.host.n,
      D.base.pathBound,top,Ms.length]) ?_ ?_ (hFit mid hTables) ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,injectFinishArgs,hTwo,hAddr,hN',hCount]
  · wram_words
  intro v after pos₂ hFinal
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp))
    ⟨slot,rep,top,mid,rfl,hTables,hFinal⟩ ?_
  simp [buildInjectFinishContract,buildInjectTablesContract,buildFinishBatchContract,
    ta,Expr.size,argsSize,ChoiceLoopData.injectionData]
  omega

/-- The injection preserves the original game graph words while rebuilding
the dense tables needed to append its matched rows. -/
theorem ChoiceLoopTrace.injectFinishFit {w b heap slot rep top : ℕ} {D : ChoiceLoopData}
    {β : ℝ} {bh : ℕ} {initial last mem : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts last) (h : ChoiceGameHyp D β bh)
    (hL : GameFixedLayout w D.geometry) (hb : b ≤ bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L b 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    (hAffine : ∀ i, D.childAddr i = slot+i*D.geometry.slotWords)
    (hSlotEnd : slot+D.count*D.geometry.slotWords ≤ D.addrs.heap)
    (hTerm : D.first+D.count*D.base.childSize < 2^w)
    (hReply : ListAt mem rep (routeResultWords (.matched Ms emb)))
    (hTop : rep + (routeResultWords (.matched Ms emb)).length ≤ top)
    (hZero : ZeroFrom mem top) (hRep : D.addrs.heap ≤ rep)
    (hHost : GraphAt mem D.addrs.host D.base.host)
    (hChildren : ∀ c < D.count, GraphAt mem (D.childAddr c) (gameGraph D.base.childSize (sts c)))
    (hWord : (D.injectionData sts Ms emb).cursor
      (top+4+Ms.flatten.length+D.base.pathBound+1+D.base.host.n) Ms.length < 2^w) :
    (buildInjectFinishContract w D sts Ms emb).pre (injectFinishArgs D slot rep top) mem := by
  have hLen : Ms.length = D.count := by simpa [injPairs] using hMatch.1
  have hIdx : D.addrs.replies+D.count ≤ D.addrs.heap := by
    have hr : D.addrs.replies+D.count+1 ≤ D.addrs.heap := hL.replies; omega
  have hG : D.addrs.graphs+D.count ≤ D.addrs.offsets := hL.graphs
  have hO : D.addrs.offsets+D.count ≤ D.addrs.replies := hL.offsets
  have hDir : D.directory+D.limit ≤ D.saved := hL.directory
  have hSaved : D.saved+D.count ≤ D.addrs.graphs := hL.saved
  have hH := hL.host
  change D.addrs.host+D.base.host.encode.length ≤ D.directory at hH
  rw [buildGraph_encode_length] at hH
  have hN : mem D.addrs.host = D.base.host.n := by
    have hz := hHost 0 (by rw [buildGraph_encode_length]; omega)
    simpa [Graph.encode] using hz
  have hRoom := ((D.injectionData sts Ms emb).cursor_mono
    (top+4+Ms.flatten.length+D.base.pathBound+1+D.base.host.n)
    (Nat.zero_le Ms.length)).trans_lt hWord
  change top+4+Ms.flatten.length+D.base.pathBound+1+D.base.host.n < 2^w at hRoom
  have hAbove : D.addrs.heap ≤ top := hRep.trans (Nat.le_trans (Nat.le_add_right ..) hTop)
  refine ⟨slot,rep,top,rfl,
    ⟨D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,D.geometry.slotWords,
      D.addrs.replies,rfl,hG,hO,by omega,by omega,hTerm,by omega⟩,
    by omega,by omega,by omega,by omega,hN,by omega,hLen,?_⟩
  intro mid hPost
  obtain ⟨_,_,_,_,_,_,_,_,he,hFrame,hGraphs,hOff,hIndices⟩ := hPost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
  have htG : ListAt mid D.addrs.graphs (tabList D.count D.childAddr) := by
    rw [show D.childAddr = (fun i => slot+i*D.geometry.slotWords) from funext hAffine]
    exact hGraphs
  have htO : ListAt mid D.addrs.offsets (tabList D.count D.offset) := hOff
  have hKeep (a : ℕ) (ha : a < D.addrs.graphs ∨
      D.addrs.offsets+D.count ≤ a ∧ a < D.addrs.replies ∨ D.addrs.replies+D.count ≤ a) :
      mid a = mem a := by
    rcases ha with ha | ⟨ha,hb⟩ | ha
    · exact hFrame.2 a (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))
    · exact hFrame.2 a (Or.inr (by omega)) (Or.inr ha) (Or.inl hb)
    · exact hFrame.2 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr ha)
  have hChildAt (c : ℕ) (hc : c < D.count) :
      GraphAt mid (D.childAddr c) (gameGraph D.base.childSize (sts c)) := by
    have hs := hL.slots c hc
    change D.addrs.offsets+D.count ≤ D.childAddr c ∧
      D.childAddr c+D.geometry.slotWords ≤ D.addrs.replies at hs
    obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
      h.denominator h.children h.even (coreLevel_le h.coreSize)
    have hLen := (gameGraph_bounds_of_inv (hInv c hc)).2.2.1
    have hn : (gameGraph D.base.childSize (sts c)).encode.length ≤ D.geometry.slotWords :=
      hLen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ D.limit)) _)
    exact WordRAM.ListAt.congr (hChildren c hc) fun a ha hb =>
      hKeep a (Or.inr (Or.inl ⟨hs.1.trans ha,hb.trans_le ((Nat.add_le_add_left hn _).trans hs.2)⟩))
  have hReply' := WordRAM.ListAt.congr hReply fun a ha _ => hKeep a (Or.inr (Or.inr (hIdx.trans (hRep.trans ha))))
  have hZero' : ZeroFrom mid top :=
    fun a ha => (hKeep a (Or.inr (Or.inr (hIdx.trans (hAbove.trans ha))))).trans (hZero a ha)
  have hEnds : ListAt mid (D.addrs.host+2) (D.base.host.edges.flatMap fun e => [e.1,e.2]) := by
    have hEnc : GraphAt mid D.addrs.host D.base.host := WordRAM.ListAt.congr hHost fun a _ ha => by
      rw [buildGraph_encode_length] at ha
      exact hKeep a (Or.inl (by omega))
    change ListAt mid D.addrs.host ([D.base.host.n,D.base.host.m] ++ _) at hEnc
    exact (listAt_append.mp hEnc).2
  exact hTrace.injectFinishPre h hL hb hMatch hFull hReply' hTop hZero' hIndices htG htO
    (hIdx.trans hRep) hEnds hChildAt hWord

end MinCostFlow.HierPaths
