module

public import MinCostFlow.HierPaths.BuildProgInjectFinish

/-!
# Final injection after the certified game

The last pass packs the saved certificates, routes their complements
together, and applies the routed rows to the completed game graphs.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the parent graph and terminal addresses, saved table,
first terminal, child size and count, router bounds, free arena, active
tables, slot base and stride, reply pointers, and the walk length bound. -/
def buildInjectEndProc (fRoute fFinish : ℕ) : Stmt :=
  .seq (.call 15 fRoute [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8])
    (.seq (.assign 16 (.bin .add
      (.bin .add (.bin .add (.bin .add (.reg 8) (.reg 4))
        (.bin .add (.reg 5) (.reg 5))) (.const 1))
      (.bin .mul (.reg 5) (.reg 4))))
      (.seq (.call 17 fFinish [.reg 0,.reg 9,.reg 10,.reg 11,.reg 3,.reg 4,.reg 5,.reg 12,
        .reg 13,.reg 16,.reg 14,.reg 15])
        (.ret (.reg 17))))

theorem buildInjectEndProc_noRand (fRoute fFinish : ℕ) :
    (buildInjectEndProc fRoute fFinish).NoRand := by
  simp [buildInjectEndProc,Stmt.NoRand]

/-- Addresses and player bounds passed to the end of the game. -/
def injectEndArgs (D : ChoiceLoopData) (heap slot : ℕ) : List ℕ :=
  [D.addrs.host,D.addrs.verts,D.saved,D.first,D.base.childSize,D.count,D.base.Δ,D.base.L,heap,
    D.addrs.graphs,D.addrs.offsets,slot,D.geometry.slotWords,D.addrs.replies,D.base.pathBound]

/-- The fixed layout and space bounds needed by the final injection. -/
structure InjectEndFit (w : ℕ) (D : ChoiceLoopData) (heap slot : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
    (sts : ℕ → ChildState) : Prop where
  affine : ∀ i, D.childAddr i = slot+i*D.geometry.slotWords
  slots : slot+D.count*D.geometry.slotWords ≤ D.addrs.heap
  terms : D.first+D.count*D.base.childSize < 2^w
  sPos : 1 ≤ D.base.childSize
  xCard : D.base.verts.card = D.base.childSize * D.count
  bits : 4 < 2^w
  batch : injectReplyBase heap D.count D.base.childSize+D.base.childSize < 2^w
  route : injectReplyBase heap D.count D.base.childSize +
    (D.base.verts.card + 1) *
      routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
        (pairsWords pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) < 2^w
  walks : ∀ top,
    injectReplyBase heap D.count D.base.childSize + (routeResultWords (.matched Ms emb)).length ≤ top →
    top ≤ injectReplyBase heap D.count D.base.childSize +
      (D.base.verts.card + 1) *
        routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
          (pairsWords pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) →
    (D.injectionData sts Ms emb).cursor
      (top+4+Ms.flatten.length+D.base.pathBound+1+D.base.host.n) Ms.length < 2^w

/-- The full injection records all its newly appended rows and walks.
The game archive is framed except for the updated child graphs and tables. -/
def buildInjectEndContract (w : ℕ) (D : ChoiceLoopData) (heap slot : ℕ)
    (sts : ℕ → ChildState) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) : Contract :=
  let pairs := injPairs D.base.childSize D.count D.offset sts
  let B := buildInjectRouteContract w D.base.K D.base.route D.base.routeCost D.base.routeSpace
    D.base.host D.base.verts pairs D.base.childSize D.base.Δ D.base.L
  let F := buildInjectFinishContract w D sts Ms emb
  { pre := fun args mem => args = injectEndArgs D heap slot ∧ ChoiceGameMemory D heap sts mem ∧
      InjectInput w mem D.saved heap D.first D.base.childSize pairs ∧
      (∀ i < pairs.length, (buildBatchRow pairs i).length = D.base.childSize) ∧
      InjectEndFit w D heap slot pairs Ms emb sts
    post := fun _ mem v after => ∃ top mid,
      injectReplyBase heap D.count D.base.childSize + (routeResultWords (.matched Ms emb)).length ≤ top ∧
      top ≤ injectReplyBase heap D.count D.base.childSize +
        (D.base.verts.card + 1) *
          routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
            (pairsWords pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) ∧
      B.post [D.addrs.host,D.addrs.verts,D.saved,D.first,D.base.childSize,D.count,D.base.Δ,D.base.L,heap]
        mem top mid ∧
      F.post (injectFinishArgs D slot (injectReplyBase heap D.count D.base.childSize) top)
        mid v after
    cost := fun args mem => B.cost args mem + F.cost args mem + 120 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- A finished trace and its routed row certificates suffice for the
combined final injection. -/
theorem buildInjectEndProc_meetsContract {w f fRoute fFinish : ℕ} {p : Program}
    {D : ChoiceLoopData} {β : ℝ} {bh heap slot runEnd : ℕ}
    {initial last : ℕ → ℕ} {sts : ℕ → ChildState} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts last) (h : ChoiceGameHyp D β bh)
    (hL : GameFixedLayout w D.geometry)
    (hf : p.procs[f]? = some (buildInjectEndProc fRoute fFinish))
    (hRoute : MeetsContract w p fRoute (buildInjectRouteContract w D.base.K D.base.route
      D.base.routeCost D.base.routeSpace D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.childSize D.base.Δ D.base.L))
    (hFinish : MeetsContract w p fFinish (buildInjectFinishContract w D sts Ms emb))
    (hRes : lemma1Route D.base.route D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L = (.matched Ms emb,runEnd))
    (hB : runEnd ≤ bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L runEnd 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card) :
    MeetsContract w p f (buildInjectEndContract w D heap slot sts Ms emb) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨rfl,hMem,hInput,hSizes,hFit⟩ := hPre
  let pairs := injPairs D.base.childSize D.count D.offset sts
  let g := D.addrs.host
  let x := D.addrs.verts
  let s := D.base.childSize
  let k := D.count
  let rep := injectReplyBase heap k s
  let result := routeResultWords (.matched Ms emb)
  have hPairs : pairs.length = k := by simp [pairs,injPairs,k]
  have hRes' : (lemma1Route D.base.route D.base.host D.base.verts pairs D.base.Δ D.base.L).1 =
      .matched Ms emb := congrArg Prod.fst hRes
  have hDir : D.directory+D.limit ≤ D.saved := hL.directory
  have hSaved : D.saved+D.count ≤ D.addrs.graphs := hL.saved
  have hGraphs : D.addrs.graphs+D.count ≤ D.addrs.offsets := hL.graphs
  have hOff : D.addrs.offsets+D.count ≤ D.addrs.replies := hL.offsets
  have hReply : D.addrs.replies+D.count ≤ heap := by
    have hr : D.addrs.replies+D.count+1 ≤ D.addrs.heap := hL.replies
    have hm : D.addrs.heap ≤ heap := hMem.heap
    omega
  have hPHost : g + D.base.host.encode.length ≤ D.directory := hL.host
  have hPVerts : x + (finsetWords D.base.verts).length ≤ D.directory := hL.verts
  have hGHeap : g+D.base.host.encode.length ≤ heap := by omega
  have hXHeap : x+(finsetWords D.base.verts).length ≤ heap := by omega
  have hSHeap : D.saved+k ≤ heap := by dsimp [k]; omega
  have hh : heap ≤ rep := by unfold rep injectReplyBase buildBatchEnd; omega
  have hOne : 1 < 2^w := by have := hFit.bits; omega
  have hRepW : rep < 2^w := (Nat.le_add_right ..).trans_lt hFit.batch
  have hBase : heap+s+(k+k)+1+k*s < 2^w := by
    have he : heap+s+(k+k)+1+k*s = rep := by unfold rep injectReplyBase buildBatchEnd; omega
    rw [he]
    exact hRepW
  have h2k : k+k < 2^w := by omega
  have hHeapS : heap+s < 2^w := by omega
  have hHeapK : heap+s+(k+k) < 2^w := by omega
  have hHeapK1 : heap+s+(k+k)+1 < 2^w := by omega
  have hProd : k*s < 2^w := by omega
  refine runs_start_le ?_
  unfold buildInjectEndProc
  refine runs_seq_call_le hRoute
    (vs := [g,x,D.saved,D.first,s,k,D.base.Δ,D.base.L,heap]) ?_ ?_ ?_ ?_
  · simp [evalArgs,Expr.eval,startState,injectEndArgs,g,x,s,k]
  · intro a ha
    exact hWords a (by simp [injectEndArgs,g,x,s,k] at ha ⊢; tauto)
  · exact ⟨g,x,D.saved,D.first,heap,by rw [hPairs],hFit.sPos,by rw [hPairs]; exact hFit.xCard,
      hMem.host,h.valid,hMem.verts,hGHeap,hXHeap,by rw [hPairs]; exact hSHeap,hMem.zero,hFit.bits,
      by rw [hPairs]; exact hFit.batch,by rw [hPairs]; exact hFit.route,hInput,hSizes,
      hTrace.injectRouterPre h⟩
  intro u mid pos₁ hPost
  have hRoutePost := hPost
  obtain ⟨g₁,x₁,saved₁,first₁,heap₁,he,hMemHeap,hResult,huLo,huBound,hFrame,hZero⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  have hhEq : heap = heap₁ := he.2.2.2.2.2.2
  subst heap₁
  change ListAt mid (injectReplyBase heap pairs.length s)
    (routeResultWords (lemma1Route D.base.route D.base.host D.base.verts pairs D.base.Δ D.base.L).1) at hResult
  change injectReplyBase heap pairs.length s +
    (routeResultWords (lemma1Route D.base.route D.base.host D.base.verts pairs D.base.Δ D.base.L).1).length ≤ u at huLo
  rw [hPairs,hRes'] at hResult huLo
  change u ≤ injectReplyBase heap pairs.length s +
    (D.base.verts.card + 1) *
      routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
        (pairsWords pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) at huBound
  rw [hPairs] at huBound
  change ∀ a < heap, mid a = mem a at hFrame
  change rep + result.length ≤ u at huLo
  refine runs_seq_assign_le (v := rep) ?_ ?_
  · simp [Expr.eval,startState,injectEndArgs,Function.update,hOne,h2k,hHeapS,hHeapK,
      hHeapK1,hProd,hBase,rep,injectReplyBase,buildBatchEnd,s,k,Nat.two_mul]
  have hHostMid := WordRAM.ListAt.congr hMem.host fun a _ ha => hFrame a (ha.trans_le hGHeap)
  have hChildMid (i : ℕ) (hi : i < k) : GraphAt mid (D.childAddr i) (gameGraph s (sts i)) := by
    obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
      h.denominator h.children h.even (coreLevel_le h.coreSize)
    have hLen := (gameGraph_bounds_of_inv (hInv i hi)).2.2.1
    have hSpan : (gameGraph s (sts i)).encode.length ≤ D.geometry.slotWords :=
      hLen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ D.limit)) _)
    have hSlot := (hL.slots i hi).2
    change D.childAddr i+D.geometry.slotWords ≤ D.addrs.replies at hSlot
    exact WordRAM.ListAt.congr (hMem.children i hi) fun a _ ha =>
      hFrame a (ha.trans_le ((Nat.add_le_add_left hSpan _).trans hSlot) |>.trans_le (Nat.le_of_add_right_le hReply))
  have hHeap : D.addrs.heap ≤ rep := hMem.heap.trans hh
  have hWalksU := hFit.walks u huLo huBound
  have hFinishPre := hTrace.injectFinishFit h hL hB hMatch hFull hFit.affine hFit.slots hFit.terms
    hResult huLo hZero hHeap hHostMid hChildMid hWalksU
  have hTopW : u < 2^w := huBound.trans_lt hFit.route
  refine runs_seq_call_le hFinish (vs := injectFinishArgs D slot rep u)
    ?_ ?_ hFinishPre ?_
  · simp [evalArgs,Expr.eval,startState,injectEndArgs,injectFinishArgs,Function.update]
  · intro a ha
    simp only [injectFinishArgs,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact hRepW | exact hTopW | apply hWords; simp [injectEndArgs]
  intro v after pos₂ hFinal
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp))
    ⟨u,mid,huLo,huBound,hRoutePost,hFinal⟩ ?_
  simp [buildInjectEndContract,buildInjectRouteContract,buildInjectFinishContract,buildInjectionContract,
    buildFullRouteContract,buildFinishBatchContract,Expr.size,argsSize]
  omega

end MinCostFlow.HierPaths
