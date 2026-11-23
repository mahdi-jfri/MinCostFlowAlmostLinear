module

public import MinCostFlow.HierPaths.BuildProgConnRoute
public import MinCostFlow.HierPaths.BuildProgConnErase
import MinCostFlow.HierPaths.BuildProgGameSlots

/-!
# Complete connector block for a sibling pair

Route the child intervals, shorten the returned paths, and write the
CSR row of connector records above the router's bumped cursor. Each step leaves
the parent input intact and stores the row address at the first workspace word.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The caller passes the parent graph and terminals, the two child starts
and size, the router bounds, heap, raw walk length bound, and `X.card`. -/
def buildConnOneProc (fRoute fErase fGather : ℕ) : Stmt :=
  .call 10 fRoute [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 9] ;;
  .assign 11 (.bin .add (.bin .add (.reg 7) (.const 3)) (.bin .add (.reg 4) (.reg 4))) ;;
  .call 12 fErase [.reg 11,.reg 10,.bin .add (.reg 0) (.const 2),.load (.reg 0),.reg 8,.reg 4] ;;
  .call 13 fGather [.reg 10,.reg 4,.reg 12] ;;
  .store (.reg 7) (.reg 12) ;;
  .ret (.reg 13)

theorem buildConnOneProc_noRand (fRoute fErase fGather : ℕ) :
    (buildConnOneProc fRoute fErase fGather).NoRand := by
  simp [buildConnOneProc,Stmt.NoRand]

/-- Connector records for the raw matching, in the order of its endpoints. -/
def connectorRows (G : Graph) (M : List (ℕ × ℕ)) (emb : ℕ → List ℕ) : ℕ → List ℕ :=
  buildConnectorRowWords (edgeAt M) (fun i => erase G.edges (edgeAt M i).1 (emb i))

/-- The compact connector block follows the bumped workspace. The caller receives
its address through the first free word of the workspace. -/
def buildConnOneContract (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) (a b Δ L d : ℕ)
    (M : List (ℕ × ℕ)) (emb : ℕ → List ℕ) : Contract :=
  let s := M.length
  let pairs := connRequestPairs a b s
  let R := buildConnRouteContract w K route routeCost sR G X a b s Δ L
  { pre := fun args mem => ∃ g x h,
      args = [g,x,a,b,s,Δ,L,h,d,X.card] ∧ R.pre [g,x,a,b,s,Δ,L,h,X.card] mem ∧
      4 < 2^w ∧ G.n < 2^w ∧
      let rep := h+3+2*s
      ∀ top, rep+(routeResultWords (.matched [M] emb)).length ≤ top →
        top ≤ rep+(X.card+1)*routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
          (Δ + L + max 2 X.card) →
        (connectorWalkRow M emb).cursor (top+2+s+d+1+G.n) s +
          (csrList s (connectorRows G M emb)).length < 2^w
    post := fun args mem v after => ∃ g x h top out,
      args = [g,x,a,b,s,Δ,L,h,d,X.card] ∧
      h+3+2*s+(routeResultWords (.matched [M] emb)).length ≤ top ∧
      top ≤ h+3+2*s+(X.card+1)*routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 X.card) ∧
      out = (connectorWalkRow M emb).cursor (top+2+s+d+1+G.n) s ∧
      h < out ∧ after h = out ∧ ListAt after out (csrList s (connectorRows G M emb)) ∧
      v = out+(csrList s (connectorRows G M emb)).length ∧
      (∀ j < h, after j = mem j) ∧ ZeroFrom after v
    cost := fun args mem => R.cost args mem +
      (buildConnEraseContract w G M emb d).cost args mem +
      (rangeCost (fun i => 17*(erase G.edges (edgeAt M i).1 (emb i)).length+100) 0 s +
        30*s+40) + 140 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The routed pair, shortened paths and connector CSR writer compose in
one bounded run and preserve the original parent memory. -/
theorem buildConnOneProc_meetsContract {w K a b Δ L d f fRoute fErase fGather denom : ℕ}
    {p : Program} {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {X : Finset ℕ} {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ}
    (hf : p.procs[f]? = some (buildConnOneProc fRoute fErase fGather))
    (hr : MeetsContract w p fRoute (buildConnRouteContract w K route routeCost sR G X a b M.length Δ L))
    (he : MeetsContract w p fErase (buildConnEraseContract w G M emb d))
    (hg : ∀ ctx n, MeetsContract w p fGather
      (initCSRWriteContract w ctx M.length (connectorRows G M emb)
       (fun i => 17*(erase G.edges (edgeAt M i).1 (emb i)).length+100)
       (fun dst mem => n ≤ dst ∧ ConnectorRowsAt ctx M.length (edgeAt M)
         (fun i => erase G.edges (edgeAt M i).1 (emb i)) n mem) 0))
    (hValid : G.IsValid)
    (hMatch : RouteMatchedSpec G X (connRequestPairs a b M.length) Δ L denom 0 [M] emb)
    (hRes : (lemma1Route route G X (connRequestPairs a b M.length) Δ L).1 = .matched [M] emb)
    (hPath : routePathLen Δ denom L ≤ d) :
    MeetsContract w p f (buildConnOneContract w K route routeCost sR G X a b Δ L d M emb) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g,x,h,rfl,hRoute,hBits,hN,hRoomAll⟩ := hPre
  let s := M.length
  let R := connectorWalkRow M emb
  let rep := h+3+2*s
  let row := connectorRows G M emb
  let sec := csrList s row
  have hThree : 3 < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hOne : 1 < 2^w := by omega
  refine runs_start_le ?_
  unfold buildConnOneProc
  refine runs_seq_call_le hr (vs := [g,x,a,b,s,Δ,L,h,X.card]) ?_ ?_ hRoute ?_
  · simp [evalArgs,Expr.eval,startState,s]
  · intro y hy
    exact hWords y (by simp [s] at hy ⊢; tauto)
  intro top mid pos₁ hPost
  obtain ⟨_,_,_,hArg,hAt,hTopLo,hTopHi,hFrame,hZ⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at hArg
  obtain ⟨rfl,rfl,_,rfl⟩ := hArg
  rw [hRes] at hAt hTopLo
  have hRoom : R.cursor (top+2+s+d+1+G.n) s + sec.length < 2^w := hRoomAll top hTopLo hTopHi
  let work := top+2+s+d+1+G.n
  let last := R.cursor work s
  have hLeTop : h ≤ top := by omega
  have hLeWork : top ≤ work := by dsimp [work]; omega
  have hLeLast : work ≤ last := R.cursor_mono work (Nat.zero_le s)
  have hTopW : top < 2^w := (hLeWork.trans hLeLast).trans_lt (lt_of_le_of_lt (Nat.le_add_right ..) hRoom)
  have hRepW : rep < 2^w := (Nat.le_trans (Nat.le_add_right ..) hTopLo).trans_lt hTopW
  have hH3 : h+3 < 2^w := by dsimp [rep] at hRepW; omega
  have hS2 : s+s < 2^w := by dsimp [rep] at hRepW; omega
  have hResult : h+3+(s+s) < 2^w := by dsimp [rep] at hRepW; omega
  have hIdx : g+2 < 2^w := by
    obtain ⟨_,_,_,eq,_,_,_,hGe,_⟩ := hRoute
    simp only [List.cons.injEq,and_true,true_and] at eq
    obtain ⟨rfl,rfl,_,rfl⟩ := eq
    rw [buildGraph_encode_length] at hGe
    omega
  refine runs_seq_assign_le (v := rep) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hThree,hH3,hS2,hResult,rep,s,Nat.two_mul]
  obtain ⟨_,_,_,eq,hGraph,_,_,hGraphEnd,_,_,_,_,_,_,hRouter⟩ := hRoute
  simp only [List.cons.injEq,and_true,true_and] at eq
  obtain ⟨rfl,rfl,_,rfl⟩ := eq
  have hGmid : GraphAt mid g G := WordRAM.ListAt.congr hGraph fun j _ hj => hFrame j (hj.trans_le hGraphEnd)
  have hMs : mid g = G.n := by
    have hz := hGmid 0 (by rw [buildGraph_encode_length]; omega)
    simpa [Graph.encode] using hz
  have hEnds : ListAt mid (g+2) (G.edges.flatMap fun e => [e.1,e.2]) := by
    change ListAt mid g ([G.n,G.m]++_) at hGmid
    exact (listAt_append.mp hGmid).2
  have hEndsLe : g+2+2*G.m ≤ top := by
    rw [buildGraph_encode_length] at hGraphEnd
    omega
  have hPreErase := buildConnErase_pre_of_matched hValid hRouter.1 hRouter.2.2.2.2.2.2
    hMatch hPath hAt hTopLo hEnds hEndsLe hZ hBits (lt_of_le_of_lt (Nat.le_add_right ..) hRoom)
  refine runs_seq_call_le he (vs := [rep,top,g+2,G.n,d,s]) ?_ ?_ hPreErase ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,hMs,hTwo,hIdx,s]
  · have hD := hWords d (by simp)
    wram_words
  intro out clean pos₂ hPost
  obtain ⟨_,_,_,eq,hOut,hRows,hKeep,_,hZero⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at eq
  obtain ⟨rfl,rfl,_,_⟩ := eq
  change out = last at hOut
  have hComplete : out + sec.length < 2^w := hOut.symm ▸ hRoom
  have ho : out < 2^w := (Nat.le_add_right ..).trans_lt hComplete
  refine runs_seq_call_le (hg top out) (vs := [top,s,out]) ?_ ?_
    ⟨out,rfl,⟨le_rfl,hRows⟩,hZero,by simpa [sec,row] using hComplete,hOne⟩ ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,s]
  · wram_words
  intro v after pos₃ hPost
  obtain ⟨out₂,eq,ht,hAt,hZ',hBelow⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at eq
  have hOutEq : out = out₂ := eq.2
  subst out₂
  refine runs_seq_store_le (x := h) (v := out) (Expr.eval_reg_of_eq (by simp [startState]))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let final := Function.update after h out
    have hHOut : h < out := by have hh : top+2 ≤ out := hRows.1; omega
    have hv : out ≤ v := by omega
    refine ⟨g,x,h,top,out,rfl,hTopLo,hTopHi,hOut,hHOut,by simp [final],?_,ht,?_,?_⟩
    · exact WordRAM.ListAt.congr hAt fun j hj _ => Function.update_of_ne (by omega) _ _
    · intro j hj
      exact (Function.update_of_ne (by omega) _ _).trans
        ((hBelow j (by omega)).trans ((hKeep j (by omega)).trans (hFrame j hj)))
    · intro j hj
      change v ≤ j at hj
      exact (Function.update_of_ne (by omega) _ _).trans (hZ' j hj)
  · simp [buildConnOneContract,buildConnRouteContract,buildConnEraseContract,
      initCSRWriteContract,buildWalkRowContract,buildFullRouteContract,Expr.size,argsSize,s]
    omega

end MinCostFlow.HierPaths
