module

public import MinCostFlow.HierPaths.BuildProgConnRequest
public import MinCostFlow.HierPaths.BuildProgFullRoute

/-!
# Routing a sibling pair

A single full-routing call consumes the two packed child intervals.
The reply retains both its matching endpoints and its raw walks, and returns a bumped heap cursor.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments give the parent graph and terminal list, the two child starts,
the common size, the router degree and size bounds, the free arena, and `X.card`. -/
def buildConnRouteProc (fRequest fFull : ℕ) : Stmt :=
  .seq (.call 9 fRequest [.reg 2,.reg 3,.reg 4,.reg 7])
    (.seq (.call 10 fFull [.reg 0,.reg 1,.reg 7,.reg 5,.reg 6,.const 2,.reg 8,.const 1,.reg 9,.reg 9])
      (.ret (.reg 10)))

theorem buildConnRouteProc_noRand (fRequest fFull : ℕ) :
    (buildConnRouteProc fRequest fFull).NoRand := by
  simp [buildConnRouteProc,Stmt.NoRand]

/-- Inputs are preserved, the reply is at the end of the request block, and the returned
bump cursor satisfies `ZeroFrom after v`. -/
def buildConnRouteContract (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) (a b s Δ L : ℕ) : Contract :=
  let pairs := connRequestPairs a b s
  { pre := fun args mem => ∃ g x h, args = [g,x,a,b,s,Δ,L,h,X.card] ∧
      GraphAt mem g G ∧ G.IsValid ∧ ListAt mem x (finsetWords X) ∧
      g+G.encode.length ≤ h ∧ x+(finsetWords X).length ≤ h ∧
      a+s < 2^w ∧ b+s < 2^w ∧ 4 < 2^w ∧ ZeroFrom mem h ∧
      h+3+2*s+(X.card+1)*routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 X.card) < 2^w ∧
      RouterPre G X pairs Δ L
    post := fun args mem v after => ∃ g x h, args = [g,x,a,b,s,Δ,L,h,X.card] ∧
      ListAt after (h+3+2*s) (routeResultWords (lemma1Route route G X pairs Δ L).1) ∧
      h+3+2*s+(routeResultWords (lemma1Route route G X pairs Δ L).1).length ≤ v ∧
      v ≤ h+3+2*s+(X.card+1)*routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 X.card) ∧
      (∀ j < h, after j = mem j) ∧ ZeroFrom after v
    cost := fun args mem => 48*s+64 +
      (buildFullRouteContract w K route routeCost sR G X pairs Δ L X.card 2).cost args mem + 40 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The sibling request and full router compose without changing earlier cells. -/
theorem buildConnRouteProc_meetsContract {w K a b s Δ L f fRequest fFull fRouter fCopy : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {G : Graph} {X : Finset ℕ}
    {p : Program} {β : ℝ} (hf : p.procs[f]? = some (buildConnRouteProc fRequest fFull))
    (hReq : p.procs[fRequest]? = some buildConnRequestProc)
    (hFull : p.procs[fFull]? = some (buildFullRouteProc fRouter fCopy fFull))
    (hRouter : ProvidesRouter w K route routeCost sR p fRouter)
    (hCopy : p.procs[fCopy]? = some buildCopyProc) (hPlayer : IsMatchingPlayer route routeCost)
    (hExp : G.IsExpansionExpanderOn X β) (hβ : 0 < β) (hWord : X.card < 2^w) :
    MeetsContract w p f (buildConnRouteContract w K route routeCost sR G X a b s Δ L) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g,x,h,rfl,hG,hGval,hX,hGe,hXe,ha,hb,hw4,hZ,hRoom,hRouterPre⟩ := hPre
  let reply := h+3+2*s
  let pairs := connRequestPairs a b s
  have hRep : reply < 2^w := lt_of_le_of_lt (Nat.le_add_right ..) hRoom
  have hh : h ≤ reply := by dsimp [reply]; omega
  have hOne : 1 < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hSingleRoom : reply + sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) < 2^w := by
    have h0 : sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) ≤
        routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      le_routerSpaceUpTo (by omega)
    have h1 : 1 * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) ≤
        (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp [reply, pairs] at h0 h1 hRoom ⊢; omega
  have hFuel : X.card < 2^(X.card+1)*2 := by
    have hh := Nat.lt_two_pow_self (n := X.card)
    rw [Nat.pow_succ]
    omega
  have hPairWords : h+(pairsWords pairs).length = reply := by
    unfold pairs
    rw [connRequestPairs_words]
    simp [length_tabList,reply]
    omega
  have hRun := buildFullRouteProc_meetsContract (pairs := pairs) (Δ := Δ) (L := L)
    hFull hRouter hCopy hPlayer hβ hExp hWord X.card 2 hFuel
  refine runs_start_le ?_
  unfold buildConnRouteProc
  refine runs_seq_call_le (buildConnRequestProc_meetsContract hReq) (vs := [a,b,s,h]) ?_ ?_
    ⟨a,b,s,h,rfl,ha,hb,hRep⟩ ?_
  · simp [evalArgs,Expr.eval,startState]
  · intro y hy
    exact hWords y (by simp at hy ⊢; tauto)
  intro u mid pos₁ hPost
  obtain ⟨_,_,_,_,he,hu,hPairs,hFrame⟩ := hPost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  change u = reply at hu
  subst u
  have hZ₁ : ZeroFrom mid reply := fun j hj =>
    (hFrame j (Or.inr hj)).trans (hZ j (hh.trans hj))
  refine runs_seq_call_le hRun (vs := [g,x,h,Δ,L,2,X.card,1,reply,reply]) ?_ ?_
    ⟨g,x,h,reply,reply,rfl,le_rfl,by omega,hRoom,
      ⟨⟨g,x,h,Δ,L,2,0,reply,rfl,
        WordRAM.ListAt.congr hG (fun j _ hj => hFrame j (Or.inl (hj.trans_le hGe))), hGval,
        WordRAM.ListAt.congr hX (fun j _ hj => hFrame j (Or.inl (hj.trans_le hXe))),
        hPairs,hGe.trans hh,hXe.trans hh,hPairWords.le,hRouterPre,le_rfl⟩,hZ₁,hSingleRoom⟩⟩ ?_
  · simp [evalArgs,Expr.eval,startState,Function.update,hOne,hTwo]
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact hRep | exact hOne | exact hTwo | exact hWord | apply hWords; simp
  intro v after pos₂ hPost
  obtain ⟨_,_,_,_,_,he,hLo,hLe,hKeep,hZ₂,hResult⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,_,rfl,rfl⟩ := he
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · exact ⟨g,x,h,rfl,hResult,hLo,hLe,
      fun j hj => (hKeep j (hj.trans_le hh)).trans (hFrame j (Or.inl hj)),hZ₂⟩
  · simp [buildConnRouteContract,buildConnRequestContract,buildFullRouteContract,pairs,Expr.size,argsSize]
    omega

end MinCostFlow.HierPaths
