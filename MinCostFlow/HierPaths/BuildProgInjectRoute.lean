module

public import MinCostFlow.HierPaths.BuildProgInjectBatch
public import MinCostFlow.HierPaths.BuildProgFullRoute

/-!
# Routing the final injection

Allocate a reusable mask and the pair table above the game archive.
The full router writes the complete reply at `reply` and returns the bumped
arena top `v`, which is also recorded at `mem[heap]` so downstream walk and
hole collectors can locate `walkDir = mem[heap] + 4`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are host, terminals, saved pointers, first terminal, child
size, number of children, degree bound, size bound, and free arena base. -/
def buildInjectRouteProc (fBatch fFull : ℕ) : Stmt :=
  .seq (.assign 9 (.bin .add (.reg 8) (.reg 4)))
    (.seq (.call 10 fBatch [.reg 2,.reg 8,.reg 5,.reg 4,.reg 9,.reg 3])
      (.seq (.call 11 fFull [.reg 0,.reg 1,.reg 9,.reg 6,.reg 7,.const 2,
        .bin .mul (.reg 4) (.reg 5),.reg 5,.reg 10,.reg 10])
        (.seq (.store (.reg 8) (.reg 11))
          (.ret (.reg 11)))))

theorem buildInjectRouteProc_noRand (fBatch fFull : ℕ) :
    (buildInjectRouteProc fBatch fFull).NoRand := by
  simp [buildInjectRouteProc,Stmt.NoRand]

/-- Arena address of the reply after the mask and the packed input. -/
def injectReplyBase (heap k s : ℕ) : ℕ := buildBatchEnd (heap+s) k s

/-- The final routing call leaves the game archive and returns the bumped arena end
of the full batch reply, storing that end at `mem'[heap]`. -/
def buildInjectRouteContract (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (s Δ L : ℕ) : Contract where
  pre args mem := ∃ g x saved first heap,
    args = [g,x,saved,first,s,pairs.length,Δ,L,heap] ∧
    1 ≤ s ∧ X.card = s * pairs.length ∧
    GraphAt mem g G ∧ G.IsValid ∧ ListAt mem x (finsetWords X) ∧
    g+G.encode.length ≤ heap ∧ x+(finsetWords X).length ≤ heap ∧ saved+pairs.length ≤ heap ∧
    ZeroFrom mem heap ∧ 4 < 2^w ∧
    injectReplyBase heap pairs.length s + s < 2^w ∧
    injectReplyBase heap pairs.length s +
      (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 X.card) < 2^w ∧
    InjectInput w mem saved heap first s pairs ∧
    (∀ i < pairs.length, (buildBatchRow pairs i).length = s) ∧ RouterPre G X pairs Δ L
  post args mem v mem' := ∃ g x saved first heap,
    args = [g,x,saved,first,s,pairs.length,Δ,L,heap] ∧
    let reply := injectReplyBase heap pairs.length s
    mem' heap = v ∧
    ListAt mem' reply (routeResultWords (lemma1Route route G X pairs Δ L).1) ∧
    reply + (routeResultWords (lemma1Route route G X pairs Δ L).1).length ≤ v ∧
    v ≤ reply + (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
      (Δ + L + max 2 X.card) ∧
    (∀ a < heap, mem' a = mem a) ∧ ZeroFrom mem' v
  cost args mem := (buildInjectionContract w s pairs).cost args mem +
    (buildFullRouteContract w K route routeCost sR G X pairs Δ L X.card 2).cost args mem + 70

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Pack the finished children's requests, then make one full routing call. -/
theorem buildInjectRouteProc_meetsContract {w K s Δ L f fBatch fSides fMask fPack fFull fRoute fCopy : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {p : Program} {β : ℝ}
    (hf : p.procs[f]? = some (buildInjectRouteProc fBatch fFull))
    (hb : p.procs[fBatch]? = some (buildInjectionProc fSides))
    (hs : p.procs[fSides]? = some (buildInjectSidesProc fMask fPack))
    (hm : p.procs[fMask]? = some buildCutMaskProc) (hp : p.procs[fPack]? = some buildCutPackProc)
    (hfull : p.procs[fFull]? = some (buildFullRouteProc fRoute fCopy fFull))
    (hr : ProvidesRouter w K route routeCost sR p fRoute) (hcopy : p.procs[fCopy]? = some buildCopyProc)
    (hPlayer : IsMatchingPlayer route routeCost) (hβ : 0 < β)
    (hExp : G.IsExpansionExpanderOn X β) (hWord : X.card < 2^w) :
    MeetsContract w p f (buildInjectRouteContract w K route routeCost sR G X pairs s Δ L) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g,x,saved,first,heap,rfl,hs1,hXcard,hG,hGval,hX,hGend,hXend,hSaved,hZero,hw,hEnd,hRoom,
    hIn,hSizes,hRouter⟩ := hPre
  let out := heap+s
  let reply := injectReplyBase heap pairs.length s
  have hOut : out < 2^w := by
    change buildBatchEnd out pairs.length s+s < 2^w at hEnd; unfold buildBatchEnd at hEnd; omega
  have hReply : reply < 2^w := lt_of_le_of_lt (Nat.le_add_right ..) hEnd
  have hTwo : 2 < 2^w := by omega
  have hSingleRoom : reply + sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) < 2^w := by
    have h0 : sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) ≤
        routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      le_routerSpaceUpTo (by omega)
    have h1 : 1 * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) ≤
        (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp [reply] at h0 h1 hRoom ⊢; omega
  have hFirstWord := hWords first (by simp)
  have hDWord := hWords Δ (by simp)
  have hLWord := hWords L (by simp)
  have hFuel : X.card < 2^(X.card+1)*2 := by
    have hh := Nat.lt_two_pow_self (n := X.card)
    rw [Nat.pow_succ]
    omega
  have hFull := buildFullRouteProc_meetsContract (pairs := pairs) (Δ := Δ) (L := L)
    hfull hr hcopy hPlayer hβ hExp hWord X.card 2 hFuel
  have hOutLe : out ≤ reply := by unfold reply injectReplyBase buildBatchEnd; omega
  have hHeapOut : heap ≤ out := Nat.le_add_right ..
  have hHeapLtRep : heap < reply := by unfold reply injectReplyBase buildBatchEnd; omega
  have hPairLen : out + (pairsWords pairs).length = reply := by
    rw [injectPairsWords_length hSizes]
    unfold reply injectReplyBase buildBatchEnd out
    omega
  refine runs_start_le ?_
  unfold buildInjectRouteProc
  refine runs_seq_assign_le (v := out) ?_ ?_
  · simp [Expr.eval,startState,out,hOut]
  refine runs_seq_call_le (buildInjectionProc_meetsContract hb hs hm hp)
    (vs := [saved,heap,pairs.length,s,out,first]) ?_ ?_
    ⟨saved,heap,first,out,rfl,hSaved,le_rfl,hEnd,hw,hIn,hSizes⟩ ?_
  · simp [evalArgs,Expr.eval,startState,Function.update]
  · wram_words
  intro v₁ mem₁ pos₁ hPost
  obtain ⟨_,_,_,_,he,hv,hP,hFrame⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  change v₁ = reply at hv
  subst v₁
  have hBelow : ∀ a < heap, mem₁ a = mem a :=
    fun a ha => hFrame a (Or.inl ha) (Or.inl (ha.trans_le hHeapOut))
  have hZ : ZeroFrom mem₁ reply :=
    fun a ha => (hFrame a (Or.inr (hOutLe.trans ha)) (Or.inr ha)).trans
      (hZero a ((hHeapOut.trans hOutLe).trans ha))
  refine runs_seq_call_le hFull (vs := [g,x,out,Δ,L,2,X.card,pairs.length,reply,reply]) ?_ ?_
    ⟨g,x,out,reply,reply,rfl,le_rfl,by omega,hRoom,⟨⟨g,x,out,Δ,L,2,0,reply,rfl,
      WordRAM.ListAt.congr hG (fun a _ ha => hBelow a (ha.trans_le hGend)), hGval,
      WordRAM.ListAt.congr hX (fun a _ ha => hBelow a (ha.trans_le hXend)),
      hP.pairsAt hSizes,hGend.trans (hHeapOut.trans hOutLe),hXend.trans (hHeapOut.trans hOutLe),
      hPairLen.le,hRouter,le_rfl⟩,hZ,hSingleRoom⟩⟩ ?_
  · simp [evalArgs,Expr.eval,startState,Function.update,hTwo,hXcard.symm,hWord]
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact hOut | exact hTwo | exact hWord | exact hReply | exact hWords _ (by simp)
  intro v mem₂ pos₂ hPost
  obtain ⟨_,_,_,_,_,he,hLo,hLe,hFrame₂,hZ₂,hResult⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  refine runs_seq_store_le (x := heap) (v := v)
    (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let mem₃ := Function.update mem₂ heap v
    refine ⟨g,x,saved,first,heap,rfl,Function.update_self ..,?_,hLo,hLe,?_,?_⟩
    · exact WordRAM.ListAt.congr hResult fun a ha _ => Function.update_of_ne (by omega) _ _
    · intro a ha
      exact (Function.update_of_ne (by omega) _ _).trans
        ((hFrame₂ a (ha.trans_le (hHeapOut.trans hOutLe))).trans (hBelow a ha))
    · intro a ha
      dsimp only [Outcome.value] at ha
      exact (Function.update_of_ne (by omega) _ _).trans (hZ₂ a ha)
  · simp [buildInjectRouteContract,buildInjectionContract,buildFullRouteContract,Expr.size,argsSize]
    omega

end MinCostFlow.HierPaths
