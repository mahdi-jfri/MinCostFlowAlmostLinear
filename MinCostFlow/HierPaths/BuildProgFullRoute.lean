module

public import MinCostFlow.HierPaths.BuildProgTags
public import MinCostFlow.HierPaths.BuildProgCopy
import MinCostFlow.HierPaths.InitLayout

/-!
# Full routing in the static builder

The procedure tries the router with zero deficit. Under the bump router contract, a cut reply is
left in place and the next attempt allocates from the returned bump cursor `v` without zeroing
router scratch. When the final attempt matches at `h ≥ dst`, the matched block is copied down once
to `dst` using `buildCopyProc`, returning the final bump cursor `v`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Args are `[gAddr, xAddr, pAddr, Δ, L, b, xLen, pCount, dst, h]` with `dst ≤ h`.
Calls `fRoute` at `h`; on a cut, recurses from the bumped cursor `v` with `2 * b`;
on a match, copies `[h, h + len)` down to `dst` if `dst < h` and returns `v`. -/
def buildFullRouteProc (fRoute fCopy self : ℕ) : Stmt :=
  .seq (.call 10 fRoute
      [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .const 0, .reg 6, .reg 7, .reg 9])
    (.seq (.cond (.load (.bin .add (.reg 9) (.const 4)))
      (.seq (.call 10 self
        [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.reg 5),
          .reg 6, .reg 7, .reg 8, .reg 10])
        (.ret (.reg 10)))
      (.seq (.cond (.bin .lt (.reg 8) (.reg 9))
        (.call 11 fCopy
          [.reg 9, .bin .add (.load (.bin .add (.reg 9) (.const 3))) (.const 4), .reg 8])
        .nop)
        (.ret (.reg 10)))) .nop)

theorem buildFullRouteProc_noRand (fRoute fCopy self : ℕ) :
    (buildFullRouteProc fRoute fCopy self).NoRand := by
  simp [buildFullRouteProc, Stmt.NoRand]

/-- Cost of each router call and its wrapper. Retries bump without zeroing; the single final
matched reply is copied down to `dst` once. -/
def buildFullRouteCost (callCost : ℕ → ℕ) (outcome : ℕ → RouteResult) : ℕ → ℕ → ℕ
  | 0, b => callCost b + 17 * (routeResultWords (outcome b)).length + 70
  | n + 1, b =>
    match outcome b with
    | .matched Ms emb => callCost b + 17 * (routeResultWords (.matched Ms emb)).length + 70
    | .cut _ => callCost b + 40 + buildFullRouteCost callCost outcome n (2 * b)

/-- The wrapper for one full-routing request. The starting denominator and the induction
bound select the model run. Neither is built into the procedure body. -/
def buildFullRouteContract (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L n b : ℕ) : Contract where
  pre args mem := ∃ gAddr xAddr pAddr dst h,
    args = [gAddr, xAddr, pAddr, Δ, L, b, X.card, pairs.length, dst, h] ∧
    dst ≤ h ∧ 3 < 2 ^ w ∧
    h + (n + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
      (Δ + L + max b X.card) < 2 ^ w ∧
    (RouterProcContract w K route routeCost sR G X pairs).pre
      [gAddr, xAddr, pAddr, Δ, L, b, 0, X.card, pairs.length, h] mem
  post args mem v mem' := ∃ gAddr xAddr pAddr dst h,
    args = [gAddr, xAddr, pAddr, Δ, L, b, X.card, pairs.length, dst, h] ∧
    dst + (routeResultWords (fullRoute route G X pairs Δ L n b).1).length ≤ v ∧
    v ≤ h + (n + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
      (Δ + L + max b X.card) ∧
    (∀ x < dst, mem' x = mem x) ∧ ZeroFrom mem' v ∧
    ListAt mem' dst (routeResultWords (fullRoute route G X pairs Δ L n b).1)
  cost _ _ := buildFullRouteCost
    (fun b' => K * (routeCost G X pairs Δ L b' 0 + G.encode.length +
      (finsetWords X).length * (L + 1) + (pairsWords pairs).length + 1))
    (fun b' => route G X pairs Δ L b' 0) n b

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem runs_ret_nop_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hq : Q (.returned v) st) (hc : k + (e.size + 1) + 1 ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.ret e) .nop) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.returned v, st, e.size + 1 + 1, runs_seq_iff.mpr (Or.inl
    ⟨v, e.size + 1, runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, rfl, rfl⟩), hq, by omega⟩

private theorem routerInputs_frame {mem mem' : ℕ → ℕ} {gAddr xAddr pAddr h : ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hf : ∀ i < h, mem' i = mem i)
    (hG : GraphAt mem gAddr G) (hX : ListAt mem xAddr (finsetWords X))
    (hP : ListAt mem pAddr (pairsWords pairs))
    (hg : gAddr + G.encode.length ≤ h) (hx : xAddr + (finsetWords X).length ≤ h)
    (hp : pAddr + (pairsWords pairs).length ≤ h) :
    GraphAt mem' gAddr G ∧ ListAt mem' xAddr (finsetWords X) ∧
      ListAt mem' pAddr (pairsWords pairs) := by
  refine ⟨?_, ?_, ?_⟩
  · change ListAt mem' gAddr G.encode
    exact ListAt.congr hG fun i _ hi => hf i (hi.trans_le hg)
  · exact ListAt.congr hX fun i _ hi => hf i (hi.trans_le hx)
  · exact ListAt.congr hP fun i _ hi => hf i (hi.trans_le hp)

private theorem routeMatched_len_offset {mem : ℕ → ℕ} {h : ℕ} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (hAt : ListAt mem h (routeResultWords (.matched Ms emb))) :
    mem (h + 3) + 4 = (routeResultWords (.matched Ms emb)).length := by
  let bs : List (List ℕ) :=
    [[0], csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]),
      csrList Ms.flatten.length emb]
  have hAt' : ListAt mem h (layoutList bs) := hAt
  have hOff := csrList_offset hAt' (le_refl 3)
  have hLen : (routeResultWords (.matched Ms emb)).length = (layoutList bs).length := rfl
  rw [length_layoutList] at hLen
  simp only [bs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.range_succ, List.map_append,
    List.sum_append, List.getD_cons_zero, List.getD_cons_succ, List.range_zero] at hLen hOff
  change mem (h + 3) = _ at hOff
  omega

/-- The RAM loop returns the same block as `fullRoute` at `dst`, bumping through at most `n + 1`
router calls without zeroing router scratch. -/
theorem buildFullRouteProc_meetsContract
    {w K : ℕ} {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    {p : Program} {self fRoute fCopy : ℕ}
    (hself : p.procs[self]? = some (buildFullRouteProc fRoute fCopy self))
    (hRoute : ProvidesRouter w K route routeCost sR p fRoute)
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hPlayer : IsMatchingPlayer route routeCost) {β : ℝ} (hβ : 0 < β)
    (hExp : G.IsExpansionExpanderOn X β) (hXw : X.card < 2 ^ w) :
    ∀ n b, X.card < 2 ^ (n + 1) * b →
      MeetsContract w p self (buildFullRouteContract w K route routeCost sR G X pairs Δ L n b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hFuel
    refine meetsContract_of_runs hself fun args mem pos ω hWords hPre => ?_
    obtain ⟨g, x, ps, dst, h, rfl, hDstLe, hw4, hTotalSpace, hPre⟩ := hPre
    have hPre' := hPre
    obtain ⟨⟨_, _, _, _, _, _, _, _, hArgs, hG, hGval, hX, hP, hg, hx, hp, hRouter, hb⟩, hZ, hSpace⟩ := hPre
    simp only [List.cons.injEq, and_true, true_and] at hArgs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hArgs
    set sp := routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max b X.card)
    set sp0 := sR G.n G.encode.length (pairsWords pairs).length (Δ + L + b + 0)
    have hsp0Le : sp0 ≤ sp := le_routerSpaceUpTo (by omega)
    change ZeroFrom mem h at hZ
    change h + sp0 < 2 ^ w at hSpace
    have hOne : 1 < 2 ^ w := by omega
    have hThree : 3 < 2 ^ w := by omega
    refine runs_start_le ?_
    unfold buildFullRouteProc
    refine runs_seq_call_le (hRoute G X pairs)
      (vs := [g, x, ps, Δ, L, b, 0, X.card, pairs.length, h])
      (by simp [evalArgs, Expr.eval, startState]) ?_ hPre' ?_
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact Nat.two_pow_pos _ | exact hWords _ (by simp)
    intro v mem₁ pos₁ hPost
    obtain ⟨⟨hv₁, hv₂, hf, hz, _⟩, _, _, _, _, _, _, _, _, hArgs, hAt, hEndLe⟩ := hPost
    simp only [List.cons.injEq, and_true, true_and] at hArgs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hArgs
    change h ≤ v at hv₁
    change v ≤ h + sp0 at hv₂
    have hv₂' : v ≤ h + sp := hv₂.trans (Nat.add_le_add_left hsp0Le h)
    change ∀ i < h, mem₁ i = mem i at hf
    have hvw : v < 2 ^ w := hv₂.trans_lt hSpace
    have hOutW : h + (routeResultWords (route G X pairs Δ L b 0)).length < 2 ^ w :=
      hEndLe.trans_lt hvw
    refine runs_seq_cond_le (v := routeTag (route G X pairs Δ L b 0))
      (eval_routeTag (by rfl) hAt hOutW) ?_ ?_
    · intro hTag
      cases hR : route G X pairs Δ L b 0 with
      | matched M emb => exact False.elim (hTag (by simp [hR, routeTag]))
      | cut U =>
        have hs := hPlayer.spec G X pairs Δ L b 0 hRouter.1 hRouter.2.1 hRouter.2.2.1
          hRouter.2.2.2.1 hRouter.2.2.2.2.1 hRouter.2.2.2.2.2.1 hb hRouter.2.2.2.2.2.2
        rw [hR] at hs
        have hbX := (cut_forces hβ hExp hs).2
        cases n with
        | zero =>
          exfalso
          simpa using (Nat.not_lt_of_ge hbX hFuel)
        | succ n =>
          have hNextFuel : X.card < 2 ^ (n + 1) * (2 * b) := by
            simpa only [pow_succ (a := 2) (n + 1), Nat.mul_assoc] using hFuel
          have hNext := ih n (Nat.lt_succ_self n) (2 * b) hNextFuel
          obtain ⟨hG₁, hX₁, hP₁⟩ := routerInputs_frame hf hG hX hP hg hx hp
          have hBW := hbX.trans_lt hXw
          set spNext := routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
            (Δ + L + max (2 * b) X.card)
          have hSpNextLe : spNext ≤ sp := routerSpaceUpTo_mono (by omega)
          have hSp2bLe : sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 * b + 0) ≤ spNext :=
            le_routerSpaceUpTo (by omega)
          have hNextTotal : v + (n + 1) * spNext < 2 ^ w := by
            have hmul : (n + 1 + 1) * sp = sp + (n + 1) * sp := by ring
            have hmn : (n + 1) * spNext ≤ (n + 1) * sp := Nat.mul_le_mul_left _ hSpNextLe
            omega
          have hNextSingle : v + sR G.n G.encode.length (pairsWords pairs).length
              (Δ + L + 2 * b + 0) < 2 ^ w := by
            have h1 : 1 * spNext ≤ (n + 1) * spNext := Nat.mul_le_mul_right spNext (by omega)
            omega
          refine runs_seq_assoc_le ?_
          refine runs_seq_call_le hNext (vs := [g, x, ps, Δ, L, 2 * b, X.card, pairs.length, dst, v]) ?_ ?_
            ⟨g, x, ps, dst, v, rfl, hDstLe.trans hv₁, hw4, hNextTotal,
             ⟨⟨g, x, ps, Δ, L, 2 * b, 0, v, rfl, hG₁, hGval, hX₁, hP₁, hg.trans hv₁, hx.trans hv₁,
                hp.trans hv₁, hRouter, by omega⟩, hz, hNextSingle⟩⟩ ?_
          · simp [evalArgs, Expr.eval, startState, Function.update, ← Nat.two_mul, hBW]
          · intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | exact hBW | exact hvw | exact hWords _ (by simp)
          intro v₂ mem₂ pos₂ hPostNext
          obtain ⟨_, _, _, _, _, hArgs, hLo, hHi, hFrame, hZero₂, hResult⟩ := hPostNext
          simp only [List.cons.injEq, and_true, true_and] at hArgs
          obtain ⟨_, _, _, rfl, rfl⟩ := hArgs
          have hHi' : v₂ ≤ h + (n + 1 + 1) * sp := by
            have hmul : (n + 1 + 1) * sp = sp + (n + 1) * sp := by ring
            have hmn : (n + 1) * spNext ≤ (n + 1) * sp := Nat.mul_le_mul_left _ hSpNextLe
            change v₂ ≤ v + (n + 1) * spNext at hHi
            omega
          refine runs_ret_nop_le (v := v₂) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
          · exact ⟨g, x, ps, dst, h, rfl,
              by simpa only [fullRoute, hR, Outcome.value] using hLo, hHi',
              fun i hi => (hFrame i hi).trans (hf i (hi.trans_le hDstLe)), hZero₂,
              by simpa only [fullRoute, hR] using hResult⟩
          · simp [buildFullRouteContract, RouterProcContract, heapContract,
              buildFullRouteCost, hR, argsSize, Expr.size]
            omega
    · intro hTag
      cases hR : route G X pairs Δ L b 0 with
      | cut U => simp [hR, routeTag] at hTag
      | matched M emb =>
        have hResult : (fullRoute route G X pairs Δ L n b).1 = .matched M emb := by
          cases n <;> simp [fullRoute, hR]
        rw [hR] at hAt hEndLe hOutW
        set len := (routeResultWords (.matched M emb)).length
        have hOff := routeMatched_len_offset hAt
        have hHiBound : v ≤ h + (n + 1) * sp := by
          have h1 : 1 * sp ≤ (n + 1) * sp := Nat.mul_le_mul_right sp (by omega)
          omega
        refine runs_seq_assoc_le ?_
        refine runs_seq_cond_le (v := if dst < h then 1 else 0)
          (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_reg_of_eq (by simp [startState])) hOne) ?_ ?_
        · intro hlt1
          have hlt : dst < h := by split_ifs at hlt1 with h' <;> simp_all
          have hH3W : h + 3 < 2 ^ w := by have := routeTag_lt_length (.matched M emb); omega
          have hFour : 4 < 2 ^ w := by have := routeTag_lt_length (.matched M emb); omega
          have hLenW : len < 2 ^ w := by omega
          have hCopyEval : evalArgs w
              { mem := mem₁
                regs := Function.update (startState [g, x, ps, Δ, L, b, X.card, pairs.length, dst, h] mem pos).regs 10 v
                pos := pos₁ }
              [.reg 9, .bin .add (.load (.bin .add (.reg 9) (.const 3))) (.const 4), .reg 8] =
              some [h, len, dst] := by
            unfold evalArgs
            rw [Expr.eval_reg_of_eq (v := h) (by simp [startState])]
            unfold evalArgs
            have hLoad : (Expr.load (.bin .add (.reg 9) (.const 3))).eval w
                { mem := mem₁
                  regs := Function.update (startState [g, x, ps, Δ, L, b, X.card, pairs.length, dst, h] mem pos).regs 10 v
                  pos := pos₁ } = some (mem₁ (h + 3)) :=
              Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
                (Expr.eval_const hThree) hH3W)
            have hOff' : mem₁ (h + 3) + 4 = len := hOff
            have hAdd : (Expr.bin .add (.load (.bin .add (.reg 9) (.const 3))) (.const 4)).eval w
                { mem := mem₁
                  regs := Function.update (startState [g, x, ps, Δ, L, b, X.card, pairs.length, dst, h] mem pos).regs 10 v
                  pos := pos₁ } = some len := by
              rw [← hOff']
              exact Expr.eval_add hLoad (Expr.eval_const hFour) (hOff'.symm ▸ hLenW)
            rw [hAdd]
            unfold evalArgs
            rw [Expr.eval_reg_of_eq (v := dst) (by simp [startState])]
            rfl
          refine runs_seq_call_le (buildCopyProc_meetsDownContract hCopy) (vs := [h, len, dst])
            hCopyEval (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                          rcases hi with rfl | rfl | rfl <;> first | exact hLenW | exact hWords _ (by simp))
            ⟨h, len, dst, rfl, hDstLe, hOutW, hOne⟩ ?_
          intro _ mem₂ pos₂ hPostCopy
          obtain ⟨_, _, _, hEqC, hCopied, hFrC⟩ := hPostCopy
          simp only [List.cons.injEq, and_true] at hEqC
          obtain ⟨rfl, rfl, rfl⟩ := hEqC
          have hAtDst : ListAt mem₂ dst (routeResultWords (.matched M emb)) := fun j hj =>
            (hCopied j hj).trans (hAt j hj)
          have hFrDst : ∀ i < dst, mem₂ i = mem i := fun i hi =>
            (hFrC i (Or.inl hi)).trans (hf i (hi.trans_le hDstLe))
          have hZero₂ : ZeroFrom mem₂ v := fun i hi =>
            (hFrC i (Or.inr (by omega))).trans (hz i hi)
          refine runs_ret_nop_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
          · exact ⟨g, x, ps, dst, h, rfl, by dsimp only [Outcome.value]; rw [hResult]; omega, hHiBound,
              hFrDst, hZero₂, hResult ▸ hAtDst⟩
          · cases n <;> simp [buildFullRouteContract, RouterProcContract, heapContract,
              buildCopyDownContract, buildCopyContract, buildFullRouteCost, hR, argsSize,
              Expr.size, len] <;> omega
        · intro hge1
          have hDstEq : dst = h := by
            have hnot : ¬ dst < h := fun hlt => by simp [hlt] at hge1
            omega
          subst hDstEq
          refine runs_seq_nop_le ?_
          refine runs_ret_nop_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
          · exact ⟨g, x, ps, dst, dst, rfl, by rw [hResult]; exact hEndLe, hHiBound, hf, hz,
              hResult ▸ hAt⟩
          · cases n <;> simp [buildFullRouteContract, RouterProcContract, heapContract,
              buildFullRouteCost, hR, argsSize, Expr.size] <;> omega

end MinCostFlow.HierPaths
