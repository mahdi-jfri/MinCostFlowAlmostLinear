module

public import MinCostFlow.HierPaths.BuildProgBatchInputs
public import MinCostFlow.HierPaths.BuildProgFullRoute
import MinCostFlow.HierPaths.InitBlockLen

/-!
# The common router call of a game round

When at least one active child receives a cut, pack all cut requests and route
them together. A round with only expander replies exits after selection. The
count and child indices at the front of the block identify the routed children.
When routed, the returned bump-end is stored at `batch` so downstream walk and
hole collectors can find `walkDir = mem[batch] + 4`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Args are `[replies, activeCount, childSize, host, vertices, Δ, L, heap, xLen]`. -/
def buildRoundRouteProc (fSelect fBatch fRoute : ℕ) : Stmt :=
  .seq (.assign 9 (.bin .add (.reg 7) (.const 1)))
    (.seq (.call 10 fSelect [.reg 0, .reg 1, .reg 9])
      (.seq (.store (.reg 7) (.reg 10))
        (.seq (.assign 11 (.bin .add (.reg 9) (.reg 1)))
          (.seq (.cond (.reg 10)
            (.seq (.call 12 fBatch [.reg 0, .reg 9, .reg 10, .reg 2, .reg 11])
              (.seq (.call 13 fRoute
                [.reg 3, .reg 4, .reg 11, .reg 5, .reg 6, .const 2, .reg 8, .reg 10, .reg 12, .reg 12])
                (.seq (.store (.reg 11) (.reg 13))
                  (.assign 11 (.reg 13)))))
            .nop) (.ret (.reg 11))))))

theorem buildRoundRouteProc_noRand (fSelect fBatch fRoute : ℕ) :
    (buildRoundRouteProc fSelect fBatch fRoute).NoRand := by
  simp [buildRoundRouteProc, Stmt.NoRand]

/-- Layout after the common call. The router result is at `reply`, and `mem batch` records
the bumped end `v` so downstream collectors can locate `walkDir = v + 4`. -/
def RoundRouteAt (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q s h v : ℕ)
    (res : RouteResult) (mem : ℕ → ℕ) : Prop :=
  let idx := batchJobIndices J core q
  let batch := h + 1 + J.count
  let reply := buildBatchEnd batch idx.length s
  mem h = idx.length ∧ ListAt mem (h + 1) idx ∧
  if idx.isEmpty then v = batch else
    mem batch = v ∧ ListAt mem reply (routeResultWords res) ∧
      reply + (routeResultWords res).length ≤ v

/-- The route round consumes the core replies and appends the cut list, router batch
and, when the batch has a pair, the result of full routing. -/
def buildRoundRouteContract (w K q s Δ L : ℕ) (J : BuildGameJobs)
    (core : ℕ → Graph → CoreResult) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) : Contract :=
  let pairs := batchJobPairs J core q s
  let k := pairs.length
  let res := (lemma1Route route G X pairs Δ L).1
  let C := buildFullRouteContract w K route routeCost sR G X pairs Δ L X.card 2
  { pre := fun args mem => ∃ replies g x h₀ h,
      args = [replies, J.count, s, g, x, Δ, L, h, X.card] ∧
      GameRepliesAt J core q h₀ replies mem ∧ replies + J.count + 1 ≤ h₀ ∧
      J.prepPrefix core q h₀ J.count ≤ h ∧ ZeroFrom mem h ∧
      GraphAt mem g G ∧ G.IsValid ∧ ListAt mem x (finsetWords X) ∧
      g + G.encode.length ≤ h ∧ x + (finsetWords X).length ≤ h ∧
      RouterPre G X pairs Δ L ∧ 3 < 2 ^ w ∧
      buildBatchEnd (h + 1 + J.count) k s +
        (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
          (Δ + L + max 2 X.card) < 2 ^ w ∧
      2 * (s / 2) = s ∧ (∀ i < J.count, (J.graph i).n = s) ∧
      (∀ i < J.count, ∀ U, J.answer core q i = .cut U → U ⊆ Finset.range s)
    post := fun args mem v mem' => ∃ replies g x h,
      args = [replies, J.count, s, g, x, Δ, L, h, X.card] ∧
      RoundRouteAt J core q s h v res mem' ∧
      v ≤ buildBatchEnd (h + 1 + J.count) k s +
        (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
          (Δ + L + max 2 X.card) ∧
      (∀ j < h, mem' j = mem j) ∧ ZeroFrom mem' v
    cost := fun _ _ => 36 * J.count + k * (17 * s + 128) + C.cost [] (fun _ => 0) + 160 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private theorem batchJobIndices_le (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q : ℕ) :
    (batchJobIndices J core q).length ≤ J.count := by
  simpa [batchJobIndices, cutReplyIndices] using List.length_filter_le
    (fun i => decide (coreTag (J.answer core q i) = 0)) (List.range J.count)

/-- All requesting children share one full-routing call, including all retries of Lemma 1. -/
theorem buildRoundRouteProc_meetsContract {w K q s Δ L : ℕ} {J : BuildGameJobs}
    {core : ℕ → Graph → CoreResult} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {G : Graph} {X : Finset ℕ} {p : Program}
    {f fSelect fBatch fFull fCopy fRoute : ℕ}
    (hf : p.procs[f]? = some (buildRoundRouteProc fSelect fBatch fFull))
    (hSel : p.procs[fSelect]? = some buildGameSelectProc)
    (hBatch : p.procs[fBatch]? = some (buildBatchProc fCopy))
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hFull : p.procs[fFull]? = some (buildFullRouteProc fRoute fCopy fFull))
    (hRoute : ProvidesRouter w K route routeCost sR p fRoute)
    (hPlayer : IsMatchingPlayer route routeCost) {β : ℝ} (hβ : 0 < β)
    (hExp : G.IsExpansionExpanderOn X β) (hXw : X.card < 2 ^ w) :
    MeetsContract w p f (buildRoundRouteContract w K q s Δ L J core route routeCost sR G X) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨replies, g, x, h₀, h, rfl, hReplies, hTable, hPrepared, hZ, hG, hGval, hX, hGend, hXend,
    hRouter, hw, hRoom, hEven, hSizes, hSets⟩ := hPre
  let idx := batchJobIndices J core q
  let pairs := batchJobPairs J core q s
  let k := idx.length
  let batch := h + 1 + J.count
  let reply := buildBatchEnd batch k s
  have hk : pairs.length = k := length_batchJobPairs J core q s
  change buildBatchEnd batch pairs.length s +
    (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
      (Δ + L + max 2 X.card) < 2 ^ w at hRoom
  rw [hk] at hRoom
  have hRoom' : reply + (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
      (Δ + L + max 2 X.card) < 2 ^ w := hRoom
  have hSingleRoom : reply + sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) < 2 ^ w := by
    have h0 : sR G.n G.encode.length (pairsWords pairs).length (Δ + L + 2 + 0) ≤
        routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      le_routerSpaceUpTo (by omega)
    have h1 : 1 * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) ≤
        (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length (Δ + L + max 2 X.card) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hBatchLe : batch ≤ reply := by unfold reply buildBatchEnd; omega
  have hBatchLt : batch < reply := by unfold reply buildBatchEnd; omega
  have hkw : k ≤ J.count := batchJobIndices_le J core q
  have hH1 : h + 1 < 2 ^ w := by dsimp [batch] at hBatchLe; omega
  have hB : h + 1 + J.count < 2 ^ w := by dsimp [batch] at hBatchLe; omega
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hh : h₀ ≤ h :=
    (J.prepPrefix_mono core q h₀ (Nat.zero_le J.count)).trans hPrepared
  have hTags : ReplyTagsAt mem replies J.count (h + 1) (fun i => J.answer core q i) :=
    hReplies.tags (by omega)
  refine runs_start_le ?_
  unfold buildRoundRouteProc
  refine runs_seq_assign_le (v := h + 1) ?_ ?_
  · simp [Expr.eval, startState, hOne, hH1]
  refine runs_seq_call_le (buildGameSelectProc_meetsContract hSel)
    (vs := [replies, J.count, h + 1]) ?_ ?_
    ⟨replies, h + 1, rfl, by omega, hB, hw, hTags⟩ ?_
  · simp [evalArgs, Expr.eval, Function.update, startState]
  · wram_words
  intro v₁ mem₁ pos₁ hPost
  obtain ⟨_, _, hEq, hv₁, hCuts, hFrame₁⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  change v₁ = k at hv₁
  subst v₁
  refine runs_seq_store_le (x := h) (v := k) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, startState]
  · simp [Expr.eval, Function.update]
  refine runs_seq_assign_le (v := batch) ?_ ?_
  · simp [Expr.eval, Function.update, startState, hB, batch]
  let mem₂ := Function.update mem₁ h k
  have hCuts₂ : ListAt mem₂ (h + 1) idx := WordRAM.ListAt.congr hCuts
    fun a ha _ => Function.update_of_ne (by omega) _ _
  have hF₂ : ∀ a, a < h ∨ batch ≤ a → mem₂ a = mem a := by
    intro a ha
    have hne : a ≠ h := by dsimp [batch] at ha; omega
    exact (Function.update_of_ne hne _ _).trans (hFrame₁ a (by dsimp [batch] at ha; omega))
  have hCount : mem₂ h = k := Function.update_self ..
  have hZ₂ : ZeroFrom mem₂ batch := fun a ha =>
    (hF₂ a (Or.inr ha)).trans (hZ a (by dsimp [batch] at ha; omega))
  have hReplies₂ : GameRepliesAt J core q h₀ replies mem₂ := by
    refine ⟨(hF₂ _ (Or.inl (by omega))).trans hReplies.1, ?_⟩
    intro i hi
    obtain ⟨hp, hb⟩ := hReplies.2 i hi
    refine ⟨(hF₂ _ (Or.inl (by omega))).trans hp, ?_⟩
    have hEnd := (J.prepPrefix_mono core q h₀ (show i + 1 ≤ J.count by omega)).trans hPrepared
    refine hb.frame (fun a _ ha => hF₂ a (Or.inl (ha.trans_le hEnd))) ?_
    intro U hU
    rw [hSizes i hi]
    exact hSets i hi U hU
  refine runs_seq_cond_le (v := k) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · intro hkPos
    obtain ⟨hRows, hLens⟩ := hReplies₂.batchRows (out := batch) hCuts₂ (by dsimp [batch]; omega)
      (hPrepared.trans (by dsimp [batch]; omega)) hSizes hSets hEven
    refine runs_seq_assoc_le ?_
    refine runs_seq_call_le (buildBatchProc_meetsContract hBatch hCopy)
      (vs := [replies, h + 1, k, s, batch]) ?_ ?_
      ⟨replies, h + 1, batch, by rw [hk], by rw [hk]; dsimp [batch]; omega,
        by rw [hk]; exact lt_of_le_of_lt (Nat.le_add_right ..) hRoom', hw, hRows, hLens⟩ ?_
    · simp [evalArgs, Expr.eval, Function.update, startState]
    · have hs := hWords s (by simp)
      wram_words
    intro v₃ mem₃ pos₃ hPost
    obtain ⟨_, _, _, hEq, hv₃, hWritten, hFrame₃⟩ := hPost
    simp only [List.cons.injEq, and_true, true_and] at hEq
    obtain ⟨rfl, _, _, rfl⟩ := hEq
    rw [hk] at hv₃ hFrame₃
    change v₃ = reply at hv₃
    subst v₃
    have hMem : ∀ a < h, mem₃ a = mem a :=
      fun a ha => (hFrame₃ _ (Or.inl (by dsimp [batch]; omega))).trans (hF₂ _ (Or.inl ha))
    have hBefore : ∀ a < batch, mem₃ a = mem₂ a := fun a ha => hFrame₃ a (Or.inl ha)
    have hZ₃ : ZeroFrom mem₃ reply := fun a ha =>
      (hFrame₃ _ (Or.inr ha)).trans (hZ₂ a (hBatchLe.trans ha))
    have hPairs : ListAt mem₃ batch (pairsWords pairs) :=
      hWritten.pairsAt hEven (batchJobPairs_halves hSets hEven)
    have hLen : batch + (pairsWords pairs).length ≤ reply := by
      have hLayout : (pairsWords pairs).length = 2 * pairs.length + 1 + pairs.length * s := by
        have hSum : ∀ xs : List (Finset ℕ × Finset ℕ),
            (∀ p ∈ xs, p.1.card = s / 2 ∧ p.2.card = s / 2) →
            ((xs.flatMap fun p => [finsetWords p.1, finsetWords p.2]).map List.length).sum =
              xs.length * s := by
          intro xs
          induction xs with
          | nil => simp
          | cons p xs ih =>
            intro h
            have hp := h p (by simp)
            have hTail := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
            rw [List.flatMap_cons]
            change (finsetWords p.1).length + ((finsetWords p.2).length +
              ((xs.flatMap fun a => [finsetWords a.1, finsetWords a.2]).map List.length).sum) =
                (xs.length + 1) * s
            rw [hTail, finsetWords, finsetWords, Finset.length_sort, Finset.length_sort,
              hp.1, hp.2, Nat.add_mul]
            omega
        rw [pairsWords, length_layoutList, batch_sections_length,
          hSum pairs (batchJobPairs_halves hSets hEven)]
      rw [hLayout, hk]
      dsimp [reply, buildBatchEnd]
      omega
    have hFuel : X.card < 2 ^ (X.card + 1) * 2 := by
      have hh := Nat.lt_two_pow_self (n := X.card)
      rw [Nat.pow_succ]
      omega
    have hFR := buildFullRouteProc_meetsContract (pairs := pairs) (Δ := Δ) (L := L)
      hFull hRoute hCopy hPlayer hβ hExp hXw X.card 2 hFuel
    refine runs_seq_assoc_le ?_
    refine runs_seq_call_le hFR (vs := [g, x, batch, Δ, L, 2, X.card, k, reply, reply]) ?_ ?_
      ⟨g, x, batch, reply, reply, by rw [hk], le_rfl, hw, hRoom',
        ⟨⟨g, x, batch, Δ, L, 2, 0, reply, by rw [hk],
          WordRAM.ListAt.congr hG (fun a _ ha => hMem a (ha.trans_le hGend)), hGval,
          WordRAM.ListAt.congr hX (fun a _ ha => hMem a (ha.trans_le hXend)),
          hPairs, by dsimp [batch] at hBatchLe; omega,
          by dsimp [batch] at hBatchLe; omega, hLen, hRouter, le_rfl⟩, hZ₃, hSingleRoom⟩⟩ ?_
    · simp [evalArgs, Expr.eval, Function.update, startState, hTwo]
    · have hD := hWords Δ (by simp)
      have hL := hWords L (by simp)
      have hRepW : reply < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right ..) hRoom'
      wram_words
    intro v₄ mem₄ pos₄ hPost
    obtain ⟨_, _, _, _, _, hEq, hLo, hHi, hF₄, hZ₄, hRouteAt⟩ := hPost
    simp only [List.cons.injEq, and_true, true_and] at hEq
    obtain ⟨rfl, rfl, rfl, _, rfl, rfl⟩ := hEq
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_le (x := batch) (v := v₄)
      (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_assign_le (v := v₄) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_ret_le (v := v₄) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
    · let mem₅ := Function.update mem₄ batch v₄
      have hMem₅ : ∀ a < h, mem₅ a = mem a := fun a ha =>
        (Function.update_of_ne (by dsimp [batch]; omega) _ _).trans
          ((hF₄ a (by dsimp [batch] at hBatchLe; omega)).trans (hMem a ha))
      have hZ₅ : ZeroFrom mem₅ v₄ := fun a ha =>
        (Function.update_of_ne (by omega) _ _).trans (hZ₄ a ha)
      have hHi' : v₄ ≤ buildBatchEnd (h + 1 + J.count) pairs.length s +
          (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
            (Δ + L + max 2 X.card) := by
        rw [hk]; exact hHi
      refine ⟨replies, g, x, h, rfl, ?_, hHi', hMem₅, hZ₅⟩
      have hne : idx.isEmpty = false :=
        Bool.eq_false_iff.mpr (fun he => hkPos (List.isEmpty_iff_length_eq_zero.mp he))
      change mem₅ h = k ∧ ListAt mem₅ (h + 1) idx ∧ _
      refine ⟨(Function.update_of_ne (by dsimp [batch]; omega) _ _).trans
        ((hF₄ _ (by dsimp [batch] at hBatchLe; omega)).trans
          ((hBefore _ (by dsimp [batch]; omega)).trans hCount)), ?_, ?_⟩
      · exact WordRAM.ListAt.congr hCuts₂ fun a _ ha =>
          (Function.update_of_ne (by dsimp [batch]; omega) _ _).trans
            ((hF₄ a (by dsimp [batch] at hBatchLe; omega)).trans
              (hBefore a (by dsimp [batch]; omega)))
      · change (if idx.isEmpty then _ else
            mem₅ batch = v₄ ∧ ListAt mem₅ reply _ ∧ reply + _ ≤ v₄)
        simp only [hne, Bool.false_eq_true, ite_false]
        exact ⟨Function.update_self ..,
          WordRAM.ListAt.congr hRouteAt (fun a ha _ => Function.update_of_ne (by omega) _ _), hLo⟩
    · simp [buildRoundRouteContract, buildBatchContract, buildGameSelectContract,
        buildFullRouteContract, Expr.size, argsSize, pairs, Nat.mul_add]
      omega
  · intro hK
    refine runs_seq_nop_le ?_
    refine runs_ret_le (v := batch) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
    · have hHi' : batch ≤ buildBatchEnd (h + 1 + J.count) pairs.length s +
          (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
            (Δ + L + max 2 X.card) := by
        rw [hk]; exact hBatchLe.trans (Nat.le_add_right ..)
      refine ⟨replies, g, x, h, rfl, ?_, hHi', fun a ha => hF₂ a (Or.inl ha), hZ₂⟩
      have he : idx.isEmpty = true := by
        have hk' : idx.length = 0 := hK
        have hnil : idx = [] := List.length_eq_zero_iff.mp hk'
        rw [hnil]
        rfl
      refine ⟨hCount, hCuts₂, ?_⟩
      change (if idx.isEmpty then batch = h + 1 + J.count else _)
      simp [he, batch]
    · simp [buildRoundRouteContract, buildGameSelectContract, Expr.size, argsSize]
      omega

end MinCostFlow.HierPaths
