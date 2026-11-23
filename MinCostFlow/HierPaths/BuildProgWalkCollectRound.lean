module

public import MinCostFlow.HierPaths.BuildProgChildTrace
import MinCostFlow.HierPaths.InitLayout

/-!
# Collecting per-child walk pointers from the game archive

Scan the round directory (`0 .. limit - 1`) and the final injection reply to build a flat
per-child pointer table `walkPtrs[c][e]` and counts `walkCnt[c] = (F c).length` above `injEnd`.
All archived memory below `injEnd` stays unchanged, and each pointer points to `SeqAt` for the
exact corresponding walk in `D.emb c`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Predicate for the flat per-child walk pointer table at `[walkCnt, walkPtrs + k * cap)`. -/
def WalkTableAt (k walkCnt walkPtrs cap : ℕ) (curWalks : ℕ → List (List ℕ))
    (mem : ℕ → ℕ) : Prop :=
  walkCnt + k ≤ walkPtrs ∧
  ∀ c < k, (curWalks c).length ≤ cap ∧ mem (walkCnt + c) = (curWalks c).length ∧
    ∀ e < (curWalks c).length,
      let w := (curWalks c).getD e []
      let addr := mem (walkPtrs + c * cap + e)
      addr + 1 + w.length ≤ walkCnt ∧ SeqAt mem addr w

/-- Append `mem[walkDir + loEdge .. walkDir + hiEdge - 1]` to `walkPtrs[c]`.
Args: `[walkDir, loEdge, hiEdge, walkCnt, walkPtrs, cap, c]`. -/
def buildAppendRowWalksProc : Stmt :=
  .assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
  .assign 8 (.bin .add (.reg 4) (.bin .mul (.reg 6) (.reg 5))) ;;
  forRange 9 (.reg 1) (.reg 2)
    (.store (.bin .add (.reg 8) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 9))) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1))) ;;
  .store (.bin .add (.reg 3) (.reg 6)) (.reg 7) ;;
  .ret (.const 0)

theorem buildAppendRowWalksProc_noRand : buildAppendRowWalksProc.NoRand := by
  simp [buildAppendRowWalksProc, forRange, forUp, Stmt.NoRand]

/-- Contract for appending one child's walk pointers from a walk directory slice. -/
def buildAppendRowWalksContract (w : ℕ) (oldCnt : ℕ) (ptrs : ℕ → ℕ) : Contract where
  pre args mem := ∃ walkDir lo hi walkCnt walkPtrs cap c,
    args = [walkDir, lo, hi, walkCnt, walkPtrs, cap, c] ∧
    lo ≤ hi ∧ mem (walkCnt + c) = oldCnt ∧
    (∀ r, lo ≤ r → r < hi → mem (walkDir + r) = ptrs r) ∧
    walkDir + hi ≤ walkCnt ∧ walkCnt + c < walkPtrs + c * cap ∧
    walkPtrs + c * cap + oldCnt + (hi - lo) < 2 ^ w ∧ 1 < 2 ^ w
  post args mem _ after := ∃ walkDir lo hi walkCnt walkPtrs cap c,
    args = [walkDir, lo, hi, walkCnt, walkPtrs, cap, c] ∧
    after (walkCnt + c) = oldCnt + (hi - lo) ∧
    (∀ e < hi - lo, after (walkPtrs + c * cap + oldCnt + e) = ptrs (lo + e)) ∧
    ∀ a, a ≠ walkCnt + c →
      (a < walkPtrs + c * cap + oldCnt ∨ walkPtrs + c * cap + oldCnt + (hi - lo) ≤ a) →
      after a = mem a
  cost args _ := 32 * (args.getD 2 0 - args.getD 1 0) + 60

/-- Collect all walks of one executed round record `rec ≠ 0`.
Args: `[rec, start, s, walkCnt, walkPtrs, cap]`. -/
def buildCollectRoundProc (fAppend : ℕ) : Stmt :=
  .assign 6 (.load (.reg 0)) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 8 (.load (.reg 6)) ;;
  .cond (.reg 8)
    (.assign 9 (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 7)) ;;
     .assign 10 (.bin .add (.bin .add (.bin .add (.reg 9) (.bin .add (.reg 8) (.reg 8))) (.const 1))
                   (.bin .mul (.reg 8) (.reg 2))) ;;
     .assign 11 (.bin .add (.bin .add (.reg 10) (.const 4)) (.load (.bin .add (.reg 10) (.const 1)))) ;;
     .assign 12 (.bin .add (.load (.reg 9)) (.const 4)) ;;
     forRange 13 (.const 0) (.reg 8)
       (.assign 14 (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 13))) ;;
        .assign 15 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 14))) ;;
        .assign 16 (.bin .div (.bin .sub (.reg 15) (.reg 1)) (.reg 2)) ;;
        .assign 17 (.bin .div (.load (.bin .add (.reg 11) (.reg 13))) (.const 2)) ;;
        .assign 18 (.bin .div (.load (.bin .add (.bin .add (.reg 11) (.reg 13)) (.const 1))) (.const 2)) ;;
        .call 19 fAppend [.reg 12, .reg 17, .reg 18, .reg 3, .reg 4, .reg 5, .reg 16]))
    .nop ;;
  .ret (.const 0)

theorem buildCollectRoundProc_noRand (fAppend : ℕ) : (buildCollectRoundProc fAppend).NoRand := by
  simp [buildCollectRoundProc, forRange, forUp, Stmt.NoRand]

/-- Contract for scanning one executed round record into the walk pointer table. -/
def buildCollectRoundContract (w : ℕ) (G : Graph) (start s k d coreCap lo hi rec : ℕ)
    (walks : ℕ → List (List ℕ)) (hole : Option ℕ)
    (preWalks : ℕ → List (List ℕ)) : Contract where
  pre args mem := ∃ walkCnt walkPtrs cap,
    args = [rec, start, s, walkCnt, walkPtrs, cap] ∧
    rec ≠ 0 ∧ 1 ≤ s ∧ hi ≤ walkCnt ∧
    RoundArchive G start s k d coreCap mem lo hi rec walks hole ∧
    WalkTableAt k walkCnt walkPtrs cap preWalks mem ∧
    (∀ c < k, (preWalks c).length + (walks c).length ≤ cap) ∧
    walkPtrs + k * cap < 2 ^ w ∧ ZeroFrom mem (walkPtrs + k * cap) ∧
    start + k * s < 2 ^ w ∧ 4 < 2 ^ w
  post args mem _ after := ∃ walkCnt walkPtrs cap,
    args = [rec, start, s, walkCnt, walkPtrs, cap] ∧
    WalkTableAt k walkCnt walkPtrs cap (fun c => preWalks c ++ walks c) after ∧
    (∀ a < walkCnt, after a = mem a) ∧ ZeroFrom after (walkPtrs + k * cap)
  cost _ _ := 32 * (s * k) + 140 * k + 200

/-- Collect all walks of all rounds (`0 .. limit - 1`) and the final injection into the
flat per-child walk pointer table at `[walkCnt, walkPtrs + k * cap)`.
Args: `[directory, limit, start, s, k, heap1, walkCnt, walkPtrs, cap]`. -/
def buildCollectWalksProc (fRound fAppend : ℕ) : Stmt :=
  forRange 9 (.const 0) (.reg 1)
    (.assign 10 (.load (.bin .add (.reg 0) (.reg 9))) ;;
     .cond (.reg 10)
       (.call 11 fRound [.reg 10, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8])
       .nop) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 5) (.reg 3))
                (.bin .add (.reg 4) (.reg 4))) (.const 1)) (.bin .mul (.reg 4) (.reg 3))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.const 4)) (.load (.bin .add (.reg 10) (.const 1)))) ;;
  .assign 12 (.bin .add (.load (.reg 5)) (.const 4)) ;;
  forRange 9 (.const 0) (.reg 4)
    (.assign 13 (.bin .div (.load (.bin .add (.reg 11) (.reg 9))) (.const 2)) ;;
     .assign 14 (.bin .div (.load (.bin .add (.bin .add (.reg 11) (.reg 9)) (.const 1))) (.const 2)) ;;
     .call 15 fAppend [.reg 12, .reg 13, .reg 14, .reg 6, .reg 7, .reg 8, .reg 9]) ;;
  .ret (.const 0)

theorem buildCollectWalksProc_noRand (fRound fAppend : ℕ) :
    (buildCollectWalksProc fRound fAppend).NoRand := by
  simp [buildCollectWalksProc, forRange, forUp, Stmt.NoRand]

/-- Contract for building the complete per-child walk pointer table above `injEnd`. -/
def buildCollectWalksContract (w : ℕ) (D : ChoiceLoopData) (slot slotWords heap₁ injEnd : ℕ)
    (sts : ℕ → ChildState) (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : Contract where
  pre args mem := ∃ cap,
    args = [D.directory, D.limit, D.first, D.base.childSize, D.count, heap₁,
      injEnd, injEnd + D.count, cap] ∧
    1 ≤ D.base.childSize ∧ D.directory + D.limit ≤ injEnd ∧
    TraceRoundsMem D D.limit heap₁ sts mem ∧
    InjArchive D.base.host D.base.childSize D.count D.base.pathBound (roundRouteCap D) slot slotWords
      heap₁ injEnd F (fun c => (sts c).rounds.flatten.map Prod.snd) mem ∧
    (∀ c < D.count, (F c).length ≤ cap) ∧
    injEnd + D.count + D.count * cap < 2 ^ w ∧
    D.first + D.count * D.base.childSize < 2 ^ w ∧ 4 < 2 ^ w
  post args mem _ after := ∃ cap,
    args = [D.directory, D.limit, D.first, D.base.childSize, D.count, heap₁,
      injEnd, injEnd + D.count, cap] ∧
    WalkTableAt D.count injEnd (injEnd + D.count) cap (fun c => (F c).map Prod.snd) after ∧
    (∀ a < injEnd, after a = mem a) ∧ ZeroFrom after (injEnd + D.count + D.count * cap)
  cost _ _ := (D.limit + 1) * (32 * (D.base.childSize * D.count) + 170 * D.count + 260) + 120

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

theorem flatIndex_succ_eq (Ms : List (List (ℕ × ℕ))) {j : ℕ} (hj : j < Ms.length) :
    flatIndex Ms (j + 1) 0 = flatIndex Ms j 0 + (Ms.getD j []).length := by
  unfold flatIndex
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ hj]
  omega

theorem flatIndex_le_flatten (Ms : List (List (ℕ × ℕ))) {j : ℕ} (hj : j ≤ Ms.length) :
    flatIndex Ms j 0 ≤ Ms.flatten.length := by
  have hgen : ∀ n ≤ Ms.length, flatIndex Ms n 0 = (Ms.take n).flatten.length := by
    intro n
    induction n with
    | zero => intro _; simp [flatIndex]
    | succ n ih =>
      intro hn
      rw [flatIndex_succ_eq Ms hn, ih (Nat.le_of_succ_le hn),
        List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
        List.flatten_singleton, List.getD_eq_getElem _ _ hn]
  rw [hgen j hj]
  have hsplit : Ms = Ms.take j ++ Ms.drop j := (List.take_append_drop j Ms).symm
  conv_rhs => rw [hsplit]
  rw [List.flatten_append, List.length_append]
  omega

theorem routeMatched_mt_offsets {mem : ℕ → ℕ} {rep : ℕ} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (hAt : ListAt mem rep (routeResultWords (.matched Ms emb))) :
    mem (rep + 1) = 1 ∧
    (∀ j ≤ Ms.length, mem (rep + 5 + j) = 2 * flatIndex Ms j 0) ∧
    Ms.length + 6 + 2 * Ms.flatten.length ≤ (routeResultWords (.matched Ms emb)).length := by
  let bs : List (List ℕ) :=
    [[0], csrList Ms.length (matchingRowWords Ms), csrList Ms.flatten.length emb]
  have hAt' : ListAt mem rep (layoutList bs) := hAt
  have hOff1 : mem (rep + 1) = 1 := by
    have h1 := csrList_offset hAt' (show 1 ≤ 3 by omega)
    simpa [bs, List.range_succ, List.getD_cons_zero] using h1
  have hMtAt : ListAt mem (rep + 5) (csrList Ms.length (matchingRowWords Ms)) := by
    have h1 := listAt_csrList_get hAt' (show 1 < bs.length by simp [bs])
    simpa [bs, List.range_succ, List.getD_cons_zero, List.getD_cons_succ] using h1
  have hMtOff : ∀ j ≤ Ms.length, mem (rep + 5 + j) = 2 * flatIndex Ms j 0 := by
    intro j hj
    have h1 := csrList_offset hMtAt hj
    rw [h1]
    have hgen : ∀ n ≤ Ms.length,
        ((List.range n).map fun i => (matchingRowWords Ms i).length).sum = 2 * flatIndex Ms n 0 := by
      intro n
      induction n with
      | zero => intro _; simp [flatIndex]
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, ih (Nat.le_of_succ_le hn), length_matchingRowWords,
          flatIndex_succ_eq Ms hn]
        omega
    exact hgen j hj
  have hLen : Ms.length + 6 + 2 * Ms.flatten.length ≤ (routeResultWords (.matched Ms emb)).length := by
    change Ms.length + 6 + 2 * Ms.flatten.length ≤ (layoutList bs).length
    rw [length_layoutList]
    simp only [bs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have h1 : (csrList Ms.length (matchingRowWords Ms)).length =
        Ms.length + 1 + 2 * Ms.flatten.length := by
      rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
      have hgen : ∀ n ≤ Ms.length,
          ((List.range n).map fun i => (matchingRowWords Ms i).length).sum =
            2 * (Ms.take n).flatten.length := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hn
          rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton, ih (Nat.le_of_succ_le hn), length_matchingRowWords,
            List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
            List.flatten_singleton, List.getD_eq_getElem _ _ hn]
          omega
      have := hgen Ms.length le_rfl
      simp only [List.take_length] at this
      omega
    omega
  exact ⟨hOff1, hMtOff, hLen⟩

/-- `buildAppendRowWalksProc` meets `buildAppendRowWalksContract`. -/
theorem buildAppendRowWalksProc_meetsContract {w f oldCnt : ℕ} {ptrs : ℕ → ℕ} {p : Program}
    (hf : p.procs[f]? = some buildAppendRowWalksProc) :
    MeetsContract w p f (buildAppendRowWalksContract w oldCnt ptrs) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨walkDir, lo, hi, walkCnt, walkPtrs, cap, c, rfl, hlo, hcnt, hptrs,
    hdirLe, hcntLt, htop, hw⟩ := hPre
  set base := walkPtrs + c * cap
  refine runs_start_le ?_
  unfold buildAppendRowWalksProc
  refine runs_seq_assign_le (v := oldCnt)
    (by rw [← hcnt]; exact Expr.eval_load (Expr.eval_add
          (Expr.eval_reg_of_eq (show (startState [walkDir, lo, hi, walkCnt, walkPtrs, cap, c] mem pos).regs 3 = walkCnt from rfl))
          (Expr.eval_reg_of_eq (show (startState [walkDir, lo, hi, walkCnt, walkPtrs, cap, c] mem pos).regs 6 = c from rfl))
          (by omega))) ?_
  refine runs_seq_assign_le (v := base)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) (by omega)) ?_
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .reg 1) (hi := .reg 2)
    (body := .store (.bin .add (.reg 8) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 9))) ;;
             .assign 7 (.bin .add (.reg 7) (.const 1)))
    (P := fun st =>
      st.regs 0 = walkDir ∧ st.regs 1 = lo ∧ st.regs 2 = hi ∧ st.regs 3 = walkCnt ∧
      st.regs 4 = walkPtrs ∧ st.regs 5 = cap ∧ st.regs 6 = c ∧
      st.regs 7 = oldCnt ∧ st.regs 8 = base ∧ st.mem = mem)
    (Inv := fun i st =>
      st.regs 0 = walkDir ∧ st.regs 1 = lo ∧ st.regs 2 = hi ∧ st.regs 3 = walkCnt ∧
      st.regs 4 = walkPtrs ∧ st.regs 5 = cap ∧ st.regs 6 = c ∧
      st.regs 7 = oldCnt + (i - lo) ∧ st.regs 8 = base ∧ st.regs 9 = i ∧
      (∀ e < i - lo, st.mem (base + oldCnt + e) = ptrs (lo + e)) ∧
      (∀ a, (a < base + oldCnt ∨ base + oldCnt + (i - lo) ≤ a) → st.mem a = mem a))
    15 lo hi hlo hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hm⟩ => by
      refine ⟨by simp [Expr.eval, h1], ?_⟩
      refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
        by simpa using h8, by simp,
        fun _ he => by omega, fun _ _ => hm ▸ rfl⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.2.1])
    (fun i hge hilt => by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hwr, hfr⟩
      have hsrc : st.mem (walkDir + i) = ptrs i := by
        rw [hfr _ (Or.inl (by omega))]; exact hptrs i hge hilt
      refine runs_start_le ?_
      refine runs_seq_store_le (x := base + (oldCnt + (i - lo))) (v := ptrs i)
        (Expr.eval_add (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h7) (by omega))
        (by rw [← hsrc]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h0)
              (Expr.eval_reg_of_eq h9) (by omega))) ?_
      refine runs_assign_le (v := oldCnt + (i - lo) + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq h7) (Expr.eval_const hw) (by omega)) ?_
        (by simp [Expr.size])
      refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simp; omega,
        by simpa using h8, by simp, ?_, ?_⟩, by simp [h9]⟩
      · intro e he
        dsimp only
        by_cases hlast : e = i - lo
        · subst hlast
          rw [show base + oldCnt + (i - lo) = base + (oldCnt + (i - lo)) by omega,
            Function.update_self, show lo + (i - lo) = i by omega]
        · rw [Function.update_of_ne (by omega)]
          exact hwr e (by omega)
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a (by omega))
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp, by simp, rfl⟩ ?_
  intro st3 ⟨_, _, _, h3, _, _, h6, h7, _, _, hwr, hfr⟩
  refine runs_seq_store_le (x := walkCnt + c) (v := oldCnt + (hi - lo))
    (Expr.eval_add (Expr.eval_reg_of_eq h3) (Expr.eval_reg_of_eq h6) (by omega))
    (Expr.eval_reg_of_eq h7) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
  · refine ⟨walkDir, lo, hi, walkCnt, walkPtrs, cap, c, rfl, by simp, ?_, ?_⟩
    · intro e he
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hwr e he
    · intro a hne ha
      dsimp only
      rw [Function.update_of_ne hne]
      exact hfr a ha
  · simp only [buildAppendRowWalksContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size]
    omega

theorem walkTable_append {k walkCnt walkPtrs cap c : ℕ}
    {curWalks : ℕ → List (List ℕ)} {extra : List (List ℕ)} {mem after : ℕ → ℕ}
    (hWT : WalkTableAt k walkCnt walkPtrs cap curWalks mem)
    (hc : c < k) (hCap : (curWalks c).length + extra.length ≤ cap)
    (hCnt : after (walkCnt + c) = (curWalks c).length + extra.length)
    (hNew : ∀ e < extra.length,
      let w := extra.getD e []
      let addr := after (walkPtrs + c * cap + (curWalks c).length + e)
      addr + 1 + w.length ≤ walkCnt ∧ SeqAt mem addr w)
    (hFrame : ∀ a, a ≠ walkCnt + c →
      (a < walkPtrs + c * cap + (curWalks c).length ∨
        walkPtrs + c * cap + (curWalks c).length + extra.length ≤ a) →
      after a = mem a) :
    WalkTableAt k walkCnt walkPtrs cap
      (fun c' => if c' = c then curWalks c' ++ extra else curWalks c') after ∧
    (∀ a < walkCnt, after a = mem a) ∧
    (∀ a, walkPtrs + k * cap ≤ a → after a = mem a) := by
  have hWT1 : walkCnt + k ≤ walkPtrs := hWT.1
  have hLt : ∀ a < walkCnt, after a = mem a := fun a ha =>
    hFrame a (by omega) (Or.inl (by omega))
  have hGe : ∀ a, walkPtrs + k * cap ≤ a → after a = mem a := by
    intro a ha
    have hck : (c + 1) * cap ≤ k * cap := Nat.mul_le_mul_right cap hc
    rw [Nat.succ_mul] at hck
    exact hFrame a (by omega) (Or.inr (by omega))
  refine ⟨⟨hWT1, fun c' hc' => ?_⟩, hLt, hGe⟩
  by_cases heq : c' = c
  · subst heq
    simp only [↓reduceIte, List.length_append]
    refine ⟨hCap, hCnt, fun e he => ?_⟩
    by_cases h1 : e < (curWalks c').length
    · have hAddr : after (walkPtrs + c' * cap + e) = mem (walkPtrs + c' * cap + e) :=
        hFrame _ (by omega) (Or.inl (by omega))
      obtain ⟨hlt, hseq⟩ := (hWT.2 c' hc').2.2 e h1
      have hget : (curWalks c' ++ extra).getD e [] = (curWalks c').getD e [] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getD_eq_getElem _ _ h1, List.getElem_append_left h1]
      rw [hAddr, hget]
      exact ⟨hlt, seqAt_frame hseq fun a ha hb => hLt a (by omega)⟩
    · have he2 : e - (curWalks c').length < extra.length := by omega
      have hpos : walkPtrs + c' * cap + e =
          walkPtrs + c' * cap + (curWalks c').length + (e - (curWalks c').length) := by omega
      have hget : (curWalks c' ++ extra).getD e [] = extra.getD (e - (curWalks c').length) [] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getD_eq_getElem _ _ he2, List.getElem_append_right (by omega)]
      rw [hpos, hget]
      obtain ⟨hlt, hseq⟩ := hNew (e - (curWalks c').length) he2
      exact ⟨hlt, seqAt_frame hseq fun a ha hb => hLt a (by omega)⟩
  · simp only [heq, ↓reduceIte]
    obtain ⟨hcl, hcc, hcw⟩ := hWT.2 c' hc'
    have hdisj : ∀ e < cap, walkPtrs + c' * cap + e < walkPtrs + c * cap ∨
        walkPtrs + c * cap + cap ≤ walkPtrs + c' * cap + e := by
      intro e he
      rcases lt_or_gt_of_ne heq with hlt | hgt
      · left
        have h1 : (c' + 1) * cap ≤ c * cap := Nat.mul_le_mul_right cap hlt
        rw [Nat.succ_mul] at h1; omega
      · right
        have h1 : (c + 1) * cap ≤ c' * cap := Nat.mul_le_mul_right cap hgt
        rw [Nat.succ_mul] at h1; omega
    refine ⟨hcl, (hFrame _ (by omega) (Or.inl (by omega))).trans hcc, fun e he => ?_⟩
    have hAddr : after (walkPtrs + c' * cap + e) = mem (walkPtrs + c' * cap + e) := by
      rcases hdisj e (he.trans_le hcl) with h1 | h2
      · exact hFrame _ (by omega) (Or.inl (by omega))
      · exact hFrame _ (by omega) (Or.inr (by omega))
    obtain ⟨hlt, hseq⟩ := hcw e he
    rw [hAddr]
    exact ⟨hlt, seqAt_frame hseq fun a ha hb => hLt a (by omega)⟩

/-- `buildCollectRoundProc` meets `buildCollectRoundContract`. -/
theorem buildCollectRoundProc_meetsContract {w f fAppend : ℕ} {p : Program}
    {G : Graph} {start s k d coreCap lo hi rec : ℕ} {walks : ℕ → List (List ℕ)} {hole : Option ℕ}
    {preWalks : ℕ → List (List ℕ)}
    (hf : p.procs[f]? = some (buildCollectRoundProc fAppend))
    (hfA : p.procs[fAppend]? = some buildAppendRowWalksProc) :
    MeetsContract w p f
      (buildCollectRoundContract w G start s k d coreCap lo hi rec walks hole preWalks) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨walkCnt, walkPtrs, cap, rfl, hrec0, hs1, hhiLe, hArch, hWT, hCapAll, htop, hZF, hstW, hw4⟩ := hPre
  have hWT1 : walkCnt + k ≤ walkPtrs := hWT.1
  unfold RoundArchive at hArch
  rw [ite_eq_right hrec0] at hArch
  obtain ⟨prep, oldCount, act, numCuts, cutIdx, hlp, hpr, hhiEq, ho1, hok, hmp, hmo, hact,
    hactInj, hmnum, hnumLe, hcut, hcutInj, hRest⟩ := hArch
  refine runs_start_le ?_
  unfold buildCollectRoundProc
  refine runs_seq_assign_le (v := prep)
    (by rw [← hmp]; exact Expr.eval_load
          (Expr.eval_reg_of_eq (show (startState [rec, start, s, walkCnt, walkPtrs, cap] mem pos).regs 0 = rec from rfl))) ?_
  refine runs_seq_assign_le (v := oldCount)
    (by rw [← hmo]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_const (by omega)) (by omega))) ?_
  refine runs_seq_assign_le (v := numCuts)
    (by rw [← hmnum]; exact Expr.eval_load (Expr.eval_reg_of_eq (by simp))) ?_
  refine runs_seq_cond_le (v := numCuts) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · intro hnc
    rw [ite_eq_right hnc] at hRest
    obtain ⟨Ms, emb, routedEnd, hMlen, hRowLe, hloRep, hMemBatch, hRepEndLe, hEndRec, hRepAt, _, _,
      hPRec, _, hWalksAt, hWtAt, hWtOther, _⟩ := hRest
    let batch := prep + 1 + oldCount
    let rep := buildBatchEnd batch numCuts s
    let walkDir := routedEnd + 4
    have hRepEndLe' : rep + (routeResultWords (.matched Ms emb)).length ≤ routedEnd := hRepEndLe
    obtain ⟨hRep1, hMtOff, hTwoFlatLe⟩ := routeMatched_mt_offsets hRepAt
    have hRoW : routedEnd < 2 ^ w := by omega
    have hRepW : rep < 2 ^ w := by omega
    have hBatchW : batch < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
    have hWdW : walkDir < 2 ^ w := by dsimp [walkDir]; omega
    have hActCutInj : ∀ j₁ < numCuts, ∀ j₂ < numCuts,
        act (cutIdx j₁) = act (cutIdx j₂) → j₁ = j₂ := fun j₁ hj₁ j₂ hj₂ heq =>
      hcutInj j₁ hj₁ j₂ hj₂ (hactInj _ (hcut j₁ hj₁).1 _ (hcut j₂ hj₂).1 heq)
    let curWalksAt : ℕ → ℕ → List (List ℕ) := fun j c =>
      preWalks c ++ if ∃ j' < j, act (cutIdx j') = c then walks c else []
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := batch)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) hBatchW) ?_
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := rep)
      (by have h1 : numCuts + numCuts < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
          have h2 : batch + (numCuts + numCuts) < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
          have h3 : batch + (numCuts + numCuts) + 1 < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
          have h4 : numCuts * s < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
          have h5 : batch + (numCuts + numCuts) + 1 + numCuts * s = rep := by
            dsimp [rep, buildBatchEnd]; omega
          rw [← h5]
          exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) h1) h2)
            (Expr.eval_const (by omega)) h3)
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp))
              (Expr.eval_reg_of_eq (by simp [startState])) h4) (by rw [h5]; exact hRepW)) ?_
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := rep + 5)
      (by have h1 : rep + 4 + mem (rep + 1) = rep + 5 := by rw [hRep1]
          rw [← h1]
          exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
              (Expr.eval_const (by omega)) (by omega)))
            (by rw [h1]; omega)) ?_
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := walkDir)
      (by have h1 : mem batch + 4 = walkDir := by rw [hMemBatch]
          rw [← h1]
          exact Expr.eval_add (Expr.eval_load (Expr.eval_reg_of_eq (by simp)))
            (Expr.eval_const (by omega)) (by rw [h1]; exact hWdW)) ?_
    have hloop := Triple.forRange_const (w := w) (p := p) (r := 13) (lo := .const 0) (hi := .reg 8)
      (body :=
        .assign 14 (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 13))) ;;
        .assign 15 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 14))) ;;
        .assign 16 (.bin .div (.bin .sub (.reg 15) (.reg 1)) (.reg 2)) ;;
        .assign 17 (.bin .div (.load (.bin .add (.reg 11) (.reg 13))) (.const 2)) ;;
        .assign 18 (.bin .div (.load (.bin .add (.bin .add (.reg 11) (.reg 13)) (.const 1))) (.const 2)) ;;
        .call 19 fAppend [.reg 12, .reg 17, .reg 18, .reg 3, .reg 4, .reg 5, .reg 16])
      (P := fun st =>
        st.regs 0 = rec ∧ st.regs 1 = start ∧ st.regs 2 = s ∧
        st.regs 3 = walkCnt ∧ st.regs 4 = walkPtrs ∧ st.regs 5 = cap ∧
        st.regs 6 = prep ∧ st.regs 8 = numCuts ∧ st.regs 11 = rep + 5 ∧
        st.regs 12 = walkDir ∧ st.mem = mem)
      (Inv := fun j st =>
        st.regs 0 = rec ∧ st.regs 1 = start ∧ st.regs 2 = s ∧
        st.regs 3 = walkCnt ∧ st.regs 4 = walkPtrs ∧ st.regs 5 = cap ∧
        st.regs 6 = prep ∧ st.regs 8 = numCuts ∧ st.regs 11 = rep + 5 ∧
        st.regs 12 = walkDir ∧ st.regs 13 = j ∧
        WalkTableAt k walkCnt walkPtrs cap (curWalksAt j) st.mem ∧
        (∀ a < walkCnt, st.mem a = mem a) ∧ ZeroFrom st.mem (walkPtrs + k * cap))
      (32 * s + 130) 0 numCuts (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h8, h11, h12, hm⟩ => by
        refine ⟨by eval_expr, ?_⟩
        have hcur0 : curWalksAt 0 = preWalks := by funext c; simp [curWalksAt]
        refine ⟨by simpa using h0, by simpa using h1, by simpa using h2,
          by simpa using h3, by simpa using h4, by simpa using h5,
          by simpa using h6, by simpa using h8, by simpa using h11,
          by simpa using h12, by simp,
          by simpa [hm, hcur0] using hWT, fun _ _ => hm ▸ rfl, hm ▸ hZF⟩)
      (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.2.2.2.2.2.2.1])
      (fun j _ hj => by
        intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h8, h11, h12, h13, hWTj, hPresJ, hZFj⟩
        have hjM : j < Ms.length := hMlen.symm ▸ hj
        set idx := cutIdx j
        set c := act idx
        have hidxLt : idx < oldCount := (hcut j hj).1
        have hcLt : c < k := (hact idx hidxLt).1
        have hloE : flatIndex Ms j 0 ≤ flatIndex Ms (j + 1) 0 := by
          rw [flatIndex_succ_eq Ms hjM]; omega
        have hhiE : flatIndex Ms (j + 1) 0 ≤ Ms.flatten.length :=
          flatIndex_le_flatten Ms (Nat.succ_le_of_lt hjM)
        have hLenEq : flatIndex Ms (j + 1) 0 - flatIndex Ms j 0 = (Ms.getD j []).length := by
          rw [flatIndex_succ_eq Ms hjM]; omega
        have hMcut : st.mem (prep + 1 + j) = idx :=
          (hPresJ _ (by dsimp [rep, batch, buildBatchEnd] at hRepEndLe'; omega)).trans (hcut j hj).2
        have hMoff : st.mem (rec + 2 + idx) = start + c * s :=
          (hPresJ _ (by omega)).trans (hact idx hidxLt).2
        have hMmt0 : st.mem (rep + 5 + j) = 2 * flatIndex Ms j 0 :=
          (hPresJ _ (by omega)).trans (hMtOff j (Nat.le_of_lt hjM))
        have hMmt1 : st.mem (rep + 5 + j + 1) = 2 * flatIndex Ms (j + 1) 0 := by
          rw [show rep + 5 + j + 1 = rep + 5 + (j + 1) by omega]
          exact (hPresJ _ (by omega)).trans (hMtOff (j + 1) (Nat.succ_le_of_lt hjM))
        have hcsW : start + c * s < 2 ^ w := by
          have h1' : (c + 1) * s ≤ k * s := Nat.mul_le_mul_right s hcLt
          rw [Nat.succ_mul] at h1'; omega
        have hsW : s < 2 ^ w := by
          have h1' : 1 * s ≤ k * s := Nat.mul_le_mul_right s (by omega)
          omega
        have h2loW : 2 * flatIndex Ms j 0 < 2 ^ w := by omega
        have h2hiW : 2 * flatIndex Ms (j + 1) 0 < 2 ^ w := by omega
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := idx)
          (by rw [← hMcut]; exact Expr.eval_load (Expr.eval_add
                (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_const (by omega)) (by omega))
                (Expr.eval_reg_of_eq h13) (by dsimp [rep, batch, buildBatchEnd] at hRepEndLe'; omega))) ?_
        refine runs_seq_assign_le (v := start + c * s)
          (by rw [← hMoff]; exact Expr.eval_load (Expr.eval_add
                (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h0)) (Expr.eval_const (by omega)) (by omega))
                (Expr.eval_reg_of_eq (by simp)) (by omega))) ?_
        refine runs_seq_assign_le (v := c)
          (by have hsub : start + c * s - start = c * s := by omega
              have hdiv : (start + c * s - start) / s = c := by
                rw [hsub]; exact Nat.mul_div_cancel c (by omega)
              conv_rhs => rw [← hdiv]
              exact Expr.eval_div
                (Expr.eval_sub (Expr.eval_reg_of_eq (v := start + c * s) (by simp))
                  (Expr.eval_reg_of_eq (v := start) (by simpa using h1)) (by omega))
                (Expr.eval_reg_of_eq (v := s) (by simpa using h2)) (by omega)) ?_
        refine runs_seq_assign_le (v := flatIndex Ms j 0)
          (by have hdiv : 2 * flatIndex Ms j 0 / 2 = flatIndex Ms j 0 :=
                Nat.mul_div_right _ (by omega : 0 < 2)
              rw [← hdiv]
              exact Expr.eval_div
                (by rw [← hMmt0]; exact Expr.eval_load (Expr.eval_add
                      (Expr.eval_reg_of_eq (by simpa using h11))
                      (Expr.eval_reg_of_eq (by simpa using h13))
                      (by dsimp [rep, batch] at hPRec ⊢; omega)))
                (Expr.eval_const (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := flatIndex Ms (j + 1) 0)
          (by have hdiv : 2 * flatIndex Ms (j + 1) 0 / 2 = flatIndex Ms (j + 1) 0 :=
                Nat.mul_div_right _ (by omega : 0 < 2)
              rw [← hdiv]
              exact Expr.eval_div
                (by rw [← hMmt1]; exact Expr.eval_load (Expr.eval_add
                      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h11))
                        (Expr.eval_reg_of_eq (by simpa using h13))
                        (by dsimp [rep, batch] at hPRec ⊢; omega))
                      (Expr.eval_const (by omega))
                      (by dsimp [rep, batch] at hPRec ⊢; omega)))
                (Expr.eval_const (by omega)) (by omega)) ?_
        have hNotPrev : ¬ ∃ j' < j, act (cutIdx j') = c := by
          rintro ⟨j', hj', heq⟩
          have := hActCutInj j' (hj'.trans hj) j hj heq; omega
        have hCurC : curWalksAt j c = preWalks c := by simp [curWalksAt, hNotPrev]
        have hWalksLen : (walks c).length = (Ms.getD j []).length := by
          rw [hWtAt j hj, List.length_map, List.length_range]
        have hCapC : (curWalksAt j c).length + (walks c).length ≤ cap := by
          rw [hCurC]; exact hCapAll c hcLt
        have hck : (c + 1) * cap ≤ k * cap := Nat.mul_le_mul_right cap hcLt
        rw [Nat.succ_mul] at hck
        have hAppSpec := buildAppendRowWalksProc_meetsContract (w := w)
          (oldCnt := (curWalksAt j c).length) (ptrs := fun r => mem (walkDir + r)) hfA
        have hAppPre : (buildAppendRowWalksContract w (curWalksAt j c).length
            (fun r => mem (walkDir + r))).pre
            [walkDir, flatIndex Ms j 0, flatIndex Ms (j + 1) 0, walkCnt, walkPtrs, cap, c] st.mem := by
          refine ⟨walkDir, flatIndex Ms j 0, flatIndex Ms (j + 1) 0, walkCnt, walkPtrs, cap, c,
            rfl, hloE, (hWTj.2 c hcLt).2.1,
            fun r _ hr => hPresJ _ (by dsimp [walkDir]; omega),
            by dsimp [walkDir]; omega, by omega, by omega, by omega⟩
        refine runs_call_le hAppSpec
          (vs := [walkDir, flatIndex Ms j 0, flatIndex Ms (j + 1) 0, walkCnt, walkPtrs, cap, c])
          (by simp [evalArgs, Expr.eval, h12, h3, h4, h5])
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | hx | rfl
              · exact hWdW
              · omega
              · omega
              · omega
              · omega
              · rw [hx]; have : 1 * cap ≤ k * cap := Nat.mul_le_mul_right cap (by omega); omega
              · omega)
          hAppPre ?_
        intro rv mNext posNext hPostApp
        obtain ⟨_, _, _, _, _, _, _, heqA, hCntA, hWrA, hFrA⟩ := hPostApp
        simp only [List.cons.injEq, and_true] at heqA
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqA
        have hStepWT := walkTable_append (c := c) (extra := walks c) hWTj hcLt hCapC
          (by rw [hCntA, hLenEq, hWalksLen])
          (fun e he => by
            have he' : e < (Ms.getD j []).length := hWalksLen ▸ he
            have hwr := hWrA e (hLenEq.symm ▸ he')
            dsimp only; rw [hwr]; dsimp only; rw [← Nat.add_assoc]
            obtain ⟨_, hARec, hSeq⟩ := hWalksAt j hj e he'
            have hGetW : (walks c).getD e [] =
                erase G.edges ((matchingWalkRow Ms emb j).u e) ((matchingWalkRow Ms emb j).raw e) := by
              rw [hWtAt j hj, List.getD_eq_getElem _ _ (by simp; exact he'), List.getElem_map,
                List.getElem_range]
            rw [hGetW]
            exact ⟨by dsimp [walkDir]; omega,
              seqAt_frame hSeq fun a ha hb => hPresJ a (by dsimp [walkDir] at hb ⊢; omega)⟩)
          (fun a hne ha => hFrA a hne (by rw [hLenEq, ← hWalksLen]; exact ha))
        have hCurEq : (fun c' => if c' = c then curWalksAt j c' ++ walks c else curWalksAt j c') =
            curWalksAt (j + 1) := by
          funext c'
          by_cases hcc' : c' = c
          · rw [hcc']
            simp only [↓reduceIte, hCurC, curWalksAt]
            have hex : ∃ j' < j + 1, act (cutIdx j') = c := ⟨j, Nat.lt_succ_self j, rfl⟩
            rw [ite_eq_left hex]
          · simp only [hcc', ↓reduceIte, curWalksAt]
            have hiff : (∃ j' < j + 1, act (cutIdx j') = c') ↔ (∃ j' < j, act (cutIdx j') = c') := by
              constructor
              · rintro ⟨j', hj', he⟩
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hlt | rfl
                · exact ⟨j', hlt, he⟩
                · exact (hcc' he.symm).elim
              · rintro ⟨j', hj', he⟩; exact ⟨j', Nat.lt_succ_of_lt hj', he⟩
            simp only [hiff]
        refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
          by simpa using h3, by simpa using h4, by simpa using h5,
          by simpa using h6, by simpa using h8, by simpa using h11,
          by simpa using h12, by simp,
          by rw [hCurEq] at hStepWT; exact hStepWT.1,
          fun a ha => (hStepWT.2.1 a ha).trans (hPresJ a ha),
          fun a ha => (hStepWT.2.2 a ha).trans (hZFj a ha)⟩, by simp [h13]⟩, ?_⟩
        simp only [buildAppendRowWalksContract, List.getD_cons_succ, List.getD_cons_zero,
          Expr.size, argsSize]
        have hrl := hRowLe j hj
        omega)
    refine runs_seq_triple_le hloop
      ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
       by simp [startState], by simp [startState], by simp, by simp, by simp, by simp, rfl⟩ ?_
    intro st8 ⟨_, _, _, _, _, _, _, _, _, _, _, hWTend, hPresEnd, hZFend⟩
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · refine ⟨walkCnt, walkPtrs, cap, rfl, ?_, hPresEnd, hZFend⟩
      refine ⟨hWTend.1, fun c hc => ?_⟩
      have hEqC : curWalksAt numCuts c = preWalks c ++ walks c := by
        dsimp [curWalksAt]
        by_cases hex : ∃ j' < numCuts, act (cutIdx j') = c
        · simp [hex]
        · push Not at hex
          rw [ite_eq_right (by push Not; exact hex), hWtOther c hc hex]
      simpa only [hEqC] using hWTend.2 c hc
    · simp only [buildCollectRoundContract, Expr.size, Nat.sub_zero]
      have hnorm : 32 * s + 130 + 1 + 8 = 32 * s + 139 := by omega
      rw [hnorm]
      have hnk : numCuts ≤ k := hnumLe.trans hok
      have hmul : numCuts * (32 * s + 139) ≤ k * (32 * s + 139) := Nat.mul_le_mul_right _ hnk
      have hexp : k * (32 * s + 139) = 32 * (s * k) + 139 * k := by ring
      omega
  · intro hnc
    rw [ite_eq_left hnc] at hRest
    obtain ⟨hEmptyW, _, _⟩ := hRest
    refine runs_seq_nop_le ?_
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · refine ⟨walkCnt, walkPtrs, cap, rfl, ?_, fun _ _ => rfl, hZF⟩
      have heq : (fun c => preWalks c ++ walks c) = preWalks := by
        funext c; simp [hEmptyW c]
      rwa [heq]
    · simp only [buildCollectRoundContract, Expr.size]
      omega


end MinCostFlow.HierPaths
