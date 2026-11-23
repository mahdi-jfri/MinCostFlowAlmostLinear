module

public import MinCostFlow.MinRatio.WireSelectQuery
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Verification of in-place opposite-pair cancellation on explicit cycle edges

Verifies `cancelEdgesFindOppBody` and `cancelRouteEdgesLoopBody` (`WireSelectQuery.lean`):
1. `swapRemove` and its permutation/length/lookup/flow lemmas (`swapRemove_perm`,
   `swapRemove_pair_props`): removing an opposite-orientation pair `(e, b)` and `(e, !b)` via
   swap-with-last preserves the signed off-tree flow `∑ x ∈ edges, walkFlow [x] ei` on every edge,
   keeps all remaining entries in the original list, and leaves the prefix `[0 .. i - 1]` intact.
2. `cancelEdgesFindOpp_runs`: scans `edgesBase[j .. len - 1]` read-only in at most
   `50 * (len - j) + 10` steps.
3. `cancelRouteEdgesLoop_runs` and `cancelRouteEdges_runs`: cancels all opposite-orientation pairs
   in place in `[edgesBase, edgesBase + 2 * len)` and updates `mem[descBase + 3]`, using `0`
   scratch words and at most `cancelRouteEdgesCost len = 50 * len * len + 150 * len + 20` steps,
   producing `NoOppositePairs edges'`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-! ## 1. Pure swap-remove algebra -/

/-- Remove index `idx` from `l` by moving the last element into slot `idx` (when `idx + 1 < l.length`)
and dropping the last element. -/
def swapRemove (l : List (ℕ × Bool)) (idx : ℕ) : List (ℕ × Bool) :=
  if idx < l.dropLast.length then
    l.dropLast.set idx (l.getD l.dropLast.length (0, false))
  else
    l.dropLast

lemma swapRemove_length {l : List (ℕ × Bool)} {idx : ℕ} (_ : idx < l.length) :
    (swapRemove l idx).length = l.length - 1 := by
  unfold swapRemove; split_ifs <;> simp

lemma swapRemove_getElem {l : List (ℕ × Bool)} {idx k : ℕ}
    (h : idx < l.length) (hk : k < (swapRemove l idx).length) :
    (swapRemove l idx)[k]'hk =
      if k = idx then l[l.length - 1]'(by omega) else l[k]'(by
        have hlen := swapRemove_length h; omega) := by
  have hlen : (swapRemove l idx).length = l.length - 1 := swapRemove_length h
  have hlt : k < l.length - 1 := hlen ▸ hk
  unfold swapRemove
  by_cases hidx : idx < l.dropLast.length
  · simp only [hidx, ↓reduceIte]
    by_cases hkeq : k = idx
    · subst hkeq
      simp only [↓reduceIte, List.getElem_set_self, List.length_dropLast]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    · simp only [hkeq, ↓reduceIte]
      rw [List.getElem_set_ne (Ne.symm hkeq)]
      exact List.getElem_dropLast (by simp; omega)
  · simp only [hidx, ↓reduceIte]
    simp only [List.length_dropLast] at hidx
    have hkne : k ≠ idx := by omega
    simp only [hkne, ↓reduceIte]
    exact List.getElem_dropLast (by simp; omega)

lemma swapRemove_perm {l : List (ℕ × Bool)} {idx : ℕ} (h : idx < l.length) :
    (l[idx]'h :: swapRemove l idx).Perm l := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  have hsplit : l = l.dropLast ++ [l[l.length - 1]'(by omega)] := by
    have h1 := (List.dropLast_append_getLast hne).symm
    rwa [List.getLast_eq_getElem] at h1
  set y := l[l.length - 1]'(by omega)
  set l' := l.dropLast
  have hl'len : l'.length = l.length - 1 := List.length_dropLast
  have hyD : l.getD l'.length (0, false) = y := by
    rw [List.getD_eq_getElem?_getD, hl'len, List.getElem?_eq_getElem (by omega)]; rfl
  unfold swapRemove
  split_ifs with hidx
  · have hidx' : idx < l'.length := hidx
    have hli : l[idx]'h = l'[idx]'hidx' := (List.getElem_dropLast (by omega)).symm
    have hset_eq : l'.set idx y = l'.take idx ++ y :: l'.drop (idx + 1) := by
      have hlenEq : (l'.set idx y).length = (l'.take idx ++ y :: l'.drop (idx + 1)).length := by
        simp only [List.length_set, List.length_append, List.length_take, List.length_cons,
          List.length_drop, Nat.min_eq_left (Nat.le_of_lt hidx')]
        omega
      refine List.ext_getElem hlenEq fun k hk1 hk2 => ?_
      have htk : (l'.take idx).length = idx := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx')]
      by_cases hki : k = idx
      · subst hki; simp only [List.getElem_set_self]
        rw [List.getElem_append_right (by rw [htk])]; simp [htk]
      · rw [List.getElem_set_ne (Ne.symm hki)]
        by_cases hklt : k < idx
        · rw [List.getElem_append_left (by rw [htk]; exact hklt), List.getElem_take]
        · rw [List.getElem_append_right (by rw [htk]; omega)]
          have hsub : k - (l'.take idx).length = (k - idx - 1) + 1 := by rw [htk]; omega
          simp only [hsub, List.getElem_cons_succ, List.getElem_drop]; congr 1; omega
    have hl'_eq : l' = l'.take idx ++ l'[idx]'hidx' :: l'.drop (idx + 1) := by
      have h1 := (List.take_append_drop idx l').symm
      rwa [List.drop_eq_getElem_cons hidx'] at h1
    change (l[idx]'h :: l'.set idx (l.getD l'.length (0, false))).Perm l
    rw [hyD, hset_eq, hli]
    conv_rhs => rw [hsplit, hl'_eq]
    exact List.perm_middle.symm.trans ((List.Perm.append_left _ (List.Perm.swap _ _ _)).trans
      (List.perm_middle.trans (List.perm_append_singleton _ _).symm))
  · have hidx_eq : idx = l.length - 1 := by have : ¬ idx < l'.length := hidx; omega
    have hli : l[idx]'h = y := by simp [y, hidx_eq]
    rw [hli]; conv_rhs => rw [hsplit]
    exact (List.perm_append_singleton _ _).symm

lemma swapRemove_pair_props {l : List (ℕ × Bool)} {i j : ℕ}
    (hij : i < j) (hj : j < l.length)
    (hopp : l[j]'hj = ((l[i]'(hij.trans hj)).1, !(l[i]'(hij.trans hj)).2)) :
    let l₁ := swapRemove l j
    let l₂ := swapRemove l₁ i
    l₂.length = l.length - 2 ∧
    (∀ k (hk : k < i), l₂[k]'(by
        have h1 : l₁.length = l.length - 1 := swapRemove_length hj
        have h2 : l₂.length = l₁.length - 1 := swapRemove_length (by omega)
        omega) = l[k]'(by omega)) ∧
    (∀ x ∈ l₂, x ∈ l) ∧
    (∀ ei : ℕ, (l₂.map fun x => walkFlow [x] ei).sum = (l.map fun x => walkFlow [x] ei).sum) := by
  intro l₁ l₂
  have hl₁len : l₁.length = l.length - 1 := swapRemove_length hj
  have hi₁ : i < l₁.length := by omega
  have hl₂len : l₂.length = l.length - 2 := by
    have h2 : l₂.length = l₁.length - 1 := swapRemove_length hi₁; omega
  have hl₁i : l₁[i]'hi₁ = l[i]'(hij.trans hj) := by
    rw [swapRemove_getElem hj hi₁]; simp [Nat.ne_of_lt hij]
  have hperm : (l[j]'hj :: l[i]'(hij.trans hj) :: l₂).Perm l := by
    have hp1 : (l₁[i]'hi₁ :: l₂).Perm l₁ := swapRemove_perm hi₁
    rw [hl₁i] at hp1
    exact (List.Perm.cons (l[j]'hj) hp1).trans (swapRemove_perm hj)
  refine ⟨hl₂len, ?_, ?_, ?_⟩
  · intro k hk
    have hk₁ : k < l₁.length := by omega
    have hk₂ : k < l₂.length := by omega
    rw [swapRemove_getElem hi₁ hk₂, ite_eq_right (Nat.ne_of_lt hk),
        swapRemove_getElem hj hk₁, ite_eq_right (by omega)]
  · intro x hx
    exact hperm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  · intro ei
    have hsum := (hperm.map fun x => walkFlow [x] ei).sum_eq
    simp only [List.map_cons, List.sum_cons] at hsum
    have hcancel : walkFlow [l[j]'hj] ei + walkFlow [l[i]'(hij.trans hj)] ei = 0 := by
      rw [hopp]
      cases hdir : (l[i]'(hij.trans hj)).2 <;> simp [walkFlow, hdir] <;> split_ifs <;> ring
    linarith

/-! ## 2. `ExplicitEdgesAt` update helper for swap-remove -/

private lemma explicitEdgesAt_swapRemove {mem mem' : ℕ → ℕ} {edgesBase idx : ℕ}
    {l : List (ℕ × Bool)} (hEd : ExplicitEdgesAt mem edgesBase l) (hidx : idx < l.length)
    (hupd :
      if idx < l.length - 1 then
        mem' (edgesBase + 2 * idx) = mem (edgesBase + 2 * (l.length - 1)) ∧
        mem' (edgesBase + 2 * idx + 1) = mem (edgesBase + 2 * (l.length - 1) + 1) ∧
        ∀ a, a ≠ edgesBase + 2 * idx → a ≠ edgesBase + 2 * idx + 1 → mem' a = mem a
      else
        mem' = mem) :
    ExplicitEdgesAt mem' edgesBase (swapRemove l idx) := by
  intro k hk
  have hlen : (swapRemove l idx).length = l.length - 1 := swapRemove_length hidx
  have hk' : k < (swapRemove l idx).length := by simpa only [List.length_map] using hk
  simp only [List.getElem_map]
  rw [swapRemove_getElem hidx hk']
  by_cases hlt : idx < l.length - 1
  · simp only [hlt, ↓reduceIte] at hupd
    by_cases hkeq : k = idx
    · subst hkeq; simp only [↓reduceIte]
      have hlast := hEd.read (show l.length - 1 < l.length by omega)
      exact ⟨hupd.1.trans hlast.1, hupd.2.1.trans hlast.2⟩
    · simp only [hkeq, ↓reduceIte]
      have hkorig := hEd.read (show k < l.length by omega)
      exact ⟨(hupd.2.2 _ (by omega) (by omega)).trans hkorig.1,
             (hupd.2.2 _ (by omega) (by omega)).trans hkorig.2⟩
  · simp only [hlt, ↓reduceIte] at hupd; subst hupd
    have hkne : k ≠ idx := by omega
    simp only [hkne, ↓reduceIte]
    exact hEd.read (show k < l.length by omega)

private lemma pair_match_iff (x : ℕ × Bool) (e : ℕ) (b : Bool) :
    (x.1 = e ∧ (if x.2 then 1 else 0) + (if b then 1 else 0) = 1) ↔ x = (e, !b) := by
  rcases x with ⟨eid, dir⟩; cases dir <;> cases b <;> simp

/-! ## 3. Verification of `cancelEdgesFindOppBody` -/

/-- `cancelEdgesFindOppBody` scans `edgesBase[j .. edges.length - 1]` read-only in at most
`50 * (edges.length - j) + 10` steps, returning the first index `res < edges.length` with
`edges[res] = (e, !b)` or `edges.length` if none exists. -/
theorem cancelEdgesFindOpp_runs {w findOpp edgesBase : ℕ} {p : Program} {ω : ℕ → Bool}
    {edges : List (ℕ × Bool)} {e : ℕ} {b : Bool} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w)
    (hpFind : p.procs[findOpp]? = some (cancelEdgesFindOppBody findOpp))
    (hEd : ExplicitEdgesAt mem edgesBase edges)
    (hEdW : ∀ x ∈ edges, x.1 < 2 ^ w)
    (_heW : e < 2 ^ w)
    (hAddrW : edgesBase + 2 * edges.length < 2 ^ w) :
    ∀ (rem j pos : ℕ), j ≤ edges.length → edges.length - j = rem →
      ∃ (res c : ℕ) (st' : State),
        Runs w p ω (cancelEdgesFindOppBody findOpp)
          (startState [edgesBase, edges.length, e, if b then 1 else 0, j] mem pos)
          (.returned res) st' c ∧
        st'.mem = mem ∧
        j ≤ res ∧ res ≤ edges.length ∧
        (∀ hlt : res < edges.length, edges[res]'hlt = (e, !b)) ∧
        (res = edges.length → ∀ k (hk : k < edges.length), j ≤ k → edges[k]'hk ≠ (e, !b)) ∧
        c ≤ 50 * rem + 10 := by
  intro rem
  induction rem with
  | zero =>
    intro j pos hj hrem
    have hjeq : j = edges.length := by omega
    subst hjeq
    let s0 := startState [edgesBase, edges.length, e, if b then 1 else 0, edges.length] mem pos
    have rRet : Runs w p ω (.ret (.reg 1)) s0 (.returned edges.length) s0 2 :=
      runs_ret_iff.mpr ⟨edges.length, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
    have rCond : Runs w p ω (cancelEdgesFindOppBody findOpp) s0 (.returned edges.length) s0 _ :=
      runs_cond_iff.mpr ⟨0, 2,
        by simp [Expr.eval, BinOp.eval, s0, startState, show 0 < 2 ^ w by omega],
        by simp only [↓reduceIte]; exact rRet, rfl⟩
    exact ⟨edges.length, _, s0, rCond, rfl, le_rfl, le_rfl,
      fun hlt => absurd hlt (lt_irrefl _), fun _ k hk hle => by omega, by simp [Expr.size]⟩
  | succ rem ih =>
    intro j pos hj hrem
    have hjlt : j < edges.length := by omega
    have hread := hEd.read hjlt
    set ej := (edges[j]'hjlt).1
    set bj := (edges[j]'hjlt).2
    set dj : ℕ := if bj then 1 else 0
    set d : ℕ := if b then 1 else 0
    have hejW : ej < 2 ^ w := hEdW _ (List.getElem_mem hjlt)
    have hdjW : dj < 2 ^ w := by dsimp only [dj]; split_ifs <;> omega
    have hdW : d < 2 ^ w := by dsimp only [d]; split_ifs <;> omega
    have hdj_addW : dj + d < 2 ^ w := by dsimp only [dj, d]; split_ifs <;> omega
    have hj1W : j + 1 < 2 ^ w := by omega
    have h2jW : 2 * j < 2 ^ w := by omega
    have ha0W : edgesBase + 2 * j < 2 ^ w := by omega
    have ha1W : edgesBase + 2 * j + 1 < 2 ^ w := by omega
    have hMatchIff : (ej = e ∧ dj + d = 1) ↔ edges[j]'hjlt = (e, !b) :=
      pair_match_iff (edges[j]'hjlt) e b
    let s0 := startState [edgesBase, edges.length, e, d, j] mem pos
    let rg5 := Function.update s0.regs 5 ej
    let rg6 := Function.update rg5 6 dj
    let st6 : State := ⟨mem, rg6, pos⟩
    have rA5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))))
        s0 .normal ⟨mem, rg5, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨ej, by
        simp [Expr.eval, BinOp.eval, s0, startState, show 2 < 2 ^ w by omega, h2jW, ha0W, hread.1, ej],
        rfl, rfl, rfl⟩
    have rA6 : Runs w p ω
        (.assign 6 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4))) (.const 1))))
        ⟨mem, rg5, pos⟩ .normal st6 9 :=
      runs_assign_iff.mpr ⟨dj, by
        simp [Expr.eval, BinOp.eval, rg5, s0, startState, show 1 < 2 ^ w by omega,
          show 2 < 2 ^ w by omega, h2jW, ha0W, ha1W, hread.2, dj, bj],
        rfl, rfl, rfl⟩
    let sInnerCond : Stmt :=
      .cond (.bin .eq (.bin .add (.reg 6) (.reg 3)) (.const 1)) (.ret (.reg 4)) .nop
    let sOuterCond : Stmt := .cond (.bin .eq (.reg 5) (.reg 2)) sInnerCond .nop
    let sTail : Stmt :=
      .call 7 findOpp [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1)] ;; .ret (.reg 7)
    let sThen : Stmt :=
      .assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))) ;;
      .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
      sOuterCond ;; sTail
    by_cases hhit : edges[j]'hjlt = (e, !b)
    · obtain ⟨hejEq, hsumEq⟩ := hMatchIff.mpr hhit
      have rRetJ : Runs w p ω (.ret (.reg 4)) st6 (.returned j) st6 2 :=
        runs_ret_iff.mpr ⟨j, by simp [Expr.eval, st6, rg6, rg5, s0, startState], rfl, rfl, rfl⟩
      have rIn : Runs w p ω sInnerCond st6 (.returned j) st6 _ :=
        runs_cond_iff.mpr ⟨1, 2,
          by simp [Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState,
            show 1 < 2 ^ w by omega, hsumEq],
          by simp only [one_ne_zero, ↓reduceIte]; exact rRetJ, rfl⟩
      have rOut : Runs w p ω sOuterCond st6 (.returned j) st6 _ :=
        runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState, hejEq, show 1 < 2 ^ w by omega],
          by simp only [one_ne_zero, ↓reduceIte]; exact rIn, rfl⟩
      have rSeqOut : Runs w p ω (sOuterCond ;; sTail) st6 (.returned j) st6 _ :=
        runs_seq_iff.mpr (Or.inl ⟨j, _, rOut, rfl, rfl⟩)
      have rThen : Runs w p ω sThen s0 (.returned j) st6 _ :=
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA5, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA6, rSeqOut, rfl⟩), rfl⟩)
      have rFull : Runs w p ω (cancelEdgesFindOppBody findOpp) s0 (.returned j) st6 _ :=
        runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, s0, startState, hjlt, show 1 < 2 ^ w by omega],
          by simp only [one_ne_zero, ↓reduceIte]; exact rThen, rfl⟩
      exact ⟨j, _, st6, rFull, rfl, le_rfl, Nat.le_of_lt hjlt,
        fun _ => hhit, fun heq => absurd heq (Nat.ne_of_lt hjlt), by simp [Expr.size]; omega⟩
    · have hnotPair : ¬ (ej = e ∧ dj + d = 1) := fun h => hhit (hMatchIff.mp h)
      obtain ⟨res, cRec, stRec, hrRec, hmemRec, hresLo, hresHi, hresHit, hresMiss, hcRec⟩ :=
        ih (j + 1) pos (by omega) (by omega)
      have rOutNop : ∃ cOut, Runs w p ω sOuterCond st6 .normal st6 cOut ∧ cOut ≤ 14 := by
        by_cases hejEq : ej = e
        · have hsumNe : dj + d ≠ 1 := fun hs => hnotPair ⟨hejEq, hs⟩
          have rIn : Runs w p ω sInnerCond st6 .normal st6 _ :=
            runs_cond_iff.mpr ⟨0, 1,
              by simp [Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState,
                show 1 < 2 ^ w by omega, hdj_addW, hsumNe, show 0 < 2 ^ w by omega],
              by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have rOut : Runs w p ω sOuterCond st6 .normal st6 _ :=
            runs_cond_iff.mpr ⟨1, _,
              by simp [Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState, hejEq, show 1 < 2 ^ w by omega],
              by simp only [one_ne_zero, ↓reduceIte]; exact rIn, rfl⟩
          exact ⟨_, rOut, by simp [Expr.size]⟩
        · have rOut : Runs w p ω sOuterCond st6 .normal st6 _ :=
            runs_cond_iff.mpr ⟨0, 1,
              by simp [Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState, hejEq, show 0 < 2 ^ w by omega],
              by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          exact ⟨_, rOut, by simp [Expr.size]⟩
      obtain ⟨cOut, rOut, hcOut⟩ := rOutNop
      let rg7 := Function.update rg6 7 res
      have rCall : Runs w p ω
          (.call 7 findOpp [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1)])
          st6 .normal ⟨stRec.mem, rg7, stRec.pos⟩ (cRec + 8) := by
        refine runs_call_iff.mpr ⟨[edgesBase, edges.length, e, d, j + 1], _, .returned res,
          stRec, cRec, ?_, hpFind, hrRec, rfl, rfl, ?_⟩
        · simp [evalArgs, Expr.eval, BinOp.eval, st6, rg6, rg5, s0, startState,
            show 1 < 2 ^ w by omega, hj1W]
        · simp [argsSize, Expr.size]; omega
      have rRet : Runs w p ω (.ret (.reg 7))
          ⟨stRec.mem, rg7, stRec.pos⟩ (.returned res) ⟨stRec.mem, rg7, stRec.pos⟩ 2 :=
        runs_ret_iff.mpr ⟨res, by simp [Expr.eval, rg7], rfl, rfl, rfl⟩
      have rTail : Runs w p ω sTail st6 (.returned res) ⟨stRec.mem, rg7, stRec.pos⟩ _ :=
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCall, rRet, rfl⟩)
      have rThen : Runs w p ω sThen s0 (.returned res) ⟨stRec.mem, rg7, stRec.pos⟩ _ :=
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA5, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA6,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rOut, rTail, rfl⟩), rfl⟩), rfl⟩)
      have rFull : Runs w p ω (cancelEdgesFindOppBody findOpp)
          s0 (.returned res) ⟨stRec.mem, rg7, stRec.pos⟩ _ :=
        runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, s0, startState, hjlt, show 1 < 2 ^ w by omega],
          by simp only [one_ne_zero, ↓reduceIte]; exact rThen, rfl⟩
      refine ⟨res, _, ⟨stRec.mem, rg7, stRec.pos⟩, rFull, hmemRec, by omega, hresHi, hresHit, ?_, ?_⟩
      · intro hresEq k hk hjk
        by_cases hkj : k = j
        · subst hkj; exact hhit
        · exact hresMiss hresEq k hk (by omega)
      · simp only [Expr.size]; omega

/-! ## 4. Verification of `cancelRouteEdgesLoopBody` -/

/-- One conditional swap-remove block (moves slot `rLast` into `rSlot` when `rSlot < rLast`). -/
private def swapStmt (rSlot rLast : ℕ) : Stmt :=
  .cond (.bin .lt (.reg rSlot) (.reg rLast))
    (.assign 8 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rLast)))) ;;
     .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rLast))) (.const 1))) ;;
     .store (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rSlot))) (.reg 8) ;;
     .store (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rSlot))) (.const 1)) (.reg 9))
    .nop

/-- Helper executing `swapStmt rSlot rLast`. -/
private lemma swapBlock_runs {w edgesBase slotIdx lastIdx rSlot rLast : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 < 2 ^ w)
    (h0 : regs 0 = edgesBase) (hS : regs rSlot = slotIdx) (hL : regs rLast = lastIdx)
    (hAddrW : edgesBase + 2 * (lastIdx + 1) < 2 ^ w)
    (hrS8 : rSlot ≠ 8) (hrS9 : rSlot ≠ 9) (hrL8 : rLast ≠ 8) :
    ∃ (mem' : ℕ → ℕ) (regs' : ℕ → ℕ) (c : ℕ),
      Runs w p ω (swapStmt rSlot rLast)
        ⟨mem, regs, pos⟩ .normal ⟨mem', regs', pos⟩ c ∧
      (∀ r, r ≠ 8 → r ≠ 9 → regs' r = regs r) ∧
      (if slotIdx < lastIdx then
        mem' (edgesBase + 2 * slotIdx) = mem (edgesBase + 2 * lastIdx) ∧
        mem' (edgesBase + 2 * slotIdx + 1) = mem (edgesBase + 2 * lastIdx + 1) ∧
        ∀ a, a ≠ edgesBase + 2 * slotIdx → a ≠ edgesBase + 2 * slotIdx + 1 → mem' a = mem a
       else
        mem' = mem) ∧
      c ≤ 40 := by
  by_cases hlt : slotIdx < lastIdx
  · set v1 := mem (edgesBase + 2 * lastIdx)
    set v2 := mem (edgesBase + 2 * lastIdx + 1)
    let r1 := Function.update regs 8 v1
    let r2 := Function.update r1 9 v2
    let m1 := Function.update mem (edgesBase + 2 * slotIdx) v1
    let m2 := Function.update m1 (edgesBase + 2 * slotIdx + 1) v2
    have h2LW : 2 * lastIdx < 2 ^ w := by omega
    have h2SW : 2 * slotIdx < 2 ^ w := by omega
    have haL0 : edgesBase + 2 * lastIdx < 2 ^ w := by omega
    have haL1 : edgesBase + 2 * lastIdx + 1 < 2 ^ w := by omega
    have haS0 : edgesBase + 2 * slotIdx < 2 ^ w := by omega
    have haS1 : edgesBase + 2 * slotIdx + 1 < 2 ^ w := by omega
    have s1 : Runs w p ω
        (.assign 8 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rLast)))))
        ⟨mem, regs, pos⟩ .normal ⟨mem, r1, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨v1, by
        simp [Expr.eval, BinOp.eval, h0, hL, show 2 < 2 ^ w by omega, h2LW, haL0, v1], rfl, rfl, rfl⟩
    have s2 : Runs w p ω
        (.assign 9 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rLast))) (.const 1))))
        ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 9 :=
      runs_assign_iff.mpr ⟨v2, by
        simp [Expr.eval, BinOp.eval, r1, h0, hL, hrL8, show 1 < 2 ^ w by omega,
          show 2 < 2 ^ w by omega, h2LW, haL0, haL1, v2], rfl, rfl, rfl⟩
    have s3 : Runs w p ω
        (.store (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rSlot))) (.reg 8))
        ⟨mem, r2, pos⟩ .normal ⟨m1, r2, pos⟩ 7 :=
      runs_store_iff.mpr ⟨edgesBase + 2 * slotIdx, v1,
        by simp [Expr.eval, BinOp.eval, r2, r1, h0, hS, hrS8, hrS9, show 2 < 2 ^ w by omega, h2SW, haS0],
        by simp [Expr.eval, r2, r1], rfl, rfl, rfl⟩
    have s4 : Runs w p ω
        (.store (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg rSlot))) (.const 1)) (.reg 9))
        ⟨m1, r2, pos⟩ .normal ⟨m2, r2, pos⟩ 9 :=
      runs_store_iff.mpr ⟨edgesBase + 2 * slotIdx + 1, v2,
        by simp [Expr.eval, BinOp.eval, r2, r1, h0, hS, hrS8, hrS9,
          show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega, h2SW, haS0, haS1],
        by simp [Expr.eval, r2], rfl, rfl, rfl⟩
    have rBody := runs_seq_iff.mpr (Or.inr ⟨_, _, _, s1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, s2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, s3, s4, rfl⟩), rfl⟩), rfl⟩)
    have rCond : Runs w p ω (swapStmt rSlot rLast) ⟨mem, regs, pos⟩ .normal ⟨m2, r2, pos⟩ _ :=
      runs_cond_iff.mpr ⟨1, _,
        by simp [Expr.eval, BinOp.eval, hS, hL, hlt, show 1 < 2 ^ w by omega],
        by simp only [one_ne_zero, ↓reduceIte]; exact rBody, rfl⟩
    refine ⟨m2, r2, _, rCond, ?_, ?_, by simp [Expr.size]⟩
    · intro r hr8 hr9
      simp [r2, r1, Function.update_of_ne hr9, Function.update_of_ne hr8]
    · simp only [hlt, ↓reduceIte]
      refine ⟨by simp [m2, m1],
              by simp [m2], fun a ha1 ha2 => by simp [m2, m1, ha1, ha2]⟩
  · have rCond : Runs w p ω (swapStmt rSlot rLast) ⟨mem, regs, pos⟩ .normal ⟨mem, regs, pos⟩ _ :=
      runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, hS, hL, hlt, show 0 < 2 ^ w by omega],
        by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨mem, regs, _, rCond, fun _ _ _ => rfl, by simp only [hlt, ↓reduceIte], by simp [Expr.size]⟩

/-- In-place opposite-pair cancellation loop invariant & correctness:
cancels all opposite-orientation pairs in `edges` in place in `[edgesBase, edgesBase + 2 * edges.length)`
and writes the resulting length to `mem[descBase + 3]`, using `0` scratch words and at most
`(edges.length - i) * (50 * maxLen + 150) + 20` steps. -/
theorem cancelRouteEdgesLoop_runs {w cancelEdges findOpp edgesBase descBase maxLen : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hw16 : 16 < 2 ^ w)
    (hpLoop : p.procs[cancelEdges]? = some (cancelRouteEdgesLoopBody cancelEdges findOpp))
    (hpFind : p.procs[findOpp]? = some (cancelEdgesFindOppBody findOpp))
    (hDisj : descBase + 3 < edgesBase)
    (hAddrW : edgesBase + 2 * maxLen < 2 ^ w) :
    ∀ (rem : ℕ) (i pos : ℕ) (mem : ℕ → ℕ) (edges : List (ℕ × Bool)),
      edges.length ≤ maxLen →
      (hiLe : i ≤ edges.length) →
      edges.length - i = rem →
      mem (descBase + 3) = edges.length →
      ExplicitEdgesAt mem edgesBase edges →
      (∀ x ∈ edges, x.1 < 2 ^ w) →
      (∀ k (hk : k < i) m (hm : m < edges.length),
        edges[k]'(by omega) ≠ ((edges[m]'hm).1, !(edges[m]'hm).2)) →
      ∃ (c : ℕ) (st' : State) (edges' : List (ℕ × Bool)),
        Runs w p ω (cancelRouteEdgesLoopBody cancelEdges findOpp)
          (startState [edgesBase, descBase, i] mem pos) (.returned 0) st' c ∧
        edges'.length ≤ edges.length ∧
        st'.mem (descBase + 3) = edges'.length ∧
        ExplicitEdgesAt st'.mem edgesBase edges' ∧
        NoOppositePairs edges' ∧
        (∀ x ∈ edges', x ∈ edges) ∧
        (∀ ei : ℕ, (edges'.map fun x => walkFlow [x] ei).sum =
          (edges.map fun x => walkFlow [x] ei).sum) ∧
        (∀ a, a ≠ descBase + 3 → (a < edgesBase ∨ edgesBase + 2 * edges.length ≤ a) →
          st'.mem a = mem a) ∧
        c ≤ rem * (50 * maxLen + 150) + 20 := by
  intro rem
  induction rem using Nat.strong_induction_on with
  | h rem ih =>
    intro i pos mem edges hLenLe hiLe hrem hDescLen hEd hEdW hClean
    have hdb3W : descBase + 3 < 2 ^ w := by omega
    have hlenW : edges.length < 2 ^ w := by omega
    by_cases hrem0 : rem = 0
    · have hieq : i = edges.length := by omega
      subst hieq
      have hrun : ∃ o st' c, Runs w p ω (cancelRouteEdgesLoopBody cancelEdges findOpp)
          (startState [edgesBase, descBase, edges.length] mem pos) o st' c ∧
          (o = .returned 0 ∧ st'.mem = mem) ∧ c ≤ 20 := by
        apply runs_start_le (T := 20)
        unfold cancelRouteEdgesLoopBody
        refine runs_seq_assign_flat (v := edges.length)
          (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, hdb3W, hDescLen]) ?_
        refine WordRAM.runs_cond_le (v := 0)
          (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega])
          (fun h => absurd rfl h) ?_
        intro _
        refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, rfl⟩ ?_
        simp [Expr.size]
      obtain ⟨o, st', c, hr, ⟨rfl, hmem⟩, hc⟩ := hrun
      have hNoOpp : NoOppositePairs edges := by
        intro x hx hmemOpp
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        obtain ⟨m, hm, hmEq⟩ := List.mem_iff_getElem.mp hmemOpp
        have hne := hClean k hk m hm
        rcases he : edges[k]'hk with ⟨eid, dir⟩
        rw [he] at hmEq hne; rw [hmEq] at hne
        cases dir <;> simp at hne
      exact ⟨c, st', edges, hr, le_rfl, hmem ▸ hDescLen, hmem ▸ hEd, hNoOpp,
        fun _ h => h, fun _ => rfl, fun _ _ _ => congrFun hmem _, by omega⟩
    · have hilt : i < edges.length := by omega
      have hreadI := hEd.read hilt
      set ei := (edges[i]'hilt).1
      set bi := (edges[i]'hilt).2
      set di : ℕ := if bi then 1 else 0
      have heiW : ei < 2 ^ w := hEdW _ (List.getElem_mem hilt)
      have hdiW : di < 2 ^ w := by dsimp only [di]; split_ifs <;> omega
      have h2iW : 2 * i < 2 ^ w := by omega
      have haI0 : edgesBase + 2 * i < 2 ^ w := by omega
      have haI1 : edgesBase + 2 * i + 1 < 2 ^ w := by omega
      have hi1W : i + 1 < 2 ^ w := by omega
      obtain ⟨j, cFind, stFind, hrFind, hmemFind, hjLo, hjHi, hjHit, hjMiss, hcFind⟩ :=
        cancelEdgesFindOpp_runs (e := ei) (b := bi) hw16 hpFind hEd hEdW heiW (by omega)
          (edges.length - (i + 1)) (i + 1) pos (by omega) rfl
      have hcFindBd : cFind ≤ 50 * maxLen + 10 := by
        have h1 : 50 * (edges.length - (i + 1)) ≤ 50 * maxLen := Nat.mul_le_mul_left 50 (by omega)
        omega
      let s0 := startState [edgesBase, descBase, i] mem pos
      let rg3 := Function.update s0.regs 3 edges.length
      let rg4 := Function.update rg3 4 ei
      let rg5 := Function.update rg4 5 di
      let rg6 := Function.update rg5 6 j
      have rA3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 1) (.const 3))))
          s0 .normal ⟨mem, rg3, pos⟩ 5 :=
        runs_assign_iff.mpr ⟨edges.length, by
          simp [Expr.eval, BinOp.eval, s0, startState, show 3 < 2 ^ w by omega, hdb3W, hDescLen],
          rfl, rfl, rfl⟩
      have rA4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2)))))
          ⟨mem, rg3, pos⟩ .normal ⟨mem, rg4, pos⟩ 7 :=
        runs_assign_iff.mpr ⟨ei, by
          simp [Expr.eval, BinOp.eval, rg3, s0, startState, show 2 < 2 ^ w by omega, h2iW, haI0, hreadI.1, ei],
          rfl, rfl, rfl⟩
      have rA5 : Runs w p ω
          (.assign 5 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))) (.const 1))))
          ⟨mem, rg4, pos⟩ .normal ⟨mem, rg5, pos⟩ 9 :=
        runs_assign_iff.mpr ⟨di, by
          simp [Expr.eval, BinOp.eval, rg4, rg3, s0, startState, show 1 < 2 ^ w by omega,
            show 2 < 2 ^ w by omega, h2iW, haI0, haI1, hreadI.2, di, bi],
          rfl, rfl, rfl⟩
      have rCallFind : Runs w p ω
          (.call 6 findOpp [.reg 0, .reg 3, .reg 4, .reg 5, .bin .add (.reg 2) (.const 1)])
          ⟨mem, rg5, pos⟩ .normal ⟨mem, rg6, stFind.pos⟩ (cFind + 8) := by
        refine runs_call_iff.mpr ⟨[edgesBase, edges.length, ei, di, i + 1], _, .returned j,
          stFind, cFind, ?_, hpFind, hrFind, rfl, ?_, ?_⟩
        · simp [evalArgs, Expr.eval, BinOp.eval, rg5, rg4, rg3, s0, startState,
            show 1 < 2 ^ w by omega, hi1W]
        · cases stFind; dsimp only at hmemFind; subst hmemFind; rfl
        · simp [argsSize, Expr.size]; omega
      let sSwapHit : Stmt :=
        .assign 7 (.bin .sub (.reg 3) (.const 1)) ;; swapStmt 6 7 ;;
        .assign 10 (.bin .sub (.reg 7) (.const 1)) ;; swapStmt 2 10 ;;
        .store (.bin .add (.reg 1) (.const 3)) (.reg 10) ;;
        .call 11 cancelEdges [.reg 0, .reg 1, .reg 2] ;; .ret (.const 0)
      let sMiss : Stmt :=
        .call 11 cancelEdges [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1)] ;; .ret (.const 0)
      let sCondJ : Stmt := .cond (.bin .lt (.reg 6) (.reg 3)) sSwapHit sMiss
      let sThen : Stmt :=
        .assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2)))) ;;
        .assign 5 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))) (.const 1))) ;;
        .call 6 findOpp [.reg 0, .reg 3, .reg 4, .reg 5, .bin .add (.reg 2) (.const 1)] ;; sCondJ
      let sCondI : Stmt := .cond (.bin .lt (.reg 2) (.reg 3)) sThen (.ret (.const 0))
      by_cases hjlt : j < edges.length
      · have hij : i < j := by omega
        have hOppJ : edges[j]'hjlt = ((edges[i]'hilt).1, !(edges[i]'hilt).2) := hjHit hjlt
        set l₁ := swapRemove edges j
        set l₂ := swapRemove l₁ i
        have hl₁len : l₁.length = edges.length - 1 := swapRemove_length hjlt
        obtain ⟨hl₂len, hl₂pref, hl₂sub, hl₂flow⟩ := swapRemove_pair_props hij hjlt hOppJ
        have hl₂len' : l₂.length = edges.length - 2 := hl₂len
        have hlen1W : edges.length - 1 < 2 ^ w := by omega
        have hlen2W : edges.length - 2 < 2 ^ w := by omega
        let rg7 := Function.update rg6 7 (edges.length - 1)
        have rA7 : Runs w p ω (.assign 7 (.bin .sub (.reg 3) (.const 1)))
            ⟨mem, rg6, stFind.pos⟩ .normal ⟨mem, rg7, stFind.pos⟩ 4 :=
          runs_assign_iff.mpr ⟨edges.length - 1, by
            simp [Expr.eval, BinOp.eval, rg6, rg5, rg4, rg3, s0, startState, show 1 < 2 ^ w by omega, hlen1W],
            rfl, rfl, rfl⟩
        obtain ⟨mem1, rgB1, cSw1, rSw1, hrgB1, hmem1Upd, hcSw1⟩ :=
          swapBlock_runs (p := p) (ω := ω) (edgesBase := edgesBase)
            (rSlot := 6) (rLast := 7) (slotIdx := j) (lastIdx := edges.length - 1)
            (mem := mem) (regs := rg7) (pos := stFind.pos) hw16
            (by simp [rg7, rg6, rg5, rg4, rg3, s0, startState])
            (by simp [rg7, rg6]) (by simp [rg7]) (by omega)
            (by decide) (by decide) (by decide)
        have hEd1 : ExplicitEdgesAt mem1 edgesBase l₁ :=
          explicitEdgesAt_swapRemove hEd hjlt hmem1Upd
        let rg10 := Function.update rgB1 10 (edges.length - 2)
        have rA10 : Runs w p ω (.assign 10 (.bin .sub (.reg 7) (.const 1)))
            ⟨mem1, rgB1, stFind.pos⟩ .normal ⟨mem1, rg10, stFind.pos⟩ 4 :=
          runs_assign_iff.mpr ⟨edges.length - 2, by
            simp [Expr.eval, BinOp.eval, hrgB1 7 (by decide) (by decide), rg7,
              show 1 < 2 ^ w by omega, show edges.length - 1 - 1 = edges.length - 2 by omega, hlen2W],
            rfl, rfl, rfl⟩
        obtain ⟨mem2, rgB2, cSw2, rSw2, hrgB2, hmem2Upd, hcSw2⟩ :=
          swapBlock_runs (p := p) (ω := ω) (edgesBase := edgesBase)
            (rSlot := 2) (rLast := 10) (slotIdx := i) (lastIdx := edges.length - 2)
            (mem := mem1) (regs := rg10) (pos := stFind.pos) hw16
            (by simp [rg10, hrgB1 0 (by decide) (by decide), rg7, rg6, rg5, rg4, rg3, s0, startState])
            (by simp [rg10, hrgB1 2 (by decide) (by decide), rg7, rg6, rg5, rg4, rg3, s0, startState])
            (by simp [rg10]) (by omega) (by decide) (by decide) (by decide)
        have hEd2 : ExplicitEdgesAt mem2 edgesBase l₂ :=
          explicitEdgesAt_swapRemove hEd1 (show i < l₁.length by omega)
            (by simpa only [hl₁len, show edges.length - 1 - 1 = edges.length - 2 by omega] using hmem2Upd)
        let mem3 := Function.update mem2 (descBase + 3) (edges.length - 2)
        have hEd3 : ExplicitEdgesAt mem3 edgesBase l₂ :=
          hEd2.congr fun a ha _ => Function.update_of_ne (by omega) _ _
        have hEd3W : ∀ x ∈ l₂, x.1 < 2 ^ w := fun x hx => hEdW x (hl₂sub x hx)
        have hClean2 : ∀ k (hk : k < i) m (hm : m < l₂.length),
            l₂[k]'(by omega) ≠ ((l₂[m]'hm).1, !(l₂[m]'hm).2) := by
          intro k hk m hm
          rw [hl₂pref k hk]
          have hmMem : l₂[m]'hm ∈ edges := hl₂sub _ (List.getElem_mem hm)
          obtain ⟨m', hm', hmEq⟩ := List.mem_iff_getElem.mp hmMem
          rw [← hmEq]; exact hClean k hk m' hm'
        have rStoreLen : Runs w p ω (.store (.bin .add (.reg 1) (.const 3)) (.reg 10))
            ⟨mem2, rgB2, stFind.pos⟩ .normal ⟨mem3, rgB2, stFind.pos⟩ 5 :=
          runs_store_iff.mpr ⟨descBase + 3, edges.length - 2,
            by simp [Expr.eval, BinOp.eval, hrgB2 1 (by decide) (by decide), rg10,
              hrgB1 1 (by decide) (by decide), rg7, rg6, rg5, rg4, rg3, s0, startState,
              show 3 < 2 ^ w by omega, hdb3W],
            by simp [Expr.eval, hrgB2 10 (by decide) (by decide), rg10], rfl, rfl, rfl⟩
        obtain ⟨cRec, stRec, edges', hrRec, hlen', hDesc', hEd', hNoOpp', hSub', hFlow', hFr', hcRec⟩ :=
          ih (l₂.length - i) (by omega) i stFind.pos mem3 l₂ (by omega) (by omega) rfl
            (by simp [mem3, hl₂len']) hEd3 hEd3W hClean2
        let rg11 := Function.update rgB2 11 0
        have rCallRec : Runs w p ω (.call 11 cancelEdges [.reg 0, .reg 1, .reg 2])
            ⟨mem3, rgB2, stFind.pos⟩ .normal ⟨stRec.mem, rg11, stRec.pos⟩ (cRec + 4) := by
          refine runs_call_iff.mpr ⟨[edgesBase, descBase, i], _, .returned 0, stRec, cRec,
            ?_, hpLoop, hrRec, rfl, rfl, ?_⟩
          · simp [evalArgs, Expr.eval, hrgB2 0 (by decide) (by decide),
              hrgB2 1 (by decide) (by decide), hrgB2 2 (by decide) (by decide), rg10,
              hrgB1 0 (by decide) (by decide), hrgB1 1 (by decide) (by decide),
              hrgB1 2 (by decide) (by decide), rg7, rg6, rg5, rg4, rg3, s0, startState]
          · simp [argsSize, Expr.size]; omega
        have rRet0 : Runs w p ω (.ret (.const 0))
            ⟨stRec.mem, rg11, stRec.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ 2 :=
          runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rInner : Runs w p ω sSwapHit ⟨mem, rg6, stFind.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA7, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rSw1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA10, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rSw2,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rStoreLen,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallRec, rRet0, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have rCondJ : Runs w p ω sCondJ ⟨mem, rg6, stFind.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_cond_iff.mpr ⟨1, _,
            by simp [Expr.eval, BinOp.eval, rg6, rg5, rg4, rg3, s0, startState, hjlt, show 1 < 2 ^ w by omega],
            by simp only [one_ne_zero, ↓reduceIte]; exact rInner, rfl⟩
        have rThen : Runs w p ω sThen ⟨mem, rg3, pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA4, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA5,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallFind, rCondJ, rfl⟩), rfl⟩), rfl⟩)
        have rCondI : Runs w p ω sCondI ⟨mem, rg3, pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_cond_iff.mpr ⟨1, _,
            by simp [Expr.eval, BinOp.eval, rg3, s0, startState, hilt, show 1 < 2 ^ w by omega],
            by simp only [one_ne_zero, ↓reduceIte]; exact rThen, rfl⟩
        have rFull : Runs w p ω (cancelRouteEdgesLoopBody cancelEdges findOpp)
            s0 (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA3, rCondI, rfl⟩)
        have hFrame : ∀ a, a ≠ descBase + 3 → (a < edgesBase ∨ edgesBase + 2 * edges.length ≤ a) →
            stRec.mem a = mem a := by
          intro a ha3 haOut
          have h1 : stRec.mem a = mem3 a := hFr' a ha3 (by rcases haOut with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
          have h2 : mem3 a = mem2 a := Function.update_of_ne ha3 _ _
          have h3 : mem2 a = mem1 a := by
            by_cases hlt2 : i < edges.length - 2
            · simp only [hlt2, ↓reduceIte] at hmem2Upd; exact hmem2Upd.2.2 a (by omega) (by omega)
            · simp only [hlt2, ↓reduceIte] at hmem2Upd; exact congrFun hmem2Upd a
          have h4 : mem1 a = mem a := by
            by_cases hlt1 : j < edges.length - 1
            · simp only [hlt1, ↓reduceIte] at hmem1Upd; exact hmem1Upd.2.2 a (by omega) (by omega)
            · simp only [hlt1, ↓reduceIte] at hmem1Upd; exact congrFun hmem1Upd a
          exact h1.trans (h2.trans (h3.trans h4))
        refine ⟨_, ⟨stRec.mem, rg11, stRec.pos⟩, edges', rFull, by omega, hDesc', hEd', hNoOpp',
          fun x hx => hl₂sub x (hSub' x hx), fun ei => (hFlow' ei).trans (hl₂flow ei), hFrame, ?_⟩
        have hrem2 : l₂.length - i + 2 = rem := by omega
        have hmul : (l₂.length - i) * (50 * maxLen + 150) + 2 * (50 * maxLen + 150) =
            rem * (50 * maxLen + 150) := by rw [← hrem2]; ring
        simp only [Expr.size]; omega
      · have hjeq : j = edges.length := by omega
        have hCleanNext : ∀ k (hk : k < i + 1) m (hm : m < edges.length),
            edges[k]'(by omega) ≠ ((edges[m]'hm).1, !(edges[m]'hm).2) := by
          intro k hk m hm
          by_cases hki : k < i
          · exact hClean k hki m hm
          · have hkeq : k = i := by omega
            subst k
            by_cases hmi : m < i
            · intro heq
              have hrev := hClean m hmi i hilt
              rcases hcm : edges[m]'hm with ⟨em, bm⟩
              rcases hci : edges[i]'hilt with ⟨ei', bi'⟩
              rw [hcm, hci] at heq hrev; simp only [Prod.mk.injEq] at heq
              rcases heq with ⟨rfl, rfl⟩; cases bm <;> simp at hrev
            · by_cases hmeq : m = i
              · subst m; rcases hci : edges[i]'hilt with ⟨ei', bi'⟩; cases bi' <;> simp
              · intro heq
                have hmiss := hjMiss hjeq m hm (by omega)
                rcases hcm : edges[m]'hm with ⟨em, bm⟩
                rcases hci : edges[i]'hilt with ⟨ei', bi'⟩
                have hei_eq : ei = ei' := by simp [ei, hci]
                have hbi_eq : bi = bi' := by simp [bi, hci]
                rw [hcm, hci] at heq; rw [hcm, hei_eq, hbi_eq] at hmiss
                simp only [Prod.mk.injEq] at heq
                rcases heq with ⟨rfl, rfl⟩; cases bm <;> simp at hmiss
        obtain ⟨cRec, stRec, edges', hrRec, hlen', hDesc', hEd', hNoOpp', hSub', hFlow', hFr', hcRec⟩ :=
          ih (edges.length - (i + 1)) (by omega) (i + 1) stFind.pos mem edges hLenLe (by omega) rfl
            hDescLen hEd hEdW hCleanNext
        let rg11 := Function.update rg6 11 0
        have rCallRec : Runs w p ω (.call 11 cancelEdges [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1)])
            ⟨mem, rg6, stFind.pos⟩ .normal ⟨stRec.mem, rg11, stRec.pos⟩ (cRec + 6) := by
          refine runs_call_iff.mpr ⟨[edgesBase, descBase, i + 1], _, .returned 0, stRec, cRec,
            ?_, hpLoop, hrRec, rfl, rfl, ?_⟩
          · simp [evalArgs, Expr.eval, BinOp.eval, rg6, rg5, rg4, rg3, s0, startState,
              show 1 < 2 ^ w by omega, hi1W]
          · simp [argsSize, Expr.size]; omega
        have rRet0 : Runs w p ω (.ret (.const 0))
            ⟨stRec.mem, rg11, stRec.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ 2 :=
          runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rElse : Runs w p ω sMiss ⟨mem, rg6, stFind.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallRec, rRet0, rfl⟩)
        have rCondJ : Runs w p ω sCondJ ⟨mem, rg6, stFind.pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_cond_iff.mpr ⟨0, _,
            by simp [Expr.eval, BinOp.eval, rg6, rg5, rg4, rg3, s0, startState, hjlt, show 0 < 2 ^ w by omega],
            by simp only [↓reduceIte]; exact rElse, rfl⟩
        have rThen : Runs w p ω sThen ⟨mem, rg3, pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA4, runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA5,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallFind, rCondJ, rfl⟩), rfl⟩), rfl⟩)
        have rCondI : Runs w p ω sCondI ⟨mem, rg3, pos⟩ (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_cond_iff.mpr ⟨1, _,
            by simp [Expr.eval, BinOp.eval, rg3, s0, startState, hilt, show 1 < 2 ^ w by omega],
            by simp only [one_ne_zero, ↓reduceIte]; exact rThen, rfl⟩
        have rFull : Runs w p ω (cancelRouteEdgesLoopBody cancelEdges findOpp)
            s0 (.returned 0) ⟨stRec.mem, rg11, stRec.pos⟩ _ :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA3, rCondI, rfl⟩)
        refine ⟨_, ⟨stRec.mem, rg11, stRec.pos⟩, edges', rFull, hlen', hDesc', hEd', hNoOpp',
          hSub', hFlow', hFr', ?_⟩
        have hrem1 : edges.length - (i + 1) + 1 = rem := by omega
        have hmul : (edges.length - (i + 1)) * (50 * maxLen + 150) + (50 * maxLen + 150) =
            rem * (50 * maxLen + 150) := by rw [← hrem1]; ring
        simp only [Expr.size]; omega

/-- Entry-point specialization of `cancelRouteEdgesLoop_runs` at `i = 0`, bounding cost by
`cancelRouteEdgesCost maxLen`. -/
theorem cancelRouteEdges_runs {w cancelEdges findOpp edgesBase descBase maxLen pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {edges : List (ℕ × Bool)}
    (hw16 : 16 < 2 ^ w)
    (hpLoop : p.procs[cancelEdges]? = some (cancelRouteEdgesLoopBody cancelEdges findOpp))
    (hpFind : p.procs[findOpp]? = some (cancelEdgesFindOppBody findOpp))
    (hDisj : descBase + 3 < edgesBase)
    (hAddrW : edgesBase + 2 * maxLen < 2 ^ w)
    (hLenLe : edges.length ≤ maxLen)
    (hDescLen : mem (descBase + 3) = edges.length)
    (hEd : ExplicitEdgesAt mem edgesBase edges)
    (hEdW : ∀ x ∈ edges, x.1 < 2 ^ w) :
    ∃ (c : ℕ) (st' : State) (edges' : List (ℕ × Bool)),
      Runs w p ω (cancelRouteEdgesLoopBody cancelEdges findOpp)
        (startState [edgesBase, descBase, 0] mem pos) (.returned 0) st' c ∧
      edges'.length ≤ edges.length ∧
      st'.mem (descBase + 3) = edges'.length ∧
      ExplicitEdgesAt st'.mem edgesBase edges' ∧
      NoOppositePairs edges' ∧
      (∀ x ∈ edges', x ∈ edges) ∧
      (∀ ei : ℕ, (edges'.map fun x => walkFlow [x] ei).sum =
        (edges.map fun x => walkFlow [x] ei).sum) ∧
      (∀ a, a ≠ descBase + 3 → (a < edgesBase ∨ edgesBase + 2 * edges.length ≤ a) →
        st'.mem a = mem a) ∧
      c ≤ cancelRouteEdgesCost maxLen := by
  obtain ⟨c, st', edges', hr, hlen', hDesc', hEd', hNoOpp', hSub', hFlow', hFr', hc⟩ :=
    cancelRouteEdgesLoop_runs hw16 hpLoop hpFind hDisj hAddrW
      edges.length 0 pos mem edges hLenLe (Nat.zero_le _) (Nat.sub_zero _) hDescLen hEd hEdW
      (fun k hk => absurd hk (Nat.not_lt_zero _))
  refine ⟨c, st', edges', hr, hlen', hDesc', hEd', hNoOpp', hSub', hFlow', hFr', ?_⟩
  unfold cancelRouteEdgesCost
  have h1 : edges.length * (50 * maxLen + 150) ≤ maxLen * (50 * maxLen + 150) :=
    Nat.mul_le_mul_right _ hLenLe
  have h2 : maxLen * (50 * maxLen + 150) = 50 * maxLen * maxLen + 150 * maxLen := by ring
  omega

end MinCostFlow.MinRatio
