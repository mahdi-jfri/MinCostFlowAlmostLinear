module

public import MinCostFlow.HierPaths.DelProgLevel
public import MinCostFlow.HierPaths.LossCountersSpec

/-!
# The climb in the `Delete` program

After a new direct failure of `u`, `Delete` climbs from the leaf depth to the root and runs one
level of the counters at each depth, as long as the change `Δ` is not zero (`climb`,
`HierPaths/LossCounters.lean`). `climbStmt` is this loop: register `11` holds the depth and
register `12` the change. Each round lowers the depth by one and runs `levelStmt`.

`climb_triple` says that from the climb invariant `ClimbInv` (`HierPaths/LossCountersSpec.lean`)
the loop leaves the counters and the lost set of `climb` in the block and appends the output of
`climb` to the work list. The invariant gives the bounds the levels need: the new sum of a group
is the number of lost terminals among its children, so at most `2 ^ x`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

theorem length_layoutList_of_map_length {bs cs : List (List ℕ)}
    (h : bs.map List.length = cs.map List.length) :
    (layoutList bs).length = (layoutList cs).length := by
  have key : ∀ (ds : List (List ℕ)), (layoutList ds).length =
      ds.length + 1 + ((List.range ds.length).map fun j => (ds.getD j []).length).sum := by
    intro ds
    simp [layoutList, csrList, csrData, List.length_flatMap]
  have hlen : bs.length = cs.length := by
    simpa using congrArg List.length h
  have hget : ∀ j, (bs.getD j []).length = (cs.getD j []).length := by
    intro j
    have h' := congrArg (fun l => l[j]?) h
    simp only [List.getElem?_map] at h'
    rcases hb : bs[j]? with _ | l <;> rcases hc : cs[j]? with _ | l' <;>
      simp [hb, hc, List.getD_eq_getElem?_getD] at h' ⊢
    exact h'
  rw [key, key, hlen]
  simp only [hget]

theorem HierConcrete.length_encode_withLoss (x : HierConcrete) (L : LossState) :
    (x.withLoss L).encode.length = x.encode.length := by
  apply length_layoutList_of_map_length
  simp [HierConcrete.sections, HierConcrete.withLoss, HierConcrete.withSt, csrList, csrData,
    List.length_flatMap, HierConcrete.header, HierConcrete.n, HierConcrete.m, HierConcrete.depth, HierConcrete.pairIdxTable]

/-- The loop test: the depth and the change are both positive. -/
def climbTest : Expr := .bin .and (.bin .lt (.const 0) (.reg 11)) (.bin .lt (.const 0) (.reg 12))

/-- The climb. -/
def climbStmt : Stmt :=
  .loop climbTest (.seq (.assign 11 (.bin .sub (.reg 11) (.const 1))) levelStmt)

theorem climbStmt_noRand : climbStmt.NoRand := by
  simp [climbStmt, Stmt.NoRand, levelStmt_noRand]

/-! ### Model facts for the climb -/

theorem groupSize_le_two_pow {x b j : ℕ} : groupSize x b j ≤ 2 ^ x := by
  have hpos : 0 < numGroups x b j := by unfold numGroups; positivity
  calc groupSize x b j ≤ numGroups x b j * groupSize x b j := Nat.le_mul_of_pos_left _ hpos
    _ = 2 ^ x := numGroups_mul_groupSize

theorem climb_succ_of_ne {x b u j Δ : ℕ} {st : LossState} (hΔ : Δ ≠ 0) :
    climb x b u (j + 1) Δ st =
      ((climb x b u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1).1,
        (levelStep x b u j Δ st).2.1 ++
          (climb x b u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1).2) := by
  simp only [climb, hΔ, if_false]

theorem climb_stop {x b u j Δ : ℕ} {st : LossState} (h : j = 0 ∨ Δ = 0) :
    climb x b u j Δ st = (st, []) := by
  rcases h with h | h
  · subst h; rfl
  · cases j <;> simp [climb, h]

/-- Under the climb invariant, the new sum of the group of `u` at depth `j` is at most `2 ^ x`:
it is the number of lost terminals among the children (the `sum` and `delta` fields of
`ClimbInv`), and these are members of the group. -/
theorem ClimbInv.sum_add_le {x b u j Δ : ℕ} {F : Finset ℕ} {st : LossState}
    (hj : j < leafDepth x b) (hinv : ClimbInv x b F u (j + 1) Δ st) :
    st.sum j (groupOf x b j u) + Δ ≤ 2 ^ x := by
  have hs : st.sum j (groupOf x b j u) + Δ =
      (childUnion x b (insert u F) j (groupOf x b j u)).card := by
    rw [hinv.sum j hj, failSetAt_of_lt (Nat.lt_succ_self j), hinv.delta, card_childUnion_insert]
  rw [hs]
  calc (childUnion x b (insert u F) j (groupOf x b j u)).card
      ≤ (members x b j (groupOf x b j u)).card :=
        Finset.card_le_card (childUnion_subset_members j _)
    _ = groupSize x b j := card_members _
    _ ≤ 2 ^ x := groupSize_le_two_pow

/-! ### The loop -/

/-- A loop can carry a remaining cost bound through its proof invariant. -/
private theorem delLoop_budget {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {Inv : ℕ → State → Prop} {Q : State → Prop} {v : State → ℕ}
    (hc : ∀ k s, Inv k s → e.eval w s = some (v s))
    (he : ∀ k s, Inv k s → v s = 0 → Q s ∧ e.size + 1 ≤ k)
    (hs : ∀ k s, Inv k s → v s ≠ 0 →
      ∃ cost, Triple w p (fun t => t = s) body
        (normalPost fun t => ∃ remaining, Inv remaining t ∧ e.size + cost + remaining + 1 ≤ k)
        (fun _ => cost)) :
    ∀ k, Triple w p (Inv k) (.loop e body) (normalPost Q) (fun _ => k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s ω hI
    by_cases hv : v s = 0
    · obtain ⟨hQ, hcost⟩ := he k s hI hv
      exact ⟨.normal, s, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hc k s hI, rfl, rfl, rfl⟩), hQ, hcost⟩
    · obtain ⟨cost, H⟩ := hs k s hI hv
      obtain ⟨o, t, c₁, hr, hQ, hc₁⟩ := H s ω rfl
      cases o <;> try contradiction
      obtain ⟨remaining, hI', hbudget⟩ := hQ
      obtain ⟨o, t', c₂, hr', hQ', hc₂⟩ := ih remaining (by omega) t ω hI'
      dsimp only at hc₁ hc₂
      refine ⟨o, t', e.size + c₁ + c₂ + 1, ?_, hQ', by change e.size + c₁ + c₂ + 1 ≤ k; omega⟩
      exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨v s, t, c₁, c₂, hc k s hI,
        hv, hr, hr', rfl⟩))

/-- Both loss event counters are nondecreasing during a climb. -/
theorem climb_counts_mono (x b u : ℕ) :
    ∀ j Δ (L : LossState), L.updates ≤ (climb x b u j Δ L).1.updates ∧
      L.enumerated ≤ (climb x b u j Δ L).1.enumerated := by
  intro j
  induction j with
  | zero => intro Δ L; simp [climb]
  | succ j ih =>
    intro Δ L
    by_cases hd : Δ = 0
    · simp [climb, hd]
    rw [climb_succ_of_ne hd]
    let mid := levelStep x b u j Δ L
    obtain ⟨hu, he⟩ := ih mid.2.2 mid.1
    exact ⟨(by rw [levelStep_updates]; omega : L.updates ≤ mid.1.updates).trans hu,
      (by rw [levelStep_enumerated]; omega : L.enumerated ≤ mid.1.enumerated).trans he⟩

/-- The remaining cost charges the final increases of the two event counters. -/
def delClimbCost (L Lf : LossState) : ℕ :=
  700 * (Lf.updates - L.updates) + 130 * (Lf.enumerated - L.enumerated) + 8

private theorem delClimbCost_split {L mid Lf : LossState}
    (hu : mid.updates = L.updates + 1) (he : L.enumerated ≤ mid.enumerated)
    (hfu : mid.updates ≤ Lf.updates) (hfe : mid.enumerated ≤ Lf.enumerated) :
    delClimbCost L Lf = 700 + 130 * (mid.enumerated - L.enumerated) + delClimbCost mid Lf := by
  unfold delClimbCost
  omega

/-- The event-based bound is at most the bound charging every level its largest enumeration. -/
theorem delClimbCost_le (x b u : ℕ) :
    ∀ j Δ (L : LossState), delClimbCost L (climb x b u j Δ L).1 ≤
      j * (130 * 2 ^ x + 700) + 8 := by
  intro j
  induction j with
  | zero => intro Δ L; simp [climb, delClimbCost]
  | succ j ih =>
    intro Δ L
    by_cases hΔ : Δ = 0
    · simp [climb, hΔ, delClimbCost]
    rw [climb_succ_of_ne hΔ]
    let mid := levelStep x b u j Δ L
    let Lf := (climb x b u j mid.2.2 mid.1).1
    have hU : mid.1.updates = L.updates + 1 := levelStep_updates ..
    have hE : mid.1.enumerated = L.enumerated +
        (if levelCond x b u j Δ L then groupSize x b j else 0) := levelStep_enumerated ..
    have hle : mid.1.enumerated - L.enumerated ≤ 2 ^ x := by
      rw [hE, Nat.add_sub_cancel_left]
      split
      · exact groupSize_le_two_pow
      · exact Nat.zero_le _
    obtain ⟨hu, he⟩ := climb_counts_mono x b u j mid.2.2 mid.1
    change delClimbCost L Lf ≤ _
    rw [delClimbCost_split hU (by omega) hu he, Nat.succ_mul j (130 * 2 ^ x + 700)]
    have hbound : delClimbCost mid.1 Lf ≤ j * (130 * 2 ^ x + 700) + 8 := ih _ _
    dsimp only [Lf] at hbound
    omega

/-- The state of the climb loop between rounds: at depth `j` with change `Δ` and loss state `L`,
after appending `out` to the work list. Running the rest of `climb` from there gives the final
loss state `Lf` and the rest of the final output `outF`. -/
def ClimbLoopInv (x : HierConcrete) (F : Finset ℕ) (b u WB c0 : ℕ) (L0 : List ℕ)
    (mem0 : ℕ → ℕ) (Lf : LossState) (outF : List ℕ) (budget : ℕ) (s : State) : Prop :=
  ∃ (j Δ : ℕ) (L : LossState) (out : List ℕ), ClimbInv x.H.A.x x.H.A.b F u j Δ L ∧
    (climb x.H.A.x x.H.A.b u j Δ L).1 = Lf ∧ out ++ (climb x.H.A.x x.H.A.b u j Δ L).2 = outF ∧
    s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 11 = j ∧ s.regs 12 = Δ ∧ s.regs 22 = WB ∧
    s.regs 23 = c0 + out.length ∧ ListAt s.mem b (x.withLoss L).encode ∧
    ListAt s.mem WB (L0 ++ out) ∧
    (∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨ WB + c0 + out.length ≤ a) →
      s.mem a = mem0 a) ∧ budget = delClimbCost L Lf

theorem climb_triple {w : ℕ} {p : Program} (x : HierConcrete) {F : Finset ℕ}
    {b u WB c0 : ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ}
    (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x) (hu : u < 2 ^ x.H.A.x)
    (hinv : ClimbInv x.H.A.x x.H.A.b F u x.depth 1 x.ms.st.loss) (hL0 : L0.length = c0)
    (hb : b + x.encode.length < 2 ^ w) (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w)
    (hd : x.depth < 2 ^ w) (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hblk : b + x.encode.length ≤ WB)
    (hw : WB + c0 + (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2.length + 2 ^ x.H.A.x <
      2 ^ w) :
    Triple w p (fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 11 = x.depth ∧ s.regs 12 = 1 ∧
        s.regs 22 = WB ∧ s.regs 23 = c0 ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) climbStmt
      (normalPost fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 22 = WB ∧
        s.regs 23 = c0 + (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2.length ∧
        ListAt s.mem b (x.withLoss (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).1).encode ∧
        ListAt s.mem WB (L0 ++ (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
          WB + c0 + (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2.length ≤ a) →
          s.mem a = mem0 a)
      (fun _ => delClimbCost x.ms.st.loss (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).1) := by
  have h1w : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hgs : ∀ j, groupSize x.H.A.x x.H.A.b j ≤ 2 ^ x.H.A.x := fun _ => groupSize_le_two_pow
  have htest : climbTest.size = 7 := rfl
  have hsub : (Expr.bin .sub (.reg 11) (.const 1)).size = 3 := rfl
  have hloop := delLoop_budget (w := w) (p := p) (e := climbTest)
    (body := .seq (.assign 11 (.bin .sub (.reg 11) (.const 1))) levelStmt)
    (Inv := ClimbLoopInv x F b u WB c0 L0 mem0
      (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).1
      (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2)
    (Q := fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 22 = WB ∧
        s.regs 23 = c0 + (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2.length ∧
        ListAt s.mem b (x.withLoss (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).1).encode ∧
        ListAt s.mem WB (L0 ++ (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
          WB + c0 + (climb x.H.A.x x.H.A.b u x.depth 1 x.ms.st.loss).2.length ≤ a) →
          s.mem a = mem0 a)
    (v := fun s => (if 0 < s.regs 11 then 1 else 0) &&& (if 0 < s.regs 12 then 1 else 0))
    (fun _ s _ => Expr.eval_and (Expr.eval_lt_op (Expr.eval_const h0w) (Expr.eval_reg _ _ _) h1w)
      (Expr.eval_lt_op (Expr.eval_const h0w) (Expr.eval_reg _ _ _) h1w)
      (by split_ifs <;> omega))
    (fun budget s hI hv => by
      obtain ⟨j, Δ, L, out, _, hLf, hout, h0, h10, h11, h12, h22, h23, hbl, hwl, hfr, hbudget⟩ := hI
      have hstop : j = 0 ∨ Δ = 0 := by
        by_contra hne
        push_neg at hne
        have hj : 0 < s.regs 11 := by omega
        have hΔ : 0 < s.regs 12 := by omega
        simp [hj, hΔ] at hv
      rw [climb_stop hstop] at hLf hout
      simp only [List.append_nil] at hout
      subst hLf hout
      exact ⟨⟨h0, h10, h22, h23, hbl, hwl, hfr⟩, by simp [hbudget, delClimbCost, htest]⟩)
    (fun budget s hI hv => by
      obtain ⟨j, Δ, L, out, hci, hLf, hout, h0, h10, h11, h12, h22, h23, hbl, hwl, hfr, hbudget⟩ := hI
      have hpos : 0 < j ∧ 0 < Δ := by
        by_contra hne
        rw [not_and_or] at hne
        rcases hne with hne | hne
        · have : ¬ 0 < s.regs 11 := by omega
          simp [this] at hv
        · have : ¬ 0 < s.regs 12 := by omega
          simp [this] at hv
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hle : j' + 1 ≤ x.depth := hci.le
      have hj' : j' < leafDepth x.H.A.x x.H.A.b := hle
      have hΔ : Δ ≠ 0 := by omega
      rw [climb_succ_of_ne hΔ] at hLf hout
      have houtlen := congrArg List.length hout
      simp only [List.length_append] at houtlen
      have hs4 := hci.sum_add_le hj'
      obtain ⟨st1, hst1⟩ : ∃ st1 : State, st1 = { s with regs := Function.update s.regs 11 j' } :=
        ⟨_, rfl⟩
      have tA : Triple w p (fun s' => s' = s) (.assign 11 (.bin .sub (.reg 11) (.const 1)))
          (normalPost fun s' => s' = st1) (fun _ => 3 + 1) :=
        Triple.assign (val := fun _ => j') (fun s' hs' => by
            subst hs'
            rw [show j' = s'.regs 11 - 1 by omega]
            exact Expr.eval_sub (Expr.eval_reg _ _ _) (Expr.eval_const h1w) (by omega))
          (fun s' hs' => by subst hs'; exact hst1.symm)
      have tL := level_triple (w := w) (p := p) (x.withLoss L) (b := b) (u := u) (j := j')
        (Δ := Δ) (WB := WB) (c0 := c0 + out.length) (R := st1.regs) (L0 := L0 ++ out)
        (mem0 := s.mem)
        (by rw [hst1]; simpa [Function.update_apply] using h0)
        (by rw [hst1]; simpa [Function.update_apply] using h10)
        (by rw [hst1]; simp)
        (by rw [hst1]; simpa [Function.update_apply] using h12)
        (by rw [hst1]; simpa [Function.update_apply] using h22)
        (by rw [hst1]; simpa [Function.update_apply] using h23)
        (by simp [hL0]) hnt hu (show j' ≤ x.depth by omega)
        (by rw [HierConcrete.length_encode_withLoss]; exact hb)
        (lt_of_le_of_lt (Nat.mul_le_mul_right _ (show j' ≤ x.depth - 1 by omega)) hdb)
        (show 2 ^ x.H.A.x < 2 ^ w by omega)
        (show 4 * (L.sum j' (groupOf x.H.A.x x.H.A.b j' u) + Δ) < 2 ^ w by omega)
        (by rw [HierConcrete.length_encode_withLoss]; exact hblk)
        (show WB + (c0 + out.length) + groupSize x.H.A.x x.H.A.b j' < 2 ^ w by
          have := hgs j'; omega)
      refine ⟨3 + 1 + delLevelCost x.H.A.x x.H.A.b u j' Δ L + 1,
        (Triple.seq_normal_const tA (tL.weaken_pre fun s' hs' => ?_)).strengthen_post ?_⟩
      · subst hs'
        refine ⟨rfl, ?_, ?_, ?_⟩
        · rw [hst1]; exact hbl
        · rw [hst1]; exact hwl
        · rw [hst1]
      · intro o s' hq
        cases o with
        | returned _ => exact hq.elim
        | normal =>
          obtain ⟨g0, g10, g11, g22, g12, g23, gbl, gwl, gfr⟩ := hq
          refine ⟨delClimbCost (levelStep x.H.A.x x.H.A.b u j' Δ L).1 _,
            ⟨j', _, _, out ++ (levelStep x.H.A.x x.H.A.b u j' Δ L).2.1,
            levelStep_spec hj' hci, hLf, by rw [List.append_assoc]; exact hout, g0, g10, g11,
            g12, g22, by rw [g23, List.length_append, Nat.add_assoc]; rfl, gbl,
            by rw [← List.append_assoc]; exact gwl, ?_, rfl⟩, ?_⟩
          · intro a ha hb'
            rw [List.length_append] at hb'
            have hlen : (x.withLoss L).encode.length = x.encode.length :=
              HierConcrete.length_encode_withLoss x L
            rcases hb' with h | h
            · rw [gfr a (by rw [hlen]; exact ha) (Or.inl (by omega))]
              exact hfr a ha (Or.inl h)
            · rw [gfr a (by rw [hlen]; exact ha) (Or.inr (Nat.le_trans (Nat.le_of_eq
                (by simp only [Nat.add_assoc]; rfl)) h))]
              exact hfr a ha (Or.inr (by omega))
          · let mid := levelStep x.H.A.x x.H.A.b u j' Δ L
            have hu' : mid.1.updates = L.updates + 1 := levelStep_updates ..
            have he' : L.enumerated ≤ mid.1.enumerated := by
              change _ ≤ (levelStep x.H.A.x x.H.A.b u j' Δ L).1.enumerated
              rw [levelStep_enumerated]
              omega
            obtain ⟨huF, heF⟩ := climb_counts_mono x.H.A.x x.H.A.b u j' mid.2.2 mid.1
            rw [hLf] at huF heF
            rw [hbudget, delClimbCost_split hu' he' huF heF, delLevelCost_eq, htest]
            dsimp only [mid]
            omega)
  refine (hloop _).weaken_pre (fun s hs => ?_)
  obtain ⟨h0, h10, h11, h12, h22, h23, hbl, hwl, hm⟩ := hs
  exact ⟨x.depth, 1, x.ms.st.loss, [], hinv, rfl, rfl, h0, h10, h11, h12, h22,
    by rw [h23]; rfl, hbl, by simpa using hwl, fun a _ _ => by rw [hm], rfl⟩

end MinCostFlow.HierPaths

end
