module

public import MinCostFlow.SparseCore.Program.ReadEmb

/-!
# The loop that applies a change list to the embedding table

`embLoop_triple` is the proof of the loop of `embStepStmt` and `embInitStmt`. Each round takes one
entry `(e, walk)` of the change list, copies the walk to the heap with `copyWords`, and points the
table word of `e` to the copy.

The loop starts from a table `EmbRepAt eCap r v ptr` whose walks lie below `lo`. The input (the
list and its walks) lies below `lo` too, outside the record and the table. New walks go to the
heap from `hp0`, which is above `lo` and above the table, and where memory is zero. At the end the
table is `v.apply X`; each walk is either an old one, unchanged, or a new one in `[hp0, h')`;
memory below `hp0` outside the table is unchanged; and memory is zero from the end of the heap.
-/

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner.Program

public section

/-- The state of the loop after the entries `pre`, with the entries `ys` left. -/
@[expose] def EmbLoopInv (eCap r a hp0 : ℕ) (mem₀ : ℕ → ℕ) (v : EmbView) (ptr : ℕ → ℕ)
    (X : EmbChange) (ys : EmbChange) (st : State) : Prop :=
  ∃ pre : EmbChange, pre ++ ys = X ∧
    st.regs 4 = r + 2 ∧ st.regs 5 = a + 2 * pre.length ∧ st.regs 6 = ys.length ∧
    st.regs 7 = (pre.foldl embConcStep (ptr, hp0)).2 ∧
    EmbRepAt eCap r (v.apply pre) (pre.foldl embConcStep (ptr, hp0)).1 st.mem ∧
    (∀ x, x < hp0 → (x < r + 2 ∨ r + 2 + eCap ≤ x) → st.mem x = mem₀ x) ∧
    ZeroFrom st.mem (pre.foldl embConcStep (ptr, hp0)).2 ∧
    ∀ e ∈ (v.apply pre).dom,
      ((pre.foldl embConcStep (ptr, hp0)).1 e = ptr e ∧ (v.apply pre).emb e = v.emb e ∧
        e ∈ v.dom) ∨
      (hp0 ≤ (pre.foldl embConcStep (ptr, hp0)).1 e ∧
        (pre.foldl embConcStep (ptr, hp0)).1 e + walkWords ((v.apply pre).emb e) ≤
          (pre.foldl embConcStep (ptr, hp0)).2)

theorem EmbView.apply_nil (v : EmbView) : v.apply [] = v := by
  cases v
  simp [EmbView.apply]

/-- A change list stays in memory when the memory agrees on its cells. -/
theorem EmbChangeAt.of_agree {mem mem' : ℕ → ℕ} {a lo : ℕ} {X : EmbChange}
    (hX : EmbChangeAt mem a X) (hin : a + 2 * X.length ≤ lo)
    (hw : ∀ i (hi : i < X.length), mem (a + 2 * i + 1) + walkWords X[i].2 ≤ lo)
    (hag : ∀ x < lo, mem' x = mem x) : EmbChangeAt mem' a X := by
  intro i hi
  obtain ⟨h1, h2⟩ := hX i hi
  have hq : mem' (a + 2 * i + 1) = mem (a + 2 * i + 1) := hag _ (by omega)
  refine ⟨(hag _ (by omega)).trans h1, ?_⟩
  rw [hq]
  refine h2.of_agree fun x hx1 hx2 => hag x ?_
  have := hw i hi
  simp only [walkWords] at this
  omega

private theorem getElem_mid {α : Type*} {pre ys : List α} {x : α} {xs : List α} {X : List α}
    (hpre : pre ++ ys = X) (hys : ys = x :: xs) (h : pre.length < X.length) :
    X[pre.length] = x := by
  subst hys hpre
  simp

/-- The loop applies the change list. -/
theorem embLoop_triple {w : ℕ} {p : Program} {bCopy : ℕ}
    (hcopy : MeetsContract w p bCopy (copyWordsContract w))
    {eCap r a lo hp0 : ℕ} {mem₀ : ℕ → ℕ} {v : EmbView} {ptr : ℕ → ℕ} {X : EmbChange}
    (hlt : hp0 + (X.map fun p => walkWords p.2).sum < 2 ^ w)
    (hlo : lo ≤ hp0) (htab : r + 2 + eCap ≤ hp0)
    (hin : EmbInputAt mem₀ (fun x => r ≤ x ∧ x < r + 2 + eCap) a eCap lo X)
    (hX : EmbChangeAt mem₀ a X)
    (hold : ∀ e ∈ v.dom, ptr e + walkWords (v.emb e) ≤ lo) :
    Triple w p (EmbLoopInv eCap r a hp0 mem₀ v ptr X X) (.loop (.reg 6) (embLoopBody bCopy))
      (normalPost (EmbLoopInv eCap r a hp0 mem₀ v ptr X []))
      (fun _ => (X.map fun q => 17 * walkWords q.2 + 80).sum +
        X.length * ((Expr.reg 6).size + 1) + (Expr.reg 6).size + 1) := by
  obtain ⟨hinA, hinNot, hinE⟩ := hin
  refine Triple.loop_list (fun q => 17 * walkWords q.2 + 80) (fun st hInv => ?_)
    (fun x xs st hInv => ?_) X
  · obtain ⟨pre, hpre, h4, h5, h6, h7, hrep, hfr, hz, hloc⟩ := hInv
    exact ⟨Expr.eval_reg_of_eq h6, ⟨pre, hpre, h4, h5, h6, h7, hrep, hfr, hz, hloc⟩⟩
  obtain ⟨pre, hpre, h4, h5, h6, h7, hrep, hfr, hz, hloc⟩ := hInv
  refine ⟨xs.length + 1, Expr.eval_reg_of_eq (by simp [h6]), by omega, ?_⟩
  intro st' ω' hst'
  subst hst'
  -- names for the entry and the heap
  obtain ⟨e, W⟩ := x
  set i := pre.length with hi_def
  have hiX : i < X.length := by rw [← hpre]; simp [hi_def]
  have hXi : X[i] = (e, W) := getElem_mid hpre rfl hiX
  set s := pre.foldl embConcStep (ptr, hp0) with hs
  set H := s.2 with hH
  set q := mem₀ (a + 2 * i + 1) with hq
  obtain ⟨hXe, hXw⟩ := hX i hiX
  rw [hXi] at hXe hXw
  obtain ⟨heCap, hqlo, hqNot⟩ := hinE i hiX
  rw [hXi] at heCap hqlo hqNot
  simp only at hXe hXw heCap hqlo hqNot
  -- the heap bound
  have hsum : H + walkWords W + (xs.map fun p => walkWords p.2).sum =
      hp0 + (X.map fun p => walkWords p.2).sum := by
    rw [hH, hs, embConcStep_fold_snd, ← hpre]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega
  have hHlt : H + walkWords W < 2 ^ w := by omega
  have hHge : hp0 ≤ H := by rw [hH, hs, embConcStep_fold_snd]; omega
  have hWw : walkWords W = 1 + 2 * W.length := rfl
  -- the entry cells and the walk cells are read from `mem₀`
  have hent : ∀ k < 2, st'.mem (a + 2 * i + k) = mem₀ (a + 2 * i + k) := by
    intro k hk
    have hlt' : 2 * i + k < 2 * X.length := by omega
    refine hfr _ (by omega) ?_
    have := hinNot (2 * i + k) hlt'
    simp only [not_and, not_lt] at this
    by_cases hr : r ≤ a + 2 * i + k
    · right; rw [← Nat.add_assoc] at this; exact this hr
    · left; omega
  have hwalk : ∀ j < walkWords W, st'.mem (q + j) = mem₀ (q + j) := by
    intro j hj
    refine hfr _ (by omega) ?_
    have := hqNot j hj
    simp only [not_and, not_lt] at this
    by_cases hr : r ≤ q + j
    · right; exact this hr
    · left; omega
  have he_eq : st'.mem (a + 2 * i) = e := by simpa using (hent 0 (by omega)).trans hXe
  have hq_eq : st'.mem (a + 2 * i + 1) = q := hent 1 (by omega)
  have hlen : st'.mem q = W.length := by
    rw [show q = q + 0 from rfl, hwalk 0 (by simp [walkWords])]
    exact MWalkAt_head hXw
  have hw2 : 2 < 2 ^ w := by omega
  apply runs_start_le
  refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq h5) he_eq) ?_
  refine runs_seq_assign_le (v := q) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (by simp [h5])) (Expr.eval_const (by omega)) (by omega)) hq_eq) ?_
  refine runs_seq_assign_le (v := 1 + 2 * W.length) (Expr.eval_add (Expr.eval_const (by omega))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (by simp)) hlen) (by omega)) (by omega)) ?_
  refine runs_seq_call_le (vs := [q, H, 1 + 2 * W.length]) hcopy
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) (evalArgs_cons
      (Expr.eval_reg_of_eq (by simp [h7, hH, hs])) (evalArgs_cons (Expr.eval_reg_of_eq (by simp))
        (evalArgs_nil _ _))))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    ⟨q, H, 1 + 2 * W.length, rfl, by omega, by omega, by omega, by omega⟩ ?_
  rintro _ m2 pos2 ⟨_, _, _, hargs, -, hcp, hcfr⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  refine runs_seq_store_le (x := r + 2 + e) (v := H) (Expr.eval_add
    (Expr.eval_reg_of_eq (by simp [h4])) (Expr.eval_reg_of_eq (by simp)) (by omega))
    (Expr.eval_reg_of_eq (by simp [h7, hH, hs])) ?_
  refine runs_seq_assign_le (v := H + (1 + 2 * W.length)) (Expr.eval_add
    (Expr.eval_reg_of_eq (by simp [h7, hH, hs])) (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  refine runs_seq_assign_le (v := a + 2 * i + 2) (Expr.eval_add
    (Expr.eval_reg_of_eq (by simp [h5])) (Expr.eval_const (by omega)) (by omega)) ?_
  have hxsl : xs.length + 1 ≤ X.length := by rw [← hpre]; simp
  refine runs_assign_le (v := xs.length + 1 - 1) (Expr.eval_sub
    (Expr.eval_reg_of_eq (by simp [h6])) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
  swap
  · simp only [Expr.size, argsSize, walkWords, copyWordsContract]
    omega
  -- the new state
  set m3 := Function.update m2 (r + 2 + e) H with hm3
  have hm2_lo : ∀ x, x < H → m2 x = st'.mem x := fun x hx => hcfr x (Or.inl hx)
  have hm2_hi : ∀ x, H + (1 + 2 * W.length) ≤ x → m2 x = st'.mem x :=
    fun x hx => hcfr x (Or.inr hx)
  have hm3_ne : ∀ x, x ≠ r + 2 + e → m3 x = m2 x := fun x hx => by
    simp only [hm3, Function.update_apply, hx, ite_false]
  have hpre' : pre ++ [(e, W)] ++ xs = X := by simpa using hpre
  have hfold : (pre ++ [(e, W)]).foldl embConcStep (ptr, hp0) =
      (Function.update s.1 e H, H + (1 + 2 * W.length)) := by
    simp [List.foldl_append, embConcStep, hs, hH, walkWords]
  have hview : v.apply (pre ++ [(e, W)]) =
      ⟨Function.update (v.apply pre).emb e W, insert e (v.apply pre).dom⟩ := by
    rw [EmbView.apply_append, EmbView.apply_singleton]
  obtain ⟨hr0, hr1, hrE⟩ := hrep
  refine ⟨pre ++ [(e, W)], hpre', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · simp [h4]
  · simp [hi_def]; omega
  · simp
  · simp [hfold]
  · -- the table
    rw [hview, hfold]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm3_ne _ (by omega), hm2_lo _ (by omega)]; exact hr0
    · rw [hm3_ne _ (by omega), hm2_lo _ (by omega)]; exact hr1
    intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee
      simp only [Function.update_self]
      refine ⟨heCap, by omega, by simp [hm3], ?_⟩
      intro j hj
      have hj' : j < 1 + 2 * W.length := by simpa [mWalkEncode_length] using hj
      rw [hm3_ne _ (by omega), hcp j hj', hwalk j hj']
      exact hXw j hj
    · have he'd : e' ∈ (v.apply pre).dom := he'.resolve_left hee
      obtain ⟨hlt', hge', htab', hwk'⟩ := hrE e' he'd
      simp only [Function.update_of_ne hee]
      refine ⟨hlt', hge', ?_, ?_⟩
      · rw [hm3_ne _ (by omega), hm2_lo _ (by omega)]; exact htab'
      · -- the old walk is below `H` and above the table
        have hbelow : s.1 e' + walkWords ((v.apply pre).emb e') ≤ H := by
          rcases hloc e' he'd with ⟨hp, hem, hdom⟩ | ⟨_, hle⟩
          · have := hold e' hdom
            rw [hp, hem]; omega
          · exact hle
        refine hwk'.of_agree fun x hx1 hx2 => ?_
        simp only [walkWords] at hbelow
        rw [hm3_ne _ (by omega), hm2_lo _ (by omega)]
  · intro x hx hx'
    rw [hm3_ne _ (by omega), hm2_lo _ (by omega)]
    exact hfr x hx hx'
  · rw [hfold]
    intro x hx
    simp only at hx
    rw [hm3_ne _ (by omega), hm2_hi _ hx]
    exact hz x (by omega)
  · rw [hview, hfold]
    intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee
      right
      simp [walkWords]
      omega
    · have he'd : e' ∈ (v.apply pre).dom := he'.resolve_left hee
      simp only [Function.update_of_ne hee]
      rcases hloc e' he'd with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩

end

end MinCostFlow.SparseCore.Program.Read
