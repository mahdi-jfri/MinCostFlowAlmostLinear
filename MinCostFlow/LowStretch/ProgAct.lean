module

public import MinCostFlow.LowStretch.ProgArcs2

/-!
# The radius and the active pairs of a cluster

After Dijkstra from the center, the program needs the radius `Δ` and the active pairs.
* `maxP` returns the largest tentative cost of the nodes `u < s` (`maxP_spec`). Once the run is
  over, these are the distances, so this is `Δ`.
* `actP` copies the stored entries whose weight `ω` has `ω² ≤ QD` to a new array, in order, and
  returns how many it copied (`actP_spec`). With `QD = Q Δ θ` these are the active pairs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The largest tentative cost -/

/-- The tentative cost of node `u`, as `DL.tentOf` reads it. -/
def tvOf (mem : ℕ → ℕ) (TS NN rs INF u : ℕ) : ℕ :=
  if mem (TS + u) = rs then mem (TS + NN + u) else INF

/-- `maxP` with `args = [TS, NN, s, rs, INF]`. -/
def maxP : Stmt :=
  .seq (.assign 6 (.const 0))
  (.seq (forRange 5 (.const 0) (.reg 2)
    (.seq (.cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 5))) (.reg 3))
        (.assign 7 (.load (.bin .add (.bin .add (.reg 0) (.reg 1)) (.reg 5))))
        (.assign 7 (.reg 4)))
      (.cond (.bin .lt (.reg 6) (.reg 7)) (.assign 6 (.reg 7)) .nop)))
  (.ret (.reg 6)))

theorem maxP_noRand : maxP.NoRand := by simp [maxP, forRange, forUp, Stmt.NoRand]

/-- The contract of `maxP`. -/
def maxPC (w : ℕ) : Contract where
  pre args mem := ∃ TS NN s rs INF, args = [TS, NN, s, rs, INF] ∧ TS + NN + s + 1 < 2 ^ w ∧
    ∀ u < s, mem (TS + NN + u) < 2 ^ w
  post args mem v mem' := mem' = mem ∧ ∀ TS NN s rs INF, args = [TS, NN, s, rs, INF] →
    v = (Finset.range s).sup (tvOf mem TS NN rs INF)
  cost args _ := 60 * args.getD 2 0 + 30

theorem maxP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [maxP]) :
    MeetsContract w p b (maxPC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨TS, NN, s, rs, INF, rfl, hl, hv⟩ := hpre
  have hproc : p.procs[b]? = some maxP := hp 0 (by simp)
  clear hp
  have hw1 : 1 < 2 ^ w := by omega
  have hwA := hwords
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hwA
  obtain ⟨wTS, wNN, ws, wrs, wINF⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = TS ∧ st.regs 1 = NN ∧ st.regs 2 = s ∧
    st.regs 3 = rs ∧ st.regs 4 = INF ∧ st.mem = mem
  have hRn : ∀ st st' : State, R st → st'.mem = st.mem → (∀ r < 5, st'.regs r = st.regs r) →
      R st' :=
    fun st st' ⟨a0, a1, a2, a3, a4, a5⟩ hm hs =>
      ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
        (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, hm.trans a5⟩
  have htv : ∀ u < s, tvOf mem TS NN rs INF u < 2 ^ w := fun u hu => by
    unfold tvOf; split_ifs
    · exact hv u hu
    · exact wINF
  let I : ℕ → State → Prop := fun u st => R st ∧ st.regs 5 = u ∧
    st.regs 6 = (Finset.range u).sup (tvOf mem TS NN rs INF)
  have hsup : ∀ u ≤ s, (Finset.range u).sup (tvOf mem TS NN rs INF) < 2 ^ w := by
    intro u hu
    induction u with
    | zero => simp
    | succ u ih =>
      rw [Finset.range_add_one, Finset.sup_insert]
      have := ih (by omega); have := htv u (by omega)
      exact max_lt (by assumption) (by assumption)
  have hL := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .seq (.cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 5))) (.reg 3))
        (.assign 7 (.load (.bin .add (.bin .add (.reg 0) (.reg 1)) (.reg 5))))
        (.assign 7 (.reg 4)))
      (.cond (.bin .lt (.reg 6) (.reg 7)) (.assign 6 (.reg 7)) .nop))
    (P := fun st => R st ∧ st.regs 6 = 0) (Inv := I) 40 0 s (Nat.zero_le _) hw1
    (fun _ => ws)
    (fun st ⟨hr, h6⟩ => ⟨by eval_expr, hRn st _ hr rfl (fun r hr => by
        simp only [Function.update_apply]; rw [if_neg (by omega)]), by simp,
      by simp only [Function.update_apply]; simp [h6]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.1; eval_expr)
    (fun u _ hu st ω hI => by
      obtain ⟨hr, h5, h6⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hr
      have b1 : st.mem (TS + u) < 2 ^ w ∨ True := Or.inr trivial
      have b2 : st.mem (TS + NN + u) < 2 ^ w := by rw [a5]; exact hv u hu
      have hs6 := hsup u (by omega)
      have ht := htv u hu
      rw [← h6] at hs6
      have hsup1 : (Finset.range (u + 1)).sup (tvOf mem TS NN rs INF) =
          max (tvOf mem TS NN rs INF u) ((Finset.range u).sup (tvOf mem TS NN rs INF)) := by
        rw [Finset.range_add_one, Finset.sup_insert]
      refine runs_start_le ?_
      wram_run
      all_goals first
        | wram_cost
        | (refine ⟨⟨hRn st _ hr' rfl (fun r hr => by
              simp only [Function.update_apply]; split_ifs <;> omega), by simp, ?_⟩,
            by simp [h5]⟩
           simp only [a5] at *
           simp only [Function.update_apply, hsup1, tvOf]
           try (split_ifs <;> omega)))
  refine ⟨maxP, hproc, ?_⟩
  dsimp only [maxP]
  refine runs_start_le ?_
  wram_step
  refine runs_seq_triple_le hL ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp⟩ (fun st1 h1 => ?_)
  obtain ⟨⟨a0, a1, a2, a3, a4, a5⟩, -, h6⟩ := h1
  refine runs_ret_le (by eval_expr) ⟨a5, fun TS' NN' s' rs' INF' he => ?_⟩ ?_
  · simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := he
    rw [← h6]; rfl
  · simp only [maxPC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

/-! ### The active entries -/

/-- The pair of stored entry `j`. -/
def gpr (mem : ℕ → ℕ) (SA j : ℕ) : ℕ := mem (SA + 2 * j)

/-- The half flag of stored entry `j`. -/
def gfl (mem : ℕ → ℕ) (SA j : ℕ) : ℕ := mem (SA + 2 * j + 1)

/-- The entries before `k` whose weight `ω` has `ω² ≤ QD`. -/
def selL (mem : ℕ → ℕ) (SA PW QD k : ℕ) : List ℕ :=
  (List.range k).filter fun j => mem (PW + gpr mem SA j) * mem (PW + gpr mem SA j) ≤ QD

theorem selL_succ (mem : ℕ → ℕ) (SA PW QD k : ℕ) :
    selL mem SA PW QD (k + 1) = selL mem SA PW QD k ++
      (if mem (PW + gpr mem SA k) * mem (PW + gpr mem SA k) ≤ QD then [k] else []) := by
  unfold selL
  rw [List.range_succ, List.filter_append]
  split_ifs with h <;> simp [h]

theorem selL_length_le (mem : ℕ → ℕ) (SA PW QD k : ℕ) : (selL mem SA PW QD k).length ≤ k := by
  unfold selL
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_selL {mem : ℕ → ℕ} {SA PW QD k j : ℕ} :
    j ∈ selL mem SA PW QD k ↔ j < k ∧ mem (PW + gpr mem SA j) * mem (PW + gpr mem SA j) ≤ QD := by
  unfold selL; simp

/-- The output after the entries of `l`: entry `i` of `l` is copied to cells `2i` and `2i + 1`. -/
def ActDone (mem M : ℕ → ℕ) (SA OUT : ℕ) (l : List ℕ) : Prop :=
  ∀ i < l.length, M (OUT + 2 * i) = gpr mem SA (l.getD i 0) ∧
    M (OUT + 2 * i + 1) = gfl mem SA (l.getD i 0)

theorem ActDone.step {mem M : ℕ → ℕ} {SA OUT : ℕ} {l : List ℕ} (hd : ActDone mem M SA OUT l)
    (j : ℕ) {A1 A2 V1 V2 : ℕ} (e1 : A1 = OUT + 2 * l.length) (f1 : V1 = gpr mem SA j)
    (e2 : A2 = OUT + 2 * l.length + 1) (f2 : V2 = gfl mem SA j) :
    ActDone mem (Function.update (Function.update M A1 V1) A2 V2) SA OUT (l ++ [j]) ∧
    ∀ a, a ≠ OUT + 2 * l.length → a ≠ OUT + 2 * l.length + 1 →
      Function.update (Function.update M A1 V1) A2 V2 a = M a := by
  subst A1 A2 V1 V2
  refine ⟨fun i hi => ?_, fun a h1 h2 => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i = l.length
    · subst e
      have g : (l ++ [j]).getD l.length 0 = j := by simp
      rw [g]
      refine ⟨?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · have hi' : i < l.length := by omega
      have g : (l ++ [j]).getD i 0 = l.getD i 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi',
          List.getElem_append_left hi']
      rw [g]
      obtain ⟨d1, d2⟩ := hd i hi'
      refine ⟨?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne] <;> assumption
  · simp (disch := omega) only [Function.update_of_ne]

theorem ActDone.of_eq {mem M : ℕ → ℕ} {SA OUT : ℕ} {l l' : List ℕ} (hd : ActDone mem M SA OUT l)
    (e : l' = l) : ActDone mem M SA OUT l' := e ▸ hd

/-- The body of `actP`, for entry `j` in register `5` and the count in register `6`. -/
def actB : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 5)))))
  (.seq (.assign 8 (.load (.bin .add (.reg 2) (.reg 7))))
  (.cond (.bin .lt (.reg 4) (.bin .mul (.reg 8) (.reg 8))) .nop
    (.seq (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6))) (.reg 7))
    (.seq (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6))) (.const 1))
        (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 5))) (.const 1))))
      (.assign 6 (.bin .add (.reg 6) (.const 1)))))))

/-- `actP` with `args = [nS, SA, PW, OUT, QD]`. -/
def actP : Stmt :=
  .seq (.assign 6 (.const 0))
  (.seq (forRange 5 (.const 0) (.reg 0) actB)
  (.ret (.reg 6)))

theorem actP_noRand : actP.NoRand := by simp [actP, actB, forRange, forUp, Stmt.NoRand]

/-- The contract of `actP`. -/
def actPC (w : ℕ) : Contract where
  pre args mem := ∃ nS SA PW OUT QD, args = [nS, SA, PW, OUT, QD] ∧
    SA + 2 * nS ≤ OUT ∧ OUT + 2 * nS + 2 < 2 ^ w ∧
    ∀ j < nS, PW + gpr mem SA j < OUT ∧
      mem (PW + gpr mem SA j) * mem (PW + gpr mem SA j) < 2 ^ w ∧
      gpr mem SA j < 2 ^ w ∧ gfl mem SA j < 2 ^ w
  post args mem v mem' := ∀ nS SA PW OUT QD, args = [nS, SA, PW, OUT, QD] →
    v = (selL mem SA PW QD nS).length ∧ ActDone mem mem' SA OUT (selL mem SA PW QD nS) ∧
    ∀ a, ¬ (OUT ≤ a ∧ a < OUT + 2 * nS) → mem' a = mem a
  cost args _ := 80 * args.getD 0 0 + 30

theorem actP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [actP]) :
    MeetsContract w p b (actPC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨nS, SA, PW, OUT, QD, rfl, l1, l2, hj⟩ := hpre
  have hproc : p.procs[b]? = some actP := hp 0 (by simp)
  clear hp
  have hw1 : 1 < 2 ^ w := by omega
  have hwA := hwords
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hwA
  obtain ⟨wnS, wSA, wPW, wOUT, wQD⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = nS ∧ st.regs 1 = SA ∧ st.regs 2 = PW ∧
    st.regs 3 = OUT ∧ st.regs 4 = QD
  have hRn : ∀ st st' : State, R st → (∀ r < 5, st'.regs r = st.regs r) → R st' :=
    fun st st' ⟨a0, a1, a2, a3, a4⟩ hs =>
      ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
        (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4⟩
  let I : ℕ → State → Prop := fun j st => R st ∧ st.regs 5 = j ∧
    st.regs 6 = (selL mem SA PW QD j).length ∧ ActDone mem st.mem SA OUT (selL mem SA PW QD j) ∧
    ∀ a, ¬ (OUT ≤ a ∧ a < OUT + 2 * (selL mem SA PW QD j).length) → st.mem a = mem a
  have hL := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 0)
    (body := actB) (P := fun st => R st ∧ st.regs 6 = 0 ∧ st.mem = mem) (Inv := I) 60 0 nS
    (Nat.zero_le _) hw1 (fun _ => wnS)
    (fun st ⟨hr, h6, hm⟩ => ⟨by eval_expr, hRn st _ hr (fun r hr => by
        simp only [Function.update_apply]; rw [if_neg (by omega)]), by simp,
      by simp only [Function.update_apply]; simp [h6, selL],
      fun i hi => by simp [selL] at hi, fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hjn st ω hI => by
      obtain ⟨hr, h5, h6, hdone, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4⟩ := hr
      obtain ⟨b1, b2, b3, b4⟩ := hj j hjn
      have hlen := selL_length_le mem SA PW QD j
      have e1 : st.mem (SA + 2 * j) = gpr mem SA j := hfr _ (by omega)
      have e2 : st.mem (SA + 2 * j + 1) = gfl mem SA j := hfr _ (by omega)
      have e3 : st.mem (PW + gpr mem SA j) = mem (PW + gpr mem SA j) := hfr _ (by omega)
      have b1' : st.mem (PW + st.mem (SA + 2 * j)) * st.mem (PW + st.mem (SA + 2 * j)) < 2 ^ w := by
        rw [e1, e3]; exact b2
      have b3' : st.mem (SA + 2 * j) < 2 ^ w := by rw [e1]; exact b3
      have b4' : st.mem (SA + 2 * j + 1) < 2 ^ w := by rw [e2]; exact b4
      have b5 : st.mem (PW + st.mem (SA + 2 * j)) < 2 ^ w := by
        rw [e1, e3]
        rcases Nat.eq_zero_or_pos (mem (PW + gpr mem SA j)) with h0 | h0
        · rw [h0]; omega
        · exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ h0) b2
      have key := ActDone.step hdone j (M := st.mem) (A1 := _) (A2 := _) (V1 := _) (V2 := _)
        rfl rfl rfl rfl
      have hs := selL_succ mem SA PW QD j
      have e2' : Function.update st.mem (OUT + 2 * (selL mem SA PW QD j).length) (gpr mem SA j)
          (SA + 2 * j + 1) = gfl mem SA j := by rw [Function.update_of_ne (by omega)]; exact e2
      have b6 : st.mem (st.regs 2 + st.mem (SA + 2 * j)) * st.mem (st.regs 2 + st.mem (SA + 2 * j))
          < 2 ^ w := by rw [a2]; exact b1'
      refine runs_start_le ?_
      unfold actB
      wram_run
      all_goals first
        | wram_cost
        | (have hc := hcond
           try simp only [a2, a4, e1, e3] at hc
           rw [if_neg (by omega), List.append_nil] at hs
           refine ⟨⟨hRn st _ hr' (fun r hr => by
              simp only [Function.update_apply]; split_ifs <;> omega), by simp, ?_, ?_, ?_⟩,
            by simp [h5]⟩
           · simp only [Function.update_apply, hs]; simpa using h6
           · rw [hs]; exact hdone
           · rw [hs]; exact hfr)
        | (have hc := hcond
           try simp only [a2, a4, e1, e3] at hc
           rw [if_pos (by omega)] at hs
           refine ⟨⟨hRn st _ hr' (fun r hr => by
              simp only [Function.update_apply]; split_ifs <;> omega), by simp, ?_, ?_, ?_⟩,
            by simp [h5]⟩
           · simp only [Function.update_apply, hs, List.length_append, List.length_singleton]
             simp [h6]
           · rw [hs]
             convert key.1 using 2 <;> simp [a1, a3, h5, h6, e1, e2, e2']
           · intro a ha
             rw [hs] at ha
             simp only [List.length_append, List.length_singleton] at ha
             refine Eq.trans ?_ ((key.2 a (by omega) (by omega)).trans (hfr a (by omega)))
             congr 1 <;> simp [a1, a3, h5, h6, e1, e2, e2']))
  refine ⟨actP, hproc, ?_⟩
  dsimp only [actP]
  refine runs_start_le ?_
  wram_step
  refine runs_seq_triple_le hL ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp, rfl⟩ (fun st1 h1 => ?_)
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, -, h6, hd, hfr⟩ := h1
  refine runs_ret_le (by eval_expr) (fun nS' SA' PW' OUT' QD' he => ?_) ?_
  · simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := he
    have hlen := selL_length_le mem SA PW QD nS
    exact ⟨by rw [← h6]; rfl, hd, fun a ha => hfr a (by omega)⟩
  · simp only [actPC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

end MinCostFlow.LowStretch
