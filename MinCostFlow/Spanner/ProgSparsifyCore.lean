module

public import MinCostFlow.Spanner.ProgTask1Proof
public import MinCostFlow.Spanner.ProgTask2Proof
public import MinCostFlow.Spanner.ProgTask3Proof

@[expose] public section

/-!
# Tasks 1, 2 and 3 in a Row

`sparsifyCoreBody` is the first part of the `Sparsify` procedure. It calls Task 1 (the witness
graph), Task 2 (the embedding of `W` into `J`) and Task 3 (the embedding of `J` into `W`), each
on the heap end returned by the call before. Its contract `sparsifyCoreContract` says that the
three outputs hold, one after the other, and its cost is the sum of the three task costs plus a
constant.

The tasks are called through their contracts (`task1Contract`, `task2Contract`,
`task3Contract`), so the procedure addresses are parameters. The word-size condition of the pre
is stated through the outputs of Tasks 1 and 2 (`SparsifyCoreWordOK`), because the word bounds of
Tasks 2 and 3 mention the heap ends `v1` and `v2`. The main result is
`sparsifyCore_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- First three calls of `Sparsify`: Task 1, Task 2, Task 3, leaving `v1`, `v2`, `v3` in `r4`,
`r5`, `r6`. -/
def sparsifyCorePrefix (t1 t2 t3 : ℕ) : Stmt :=
  Stmt.seq (.call 4 t1 [.reg 0, .reg 1, .reg 2, .reg 3])
    (Stmt.seq (.call 5 t2 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
      (.call 6 t3 [.reg 1, .reg 3, .reg 5]))

theorem sparsifyCorePrefix_noRand (t1 t2 t3 : ℕ) : (sparsifyCorePrefix t1 t2 t3).NoRand := by
  simp [sparsifyCorePrefix, Stmt.NoRand]

/-- Procedure of the first part of `Sparsify`, at `args = [hAddr, jAddr, embJHAddr, h]`. -/
def sparsifyCoreBody (t1 t2 t3 : ℕ) : Stmt :=
  Stmt.seq (.call 4 t1 [.reg 0, .reg 1, .reg 2, .reg 3])
    (Stmt.seq (.call 5 t2 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
      (Stmt.seq (.call 6 t3 [.reg 1, .reg 3, .reg 5])
        (.ret (.reg 6))))

/-- The input of Task 2 after Task 1 returned `v1`. -/
def Task1Input.toT2 (inp : Task1Input) (v1 : ℕ) : Task2Input :=
  ⟨inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1, inp.H', inp.J, inp.embJH⟩

/-- The input of Task 3 after Task 2 returned `v2`. -/
def Task1Input.toT3 (inp : Task1Input) (v2 : ℕ) : Task3Input :=
  ⟨inp.jAddr, inp.h, v2, inp.H', inp.J, inp.embJH⟩

/-- The word size fits Tasks 2 and 3 on every output of Tasks 1 and 2 (with the Task 1 heap end
below its cap `Task1Input.maxHeapEnd`). -/
def SparsifyCoreWordOK (impl : SpannerToolImpl) (inp : Task1Input) (w : ℕ) : Prop :=
  ∀ memPre mem1 v1,
    Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH memPre mem1 v1 w →
    v1 ≤ inp.maxHeapEnd impl → (inp.toT2 v1).WordWidthOK impl w ∧
    ∀ mem2 v2, Task2OutAt impl (inp.toT2 v1) mem1 mem2 v2 w → (inp.toT3 v2).WordWidthOK impl w

/-- The outputs of Tasks 1, 2 and 3, one after the other. -/
def SparsifyCoreOut (impl : SpannerToolImpl) (inp : Task1Input) (mem mem' : ℕ → ℕ)
    (v3 w : ℕ) : Prop :=
  ∃ mem1 v1 mem2 v2,
    Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem mem1 v1 w ∧
    Task2OutAt impl (inp.toT2 v1) mem1 mem2 v2 w ∧
    Task3OutAt impl (inp.toT3 v2) mem2 mem' v3 w

/-- Cost of the first part of `Sparsify`: the three task costs plus a constant. -/
noncomputable def sparsifyCoreCost (impl : SpannerToolImpl) (inp : Task1Input)
    (mem : ℕ → ℕ) : ℕ :=
  task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) +
    task2Cost impl inp.J (length inp.J inp.embJH) (inp.toT2 0).embVertSum +
    task3Cost impl inp.J + 40

open Classical in
/-- Contract of `sparsifyCoreBody`. -/
noncomputable def sparsifyCoreContract (impl : SpannerToolImpl) (w : ℕ) : Contract where
  pre args mem := ∃ inp : Task1Input, args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
    inp.Valid impl mem w ∧ SparsifyCoreWordOK impl inp w
  post args mem v3 mem' := ∀ inp : Task1Input,
    args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] → inp.Valid impl mem w →
    SparsifyCoreWordOK impl inp w → SparsifyCoreOut impl inp mem mem' v3 w
  cost args mem :=
    if h : ∃ inp : Task1Input, args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
        inp.Valid impl mem w ∧ SparsifyCoreWordOK impl inp w then
      sparsifyCoreCost impl (Classical.choose h) mem
    else 0

/-- Two valid inputs of Task 1 with the same addresses have the same `J`, and the same `embJH`
on the edges of `J`. -/
lemma task1_inputs_agree {impl : SpannerToolImpl} {mem : ℕ → ℕ} {w : ℕ} {inp₁ inp₂ : Task1Input}
    (hj : inp₁.jAddr = inp₂.jAddr) (he : inp₁.embJHAddr = inp₂.embJHAddr)
    (hv₁ : inp₁.Valid impl mem w) (hv₂ : inp₂.Valid impl mem w) :
    inp₁.J = inp₂.J ∧ ∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e := by
  have hJ : inp₁.J = inp₂.J := by
    have g1 := graphAt_iff_readGraph.mp hv₁.2.2.2.1
    have g2 := graphAt_iff_readGraph.mp hv₂.2.2.2.1
    rw [← g1, ← g2]
    exact congrArg (readGraph mem) hj
  refine ⟨hJ, fun e hem => ?_⟩
  have w1 := hv₁.2.2.2.2.2.1 e hem
  have w2 := hv₂.2.2.2.2.2.1 e (hJ ▸ hem)
  rw [← he] at w2
  exact walkAt_unique w1 w2

/-- The `length` and the vertex sum of `embJH` depend only on its values on the edges of `J`. -/
lemma t1_emb_stats_congr {J : Graph} {e₁ e₂ : ℕ → Walk} (h : ∀ e < J.m, e₁ e = e₂ e) :
    length J e₁ = length J e₂ ∧
      (∑ e ∈ Finset.range J.m, (e₁ e).verts.length) =
        ∑ e ∈ Finset.range J.m, (e₂ e).verts.length := by
  refine ⟨?_, Finset.sum_congr rfl fun e he => by rw [h e (Finset.mem_range.mp he)]⟩
  unfold length
  exact Finset.fold_congr fun e he => by rw [h e (Finset.mem_range.mp he)]

/-- A run of `sparsifyCoreBody` from a valid input. -/
theorem sparsifyCore_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl} {t1 t2 t3 : ℕ}
    (h1 : MeetsContract w p t1 (task1Contract impl w))
    (h2 : MeetsContract w p t2 (task2Contract impl w))
    (h3 : MeetsContract w p t3 (task3Contract impl w))
    (inp : Task1Input) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h], a < 2 ^ w)
    (hv : inp.Valid impl mem w) (hwok : SparsifyCoreWordOK impl inp w) :
    ∃ o st' c,
      Runs w p ω (sparsifyCoreBody t1 t2 t3)
        (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos) o st' c ∧
      SparsifyCoreOut impl inp mem st'.mem o.value w ∧ c ≤ sparsifyCoreCost impl inp mem := by
  obtain ⟨hH', hgH, hJv, hgJ, hEmb, hEA, hEB, hHle, hJle, hZ, hW1⟩ := hv
  have hv : inp.Valid impl mem w := ⟨hH', hgH, hJv, hgJ, hEmb, hEA, hEB, hHle, hJle, hZ, hW1⟩
  -- The cost of the Task 1 call.
  have hc1 : (task1Contract impl w).cost [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem =
      task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) := by
    have h_ex : ∃ inp' : Task1Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧ inp'.Valid impl mem w :=
      ⟨inp, rfl, hv⟩
    unfold task1Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, hj, he, _⟩ := hargs
    rw [← hj, ← he, ← (task1_inputs_agree hj he hv hvc).1]
  unfold sparsifyCoreBody
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h]) h1 ?_ hwords ?_ ?_
  · simp [evalArgs, Expr.eval, startState]
  · exact ⟨inp, rfl, hv⟩
  intro v1 mem1 pos1 hpost1
  obtain ⟨hT1, hcap1⟩ := hpost1 inp rfl hv
  obtain ⟨hw2, hw3⟩ := hwok mem mem1 v1 hT1 hcap1
  have hT1c := hT1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hagr1, -⟩ := hT1c
  -- The pre of Task 2.
  have hEmb1 := embAt_preserve hEA hEB fun k hk => hagr1 k hk
  have hv2 : (inp.toT2 v1).Valid impl mem1 w :=
    ⟨hH', GraphAt.of_agree_below hgH hHle hagr1, hJv, GraphAt.of_agree_below hgJ hJle hagr1,
      hEmb, hEmb1.1, hEmb1.2, hHle, hJle, ⟨mem, hT1⟩, hw2⟩
  have ctx2 := t2CtxOfValid hv2
  have hb2 := t2SetupHdr_word_bounds ctx2
  dsimp only at hb2
  obtain ⟨_, _, ht1v1, _, _, _, _, hv1w, _⟩ := hb2
  have ht1v1' : inp.h + 6 ≤ v1 := ht1v1
  have hv1w' : v1 + 32 < 2 ^ w := hv1w
  have hc2 : (task2Contract impl w).cost [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1] mem1 =
      task2Cost impl inp.J (length inp.J inp.embJH) (inp.toT2 0).embVertSum := by
    have h_ex : ∃ inp' : Task2Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.t1OutAddr, inp'.v1] ∧
        inp'.Valid impl mem1 w := ⟨inp.toT2 v1, rfl, hv2⟩
    unfold task2Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, hj, he, _, _⟩ := hargs
    have hJ : inp.J = inp'.J := by
      have g1 := graphAt_iff_readGraph.mp hv2.2.2.2.1
      have g2 := graphAt_iff_readGraph.mp hvc.2.2.2.1
      show (inp.toT2 v1).J = inp'.J
      rw [← g1, ← g2]
      exact congrArg (readGraph mem1) hj
    have hemb : ∀ e < inp.J.m, inp.embJH e = inp'.embJH e := fun e hem => by
      have w1 := hv2.2.2.2.2.2.1 e hem
      have w2 := hvc.2.2.2.2.2.1 e (hJ ▸ hem)
      rw [← he] at w2
      exact walkAt_unique w1 w2
    obtain ⟨hlen, hsum⟩ := t1_emb_stats_congr hemb
    unfold Task2Input.embVertSum
    simp only [Task1Input.toT2]
    rw [← hJ, ← hlen, ← hsum]
  refine runs_seq_call_le (vs := [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1]) h2
    ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have := hwords inp.hAddr (by simp); have := hwords inp.jAddr (by simp)
    have := hwords inp.embJHAddr (by simp)
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  · exact ⟨inp.toT2 v1, rfl, hv2⟩
  intro v2 mem2 pos2 hpost2
  have hT2 := hpost2 (inp.toT2 v1) rfl hv2
  have hw3' := hw3 mem2 v2 hT2
  have hT2c := hT2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hagr2, hzf2, hv12, -⟩ := hT2c
  have hagr2' : ∀ x < v1, mem2 x = mem1 x := hagr2
  have hzf2' : ZeroFrom mem2 v2 := hzf2
  have hv12' : v1 + 32 ≤ v2 := hv12
  -- The pre of Task 3.
  have hagr21 : ∀ x < inp.h, mem2 x = mem x := fun x hx =>
    (hagr2' x (by omega)).trans (hagr1 x hx)
  have hv3 : (inp.toT3 v2).Valid impl mem2 w :=
    ⟨hJv, GraphAt.of_agree_below hgJ hJle hagr21, hJle,
      ⟨mem, mem1, v1, fun x hx => (hagr2' x hx).symm ▸ rfl, by simp only [Task1Input.toT3]; omega, hzf2', hT1⟩, hw3'⟩
  have hv2w : v2 < 2 ^ w := by
    obtain ⟨_, _, hmax⟩ := hw3'
    have h1 : Task3Input.maxHeapEnd impl (inp.toT3 v2) + 3 ≤
        Task3Input.maxWordBound impl (inp.toT3 v2) := le_max_left _ _
    have h2 : Task3Input.staticEndCap impl (inp.toT3 v2) ≤
        Task3Input.maxHeapEnd impl (inp.toT3 v2) := by
      unfold Task3Input.maxHeapEnd; dsimp only; omega
    have h3 : v2 ≤ Task3Input.staticEndCap impl (inp.toT3 v2) := by
      unfold Task3Input.staticEndCap; simp only [Task1Input.toT3]; omega
    omega
  have hc3 : (task3Contract impl w).cost [inp.jAddr, inp.h, v2] mem2 = task3Cost impl inp.J := by
    have h_ex : ∃ inp' : Task3Input,
        [inp.jAddr, inp.h, v2] = [inp'.jAddr, inp'.t1OutAddr, inp'.v2] ∧
        inp'.Valid impl mem2 w := ⟨inp.toT3 v2, rfl, hv3⟩
    unfold task3Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    have hj : inp.jAddr = inp'.jAddr := (List.cons_eq_cons.mp hargs).1
    have hJ : inp.J = inp'.J := by
      have g1 := graphAt_iff_readGraph.mp hv3.2.1
      have g2 := graphAt_iff_readGraph.mp hvc.2.1
      show (inp.toT3 v2).J = inp'.J
      rw [← g1, ← g2]
      exact congrArg (readGraph mem2) hj
    rw [← hJ]
  refine runs_seq_call_le (vs := [inp.jAddr, inp.h, v2]) h3 ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update_apply]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have := hwords inp.jAddr (by simp); have := hwords inp.h (by simp)
    rcases ha with rfl | rfl | rfl <;> omega
  · exact ⟨inp.toT3 v2, rfl, hv3⟩
  intro v3 mem3 pos3 hpost3
  have hT3 := hpost3 (inp.toT3 v2) rfl hv3
  refine runs_ret_le (v := v3) (by simp [Expr.eval, Function.update_apply])
    ⟨mem1, v1, mem2, v2, hT1, hT2, hT3⟩ ?_
  have hm0 : (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos).mem = mem := rfl
  rw [hm0, hc1, hc2, hc3]
  simp only [Expr.size, argsSize, sparsifyCoreCost]
  omega

/-- `sparsifyCoreBody` at `base` meets `sparsifyCoreContract`. -/
theorem sparsifyCore_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {base t1 t2 t3 : ℕ} (hbody : p.procs[base]? = some (sparsifyCoreBody t1 t2 t3))
    (h1 : MeetsContract w p t1 (task1Contract impl w))
    (h2 : MeetsContract w p t2 (task2Contract impl w))
    (h3 : MeetsContract w p t3 (task3Contract impl w)) :
    MeetsContract w p base (sparsifyCoreContract impl w) := by
  intro args mem pos ω hwords hpre
  have h_ex := hpre
  obtain ⟨hargs, hvc, hwc⟩ := Classical.choose_spec h_ex
  set inp := Classical.choose h_ex with hinp
  rw [hargs] at hwords ⊢
  obtain ⟨o, st', c, hr, hout, hc⟩ := sparsifyCore_runs h1 h2 h3 inp mem pos ω hwords hvc hwc
  refine ⟨_, hbody, o, st', c, hr, ?_, ?_⟩
  · intro inp' hargs' hv' hw'
    have hwords' : ∀ a ∈ [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h], a < 2 ^ w := by
      rw [← hargs']; exact hwords
    obtain ⟨o', st'', c', hr', hout', -⟩ := sparsifyCore_runs h1 h2 h3 inp' mem pos ω hwords' hv' hw'
    rw [← hargs'] at hr'
    obtain ⟨ho, hst, -⟩ := Runs.det hr hr'
    rw [ho, hst]
    exact hout'
  · have h_ex' : ∃ inp' : Task1Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧
        inp'.Valid impl mem w ∧ SparsifyCoreWordOK impl inp' w := ⟨inp, rfl, hvc, hwc⟩
    unfold sparsifyCoreContract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex')]
    have hspec := Classical.choose_spec h_ex'
    generalize Classical.choose h_ex' = inp' at hspec ⊢
    obtain ⟨hargs2, hvc2, -⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs2
    obtain ⟨_, hj, he, _⟩ := hargs2
    obtain ⟨hJ, hemb⟩ := task1_inputs_agree hj he hvc hvc2
    obtain ⟨hlen, hsum⟩ := t1_emb_stats_congr hemb
    unfold sparsifyCoreCost Task2Input.embVertSum at hc ⊢
    simp only [Task1Input.toT2] at hc ⊢
    rw [← hj, ← he, ← hJ, ← hlen, ← hsum]
    exact hc

/-- Run of `sparsifyCorePrefix`: executes Tasks 1, 2, 3 and leaves `v1`, `v2`, `v3` in `r4`, `r5`,
`r6`, with `v1 ≤ inp.maxHeapEnd impl` and all three task postconditions. -/
theorem sparsifyCorePrefix_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl} {t1 t2 t3 : ℕ}
    (h1 : MeetsContract w p t1 (task1Contract impl w))
    (h2 : MeetsContract w p t2 (task2Contract impl w))
    (h3 : MeetsContract w p t3 (task3Contract impl w))
    (inp : Task1Input) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h], a < 2 ^ w)
    (hv : inp.Valid impl mem w) (hwok : SparsifyCoreWordOK impl inp w) :
    ∃ o st' c,
      Runs w p ω (sparsifyCorePrefix t1 t2 t3)
        (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos) o st' c ∧
      (o = .normal ∧
        st'.regs 0 = inp.hAddr ∧ st'.regs 1 = inp.jAddr ∧ st'.regs 2 = inp.embJHAddr ∧
        st'.regs 3 = inp.h ∧
        ∃ mem1 v1 mem2 v2 v3,
          st'.regs 4 = v1 ∧ st'.regs 5 = v2 ∧ st'.regs 6 = v3 ∧
          Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem mem1 v1 w ∧
          v1 ≤ inp.maxHeapEnd impl ∧
          Task2OutAt impl (inp.toT2 v1) mem1 mem2 v2 w ∧
          Task3OutAt impl (inp.toT3 v2) mem2 st'.mem v3 w) ∧
      c ≤ sparsifyCoreCost impl inp mem := by
  obtain ⟨hH', hgH, hJv, hgJ, hEmb, hEA, hEB, hHle, hJle, hZ, hW1⟩ := hv
  have hv : inp.Valid impl mem w := ⟨hH', hgH, hJv, hgJ, hEmb, hEA, hEB, hHle, hJle, hZ, hW1⟩
  have hc1 : (task1Contract impl w).cost [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem =
      task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) := by
    have h_ex : ∃ inp' : Task1Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧ inp'.Valid impl mem w :=
      ⟨inp, rfl, hv⟩
    unfold task1Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, hj, he, _⟩ := hargs
    rw [← hj, ← he, ← (task1_inputs_agree hj he hv hvc).1]
  unfold sparsifyCorePrefix
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h]) h1 ?_ hwords ?_ ?_
  · simp [evalArgs, Expr.eval, startState]
  · exact ⟨inp, rfl, hv⟩
  intro v1 mem1 pos1 hpost1
  obtain ⟨hT1, hcap1⟩ := hpost1 inp rfl hv
  obtain ⟨hw2, hw3⟩ := hwok mem mem1 v1 hT1 hcap1
  have hT1c := hT1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hagr1, -⟩ := hT1c
  have hEmb1 := embAt_preserve hEA hEB fun k hk => hagr1 k hk
  have hv2 : (inp.toT2 v1).Valid impl mem1 w :=
    ⟨hH', GraphAt.of_agree_below hgH hHle hagr1, hJv, GraphAt.of_agree_below hgJ hJle hagr1,
      hEmb, hEmb1.1, hEmb1.2, hHle, hJle, ⟨mem, hT1⟩, hw2⟩
  have ctx2 := t2CtxOfValid hv2
  have hb2 := t2SetupHdr_word_bounds ctx2
  dsimp only at hb2
  obtain ⟨_, _, ht1v1, _, _, _, _, hv1w, _⟩ := hb2
  have ht1v1' : inp.h + 6 ≤ v1 := ht1v1
  have hv1w' : v1 + 32 < 2 ^ w := hv1w
  have hc2 : (task2Contract impl w).cost [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1] mem1 =
      task2Cost impl inp.J (length inp.J inp.embJH) (inp.toT2 0).embVertSum := by
    have h_ex : ∃ inp' : Task2Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.t1OutAddr, inp'.v1] ∧
        inp'.Valid impl mem1 w := ⟨inp.toT2 v1, rfl, hv2⟩
    unfold task2Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, hj, he, _, _⟩ := hargs
    have hJ : inp.J = inp'.J := by
      have g1 := graphAt_iff_readGraph.mp hv2.2.2.2.1
      have g2 := graphAt_iff_readGraph.mp hvc.2.2.2.1
      show (inp.toT2 v1).J = inp'.J
      rw [← g1, ← g2]; exact congrArg (readGraph mem1) hj
    have hemb : ∀ e < inp.J.m, inp.embJH e = inp'.embJH e := fun e hem => by
      have w1 := hv2.2.2.2.2.2.1 e hem
      have w2 := hvc.2.2.2.2.2.1 e (hJ ▸ hem)
      rw [← he] at w2; exact walkAt_unique w1 w2
    obtain ⟨hlen, hsum⟩ := t1_emb_stats_congr hemb
    unfold Task2Input.embVertSum; simp only [Task1Input.toT2]; rw [← hJ, ← hlen, ← hsum]
  refine runs_seq_call_le (vs := [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h, v1]) h2
    ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have := hwords inp.hAddr (by simp); have := hwords inp.jAddr (by simp)
    have := hwords inp.embJHAddr (by simp)
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  · exact ⟨inp.toT2 v1, rfl, hv2⟩
  intro v2 mem2 pos2 hpost2
  have hT2 := hpost2 (inp.toT2 v1) rfl hv2
  have hw3' := hw3 mem2 v2 hT2
  have hT2c := hT2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hagr2, hzf2, hv12, -⟩ := hT2c
  have hagr2' : ∀ x < v1, mem2 x = mem1 x := hagr2
  have hzf2' : ZeroFrom mem2 v2 := hzf2
  have hv12' : v1 + 32 ≤ v2 := hv12
  have hagr21 : ∀ x < inp.h, mem2 x = mem x := fun x hx =>
    (hagr2' x (by omega)).trans (hagr1 x hx)
  have hv3 : (inp.toT3 v2).Valid impl mem2 w :=
    ⟨hJv, GraphAt.of_agree_below hgJ hJle hagr21, hJle,
      ⟨mem, mem1, v1, fun x hx => (hagr2' x hx).symm ▸ rfl, by simp only [Task1Input.toT3]; omega,
        hzf2', hT1⟩, hw3'⟩
  have hv2w : v2 < 2 ^ w := by
    obtain ⟨_, _, hmax⟩ := hw3'
    have h1 : Task3Input.maxHeapEnd impl (inp.toT3 v2) + 3 ≤
        Task3Input.maxWordBound impl (inp.toT3 v2) := le_max_left _ _
    have h2 : Task3Input.staticEndCap impl (inp.toT3 v2) ≤
        Task3Input.maxHeapEnd impl (inp.toT3 v2) := by
      unfold Task3Input.maxHeapEnd; dsimp only; omega
    have h3 : v2 ≤ Task3Input.staticEndCap impl (inp.toT3 v2) := by
      unfold Task3Input.staticEndCap; simp only [Task1Input.toT3]; omega
    omega
  have hc3 : (task3Contract impl w).cost [inp.jAddr, inp.h, v2] mem2 = task3Cost impl inp.J := by
    have h_ex : ∃ inp' : Task3Input,
        [inp.jAddr, inp.h, v2] = [inp'.jAddr, inp'.t1OutAddr, inp'.v2] ∧
        inp'.Valid impl mem2 w := ⟨inp.toT3 v2, rfl, hv3⟩
    unfold task3Contract; dsimp only
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc⟩ := hspec
    have hj : inp.jAddr = inp'.jAddr := (List.cons_eq_cons.mp hargs).1
    have hJ : inp.J = inp'.J := by
      have g1 := graphAt_iff_readGraph.mp hv3.2.1
      have g2 := graphAt_iff_readGraph.mp hvc.2.1
      show (inp.toT3 v2).J = inp'.J
      rw [← g1, ← g2]; exact congrArg (readGraph mem2) hj
    rw [← hJ]
  refine runs_call_le (vs := [inp.jAddr, inp.h, v2]) h3 ?_ ?_ ⟨inp.toT3 v2, rfl, hv3⟩ ?_
  · simp [evalArgs, Expr.eval, startState]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have := hwords inp.jAddr (by simp); have := hwords inp.h (by simp)
    rcases ha with rfl | rfl | rfl <;> omega
  intro v3 mem3 pos3 hpost3
  have hT3 := hpost3 (inp.toT3 v2) rfl hv3
  refine ⟨⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    mem1, v1, mem2, v2, v3, by simp, by simp, by simp, hT1, hcap1, hT2, hT3⟩, ?_⟩
  have hm0 : (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos).mem = mem := rfl
  rw [hm0, hc1, hc2, hc3]
  simp only [Expr.size, argsSize, sparsifyCoreCost]
  omega

end MinCostFlow.Spanner
