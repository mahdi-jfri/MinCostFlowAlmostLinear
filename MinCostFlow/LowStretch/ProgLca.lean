module

public import MinCostFlow.LowStretch.KLca
public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The lowest common node of every pair

`lcaOne` finds the lowest node of the merge tree above two given nodes, by the climb of
`KLca.lean`. It reads the parents `KPAR` and the heads `HEAD` of the tree. Every step at least
doubles the leaves below one of the two nodes, so it takes `O(log n)` steps (`lcaOne_spec`).
`lcaAll` does this for the two ends of every pair and writes the answers to an array
(`lcaAll_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `v` is the lowest node above both `a` and `b`. -/
def KT.IsLca (T : KT) (a b v : ℕ) : Prop :=
  T.Under a v ∧ T.Under b v ∧ ∀ l, T.Under a l → T.Under b l → T.Under v l

/-- `lcaOne` with `args = [KPAR, HEAD, a, b, n]`. -/
def lcaOne : Stmt :=
  .seq (.assign 5 (.load (.bin .add (.reg 1) (.reg 2))))
  (.seq (.assign 6 (.load (.bin .add (.reg 1) (.reg 3))))
  (.seq (.loop (.bin .sub (.const 1) (.bin .eq (.reg 5) (.reg 6)))
    (.cond (.bin .lt (.reg 5) (.reg 6))
      (.seq (.assign 2 (.load (.bin .add (.reg 0) (.reg 5))))
        (.assign 5 (.load (.bin .add (.reg 1) (.reg 2)))))
      (.seq (.assign 3 (.load (.bin .add (.reg 0) (.reg 6))))
        (.assign 6 (.load (.bin .add (.reg 1) (.reg 3)))))))
  (.cond (.bin .lt (.reg 2) (.reg 3)) (.ret (.reg 3)) (.ret (.reg 2)))))

theorem lcaOne_noRand : lcaOne.NoRand := by simp [lcaOne, Stmt.NoRand]

/-- The tree `T` sits in memory: parents at `KPAR`, heads at `HEAD`. -/
def KT.InMem (T : KT) (G : PG) (w : ℕ) (mem : ℕ → ℕ) (KPAR HEAD : ℕ) : Prop :=
  T.Ok G ∧ (∀ k < T.N, mem (KPAR + k) = T.par k ∧ mem (HEAD + k) = T.hd G k) ∧
    KPAR + T.N < 2 ^ w ∧ HEAD + T.N < 2 ^ w

/-- The contract of `lcaOne` for the tree `T` of `G`. -/
def lcaC (w : ℕ) (T : KT) (G : PG) : Contract where
  pre args mem := ∃ KPAR HEAD a b, args = [KPAR, HEAD, a, b, G.n] ∧ T.InMem G w mem KPAR HEAD ∧
    a < T.N ∧ b < T.N
  post args mem v mem' := mem' = mem ∧ ∀ KPAR HEAD a b, args = [KPAR, HEAD, a, b, G.n] →
    T.IsLca a b v
  cost args _ := 80 * Nat.log 2 (args.getD 4 0) + 100

/-- The measure of the climb: how far the two nodes are from having all leaves. -/
noncomputable def lcaM (T : KT) (G : PG) (a b : ℕ) : ℕ :=
  (Nat.log 2 G.n - Nat.log 2 (T.sz G a)) + (Nat.log 2 G.n - Nat.log 2 (T.sz G b))

theorem lcaOne_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [lcaOne]) (T : KT) (G : PG) :
    MeetsContract w p b (lcaC w T G) := by
  intro args mem pos ω hwords hpre
  obtain ⟨KPAR, HEAD, a0, b0, rfl, ⟨ht, hm, hw1, hw2⟩, ha0, hb0⟩ := hpre
  have hproc : p.procs[b]? = some lcaOne := hp 0 (by simp)
  clear hp
  -- the state of the climb
  let I : State → Prop := fun st => st.regs 0 = KPAR ∧ st.regs 1 = HEAD ∧ st.mem = mem ∧
    st.regs 2 < T.N ∧ st.regs 3 < T.N ∧ st.regs 5 = T.hd G (st.regs 2) ∧
    st.regs 6 = T.hd G (st.regs 3) ∧ T.Under a0 (st.regs 2) ∧ T.Under b0 (st.regs 3) ∧
    ∀ l, T.Under a0 l → T.Under b0 l → T.Under (st.regs 2) l ∧ T.Under (st.regs 3) l
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .sub (.const 1) (.bin .eq (.reg 5) (.reg 6)))
    (body := .cond (.bin .lt (.reg 5) (.reg 6))
      (.seq (.assign 2 (.load (.bin .add (.reg 0) (.reg 5))))
        (.assign 5 (.load (.bin .add (.reg 1) (.reg 2)))))
      (.seq (.assign 3 (.load (.bin .add (.reg 0) (.reg 6))))
        (.assign 6 (.load (.bin .add (.reg 1) (.reg 3)))))) (Inv := I)
    (Q := fun st => I st ∧ st.regs 5 = st.regs 6)
    (fun st => lcaM T G (st.regs 2) (st.regs 3))
    (fun st => 1 - (if st.regs 5 = st.regs 6 then 1 else 0)) 30
    (fun st hI => by eval_expr)
    (fun st hI hv => ⟨hI, by by_contra hne; simp [hne] at hv⟩)
    (fun st hI hv => by
      obtain ⟨h0, h1, hmm, h2, h3, h5, h6, hua, hub, hl⟩ := hI
      have hne : st.regs 5 ≠ st.regs 6 := by intro e; simp [e] at hv
      have hd2 := (KT.hd_under ht _ h2).lt_N ht h2
      have hd3 := (KT.hd_under ht _ h3).lt_N ht h3
      intro st' ω' hst
      subst hst
      refine runs_start_le ?_
      by_cases hlt : st'.regs 5 < st'.regs 6
      · -- move the first node
        rw [h5, h6] at hlt
        have hc := KT.climb ht h2 h3 ⟨T.N, KT.reach_root ht h2⟩ ⟨T.N, KT.reach_root ht h3⟩ hlt
        have hpN := KT.climb_lt ht h2
        have e1 : st'.mem (st'.regs 0 + st'.regs 5) = T.par (T.hd G (st'.regs 2)) := by
          rw [h0, h5, hmm]; exact (hm _ hd2).1
        have e2 : st'.mem (st'.regs 1 + T.par (T.hd G (st'.regs 2))) =
            T.hd G (T.par (T.hd G (st'.regs 2))) := by
          rw [h1, hmm]; exact (hm _ hpN).2
        have b1 : st'.mem (st'.regs 0 + st'.regs 5) < 2 ^ w := by rw [e1]; omega
        have e1a : st'.mem (KPAR + T.hd G (st'.regs 2)) = T.par (T.hd G (st'.regs 2)) := by
          rw [hmm]; exact (hm _ hd2).1
        have b2' : st'.regs 1 + st'.mem (KPAR + T.hd G (st'.regs 2)) < 2 ^ w := by
          rw [e1a, h1]; omega
        have e2a : st'.mem (st'.regs 1 + st'.mem (KPAR + T.hd G (st'.regs 2))) =
            T.hd G (T.par (T.hd G (st'.regs 2))) := by rw [e1a]; exact e2
        have b2 : st'.mem (st'.regs 1 + T.par (T.hd G (st'.regs 2))) < 2 ^ w := by
          rw [e2]; have := (KT.hd_under ht _ hpN).lt_N ht hpN; omega
        have hsz := KT.log_sz_lt ht h2 (KT.climb_sz ht h2 hc.1)
        have hlog := KT.log_sz_le (T := T) (G := G) (T.par (T.hd G (st'.regs 2)))
        wram_run
        · refine ⟨⟨by simp [h0], by simp [h1], by simp [hmm], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp [e1, e1a, hpN]
          · simp [h3]
          · simp [e1, e1a, e2a, e2]
          · simp [h6]
          · simp only [Function.update_apply]; simp [e1, e1a]
            exact hua.trans ((KT.hd_under ht _ h2).trans (KT.Under.par _))
          · simp [hub]
          · intro l hla hlb
            simp only [Function.update_apply]; simp [e1, e1a]
            obtain ⟨l2, l3⟩ := hl l hla hlb
            exact ⟨(KT.climb ht h2 h3 l2 l3 hlt).2, l3⟩
          · simp only [Function.update_apply]; simp [e1, e1a]
            unfold lcaM; omega
        · wram_cost
      · -- move the second node
        have hlt' : T.hd G (st'.regs 3) < T.hd G (st'.regs 2) := by
          rw [h5, h6] at hlt hne; omega
        have hc := KT.climb ht h3 h2 ⟨T.N, KT.reach_root ht h3⟩ ⟨T.N, KT.reach_root ht h2⟩ hlt'
        have hpN := KT.climb_lt ht h3
        have e1 : st'.mem (st'.regs 0 + st'.regs 6) = T.par (T.hd G (st'.regs 3)) := by
          rw [h0, h6, hmm]; exact (hm _ hd3).1
        have e2 : st'.mem (st'.regs 1 + T.par (T.hd G (st'.regs 3))) =
            T.hd G (T.par (T.hd G (st'.regs 3))) := by
          rw [h1, hmm]; exact (hm _ hpN).2
        have b1 : st'.mem (st'.regs 0 + st'.regs 6) < 2 ^ w := by rw [e1]; omega
        have e1a : st'.mem (KPAR + T.hd G (st'.regs 3)) = T.par (T.hd G (st'.regs 3)) := by
          rw [hmm]; exact (hm _ hd3).1
        have b2' : st'.regs 1 + st'.mem (KPAR + T.hd G (st'.regs 3)) < 2 ^ w := by
          rw [e1a, h1]; omega
        have e2a : st'.mem (st'.regs 1 + st'.mem (KPAR + T.hd G (st'.regs 3))) =
            T.hd G (T.par (T.hd G (st'.regs 3))) := by rw [e1a]; exact e2
        have b2 : st'.mem (st'.regs 1 + T.par (T.hd G (st'.regs 3))) < 2 ^ w := by
          rw [e2]; have := (KT.hd_under ht _ hpN).lt_N ht hpN; omega
        have hsz := KT.log_sz_lt ht h3 (KT.climb_sz ht h3 hc.1)
        have hlog := KT.log_sz_le (T := T) (G := G) (T.par (T.hd G (st'.regs 3)))
        wram_run
        · refine ⟨⟨by simp [h0], by simp [h1], by simp [hmm], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp [h2]
          · simp [e1, e1a, hpN]
          · simp [h5]
          · simp [e1, e1a, e2a, e2]
          · simp [hua]
          · simp only [Function.update_apply]; simp [e1, e1a]
            exact hub.trans ((KT.hd_under ht _ h3).trans (KT.Under.par _))
          · intro l hla hlb
            simp only [Function.update_apply]; simp [e1, e1a]
            obtain ⟨l2, l3⟩ := hl l hla hlb
            exact ⟨l2, (KT.climb ht h3 h2 l3 l2 hlt').2⟩
          · simp only [Function.update_apply]; simp [e1, e1a]
            unfold lcaM; omega
        · wram_cost)
  refine ⟨lcaOne, hproc, ?_⟩
  dsimp only [lcaOne]
  refine runs_start_le ?_
  have e5 : mem (HEAD + a0) = T.hd G a0 := (hm _ ha0).2
  have e6 : mem (HEAD + b0) = T.hd G b0 := (hm _ hb0).2
  have b5 : mem (HEAD + a0) < 2 ^ w := by
    rw [e5]; have := (KT.hd_under ht _ ha0).lt_N ht ha0; omega
  have b6 : mem (HEAD + b0) < 2 ^ w := by
    rw [e6]; have := (KT.hd_under ht _ hb0).lt_N ht hb0; omega
  wram_step
  wram_step
  refine runs_seq_triple_le hloop ?_ (fun st hQ => ?_)
  · refine ⟨by simp [startState], by simp [startState], rfl, by simp [startState, ha0],
      by simp [startState, hb0], by simp [startState, e5], by simp [startState, e6],
      by simp [startState]; exact KT.Under.refl _, by simp [startState]; exact KT.Under.refl _,
      fun l hla hlb => by simp [startState]; exact ⟨hla, hlb⟩⟩
  obtain ⟨⟨h0, h1, hmm, h2, h3, h5, h6, hua, hub, hl⟩, he⟩ := hQ
  rw [h5, h6] at he
  obtain ⟨m1, m2, m3⟩ := KT.meet ht h2 h3 he
  have hfin : T.IsLca a0 b0 (max (st.regs 2) (st.regs 3)) :=
    ⟨hua.trans m1, hub.trans m2, fun l hla hlb => m3 l (hl l hla hlb).1 (hl l hla hlb).2⟩
  have hM : lcaM T G a0 b0 ≤ 2 * Nat.log 2 G.n := by unfold lcaM; omega
  by_cases hlt : st.regs 2 < st.regs 3
  · rw [max_eq_right hlt.le] at hfin
    wram_run
    · exact ⟨hmm, fun _ _ _ _ he' => by
        simp only [List.cons.injEq] at he'
        obtain ⟨-, -, rfl, rfl, -⟩ := he'
        exact hfin⟩
    · simp only [lcaC, List.getD_cons_zero, List.getD_cons_succ, Expr.size, startState]
      simp only [Function.update_apply]
      simp only [show (2 : ℕ) ≠ 5 by decide, show (2 : ℕ) ≠ 6 by decide, show (3 : ℕ) ≠ 5 by decide,
        show (3 : ℕ) ≠ 6 by decide, ite_false, List.getD_cons_zero, List.getD_cons_succ]
      generalize lcaM T G a0 b0 = M at hM ⊢
      generalize Nat.log 2 G.n = L at hM ⊢
      omega
  · rw [max_eq_left (by omega)] at hfin
    wram_run
    · exact ⟨hmm, fun _ _ _ _ he' => by
        simp only [List.cons.injEq] at he'
        obtain ⟨-, -, rfl, rfl, -⟩ := he'
        exact hfin⟩
    · simp only [lcaC, List.getD_cons_zero, List.getD_cons_succ, Expr.size, startState]
      simp only [Function.update_apply]
      simp only [show (2 : ℕ) ≠ 5 by decide, show (2 : ℕ) ≠ 6 by decide, show (3 : ℕ) ≠ 5 by decide,
        show (3 : ℕ) ≠ 6 by decide, ite_false, List.getD_cons_zero, List.getD_cons_succ]
      generalize lcaM T G a0 b0 = M at hM ⊢
      generalize Nat.log 2 G.n = L at hM ⊢
      omega

/-- `lcaAll bO` with `args = [m, IN, KPAR, HEAD, LCA, n]`; `lcaOne` sits at `bO`. It writes the
lowest common node of the two ends of pair `q` to `LCA + q`. -/
def lcaAll (bO : ℕ) : Stmt :=
  .seq (forRange 6 (.const 0) (.reg 0)
    (.seq (.call 7 bO [.reg 2, .reg 3, .load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 6))),
        .load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 6))) (.const 1)), .reg 5])
      (.store (.bin .add (.reg 4) (.reg 6)) (.reg 7))))
  (.ret (.const 0))

theorem lcaAll_noRand (bO : ℕ) : (lcaAll bO).NoRand := by
  simp [lcaAll, forRange, forUp, Stmt.NoRand]

/-- The contract of `lcaAll` for the tree `T` of `G`. All the arrays it reads lie below `LCA`. -/
def lcaAC (w : ℕ) (T : KT) (G : PG) : Contract where
  pre args mem := ∃ IN KPAR HEAD LCA, args = [G.m, IN, KPAR, HEAD, LCA, G.n] ∧
    T.InMem G w mem KPAR HEAD ∧
    (∀ q < G.m, mem (IN + 3 * q) = G.pu q ∧ mem (IN + 3 * q + 1) = G.pv q) ∧
    (∀ q < G.m, G.pu q < G.n ∧ G.pv q < G.n) ∧
    IN + 3 * G.m ≤ LCA ∧ KPAR + T.N ≤ LCA ∧ HEAD + T.N ≤ LCA ∧ LCA + G.m < 2 ^ w
  post args mem _ mem' := ∀ IN KPAR HEAD LCA, args = [G.m, IN, KPAR, HEAD, LCA, G.n] →
    (∀ q < G.m, T.IsLca (G.pu q) (G.pv q) (mem' (LCA + q))) ∧
    ∀ a, (a < LCA ∨ LCA + G.m ≤ a) → mem' a = mem a
  cost args _ := args.getD 0 0 * (80 * Nat.log 2 (args.getD 5 0) + 200) + 20

theorem lcaAll_spec {w : ℕ} {p : Program} {b bO : ℕ} (hp : p.HasAt b [lcaAll bO])
    (hO : p.HasAt bO [lcaOne]) (T : KT) (G : PG) : MeetsContract w p b (lcaAC w T G) := by
  intro args mem pos ω hwords hpre
  obtain ⟨IN, KPAR, HEAD, LCA, rfl, hT, hin, hG, l1, l2, l3, l4⟩ := hpre
  have hproc : p.procs[b]? = some (lcaAll bO) := hp 0 (by simp)
  have hS := lcaOne_spec (w := w) hO T G
  clear hp hO
  obtain ⟨ht, hm, hw1, hw2⟩ := hT
  have hnN := ht.n_lt
  have hw : 1 < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun q st => st.regs 0 = G.m ∧ st.regs 1 = IN ∧ st.regs 2 = KPAR ∧
    st.regs 3 = HEAD ∧ st.regs 4 = LCA ∧ st.regs 5 = G.n ∧ st.regs 6 = q ∧
    (∀ q' < q, T.IsLca (G.pu q') (G.pv q') (st.mem (LCA + q'))) ∧
    ∀ a, (a < LCA ∨ LCA + q ≤ a) → st.mem a = mem a
  have hL := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := .seq (.call 7 bO [.reg 2, .reg 3,
        .load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 6))),
        .load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 6))) (.const 1)), .reg 5])
      (.store (.bin .add (.reg 4) (.reg 6)) (.reg 7)))
    (P := fun st => st = startState [G.m, IN, KPAR, HEAD, LCA, G.n] mem pos) (Inv := I)
    (80 * Nat.log 2 G.n + 160) 0 G.m (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hst => by
      subst hst
      exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
        by simp [startState], by simp [startState], by simp [startState], by simp,
        fun q hq => absurd hq (by omega), fun a _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.1; eval_expr)
    (fun q _ hq st ω hI => by
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, hdone, hfr⟩ := hI
      obtain ⟨mu, mv⟩ := hin q hq
      obtain ⟨hpu, hpv⟩ := hG q hq
      have eu : st.mem (st.regs 1 + 3 * st.regs 6) = G.pu q := by
        rw [b1, b6, hfr _ (Or.inl (by omega))]; exact mu
      have ev : st.mem (st.regs 1 + 3 * st.regs 6 + 1) = G.pv q := by
        rw [b1, b6, hfr _ (Or.inl (by omega))]; exact mv
      have bu : st.mem (st.regs 1 + 3 * st.regs 6) < 2 ^ w := by rw [eu]; omega
      have bv : st.mem (st.regs 1 + 3 * st.regs 6 + 1) < 2 ^ w := by rw [ev]; omega
      have hT' : T.InMem G w st.mem KPAR HEAD :=
        ⟨ht, fun k hk => by
          rw [hfr _ (Or.inl (by omega)), hfr _ (Or.inl (by omega))]; exact hm k hk, hw1, hw2⟩
      refine runs_start_le ?_
      have eu' : st.mem (IN + 3 * q) = G.pu q := by rw [hfr _ (Or.inl (by omega))]; exact mu
      have ev' : st.mem (IN + 3 * q + 1) = G.pv q := by rw [hfr _ (Or.inl (by omega))]; exact mv
      wram_step
      · exact ⟨KPAR, HEAD, G.pu q, G.pv q, by simp [eu', ev'], hT', by omega, by omega⟩
      · intro v mem' pos' hpost
        obtain ⟨rfl, hv⟩ := hpost
        have hv' := hv KPAR HEAD (G.pu q) (G.pv q) (by simp [eu', ev'])
        wram_run
        · refine ⟨⟨by simp [b0], by simp [b1], by simp [b2], by simp [b3], by simp [b4],
            by simp [b5], by simp, fun q' hq' => ?_, fun a ha => ?_⟩, by simp [b6]⟩
          · show T.IsLca _ _ (Function.update st.mem (st.regs 4 + st.regs 6) v (LCA + q'))
            rw [b4, b6]
            by_cases e : q' = q
            · subst e; simp [hv']
            · rw [Function.update_of_ne (by omega)]; exact hdone q' (by omega)
          · show Function.update st.mem (st.regs 4 + st.regs 6) v a = mem a
            rw [b4, b6, Function.update_of_ne (by omega)]; exact hfr a (by omega)
        · simp only [lcaC, List.getD_cons_zero, List.getD_cons_succ]
          wram_cost)
  refine ⟨lcaAll bO, hproc, ?_⟩
  dsimp only [lcaAll]
  refine runs_start_le ?_
  refine runs_seq_triple_le hL rfl (fun st h => ?_)
  obtain ⟨-, -, -, -, -, -, -, hdone, hfr⟩ := h
  refine runs_ret_le (by eval_expr) (fun IN' KPAR' HEAD' LCA' he => ?_) ?_
  · simp only [List.cons.injEq] at he
    obtain ⟨-, rfl, rfl, rfl, rfl, -⟩ := he
    exact ⟨hdone, hfr⟩
  · simp only [lcaAC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    simp only [Nat.sub_zero]
    generalize Nat.log 2 G.n = L
    nlinarith

end MinCostFlow.LowStretch
