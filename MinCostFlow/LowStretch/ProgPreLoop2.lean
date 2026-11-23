module

public import MinCostFlow.LowStretch.ProgPreMath
public import MinCostFlow.LowStretch.ProgPreLoop

/-!
# Three more loops of the preprocessing

* `maxwP` finds the largest weight of the input (`maxwP_spec`).
* `labP` gives every node of the merge tree the head of its `θ`-node, from the root down: an
  `θ`-node gets its own head, and a node of weight below `θ` that is not an `θ`-node gets the
  label of its parent, which comes earlier since a parent has a larger number. The leaves are the
  vertices, so this writes `LAB[v] = hd (top θ v)` for every vertex (`labP_spec`).
* `locP` writes `LOC[HEAD[NODES[i]]] = i` for every node of the record (`locP_spec`); the heads
  of the nodes are different, so no write is undone.

The test of an `x`-node is the expression `nodeE` (`nodeE_eval`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The test of an `x`-node -/

/-- The test `mw k < θ ∧ (k + 1 < N → θ ≤ mw (par k))`, with `N`, `KMW`, `KPAR` and `θ` in
registers `0`, `2`, `3` and `4`. -/
def nodeE (k : Expr) : Expr :=
  .bin .mul (.bin .lt (.load (.bin .add (.reg 2) k)) (.reg 4))
    (.bin .sub (.const 1) (.bin .mul (.bin .lt (.bin .add k (.const 1)) (.reg 0))
      (.bin .lt (.load (.bin .add (.reg 2) (.load (.bin .add (.reg 3) k)))) (.reg 4))))

theorem nodeE_eval {w : ℕ} {st : State} {k : Expr} {kv N KMW KPAR TH a b c : ℕ}
    (hk : k.eval w st = some kv) (h0 : st.regs 0 = N) (h2 : st.regs 2 = KMW)
    (h3 : st.regs 3 = KPAR) (h4 : st.regs 4 = TH) (ha : st.mem (KMW + kv) = a)
    (hb : st.mem (KPAR + kv) = b) (hc : st.mem (KMW + b) = c) (w1 : KMW + kv < 2 ^ w)
    (w2 : KPAR + kv < 2 ^ w) (w3 : KMW + b < 2 ^ w) (w4 : kv + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    (nodeE k).eval w st = some (if a < TH ∧ (kv + 1 < N → TH ≤ c) then 1 else 0) := by
  have l1 : ∀ x y : ℕ, (if x < y then 1 else 0) < 2 ^ w := fun x y => by split_ifs <;> omega
  have e1 : (Expr.bin .lt (.load (.bin .add (.reg 2) k)) (.reg 4)).eval w st =
      some (if a < TH then 1 else 0) := by
    have := Expr.eval_bin (op := .lt) (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq h2) hk w1) ha) (Expr.eval_reg_of_eq h4) (by simpa using l1 a TH)
    simpa using this
  have e2 : (Expr.bin .lt (.bin .add k (.const 1)) (.reg 0)).eval w st =
      some (if kv + 1 < N then 1 else 0) := by
    have := Expr.eval_bin (op := .lt) (Expr.eval_add hk (Expr.eval_const hw) w4)
      (Expr.eval_reg_of_eq h0) (by simpa using l1 (kv + 1) N)
    simpa using this
  have e3 : (Expr.bin .lt (.load (.bin .add (.reg 2) (.load (.bin .add (.reg 3) k)))) (.reg 4)).eval
      w st = some (if c < TH then 1 else 0) := by
    have := Expr.eval_bin (op := .lt) (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3) hk w2) hb) w3) hc)
      (Expr.eval_reg_of_eq h4) (by simpa using l1 c TH)
    simpa using this
  have e4 := Expr.eval_bin (op := .mul) e2 e3 (by simp; split_ifs <;> omega)
  have e5 := Expr.eval_bin (op := .sub) (Expr.eval_const (k := 1) hw) e4 (by simp; omega)
  have e6 := Expr.eval_bin (op := .mul) e1 e5 (by simp; split_ifs <;> omega)
  unfold nodeE
  rw [e6]
  congr 1
  simp only [BinOp.eval]
  by_cases h1 : a < TH <;> by_cases h2 : kv + 1 < N <;> by_cases h3 : c < TH <;> simp [h1, h2, h3] <;>
    omega

theorem nodeE_size (k : Expr) : (nodeE k).size = 3 * k.size + 21 := by
  simp [nodeE, Expr.size]; ring

/-! ### The largest weight -/

/-- The weight of edge `j` of the input at `IN`. -/
def wtAt (mem : ℕ → ℕ) (IN j : ℕ) : ℕ := mem (IN + 3 * j + 2)

/-- The body of `maxwP`: `x := IN[3j + 2]`; if `W < x` then `W := x`. -/
def maxwB : Stmt :=
  .seq (.assign 3 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 15)))
    (.const 2))))
  (.cond (.bin .lt (.reg 2) (.reg 3)) (.assign 2 (.reg 3)) .nop)

/-- `maxwP` with `args = [m, IN]`: the largest weight of the `m` edges at `IN`. -/
def maxwP : Stmt :=
  .seq (forRange 15 (.const 0) (.reg 0) maxwB) (.ret (.reg 2))

theorem maxwP_noRand : maxwP.NoRand := by simp [maxwP, maxwB, forRange, forUp, Stmt.NoRand]

/-- The contract of `maxwP`. -/
def maxwC (w : ℕ) : Contract where
  pre args mem := ∃ m IN, args = [m, IN] ∧ IN + 3 * m + 3 < 2 ^ w ∧ ∀ j < m, wtAt mem IN j < 2 ^ w
  post args mem v mem' := mem' = mem ∧ (∀ j < args.getD 0 0, wtAt mem (args.getD 1 0) j ≤ v) ∧
    (v = 0 ∨ ∃ j < args.getD 0 0, v = wtAt mem (args.getD 1 0) j)
  cost args _ := 30 * args.getD 0 0 + 20

theorem maxwP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [maxwP]) :
    MeetsContract w p b (maxwC w) := by
  intro args mem pos ω _ hpre
  obtain ⟨m, IN, rfl, hbd, hwt⟩ := hpre
  have hproc : p.procs[b]? = some maxwP := hp 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun i st => st.regs 0 = m ∧ st.regs 1 = IN ∧ st.regs 15 = i ∧
    st.mem = mem ∧ (∀ j < i, wtAt mem IN j ≤ st.regs 2) ∧
    (st.regs 2 = 0 ∨ ∃ j < i, st.regs 2 = wtAt mem IN j)
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := maxwB) (P := fun st => st = startState [m, IN] mem pos) (Inv := I) 20 0 m
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      exact ⟨Expr.eval_const (by omega), rfl, rfl, by simp, rfl, fun _ h => absurd h (by omega),
        Or.inl (by simp [startState])⟩)
    (fun _ _ _ _ hI => hI.2.2.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq hI.1)
    (fun i _ hi st ω hI => by
      obtain ⟨h0, h1, h15, hm, hle, hor⟩ := hI
      have ha : (Expr.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 15))) (.const 2)).eval
          w st = some (IN + 3 * i + 2) :=
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h1)
          (Expr.eval_bin (op := .mul) (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h15)
            (by simp; omega)) (by omega)) (Expr.eval_const (by omega)) (by omega)
      have hx := Expr.eval_load_of_eq ha (show st.mem (IN + 3 * i + 2) = wtAt mem IN i by
        rw [hm]; rfl)
      refine runs_start_le (runs_seq_assign_le hx ?_)
      set x := wtAt mem IN i with hx'
      have hxw : x < 2 ^ w := hwt i hi
      have hc := Expr.eval_bin (op := .lt) (st := { st with regs := Function.update st.regs 3 x })
        (Expr.eval_reg_of_eq (r := 2) (v := st.regs 2) (by simp))
        (Expr.eval_reg_of_eq (r := 3) (v := x) (by simp))
        (show (if _ < x then 1 else 0) < 2 ^ w by split_ifs <;> omega)
      refine runs_cond_le hc (fun hv => ?_) (fun hv => ?_)
      · have hlt : st.regs 2 < x := by
          by_contra h; exact hv (by simp [BinOp.eval, h])
        refine runs_assign_le (Expr.eval_reg_of_eq (r := 3) (v := x) (by simp)) ?_
          (by simp only [Expr.size]; omega)
        refine ⟨⟨by simp [Function.update_apply, h0], by simp [Function.update_apply, h1],
          by simp, by simp [hm], fun j hj => ?_, Or.inr ⟨i, by omega, by simp [hx']⟩⟩,
          by simp [Function.update_apply, h15]⟩
        simp only [Function.update_apply]
        simp only [show (2 : ℕ) ≠ 15 by omega, ite_true, ite_false]
        rcases Nat.lt_or_ge j i with hj' | hj'
        · have := hle j hj'; omega
        · rw [show j = i by omega]
      · have hge : x ≤ st.regs 2 := by
          by_contra h; push Not at h
          simp [BinOp.eval, h] at hv
        refine runs_nop_le ⟨⟨by simp [Function.update_apply, h0], by simp [Function.update_apply, h1],
          by simp, by simp [hm], fun j hj => ?_, ?_⟩, by simp [Function.update_apply, h15]⟩
          (by simp only [Expr.size]; omega)
        · simp only [Function.update_apply]
          simp only [show (2 : ℕ) ≠ 15 by omega, show (2 : ℕ) ≠ 3 by omega, ite_false]
          rcases Nat.lt_or_ge j i with hj' | hj'
          · exact hle j hj'
          · rw [show j = i by omega]; exact hge
        · simp only [Function.update_apply]
          simp only [show (2 : ℕ) ≠ 15 by omega, show (2 : ℕ) ≠ 3 by omega, ite_false]
          rcases hor with h | ⟨j, hj, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, he⟩)
  refine ⟨maxwP, hproc, ?_⟩
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, -, hm, hle, hor⟩ := hI
  refine runs_ret_le (Expr.eval_reg w 2 st) ⟨hm, hle, hor⟩ ?_
  simp only [Expr.size, maxwC, List.getD_cons_zero]
  omega

/-! ### The labels -/

/-- The body of `labP`: `k := N - 1 - j`; `LAB[k] := HEAD[k]` if `k` is an `θ`-node, else
`LAB[k] := LAB[KPAR[k]]`. -/
def labB : Stmt :=
  .seq (.assign 16 (.bin .sub (.bin .sub (.reg 0) (.const 1)) (.reg 15)))
  (.cond (nodeE (.reg 16))
    (.store (.bin .add (.reg 1) (.reg 16)) (.load (.bin .add (.reg 5) (.reg 16))))
    (.store (.bin .add (.reg 1) (.reg 16))
      (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 3) (.reg 16)))))))

/-- `labP` with `args = [N, LAB, KMW, KPAR, TH, HEAD]`. -/
def labP : Stmt := .seq (forRange 15 (.const 0) (.reg 0) labB) (.ret (.const 0))

theorem labP_noRand : labP.NoRand := by simp [labP, labB, nodeE, forRange, forUp, Stmt.NoRand]

/-- The contract of `labP` for the merge tree `T` of `G`. -/
def labC (w : ℕ) (T : KT) (G : PG) : Contract where
  pre args mem := ∃ N LAB KMW KPAR TH HEAD, args = [N, LAB, KMW, KPAR, TH, HEAD] ∧ T.Ok G ∧
    N = T.N ∧ 1 ≤ TH ∧
    (∀ k < N, mem (KMW + k) = T.mw k ∧ mem (KPAR + k) = T.par k ∧ mem (HEAD + k) = T.hd G k) ∧
    KMW + N ≤ LAB ∧ KPAR + N ≤ LAB ∧ HEAD + N ≤ LAB ∧ LAB + N + 1 < 2 ^ w
  post args mem _ mem' := ∀ N LAB KMW KPAR TH HEAD, args = [N, LAB, KMW, KPAR, TH, HEAD] →
    (∀ v < G.n, mem' (LAB + v) = T.hd G (T.top TH v)) ∧
    ∀ a, (a < LAB ∨ LAB + N ≤ a) → mem' a = mem a
  cost args _ := 60 * args.getD 0 0 + 20

theorem labP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [labP]) (T : KT) (G : PG) :
    MeetsContract w p b (labC w T G) := by
  intro args mem pos ω _ hpre
  obtain ⟨N, LAB, KMW, KPAR, TH, HEAD, rfl, hT, hN, hTH, hm, l1, l2, l3, l4⟩ := hpre
  have hproc : p.procs[b]? = some labP := hp 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  set args := [N, LAB, KMW, KPAR, TH, HEAD] with hargs
  have hnN := hT.n_lt
  -- the labels of the nodes from `N - i` on
  let Dn : ℕ → (ℕ → ℕ) → Prop := fun i M => ∀ k, N - i ≤ k → k < N → T.mw k < TH →
    ∃ t, T.IsNode TH t ∧ T.Under k t ∧ M (LAB + k) = T.hd G t
  let I : ℕ → State → Prop := fun i st => LoopRegs args st ∧ st.regs 15 = i ∧ Dn i st.mem ∧
    ∀ a, (a < LAB + (N - i) ∨ LAB + N ≤ a) → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := labB) (P := fun st => LoopRegs args st ∧ st.mem = mem) (Inv := I) 50 0 N
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hmm⟩ => ⟨Expr.eval_const (by omega), hr.upd le_rfl 0, by simp,
      fun k hk hk' _ => absurd hk' (by omega), fun a _ => by simp [hmm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq (hI.1 0 (by omega)))
    (fun i _ hi st ω hI => by
      obtain ⟨hR, h15, hD, hfr⟩ := hI
      have r0 : st.regs 0 = N := hR 0 (by omega)
      have r1 : st.regs 1 = LAB := hR 1 (by omega)
      have r2 : st.regs 2 = KMW := hR 2 (by omega)
      have r3 : st.regs 3 = KPAR := hR 3 (by omega)
      have r4 : st.regs 4 = TH := hR 4 (by omega)
      have r5 : st.regs 5 = HEAD := hR 5 (by omega)
      obtain ⟨k, hk⟩ : ∃ k, k = N - 1 - i := ⟨_, rfl⟩
      have hkN : k < N := by omega
      have hk' : k < T.N := by omega
      have hpk := KT.par_lt_N hT hk'
      have hmk := hm k hkN
      have hmp := hm (T.par k) (by omega)
      have ek : (Expr.bin .sub (.bin .sub (.reg 0) (.const 1)) (.reg 15)).eval w st = some k := by
        rw [hk]
        exact Expr.eval_bin (op := .sub) (Expr.eval_bin (op := .sub) (Expr.eval_reg_of_eq r0)
          (Expr.eval_const hw1) (by simp; omega)) (Expr.eval_reg_of_eq h15) (by simp; omega)
      refine runs_start_le (runs_seq_assign_le ek ?_)
      set st1 : State := { st with regs := Function.update st.regs 16 k } with hst1
      clear_value st1
      have s0 : st1.regs 0 = N := by simp [hst1, r0]
      have s1 : st1.regs 1 = LAB := by simp [hst1, r1]
      have s2 : st1.regs 2 = KMW := by simp [hst1, r2]
      have s3 : st1.regs 3 = KPAR := by simp [hst1, r3]
      have s4 : st1.regs 4 = TH := by simp [hst1, r4]
      have s5 : st1.regs 5 = HEAD := by simp [hst1, r5]
      have s16 : st1.regs 16 = k := by simp [hst1]
      have sm : st1.mem = st.mem := by rw [hst1]
      have ea : st1.mem (KMW + k) = T.mw k := by rw [sm, hfr _ (Or.inl (by omega))]; exact hmk.1
      have eb : st1.mem (KPAR + k) = T.par k := by
        rw [sm, hfr _ (Or.inl (by omega))]; exact hmk.2.1
      have ec : st1.mem (KMW + T.par k) = T.mw (T.par k) := by
        rw [sm, hfr _ (Or.inl (by omega))]; exact hmp.1
      have hc := nodeE_eval (Expr.eval_reg_of_eq s16) s0 s2 s3 s4 ea eb ec (by omega) (by omega)
        (by omega) (by omega) hw1
      have hst : Expr.size (.reg 16) = 1 := rfl
      have haddr : (Expr.bin .add (.reg 1) (.reg 16)).eval w st1 = some (LAB + k) :=
        Expr.eval_add (Expr.eval_reg_of_eq s1) (Expr.eval_reg_of_eq s16) (by omega)
      -- the facts kept by a write at `LAB + k`
      have keep : ∀ x, (T.mw k < TH → ∃ t, T.IsNode TH t ∧ T.Under k t ∧ x = T.hd G t) →
          (fun st₂ : State => I (i + 1) { st₂ with regs := Function.update st₂.regs 15 (i + 1) } ∧
            st₂.regs 15 = i) { st1 with mem := Function.update st1.mem (LAB + k) x } := by
        intro x hx
        refine ⟨⟨fun r hr => ?_, by simp, fun k' (h1 : N - (i + 1) ≤ k') (h2 : k' < N)
          (h3 : T.mw k' < TH) => ?_, fun a (ha : a < LAB + (N - (i + 1)) ∨ LAB + N ≤ a) => ?_⟩, ?_⟩
        · simp only [Function.update_apply, hst1]
          rw [if_neg (by omega), if_neg (by omega)]; exact hR r hr
        · by_cases e : k' = k
          · subst e; obtain ⟨t, ht⟩ := hx h3; exact ⟨t, ht.1, ht.2.1, by simp [ht.2.2]⟩
          · clear hx
            have hk'' : N - i ≤ k' := by omega
            have hne : LAB + k' ≠ LAB + k := by omega
            obtain ⟨t, ht⟩ := hD k' hk'' h2 h3
            refine ⟨t, ht.1, ht.2.1, ?_⟩
            show Function.update st1.mem (LAB + k) x (LAB + k') = _
            rw [Function.update_of_ne hne, sm]; exact ht.2.2
        · clear hx
          show Function.update st1.mem (LAB + k) x a = _
          rw [Function.update_of_ne (show a ≠ LAB + k by omega), sm]; exact hfr a (by omega)
        · simp [hst1, h15]
      refine runs_cond_le hc (fun hv => ?_) (fun hv => ?_)
      · -- `k` is an `θ`-node
        have hnd : T.IsNode TH k := by
          by_contra hn
          exact hv (by rw [if_neg (by
            rintro ⟨h1, h2⟩; exact hn ⟨hk', h1, fun h => h2 (by omega)⟩)])
        have hx : (Expr.load (.bin .add (.reg 5) (.reg 16))).eval w st1 = some (T.hd G k) :=
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq s5) (Expr.eval_reg_of_eq s16)
            (by omega)) (by rw [sm, hfr _ (Or.inl (by omega))]; exact hmk.2.2)
        refine runs_store_le haddr hx (keep _ fun _ => ⟨k, hnd, KT.Under.refl k, rfl⟩) ?_
        simp only [nodeE_size, Expr.size]; omega
      · -- `k` is not an `θ`-node
        have hnd : ¬ (T.mw k < TH ∧ (k + 1 < N → TH ≤ T.mw (T.par k))) := by
          intro h; simp [h] at hv; have := h.2 hv.1; omega
        have hx : (Expr.load (.bin .add (.reg 1) (.load (.bin .add (.reg 3) (.reg 16))))).eval w st1 =
            some (st.mem (LAB + T.par k)) :=
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq s1)
            (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq s3)
              (Expr.eval_reg_of_eq s16) (by omega)) eb) (by omega)) (by rw [sm])
        refine runs_store_le haddr hx (keep _ fun hlt => ?_) ?_
        · have h1 : k + 1 < N ∧ T.mw (T.par k) < TH := by
            by_contra hc'
            exact hnd ⟨hlt, fun h => by by_contra h'; exact hc' ⟨h, by omega⟩⟩
          have hlt' := (hT.par_lt k (by omega)).1
          obtain ⟨t, ht⟩ := hD (T.par k) (by omega) (by omega) h1.2
          exact ⟨t, ht.1, (KT.Under.par k).trans ht.2.1, ht.2.2⟩
        · simp only [nodeE_size, Expr.size]; omega)
  refine ⟨labP, hproc, ?_⟩
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨LoopRegs.start mem pos, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hD, hfr⟩ := hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ?_ ?_
  · intro N' LAB' KMW' KPAR' TH' HEAD' he
    simp only [hargs, List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := he
    refine ⟨fun v hv => ?_, fun a ha => hfr a (by omega)⟩
    obtain ⟨t, ht, hu, he⟩ := hD v (by omega) (by omega) (by rw [hT.leaf_mw v hv]; omega)
    rw [he, ht.top_eq hT hv hTH hu]
  · simp only [Expr.size, labC, hargs, List.getD_cons_zero, Nat.sub_zero]; omega

/-! ### The local indices -/

/-- The head of node number `i` of the list at `NODES`. -/
def hdAt (mem : ℕ → ℕ) (NODES HEAD i : ℕ) : ℕ := mem (HEAD + mem (NODES + i))

/-- The body of `locP`: `LOC[HEAD[NODES[i]]] := i`. -/
def locB : Stmt :=
  .store (.bin .add (.reg 1) (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 2) (.reg 15))))))
    (.reg 15)

/-- `locP` with `args = [s, LOC, NODES, HEAD]`. -/
def locP : Stmt := .seq (forRange 15 (.const 0) (.reg 0) locB) (.ret (.const 0))

theorem locP_noRand : locP.NoRand := by simp [locP, locB, forRange, forUp, Stmt.NoRand]

/-- The contract of `locP`: the heads of the listed nodes are different and lie below `LOC`. -/
def locC (w : ℕ) : Contract where
  pre args mem := ∃ s LOC NODES HEAD, args = [s, LOC, NODES, HEAD] ∧ NODES + s ≤ LOC ∧
    (∀ i < s, HEAD + mem (NODES + i) < LOC) ∧ (∀ i < s, LOC + hdAt mem NODES HEAD i < 2 ^ w) ∧
    (∀ i < s, ∀ j < s, i ≠ j → hdAt mem NODES HEAD i ≠ hdAt mem NODES HEAD j) ∧ LOC + 1 < 2 ^ w
  post args mem _ mem' := ∀ s LOC NODES HEAD, args = [s, LOC, NODES, HEAD] →
    (∀ i < s, mem' (LOC + hdAt mem NODES HEAD i) = i) ∧
    ∀ a, (∀ i < s, a ≠ LOC + hdAt mem NODES HEAD i) → mem' a = mem a
  cost args _ := 30 * args.getD 0 0 + 20

theorem locP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [locP]) :
    MeetsContract w p b (locC w) := by
  intro args mem pos ω _ hpre
  obtain ⟨s, LOC, NODES, HEAD, rfl, l1, l2, l3, hinj, l4⟩ := hpre
  have hproc : p.procs[b]? = some locP := hp 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hs : s < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun i st => LoopRegs [s, LOC, NODES, HEAD] st ∧ st.regs 15 = i ∧
    (∀ i' < i, st.mem (LOC + hdAt mem NODES HEAD i') = i') ∧
    ∀ a, (∀ i' < i, a ≠ LOC + hdAt mem NODES HEAD i') → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := locB) (P := fun st => LoopRegs [s, LOC, NODES, HEAD] st ∧ st.mem = mem) (Inv := I)
    15 0 s (Nat.zero_le _) hw1 (fun _ => hs)
    (fun st ⟨hr, hm⟩ => ⟨Expr.eval_const (by omega), hr.upd le_rfl 0, by simp,
      fun _ h => absurd h (by omega), fun a _ => by simp [hm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq (hI.1 0 (by omega)))
    (fun i _ hi st ω hI => by
      obtain ⟨hR, h15, hdone, hfr⟩ := hI
      have r1 : st.regs 1 = LOC := hR 1 (by omega)
      have r2 : st.regs 2 = NODES := hR 2 (by omega)
      have r3 : st.regs 3 = HEAD := hR 3 (by omega)
      have hl2 := l2 i hi
      have hl3 := l3 i hi
      have hnot : ∀ x, x < LOC → ∀ i' < i, x ≠ LOC + hdAt mem NODES HEAD i' := by
        intro x hx i' _; omega
      have e1 : st.mem (NODES + i) = mem (NODES + i) := hfr _ (hnot _ (by omega))
      have e2 : st.mem (HEAD + mem (NODES + i)) = hdAt mem NODES HEAD i := hfr _ (hnot _ hl2)
      have ha : (Expr.bin .add (.reg 1) (.load (.bin .add (.reg 3)
          (.load (.bin .add (.reg 2) (.reg 15)))))).eval w st =
          some (LOC + hdAt mem NODES HEAD i) :=
        Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq r3) (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r2)
            (Expr.eval_reg_of_eq h15) (by omega)) e1) (by omega)) e2) hl3
      refine runs_start_le (runs_store_le ha (Expr.eval_reg_of_eq h15) ?_ (by simp [Expr.size]))
      refine ⟨⟨(hR.mem _).upd le_rfl _, by simp, fun i' hi' => ?_, fun a ha' => ?_⟩, h15⟩
      · show Function.update st.mem (LOC + hdAt mem NODES HEAD i) i
          (LOC + hdAt mem NODES HEAD i') = i'
        by_cases e : i' = i
        · subst e; simp
        · have hne := hinj i' (by omega) i hi e
          rw [Function.update_of_ne (by omega)]; exact hdone i' (by omega)
      · show Function.update st.mem (LOC + hdAt mem NODES HEAD i) i a = _
        rw [Function.update_of_ne (ha' i (by omega))]
        exact hfr a fun i' hi' => ha' i' (by omega))
  refine ⟨locP, hproc, ?_⟩
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨LoopRegs.start mem pos, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ?_ ?_
  · intro s' LOC' NODES' HEAD' he
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := he
    exact ⟨hdone, hfr⟩
  · simp only [Expr.size, locC, List.getD_cons_zero, Nat.sub_zero]; omega

end MinCostFlow.LowStretch
