module

public import MinCostFlow.HierPaths.InitProgTermRecords

/-!
# Interleaving endpoint records

For connector `i`, two consecutive key cells receive its endpoints.
The corresponding payload cells both receive `i`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Each iteration writes two keys and two payloads. -/
def initTermColumnStep : Stmt :=
  .assign 6 (.bin .add (.reg 5) (.reg 5)) ;;
  .store (.bin .add (.reg 3) (.reg 6)) (.load (.bin .add (.reg 0) (.reg 5))) ;;
  .store (.bin .add (.bin .add (.reg 3) (.reg 6)) (.const 1))
    (.load (.bin .add (.reg 1) (.reg 5))) ;;
  .store (.bin .add (.reg 4) (.reg 6)) (.reg 5) ;;
  .store (.bin .add (.bin .add (.reg 4) (.reg 6)) (.const 1)) (.reg 5)

def initTermColumns : Stmt :=
  forRange 5 (.const 0) (.reg 2) initTermColumnStep ;; .ret (.const 0)

theorem initTermColumns_noRand : initTermColumns.NoRand := by
  simp [initTermColumns, initTermColumnStep, forRange, forUp, Stmt.NoRand]

/-- The two input columns precede the two output columns. -/
def initTermColumnsContract (w : ℕ) : Contract where
  pre args _ := ∃ A B n K V, args = [A, B, n, K, V] ∧
    A + n ≤ K ∧ B + n ≤ K ∧ K + 2 * n ≤ V ∧ V + 2 * n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem _ mem' := ∃ A B n K V, args = [A, B, n, K, V] ∧
    (∀ i < n, mem' (K + 2 * i) = mem (A + i) ∧ mem' (K + 2 * i + 1) = mem (B + i) ∧
      mem' (V + 2 * i) = i ∧ mem' (V + 2 * i + 1) = i) ∧
    ∀ y, y < K ∨ (K + 2 * n ≤ y ∧ y < V) ∨ V + 2 * n ≤ y → mem' y = mem y
  cost args _ := 50 * args.getD 2 0 + 20

private theorem initTermColumnStep_triple {w A B n K V i : ℕ} {p : Program} {s : State}
    (hi : i < n) (ha : A + n ≤ K) (hb : B + n ≤ K) (hk : K + 2 * n ≤ V)
    (hv : V + 2 * n < 2 ^ w) (h1 : 1 < 2 ^ w)
    (r0 : s.regs 0 = A) (r1 : s.regs 1 = B) (r3 : s.regs 3 = K) (r4 : s.regs 4 = V)
    (r5 : s.regs 5 = i) :
    Triple w p (fun t => t = s) initTermColumnStep
      (normalPost fun t => (∀ j ≤ 5, t.regs j = s.regs j) ∧
        t.mem = Function.update (Function.update (Function.update (Function.update s.mem
          (K + 2 * i) (s.mem (A + i))) (K + 2 * i + 1) (s.mem (B + i))) (V + 2 * i) i)
          (V + 2 * i + 1) i) (fun _ => 41) := by
  intro st ω hs
  subst st
  refine runs_start_le ?_
  unfold initTermColumnStep
  refine runs_seq_assign_le (v := 2 * i) (Expr.eval_eq_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq r5) (Expr.eval_reg_of_eq r5) (by omega)) (by omega)) ?_
  have eK : (Expr.bin .add (.reg 3) (.reg 6)).eval w
      { s with regs := Function.update s.regs 6 (2 * i) } = some (K + 2 * i) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r3)) (Expr.eval_reg_of_eq rfl) (by omega)
  have eV : (Expr.bin .add (.reg 4) (.reg 6)).eval w
      { s with regs := Function.update s.regs 6 (2 * i) } = some (V + 2 * i) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r4)) (Expr.eval_reg_of_eq rfl) (by omega)
  have eA : (Expr.bin .add (.reg 0) (.reg 5)).eval w
      { s with regs := Function.update s.regs 6 (2 * i) } = some (A + i) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r0))
      (Expr.eval_reg_of_eq (by simpa using r5)) (by omega)
  refine runs_seq_store_le (x := K + 2 * i) (v := s.mem (A + i)) eK
    (Expr.eval_load_of_eq eA rfl) ?_
  refine runs_seq_store_le (x := K + 2 * i + 1) (v := s.mem (B + i)) ?_ ?_ ?_
  · refine Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r3))
      (Expr.eval_reg_of_eq rfl) (by omega)) (Expr.eval_const h1) (by omega)
  · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r1))
      (Expr.eval_reg_of_eq (by simpa using r5)) (by omega)) (Function.update_of_ne (by omega) _ _)
  refine runs_seq_store_le (x := V + 2 * i) (v := i)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r4)) (Expr.eval_reg_of_eq rfl) (by omega))
    (Expr.eval_reg_of_eq (by simpa using r5)) ?_
  refine runs_store_le (x := V + 2 * i + 1) (v := i)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r4))
      (Expr.eval_reg_of_eq rfl) (by omega)) (Expr.eval_const h1) (by omega))
    (Expr.eval_reg_of_eq (by simpa using r5)) ?_ ?_
  · exact ⟨fun j hj => Function.update_of_ne (by omega) _ _, rfl⟩
  · simp [Expr.size]

theorem initTermColumns_meetsContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some initTermColumns) :
    MeetsContract w p f (initTermColumnsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨A, B, n, K, V, rfl, ha, hb, hk, hv, h1⟩ := hpre
  let initial := startState [A, B, n, K, V] mem pos
  let R := fun s : State => s.regs 0 = A ∧ s.regs 1 = B ∧ s.regs 2 = n ∧
    s.regs 3 = K ∧ s.regs 4 = V
  let Inv := fun i (s : State) => R s ∧ s.regs 5 = i ∧
    (∀ j < i, s.mem (K + 2 * j) = mem (A + j) ∧ s.mem (K + 2 * j + 1) = mem (B + j) ∧
      s.mem (V + 2 * j) = j ∧ s.mem (V + 2 * j + 1) = j) ∧
    ∀ y, y < K ∨ (K + 2 * i ≤ y ∧ y < V) ∨ V + 2 * i ≤ y → s.mem y = mem y
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 5) (hi := .reg 2) (lo := .const 0)
    (P := fun s => s = initial) (Inv := Inv) (body := initTermColumnStep)
    41 0 n (Nat.zero_le _) h1 (fun _ => hw _ (by simp))
    (fun s hs => by
      subst s
      exact ⟨Expr.eval_const (Nat.two_pow_pos w), ⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.1.2.2.1)
    (fun i _ hi => by
      intro s ω' ⟨⟨r0, r1, r2, r3, r4⟩, r5, hdata, hframe⟩
      obtain ⟨o, t, c, hr, ht, hc⟩ :=
        initTermColumnStep_triple hi ha hb hk hv h1 r0 r1 r3 r4 r5 s ω' rfl
      cases o with
      | returned => exact False.elim ht
      | normal =>
        obtain ⟨hregs, hm⟩ := ht
        have hA : s.mem (A + i) = mem (A + i) := hframe _ (.inl (by omega))
        have hB : s.mem (B + i) = mem (B + i) := hframe _ (.inl (by omega))
        refine ⟨.normal, t, c, hr, ⟨⟨?_, by simp, ?_, ?_⟩, (hregs 5 le_rfl).trans r5⟩, hc⟩
        · exact ⟨(hregs 0 (by decide)).trans r0, (hregs 1 (by decide)).trans r1,
            (hregs 2 (by decide)).trans r2, (hregs 3 (by decide)).trans r3,
            (hregs 4 (by decide)).trans r4⟩
        · intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
          · obtain ⟨h0, h1', h2, h3⟩ := hdata j hj'
            rw [hm]
            refine ⟨?_, ?_, ?_, ?_⟩
            all_goals
              repeat rw [Function.update_of_ne (by omega)]
              assumption
          · rw [hm, hA, hB]
            refine ⟨?_, ?_, ?_, ?_⟩
            all_goals
              repeat rw [Function.update_of_ne (by omega)]
              exact Function.update_self ..
        · intro y hy
          change y < K ∨ (K + 2 * (i + 1) ≤ y ∧ y < V) ∨ V + 2 * (i + 1) ≤ y at hy
          rw [hm]
          repeat rw [Function.update_of_ne (by omega)]
          exact hframe y (by omega))
  refine runs_start_le ?_
  unfold initTermColumns
  refine runs_seq_triple_le hloop rfl ?_
  intro s ⟨_, _, hdata, hf⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos w))
    ⟨A, B, n, K, V, rfl, hdata, hf⟩ ?_
  simp [initTermColumnsContract, Expr.size, Nat.mul_comm n]

theorem initTermColumns_records {mem mem' : ℕ → ℕ} {A B K V : ℕ} (S : StaticData)
    (hA : ListAt mem A (initEndpointWords S 0)) (hB : ListAt mem B (initEndpointWords S 1))
    (hdata : ∀ i < S.numConn, mem' (K + 2 * i) = mem (A + i) ∧
      mem' (K + 2 * i + 1) = mem (B + i) ∧
      mem' (V + 2 * i) = i ∧ mem' (V + 2 * i + 1) = i) :
    ListAt mem' K ((initTermRecords S).map Prod.fst) ∧
      ListAt mem' V ((initTermRecords S).map Prod.snd) := by
  let rf := fun (f : ℕ × ℕ → ℕ) i => (initTermRecord S i).map f
  have he (f : ℕ × ℕ → ℕ) :
      (initTermRecords S).map f = csrData S.numConn (rf f) := by
    simp [initTermRecords, csrData, List.map_flatMap, rf]
  have hOff (f : ℕ × ℕ → ℕ) (i : ℕ) : initCSRPrefix (rf f) i = 2 * i := by
    simp [initCSRPrefix, rf, initTermRecord, List.map_const', Nat.mul_comm]
  rw [initEndpointWords_eq_map S 0 (by decide)] at hA
  rw [initEndpointWords_eq_map S 1 (by decide)] at hB
  have hA' (i : ℕ) (hi : i < S.numConn) :
      mem (A + i) = ((connRecs S.H S.x S.b).getD i default).endA := by
    have hh := hA i (by simpa [StaticData.numConn] using hi)
    rw [List.getElem_map] at hh
    rw [List.getD_eq_getElem _ _ hi]
    exact hh
  have hB' (i : ℕ) (hi : i < S.numConn) :
      mem (B + i) = ((connRecs S.H S.x S.b).getD i default).endB := by
    have hh := hB i (by simpa [StaticData.numConn] using hi)
    rw [List.getElem_map] at hh
    rw [List.getD_eq_getElem _ _ hi]
    exact hh
  rw [he, he]
  constructor <;> apply initBucket_listAt_from_rows
  · intro i hi
    rw [hOff]
    obtain ⟨h₀, h₁, _, _⟩ := hdata i hi
    apply listAt_cons.mpr
    exact ⟨h₀.trans (hA' i hi), listAt_cons.mpr ⟨h₁.trans (hB' i hi), by simp [ListAt]⟩⟩
  · intro i hi
    rw [hOff]
    obtain ⟨_, _, h₀, h₁⟩ := hdata i hi
    exact listAt_cons.mpr ⟨h₀, listAt_cons.mpr ⟨h₁, by simp [ListAt]⟩⟩

end MinCostFlow.HierPaths

end
