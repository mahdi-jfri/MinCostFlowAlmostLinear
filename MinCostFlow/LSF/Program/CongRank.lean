module

public import MinCostFlow.LSF.Program.KeyedSort
public import MinCostFlow.LSF.Program.TreeArrays
import Mathlib.Tactic.Linarith

/-!
# Ranking the tree edges by their keys

Each vertex index `y ≠ r` stands for its parent edge `pe y`, and has a key, a `K`-limb block at
`dPtr + y K`. `congRankProc` lists the indices `y ≠ r` (`0, …, r - 1, r + 1, …, n - 1`), sorts
them by key with `keyedMergeSortStmt`, and writes the rank `k` of the `k`-th index `y` of the
sorted list into the cell `piPtr + pe y`. So the edge order `π` it writes sorts the tree edges by
their keys. The cost is `O(n K log n)`, from the sort.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow.Num

@[expose] public section

/-- The `i`-th index other than `r`. -/
def skipIdx (r i : ℕ) : ℕ := if i < r then i else i + 1

/-- Args: `[n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr]`. -/
def congRankProc (bSort : ℕ) : Stmt :=
  forRange 8 (.const 0) (.bin .sub (.reg 0) (.const 1))
    (.cond (.bin .lt (.reg 8) (.reg 1)) (.store (.bin .add (.reg 5) (.reg 8)) (.reg 8))
      (.store (.bin .add (.reg 5) (.reg 8)) (.bin .add (.reg 8) (.const 1)))) ;;
  .call 9 bSort [.reg 5, .reg 6, .reg 3, .reg 4, .const 0, .bin .sub (.reg 0) (.const 1)] ;;
  forRange 8 (.const 0) (.bin .sub (.reg 0) (.const 1))
    (.assign 10 (.load (.bin .add (.reg 5) (.reg 8))) ;;
     .store (.bin .add (.reg 7) (.load (.bin .add (.reg 2) (.reg 10)))) (.reg 8)) ;;
  .ret (.const 0)

lemma congRankProc_noRand (bSort : ℕ) : (congRankProc bSort).NoRand := by
  simp [congRankProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `congRankProc`. The parent-edge array at `peBase` is injective on the
indices other than `r`. The list and the sort scratch are `[arrPtr, arrPtr + n)` and
`[scratchPtr, scratchPtr + n)`, with `arrPtr + n ≤ scratchPtr`. -/
def congRankContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n r peBase dPtr K arrPtr scratchPtr piPtr tM : ℕ),
    args = [n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr] ∧ 2 < 2 ^ w ∧ 1 ≤ K ∧ r < n ∧
    (∀ y < n, y ≠ r → mem (peBase + y) < tM) ∧
    (∀ y < n, ∀ y' < n, y ≠ r → y' ≠ r → mem (peBase + y) = mem (peBase + y') → y = y') ∧
    (∀ y < n, Valid mem (dPtr + y * K) h K) ∧
    arrPtr + n ≤ scratchPtr ∧ scratchPtr + n < 2 ^ w ∧
    (dPtr + n * K ≤ arrPtr ∨ scratchPtr + n ≤ dPtr) ∧
    (peBase + n ≤ arrPtr ∨ scratchPtr + n ≤ peBase) ∧
    (piPtr + tM ≤ arrPtr ∨ scratchPtr + n ≤ piPtr) ∧
    (piPtr + tM ≤ peBase ∨ peBase + n ≤ piPtr) ∧
    dPtr + n * K < 2 ^ w ∧ peBase + n < 2 ^ w ∧ piPtr + tM < 2 ^ w
  post args mem ret mem' := ∃ (n r peBase dPtr K arrPtr scratchPtr piPtr tM : ℕ) (S : List ℕ),
    args = [n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr] ∧ ret = 0 ∧
    (∀ a, (a < arrPtr ∨ scratchPtr + n ≤ a) →
      (∀ y < n, y ≠ r → a ≠ piPtr + mem (peBase + y)) → mem' a = mem a) ∧
    S.Nodup ∧ S.length = n - 1 ∧ (∀ y, y ∈ S ↔ y < n ∧ y ≠ r) ∧
    S.Pairwise (fun a b => unsignedVal mem (dPtr + a * K) h K ≤
      unsignedVal mem (dPtr + b * K) h K) ∧
    ∀ k (hk : k < S.length), mem' (piPtr + mem (peBase + S[k])) = k
  cost args _ :=
    (90 * args.getD 4 0 + 180) * args.getD 0 0 * (Nat.clog 2 (args.getD 0 0) + 1) +
      70 * args.getD 0 0 + 100

lemma skipIdx_lt {r n i : ℕ} (hr : r < n) (hi : i < n - 1) : skipIdx r i < n := by
  unfold skipIdx; split_ifs <;> omega

lemma skipIdx_ne {r i : ℕ} : skipIdx r i ≠ r := by
  unfold skipIdx; split_ifs <;> omega

/-- The list of indices other than `r`. -/
lemma skipList_spec {r n : ℕ} (hr : r < n) :
    ((List.range (n - 1)).map (skipIdx r)).Nodup ∧
      ∀ y, y ∈ (List.range (n - 1)).map (skipIdx r) ↔ y < n ∧ y ≠ r := by
  refine ⟨List.Nodup.map (fun a b hab => by unfold skipIdx at hab; split_ifs at hab <;> omega)
    List.nodup_range, fun y => ?_⟩
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨skipIdx_lt hr hi, skipIdx_ne⟩
  · rintro ⟨hy, hyr⟩
    by_cases hlt : y < r
    · exact ⟨y, by omega, by simp [skipIdx, hlt]⟩
    · exact ⟨y - 1, by omega, by unfold skipIdx; split_ifs <;> omega⟩

theorem congRank_meetsContract {w h : ℕ} {p : Program} {b bSort : ℕ}
    (hp : p.procs[b]? = some (congRankProc bSort))
    (hSort : MeetsContract w p bSort (keyedMergeSortContract w h)) :
    MeetsContract w p b (congRankContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr, tM, rfl, hw2, hK, hrn, hpe, hinj,
    hval, has, hsw, hDA, hPA, hPiA, hPiP, hdw, hpw, hpiw⟩ := hpre
  set args := [n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hR0 : ∀ i < 8, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hKw : K < 2 ^ w := hwords K (by simp [hargs])
  -- loop 1: the list of indices other than `r`
  let Inv1 : ℕ → State → Prop := fun i st =>
    (∀ k < 8, st.regs k = args.getD k 0) ∧ st.regs 8 = i ∧
    (∀ k < i, st.mem (arrPtr + k) = skipIdx r k) ∧
    (∀ a, (a < arrPtr ∨ arrPtr + n ≤ a) → st.mem a = mem a)
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 0) (.bin .sub (.reg 0) (.const 1))
        (.cond (.bin .lt (.reg 8) (.reg 1)) (.store (.bin .add (.reg 5) (.reg 8)) (.reg 8))
          (.store (.bin .add (.reg 5) (.reg 8)) (.bin .add (.reg 8) (.const 1)))))
      (normalPost (Inv1 (n - 1)))
      (fun _ => (n - 1 - 0) * (20 + (Expr.bin .sub (.reg 0) (.const 1)).size + 8) +
        ((Expr.const 0).size + (Expr.bin .sub (.reg 0) (.const 1)).size + 5)) := by
    refine Triple.forRange_const 20 0 (n - 1) (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun k hk => ?_, by simp, fun k hk => absurd hk (by omega),
        fun a _ => rfl⟩
      simp only [Function.update_of_ne (show k ≠ 8 by omega)]; exact hR0 k hk
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro i _ hi st ω' ⟨hr, h8, hdone, hfr⟩
      have r1 : st.regs 1 = r := hr 1 (by omega)
      have r5 : st.regs 5 = arrPtr := hr 5 (by omega)
      refine runs_start_le ?_
      refine runs_cond_le (v := if i < r then 1 else 0) (by eval_expr) ?_ ?_
      · intro hne
        have hlt : i < r := by by_contra hc; simp [hc] at hne
        refine runs_store_le (x := arrPtr + i) (v := i) (by eval_expr) (by eval_expr) ⟨⟨?_, by simp,
          fun k hk => ?_, fun a ha => ?_⟩, by simpa using h8⟩ (by simp [Expr.size])
        · intro k hk
          simp only [Function.update_of_ne (show k ≠ 8 by omega)]; exact hr k hk
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · rw [Function.update_of_ne (by omega)]; exact hdone k hk
          · rw [Function.update_self]; simp [skipIdx, hlt]
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · intro hz
        have hge : ¬ i < r := by intro hc; simp [hc] at hz
        refine runs_store_le (x := arrPtr + i) (v := i + 1) (by eval_expr) (by eval_expr)
          ⟨⟨?_, by simp, fun k hk => ?_, fun a ha => ?_⟩, by simpa using h8⟩ (by simp [Expr.size])
        · intro k hk
          simp only [Function.update_of_ne (show k ≠ 8 by omega)]; exact hr k hk
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · rw [Function.update_of_ne (by omega)]; exact hdone k hk
          · rw [Function.update_self]; simp [skipIdx, hge]
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
  refine runs_start_le ?_
  unfold congRankProc
  refine runs_seq_triple_le hloop1 rfl ?_
  rintro st₁ ⟨hr1, -, hdone1, hfr1⟩
  have r0 : st₁.regs 0 = n := hr1 0 (by omega)
  have r3 : st₁.regs 3 = dPtr := hr1 3 (by omega)
  have r4 : st₁.regs 4 = K := hr1 4 (by omega)
  have r5 : st₁.regs 5 = arrPtr := hr1 5 (by omega)
  have r6 : st₁.regs 6 = scratchPtr := hr1 6 (by omega)
  have hkey1 : ∀ y < n, ∀ i < K, st₁.mem (dPtr + y * K + i) = mem (dPtr + y * K + i) := by
    intro y hy i hi
    have := Nat.mul_le_mul_right K (show y + 1 ≤ n by omega)
    exact hfr1 _ (by rcases hDA with hc | hc <;> [left; right] <;> nlinarith)
  have hslice1 : memSlice st₁.mem arrPtr (n - 1) = (List.range (n - 1)).map (skipIdx r) := by
    refine List.ext_getElem (by simp [memSlice_length]) fun i h1 h2 => ?_
    simp only [memSlice, List.getElem_map, List.getElem_range]
    exact hdone1 i (by simpa using h2)
  -- the sort
  refine runs_seq_call_le (vs := [arrPtr, scratchPtr, dPtr, K, 0, n - 1]) hSort
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨arrPtr, scratchPtr, dPtr, K, 0, n - 1, rfl, hw2, hK, Nat.zero_le _, by omega, by omega,
      Or.inl (by omega), fun i _ hi => ?_⟩ ?_
  · have hidx : st₁.mem (arrPtr + i) = skipIdx r i := hdone1 i hi
    have hlt := skipIdx_lt hrn hi
    have hb : skipIdx r i * K + K ≤ n * K := by
      have := Nat.mul_le_mul_right K (show skipIdx r i + 1 ≤ n by omega); nlinarith
    simp only [hidx]
    refine ⟨by omega, fun j hj => by rw [hkey1 _ hlt j hj]; exact hval _ hlt j hj, ?_, ?_⟩
    · rcases hDA with h | h <;> [left; right] <;> omega
    · rcases hDA with h | h <;> [left; right] <;> omega
  rintro v₂ mem₂ pos₂ ⟨a₂, s₂, k₂, L₂, lo₂, hi₂, heq₂, -, hsorted, hperm, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hsorted hperm hfr₂
  simp only [Nat.sub_zero, Nat.add_zero] at hsorted hperm hfr₂
  set S := memSlice mem₂ arrPtr (n - 1) with hS
  rw [hslice1] at hperm
  obtain ⟨hnd0, hmem0⟩ := skipList_spec hrn
  have hSnd : S.Nodup := hperm.nodup_iff.mpr hnd0
  have hSmem : ∀ y, y ∈ S ↔ y < n ∧ y ≠ r := fun y => (hperm.mem_iff).trans (hmem0 y)
  have hSlen : S.length = n - 1 := memSlice_length _ _ _
  have hkeyS : ∀ y < n, unsignedVal st₁.mem (dPtr + y * K) h K =
      unsignedVal mem (dPtr + y * K) h K := fun y hy => unsignedVal_congr (hkey1 y hy)
  have hSsorted : S.Pairwise (fun a b => unsignedVal mem (dPtr + a * K) h K ≤
      unsignedVal mem (dPtr + b * K) h K) := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hsorted
    rw [← hkeyS a ((hSmem a).mp ha).1, ← hkeyS b ((hSmem b).mp hb).1]; exact hab
  have hpe2 : ∀ y < n, mem₂ (peBase + y) = mem (peBase + y) := fun y hy => by
    rw [hfr₂ _ (by rcases hPA with h | h <;> [left; right] <;> omega)
      (by rcases hPA with h | h <;> [left; right] <;> omega), hfr1 _ (by omega)]
  -- loop 3: write the ranks
  let Inv3 : ℕ → State → Prop := fun k st =>
    (∀ j < 8, st.regs j = args.getD j 0) ∧ st.regs 8 = k ∧
    (∀ a, (∀ y < n, y ≠ r → a ≠ piPtr + mem (peBase + y)) → st.mem a = mem₂ a) ∧
    ∀ k' < k, st.mem (piPtr + mem (peBase + S.getD k' 0)) = k'
  have hloop3 : Triple w p (fun st => st.mem = mem₂ ∧ st.regs = Function.update st₁.regs 9 v₂)
      (forRange 8 (.const 0) (.bin .sub (.reg 0) (.const 1))
        (.assign 10 (.load (.bin .add (.reg 5) (.reg 8))) ;;
         .store (.bin .add (.reg 7) (.load (.bin .add (.reg 2) (.reg 10)))) (.reg 8)))
      (normalPost (Inv3 (n - 1)))
      (fun _ => (n - 1 - 0) * (20 + (Expr.bin .sub (.reg 0) (.const 1)).size + 8) +
        ((Expr.const 0).size + (Expr.bin .sub (.reg 0) (.const 1)).size + 5)) := by
    refine Triple.forRange_const 20 0 (n - 1) (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st ⟨hm, hrg⟩
      refine ⟨by eval_expr, fun k hk => ?_, by simp, fun a _ => hm ▸ rfl,
        fun k hk => absurd hk (by omega)⟩
      simp only [Function.update_of_ne (show k ≠ 8 by omega), hrg,
        Function.update_of_ne (show k ≠ 9 by omega)]; exact hr1 k hk
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro k _ hk st ω' ⟨hr, h8, hfr, hdone⟩
      have r2 : st.regs 2 = peBase := hr 2 (by omega)
      have r5 : st.regs 5 = arrPtr := hr 5 (by omega)
      have r7 : st.regs 7 = piPtr := hr 7 (by omega)
      have hkS : k < S.length := by omega
      have hSk : st.mem (arrPtr + k) = S[k] := by
        rw [hfr _ (fun y hy hyr => by
          have := hpe y hy hyr; rcases hPiA with h | h <;> omega)]
        simp [hS, memSlice]
      obtain ⟨hyn, hyr⟩ := (hSmem _).mp (List.getElem_mem hkS)
      have hpk : st.mem (peBase + S[k]) = mem (peBase + S[k]) := by
        rw [hfr _ (fun y hy hyr => by
          have := hpe y hy hyr; rcases hPiP with h | h <;> omega), hpe2 _ hyn]
      have hpt := hpe _ hyn hyr
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := S[k]) (by rw [← hSk]; eval_expr) ?_
      refine runs_store_le (x := piPtr + mem (peBase + S[k])) (v := k)
        (by rw [← hpk]; eval_expr) (by eval_expr) ⟨⟨fun j hj => ?_, by simp, fun a ha => ?_,
          fun k' hk' => ?_⟩, by simpa using h8⟩ (by simp [Expr.size])
      · simp only [Function.update_of_ne (show j ≠ 8 by omega),
          Function.update_of_ne (show j ≠ 10 by omega)]; exact hr j hj
      · dsimp only; rw [Function.update_of_ne (ha _ hyn hyr)]; exact hfr a ha
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
        · have hk'S : k' < S.length := by omega
          obtain ⟨hyn', hyr'⟩ := (hSmem _).mp (List.getElem_mem hk'S)
          have hne : mem (peBase + S[k']) ≠ mem (peBase + S[k]) := by
            intro heq
            have := hinj _ hyn' _ hyn hyr' hyr heq
            have := (hSnd.getElem_inj_iff).mp this
            omega
          rw [List.getD_eq_getElem _ _ hk'S, Function.update_of_ne (by omega)]
          have := hdone k' hk'
          rwa [List.getD_eq_getElem _ _ hk'S] at this
        · rw [List.getD_eq_getElem _ _ hkS, Function.update_self]
  refine runs_seq_triple_le hloop3 ⟨rfl, rfl⟩ ?_
  rintro st₃ ⟨-, -, hfr3, hdone3⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, r, peBase, dPtr, K, arrPtr, scratchPtr, piPtr, tM,
    S, rfl, rfl, fun a ha hb => ?_, hSnd, hSlen, hSmem, hSsorted, fun k hk => ?_⟩ ?_
  · rw [hfr3 a hb, hfr₂ a (by omega) (by omega), hfr1 a (by omega)]
  · have := hdone3 k (by omega)
    rwa [List.getD_eq_getElem _ _ hk] at this
  · simp only [congRankContract, keyedMergeSortContract, hargs, List.getD_cons_zero,
      List.getD_cons_succ, Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize, Nat.sub_zero]
    have hc : Nat.clog 2 (n - 1) ≤ Nat.clog 2 n := Nat.clog_mono_right 2 (by omega)
    have hm : (90 * K + 180) * (n - 1) * (Nat.clog 2 (n - 1) + 1) ≤
        (90 * K + 180) * n * (Nat.clog 2 n + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega

end

end MinCostFlow.LSF.Program
