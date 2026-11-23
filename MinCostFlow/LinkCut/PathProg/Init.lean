module

public import MinCostFlow.LinkCut.PathProg.Bodies

/-!
# The run of the initialization

`pathInitBody` on `[n, L, heap]` writes the arena header and, in one loop over the records of
nodes `0 .. 2 n`, the words of each record that are not zero: the size `1`, the four layout
words of the value block, and the link to the next free edge slot. Every other word of the
arena stays zero, since memory from the heap pointer on is zero at the start.

`pathInitBody_runs` states what memory holds afterwards (`InitMem`): the header, a zero index,
and record words given by `initWord`. The node records then hold the model state
`lctInit pathPayload n none` (shown in a later file).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.LinkCut.Gen

/-- The parent word of record `x` at the start: the next free edge slot, for an edge slot that
is not the last one. -/
def initPar (n x : ℕ) : ℕ := if n < x ∧ x + 1 < 2 * n then x + 1 else 0

/-- Word `off` of record `x` at the start, for tree width `K`. -/
def initWord (n K x off : ℕ) : ℕ :=
  if off = 2 then initPar n x
  else if off = 4 then 1
  else if off = 6 then recW K
  else if off = 7 then 6 + 4 * K
  else if off = 8 then 2 * K
  else if off = 9 then K
  else 0

/-- What memory holds after the initialization on `[n, L, heap]`, started in `mem`. -/
structure InitMem (n L heap : ℕ) (mem m : ℕ → ℕ) : Prop where
  fh : m heap = if n ≤ 1 then 0 else n + 1
  hn : m (heap + 1) = n
  hL : m (heap + 2) = L
  hK : m (heap + 3) = treeLimbs L
  hnb : m (heap + 4) = arenaNb heap n
  below : ∀ a < heap, m a = mem a
  idx : ∀ a, heap + 5 ≤ a → a < arenaNb heap n → m a = 0
  recs : ∀ x ≤ 2 * n, ∀ off < recW (treeLimbs L),
    m (arenaNb heap n + recW (treeLimbs L) * x + off) = initWord n (treeLimbs L) x off
  zero : ZeroFrom m (arenaEnd heap n L)

private theorem mul_step {S i : ℕ} : S * (i + 1) = S * i + S := by ring

private theorem mul_mono {S i j : ℕ} (h : i ≤ j) : S * i ≤ S * j := Nat.mul_le_mul_left _ h

/-- Two words of different records, or at different offsets, differ. -/
private theorem rec_ne {nb S x y off off' : ℕ} (hoff : off < S) (hoff' : off' < S)
    (hne : x ≠ y ∨ off ≠ off') : nb + S * x + off ≠ nb + S * y + off' := by
  intro heq
  rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
  · have := mul_mono (S := S) (Nat.succ_le_of_lt hxy)
    rw [mul_step] at this; omega
  · rcases hne with h | h
    · exact h rfl
    · omega
  · have := mul_mono (S := S) (Nat.succ_le_of_lt hxy)
    rw [mul_step] at this; omega

private theorem par_val (n i : ℕ) :
    (if n < i then 1 else 0) * (if i + 1 < 2 * n then 1 else 0) * (i + 1) = initPar n i := by
  unfold initPar
  split_ifs <;> simp_all <;> omega

private theorem par_le (n i : ℕ) : initPar n i ≤ i + 1 := by
  unfold initPar; split_ifs <;> omega

/-- The loop over the records, started with the registers set and memory `M`, which is zero
from `heap + 5` on. -/
theorem initLoop_triple {w n L heap : ℕ} {p : Program} {M : ℕ → ℕ}
    (hroom : arenaEnd heap n L < 2 ^ w) (hHz : ∀ a, heap + 5 ≤ a → M a = 0) :
    Triple w p (fun st => st.regs 0 = n ∧ st.regs 1 = L ∧ st.regs 2 = heap ∧
        st.regs 3 = treeLimbs L ∧ st.regs 4 = arenaNb heap n ∧ st.regs 5 = recW (treeLimbs L) ∧
        st.regs 6 = 2 * n + 1 ∧ st.mem = M)
      (forRange 7 (.const 0) (.reg 6) initRecord)
      (normalPost fun st => st.regs 4 = arenaNb heap n ∧ st.regs 5 = recW (treeLimbs L) ∧
        st.regs 6 = 2 * n + 1 ∧
        (∀ a, a < arenaNb heap n ∨ arenaNb heap n + recW (treeLimbs L) * (2 * n + 1) ≤ a →
          st.mem a = M a) ∧
        ∀ x < 2 * n + 1, ∀ off < recW (treeLimbs L),
          st.mem (arenaNb heap n + recW (treeLimbs L) * x + off) = initWord n (treeLimbs L) x off)
      (fun _ => (2 * n + 1 - 0) * (100 + (Expr.reg 6).size + 8) +
        ((Expr.const 0).size + (Expr.reg 6).size + 5)) := by
  set K := treeLimbs L with hKdef
  set S := recW K with hSdef
  set nb := arenaNb heap n with hnbdef
  have hS9 : 9 < S := by rw [hSdef]; unfold recW; omega
  have hend : arenaEnd heap n L = nb + S * (2 * n + 1) := rfl
  rw [hend] at hroom
  have hSn : S ≤ S * (2 * n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hK9 : 9 * K < S := by rw [hSdef]; unfold recW; omega
  have hnbv : nb = heap + (4 * n + 8) := by rw [hnbdef, arenaNb]; omega
  have hKv : K = 4 * L + 8 := rfl
  have hSv : S = 13 + 9 * K := rfl
  have h2n : 2 * n + 1 ≤ S * (2 * n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hw : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = n ∧ st.regs 1 = L ∧ st.regs 2 = heap ∧ st.regs 3 = K ∧ st.regs 4 = nb ∧
    st.regs 5 = S ∧ st.regs 6 = 2 * n + 1 ∧ st.regs 7 = i ∧ i ≤ 2 * n + 1 ∧
    (∀ a, a < nb ∨ nb + S * i ≤ a → st.mem a = M a) ∧
    (∀ x < i, ∀ off < S, st.mem (nb + S * x + off) = initWord n K x off)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := initRecord)
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = L ∧ st.regs 2 = heap ∧ st.regs 3 = K ∧
      st.regs 4 = nb ∧ st.regs 5 = S ∧ st.regs 6 = 2 * n + 1 ∧ st.mem = M)
    (Inv := Inv) 100 0 (2 * n + 1) (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, hm⟩ => by
      refine ⟨by simp [Expr.eval], ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, by omega, fun a _ => by simp [hm],
        fun x hx => absurd hx (Nat.not_lt_zero _)⟩ <;>
        simpa [Function.update_apply] using ‹_›)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h6 : st.regs 6 = 2 * n + 1 := hi.2.2.2.2.2.2.1
      simp [Expr.eval, h6])
    (fun i _ hin => by
      rintro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, -, hout, hrecs⟩
      have hstep : S * (i + 1) ≤ S * (2 * n + 1) := mul_mono hin
      rw [mul_step] at hstep
      have hmi : S * (i + 1) = S * i + S := mul_step
      have hSi : nb + S * i + S < 2 ^ w := by omega
      apply runs_start_le
      unfold initRecord
      refine runs_seq_assign_le (by eval_expr) ?_
      refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun N₁ hN₁ => ?_
      refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun N₂ hN₂ => ?_
      refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun N₃ hN₃ => ?_
      refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun N₄ hN₄ => ?_
      refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun N₅ hN₅ => ?_
      have hpv := par_le n i
      refine runs_store_le (x := nb + S * i + 2) (v := initPar n i) (by eval_expr) (by
        rw [← par_val]
        eval_expr_raw
        all_goals first | rfl | omega | (split_ifs <;> omega)) ?_ ?_
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, by omega, fun a ha => ?_,
          fun x hx off hoff => ?_⟩, ?_⟩
        all_goals try (simp only [Function.update_apply]; first | assumption | (simp; done))
        · have hne : ∀ c < S, a ≠ nb + S * i + c := fun c hc => by
            rcases ha with ha | ha <;> omega
          rw [hN₅, hN₄, hN₃, hN₂, hN₁]
          dsimp only
          rw [Function.update_of_ne (hne 2 (by omega)), Function.update_of_ne (hne 9 (by omega)),
            Function.update_of_ne (hne 8 (by omega)), Function.update_of_ne (hne 7 (by omega)),
            Function.update_of_ne (hne 6 (by omega)), Function.update_of_ne (hne 4 (by omega))]
          exact hout a (by omega)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · have hxi : S * x + S ≤ S * i := by
              have := mul_mono (S := S) (Nat.succ_le_of_lt hx); rw [mul_step] at this; exact this
            have hne : ∀ c < S, nb + S * x + off ≠ nb + S * i + c := fun c hc => by omega
            rw [hN₅, hN₄, hN₃, hN₂, hN₁]
            dsimp only
            rw [Function.update_of_ne (hne 2 (by omega)), Function.update_of_ne (hne 9 (by omega)),
              Function.update_of_ne (hne 8 (by omega)), Function.update_of_ne (hne 7 (by omega)),
              Function.update_of_ne (hne 6 (by omega)), Function.update_of_ne (hne 4 (by omega))]
            exact hrecs x hx off hoff
          · simp only [hN₅, hN₄, hN₃, hN₂, hN₁, Function.update_apply]
            have hz0 : st.mem (nb + S * x + off) = 0 := by
              rw [hout _ (Or.inr (by omega))]; exact hHz _ (by omega)
            split_ifs <;> unfold initWord <;> split_ifs <;> first | omega | rfl | exact hz0
      · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega)
  refine hloop.conseq (fun _ h => h) (fun o st => ?_) (fun _ _ => le_rfl)
  cases o with
  | normal =>
    rintro ⟨-, -, -, -, h4, h5, h6, -, -, hout, hrecs⟩
    exact ⟨h4, h5, h6, hout, hrecs⟩
  | returned _ => exact False.elim

/-- The run of `pathInitBody`. -/
theorem pathInitBody_runs {w n L heap pos : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hz : ZeroFrom mem heap) (hroom : arenaEnd heap n L < 2 ^ w) :
    ∃ o st' c, Runs w p ω pathInitBody (startState [n, L, heap] mem pos) o st' c ∧
      (o.value = arenaEnd heap n L ∧ InitMem n L heap mem st'.mem) ∧
      c ≤ 120 * (2 * n + 1) + 200 := by
  set K := treeLimbs L with hKdef
  set S := recW K with hSdef
  set nb := arenaNb heap n with hnbdef
  have hS9 : 9 < S := by rw [hSdef]; unfold recW; omega
  have hend : arenaEnd heap n L = nb + S * (2 * n + 1) := rfl
  rw [hend] at hroom
  have hSn : S ≤ S * (2 * n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hK9 : 9 * K < S := by rw [hSdef]; unfold recW; omega
  have hnbv : nb = heap + (4 * n + 8) := by rw [hnbdef, arenaNb]; omega
  have hKv : K = 4 * L + 8 := rfl
  have hSv : S = 13 + 9 * K := rfl
  have hw : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold pathInitBody
  rw [startState]
  wram_step; wram_step; wram_step; wram_step
  refine runs_seq_store_named_le (by eval_expr_raw <;> first | omega | split_ifs <;> omega)
    (x := heap) (v := (1 - (if n < 2 then 1 else 0)) * (n + 1)) (by
      eval_expr_raw
      all_goals first | rfl | omega | (split_ifs <;> omega)) fun M₁ hM₁ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₄ hM₄ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₅ hM₅ => ?_
  -- The memory after the header.
  have hH : ∀ a, a < heap ∨ heap + 5 ≤ a → M₅ a = mem a := by
    intro a ha
    rw [hM₅, hM₄, hM₃, hM₂, hM₁]
    simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  have hHz : ∀ a, heap + 5 ≤ a → M₅ a = 0 := fun a ha => by rw [hH a (Or.inr ha)]; exact hz a (by omega)
  have hloop := initLoop_triple (p := p) (n := n) (L := L) (by rw [hend]; exact hroom) hHz
  refine runs_seq_triple_le hloop ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun st₁ hst₁ => ?_
  obtain ⟨h4, h5, h6, hout, hrecs⟩ := hst₁
  have hret : (Expr.bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 6))).eval w st₁ =
      some (nb + S * (2 * n + 1)) :=
    Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_mul (Expr.eval_reg_of_eq h5)
      (Expr.eval_reg_of_eq h6) (by omega)) (by omega)
  refine runs_ret_le hret ?_ ?_
  swap
  · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega
  refine ⟨hend.symm, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha ha' => ?_,
    fun x hx off hoff => hrecs x (by omega) off hoff, fun a ha => ?_⟩
  · rw [hout _ (Or.inl (by omega)), hM₅, hM₄, hM₃, hM₂, hM₁]
    simp only [Function.update_apply]
    split_ifs <;> omega
  · rw [hout _ (Or.inl (by omega)), hM₅, hM₄, hM₃, hM₂]
    simp only [Function.update_apply]
    split_ifs <;> omega
  · rw [hout _ (Or.inl (by omega)), hM₅, hM₄, hM₃]
    simp only [Function.update_apply]
    split_ifs <;> omega
  · rw [hout _ (Or.inl (by omega)), hM₅, hM₄]
    simp only [Function.update_apply]
    split_ifs <;> omega
  · rw [hout _ (Or.inl (by omega)), hM₅]
    simp only [Function.update_apply]
    split_ifs <;> omega
  · rw [hout _ (Or.inl (by omega))]; exact hH a (Or.inl ha)
  · rw [hout _ (Or.inl (by omega))]; exact hHz a ha
  · show st₁.mem a = 0
    rw [hout _ (Or.inr (by rw [hend] at ha; omega))]; exact hHz a (by rw [hend] at ha; omega)

end MinCostFlow.LinkCut.PathProg
