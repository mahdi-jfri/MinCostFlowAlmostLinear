module

public import WordRAM.Logic
public import WordRAM.Tactic
public import WordRAM.Layout
public import MinCostFlow.Machine.WideWord.ArithAddSub

/-!
# Multiword multiplication on the Word-RAM

This file implements and verifies `mwMul`, computing `(x * y) % 2 ^ (L * h)` in time
`O(L + la * lb)` where `la = activeLimbs x L h` and `lb = activeLimbs y L h`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Active limb count from host memory and `tab` update helpers -/

/-- Number of active limbs (`≤ L`) of the `L`-limb word starting at `ptr` in `mem`:
the smallest `k ≤ L` such that `mem (ptr + i) = 0` for all `k ≤ i < L`. -/
def memActiveLimbs (mem : ℕ → ℕ) (ptr : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => if mem (ptr + L) = 0 then memActiveLimbs mem ptr L else L + 1

theorem memActiveLimbs_le (mem : ℕ → ℕ) (ptr L : ℕ) : memActiveLimbs mem ptr L ≤ L := by
  induction L with
  | zero => simp [memActiveLimbs]
  | succ L ih =>
    simp only [memActiveLimbs]
    split_ifs
    · exact Nat.le_trans ih (Nat.le_succ _)
    · exact le_rfl

theorem memActiveLimbs_eq_of_lt {mem₁ mem₂ : ℕ → ℕ} {ptr L : ℕ}
    (h : ∀ i < L, mem₁ (ptr + i) = mem₂ (ptr + i)) :
    memActiveLimbs mem₁ ptr L = memActiveLimbs mem₂ ptr L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [memActiveLimbs]
    rw [h L (Nat.lt_succ_self L), ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem memActiveLimbs_eq_activeLimbs_of_pointwise {mem : ℕ → ℕ} {ptr L h x : ℕ}
    (hx : ∀ i < L, mem (ptr + i) = (x / 2 ^ (i * h)) % 2 ^ h) :
    memActiveLimbs mem ptr L = activeLimbs x L h := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [memActiveLimbs, activeLimbs, hx L (Nat.lt_succ_self L),
      ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))]

theorem memActiveLimbs_eq_activeLimbs {mem : ℕ → ℕ} {ptr L h x : ℕ} (hx : LimbsAt mem ptr L h x) :
    memActiveLimbs mem ptr L = activeLimbs x L h :=
  memActiveLimbs_eq_activeLimbs_of_pointwise fun _ hi => hx.getElem hi

theorem evalLimbs_tab_update (h L idx new : ℕ) (f : ℕ → ℕ) (hidx : idx < L) :
    evalLimbs h (tab L (Function.update f idx new)) + 2 ^ (idx * h) * f idx =
    evalLimbs h (tab L f) + 2 ^ (idx * h) * new := by
  induction L with
  | zero => omega
  | succ L ih =>
    have htab : ∀ g : ℕ → ℕ, tab (L + 1) g = tab L g ++ [g L] := by
      intro g; simp [tab, List.range_succ]
    have hlen : ∀ g : ℕ → ℕ, (tab L g).length = L := by
      intro g; simp [tab]
    have heval1 : ∀ a : ℕ, evalLimbs h [a] = a := by
      intro a; simp [evalLimbs]
    rw [htab, htab, evalLimbs_append, evalLimbs_append, hlen, hlen, heval1, heval1]
    by_cases heq : idx = L
    · subst heq
      have hagree : tab idx (Function.update f idx new) = tab idx f := by
        simp only [tab]
        exact List.map_congr_left fun j hj =>
          Function.update_of_ne (Nat.ne_of_lt (List.mem_range.mp hj)) new f
      rw [hagree, Function.update_self]
      omega
    · have hlt : idx < L := by omega
      rw [Function.update_of_ne (Nat.ne_of_gt hlt)]
      have hrec := ih hlt
      omega

private theorem evalLimbs_tab_eq_zero (h L : ℕ) (f : ℕ → ℕ) (hf : ∀ k < L, f k = 0) :
    evalLimbs h (tab L f) = 0 := by
  induction L with
  | zero => simp [tab, evalLimbs]
  | succ L ih =>
    have htab : tab (L + 1) f = tab L f ++ [f L] := by simp [tab, List.range_succ]
    rw [htab, evalLimbs_append, ih (fun k hk => hf k (Nat.lt_succ_of_lt hk)),
      hf L (Nat.lt_succ_self L)]
    simp [evalLimbs]

private theorem evalLimbs_tab_update_mem (h L idx new : ℕ) (m : ℕ → ℕ) (dst : ℕ) (hidx : idx < L) :
    evalLimbs h (tab L (fun k => Function.update m (dst + idx) new (dst + k))) +
        2 ^ (idx * h) * m (dst + idx) =
      evalLimbs h (tab L (fun k => m (dst + k))) + 2 ^ (idx * h) * new := by
  have hfun : (fun k => Function.update m (dst + idx) new (dst + k)) =
      Function.update (fun k => m (dst + k)) idx new := by
    funext k
    by_cases hki : k = idx
    · subst hki; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hki]
  rw [hfun]
  exact evalLimbs_tab_update h L idx new (fun k => m (dst + k)) hidx

private theorem mul_limb_acc_lt {ai bj dij carry h w : ℕ}
    (hai : ai < 2 ^ h) (hbj : bj < 2 ^ h) (hd : dij < 2 ^ h) (hc : carry < 2 ^ h)
    (hw2 : 2 * h + 2 ≤ w) :
    ai * bj + dij + carry < 2 ^ (2 * h) ∧ ai * bj + dij + carry < 2 ^ w := by
  set m := 2 ^ h - 1
  have hm1 : 2 ^ h = m + 1 := by
    have hpos : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    omega
  have hai_le : ai ≤ m := by omega
  have hbj_le : bj ≤ m := by omega
  have hd_le : dij ≤ m := by omega
  have hc_le : carry ≤ m := by omega
  have hmul_le : ai * bj ≤ m * m := Nat.mul_le_mul hai_le hbj_le
  have hsq : 2 ^ h * 2 ^ h = 2 ^ (2 * h) := by
    rw [← Nat.pow_add, show h + h = 2 * h by ring]
  have hlt_sq : ai * bj + dij + carry < 2 ^ (2 * h) := by
    rw [← hsq, hm1]
    have hcalc : m * m + m + m + 1 = (m + 1) * (m + 1) := by ring
    omega
  have hw_lt : 2 ^ (2 * h) < 2 ^ w :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ⟨hlt_sq, lt_trans hlt_sq hw_lt⟩

private theorem mul_inner_step_eq {L i j h ai bj dij carry mem_sum mem'_sum x y : ℕ}
    (hbj : bj = (y / 2 ^ (j * h)) % 2 ^ h)
    (hsum : (mem_sum + 2 ^ ((i + j) * h) * carry) % 2 ^ (L * h) =
      (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ai * (y % 2 ^ (j * h))) % 2 ^ (L * h))
    (hupd : mem'_sum + 2 ^ ((i + j) * h) * dij =
      mem_sum + 2 ^ ((i + j) * h) * ((ai * bj + dij + carry) % 2 ^ h)) :
    (mem'_sum + 2 ^ ((i + j + 1) * h) * ((ai * bj + dij + carry) / 2 ^ h)) % 2 ^ (L * h) =
      (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ai * (y % 2 ^ ((j + 1) * h))) % 2 ^ (L * h) := by
  set p := ai * bj + dij + carry
  have hpow1 : 2 ^ ((i + j + 1) * h) = 2 ^ ((i + j) * h) * 2 ^ h := by
    rw [← Nat.pow_add, show (i + j) * h + h = (i + j + 1) * h by ring]
  have hpow_ij : 2 ^ ((i + j) * h) = 2 ^ (i * h) * 2 ^ (j * h) := by
    rw [← Nat.pow_add, Nat.add_mul]
  have hp_split : p % 2 ^ h + 2 ^ h * (p / 2 ^ h) = p := Nat.mod_add_div p (2 ^ h)
  have heq_nat : mem'_sum + 2 ^ ((i + j + 1) * h) * (p / 2 ^ h) =
      mem_sum + 2 ^ ((i + j) * h) * carry + 2 ^ (i * h) * ai * (2 ^ (j * h) * bj) := by
    have h1 : mem'_sum + 2 ^ ((i + j + 1) * h) * (p / 2 ^ h) + 2 ^ ((i + j) * h) * dij =
        mem_sum + 2 ^ ((i + j) * h) * (p % 2 ^ h + 2 ^ h * (p / 2 ^ h)) := by
      rw [hpow1]
      calc mem'_sum + (2 ^ ((i + j) * h) * 2 ^ h) * (p / 2 ^ h) + 2 ^ ((i + j) * h) * dij
          = (mem'_sum + 2 ^ ((i + j) * h) * dij) + 2 ^ ((i + j) * h) * (2 ^ h * (p / 2 ^ h)) := by ring
        _ = (mem_sum + 2 ^ ((i + j) * h) * (p % 2 ^ h)) + 2 ^ ((i + j) * h) * (2 ^ h * (p / 2 ^ h)) := by
            rw [hupd]
        _ = mem_sum + 2 ^ ((i + j) * h) * (p % 2 ^ h + 2 ^ h * (p / 2 ^ h)) := by ring
    rw [hp_split] at h1
    have h2 : mem_sum + 2 ^ ((i + j) * h) * p =
        (mem_sum + 2 ^ ((i + j) * h) * carry + 2 ^ (i * h) * ai * (2 ^ (j * h) * bj)) +
          2 ^ ((i + j) * h) * dij := by
      rw [hpow_ij]
      dsimp only [p]
      ring
    rw [h2] at h1
    exact Nat.add_right_cancel h1
  rw [heq_nat]
  calc (mem_sum + 2 ^ ((i + j) * h) * carry + 2 ^ (i * h) * ai * (2 ^ (j * h) * bj)) % 2 ^ (L * h)
      = ((mem_sum + 2 ^ ((i + j) * h) * carry) % 2 ^ (L * h) +
          2 ^ (i * h) * ai * (2 ^ (j * h) * bj)) % 2 ^ (L * h) := by
          rw [Nat.mod_add_mod]
    _ = ((x % 2 ^ (i * h) * y + 2 ^ (i * h) * ai * (y % 2 ^ (j * h))) % 2 ^ (L * h) +
          2 ^ (i * h) * ai * (2 ^ (j * h) * bj)) % 2 ^ (L * h) := by rw [hsum]
    _ = (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ai * (y % 2 ^ (j * h) + 2 ^ (j * h) * bj)) % 2 ^ (L * h) := by
          rw [Nat.mod_add_mod]; congr 1; ring
    _ = _ := by
          subst hbj; rw [← limb_step_prefix y h j]

private theorem mul_row_truncate_mod {L i h ai jMax lb y : ℕ}
    (hi : i < L) (hjMax : jMax = min lb (L - i)) (hle : L ≤ i + jMax) :
    2 ^ (i * h) * ai * (y % 2 ^ (jMax * h)) % 2 ^ (L * h) =
      (2 ^ (i * h) * ai * y - 0) % 2 ^ (L * h) := by
  have hjeq : jMax = L - i := by omega
  have h1 : 2 ^ (L * h) = 2 ^ (i * h) * 2 ^ ((L - i) * h) := by
    rw [← Nat.pow_add, ← Nat.add_mul, Nat.add_sub_cancel' (le_of_lt hi)]
  rw [Nat.sub_zero, hjeq]
  have hsplit := (Nat.mod_add_div y (2 ^ ((L - i) * h))).symm
  calc 2 ^ (i * h) * ai * (y % 2 ^ ((L - i) * h)) % 2 ^ (L * h)
      = (2 ^ (i * h) * ai * (y % 2 ^ ((L - i) * h)) +
          2 ^ (L * h) * (ai * (y / 2 ^ ((L - i) * h)))) % 2 ^ (L * h) := by
          rw [Nat.add_mul_mod_self_left]
    _ = (2 ^ (i * h) * ai * (y % 2 ^ ((L - i) * h) +
          2 ^ ((L - i) * h) * (y / 2 ^ ((L - i) * h)))) % 2 ^ (L * h) := by
          congr 1; rw [h1]; ring
    _ = 2 ^ (i * h) * ai * y % 2 ^ (L * h) := by rw [← hsplit]

/-! ### `mwMul` procedure and contract -/

/-- Multiword multiplication `(x * y) % 2 ^ (L * h)` into `dst`, taking `[a, b, dst, L, 2 ^ h]`.
Expects `base + idxZero` to hold `mwZero`. -/
def mwMul (base : ℕ) : Stmt :=
  .call 5 (base + idxZero) [.reg 2, .reg 3] ;;
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 3)
    (.cond (.load (.bin .add (.reg 0) (.reg 6)))
      (.assign 5 (.bin .add (.reg 6) (.const 1))) .nop) ;;
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 3)
    (.cond (.load (.bin .add (.reg 1) (.reg 7)))
      (.assign 6 (.bin .add (.reg 7) (.const 1))) .nop) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.const 0) ;;
     .assign 9 (.bin .sub (.reg 3) (.reg 7)) ;;
     .cond (.bin .lt (.reg 6) (.reg 9)) (.assign 9 (.reg 6)) .nop ;;
     forRange 10 (.const 0) (.reg 9)
       (.assign 11 (.bin .add (.bin .add
           (.bin .mul (.load (.bin .add (.reg 0) (.reg 7)))
                       (.load (.bin .add (.reg 1) (.reg 10))))
           (.load (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))))
           (.reg 8)) ;;
        .store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))
          (.bin .mod (.reg 11) (.reg 4)) ;;
        .assign 8 (.bin .div (.reg 11) (.reg 4))) ;;
     .cond (.bin .lt (.bin .add (.reg 7) (.reg 9)) (.reg 3))
       (.store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 9))) (.reg 8))
       .nop) ;;
  .ret (.const 0)

theorem mwMul_noRand (base : ℕ) : (mwMul base).NoRand := by
  simp [mwMul, forRange, forUp, Stmt.NoRand]

def mwMulContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, 2 ^ h] ∧ v = 0 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        LimbsAt mem' dst L h ((x * y) % 2 ^ (L * h))) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args mem := match args with
    | [a, b, _, L, _] => 95 * L + 45 * (memActiveLimbs mem a L * memActiveLimbs mem b L) + 50
    | _ => 0

private theorem scan_active_triple {w : ℕ} {p : Program}
    {rPtr rLen rOut rIdx : ℕ}
    (hne1 : rOut ≠ rIdx) (hne2 : rPtr ≠ rOut) (hne3 : rPtr ≠ rIdx)
    (hne4 : rLen ≠ rOut) (hne5 : rLen ≠ rIdx)
    (st₀ : State) (ptr L : ℕ)
    (hw1 : 1 < 2 ^ w) (hL : L < 2 ^ w) (hbound : ptr + L < 2 ^ w)
    (hptr : st₀.regs rPtr = ptr) (hlen : st₀.regs rLen = L) (hout : st₀.regs rOut = 0) :
    Triple w p (fun st => st = st₀)
      (forRange rIdx (.const 0) (.reg rLen)
        (.cond (.load (.bin .add (.reg rPtr) (.reg rIdx)))
          (.assign rOut (.bin .add (.reg rIdx) (.const 1))) .nop))
      (normalPost fun st => st.mem = st₀.mem ∧ st.regs rIdx = L ∧
        st.regs rOut = memActiveLimbs st₀.mem ptr L ∧
        ∀ r, r ≠ rOut → r ≠ rIdx → st.regs r = st₀.regs r)
      (fun _ => (L - 0) * (9 + (Expr.reg rLen).size + 8) + ((Expr.const 0).size + (Expr.reg rLen).size + 5)) := by
  refine Triple.forRange_const (w := w) (p := p) (r := rIdx) (lo := .const 0) (hi := .reg rLen)
    (body :=
      .cond (.load (.bin .add (.reg rPtr) (.reg rIdx)))
        (.assign rOut (.bin .add (.reg rIdx) (.const 1))) .nop)
    (P := fun st => st = st₀)
    (Inv := fun i st => st.mem = st₀.mem ∧ st.regs rIdx = i ∧
      st.regs rOut = memActiveLimbs st₀.mem ptr i ∧
      ∀ r, r ≠ rOut → r ≠ rIdx → st.regs r = st₀.regs r)
    9 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      rw [hst]
      refine ⟨by eval_expr, rfl, by simp, ?_, ?_⟩
      · simp [hne1, hout, memActiveLimbs]
      · intro r hr1 hr2; simp [hr2])
    (fun _ st _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by
      have hl : st.regs rLen = L := by rw [hi.2.2.2 rLen hne4 hne5, hlen]
      eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hmem, hri, hro, hregs⟩
      dsimp only
      have hrp : st.regs rPtr = ptr := by rw [hregs rPtr hne2 hne3, hptr]
      have hload : (Expr.load (.bin .add (.reg rPtr) (.reg rIdx))).eval w st =
          some (st₀.mem (ptr + i)) := by
        rw [← hmem]
        exact Expr.eval_load_of_eq (by eval_expr) rfl
      refine runs_start_le ?_
      refine runs_cond_le hload (fun hne => ?_) (fun heq => ?_)
      · refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨hmem, by simp, ?_, ?_⟩, by simp [hne1.symm, hri]⟩
        · simp [hne1, memActiveLimbs, hne]
        · intro r hr1 hr2
          rw [Function.update_of_ne hr2]
          dsimp only
          rw [Function.update_of_ne hr1]
          exact hregs r hr1 hr2
      · refine runs_nop_le ?_ (by wram_cost)
        refine ⟨⟨hmem, by simp, ?_, ?_⟩, hri⟩
        · rw [Function.update_of_ne hne1]; simp [memActiveLimbs, heq, hro]
        · intro r hr1 hr2
          rw [Function.update_of_ne hr2]
          exact hregs r hr1 hr2)

private theorem mul_inner_triple {w : ℕ} {p : Program}
    {mem : ℕ → ℕ} {a b' dst L h la lb i jMax x y : ℕ}
    (hw1 : 1 < 2 ^ w) (hw2 : 2 * h + 2 ≤ w) (_hB : 2 ^ h < 2 ^ w) (hL : L < 2 ^ w)
    (ha : a + L < 2 ^ w) (hb : b' + L < 2 ^ w) (hdst : dst + L < 2 ^ w)
    (hnova : dst + L ≤ a ∨ a + L ≤ dst) (hnovb : dst + L ≤ b' ∨ b' + L ≤ dst)
    (hx : LimbsAt mem a L h x) (hy : LimbsAt mem b' L h y)
    (hi : i < L) (hjMax_eq : jMax = min lb (L - i)) :
    Triple w p
      (fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
        st.regs 4 = 2 ^ h ∧ st.regs 5 = la ∧ st.regs 6 = lb ∧ st.regs 7 = i ∧
        st.regs 8 = 0 ∧ st.regs 9 = jMax ∧
        (∀ k < L, st.mem (dst + k) < 2 ^ h) ∧
        (∀ q, i + lb ≤ q → q < L → st.mem (dst + q) = 0) ∧
        (∀ p, p < dst ∨ dst + L ≤ p → st.mem p = mem p) ∧
        evalLimbs h (tab L (fun k => st.mem (dst + k))) = (x % 2 ^ (i * h) * y) % 2 ^ (L * h))
      (forRange 10 (.const 0) (.reg 9)
        (.assign 11 (.bin .add (.bin .add
            (.bin .mul (.load (.bin .add (.reg 0) (.reg 7)))
                        (.load (.bin .add (.reg 1) (.reg 10))))
            (.load (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))))
            (.reg 8)) ;;
         .store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))
           (.bin .mod (.reg 11) (.reg 4)) ;;
         .assign 8 (.bin .div (.reg 11) (.reg 4))))
      (normalPost fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
        st.regs 4 = 2 ^ h ∧ st.regs 5 = la ∧ st.regs 6 = lb ∧ st.regs 7 = i ∧
        st.regs 9 = jMax ∧ st.regs 8 < 2 ^ h ∧
        (∀ k < L, st.mem (dst + k) < 2 ^ h) ∧
        (∀ q, i + lb ≤ q → q < L → st.mem (dst + q) = 0) ∧
        (∀ p, p < dst ∨ dst + L ≤ p → st.mem p = mem p) ∧
        (evalLimbs h (tab L (fun k => st.mem (dst + k))) + 2 ^ ((i + jMax) * h) * st.regs 8) % 2 ^ (L * h) =
          (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * (y % 2 ^ (jMax * h))) % 2 ^ (L * h))
      (fun _ => (jMax - 0) * (34 + (Expr.reg 9).size + 8) + ((Expr.const 0).size + (Expr.reg 9).size + 5)) := by
  refine Triple.strengthen_post (Triple.forRange_const (w := w) (p := p) (r := 10) (lo := .const 0) (hi := .reg 9)
    (body :=
      .assign 11 (.bin .add (.bin .add
          (.bin .mul (.load (.bin .add (.reg 0) (.reg 7)))
                      (.load (.bin .add (.reg 1) (.reg 10))))
          (.load (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))))
          (.reg 8)) ;;
       .store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))
         (.bin .mod (.reg 11) (.reg 4)) ;;
       .assign 8 (.bin .div (.reg 11) (.reg 4)))
    (P := fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
      st.regs 4 = 2 ^ h ∧ st.regs 5 = la ∧ st.regs 6 = lb ∧ st.regs 7 = i ∧
      st.regs 8 = 0 ∧ st.regs 9 = jMax ∧
      (∀ k < L, st.mem (dst + k) < 2 ^ h) ∧
      (∀ q, i + lb ≤ q → q < L → st.mem (dst + q) = 0) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → st.mem p = mem p) ∧
      evalLimbs h (tab L (fun k => st.mem (dst + k))) = (x % 2 ^ (i * h) * y) % 2 ^ (L * h))
    (Inv := fun j st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
      st.regs 4 = 2 ^ h ∧ st.regs 5 = la ∧ st.regs 6 = lb ∧ st.regs 7 = i ∧
      st.regs 9 = jMax ∧ st.regs 10 = j ∧ st.regs 8 < 2 ^ h ∧
      (∀ k < L, st.mem (dst + k) < 2 ^ h) ∧
      (∀ q, i + lb ≤ q → q < L → st.mem (dst + q) = 0) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → st.mem p = mem p) ∧
      (evalLimbs h (tab L (fun k => st.mem (dst + k))) + 2 ^ ((i + j) * h) * st.regs 8) % 2 ^ (L * h) =
        (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * (y % 2 ^ (j * h))) % 2 ^ (L * h))
    34 0 jMax (Nat.zero_le jMax) hw1 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hlim_lt, hzero_q, hframe, heval⟩ => by
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, hlim_lt, hzero_q, hframe, ?_⟩
      all_goals try (simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; done)
      · simp [h8, heval, Nat.mod_one])
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by have h9 := hi'.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt => by
      intro st _ ⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, hc_lt, hlim_lt, hzero_q, hframe, heval⟩
      dsimp only
      have hijL : i + j < L := by omega
      have ha_m : st.mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (a + i) (by omega)]; exact hx.getElem hi
      have hb_m : st.mem (b' + j) = (y / 2 ^ (j * h)) % 2 ^ h := by
        rw [hframe (b' + j) (by omega)]; exact hy.getElem (by omega)
      have hai_lt : (x / 2 ^ (i * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hbj_lt : (y / 2 ^ (j * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hdij_lt : st.mem (dst + (i + j)) < 2 ^ h := hlim_lt (i + j) hijL
      set ai := (x / 2 ^ (i * h)) % 2 ^ h
      set bj := (y / 2 ^ (j * h)) % 2 ^ h
      set dij := st.mem (dst + (i + j))
      set pval := ai * bj + dij + st.regs 8
      have hp_lt := mul_limb_acc_lt hai_lt hbj_lt hdij_lt hc_lt hw2
      have hp_w : pval < 2 ^ w := hp_lt.2
      have hmul_w : ai * bj < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)) hp_w
      have hmul_add_w : ai * bj + dij < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hp_w
      have hsum_eval : (Expr.bin .add (.bin .add
            (.bin .mul (.load (.bin .add (.reg 0) (.reg 7)))
                        (.load (.bin .add (.reg 1) (.reg 10))))
            (.load (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))))
            (.reg 8)).eval w st = some pval := by
        refine Expr.eval_add (Expr.eval_add
          (Expr.eval_mul (Expr.eval_load_of_eq (by eval_expr) ha_m)
            (Expr.eval_load_of_eq (by eval_expr) hb_m) hmul_w)
          (Expr.eval_load_of_eq (by eval_expr) rfl) hmul_add_w)
          (by eval_expr) hp_w
      have hmod_lt : pval % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hdiv_lt : pval / 2 ^ h < 2 ^ h := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show h + h = 2 * h by ring]
        exact hp_lt.1
      have hupd_sum := evalLimbs_tab_update_mem h L (i + j) (pval % 2 ^ h) st.mem dst hijL
      have hstep_sum := mul_inner_step_eq (L := L) (i := i) (j := j) (h := h)
        (ai := ai) (bj := bj) (dij := dij) (carry := st.regs 8)
        (mem_sum := evalLimbs h (tab L (fun k => st.mem (dst + k))))
        (mem'_sum := evalLimbs h (tab L (fun k => Function.update st.mem (dst + (i + j)) (pval % 2 ^ h) (dst + k))))
        (x := x) (y := y) rfl heval hupd_sum
      refine runs_start_le ?_
      refine runs_seq_assign_le hsum_eval ?_
      refine runs_seq_store_le (by eval_expr)
        (Expr.eval_mod (by eval_expr) (by eval_expr) hp_w) ?_
      refine runs_assign_le (Expr.eval_div (by eval_expr) (by eval_expr) hp_w) ?_
        (by wram_cost)
      refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp; exact hdiv_lt
      · intro k hk
        dsimp only
        by_cases hkeq : k = i + j
        · subst hkeq; rw [Function.update_self]; exact hmod_lt
        · rw [Function.update_of_ne (by omega)]; exact hlim_lt k hk
      · intro q hq1 hq2
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hzero_q q hq1 hq2
      · intro r hr
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hframe r hr
      · dsimp only
        rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 10), Function.update_self]
        exact hstep_sum
      · simp [h10]))
    fun o st hq => by
      cases o with
      | returned _ => exact False.elim hq
      | normal =>
        rcases hq with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, _, hc_lt, hlim_lt, hzero_q, hframe, heval⟩
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, hc_lt, hlim_lt, hzero_q, hframe, heval⟩

theorem mwMul_meetsContract {w : ℕ} {p : Program} {f base : ℕ}
    (hZero : MeetsContract w p (base + idxZero) (mwZeroContract w))
    (hMulProc : p.procs[f]? = some (mwMul base)) :
    MeetsContract w p f (mwMulContract w) := by
  refine meetsContract_of_runs hMulProc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have ha_w : a < 2 ^ w := hwords a (by simp)
  have hb_w : b' < 2 ^ w := hwords b' (by simp)
  have hdst_w : dst < 2 ^ w := hwords dst (by simp)
  have hL_w : L < 2 ^ w := hwords L (by simp)
  set la := memActiveLimbs mem a L
  set lb := memActiveLimbs mem b' L
  have hla_le : la ≤ L := memActiveLimbs_le mem a L
  have hlb_le : lb ≤ L := memActiveLimbs_le mem b' L
  have hla_eq : la = activeLimbs x L h := memActiveLimbs_eq_activeLimbs hx
  have hlb_eq : lb = activeLimbs y L h := memActiveLimbs_eq_activeLimbs hy
  have hx_lt_la : x < 2 ^ (la * h) := hla_eq ▸ lt_two_pow_activeLimbs hx.lt_pow
  have hy_lt_lb : y < 2 ^ (lb * h) := hlb_eq ▸ lt_two_pow_activeLimbs hy.lt_pow
  refine runs_start_le ?_
  dsimp only [mwMul]
  refine runs_seq_call_le hZero (by eval_expr) (by wram_words) ⟨dst, L, rfl, hw1, hdst⟩ ?_
  rintro _ mem₁ pos₁ ⟨dst', L', heq1, _, hlist1, hframe1⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨rfl, rfl⟩
  have ha_m1 : ∀ j < L, mem₁ (a + j) = mem (a + j) := fun j hj => hframe1 (a + j) (by omega)
  have hb_m1 : ∀ j < L, mem₁ (b' + j) = mem (b' + j) := fun j hj => hframe1 (b' + j) (by omega)
  have hla_m1 : memActiveLimbs mem₁ a L = la := memActiveLimbs_eq_of_lt ha_m1
  have hlb_m1 : memActiveLimbs mem₁ b' L = lb := memActiveLimbs_eq_of_lt hb_m1
  have hzero_limbs : ∀ q < L, mem₁ (dst + q) = 0 := by
    intro q hq
    have hx0 := (limbsAt_zero_iff (h := h)).mpr hlist1
    simpa using hx0.getElem hq
  wram_step
  · refine runs_seq_triple_le
      (scan_active_triple (w := w) (p := p)
        (by decide : (5 : ℕ) ≠ 6) (by decide) (by decide) (by decide) (by decide)
        _ a L hw1 hL_w ha ?_ ?_ ?_) rfl ?_
    · simp [Function.update, startState]
    · simp [Function.update, startState]
    · simp [Function.update]
    rintro st₂ ⟨hmem2, _, hla_r, hregs2⟩
    have ha_r2 : st₂.regs 0 = a := by rw [hregs2 0 (by decide) (by decide)]; simp [Function.update, startState]
    have hb_r2 : st₂.regs 1 = b' := by rw [hregs2 1 (by decide) (by decide)]; simp [Function.update, startState]
    have hdst_r2 : st₂.regs 2 = dst := by rw [hregs2 2 (by decide) (by decide)]; simp [Function.update, startState]
    have hL_r2 : st₂.regs 3 = L := by rw [hregs2 3 (by decide) (by decide)]; simp [Function.update, startState]
    have hB_r2 : st₂.regs 4 = 2 ^ h := by rw [hregs2 4 (by decide) (by decide)]; simp [Function.update, startState]
    rw [hla_m1] at hla_r
    wram_step
    · refine runs_seq_triple_le
        (scan_active_triple (w := w) (p := p)
          (by decide : (6 : ℕ) ≠ 7) (by decide) (by decide) (by decide) (by decide)
          _ b' L hw1 hL_w hb ?_ ?_ ?_) rfl ?_
      · simp [Function.update, hb_r2]
      · simp [Function.update, hL_r2]
      · simp [Function.update]
      rintro st₃ ⟨hmem3, _, hlb_r, hregs3⟩
      have ha_r3 : st₃.regs 0 = a := by rw [hregs3 0 (by decide) (by decide)]; simp [Function.update, ha_r2]
      have hb_r3 : st₃.regs 1 = b' := by rw [hregs3 1 (by decide) (by decide)]; simp [Function.update, hb_r2]
      have hdst_r3 : st₃.regs 2 = dst := by rw [hregs3 2 (by decide) (by decide)]; simp [Function.update, hdst_r2]
      have hL_r3 : st₃.regs 3 = L := by rw [hregs3 3 (by decide) (by decide)]; simp [Function.update, hL_r2]
      have hB_r3 : st₃.regs 4 = 2 ^ h := by rw [hregs3 4 (by decide) (by decide)]; simp [Function.update, hB_r2]
      have hla_r3 : st₃.regs 5 = la := by rw [hregs3 5 (by decide) (by decide)]; simp [Function.update, hla_r]
      rw [hmem2, hlb_m1] at hlb_r
      have hmem3' : st₃.mem = mem₁ := hmem3.trans hmem2
      have houter := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
        (body :=
          .assign 8 (.const 0) ;;
          .assign 9 (.bin .sub (.reg 3) (.reg 7)) ;;
          .cond (.bin .lt (.reg 6) (.reg 9)) (.assign 9 (.reg 6)) .nop ;;
          forRange 10 (.const 0) (.reg 9)
            (.assign 11 (.bin .add (.bin .add
                (.bin .mul (.load (.bin .add (.reg 0) (.reg 7)))
                            (.load (.bin .add (.reg 1) (.reg 10))))
                (.load (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))))
                (.reg 8)) ;;
             .store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 10)))
               (.bin .mod (.reg 11) (.reg 4)) ;;
             .assign 8 (.bin .div (.reg 11) (.reg 4))) ;;
          .cond (.bin .lt (.bin .add (.reg 7) (.reg 9)) (.reg 3))
            (.store (.bin .add (.reg 2) (.bin .add (.reg 7) (.reg 9))) (.reg 8))
            .nop)
        (P := fun st => st = st₃)
        (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧
          st.regs 3 = L ∧ st.regs 4 = 2 ^ h ∧ st.regs 5 = la ∧ st.regs 6 = lb ∧
          st.regs 7 = i ∧
          (∀ k < L, st.mem (dst + k) < 2 ^ h) ∧
          (∀ q, i + lb ≤ q → q < L → st.mem (dst + q) = 0) ∧
          (∀ p, p < dst ∨ dst + L ≤ p → st.mem p = mem p) ∧
          evalLimbs h (tab L (fun k => st.mem (dst + k))) = (x % 2 ^ (i * h) * y) % 2 ^ (L * h))
        (43 * lb + 36) 0 la (Nat.zero_le la) hw1 (fun _ => by omega)
        (fun st hst => by
          rw [hst]
          refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals try (simp [ha_r3, hb_r3, hdst_r3, hL_r3, hB_r3, hla_r3, hlb_r]; done)
          · intro k hk; rw [hmem3', hzero_limbs k hk]; exact Nat.two_pow_pos _
          · intro q _ hqL; rw [hmem3', hzero_limbs q hqL]
          · intro p hp; rw [hmem3']; exact hframe1 p hp
          · simp only [Nat.zero_mul, pow_zero, Nat.mod_one, Nat.zero_mul, Nat.zero_mod]
            exact evalLimbs_tab_eq_zero h L _ (fun k hk => by rw [hmem3', hzero_limbs k hk]))
        (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.1)
        (fun _ st _ _ hi' => by have h5 := hi'.2.2.2.2.2.1; eval_expr)
        (fun i _ hilt => by
          intro st _ ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlim_lt, hzero_q, hframe, heval⟩
          have hiL : i < L := by omega
          set jMax := min lb (L - i)
          have hinner := mul_inner_triple (w := w) (p := p) (mem := mem)
            (a := a) (b' := b') (dst := dst) (L := L) (h := h) (la := la) (lb := lb)
            (i := i) (jMax := jMax) (x := x) (y := y)
            hw1 hw2 hB hL_w ha hb hdst hnova hnovb hx hy hiL rfl
          refine runs_start_le ?_
          refine runs_seq_assign_le (by eval_expr) ?_
          refine runs_seq_assign_le (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) ?_
          refine runs_seq_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1)
            (fun hne => ?_) (fun heq => ?_)
          · have hlt_j : lb < L - i := by by_contra hnot; simp [hnot] at hne
            have hjMax : lb = jMax := by omega
            refine runs_seq_assign_le (by eval_expr) ?_
            refine runs_seq_triple_le hinner
              ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
                by simp [h5], by simp [h6], by simp [h7], by simp, by simp [hjMax],
                hlim_lt, hzero_q, hframe, heval⟩ ?_
            rintro st₄ ⟨h0', h1', h2', h3', h4', h5', h6', h7', h9', hc_lt, hlim_lt', hzero_q', hframe', heval'⟩
            have hilbL : i + jMax < L := by omega
            have hj_eq : jMax = lb := by omega
            have hadd_eval : (Expr.bin .add (.reg 7) (.reg 9)).eval w st₄ = some (i + jMax) := by
              eval_expr
            refine runs_cond_le (Expr.eval_lt_op hadd_eval (by eval_expr) hw1)
              (fun hne2 => ?_) (fun heq2 => by exfalso; simp [hilbL] at heq2)
            refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost)
            have hy_mod : y % 2 ^ (jMax * h) = y := by
              rw [hj_eq]; exact Nat.mod_eq_of_lt hy_lt_lb
            have hupd := evalLimbs_tab_update_mem h L (i + jMax) (st₄.regs 8) st₄.mem dst hilbL
            have hzero_old : st₄.mem (dst + (i + jMax)) = 0 := by
              rw [hj_eq]; exact hzero_q' (i + lb) le_rfl (by omega)
            rw [hzero_old, Nat.mul_zero, Nat.add_zero] at hupd
            have hlt_pow : evalLimbs h (tab L (fun k => Function.update st₄.mem (dst + (i + jMax)) (st₄.regs 8) (dst + k))) <
                2 ^ (L * h) := by
              have hlen_tab : (tab L (fun k => Function.update st₄.mem (dst + (i + jMax)) (st₄.regs 8) (dst + k))).length = L := by
                simp [tab]
              conv_rhs => rw [← hlen_tab]
              refine evalLimbs_lt ?_
              intro d hd
              simp only [tab, List.mem_map, List.mem_range] at hd
              rcases hd with ⟨k, hk, rfl⟩
              by_cases hkeq : k = i + jMax
              · subst hkeq; rw [Function.update_self]; exact hc_lt
              · rw [Function.update_of_ne (by omega)]; exact hlim_lt' k hk
            refine ⟨⟨h0', h1', h2', h3', h4', h5', h6', by simp, ?_, ?_, ?_, ?_⟩, h7'⟩
            · intro k hk
              dsimp only
              by_cases hkeq : k = i + jMax
              · subst hkeq; rw [Function.update_self]; exact hc_lt
              · rw [Function.update_of_ne (by omega)]; exact hlim_lt' k hk
            · intro q hq1 hq2
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hzero_q' q (by omega) hq2
            · intro r hr
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hframe' r hr
            · dsimp only
              rw [← Nat.mod_eq_of_lt hlt_pow, hupd, heval', hy_mod, limb_step_prefix x h i]
              congr 1; ring
          · have hle_j : L - i ≤ lb := by
              by_contra hnot
              have : lb < L - i := Nat.not_le.mp hnot
              simp [this] at heq
            have hjMax : L - i = jMax := by omega
            refine runs_seq_nop_le ?_
            refine runs_seq_triple_le hinner
              ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
                by simp [h5], by simp [h6], by simp [h7], by simp, by simp [hjMax],
                hlim_lt, hzero_q, hframe, heval⟩ ?_
            rintro st₄ ⟨h0', h1', h2', h3', h4', h5', h6', h7', h9', hc_lt, hlim_lt', hzero_q', hframe', heval'⟩
            have hgeL : L ≤ i + jMax := by omega
            have hnot_lt : ¬ i + jMax < L := by omega
            have hadd_eval : (Expr.bin .add (.reg 7) (.reg 9)).eval w st₄ = some (i + jMax) := by
              eval_expr
            refine runs_cond_le (Expr.eval_lt_op hadd_eval (by eval_expr) hw1)
              (fun hne2 => by exfalso; simp [hnot_lt] at hne2) (fun _ => ?_)
            refine runs_nop_le ?_ (by wram_cost)
            have hlt_pow : evalLimbs h (tab L (fun k => st₄.mem (dst + k))) < 2 ^ (L * h) := by
              have hlen_tab : (tab L (fun k => st₄.mem (dst + k))).length = L := by simp [tab]
              conv_rhs => rw [← hlen_tab]
              refine evalLimbs_lt ?_
              intro d hd
              simp only [tab, List.mem_map, List.mem_range] at hd
              rcases hd with ⟨k, hk, rfl⟩
              exact hlim_lt' k hk
            have hij_eq : i + jMax = L := by omega
            have htrunc := mul_row_truncate_mod (h := h) (lb := lb) (y := y) hiL
              (ai := (x / 2 ^ (i * h)) % 2 ^ h) rfl hgeL
            rw [Nat.sub_zero] at htrunc
            refine ⟨⟨h0', h1', h2', h3', h4', h5', h6', by simp, hlim_lt', ?_, hframe', ?_⟩, h7'⟩
            · intro q hq1 hq2; exfalso; omega
            · dsimp only
              rw [← Nat.mod_eq_of_lt hlt_pow]
              have hmod0 : (evalLimbs h (tab L (fun k => st₄.mem (dst + k))) +
                  2 ^ ((i + jMax) * h) * st₄.regs 8) % 2 ^ (L * h) =
                  evalLimbs h (tab L (fun k => st₄.mem (dst + k))) % 2 ^ (L * h) := by
                rw [hij_eq, Nat.add_mul_mod_self_left]
              rw [← hmod0, heval']
              calc (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * (y % 2 ^ (jMax * h))) % 2 ^ (L * h)
                  = (x % 2 ^ (i * h) * y % 2 ^ (L * h) +
                      2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * (y % 2 ^ (jMax * h)) % 2 ^ (L * h)) % 2 ^ (L * h) := by
                      rw [Nat.add_mod]
                _ = (x % 2 ^ (i * h) * y % 2 ^ (L * h) +
                      2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * y % 2 ^ (L * h)) % 2 ^ (L * h) := by
                      rw [htrunc]
                _ = (x % 2 ^ (i * h) * y + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) * y) % 2 ^ (L * h) := by
                      rw [← Nat.add_mod]
                _ = x % 2 ^ ((i + 1) * h) * y % 2 ^ (L * h) := by
                      rw [limb_step_prefix x h i]; congr 1; ring)
      refine runs_seq_triple_le houter rfl ?_
      rintro st₄ ⟨_, _, _, _, _, _, _, _, hlim_lt, _, hframe, heval⟩
      have hx_mod : x % 2 ^ (la * h) = x := Nat.mod_eq_of_lt hx_lt_la
      rw [hx_mod] at heval
      have hlimbs : LimbsAt st₄.mem dst L h (evalLimbs h (tab L (fun k => st₄.mem (dst + k)))) := by
        refine limbsAt_of_list ?_ (by simp [tab]) ?_
        · intro k hk
          simp only [tab, List.length_map, List.length_range] at hk
          simp [tab]
        · intro d hd
          simp only [tab, List.mem_map, List.mem_range] at hd
          rcases hd with ⟨k, hk, rfl⟩
          exact hlim_lt k hk
      rw [heval] at hlimbs
      refine runs_ret_le (by eval_expr)
        ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
          obtain rfl : x' = x := hx'.ext hx
          obtain rfl : y' = y := hy'.ext hy
          exact hlimbs, hframe⟩ ?_
      dsimp only [mwMulContract, mwZeroContract, argsSize, Expr.size, Expr.size_const, Expr.size_reg,
        Nat.sub_zero]
      have hmul_eq : la * (43 * lb + 36 + 1 + 8) = 43 * (la * lb) + 45 * la := by ring
      have huv : la * lb = memActiveLimbs mem a L * memActiveLimbs mem b' L := rfl
      rw [hmul_eq]
      omega

end MinCostFlow.WideWord
