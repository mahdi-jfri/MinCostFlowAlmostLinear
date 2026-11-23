module

public import WordRAM.Logic
public import WordRAM.Tactic
public import WordRAM.Layout
public import MinCostFlow.Machine.WideWord.ArithMul
public import MinCostFlow.Machine.WideWord.ArithShift

/-!
# Multiword bit-length, division/remainder, and the full arithmetic module

This file defines and verifies:
* `mwBitLen`: host-word bit length in `O(bitLen v + 1)` time via recursion (`meetsContract_of_rec`),
* `mwDivMod`: multiword Euclidean division and remainder `(x / y, x % y)` (with `x / 0 = 0`,
  `x % 0 = x`) in `O(L * (bitLen x + 1))` time,
* `arithModule b`: the 18-procedure arithmetic library containing all basic, multiplication,
  division/remainder, and shift procedures with fixed offsets `0 .. 17`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Additional procedure indices inside `arithModule b` -/

def idxBitLen : ℕ := 13
def idxMul : ℕ := 14
def idxDivMod : ℕ := 15
def idxShiftLeft : ℕ := 16
def idxShiftRight : ℕ := 17

/-! ### Recursive `mwBitLen` procedure and contract -/

/-- Computes `bitLen v` (`reg 0`) in `O(bitLen v + 1)` time using recursive call to `selfIdx`. -/
def mwBitLen (selfIdx : ℕ) : Stmt :=
  .cond (.reg 0)
    (.call 1 selfIdx [.bin .shiftRight (.reg 0) (.const 1)] ;;
     .ret (.bin .add (.reg 1) (.const 1)))
    (.ret (.const 0))

theorem mwBitLen_noRand (selfIdx : ℕ) : (mwBitLen selfIdx).NoRand := by
  simp [mwBitLen, Stmt.NoRand]

def mwBitLenContract (w : ℕ) : Contract where
  pre args _ := ∃ v, args = [v] ∧ 1 < 2 ^ w ∧ v < 2 ^ w ∧ bitLen v < 2 ^ w
  post args mem v mem' :=
    ∃ x, args = [x] ∧ mem' = mem ∧ v = bitLen x
  cost args _ := match args with | [v] => 11 * bitLen v + 4 | _ => 0

theorem bitLen_pos_div {v : ℕ} (hv : 0 < v) : bitLen v = bitLen (v / 2) + 1 := by
  by_cases hv1 : v = 1
  · subst hv1; simp [bitLen]
  · have hv2 : 2 ≤ v := by omega
    have hdiv_pos : 0 < v / 2 := Nat.div_pos hv2 (by norm_num)
    simp only [bitLen, Nat.ne_of_gt hv, Nat.ne_of_gt hdiv_pos, ↓reduceIte]
    rw [Nat.log_of_one_lt_of_le (by norm_num) hv2]

theorem mwBitLen_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hProc : p.procs[f]? = some (mwBitLen f)) :
    MeetsContract w p f (mwBitLenContract w) := by
  refine meetsContract_of_rec (fun args _ => args.headD 0) hProc ?_
  intro n ih args mem pos ω hwords hpre hmeas
  rcases hpre with ⟨v, rfl, hw1, hv, hbl⟩
  dsimp only [List.headD] at hmeas
  subst hmeas
  refine runs_start_le ?_
  dsimp only [mwBitLen]
  wram_step
  · have hv_pos : 0 < v := Nat.pos_of_ne_zero hcond
    have hbl_eq : bitLen v = bitLen (v / 2) + 1 := bitLen_pos_div hv_pos
    have hdiv_lt : v / 2 < v := Nat.div_lt_self hv_pos (by norm_num)
    have hdiv_w : v / 2 < 2 ^ w := lt_trans hdiv_lt hv
    have hbl_div_w : bitLen (v / 2) < 2 ^ w := by omega
    have hshr_eval : (Expr.bin .shiftRight (.reg 0) (.const 1)).eval w (startState [v] mem pos) =
        some (v / 2) := by
      simpa [Nat.shiftRight_eq_div_pow] using
        Expr.eval_shiftRight (w := w) (st := startState [v] mem pos) (a := .reg 0) (b := .const 1)
          (by eval_expr) (by eval_expr) hv
    refine runs_seq_call_le (f := f) ih (by exact evalArgs_cons hshr_eval (evalArgs_nil w _))
      (by wram_words) ⟨⟨v / 2, rfl, hw1, hdiv_w, hbl_div_w⟩, by simpa using hdiv_lt⟩ ?_
    rintro v₁ mem₁ pos₁ ⟨x', heq1, hmem1, rfl⟩
    simp only [List.cons.injEq, and_true] at heq1
    subst heq1
    refine runs_ret_le (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
      ⟨v, rfl, hmem1, by simp [Outcome.value, hbl_eq]⟩ ?_
    dsimp only [Contract.below, mwBitLenContract]
    rw [hbl_eq]
    wram_cost
  · have hv0 : v = 0 := hcond
    subst hv0
    refine runs_ret_le (by eval_expr) ⟨0, rfl, rfl, by simp [Outcome.value, bitLen]⟩ ?_
    dsimp only [Contract.below, mwBitLenContract]
    wram_cost

/-! ### Arithmetic helpers for `mwDivMod` -/

private theorem divMod_limb_bit {x h j b : ℕ} (hb : b < h) :
    (((x / 2 ^ (j * h)) % 2 ^ h) >>> b) &&& 1 = (x / 2 ^ (j * h + b)) % 2 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hh : 2 ^ h = 2 ^ b * (2 * 2 ^ (h - 1 - b)) := by
    calc 2 ^ h = 2 ^ (b + (1 + (h - 1 - b))) := by congr 1; omega
      _ = 2 ^ b * (2 ^ 1 * 2 ^ (h - 1 - b)) := by rw [Nat.pow_add, Nat.pow_add]
      _ = 2 ^ b * (2 * 2 ^ (h - 1 - b)) := by simp
  rw [hh, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem divMod_rem_sub {r y bit L h z borrow : ℕ}
    (hr : r < y) (hy : y < 2 ^ (L * h)) (hbit : bit ≤ 1) (hb : borrow ≤ 1)
    (hz : z < 2 ^ (L * h))
    (heq : z + y = (2 * r + bit) % 2 ^ (L * h) + borrow * 2 ^ (L * h))
    (hge : (2 * r + bit) / 2 ^ (L * h) ≠ 0 ∨ y ≤ (2 * r + bit) % 2 ^ (L * h)) :
    z = 2 * r + bit - y ∧ z < y ∧ y ≤ 2 * r + bit := by
  set nval := 2 * r + bit
  have hn_lt : nval < 2 * 2 ^ (L * h) := by omega
  have hc_le : nval / 2 ^ (L * h) ≤ 1 :=
    Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))
  have hn_split : nval % 2 ^ (L * h) + (nval / 2 ^ (L * h)) * 2 ^ (L * h) = nval := by
    rw [Nat.mul_comm (nval / 2 ^ (L * h))]
    exact Nat.mod_add_div nval (2 ^ (L * h))
  rcases hge with hc_ne | hy_le
  · have hc1 : nval / 2 ^ (L * h) = 1 := Nat.le_antisymm hc_le (Nat.pos_of_ne_zero hc_ne)
    rw [hc1, Nat.one_mul] at hn_split
    have hborrow1 : borrow = 1 := by
      by_contra hnb
      have hb0 : borrow = 0 := by omega
      rw [hb0, Nat.zero_mul, Nat.add_zero] at heq
      omega
    rw [hborrow1, Nat.one_mul] at heq
    have hsub : z = nval - y := by omega
    refine ⟨hsub, by omega, by omega⟩
  · have hc0 : nval / 2 ^ (L * h) = 0 := by
      by_contra hne
      have hc1 : nval / 2 ^ (L * h) = 1 := Nat.le_antisymm hc_le (Nat.pos_of_ne_zero hne)
      rw [hc1, Nat.one_mul] at hn_split
      omega
    have hn_eq : nval % 2 ^ (L * h) = nval := by
      rw [hc0, Nat.zero_mul, Nat.add_zero] at hn_split; exact hn_split
    have hborrow0 : borrow = 0 := by
      by_contra hnb
      have hb1 : borrow = 1 := by omega
      rw [hb1, Nat.one_mul] at heq
      omega
    rw [hborrow0, Nat.zero_mul, Nat.add_zero, hn_eq] at heq
    refine ⟨by omega, by omega, by omega⟩

private theorem divMod_euclid_step {x_s q_s y r bit : ℕ}
    (hx_s : x_s = q_s * y + r) :
    (2 * x_s + bit = (2 * q_s + if y ≤ 2 * r + bit then 1 else 0) * y +
      if y ≤ 2 * r + bit then 2 * r + bit - y else 2 * r + bit) := by
  set P := q_s * y
  have h1 : 2 * q_s * y = 2 * P := by ring
  have h2 : (2 * q_s + 1) * y = 2 * P + y := by dsimp only [P]; ring
  split_ifs with h
  · rw [h2]; omega
  · rw [show (2 * q_s + 0) * y = 2 * P by dsimp only [P]; ring]; omega

private theorem dm_evalLimbs_tab_zero (h L : ℕ) (f : ℕ → ℕ) (hf : ∀ k < L, f k = 0) :
    evalLimbs h (tab L f) = 0 := by
  induction L with
  | zero => simp [tab, evalLimbs]
  | succ L ih =>
    have htab : tab (L + 1) f = tab L f ++ [f L] := by simp [tab, List.range_succ]
    rw [htab, evalLimbs_append, ih (fun k hk => hf k (by omega)), hf L (by omega)]
    simp [evalLimbs]

private theorem divMod_q_dvd {L h : ℕ} (m : ℕ → ℕ) (limbIdx k : ℕ)
    (hk : k ≤ h)
    (hlow : ∀ j < limbIdx, m j = 0)
    (hdvd : 2 ^ k ∣ m limbIdx) :
    2 ^ (limbIdx * h + k) ∣ evalLimbs h (tab L m) := by
  induction L with
  | zero => simp [tab, evalLimbs]
  | succ L ih =>
    have htab : tab (L + 1) m = tab L m ++ [m L] := by simp [tab, List.range_succ]
    have hlen : (tab L m).length = L := by simp [tab]
    have heval1 : evalLimbs h [m L] = m L := by simp [evalLimbs]
    rw [htab, evalLimbs_append, hlen, heval1]
    by_cases hlt : L < limbIdx
    · have h0 : evalLimbs h (tab L m) = 0 := dm_evalLimbs_tab_zero h L m (fun j hj => hlow j (by omega))
      rw [h0, hlow L hlt, Nat.mul_zero, Nat.add_zero]
      exact dvd_zero _
    · by_cases heq : L = limbIdx
      · subst heq
        have h0 : evalLimbs h (tab L m) = 0 := dm_evalLimbs_tab_zero h L m hlow
        rw [h0, Nat.zero_add, Nat.pow_add]
        exact mul_dvd_mul_left _ hdvd
      · have hgt : limbIdx + 1 ≤ L := by omega
        refine dvd_add ih ?_
        have hexp : limbIdx * h + k ≤ L * h := by
          calc limbIdx * h + k ≤ limbIdx * h + h := Nat.add_le_add_left hk _
            _ = (limbIdx + 1) * h := by ring
            _ ≤ L * h := Nat.mul_le_mul_right h hgt
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hexp) _

private theorem divMod_pow_add_lt {m d h : ℕ} (hd : d < h) (hlt : m < 2 ^ h) (hdvd : 2 ^ (d + 1) ∣ m) :
    m + 2 ^ d < 2 ^ h ∧ 2 ^ d ∣ (m + 2 ^ d) := by
  rcases hdvd with ⟨k, rfl⟩
  have h2d1_pos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos _
  have hdvd_h : 2 ^ (d + 1) ∣ 2 ^ h := Nat.pow_dvd_pow 2 hd
  rcases hdvd_h with ⟨q, hq⟩
  have hkq : k < q := by
    by_contra hle
    have hqk : q ≤ k := Nat.not_lt.mp hle
    have h1 : 2 ^ h ≤ 2 ^ (d + 1) * k := by rw [hq]; exact Nat.mul_le_mul_left _ hqk
    omega
  have hk1 : k + 1 ≤ q := hkq
  have hlt1 : 2 ^ (d + 1) * k + 2 ^ d < 2 ^ (d + 1) * (k + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ]; omega
  have hle2 : 2 ^ (d + 1) * (k + 1) ≤ 2 ^ h := by
    rw [hq]; exact Nat.mul_le_mul_left _ hk1
  refine ⟨lt_of_lt_of_le hlt1 hle2, ?_⟩
  rw [Nat.pow_succ, Nat.mul_assoc]
  exact dvd_add (dvd_mul_right _ _) (dvd_refl _)

private theorem rangeCost_divMod (k h M C la : ℕ) (hla : 1 ≤ la) :
    rangeCost (fun cnt => (if cnt = 0 then k else h) * M + C) 0 la =
      (k + (la - 1) * h) * M + la * C := by
  rw [rangeCost_zero_eq_range]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hla)
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
  simp only [↓reduceIte]
  have htail : (List.map (fun cnt => (if cnt = 0 then k else h) * M + C)
      (List.map Nat.succ (List.range m))).sum = m * (h * M + C) := by
    rw [List.map_map]
    simp only [Function.comp_def, Nat.succ_ne_zero, ↓reduceIte, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul]
  rw [htail, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring

private theorem dm_tab_update_mem (h L idx new : ℕ) (m : ℕ → ℕ) (dst : ℕ) (hidx : idx < L) :
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

private theorem divMod_q_div_step {q s : ℕ} (hdvd : 2 ^ (s + 1) ∣ q) :
    (q + 2 ^ s) / 2 ^ s = 2 * (q / 2 ^ (s + 1)) + 1 ∧
      q / 2 ^ s = 2 * (q / 2 ^ (s + 1)) := by
  rcases hdvd with ⟨k, rfl⟩
  have hs_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hs1_pos : 0 < 2 ^ (s + 1) := Nat.two_pow_pos (s + 1)
  have h1 : 2 ^ (s + 1) * k / 2 ^ (s + 1) = k := Nat.mul_div_right k hs1_pos
  have h2 : 2 ^ (s + 1) * k = 2 ^ s * (2 * k) := by rw [Nat.pow_succ]; ring
  have h3 : 2 ^ (s + 1) * k + 2 ^ s = 2 ^ s * (2 * k + 1) := by rw [Nat.pow_succ]; ring
  rw [h1, h3, h2, Nat.mul_div_right _ hs_pos, Nat.mul_div_right _ hs_pos]
  exact ⟨rfl, rfl⟩

/-- Exact bit length of the `L`-limb `h`-bit word at `mem[ptr .. ptr + L - 1]`. -/
def memBitLen (mem : ℕ → ℕ) (ptr L h : ℕ) : ℕ :=
  let la := memActiveLimbs mem ptr L
  if la = 0 then 0 else (la - 1) * h + bitLen (mem (ptr + (la - 1)))

theorem memBitLen_eq_bitLen {mem : ℕ → ℕ} {ptr L h x : ℕ} (hx : LimbsAt mem ptr L h x) :
    memBitLen mem ptr L h = bitLen x := by
  dsimp only [memBitLen]
  rw [memActiveLimbs_eq_activeLimbs hx]
  by_cases h0 : activeLimbs x L h = 0
  · have hx0 : x = 0 := (activeLimbs_eq_zero_iff hx.lt_pow).mp h0
    simp only [h0, ↓reduceIte]
    rw [hx0, bitLen_zero]
  · have hpos : 0 < activeLimbs x L h := Nat.pos_of_ne_zero h0
    have hact_le := activeLimbs_le x L h
    simp only [h0, ↓reduceIte]
    rw [hx.getElem (by omega), ← bitLen_eq_activeLimbs_mul_add hx.lt_pow hpos]

/-! ### `mwDivMod` procedure and contract -/

def divModInnerBody (base : ℕ) : Stmt :=
  .assign 13 (.bin .sub (.bin .sub (.reg 11) (.const 1)) (.reg 12)) ;;
  .assign 14 (.bin .and (.bin .shiftRight
      (.load (.bin .add (.reg 0) (.reg 10))) (.reg 13)) (.const 1)) ;;
  .call 14 (base + idxShl1AddBit) [.reg 3, .reg 14, .reg 4, .reg 6] ;;
  .cond (.reg 14) (.assign 15 (.const 0)) (.call 15 (base + idxLt) [.reg 3, .reg 1, .reg 4]) ;;
  .cond (.reg 15) .nop
    (.call 14 (base + idxRawSub) [.reg 3, .reg 1, .reg 3, .reg 4, .reg 6] ;;
     .store (.bin .add (.reg 2) (.reg 10))
       (.bin .add (.load (.bin .add (.reg 2) (.reg 10))) (.bin .shiftLeft (.const 1) (.reg 13))))

/-- Multiword Euclidean division and remainder `(x / y, x % y)` into `(qDst, rDst)` (with
`x / 0 = 0`, `x % 0 = x`), taking `[a, b, qDst, rDst, L, h, 2 ^ h]`. -/
def mwDivMod (base : ℕ) : Stmt :=
  .call 7 (base + idxZero) [.reg 2, .reg 4] ;;
  .call 7 (base + idxZero) [.reg 3, .reg 4] ;;
  .call 7 (base + idxIsZero) [.reg 1, .reg 4] ;;
  .cond (.reg 7)
    (.call 7 (base + idxCopy) [.reg 0, .reg 3, .reg 4])
    (.assign 7 (.const 0) ;;
     forRange 8 (.const 0) (.reg 4)
       (.cond (.load (.bin .add (.reg 0) (.reg 8)))
         (.assign 7 (.bin .add (.reg 8) (.const 1))) .nop) ;;
     .cond (.reg 7)
       (.assign 8 (.load (.bin .add (.reg 0) (.bin .sub (.reg 7) (.const 1)))) ;;
        .call 8 (base + idxBitLen) [.reg 8] ;;
        forRange 9 (.const 0) (.reg 7)
          (.assign 10 (.bin .sub (.bin .sub (.reg 7) (.const 1)) (.reg 9)) ;;
           .assign 11 (.reg 5) ;;
           .cond (.bin .eq (.reg 9) (.const 0)) (.assign 11 (.reg 8)) .nop ;;
           forRange 12 (.const 0) (.reg 11) (divModInnerBody base)))
       .nop) ;;
  .ret (.const 0)

theorem divModInnerBody_noRand (base : ℕ) : (divModInnerBody base).NoRand := by
  simp [divModInnerBody, Stmt.NoRand]

theorem mwDivMod_noRand (base : ℕ) : (mwDivMod base).NoRand := by
  simp [mwDivMod, divModInnerBody, forRange, forUp, Stmt.NoRand]

def mwDivModContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b qDst rDst L h x y, args = [a, b, qDst, rDst, L, h, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧
      qDst + L < 2 ^ w ∧ rDst + L < 2 ^ w ∧
      (qDst + L ≤ a ∨ a + L ≤ qDst) ∧ (qDst + L ≤ b ∨ b + L ≤ qDst) ∧
      (rDst + L ≤ a ∨ a + L ≤ rDst) ∧ (rDst + L ≤ b ∨ b + L ≤ rDst) ∧
      (qDst + L ≤ rDst ∨ rDst + L ≤ qDst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b qDst rDst L h, args = [a, b, qDst, rDst, L, h, 2 ^ h] ∧ v = 0 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        LimbsAt mem' qDst L h (x / y) ∧ LimbsAt mem' rDst L h (x % y)) ∧
      (∀ p, (p < qDst ∨ qDst + L ≤ p) → (p < rDst ∨ rDst + L ≤ p) → mem' p = mem p)
  cost args mem := match args with
    | [a, _, _, _, L, h, _] => 280 * L * (memBitLen mem a L h + 1) + 120
    | _ => 0

private def divModShift (la k h cnt bi : ℕ) : ℕ :=
  (la - 1 - cnt) * h + ((if cnt = 0 then k else h) - bi)

private def outerRem (la k h cnt : ℕ) : ℕ :=
  if cnt = 0 then (la - 1) * h + k else (la - cnt) * h

private theorem divModShift_zero {la k h cnt : ℕ} (hcnt : cnt < la) :
    divModShift la k h cnt 0 = outerRem la k h cnt := by
  dsimp only [divModShift, outerRem]
  rcases cnt with _ | cnt
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.sub_zero]
    have hmul : (la - 1 - (cnt + 1)) * h + h = (la - (cnt + 1)) * h := by
      have h1 : la - 1 - (cnt + 1) + 1 = la - (cnt + 1) := by omega
      calc (la - 1 - (cnt + 1)) * h + h = (la - 1 - (cnt + 1) + 1) * h := by ring
        _ = (la - (cnt + 1)) * h := by rw [h1]
    exact hmul

private theorem divModShift_end {la k h cnt : ℕ} :
    divModShift la k h cnt (if cnt = 0 then k else h) = outerRem la k h (cnt + 1) := by
  rcases cnt with _ | cnt
  · simp [divModShift, outerRem]
  · simp only [divModShift, outerRem, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.sub_self, Nat.add_zero]
    rw [show la - 1 - (cnt + 1) = la - (cnt + 1 + 1) by omega]

private theorem divMod_inner_triple {w : ℕ} {p : Program} {base : ℕ}
    (hShl : MeetsContract w p (base + idxShl1AddBit) (mwShl1AddBitContract w))
    (hLt : MeetsContract w p (base + idxLt) (mwLtContract w))
    (hRawSub : MeetsContract w p (base + idxRawSub) (mwRawSubContract w))
    {mem : ℕ → ℕ} {a b' qDst rDst L h la k cnt j nBits x y : ℕ}
    (hh : 1 ≤ h) (hw1 : 1 < 2 ^ w) (hw2 : 2 * h + 2 ≤ w) (hB : 2 ^ h < 2 ^ w)
    (hL : L < 2 ^ w) (hH : h < 2 ^ w)
    (ha : a + L < 2 ^ w) (hb : b' + L < 2 ^ w) (hqdst : qDst + L < 2 ^ w) (hrdst : rDst + L < 2 ^ w)
    (hnova : qDst + L ≤ a ∨ a + L ≤ qDst) (hnovb : qDst + L ≤ b' ∨ b' + L ≤ qDst)
    (hnovra : rDst + L ≤ a ∨ a + L ≤ rDst) (hnovrb : rDst + L ≤ b' ∨ b' + L ≤ rDst)
    (hnovqr : qDst + L ≤ rDst ∨ rDst + L ≤ qDst)
    (hx : LimbsAt mem a L h x) (hy : LimbsAt mem b' L h y)
    (hla_le : la ≤ L) (hcnt : cnt < la) (hnBits_eq : nBits = if cnt = 0 then k else h)
    (_hk_pos : 1 ≤ k) (hk_le : k ≤ h) (hj_eq : j = la - 1 - cnt) :
    Triple w p
      (fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧ st.regs 3 = rDst ∧
        st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = la ∧
        st.regs 8 = k ∧ st.regs 9 = cnt ∧ st.regs 10 = j ∧ st.regs 11 = nBits ∧
        (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
        (∀ m < j, st.mem (qDst + m) = 0) ∧
        2 ^ nBits ∣ st.mem (qDst + j) ∧
        ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
          x / 2 ^ (divModShift la k h cnt 0) = (q / 2 ^ (divModShift la k h cnt 0)) * y + r)
      (forRange 12 (.const 0) (.reg 11) (divModInnerBody base))
      (normalPost fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧ st.regs 3 = rDst ∧
        st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = la ∧
        st.regs 8 = k ∧ st.regs 9 = cnt ∧ st.regs 10 = j ∧ st.regs 11 = nBits ∧
        (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
        (∀ m < j, st.mem (qDst + m) = 0) ∧
        ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
          x / 2 ^ (divModShift la k h cnt nBits) = (q / 2 ^ (divModShift la k h cnt nBits)) * y + r)
      (fun _ => (nBits - 0) * ((115 * L + 100) + 1 + 8) + ((Expr.const 0).size + (Expr.reg 11).size + 5)) := by
  have hnBits_le : nBits ≤ h := by
    rw [hnBits_eq]; split_ifs <;> omega
  have hnBits_w : nBits < 2 ^ w := lt_of_le_of_lt hnBits_le hH
  have hj_lt : j < L := by omega
  have h115 : Triple w p
      (fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧ st.regs 3 = rDst ∧
        st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = la ∧
        st.regs 8 = k ∧ st.regs 9 = cnt ∧ st.regs 10 = j ∧ st.regs 11 = nBits ∧
        (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
        (∀ m < j, st.mem (qDst + m) = 0) ∧
        2 ^ nBits ∣ st.mem (qDst + j) ∧
        ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
          x / 2 ^ (divModShift la k h cnt 0) = (q / 2 ^ (divModShift la k h cnt 0)) * y + r)
      (forRange 12 (.const 0) (.reg 11) (divModInnerBody base))
      (normalPost fun st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧ st.regs 3 = rDst ∧
        st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = la ∧
        st.regs 8 = k ∧ st.regs 9 = cnt ∧ st.regs 10 = j ∧ st.regs 11 = nBits ∧ st.regs 12 = nBits ∧
        (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
        (∀ m < j, st.mem (qDst + m) = 0) ∧
        2 ^ (nBits - nBits) ∣ st.mem (qDst + j) ∧
        ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
          x / 2 ^ (divModShift la k h cnt nBits) = (q / 2 ^ (divModShift la k h cnt nBits)) * y + r)
      (fun _ => (nBits - 0) * ((115 * L + 100) + (Expr.reg 11).size + 8) +
        ((Expr.const 0).size + (Expr.reg 11).size + 5)) := by
    refine Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 11)
      (body := divModInnerBody base)
      (Inv := fun bi st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧ st.regs 3 = rDst ∧
        st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = la ∧
        st.regs 8 = k ∧ st.regs 9 = cnt ∧ st.regs 10 = j ∧ st.regs 11 = nBits ∧ st.regs 12 = bi ∧
        (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
        (∀ m < j, st.mem (qDst + m) = 0) ∧
        2 ^ (nBits - bi) ∣ st.mem (qDst + j) ∧
        ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
          x / 2 ^ (divModShift la k h cnt bi) = (q / 2 ^ (divModShift la k h cnt bi)) * y + r)
      (115 * L + 100) 0 nBits (Nat.zero_le nBits) hw1 (fun _ => hnBits_w)
      (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hfr, hlow, hdvd, hqr⟩ => by
        refine ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp [h11], by simp, hfr, hlow, by simpa using hdvd, hqr⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h11 := hi.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
      (fun bi _ hbi => by
        intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
          hfr, hlow, hdvd, q, r, hq, hr, hr_lt, heuclid⟩
        set d := nBits - 1 - bi
        set s := j * h + (d + 1)
        set s' := j * h + d
        have hd_lt : d < h := by omega
        have hbi_w : bi < 2 ^ w := lt_trans hbi hnBits_w
        have hd_w : d < 2 ^ w := lt_trans hd_lt hH
        have hs_eq : divModShift la k h cnt bi = s := by
          dsimp only [divModShift, s, d]; rw [← hj_eq, ← hnBits_eq]
          congr 1; omega
        have hs'_eq : divModShift la k h cnt (bi + 1) = s' := by
          dsimp only [divModShift, s', d]; rw [← hj_eq, ← hnBits_eq]
          congr 1; omega
        have hs_succ : s = s' + 1 := by omega
        rw [hs_eq] at heuclid
        have h2s_q : 2 ^ s ∣ q := by
          have htab_list : tab L (fun m => st.mem (qDst + m)) = toLimbs q L h := by
            refine List.ext_getElem (by simp [tab, toLimbs_length]) fun m hm _ => ?_
            have hmL : m < L := by simpa [tab] using hm
            simp only [tab, List.getElem_map, List.getElem_range]
            rw [toLimbs_getElem hmL]
            exact hq.getElem hmL
          have htab_q : evalLimbs h (tab L (fun m => st.mem (qDst + m))) = q := by
            rw [htab_list]; exact evalLimbs_toLimbs_of_lt hq.lt_pow
          rw [← htab_q]
          exact divMod_q_dvd (fun m => st.mem (qDst + m)) j (d + 1) (by omega) hlow
            (by simpa [show nBits - bi = d + 1 by omega] using hdvd)
        have ha_limb : st.mem (a + j) = (x / 2 ^ (j * h)) % 2 ^ h := by
          rw [hfr (a + j) (by omega) (by omega)]
          exact hx.getElem hj_lt
        have hy_st : LimbsAt st.mem b' L h y :=
          hy.congr fun m hm1 hm2 => hfr m (by omega) (by omega)
        set limbVal := (x / 2 ^ (j * h)) % 2 ^ h
        have hlimb_lt : limbVal < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hlimb_w : limbVal < 2 ^ w := lt_trans hlimb_lt hB
        set bit := (x / 2 ^ s') % 2
        have hbit_eq : (limbVal >>> d) &&& 1 = bit := divMod_limb_bit (x := x) hd_lt
        have hbit_le : bit ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
        have hbit_w : bit < 2 ^ w := by omega
        have hx_step : x / 2 ^ s' = 2 * (x / 2 ^ s) + bit := by
          have h1 : x / 2 ^ s = (x / 2 ^ s') / 2 := by
            rw [hs_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
          rw [h1]
          exact (Nat.div_add_mod (x / 2 ^ s') 2).symm
        refine runs_start_le ?_
        dsimp only [divModInnerBody]
        have heval13 : (Expr.bin .sub (.bin .sub (.reg 11) (.const 1)) (.reg 12)).eval w st =
            some d := by
          refine Expr.eval_sub
            (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega))
            (by eval_expr) (by omega)
        refine runs_seq_assign_le heval13 ?_
        have hshr_w : limbVal >>> d < 2 ^ w := by
          rw [Nat.shiftRight_eq_div_pow]
          exact lt_of_le_of_lt (Nat.div_le_self _ _) hlimb_w
        have heval14 : (Expr.bin .and (.bin .shiftRight
            (.load (.bin .add (.reg 0) (.reg 10))) (.reg 13)) (.const 1)).eval w
            { mem := st.mem, regs := Function.update st.regs 13 d, pos := st.pos } = some bit := by
          rw [← hbit_eq]
          refine Expr.eval_bin
            (Expr.eval_bin
              (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) ha_limb)
              (by eval_expr) hshr_w)
            (by eval_expr) (by dsimp only [BinOp.eval]; rw [hbit_eq]; exact hbit_w)
        refine runs_seq_assign_le heval14 ?_
        have hpre_shl : (mwShl1AddBitContract w).pre [rDst, bit, L, 2 ^ h] st.mem :=
          ⟨rDst, bit, L, h, r, rfl, hbit_le, hh, hw2, hrdst, hr⟩
        refine runs_seq_call_le hShl
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
          (by wram_words) hpre_shl ?_
        rintro carry mem₁ pos₁ ⟨rDst', bit', L', h', heq_args, hcarry_le, hpost_shl, hfr_shl⟩
        simp only [List.cons.injEq, and_true] at heq_args
        rcases heq_args with ⟨rfl, hbit_eq', rfl, hp_eq⟩
        have hh_eq : h' = h := Nat.pow_right_injective (by norm_num) hp_eq.symm
        cases hh_eq
        obtain ⟨hcarry_eq, hr1_limbs⟩ := hpost_shl r hr
        rw [← hbit_eq'] at hcarry_eq hr1_limbs
        set r1 := (2 * r + bit) % 2 ^ (L * h)
        have hcarry_w : carry < 2 ^ w := by omega
        have hy_st1 : LimbsAt mem₁ b' L h y :=
          hy_st.congr fun m hm1 hm2 => hfr_shl m (by omega)
        have hq_st1 : LimbsAt mem₁ qDst L h q :=
          hq.congr fun m hm1 hm2 => hfr_shl m (by omega)
        have hq_limb1 : mem₁ (qDst + j) = st.mem (qDst + j) := hfr_shl _ (by omega)
        have hq_low1 : ∀ m < j, mem₁ (qDst + m) = 0 := fun m hm => by
          rw [hfr_shl _ (by omega)]; exact hlow m hm
        have hfr1 : ∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → mem₁ q' = mem q' :=
          fun q' hnq hnr => by rw [hfr_shl q' hnr, hfr q' hnq hnr]
        have hafter_lt :
            ∀ (ltv : ℕ) (st₂ : State),
              st₂.mem = mem₁ →
              st₂.regs 0 = a → st₂.regs 1 = b' → st₂.regs 2 = qDst → st₂.regs 3 = rDst →
              st₂.regs 4 = L → st₂.regs 5 = h → st₂.regs 6 = 2 ^ h → st₂.regs 7 = la →
              st₂.regs 8 = k → st₂.regs 9 = cnt → st₂.regs 10 = j → st₂.regs 11 = nBits →
              st₂.regs 12 = bi → st₂.regs 13 = d →
              st₂.regs 15 = ltv →
              (ltv ≠ 0 → carry = 0 ∧ r1 < y) →
              (ltv = 0 → carry ≠ 0 ∨ y ≤ r1) →
              ∀ ω', ∃ o st'' c, Runs w p ω'
                (.cond (.reg 15) .nop
                  (.call 14 (base + idxRawSub) [.reg 3, .reg 1, .reg 3, .reg 4, .reg 6] ;;
                   .store (.bin .add (.reg 2) (.reg 10))
                     (.bin .add (.load (.bin .add (.reg 2) (.reg 10))) (.bin .shiftLeft (.const 1) (.reg 13)))))
                st₂ o st'' c ∧
                normalPost (fun st₃ =>
                  (st₃.regs 0 = a ∧ st₃.regs 1 = b' ∧ st₃.regs 2 = qDst ∧ st₃.regs 3 = rDst ∧
                    st₃.regs 4 = L ∧ st₃.regs 5 = h ∧ st₃.regs 6 = 2 ^ h ∧ st₃.regs 7 = la ∧
                    st₃.regs 8 = k ∧ st₃.regs 9 = cnt ∧ st₃.regs 10 = j ∧ st₃.regs 11 = nBits ∧
                    Function.update st₃.regs 12 (bi + 1) 12 = bi + 1 ∧
                    (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st₃.mem q' = mem q') ∧
                    (∀ m < j, st₃.mem (qDst + m) = 0) ∧
                    2 ^ (nBits - (bi + 1)) ∣ st₃.mem (qDst + j) ∧
                    ∃ q r₂, LimbsAt st₃.mem qDst L h q ∧ LimbsAt st₃.mem rDst L h r₂ ∧ r₂ < y ∧
                      x / 2 ^ (divModShift la k h cnt (bi + 1)) =
                        (q / 2 ^ (divModShift la k h cnt (bi + 1))) * y + r₂) ∧
                  st₃.regs 12 = bi) o st'' ∧
                c ≤ 40 * L + 40 := by
          intro ltv st₂ hm₂ rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 rr8 rr9 rr10 rr11 rr12 rr13 rr15 hlt_t hlt_f ω'
          refine runs_start_le ?_
          wram_step
          · have hlt1 : carry = 0 ∧ r1 < y := hlt_t hcond
            have hnval_lt : 2 * r + bit < 2 ^ (L * h) := by
              by_contra hge
              have hge' : 2 ^ (L * h) ≤ 2 * r + bit := Nat.not_lt.mp hge
              have : 1 ≤ (2 * r + bit) / 2 ^ (L * h) := Nat.div_pos hge' (Nat.two_pow_pos _)
              omega
            have hr1_eq : r1 = 2 * r + bit := Nat.mod_eq_of_lt hnval_lt
            have hr_lt_y : 2 * r + bit < y := by rw [← hr1_eq]; exact hlt1.2
            have hnot_yle : ¬ y ≤ 2 * r + bit := by omega
            have hq_div := (divMod_q_div_step (q := q) (s := s') (by rw [← hs_succ]; exact h2s_q)).2
            rw [← hs_succ] at hq_div
            have heuc := divMod_euclid_step (r := r) (bit := bit) heuclid
            rw [← hx_step, ← hq_div] at heuc
            simp only [hnot_yle, ↓reduceIte, Nat.add_zero] at heuc
            refine runs_nop_le ?_ (by wram_cost)
            refine ⟨⟨rr0, rr1, rr2, rr3, rr4, rr5, rr6, rr7, rr8, rr9, rr10, rr11, by simp,
              fun q' hnq hnr => by rw [hm₂]; exact hfr1 q' hnq hnr,
              fun m hm => by rw [hm₂]; exact hq_low1 m hm,
              ?_, q, r1, hm₂ ▸ hq_st1, hm₂ ▸ hr1_limbs, hlt1.2, ?_⟩, rr12⟩
            · rw [hm₂, hq_limb1, show nBits - (bi + 1) = d by omega]
              exact dvd_trans (Nat.pow_dvd_pow 2 (show d ≤ d + 1 by omega))
                (by simpa [show nBits - bi = d + 1 by omega] using hdvd)
            · rw [hs'_eq, hr1_eq]; exact heuc
          · have hge_r : carry ≠ 0 ∨ y ≤ r1 := hlt_f hcond
            have hpre_sub : (mwRawSubContract w).pre [rDst, b', rDst, L, 2 ^ h] st₂.mem :=
              ⟨rDst, b', rDst, L, h, r1, y, rfl, hh, hw2, hrdst, hb, hrdst,
                Or.inr (Or.inr rfl), hnovrb, hm₂ ▸ hr1_limbs, hm₂ ▸ hy_st1⟩
            refine runs_seq_call_le hRawSub
              (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
                (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
                  (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
              (by wram_words) hpre_sub ?_
            rintro borrow mem₂ pos₂ ⟨rDst_a, b_a, rDst_c, L_a, h_a, heq_sub, hborrow_le, hsub_post, hfr_sub⟩
            simp only [List.cons.injEq, and_true] at heq_sub
            rcases heq_sub with ⟨rfl, rfl, rfl, rfl, hp_sub⟩
            have hh_sub : h_a = h := Nat.pow_right_injective (by norm_num) hp_sub.symm
            cases hh_sub
            obtain ⟨r₂, hr₂_limbs, hr₂_eq⟩ := hsub_post r1 y (hm₂ ▸ hr1_limbs) (hm₂ ▸ hy_st1)
            obtain ⟨hr₂_val, hr₂_y, hy_le⟩ := divMod_rem_sub hr_lt hy.lt_pow hbit_le hborrow_le
              hr₂_limbs.lt_pow hr₂_eq (by simpa [hcarry_eq] using hge_r)
            have hq_st2 : LimbsAt mem₂ qDst L h q :=
              (hm₂ ▸ hq_st1).congr fun m hm1 hm2 => hfr_sub m (by omega)
            have hq_limb2 : mem₂ (qDst + j) = st.mem (qDst + j) := by
              rw [hfr_sub _ (by omega), hm₂, hq_limb1]
            have hq_low2 : ∀ m < j, mem₂ (qDst + m) = 0 := fun m hm => by
              rw [hfr_sub _ (by omega), hm₂]; exact hq_low1 m hm
            have hpow_d_lt : 2 ^ d < 2 ^ h := Nat.pow_lt_pow_right (by norm_num) hd_lt
            have hpow_d_w : 2 ^ d < 2 ^ w := lt_trans hpow_d_lt hB
            have h1shl_eq : BinOp.shiftLeft.eval 1 d = 2 ^ d := by simp [BinOp.eval, Nat.shiftLeft_eq]
            have hadd_lt_h : mem₂ (qDst + j) + 2 ^ d < 2 ^ h ∧ 2 ^ d ∣ (mem₂ (qDst + j) + 2 ^ d) :=
              divMod_pow_add_lt hd_lt (by rw [hq_limb2]; exact hq.limb_lt hj_lt)
                (by rw [hq_limb2]; simpa [show nBits - bi = d + 1 by omega] using hdvd)
            have hadd_w : mem₂ (qDst + j) + 2 ^ d < 2 ^ w := lt_trans hadd_lt_h.1 hB
            refine runs_store_le
              (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
              (Expr.eval_add
                (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) rfl)
                (Expr.eval_bin (by eval_expr) (by eval_expr) (by rw [h1shl_eq]; exact hpow_d_w))
                (by rw [h1shl_eq]; exact hadd_w))
              ?_ (by dsimp only [mwRawSubContract]; wram_cost)
            rw [h1shl_eq]
            set mem₃ := Function.update mem₂ (qDst + j) (mem₂ (qDst + j) + 2 ^ d)
            have hr₂_st3 : LimbsAt mem₃ rDst L h r₂ := hr₂_limbs.update_outside (by omega)
            have hq_ds3 : LimbsAt mem₃ qDst L h (evalLimbs h (tab L (fun m => mem₃ (qDst + m)))) :=
              limbsAt_of_list (fun m hm => by simp [tab]) (by simp [tab]) (fun v hv => by
                simp only [tab, List.mem_map, List.mem_range] at hv
                rcases hv with ⟨m, hm, rfl⟩
                dsimp only [mem₃]
                by_cases hmj : m = j
                · subst hmj; simp [Function.update_self, hadd_lt_h.1]
                · rw [Function.update_of_ne (by omega)]
                  exact hq_st2.limb_lt hm)
            have hq3_val : evalLimbs h (tab L (fun m => mem₃ (qDst + m))) = q + 2 ^ s' := by
              have hup := dm_tab_update_mem h L j (mem₂ (qDst + j) + 2 ^ d) mem₂ qDst hj_lt
              have htab_list2 : tab L (fun m => mem₂ (qDst + m)) = toLimbs q L h := by
                refine List.ext_getElem (by simp [tab, toLimbs_length]) fun m hm _ => ?_
                have hmL : m < L := by simp only [tab, List.length_map, List.length_range] at hm; exact hm
                simp only [tab, List.getElem_map, List.getElem_range]
                rw [toLimbs_getElem hmL]
                exact hq_st2.getElem hmL
              have htab_q2 : evalLimbs h (tab L (fun m => mem₂ (qDst + m))) = q := by
                rw [htab_list2]; exact evalLimbs_toLimbs_of_lt hq_st2.lt_pow
              rw [htab_q2] at hup
              have hjh : 2 ^ (j * h) * (mem₂ (qDst + j) + 2 ^ d) =
                  2 ^ (j * h) * mem₂ (qDst + j) + 2 ^ s' := by
                dsimp only [s']; rw [Nat.mul_add, Nat.pow_add]
              rw [hjh] at hup
              dsimp only [mem₃]
              omega
            rw [hq3_val] at hq_ds3
            have hq3_div := (divMod_q_div_step (q := q) (s := s') (by rw [← hs_succ]; exact h2s_q)).1
            rw [← hs_succ] at hq3_div
            have heuc := divMod_euclid_step (r := r) (bit := bit) heuclid
            simp only [hy_le, ↓reduceIte] at heuc
            rw [← hx_step, ← hq3_div] at heuc
            refine ⟨⟨rr0, rr1, rr2, rr3, rr4, rr5, rr6, rr7, rr8, rr9, rr10, rr11, by simp,
              fun q' hnq hnr => by
                dsimp only [mem₃]; rw [Function.update_of_ne (by omega), hfr_sub q' hnr, hm₂, hfr1 q' hnq hnr],
              fun m hm => by dsimp only [mem₃]; rw [Function.update_of_ne (by omega)]; exact hq_low2 m hm,
              ?_, q + 2 ^ s', r₂, hq_ds3, hr₂_st3, hr₂_y, ?_⟩, rr12⟩
            · dsimp only [mem₃]
              rw [Function.update_self, show nBits - (bi + 1) = d by omega]
              exact hadd_lt_h.2
            · rw [hs'_eq, hr₂_val]; exact heuc
        refine runs_seq_cond_le (by eval_expr)
          (fun hne_carry => by
            refine runs_seq_assign_le (by eval_expr) ?_
            obtain ⟨o, st'', c, hr, hp', hc⟩ := hafter_lt 0
              ⟨mem₁, Function.update (Function.update (Function.update (Function.update st.regs 13 d) 14 bit) 14 carry) 15 0, pos₁⟩
              rfl (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
              (by simp [h5]) (by simp [h6]) (by simp [h7]) (by simp [h8]) (by simp [h9])
              (by simp [h10]) (by simp [h11]) (by simp [h12]) (by simp) (by simp)
              (fun h0' => absurd rfl h0') (fun _ => Or.inl (by rw [hcarry_eq]; exact hne_carry)) ω
            exact ⟨o, st'', c, hr, hp', by dsimp only [mwShl1AddBitContract]; wram_cost⟩)
          (fun heq_carry => by
            have hpre_lt : (mwLtContract w).pre [rDst, b', L] mem₁ :=
              ⟨rDst, b', L, h, r1, y, rfl, hh, hw2, hrdst, hb, hr1_limbs, hy_st1⟩
            refine runs_seq_call_le hLt
              (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
              (by wram_words) hpre_lt ?_
            rintro lt_v mem₂ pos₂ ⟨rDst_l, b_l, L_l, heq_lt, hmem_lt, hpost_lt⟩
            simp only [List.cons.injEq, and_true] at heq_lt
            rcases heq_lt with ⟨rfl, rfl, rfl⟩
            have hlt_val := hpost_lt h r1 y hr1_limbs hy_st1
            obtain ⟨o, st'', c, hr, hp', hc⟩ := hafter_lt lt_v
              ⟨mem₂, Function.update (Function.update (Function.update (Function.update st.regs 13 d) 14 bit) 14 carry) 15 lt_v, pos₂⟩
              hmem_lt (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
              (by simp [h5]) (by simp [h6]) (by simp [h7]) (by simp [h8]) (by simp [h9])
              (by simp [h10]) (by simp [h11]) (by simp [h12]) (by simp) (by simp)
              (fun hne => ⟨by rw [hcarry_eq]; exact heq_carry, by
                by_contra hge
                have hnot : ¬ r1 < y := Nat.not_lt.mpr (Nat.le_of_not_lt hge)
                simp only [hnot, ↓reduceIte] at hlt_val
                exact hne hlt_val⟩)
              (fun heq => Or.inr (by
                by_contra hlt'
                have hlt1 : r1 < y := Nat.lt_of_not_le hlt'
                simp only [hlt1, ↓reduceIte] at hlt_val
                rw [heq] at hlt_val; omega)) ω
            exact ⟨o, st'', c, hr, hp', by dsimp only [mwShl1AddBitContract, mwLtContract]; wram_cost⟩))
  refine h115.strengthen_post ?_
  rintro o st' hq
  cases o with
  | returned u => exact False.elim hq
  | normal =>
    rcases hq with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, _, hfr, hlow, _, hqr⟩
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, hfr, hlow, hqr⟩

theorem mwDivMod_meetsContract {w : ℕ} {p : Program} {f base : ℕ}
    (hZero : MeetsContract w p (base + idxZero) (mwZeroContract w))
    (hCopy : MeetsContract w p (base + idxCopy) (mwCopyContract w))
    (hIsZero : MeetsContract w p (base + idxIsZero) (mwIsZeroContract w))
    (hLt : MeetsContract w p (base + idxLt) (mwLtContract w))
    (hRawSub : MeetsContract w p (base + idxRawSub) (mwRawSubContract w))
    (hShl : MeetsContract w p (base + idxShl1AddBit) (mwShl1AddBitContract w))
    (hBitLen : MeetsContract w p (base + idxBitLen) (mwBitLenContract w))
    (hProc : p.procs[f]? = some (mwDivMod base)) :
    MeetsContract w p f (mwDivModContract w) := by
  refine meetsContract_of_runs hProc ?_
  rintro args mem pos ω hwords ⟨a, b', qDst, rDst, L, h, x, y, rfl, hh, hw2, ha, hb, hqdst, hrdst,
    hnova, hnovb, hnovra, hnovrb, hnovqr, hx, hy⟩
  have hB : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.one_le_pow h 2 (by norm_num)) hB
  have hL : L < 2 ^ w := by omega
  have hH : h < 2 ^ w := lt_trans (Nat.lt_two_pow_self (n := h)) hB
  refine runs_start_le ?_
  dsimp only [mwDivMod]
  refine runs_seq_call_le hZero
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    (by wram_words) ⟨qDst, L, rfl, hw1, hqdst⟩ ?_
  rintro v0 mem₁ pos₁ ⟨q0, L0, heq0, _, hzero1, hfr1⟩
  simp only [List.cons.injEq, and_true] at heq0
  rcases heq0 with ⟨rfl, rfl⟩
  refine runs_seq_call_le hZero
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    (by wram_words) ⟨rDst, L, rfl, hw1, hrdst⟩ ?_
  rintro v1 mem₂ pos₂ ⟨r0, L1, heq1, _, hzero2, hfr2⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨rfl, rfl⟩
  dsimp only at hfr1 hfr2
  have hfr_qr2 : ∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → mem₂ q' = mem q' :=
    fun q' hnq hnr => by rw [hfr2 q' hnr, hfr1 q' hnq]; rfl
  have hx2 : LimbsAt mem₂ a L h x := hx.congr fun m hm1 hm2 => hfr_qr2 m (by omega) (by omega)
  have hy2 : LimbsAt mem₂ b' L h y := hy.congr fun m hm1 hm2 => hfr_qr2 m (by omega) (by omega)
  have hq_zero2 : LimbsAt mem₂ qDst L h 0 :=
    limbsAt_zero_iff.mpr (WordRAM.listAt_replicate.mpr fun m hm => by
      rw [hfr2 (qDst + m) (by omega)]
      exact WordRAM.listAt_replicate.mp hzero1 m hm)
  have hr_zero2 : LimbsAt mem₂ rDst L h 0 := limbsAt_zero_iff.mpr hzero2
  refine runs_seq_call_le hIsZero
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    (by wram_words) ⟨b', L, rfl, hw1, hb⟩ ?_
  rintro iz mem₃ pos₃ ⟨b_z, L_z, heqz, hmem_z, hiz_val⟩
  simp only [List.cons.injEq, and_true] at heqz
  rcases heqz with ⟨rfl, rfl⟩
  have hmem_eq : mem₃ = mem₂ := hmem_z
  dsimp only at hmem_eq hiz_val
  cases hmem_eq
  have hbl_eq : memBitLen mem a L h = bitLen x := memBitLen_eq_bitLen hx
  refine runs_seq_cond_le (by eval_expr)
    (fun hne_z => by
      have hy0 : y = 0 := by
        have hall : ∀ i < L, mem₂ (b' + i) = 0 := by
          by_contra hnot
          simp [hnot] at hne_z
        exact LimbsAt.ext hy2 (limbsAt_zero_iff.mpr (WordRAM.listAt_replicate.mpr hall))
      subst hy0
      refine runs_seq_call_le hCopy
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
        (by wram_words) ⟨a, rDst, L, rfl, hw1, ha, hrdst,
          by rcases hnovra with h1 | h2; exact Or.inl h1; exact Or.inr (Or.inl h2)⟩ ?_
      rintro vc mem₃ pos₃ ⟨a_c, r_c, L_c, heqc, _, hcp_val, hfr_cp⟩
      simp only [List.cons.injEq, and_true] at heqc
      rcases heqc with ⟨rfl, rfl, rfl⟩
      dsimp only at hcp_val hfr_cp
      have hx_cp : LimbsAt mem₃ rDst L h x :=
        ⟨hx.lt_pow, fun m hm => by
          rw [hcp_val m (by simpa [toLimbs_length] using hm)]; exact hx2.listAt m hm⟩
      have hq_cp : LimbsAt mem₃ qDst L h 0 := hq_zero2.congr fun m hm1 hm2 => hfr_cp m (by omega)
      refine runs_ret_le (by eval_expr)
        ⟨a, b', qDst, rDst, L, h, rfl, rfl, fun x' y' hx' hy' => by
          obtain rfl : x' = x := hx'.ext hx
          obtain rfl : y' = 0 := hy'.ext hy
          simpa using ⟨hq_cp, hx_cp⟩,
          fun q' hnq hnr => by dsimp only; rw [hfr_cp q' hnr, hfr_qr2 q' hnq hnr]⟩ ?_
      dsimp only [mwDivModContract, mwZeroContract, mwIsZeroContract, mwCopyContract]
      rw [Nat.mul_add, Nat.mul_one]
      wram_cost)
    (fun heq_z => by
      have hy_pos : 0 < y := by
        by_contra hnot
        have hy0 : y = 0 := by omega
        subst hy0
        have hall : ∀ i < L, mem₂ (b' + i) = 0 := fun i hi => by
          have := hy2.getElem hi; simp [Nat.zero_div, Nat.zero_mod] at this; exact this
        have hneg : ¬ (∀ i < L, mem₂ (b' + i) = 0) := by simpa using heq_z
        exact absurd hall hneg
      have hscan : Triple w p
          (fun st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
            st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = 0)
          (forRange 8 (.const 0) (.reg 4)
            (.cond (.load (.bin .add (.reg 0) (.reg 8)))
              (.assign 7 (.bin .add (.reg 8) (.const 1))) .nop))
          (normalPost fun st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
            st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
            st.regs 7 = memActiveLimbs mem a L ∧ st.regs 8 = L)
          (fun _ => (L - 0) * (9 + (Expr.reg 4).size + 8) + ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
        have hact_eq : memActiveLimbs mem₂ a L = memActiveLimbs mem a L :=
          memActiveLimbs_eq_of_lt fun i hi => hfr_qr2 (a + i) (by omega) (by omega)
        have hfor := Triple.forRange_const (w := w) (p := p) (r := 8)
          (P := fun st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
            st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧ st.regs 7 = 0)
          (lo := .const 0) (hi := .reg 4)
          (body := .cond (.load (.bin .add (.reg 0) (.reg 8)))
            (.assign 7 (.bin .add (.reg 8) (.const 1))) .nop)
          (Inv := fun i st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
            st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
            st.regs 7 = memActiveLimbs mem₂ a i ∧ st.regs 8 = i)
          9 0 L (Nat.zero_le L) hw1 (fun _ => hL)
          (fun st ⟨hm, r0, r1, r2, r3, r4, r5, r6, r7⟩ => by
            refine ⟨by eval_expr, hm, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
              by simp [r5], by simp [r6], by simp [r7, memActiveLimbs], by simp⟩)
          (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.2)
          (fun _ st _ _ hi => by have h4 := hi.2.2.2.2.2.1; eval_expr)
          (fun i _ hilt => by
            intro st _ ⟨hmem, r0, r1, r2, r3, r4, r5, r6, r7, r8⟩
            have hload : (Expr.load (.bin .add (.reg 0) (.reg 8))).eval w st = some (mem₂ (a + i)) := by
              rw [← hmem]; exact Expr.eval_load_of_eq (by eval_expr) rfl
            refine runs_start_le ?_
            refine runs_cond_le hload
              (fun hne => runs_assign_le (by eval_expr)
                ⟨⟨hmem, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
                  by simp [r5], by simp [r6], by simp [memActiveLimbs, hne], by simp⟩, r8⟩ (by wram_cost))
              (fun heq => runs_nop_le
                ⟨⟨hmem, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
                  by simp [r5], by simp [r6], by simp [memActiveLimbs, heq, r7], by simp⟩, r8⟩ (by wram_cost)))
        refine Triple.strengthen_post hfor (fun o st hq => by
          cases o with
          | returned u => exact False.elim hq
          | normal =>
            rcases hq with ⟨hmem, r0, r1, r2, r3, r4, r5, r6, r7, r8⟩
            exact ⟨hmem, r0, r1, r2, r3, r4, r5, r6, by rw [r7, hact_eq], r8⟩)
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (by eval_expr) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_triple_le hscan ⟨rfl, by simp [startState], by simp [startState],
        by simp [startState], by simp [startState], by simp [startState], by simp [startState],
        by simp [startState], by simp⟩ ?_
      rintro st_s ⟨hmem_s, rs0, rs1, rs2, rs3, rs4, rs5, rs6, rs7, _⟩
      set la := memActiveLimbs mem a L
      have hla_act : la = activeLimbs x L h := memActiveLimbs_eq_activeLimbs hx
      have hla_le : la ≤ L := by rw [hla_act]; exact activeLimbs_le x L h
      refine runs_seq_cond_le (by eval_expr)
        (fun hne_la => by
          have hla_pos : 1 ≤ la := Nat.pos_of_ne_zero hne_la
          have htop_nz : mem (a + (la - 1)) ≠ 0 := by
            rw [hx.getElem (by omega), hla_act]
            exact top_limb_ne_zero_of_activeLimbs_pos (by rw [← hla_act]; exact hla_pos)
          have htop_val : st_s.mem (a + (la - 1)) = mem (a + (la - 1)) := by
            rw [hmem_s]; exact hfr_qr2 (a + (la - 1)) (by omega) (by omega)
          have htop_lt : mem (a + (la - 1)) < 2 ^ h := hx.limb_lt (by omega)
          have htop_w : mem (a + (la - 1)) < 2 ^ w := lt_trans htop_lt hB
          set top := mem (a + (la - 1))
          set k := bitLen top
          have hk_pos : 1 ≤ k := by
            by_contra hk0
            have : k = 0 := by omega
            have h0 : top < 2 ^ 0 := this ▸ lt_two_pow_bitLen top
            exact htop_nz (by omega)
          have hk_le : k ≤ h := bitLen_le_of_lt_two_pow htop_lt
          have hk_w : k < 2 ^ w := lt_of_le_of_lt hk_le hH
          have hbl_form : bitLen x = (la - 1) * h + k := by
            rw [← hbl_eq]
            dsimp only [memBitLen]
            have hne0 : memActiveLimbs mem a L ≠ 0 := Nat.ne_of_gt hla_pos
            simp only [hne0, ↓reduceIte]
            rfl
          have hla_bl : la ≤ bitLen x := by
            rw [hla_act]; exact activeLimbs_le_bitLen hh
          refine runs_seq_assoc_le ?_
          refine runs_seq_assign_le
            (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
              (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) (by omega)) htop_val) ?_
          refine runs_seq_assoc_le ?_
          refine runs_seq_call_le hBitLen
            (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
            (by wram_words) ⟨top, rfl, hw1, htop_w, hk_w⟩ ?_
          rintro kv mem₄ pos₄ ⟨top', heq_bl, hmem_bl, hkv⟩
          simp only [List.cons.injEq, and_true] at heq_bl
          subst heq_bl; subst hmem_bl; subst hkv
          set stepCost := fun cnt => (if cnt = 0 then k else h) * (115 * L + 109) + 27
          have houter : Triple w p
              (fun st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
                st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
                st.regs 7 = la ∧ st.regs 8 = k)
              (forRange 9 (.const 0) (.reg 7)
                (.assign 10 (.bin .sub (.bin .sub (.reg 7) (.const 1)) (.reg 9)) ;;
                 .assign 11 (.reg 5) ;;
                 .cond (.bin .eq (.reg 9) (.const 0)) (.assign 11 (.reg 8)) .nop ;;
                 forRange 12 (.const 0) (.reg 11) (divModInnerBody base)))
              (normalPost fun st =>
                (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
                ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
                  x / 2 ^ (outerRem la k h la) = (q / 2 ^ (outerRem la k h la)) * y + r)
              (fun _ => rangeCost stepCost 0 la + (la - 0) * ((Expr.reg 7).size + 8) +
                ((Expr.const 0).size + (Expr.reg 7).size + 5)) := by
            have hla_w : la < 2 ^ w := lt_of_le_of_lt hla_le hL
            refine Triple.strengthen_post
              (Triple.forRange_le (w := w) (p := p) (r := 9)
                (P := fun st => st.mem = mem₂ ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
                  st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
                  st.regs 7 = la ∧ st.regs 8 = k)
                (lo := .const 0) (hi := .reg 7)
                (body :=
                  .assign 10 (.bin .sub (.bin .sub (.reg 7) (.const 1)) (.reg 9)) ;;
                  .assign 11 (.reg 5) ;;
                  .cond (.bin .eq (.reg 9) (.const 0)) (.assign 11 (.reg 8)) .nop ;;
                  forRange 12 (.const 0) (.reg 11) (divModInnerBody base))
                (Inv := fun cnt st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = qDst ∧
                  st.regs 3 = rDst ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
                  st.regs 7 = la ∧ st.regs 8 = k ∧ st.regs 9 = cnt ∧
                  (∀ q', (q' < qDst ∨ qDst + L ≤ q') → (q' < rDst ∨ rDst + L ≤ q') → st.mem q' = mem q') ∧
                  (∀ m < la - cnt, st.mem (qDst + m) = 0) ∧
                  ∃ q r, LimbsAt st.mem qDst L h q ∧ LimbsAt st.mem rDst L h r ∧ r < y ∧
                    x / 2 ^ (outerRem la k h cnt) = (q / 2 ^ (outerRem la k h cnt)) * y + r)
                stepCost 0 la (Nat.zero_le la) hw1 (fun _ => hla_w)
                (fun st ⟨hm, r0, r1, r2, r3, r4, r5, r6, r7, r8⟩ => by
                  refine ⟨by eval_expr, by simp [r0], by simp [r1], by simp [r2], by simp [r3],
                    by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp,
                    fun q' hnq hnr => by rw [hm]; exact hfr_qr2 q' hnq hnr,
                    fun m _ => by
                      rw [hm]; have h0' := hq_zero2.getElem (by omega : m < L); simpa using h0',
                    0, 0, hm ▸ hq_zero2, hm ▸ hr_zero2, hy_pos, ?_⟩
                  have hx_lt_rem : x < 2 ^ outerRem la k h 0 := by
                    simp only [outerRem, ↓reduceIte, ← hbl_form]; exact lt_two_pow_bitLen x
                  simp [Nat.div_eq_of_lt hx_lt_rem, Nat.zero_div])
                (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.2.1)
                (fun _ st _ _ hi => by have h7 := hi.2.2.2.2.2.2.2.1; eval_expr)
                (fun cnt _ hcnt => by
                  intro st _ ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, hfr, hlow, q, r, hq, hr, hr_lt, heuclid⟩
                  set j := la - 1 - cnt
                  set nBits := if cnt = 0 then k else h
                  have hj_lt : j < L := by omega
                  have hcnt_w : cnt < 2 ^ w := lt_trans hcnt hla_w
                  have hj_w : j < 2 ^ w := lt_trans hj_lt hL
                  have hnBits_w : nBits < 2 ^ w := by
                    dsimp only [nBits]; split_ifs <;> exact lt_of_le_of_lt (by omega) hH
                  have hlow_j : ∀ m < j, st.mem (qDst + m) = 0 := fun m hm => hlow m (by omega)
                  have hdvd_j : 2 ^ nBits ∣ st.mem (qDst + j) := by
                    have hz : st.mem (qDst + j) = 0 := hlow j (by omega)
                    rw [hz]; exact dvd_zero _
                  refine runs_start_le ?_
                  refine runs_seq_assign_le
                    (Expr.eval_sub (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega))
                      (by eval_expr) (by omega)) ?_
                  refine runs_seq_assign_le (by eval_expr) ?_
                  refine runs_seq_cond_le (Expr.eval_eq_op (by eval_expr) (by eval_expr) hw1)
                    (fun hne0 => by
                      have hcnt0 : cnt = 0 := by
                        by_contra hnc; simp [hnc] at hne0
                      refine runs_seq_assign_le (by eval_expr) ?_
                      have hinner := divMod_inner_triple hShl hLt hRawSub hh hw1 hw2 hB hL hH
                        ha hb hqdst hrdst hnova hnovb hnovra hnovrb hnovqr hx hy
                        hla_le hcnt rfl hk_pos hk_le rfl
                      refine runs_triple_le hinner ?_ ?_ (by
                        dsimp only [stepCost, nBits]
                        simp only [hcnt0, ↓reduceIte, Nat.sub_zero]
                        rw [show 115 * L + 100 + 1 + 8 = 115 * L + 109 by omega]
                        wram_cost)
                      · refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
                          by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
                          by simp, by dsimp only [nBits]; simp [hcnt0, Function.update_self],
                          hfr, hlow_j, hdvd_j, q, r, hq, hr, hr_lt,
                          by rwa [divModShift_zero hcnt]⟩
                      · rintro o st' hpost_in
                        cases o with
                        | returned _ => exact False.elim hpost_in
                        | normal =>
                          rcases hpost_in with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
                            sfr, slow, q', r', hq', hr', hr'_lt, heuc'⟩
                          have hlow' : ∀ m < la - (cnt + 1), st'.mem (qDst + m) = 0 :=
                            fun m hm => slow m (by omega)
                          refine ⟨⟨by simp [s0], by simp [s1], by simp [s2], by simp [s3],
                            by simp [s4], by simp [s5], by simp [s6], by simp [s7],
                            by simp [s8], by simp, sfr, hlow', q', r', hq', hr', hr'_lt, ?_⟩, s9⟩
                          have hend := divModShift_end (la := la) (k := k) (h := h) (cnt := cnt)
                          simp only [hcnt0, ↓reduceIte] at hend heuc' ⊢
                          rwa [hend] at heuc')
                    (fun heq0 => by
                      have hcnt_ne : cnt ≠ 0 := by
                        intro h0; simp [h0] at heq0
                      refine runs_seq_nop_le ?_
                      have hinner := divMod_inner_triple hShl hLt hRawSub hh hw1 hw2 hB hL hH
                        ha hb hqdst hrdst hnova hnovb hnovra hnovrb hnovqr hx hy
                        hla_le hcnt rfl hk_pos hk_le rfl
                      refine runs_triple_le hinner ?_ ?_ (by
                        dsimp only [stepCost, nBits]
                        simp only [hcnt_ne, ↓reduceIte, Nat.sub_zero]
                        rw [show 115 * L + 100 + 1 + 8 = 115 * L + 109 by omega]
                        wram_cost)
                      · refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
                          by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
                          by simp, by dsimp only [nBits]; simp [hcnt_ne],
                          hfr, hlow_j, hdvd_j, q, r, hq, hr, hr_lt,
                          by rwa [divModShift_zero hcnt]⟩
                      · rintro o st' hpost_in
                        cases o with
                        | returned _ => exact False.elim hpost_in
                        | normal =>
                          rcases hpost_in with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
                            sfr, slow, q', r', hq', hr', hr'_lt, heuc'⟩
                          have hlow' : ∀ m < la - (cnt + 1), st'.mem (qDst + m) = 0 :=
                            fun m hm => slow m (by omega)
                          refine ⟨⟨by simp [s0], by simp [s1], by simp [s2], by simp [s3],
                            by simp [s4], by simp [s5], by simp [s6], by simp [s7],
                            by simp [s8], by simp, sfr, hlow', q', r', hq', hr', hr'_lt, ?_⟩, s9⟩
                          have hend := divModShift_end (la := la) (k := k) (h := h) (cnt := cnt)
                          simp only [hcnt_ne, ↓reduceIte] at hend heuc' ⊢
                          rwa [hend] at heuc')))
              (fun o st hq => by
                cases o with
                | returned u => exact False.elim hq
                | normal =>
                  rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, hfr, _, hqr⟩
                  exact ⟨hfr, hqr⟩)
          refine runs_seq_triple_le houter
            ⟨hmem_s, by simp [rs0], by simp [rs1], by simp [rs2], by simp [rs3],
              by simp [rs4], by simp [rs5], by simp [rs6], by simp [rs7],
              by dsimp only [k]; simp⟩ ?_
          rintro st_end ⟨hfr_end, q, r, hq_end, hr_end, hr_lt_end, heuc_end⟩
          have hrem_la : outerRem la k h la = 0 := by simp [outerRem, Nat.ne_of_gt hla_pos]
          rw [hrem_la, Nat.pow_zero, Nat.div_one, Nat.div_one] at heuc_end
          have hq_eq : q = x / y := by
            rw [heuc_end, Nat.mul_comm q y, Nat.mul_add_div hy_pos, Nat.div_eq_of_lt hr_lt_end, Nat.add_zero]
          have hr_eq : r = x % y := by
            rw [heuc_end, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
              Nat.mod_mod, Nat.mod_eq_of_lt hr_lt_end]
          rw [hq_eq] at hq_end
          rw [hr_eq] at hr_end
          refine runs_ret_le (by eval_expr)
            ⟨a, b', qDst, rDst, L, h, rfl, rfl, fun x' y' hx' hy' => by
              obtain rfl : x' = x := hx'.ext hx
              obtain rfl : y' = y := hy'.ext hy
              exact ⟨hq_end, hr_end⟩, hfr_end⟩ ?_
          have hrc := rangeCost_divMod k h (115 * L + 109) 27 la hla_pos
          dsimp only [mwDivModContract, mwZeroContract, mwIsZeroContract, mwBitLenContract, stepCost]
          rw [hbl_eq]
          have hk_mul_11 : 11 * k ≤ 11 * bitLen x := Nat.mul_le_mul_left 11 (by omega)
          have hbit_main : bitLen x * (115 * L + 109) + la * 27 + la * 9 ≤ bitLen x * (115 * L + 145) := by
            have h1 : bitLen x * (115 * L + 145) = bitLen x * (115 * L + 109) + bitLen x * 36 := by ring
            have h2 : la * 36 ≤ bitLen x * 36 := Nat.mul_le_mul_right 36 hla_bl
            omega
          have hL_ge : 1 ≤ L := Nat.le_trans hla_pos hla_le
          have hmul_280 : bitLen x * (115 * L + 145) + 11 * bitLen x ≤ bitLen x * (280 * L) := by
            have : 115 * L + 145 + 11 ≤ 280 * L := by omega
            have h1 : bitLen x * (115 * L + 145) + 11 * bitLen x = bitLen x * (115 * L + 145 + 11) := by ring
            rw [h1]
            exact Nat.mul_le_mul_left _ this
          have hlin_58 : 58 * L ≤ 280 * L := by omega
          have hadd_dist : 280 * L * (bitLen x + 1) = bitLen x * (280 * L) + 280 * L := by ring
          have hcomm : k + (la - 1) * h = bitLen x := by rw [hbl_form, Nat.add_comm]
          have hbl_top : bitLen top = k := rfl
          rw [hrc, hcomm, hbl_top, hadd_dist]
          simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
            argsSize_cons, argsSize_nil, Nat.sub_zero] at *
          omega)
        (fun heq_la => by
          have hla0 : la = 0 := heq_la
          have hx0 : x = 0 := by
            rw [hla_act] at hla0
            exact (activeLimbs_eq_zero_iff hx.lt_pow).mp hla0
          subst hx0
          refine runs_seq_nop_le ?_
          refine runs_ret_le (by eval_expr)
            ⟨a, b', qDst, rDst, L, h, rfl, rfl, fun x' y' hx' hy' => by
              obtain rfl : x' = 0 := hx'.ext hx
              obtain rfl : y' = y := hy'.ext hy
              have hq_0 : LimbsAt st_s.mem qDst L h 0 :=
                hq_zero2.congr fun m _ _ => by rw [hmem_s]
              have hr_0 : LimbsAt st_s.mem rDst L h 0 :=
                hr_zero2.congr fun m _ _ => by rw [hmem_s]
              simpa using ⟨hq_0, hr_0⟩,
              fun q' hnq hnr => by rw [hmem_s]; exact hfr_qr2 q' hnq hnr⟩ ?_
          dsimp only [mwDivModContract, mwZeroContract, mwIsZeroContract]
          rw [hbl_eq, bitLen_zero]
          wram_cost))

/-! ### Complete 18-procedure arithmetic module -/

/-- The full 18-procedure multiword arithmetic module placed at `base`:
* `0..12`: `arithBasicModule base`
* `13`: `mwBitLen (base + 13)`
* `14`: `mwMul base`
* `15`: `mwDivMod base`
* `16`: `mwShiftLeft base`
* `17`: `mwShiftRight base` -/
def arithModule (base : ℕ) : List Stmt :=
  arithBasicModule base ++
    [mwBitLen (base + idxBitLen), mwMul base, mwDivMod base, mwShiftLeft base, mwShiftRight base]

theorem arithModule_length (base : ℕ) : (arithModule base).length = 18 := rfl

theorem arithModule_noRand (base : ℕ) : ∀ s ∈ arithModule base, s.NoRand := by
  intro s hs
  simp only [arithModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | rfl | rfl | rfl | rfl | rfl
  · exact arithBasicModule_noRand base s hs
  · exact mwBitLen_noRand _
  · exact mwMul_noRand _
  · exact mwDivMod_noRand _
  · exact mwShiftLeft_noRand _
  · exact mwShiftRight_noRand _

theorem arithBasic_hasAt_of_arithModule {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    p.HasAt b (arithBasicModule b) := by
  intro k hk
  have h18 : k < (arithModule b).length := by
    rw [arithModule_length]; rw [arithBasicModule_length] at hk; omega
  have h := hp k h18
  simpa [arithModule, List.getElem_append_left hk] using h

theorem arithModule_procs_at {p : Program} {b k : ℕ}
    (hp : p.HasAt b (arithModule b)) (hk : k < (arithModule b).length) :
    p.procs[b + k]? = some (arithModule b)[k] :=
  hp k hk

theorem mwZero_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxZero) (mwZeroContract w) :=
  mwZero_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwCopy_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxCopy) (mwCopyContract w) :=
  mwCopy_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwIsZero_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxIsZero) (mwIsZeroContract w) :=
  mwIsZero_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwFromHost_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxFromHost) (mwFromHostContract w) :=
  mwFromHost_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwEq_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxEq) (mwEqContract w) :=
  mwEq_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwLt_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxLt) (mwLtContract w) :=
  mwLt_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwAnd_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxAnd) (mwBitOpContract w .and) :=
  mwAnd_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwOr_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxOr) (mwBitOpContract w .or) :=
  mwOr_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwXor_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxXor) (mwBitOpContract w .xor) :=
  mwXor_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwAdd_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxAdd) (mwAddContract w) :=
  mwAdd_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwRawSub_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxRawSub) (mwRawSubContract w) :=
  mwRawSub_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwSub_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxSub) (mwSubContract w) :=
  mwSub_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwShl1AddBit_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxShl1AddBit) (mwShl1AddBitContract w) :=
  mwShl1AddBit_of_module (arithBasic_hasAt_of_arithModule hp)

theorem mwBitLen_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxBitLen) (mwBitLenContract w) := by
  refine mwBitLen_meetsContract ?_
  have h := arithModule_procs_at hp (k := idxBitLen) (by rw [arithModule_length, idxBitLen]; decide)
  simp only [arithModule, idxBitLen] at h
  rw [List.getElem_append_right (by rw [arithBasicModule_length])] at h
  simpa [arithBasicModule_length, idxBitLen] using h

theorem mwMul_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxMul) (mwMulContract w) := by
  refine mwMul_meetsContract (mwZero_of_arithModule hp) ?_
  have h := arithModule_procs_at hp (k := idxMul) (by rw [arithModule_length, idxMul]; decide)
  simp only [arithModule, idxMul] at h
  rw [List.getElem_append_right (by rw [arithBasicModule_length]; omega)] at h
  simpa [arithBasicModule_length, idxMul] using h

theorem mwDivMod_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxDivMod) (mwDivModContract w) := by
  refine mwDivMod_meetsContract (mwZero_of_arithModule hp) (mwCopy_of_arithModule hp)
    (mwIsZero_of_arithModule hp) (mwLt_of_arithModule hp) (mwRawSub_of_arithModule hp)
    (mwShl1AddBit_of_arithModule hp) (mwBitLen_of_arithModule hp) ?_
  have h := arithModule_procs_at hp (k := idxDivMod) (by rw [arithModule_length, idxDivMod]; decide)
  simp only [arithModule, idxDivMod] at h
  rw [List.getElem_append_right (by rw [arithBasicModule_length]; omega)] at h
  simpa [arithBasicModule_length, idxDivMod] using h

theorem mwShiftLeft_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxShiftLeft) (mwShiftLeftContract w) := by
  refine mwShiftLeft_meetsContract (mwZero_of_arithModule hp) ?_
  have h := arithModule_procs_at hp (k := idxShiftLeft) (by rw [arithModule_length, idxShiftLeft]; decide)
  simp only [arithModule, idxShiftLeft] at h
  rw [List.getElem_append_right (by rw [arithBasicModule_length]; omega)] at h
  simpa [arithBasicModule_length, idxShiftLeft] using h

theorem mwShiftRight_of_arithModule {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithModule b)) :
    MeetsContract w p (b + idxShiftRight) (mwShiftRightContract w) := by
  refine mwShiftRight_meetsContract (mwZero_of_arithModule hp) ?_
  have h := arithModule_procs_at hp (k := idxShiftRight) (by rw [arithModule_length, idxShiftRight]; decide)
  simp only [arithModule, idxShiftRight] at h
  rw [List.getElem_append_right (by rw [arithBasicModule_length]; omega)] at h
  simpa [arithBasicModule_length, idxShiftRight] using h

end MinCostFlow.WideWord
