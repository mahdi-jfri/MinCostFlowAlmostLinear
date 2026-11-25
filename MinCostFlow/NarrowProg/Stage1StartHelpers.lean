module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.Scaling.VertexCompression
public import MinCostFlow.NarrowProg.TopBitLength
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import WordRAM.Std.LimbsBits

/-!
# Helper procedures for Stage 1 startup

This file implements and verifies four small second-layer procedures used by `stage1Start`:
1. `stage1Compress`: removes isolated vertices from `(pTail, pHead)`, writing compressed
   endpoints `(pCompTail, pCompHead)` matching `Circulation.compress` and returning `I.compress.n`,
   in `O(m + 1)` steps using zeroed `pLabels` from `Assn.free`.
2. `stage1DecLimbs`: subtracts `1` from a positive `n`-limb base-`2 ^ k` number in `O(n + 1)` steps.
3. `stage1PrepNegCosts`: copies nonnegative cost limb lists and decrements negative cost limb lists
   into fresh heap memory (disjoint from the input), in `O(m + ∑ len + 1)` steps.
4. `stage1PadCaps`: copies canonical capacity limb lists into fixed-width `K_cap`-limb zero-padded
   buffers, in `O(m * (K_cap + 1) + 1)` steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-! ### Shared list and `Assn.free` helpers -/

/-- Splitting `Assn.free base (m * L)` into `m` contiguous `L`-word zero blocks. -/
theorem free_mul_eq_prod (base m L : ℕ) :
    Assn.free base (m * L) =
      ∏ e ∈ Finset.range m, Assn.list (base + e * L) (List.replicate L 0) := by
  induction m with
  | zero => simp [Assn.free]
  | succ m ih =>
    rw [Nat.succ_mul, Assn.free_add', ih, Finset.prod_range_succ]
    rfl

/-- Appending trailing zero limbs preserves `Nat.ofDigits`. -/
theorem ofDigits_append_replicate_zero (B : ℕ) (xs : List ℕ) (r : ℕ) :
    Nat.ofDigits B (xs ++ List.replicate r 0) = Nat.ofDigits B xs := by
  rw [Nat.ofDigits_append]
  have hz : Nat.ofDigits B (List.replicate r 0) = 0 := by
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]
  rw [hz, Nat.mul_zero, Nat.add_zero]

/-- Padding a limb list to width `K` with trailing zero limbs. -/
def padLimbs (K : ℕ) (xs : List ℕ) : List ℕ :=
  xs ++ List.replicate (K - xs.length) 0

@[sep_len] theorem length_padLimbs {K : ℕ} {xs : List ℕ} (h : xs.length ≤ K) :
    (padLimbs K xs).length = K := by
  simp [padLimbs]; omega

theorem padLimbs_limbs {k K : ℕ} {xs : List ℕ} (hL : Limbs k xs) :
    Limbs k (padLimbs K xs) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · rw [List.mem_replicate.mp hx |>.2]; exact Nat.two_pow_pos k

theorem padLimbs_ofDigits (B K : ℕ) (xs : List ℕ) :
    Nat.ofDigits B (padLimbs K xs) = Nat.ofDigits B xs :=
  ofDigits_append_replicate_zero B xs (K - xs.length)

/-! ### 1. Second-layer vertex compression (`stage1Compress`) -/

private theorem scan_append {n : ℕ} (s : VertexLabels n) (l₁ l₂ : List (Fin n)) :
    s.scan (l₁ ++ l₂) = (s.scan l₁).scan l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih (s.encounter v)

private theorem scan_take_succ {n : ℕ} (s : VertexLabels n) (l : List (Fin n)) {i : ℕ}
    (hi : i < l.length) :
    s.scan (l.take (i + 1)) = (s.scan (l.take i)).encounter l[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, scan_append]
  rfl

private theorem set_ofFn_eq_ofFn_update {n : ℕ} (f : Fin n → ℕ) (v : Fin n) (x : ℕ) :
    (List.ofFn f).set v.val x = List.ofFn (Function.update f v x) := by
  apply List.ext_getElem (by simp)
  intro j hj _
  simp only [List.length_set, List.length_ofFn] at hj
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases heq : v.val = j
  · have hfin : (⟨j, hj⟩ : Fin n) = v := Fin.ext heq.symm
    simp [heq, hfin]
  · have hfin : (⟨j, hj⟩ : Fin n) ≠ v := fun h => heq (congrArg Fin.val h).symm
    simp [heq, Function.update_of_ne hfin]

/-- Second-layer vertex compression on `(pTail, pHead)` using a zero-initialized `n`-word
label table `pLabels`. Writes compressed endpoints into `(pCompTail, pCompHead)` and returns
`I.compress.n`. -/
wram_def stage1Compress (m, pTail, pHead, pCompTail, pCompHead, pLabels) {
  cnt := 0
  for e in 0 .. m {
    v := mem[pTail + e]
    if mem[pLabels + v] == 0 {
      cnt := cnt + 1
      mem[pLabels + v] := cnt
    }
  }
  for e in 0 .. m {
    v := mem[pHead + e]
    if mem[pLabels + v] == 0 {
      cnt := cnt + 1
      mem[pLabels + v] := cnt
    }
  }
  for e in 0 .. m {
    mem[pCompTail + e] := mem[pLabels + mem[pTail + e]] - 1
    mem[pCompHead + e] := mem[pLabels + mem[pHead + e]] - 1
  }
  return cnt
}

/-- Specification of `stage1Compress`. -/
def stage1CompressSpec (w : ℕ) : Spec (Circulation × List ℕ × List ℕ) where
  pre := fun (I, ctBuf, chBuf) args => ⨆ (pTail : ℕ) (pHead : ℕ) (pCompTail : ℕ)
      (pCompHead : ℕ) (pLabels : ℕ),
    ⌜args = [I.m, pTail, pHead, pCompTail, pCompHead, pLabels] ∧
      ctBuf.length = I.m ∧ chBuf.length = I.m ∧ 2 * I.m + 1 < 2 ^ w⌝ *
    Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
    Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
    Assn.list pCompTail ctBuf *
    Assn.list pCompHead chBuf *
    Assn.list pLabels (List.replicate I.n 0)
  post := fun (I, _, _) args v => ⨆ (pTail : ℕ) (pHead : ℕ) (pCompTail : ℕ)
      (pCompHead : ℕ) (pLabels : ℕ),
    ⌜args = [I.m, pTail, pHead, pCompTail, pCompHead, pLabels] ∧ v = I.compress.n⌝ *
    Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
    Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
    Assn.list pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
    Assn.list pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
    Assn.list pLabels (List.ofFn I.endpointLabels.table)

theorem stage1Compress_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1Compress) :
    Meets w p f ((stage1CompressSpec w).withCost fun x _ => 125 * x.1.m + 50) := by
  sep_enter ⟨I, ctBuf, chBuf⟩ with hct hch hw
  set tails := List.ofFn I.tail with htails_def
  set heads := List.ofFn I.head with hheads_def
  set tailVals := List.ofFn (fun e : Fin I.m => (I.tail e).val) with htailVals_def
  set headVals := List.ofFn (fun e : Fin I.m => (I.head e).val) with hheadVals_def
  set cTailVals := List.ofFn (fun e : Fin I.m => (I.compress.tail e).val) with hcTailVals_def
  set cHeadVals := List.ofFn (fun e : Fin I.m => (I.compress.head e).val) with hcHeadVals_def
  have htv_len : tailVals.length = I.m := by simp [htailVals_def]
  have hhv_len : headVals.length = I.m := by simp [hheadVals_def]
  have hrep_empty : List.replicate I.n 0 = List.ofFn (VertexLabels.empty I.n).table := by
    apply List.ext_getElem (by simp)
    intro i hi _; simp [VertexLabels.empty]
  rw [hrep_empty]
  sep_step
  -- Loop 1: scan tails
  sep_for (fun e (v : ℕ) =>
    let s := (VertexLabels.empty I.n).scan (tails.take e)
    ⟨[I.m, pTail, pHead, pCompTail, pCompHead, pLabels, s.count, e, v],
      e ≤ I.m, 34 * (I.m - e) + 82 * I.m + 35,
      [Assn.list pTail tailVals, Assn.list pHead headVals,
       Assn.list pCompTail ctBuf, Assn.list pCompHead chBuf,
       Assn.list pLabels (List.ofFn s.table)]⟩) with v
  · set s := (VertexLabels.empty I.n).scan (tails.take e) with hs_def
    have hi_t : e < tails.length := by rw [htails_def, List.length_ofFn]; exact hhi
    have hstep := scan_take_succ (VertexLabels.empty I.n) tails hi_t
    have hti : tails[e]'hi_t = I.tail ⟨e, hhi⟩ := by simp [htails_def]
    have htv : tailVals[e]'(by simp [htailVals_def]; exact hhi) = (I.tail ⟨e, hhi⟩).val := by
      simp [htailVals_def]
    have hcnt_le : s.count ≤ e := by
      have hle := (VertexLabels.empty I.n).scan_count_le (tails.take e)
      rw [← hs_def] at hle
      simp only [VertexLabels.empty, zero_add, List.length_take, htails_def, List.length_ofFn,
        Nat.min_eq_left (by omega : e ≤ I.m)] at hle
      exact hle
    have hlt_n : (I.tail ⟨e, hhi⟩).val < I.n := (I.tail ⟨e, hhi⟩).isLt
    sep_step
    sep_step
    · -- table (I.tail ⟨e, hhi⟩) = 0
      have hzero : s.table (I.tail ⟨e, hhi⟩) = 0 := by
        simpa [htv] using hcond
      have henc : (VertexLabels.empty I.n).scan (tails.take (e + 1)) =
          ⟨s.count + 1, Function.update s.table (I.tail ⟨e, hhi⟩) (s.count + 1)⟩ := by
        rw [hstep, hti]; simp [VertexLabels.encounter, hzero, ← hs_def]
      sep_run
      · rw [henc, htv, ← set_ofFn_eq_ofFn_update, hcnt]
      · rw [henc, hcnt]
    · -- table (I.tail ⟨e, hhi⟩) ≠ 0
      have hnz : s.table (I.tail ⟨e, hhi⟩) ≠ 0 := by
        simpa [htv] using hcond
      have henc : (VertexLabels.empty I.n).scan (tails.take (e + 1)) = s := by
        rw [hstep, hti]; simp [VertexLabels.encounter, hnz, ← hs_def]
      sep_run
      · rw [henc]
      · rw [henc]
  · -- After Loop 1: tails.take I.m = tails
    have htake_t : tails.take I.m = tails := List.take_of_length_le (by simp [htails_def])
    rw [htake_t]
    set s₁ := (VertexLabels.empty I.n).scan tails with hs₁_def
    have hs₁_cnt : s₁.count ≤ I.m := by
      have hle := (VertexLabels.empty I.n).scan_count_le tails
      simp only [VertexLabels.empty, zero_add, htails_def, List.length_ofFn] at hle
      exact hle
    -- Loop 2: scan heads
    sep_for (fun e (v : ℕ) =>
      let s := s₁.scan (heads.take e)
      ⟨[I.m, pTail, pHead, pCompTail, pCompHead, pLabels, s.count, e, v],
        e ≤ I.m, 34 * (I.m - e) + 38 * I.m + 20,
        [Assn.list pTail tailVals, Assn.list pHead headVals,
         Assn.list pCompTail ctBuf, Assn.list pCompHead chBuf,
         Assn.list pLabels (List.ofFn s.table)]⟩) with v
    · set s := s₁.scan (heads.take e) with hs_def
      have hi_h : e < heads.length := by rw [hheads_def, List.length_ofFn]; exact hhi
      have hstep := scan_take_succ s₁ heads hi_h
      have hhi_e : heads[e]'hi_h = I.head ⟨e, hhi⟩ := by simp [hheads_def]
      have hhv : headVals[e]'(by simp [hheadVals_def]; exact hhi) = (I.head ⟨e, hhi⟩).val := by
        simp [hheadVals_def]
      have hcnt_le : s.count ≤ I.m + e := by
        have hle := s₁.scan_count_le (heads.take e)
        rw [← hs_def] at hle
        simp only [List.length_take, hheads_def, List.length_ofFn,
          Nat.min_eq_left (by omega : e ≤ I.m)] at hle
        omega
      have hlt_n : (I.head ⟨e, hhi⟩).val < I.n := (I.head ⟨e, hhi⟩).isLt
      sep_step
      sep_step
      · have hzero : s.table (I.head ⟨e, hhi⟩) = 0 := by simpa [hhv] using hcond
        have henc : s₁.scan (heads.take (e + 1)) =
            ⟨s.count + 1, Function.update s.table (I.head ⟨e, hhi⟩) (s.count + 1)⟩ := by
          rw [hstep, hhi_e]; simp [VertexLabels.encounter, hzero, ← hs_def]
        sep_run
        · rw [henc, hhv, ← set_ofFn_eq_ofFn_update, hcnt]
        · rw [henc, hcnt]
      · have hnz : s.table (I.head ⟨e, hhi⟩) ≠ 0 := by simpa [hhv] using hcond
        have henc : s₁.scan (heads.take (e + 1)) = s := by
          rw [hstep, hhi_e]; simp [VertexLabels.encounter, hnz, ← hs_def]
        sep_run
        · rw [henc]
        · rw [henc]
    · -- After Loop 2: s₁.scan heads = I.endpointLabels
      have htake_h : heads.take I.m = heads := List.take_of_length_le (by simp [hheads_def])
      rw [htake_h]
      have hlabels_eq : s₁.scan heads = I.endpointLabels := by
        rw [hs₁_def, ← scan_append]; rfl
      rw [hlabels_eq]
      -- Loop 3: remap tail and head
      sep_for (fun e =>
        ⟨[I.m, pTail, pHead, pCompTail, pCompHead, pLabels, I.endpointLabels.count, e, v],
          e ≤ I.m, 28 * (I.m - e) + 5,
          [Assn.list pTail tailVals, Assn.list pHead headVals,
           Assn.list pCompTail (cTailVals.take e ++ ctBuf.drop e),
           Assn.list pCompHead (cHeadVals.take e ++ chBuf.drop e),
           Assn.list pLabels (List.ofFn I.endpointLabels.table)]⟩)
      · have htv : tailVals[e]'(by simp [htailVals_def]; exact hhi) = (I.tail ⟨e, hhi⟩).val := by
          simp [htailVals_def]
        have hhv : headVals[e]'(by simp [hheadVals_def]; exact hhi) = (I.head ⟨e, hhi⟩).val := by
          simp [hheadVals_def]
        have hlt_t : (I.tail ⟨e, hhi⟩).val < I.n := (I.tail ⟨e, hhi⟩).isLt
        have hlt_h : (I.head ⟨e, hhi⟩).val < I.n := (I.head ⟨e, hhi⟩).isLt
        have hct_len : (cTailVals.take e ++ ctBuf.drop e).length = I.m := by
          simp [hcTailVals_def, hct]; omega
        have hch_len : (cHeadVals.take e ++ chBuf.drop e).length = I.m := by
          simp [hcHeadVals_def, hch]; omega
        sep_run
        · simp only [List.getElem_ofFn]
          have hfin : (⟨tailVals[e], by rw [htv]; exact hlt_t⟩ : Fin I.n) = I.tail ⟨e, hhi⟩ :=
            Fin.ext htv
          rw [hfin]
          have hval : I.endpointLabels.table (I.tail ⟨e, hhi⟩) - 1 =
              cTailVals[e]'(by simp [hcTailVals_def]; exact hhi) := by
            simp [hcTailVals_def, Circulation.compress, Circulation.encodeVertex]
          rw [hval]
          exact set_take_append_drop (by simp [hcTailVals_def]; exact hhi)
            (by simp [hcTailVals_def, hct]) rfl
        · simp only [List.getElem_ofFn]
          have hfin : (⟨headVals[e], by rw [hhv]; exact hlt_h⟩ : Fin I.n) = I.head ⟨e, hhi⟩ :=
            Fin.ext hhv
          rw [hfin]
          have hval : I.endpointLabels.table (I.head ⟨e, hhi⟩) - 1 =
              cHeadVals[e]'(by simp [hcHeadVals_def]; exact hhi) := by
            simp [hcHeadVals_def, Circulation.compress, Circulation.encodeVertex]
          rw [hval]
          exact set_take_append_drop (by simp [hcHeadVals_def]; exact hhi)
            (by simp [hcHeadVals_def, hch]) rfl
      · rw [List.take_of_length_le (by simp [hcTailVals_def]),
            List.drop_of_length_le (by omega), List.append_nil,
            List.take_of_length_le (by simp [hcHeadVals_def]),
            List.drop_of_length_le (by omega), List.append_nil]
        sep_run

theorem stage1Compress_meetsO {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1Compress) :
    MeetsO w p f (stage1CompressSpec w) fun x _ => x.1.m + 1 :=
  MeetsO.of_meets (stage1Compress_meets hp) ⟨125, fun _ => by dsimp only; omega⟩

/-! ### 2. Decrementing a positive long number (`stage1DecLimbs`) -/

/-- One step of subtracting `1` from `xs` in base `2 ^ k` with incoming borrow `b ∈ {0, 1}`. -/
def decStep (k : ℕ) (xs : List ℕ) (i b : ℕ) : ℕ × ℕ :=
  if b = 0 then (xs.getD i 0, 0)
  else if 0 < xs.getD i 0 then (xs.getD i 0 - 1, 0)
  else (2 ^ k - 1, 1)

/-- Partial decrement run starting with borrow `1`. -/
def decRun (k : ℕ) (xs : List ℕ) : ℕ → List ℕ × ℕ
  | 0 => ([], 1)
  | i + 1 =>
    let prev := decRun k xs i
    let step := decStep k xs i prev.2
    (prev.1 ++ [step.1], step.2)

@[sep_len] theorem length_decRun (k : ℕ) (xs : List ℕ) (i : ℕ) :
    (decRun k xs i).1.length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [decRun, ih]

/-- The decremented limb list. -/
def decLimbs (k : ℕ) (xs : List ℕ) : List ℕ := (decRun k xs xs.length).1

@[sep_len] theorem length_decLimbs (k : ℕ) (xs : List ℕ) :
    (decLimbs k xs).length = xs.length := length_decRun k xs xs.length

theorem decRun_spec {k : ℕ} (hk : 1 ≤ k) {xs : List ℕ} (hL : Limbs k xs) :
    ∀ i ≤ xs.length,
      Nat.ofDigits (2 ^ k) (decRun k xs i).1 + 1 =
        Nat.ofDigits (2 ^ k) (xs.take i) + (decRun k xs i).2 * (2 ^ k) ^ i ∧
      (decRun k xs i).2 ≤ 1 ∧ Limbs k (decRun k xs i).1 := by
  intro i
  induction i with
  | zero => intro _; simp [decRun, Limbs]
  | succ i ih =>
    intro hi
    obtain ⟨hv, hb, hLi⟩ := ih (by omega)
    have hB : 2 ≤ 2 ^ k := two_le_pow hk
    have hlen := length_decRun k xs i
    have hxi : xs.getD i 0 < 2 ^ k := hL.getD_lt i
    simp only [decRun, decStep]
    set B := 2 ^ k
    set L := (decRun k xs i).1
    set b := (decRun k xs i).2
    by_cases hb0 : b = 0
    · simp only [hb0, ↓reduceIte]
      refine ⟨?_, by omega, hLi.append hxi⟩
      rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ofDigits_take_succ B (by omega)]
      rw [hb0, Nat.zero_mul, Nat.add_zero] at hv
      omega
    · have hb1 : b = 1 := by omega
      by_cases hx0 : 0 < xs.getD i 0
      · simp only [hb0, ↓reduceIte, hx0]
        refine ⟨?_, by omega, hLi.append (by omega)⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ofDigits_take_succ B (by omega)]
        rw [hb1, Nat.one_mul] at hv
        have hsub : B ^ i * (xs.getD i 0 - 1) + B ^ i = B ^ i * xs.getD i 0 := by
          cases h : xs.getD i 0 with
          | zero => omega
          | succ m => simp [Nat.mul_succ]
        linarith
      · simp only [hb0, ↓reduceIte, hx0]
        refine ⟨?_, by omega, hLi.append (by omega)⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ofDigits_take_succ B (by omega)]
        have hxz : xs.getD i 0 = 0 := by omega
        rw [hb1, Nat.one_mul] at hv
        rw [hxz, Nat.mul_zero, Nat.add_zero, pow_succ, Nat.one_mul]
        have hmul : B ^ i * (B - 1) + B ^ i = B ^ i * B := by
          have : 1 ≤ B := by omega
          calc B ^ i * (B - 1) + B ^ i = B ^ i * ((B - 1) + 1) := by ring
            _ = B ^ i * B := by rw [Nat.sub_add_cancel this]
        linarith

theorem decLimbs_ofDigits {k : ℕ} (hk : 1 ≤ k) {xs : List ℕ} (hL : Limbs k xs)
    (hpos : 0 < Nat.ofDigits (2 ^ k) xs) :
    (decRun k xs xs.length).2 = 0 ∧
    Nat.ofDigits (2 ^ k) (decLimbs k xs) = Nat.ofDigits (2 ^ k) xs - 1 ∧
    Limbs k (decLimbs k xs) := by
  obtain ⟨hv, hb, hLd⟩ := decRun_spec hk hL xs.length le_rfl
  rw [List.take_length] at hv
  have hlt : Nat.ofDigits (2 ^ k) (decLimbs k xs) < (2 ^ k) ^ xs.length := by
    have := ofDigits_lt_pow hLd
    rw [length_decRun, pow_mul] at this
    exact this
  have hlt' : Nat.ofDigits (2 ^ k) (decRun k xs xs.length).1 < (2 ^ k) ^ xs.length := hlt
  have hb0 : (decRun k xs xs.length).2 = 0 := by
    by_contra hne
    have hb1 : (decRun k xs xs.length).2 = 1 := by omega
    rw [hb1, Nat.one_mul] at hv
    omega
  rw [hb0, Nat.zero_mul, Nat.add_zero] at hv
  exact ⟨hb0, by change Nat.ofDigits (2 ^ k) (decRun k xs xs.length).1 = _; omega, hLd⟩

/-- Subtract `1` from a positive `n`-limb base-`2 ^ k` number at `src`, writing into `dst`. -/
wram_def stage1DecLimbs (src, dst, n, k) {
  B := 1 <<< k
  borrow := 1
  for i in 0 .. n {
    x := mem[src + i]
    if borrow == 0 {
      mem[dst + i] := x
    } else {
      if 0 < x {
        mem[dst + i] := x - 1
        borrow := 0
      } else {
        mem[dst + i] := B - 1
      }
    }
  }
  return borrow
}

/-- Specification of `stage1DecLimbs`. -/
def stage1DecLimbsSpec (w : ℕ) : Spec (ℕ × List ℕ × List ℕ) where
  pre := fun (k, xs, zs) args => ⨆ (src : ℕ) (dst : ℕ),
    ⌜args = [src, dst, xs.length, k] ∧ zs.length = xs.length ∧
      Limbs k xs ∧ 0 < Nat.ofDigits (2 ^ k) xs ∧ 1 ≤ k ∧ 2 * k ≤ w⌝ *
    Assn.list src xs * Assn.list dst zs
  post := fun (k, xs, _) args v => ⨆ (src : ℕ) (dst : ℕ),
    ⌜args = [src, dst, xs.length, k] ∧ v = 0 ∧
      Limbs k (decLimbs k xs) ∧
      Nat.ofDigits (2 ^ k) (decLimbs k xs) = Nat.ofDigits (2 ^ k) xs - 1⌝ *
    Assn.list src xs * Assn.list dst (decLimbs k xs)

theorem stage1DecLimbs_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1DecLimbs) :
    Meets w p f ((stage1DecLimbsSpec w).withCost fun x _ => 55 * x.2.1.length + 25) := by
  sep_enter ⟨k, xs, zs⟩ with hzs hL hpos hk h2k
  have h2b := two_le_pow hk
  have h2bw := pow_lt_pow_w hk h2k
  have hrun := decRun_spec hk hL
  sep_step
  sep_step
  sep_for (fun i (x : ℕ) =>
    ⟨[src, dst, xs.length, k, 2 ^ k, (decRun k xs i).2, i, x],
      i ≤ xs.length, 45 * (xs.length - i) + 5,
      [Assn.list src xs, Assn.list dst ((decRun k xs i).1 ++ zs.drop i)]⟩) with x
  · obtain ⟨_, hb, _⟩ := hrun i (by omega)
    have hxi : xs[i]'(by omega) = xs.getD i 0 := (List.getD_eq_getElem _ _ _).symm
    have hxl := hL.getD_lt i
    have hlen := length_append_drop (zs := zs) (length_decRun k xs i) (by omega)
    sep_step
    sep_step
    · -- borrow = 0
      have h1 : (decRun k xs (i + 1)).1 = (decRun k xs i).1 ++ [xs.getD i 0] := by
        simp only [decRun, decStep, hcond, ↓reduceIte]
      have h2 : (decRun k xs (i + 1)).2 = 0 := by simp only [decRun, decStep, hcond, ↓reduceIte]
      sep_run
      rw [h1, hxi, set_append_drop (length_decRun k xs i) (by omega)]
    · -- borrow ≠ 0
      sep_step
      · -- 0 < x
        have hpos_i : 0 < xs.getD i 0 := by rw [← hxi]; exact hcond_1
        have h1 : (decRun k xs (i + 1)).1 = (decRun k xs i).1 ++ [xs.getD i 0 - 1] := by
          simp only [decRun, decStep, hcond, hpos_i, ↓reduceIte]
        have h2 : (decRun k xs (i + 1)).2 = 0 := by
          simp only [decRun, decStep, hcond, hpos_i, ↓reduceIte]
        sep_run
        rw [h1, hxi, set_append_drop (length_decRun k xs i) (by omega)]
      · -- x = 0
        have hzero : ¬ 0 < xs.getD i 0 := by rw [← hxi]; omega
        have h1 : (decRun k xs (i + 1)).1 = (decRun k xs i).1 ++ [2 ^ k - 1] := by
          simp only [decRun, decStep, hcond, hzero, ↓reduceIte]
        have h2 : (decRun k xs (i + 1)).2 = 1 := by
          simp only [decRun, decStep, hcond, hzero, ↓reduceIte]
        sep_run
        rw [h1, set_append_drop (length_decRun k xs i) (by omega)]
  · obtain ⟨hb0, hval, hLd⟩ := decLimbs_ofDigits hk hL hpos
    have hrun' : (decRun k xs xs.length).1 ++ zs.drop xs.length = decLimbs k xs := by
      rw [List.drop_of_length_le (by omega), List.append_nil]; rfl
    rw [hrun']
    sep_run

theorem stage1DecLimbs_meetsO {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1DecLimbs) :
    MeetsO w p f (stage1DecLimbsSpec w) fun x _ => x.2.1.length + 1 :=
  MeetsO.of_meets (stage1DecLimbs_meets hp) ⟨55, fun _ => by dsimp only; omega⟩

/-! ### 3. Precomputing adjusted cost limbs (`stage1PrepNegCosts`) -/

/-- The adjusted limb list for edge `e`: `decLimbs k l` if `cost < 0`, else `l`. -/
def adjCostLimbList (k : ℕ) (isNeg : Bool) (l : List ℕ) : List ℕ :=
  if isNeg then decLimbs k l else l

@[sep_len] theorem length_adjCostLimbList (k : ℕ) (isNeg : Bool) (l : List ℕ) :
    (adjCostLimbList k isNeg l).length = l.length := by
  unfold adjCostLimbList; split <;> simp [length_decLimbs]

/-- Prefix pointer offsets for storing `costLimbs` contiguously starting at `h`. -/
def costPrefixSum (costLimbs : List (List ℕ)) (i : ℕ) : ℕ :=
  ((costLimbs.take i).map List.length).sum

theorem costPrefixSum_zero (costLimbs : List (List ℕ)) : costPrefixSum costLimbs 0 = 0 := rfl

theorem costPrefixSum_succ (costLimbs : List (List ℕ)) {i : ℕ} (hi : i < costLimbs.length) :
    costPrefixSum costLimbs (i + 1) = costPrefixSum costLimbs i + (costLimbs.getD i []).length := by
  unfold costPrefixSum
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ hi]

theorem costPrefixSum_le_total (costLimbs : List (List ℕ)) (i : ℕ) :
    costPrefixSum costLimbs i ≤ (costLimbs.map List.length).sum := by
  unfold costPrefixSum
  have hsub := (List.take_sublist i costLimbs).map List.length
  exact hsub.sum_le_sum (fun _ _ => Nat.zero_le _)

/-- Copy nonnegative cost limbs and decrement negative cost limbs into fresh heap memory at `h`. -/
wram_def stage1PrepNegCosts (decIdx copyIdx : ℕ)
    (m, k, pCostSign, pCostPtrs, pCostLens, pAdjCostPtrs, h) {
  cur := h
  for e in 0 .. m {
    s := mem[pCostSign + e]
    src := mem[pCostPtrs + e]
    len := mem[pCostLens + e]
    mem[pAdjCostPtrs + e] := cur
    if s == 1 {
      r := decIdx(src, cur, len, k)
    } else {
      r := copyIdx(src, cur, len)
    }
    cur := cur + len
  }
  return cur
}

/-- Specification of `stage1PrepNegCosts`. -/
def stage1PrepNegCostsSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ) where
  pre := fun (I, k, costPtrs, costLimbs, adjPtrBuf) args =>
    ⨆ (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ) (pAdjCostPtrs : ℕ) (h : ℕ),
      ⌜args = [I.m, k, pCostSign, pCostPtrs, pCostLens, pAdjCostPtrs, h] ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧ adjPtrBuf.length = I.m ∧
        (∀ j (hj : j < I.m), Limbs k (costLimbs.getD j []) ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧
        h + (costLimbs.map List.length).sum < 2 ^ w⌝ *
      Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list pCostPtrs costPtrs *
      Assn.list pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list pAdjCostPtrs adjPtrBuf *
      Assn.free h (2 ^ w - h)
  post := fun (I, k, costPtrs, costLimbs, _) args h' =>
    ⨆ (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ) (pAdjCostPtrs : ℕ) (h : ℕ),
      let adjPtrs : List ℕ := List.ofFn fun e : Fin I.m => h + costPrefixSum costLimbs e.val
      let adjLimbs : List (List ℕ) := List.ofFn fun e : Fin I.m =>
        adjCostLimbList k (decide (I.cost e < 0)) (costLimbs.getD e.val [])
      ⌜args = [I.m, k, pCostSign, pCostPtrs, pCostLens, pAdjCostPtrs, h] ∧
        h' = h + (costLimbs.map List.length).sum ∧
        (∀ j (hj : j < I.m), Limbs k (adjLimbs.getD j []) ∧
          (adjLimbs.getD j []).length = (costLimbs.getD j []).length ∧
          Nat.ofDigits (2 ^ k) (adjLimbs.getD j []) =
            if I.cost ⟨j, hj⟩ < 0 then (I.cost ⟨j, hj⟩).natAbs - 1 else (I.cost ⟨j, hj⟩).natAbs)⌝ *
      Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list pCostPtrs costPtrs *
      Assn.list pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list pAdjCostPtrs adjPtrs *
      (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) *
      Assn.free h' (2 ^ w - h')

theorem stage1PrepNegCosts_meets {w : ℕ} {p : Program} {f decIdx copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1PrepNegCosts decIdx copyIdx))
    (hdec : Meets w p decIdx ((stage1DecLimbsSpec w).withCost fun x _ => 55 * x.2.1.length + 25))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    Meets w p f ((stage1PrepNegCostsSpec w).withCost fun x _ =>
      95 * x.1.m + 55 * (x.2.2.2.1.map List.length).sum + 25) := by
  sep_enter ⟨I, k, costPtrs, costLimbs, adjPtrBuf⟩ with hcp hcl hab hclSpec hk h2k hsp
  have h2b := two_le_pow hk
  have h2bw := pow_lt_pow_w hk h2k
  set signVals := List.ofFn (fun e : Fin I.m => if I.cost e < 0 then 1 else 0) with hsignVals_def
  set totalLen := (costLimbs.map List.length).sum with htotalLen_def
  set adjPtrs : List ℕ := List.ofFn fun e : Fin I.m => h + costPrefixSum costLimbs e.val with hadjPtrs_def
  set adjLimbs : List (List ℕ) := List.ofFn fun e : Fin I.m =>
    adjCostLimbList k (decide (I.cost e < 0)) (costLimbs.getD e.val []) with hadjLimbs_def
  sep_step
  sep_for (fun e (tmp : ℕ × ℕ × ℕ × ℕ) =>
    let cur := h + costPrefixSum costLimbs e
    ⟨[I.m, k, pCostSign, pCostPtrs, pCostLens, pAdjCostPtrs, h, cur, e,
      tmp.1, tmp.2.1, tmp.2.2.1, tmp.2.2.2],
      e ≤ I.m,
      85 * (I.m - e) + 55 * (totalLen - costPrefixSum costLimbs e) + 5,
      [Assn.list pCostSign signVals,
       Assn.list pCostPtrs costPtrs,
       Assn.list pCostLens (costLimbs.map List.length),
       ∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []),
       Assn.list pAdjCostPtrs (adjPtrs.take e ++ adjPtrBuf.drop e),
       ∏ j ∈ Finset.range e, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j []),
       Assn.free cur (2 ^ w - cur)]⟩) with ⟨s, src, len, r⟩
  · have hmem : e ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    have hps_le : costPrefixSum costLimbs e ≤ totalLen := costPrefixSum_le_total costLimbs e
    have hps_succ := costPrefixSum_succ costLimbs (by omega : e < costLimbs.length)
    have hps_succ_le : costPrefixSum costLimbs (e + 1) ≤ totalLen :=
      costPrefixSum_le_total costLimbs (e + 1)
    have hlen_i : (costLimbs.map List.length)[e]'(by simp; omega) =
        (costLimbs.getD e []).length := by
      rw [List.getElem_map, List.getD_eq_getElem _ _ (by omega : e < costLimbs.length)]
    have hptr_i : costPtrs[e]'(by omega) = costPtrs.getD e 0 :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    have hsign_i : signVals[e]'(by simp [hsignVals_def]; exact hhi) =
        if I.cost ⟨e, hhi⟩ < 0 then 1 else 0 := by simp [hsignVals_def]
    have hadjPtr_i : adjPtrs[e]'(by simp [hadjPtrs_def]; exact hhi) =
        h + costPrefixSum costLimbs e := by simp [hadjPtrs_def]
    have hadjPtr_getD : adjPtrs.getD e 0 = h + costPrefixSum costLimbs e := by
      rw [List.getD_eq_getElem _ _ (by simp [hadjPtrs_def]; exact hhi), hadjPtr_i]
    have hadjLimb_getD : adjLimbs.getD e [] =
        adjCostLimbList k (decide (I.cost ⟨e, hhi⟩ < 0)) (costLimbs.getD e []) := by
      rw [List.getD_eq_getElem _ _ (by simp [hadjLimbs_def]; exact hhi)]
      simp [hadjLimbs_def]
    have hfree_split :
        Assn.free (h + costPrefixSum costLimbs e) (2 ^ w - (h + costPrefixSum costLimbs e)) =
        Assn.list (h + costPrefixSum costLimbs e) (List.replicate (costLimbs.getD e []).length 0) *
        Assn.free (h + costPrefixSum costLimbs (e + 1))
          (2 ^ w - (h + costPrefixSum costLimbs (e + 1))) := by
      have hsub : 2 ^ w - (h + costPrefixSum costLimbs e) =
          (costLimbs.getD e []).length + (2 ^ w - (h + costPrefixSum costLimbs (e + 1))) := by
        omega
      rw [hsub, Assn.free_add', Assn.free]
      rw [show h + costPrefixSum costLimbs e + (costLimbs.getD e []).length =
          h + costPrefixSum costLimbs (e + 1) by omega]
    have hsign_len : signVals.length = I.m := by simp [hsignVals_def]
    have hadj_len : (adjPtrs.take e ++ adjPtrBuf.drop e).length = I.m := by
      simp [hadjPtrs_def, hab]; omega
    obtain ⟨hLi, hvali⟩ := hclSpec e hhi
    sep_step; sep_step; sep_step; sep_step
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))
    sep_apply hfree_split
    sep_step
    · -- s == 1: negative cost
      have hneg : I.cost ⟨e, hhi⟩ < 0 := by
        rw [hsign_i] at hcond; split_ifs at hcond with hlt; exact hlt
      have hpos : 0 < Nat.ofDigits (2 ^ k) (costLimbs.getD e []) := by rw [hvali]; omega
      sep_step from (k, costLimbs.getD e [], List.replicate (costLimbs.getD e []).length 0)
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))).symm
      have hprod_succ :
          (∏ j ∈ Finset.range e, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) *
            Assn.list (h + costPrefixSum costLimbs e) (decLimbs k (costLimbs.getD e [])) =
          ∏ j ∈ Finset.range (e + 1), Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j []) := by
        rw [Finset.prod_range_succ, hadjPtr_getD, hadjLimb_getD]
        simp [adjCostLimbList, hneg]
      sep_apply hprod_succ
      sep_run
      rw [← hadjPtr_i]
      exact set_take_append_drop (by simp [hadjPtrs_def]; exact hhi)
        (by simp [hadjPtrs_def, hab]) rfl
    · -- s ≠ 1: nonnegative cost
      have hnonneg : ¬ (I.cost ⟨e, hhi⟩ < 0) := by
        rw [hsign_i] at hcond
        by_cases hlt : I.cost ⟨e, hhi⟩ < 0
        · simp [hlt] at hcond
        · exact hlt
      sep_step from (costLimbs.getD e [], List.replicate (costLimbs.getD e []).length 0)
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))).symm
      have hprod_succ :
          (∏ j ∈ Finset.range e, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) *
            Assn.list (h + costPrefixSum costLimbs e) (costLimbs.getD e []) =
          ∏ j ∈ Finset.range (e + 1), Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j []) := by
        rw [Finset.prod_range_succ, hadjPtr_getD, hadjLimb_getD]
        simp [adjCostLimbList, hnonneg]
      sep_apply hprod_succ
      sep_run
      rw [← hadjPtr_i]
      exact set_take_append_drop (by simp [hadjPtrs_def]; exact hhi)
        (by simp [hadjPtrs_def, hab]) rfl
  · have hps_end : costPrefixSum costLimbs I.m = totalLen := by
      simp [costPrefixSum, totalLen, List.take_of_length_le (show costLimbs.length ≤ I.m by omega)]
    rw [hps_end, List.take_of_length_le (by simp [hadjPtrs_def]),
        List.drop_of_length_le (by omega), List.append_nil]
    sep_run
    intro j hj
    obtain ⟨hLj, hvalj⟩ := hclSpec j hj
    have hadj_j : adjLimbs.getD j [] =
        adjCostLimbList k (decide (I.cost ⟨j, hj⟩ < 0)) (costLimbs.getD j []) := by
      rw [List.getD_eq_getElem _ _ (by simp [hadjLimbs_def]; exact hj)]
      simp [hadjLimbs_def]
    rw [hadj_j]
    by_cases hneg : I.cost ⟨j, hj⟩ < 0
    · simp only [adjCostLimbList, hneg, decide_true, ↓reduceIte, length_decLimbs]
      have hpos : 0 < Nat.ofDigits (2 ^ k) (costLimbs.getD j []) := by rw [hvalj]; omega
      obtain ⟨_, hdv, hdL⟩ := decLimbs_ofDigits hk hLj hpos
      exact ⟨hdL, trivial, by rw [hdv, hvalj]⟩
    · simp only [adjCostLimbList, hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hLj, trivial, hvalj⟩
  · simp only [costPrefixSum_zero, Finset.prod_range_zero, Nat.add_zero, one_mul]
    sep_entail

theorem stage1PrepNegCosts_meetsO {w : ℕ} {p : Program} {f decIdx copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1PrepNegCosts decIdx copyIdx))
    (hdec : Meets w p decIdx ((stage1DecLimbsSpec w).withCost fun x _ => 55 * x.2.1.length + 25))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    MeetsO w p f (stage1PrepNegCostsSpec w) fun x _ =>
      x.1.m + (x.2.2.2.1.map List.length).sum + 1 :=
  MeetsO.of_meets (stage1PrepNegCosts_meets hp hdec hcopy) ⟨95, fun _ => by dsimp only; omega⟩

/-! ### 4. Small fixed-size header writers (`stage1Write8`, `stage1Write9`) -/

/-- Write an 8-word slice `[a0..a7]` at `dst`. -/
wram_def stage1Write8 (dst, a0, a1, a2, a3, a4, a5, a6, a7) {
  mem[dst] := a0
  mem[dst + 1] := a1
  mem[dst + 2] := a2
  mem[dst + 3] := a3
  mem[dst + 4] := a4
  mem[dst + 5] := a5
  mem[dst + 6] := a6
  mem[dst + 7] := a7
  return 0
}

def stage1Write8Spec (w : ℕ) : Spec (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) where
  pre := fun (a0, a1, a2, a3, a4, a5, a6, a7) args => ⨆ dst : ℕ,
    ⌜args = [dst, a0, a1, a2, a3, a4, a5, a6, a7] ∧ 7 < 2 ^ w⌝ *
    Assn.list dst (List.replicate 8 0)
  post := fun (a0, a1, a2, a3, a4, a5, a6, a7) args v => ⨆ dst : ℕ,
    ⌜args = [dst, a0, a1, a2, a3, a4, a5, a6, a7] ∧ v = 0⌝ *
    Assn.list dst [a0, a1, a2, a3, a4, a5, a6, a7]

theorem stage1Write8_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1Write8) :
    Meets w p f ((stage1Write8Spec w).withCost fun _ _ => 70) := by
  sep_enter ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ with hw
  sep_run

/-- Write a 9-word slice `[a0..a8]` at `dst`. -/
wram_def stage1Write9 (dst, a0, a1, a2, a3, a4, a5, a6, a7, a8) {
  mem[dst] := a0
  mem[dst + 1] := a1
  mem[dst + 2] := a2
  mem[dst + 3] := a3
  mem[dst + 4] := a4
  mem[dst + 5] := a5
  mem[dst + 6] := a6
  mem[dst + 7] := a7
  mem[dst + 8] := a8
  return 0
}

def stage1Write9Spec (w : ℕ) : Spec (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) where
  pre := fun (a0, a1, a2, a3, a4, a5, a6, a7, a8) args => ⨆ dst : ℕ,
    ⌜args = [dst, a0, a1, a2, a3, a4, a5, a6, a7, a8] ∧ 8 < 2 ^ w⌝ *
    Assn.list dst (List.replicate 9 0)
  post := fun (a0, a1, a2, a3, a4, a5, a6, a7, a8) args v => ⨆ dst : ℕ,
    ⌜args = [dst, a0, a1, a2, a3, a4, a5, a6, a7, a8] ∧ v = 0⌝ *
    Assn.list dst [a0, a1, a2, a3, a4, a5, a6, a7, a8]

theorem stage1Write9_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1Write9) :
    Meets w p f ((stage1Write9Spec w).withCost fun _ _ => 80) := by
  sep_enter ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ with hw
  sep_run

end MinCostFlow.NarrowProg.Stage1
