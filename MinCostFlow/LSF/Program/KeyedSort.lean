module

public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.DynSpanner.Program.SortOps

import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Recursive Multi-Limb Keyed Merge Sort

Implements and verifies `keyedMergeSortStmt`, sorting an index slice `arr[lo..hi)` by
multi-limb unsigned keys stored at `keys + idx * L_key` using `unsignedLessContract` and a
disjoint scratch array of length `hi - lo` in `O((hi - lo) * (log(hi - lo) + 1) * L_key)` steps.
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow.Num

@[expose] public section

/-! ## Pure Keyed Merge and Memory Slices -/

/-- Pure merge of index lists `xs` and `ys` by unsigned key `key`. -/
def keyedMerge (key : ℕ → ℕ) : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' =>
    if key y < key x then y :: keyedMerge key (x :: xs') ys'
    else x :: keyedMerge key xs' (y :: ys')

lemma keyedMerge_perm (key : ℕ → ℕ) :
    ∀ xs ys : List ℕ, List.Perm (keyedMerge key xs ys) (xs ++ ys)
  | [], ys => by simp [keyedMerge]
  | x :: xs', [] => by simp [keyedMerge]
  | x :: xs', y :: ys' => by
    unfold keyedMerge
    split_ifs
    · exact List.Perm.trans (List.Perm.cons y (keyedMerge_perm key (x :: xs') ys'))
        List.perm_middle.symm
    · exact List.Perm.cons x (keyedMerge_perm key xs' (y :: ys'))

lemma keyedMerge_mem (key : ℕ → ℕ) (xs ys : List ℕ) (z : ℕ) :
    z ∈ keyedMerge key xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  simpa using (keyedMerge_perm key xs ys).mem_iff

lemma keyedMerge_pairwise (key : ℕ → ℕ) :
    ∀ {xs ys : List ℕ},
      xs.Pairwise (fun a b => key a ≤ key b) →
      ys.Pairwise (fun a b => key a ≤ key b) →
      (keyedMerge key xs ys).Pairwise (fun a b => key a ≤ key b)
  | [], ys, _, hys => by simpa [keyedMerge] using hys
  | x :: xs', [], hxs, _ => by simpa [keyedMerge] using hxs
  | x :: xs', y :: ys', hxs, hys => by
    unfold keyedMerge
    have hxs_tail := (List.pairwise_cons.mp hxs).2
    have hys_tail := (List.pairwise_cons.mp hys).2
    have hxs_hd := (List.pairwise_cons.mp hxs).1
    have hys_hd := (List.pairwise_cons.mp hys).1
    split_ifs with hyx
    · refine List.pairwise_cons.mpr ⟨?_, keyedMerge_pairwise key hxs hys_tail⟩
      intro z hz
      rw [keyedMerge_mem] at hz
      simp only [List.mem_cons] at hz
      rcases hz with (rfl | hz) | hz
      · omega
      · have := hxs_hd z hz; omega
      · exact hys_hd z hz
    · refine List.pairwise_cons.mpr ⟨?_, keyedMerge_pairwise key hxs_tail hys⟩
      intro z hz
      rw [keyedMerge_mem] at hz
      simp only [List.mem_cons] at hz
      rcases hz with hz | (rfl | hz)
      · exact hxs_hd z hz
      · omega
      · have := hys_hd z hz; omega

/-- Read `len` consecutive words from `mem` starting at `base`. -/
def memSlice (mem : ℕ → ℕ) (base len : ℕ) : List ℕ :=
  (List.range len).map fun i => mem (base + i)

lemma memSlice_length (mem : ℕ → ℕ) (base len : ℕ) :
    (memSlice mem base len).length = len := by
  simp [memSlice]

lemma memSlice_getElem (mem : ℕ → ℕ) (base len i : ℕ) (hi : i < (memSlice mem base len).length) :
    (memSlice mem base len)[i] = mem (base + i) := by
  simp [memSlice]

lemma memSlice_eq_of_agree {mem₁ mem₂ : ℕ → ℕ} {base len : ℕ}
    (h : ∀ i < len, mem₁ (base + i) = mem₂ (base + i)) :
    memSlice mem₁ base len = memSlice mem₂ base len := by
  refine List.ext_getElem (by simp [memSlice_length]) fun i hi _ => ?_
  simp only [memSlice, List.getElem_map, List.getElem_range]
  exact h i (by simpa [memSlice] using hi)

lemma memSlice_split (mem : ℕ → ℕ) (a lo mid hi : ℕ) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    memSlice mem (a + lo) (hi - lo) =
      memSlice mem (a + lo) (mid - lo) ++ memSlice mem (a + mid) (hi - mid) := by
  refine List.ext_getElem (by simp [memSlice_length]; omega) fun i hi₁ _ => ?_
  simp only [memSlice_length] at hi₁
  by_cases him : i < mid - lo
  · have him' : i < (memSlice mem (a + lo) (mid - lo)).length := by
      simpa [memSlice_length] using him
    rw [List.getElem_append_left him', memSlice_getElem, memSlice_getElem]
  · have hge : (memSlice mem (a + lo) (mid - lo)).length ≤ i := by
      simp only [memSlice_length]; omega
    rw [List.getElem_append_right hge, memSlice_getElem, memSlice_getElem]
    simp only [memSlice_length]
    congr 1; omega

/-! ## Procedure Body and Contract -/

/-- Recursive multi-limb keyed merge sort.
Args: `[arr, scratch, keys, L_key, lo, hi]`.
Calls `bSelf` recursively on `[lo, mid)` and `[mid, hi)` and compares keys using `bULess`. -/
def keyedMergeSortStmt (bSelf bULess : ℕ) : Stmt :=
  .cond (.bin .lt (.bin .sub (.reg 5) (.reg 4)) (.const 2))
    (.ret (.const 0))
    (.assign 6 (.bin .add (.reg 4) (.bin .div (.bin .sub (.reg 5) (.reg 4)) (.const 2))) ;;
     .call 7 bSelf [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6] ;;
     .call 7 bSelf [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 5] ;;
     .assign 7 (.reg 4) ;;
     .assign 8 (.reg 6) ;;
     .assign 9 (.const 0) ;;
     .assign 10 (.bin .sub (.reg 5) (.reg 4)) ;;
     .loop (.bin .lt (.reg 9) (.reg 10))
       (.cond (.bin .lt (.reg 7) (.reg 6))
         (.cond (.bin .lt (.reg 8) (.reg 5))
           (.assign 11 (.load (.bin .add (.reg 0) (.reg 7))) ;;
            .assign 12 (.load (.bin .add (.reg 0) (.reg 8))) ;;
            .call 13 bULess
              [.bin .add (.reg 2) (.bin .mul (.reg 12) (.reg 3)),
               .bin .add (.reg 2) (.bin .mul (.reg 11) (.reg 3)),
               .reg 3] ;;
            .cond (.reg 13)
              (.store (.bin .add (.reg 1) (.reg 9)) (.reg 12) ;;
               .assign 8 (.bin .add (.reg 8) (.const 1)))
              (.store (.bin .add (.reg 1) (.reg 9)) (.reg 11) ;;
               .assign 7 (.bin .add (.reg 7) (.const 1))))
           (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 7))) ;;
            .assign 7 (.bin .add (.reg 7) (.const 1))))
         (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 8))) ;;
          .assign 8 (.bin .add (.reg 8) (.const 1))) ;;
        .assign 9 (.bin .add (.reg 9) (.const 1))) ;;
     forRange 11 (.const 0) (.reg 10)
       (.store (.bin .add (.bin .add (.reg 0) (.reg 4)) (.reg 11))
          (.load (.bin .add (.reg 1) (.reg 11)))) ;;
     .ret (.const 0))

lemma keyedMergeSortStmt_noRand (bSelf bULess : ℕ) :
    (keyedMergeSortStmt bSelf bULess).NoRand := by
  simp [keyedMergeSortStmt, forRange, forUp, Stmt.NoRand]

def keyedMergeSortContract (w h : ℕ) : Contract where
  pre args mem := ∃ arr scratch keys L_key lo hi,
    args = [arr, scratch, keys, L_key, lo, hi] ∧
    2 < 2 ^ w ∧ 1 ≤ L_key ∧ lo ≤ hi ∧ arr + hi < 2 ^ w ∧ scratch + (hi - lo) < 2 ^ w ∧
    (arr + hi ≤ scratch ∨ scratch + (hi - lo) ≤ arr) ∧
    (∀ i, lo ≤ i → i < hi →
      let idx := mem (arr + i)
      keys + idx * L_key + L_key < 2 ^ w ∧
      Valid mem (keys + idx * L_key) h L_key ∧
      (keys + idx * L_key + L_key ≤ arr + lo ∨ arr + hi ≤ keys + idx * L_key) ∧
      (keys + idx * L_key + L_key ≤ scratch ∨ scratch + (hi - lo) ≤ keys + idx * L_key))
  post args mem ret mem' := ∃ arr scratch keys L_key lo hi,
    args = [arr, scratch, keys, L_key, lo, hi] ∧ ret = 0 ∧
    (memSlice mem' (arr + lo) (hi - lo)).Pairwise
      (fun a b => unsignedVal mem (keys + a * L_key) h L_key ≤
        unsignedVal mem (keys + b * L_key) h L_key) ∧
    List.Perm (memSlice mem' (arr + lo) (hi - lo)) (memSlice mem (arr + lo) (hi - lo)) ∧
    (∀ z, (z < arr + lo ∨ arr + hi ≤ z) →
      (z < scratch ∨ scratch + (hi - lo) ≤ z) → mem' z = mem z)
  cost args _ :=
    let len := args.getD 5 0 - args.getD 4 0
    (90 * args.getD 3 0 + 180) * len * (Nat.clog 2 len + 1) + 40

/-! ## Cost and Merge Helpers -/

private lemma clog2_half_add_one {len : ℕ} (hle : 2 ≤ len) :
    Nat.clog 2 (len / 2) + 1 ≤ Nat.clog 2 len ∧
    Nat.clog 2 (len - len / 2) + 1 ≤ Nat.clog 2 len := by
  have h1 : len / 2 ≤ len - len / 2 := by omega
  have h2 : Nat.clog 2 (len / 2) ≤ Nat.clog 2 (len - len / 2) := Nat.clog_mono_right 2 h1
  have hr : Nat.clog 2 (len - len / 2) + 1 ≤ Nat.clog 2 len := by
    have hcpos : 1 ≤ Nat.clog 2 len := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < len)
    have hpow := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_refl (Nat.clog 2 len))
    rw [show Nat.clog 2 len = (Nat.clog 2 len - 1) + 1 by omega, pow_succ'] at hpow
    have hsub : Nat.clog 2 (len - len / 2) ≤ Nat.clog 2 len - 1 := by
      rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
      omega
    omega
  exact ⟨le_trans (Nat.add_le_add_right h2 1) hr, hr⟩

private lemma keyedMergeSort_rec_cost {L_key len : ℕ} (hle : 2 ≤ len) :
    let lLen := len / 2
    let rLen := len - lLen
    ((90 * L_key + 180) * lLen * (Nat.clog 2 lLen + 1) + 40) +
    ((90 * L_key + 180) * rLen * (Nat.clog 2 rLen + 1) + 40) +
    ((45 * L_key + 95) * len + 85) ≤
    (90 * L_key + 180) * len * (Nat.clog 2 len + 1) + 40 := by
  intro lLen rLen
  obtain ⟨hlc, hrc⟩ := clog2_half_add_one hle
  set K := 90 * L_key + 180
  have hl1 : lLen * (Nat.clog 2 lLen + 1) ≤ lLen * Nat.clog 2 len := Nat.mul_le_mul_left _ hlc
  have hr1 : rLen * (Nat.clog 2 rLen + 1) ≤ rLen * Nat.clog 2 len := Nat.mul_le_mul_left _ hrc
  have hsum : lLen + rLen = len := by omega
  have htail : (45 * L_key + 95) * len + 165 ≤ K * len + 40 := by
    dsimp [K]
    nlinarith
  calc
    (K * lLen * (Nat.clog 2 lLen + 1) + 40) +
        (K * rLen * (Nat.clog 2 rLen + 1) + 40) + ((45 * L_key + 95) * len + 85)
      ≤ K * (lLen * Nat.clog 2 len) + K * (rLen * Nat.clog 2 len) +
          ((45 * L_key + 95) * len + 165) := by
        simp only [Nat.mul_assoc]; nlinarith
    _ = K * len * Nat.clog 2 len + ((45 * L_key + 95) * len + 165) := by
        have hdist : K * (lLen * Nat.clog 2 len) + K * (rLen * Nat.clog 2 len) =
            K * (lLen + rLen) * Nat.clog 2 len := by ring
        rw [hdist, hsum]
    _ ≤ K * len * Nat.clog 2 len + (K * len + 40) := Nat.add_le_add_left htail _
    _ = K * len * (Nat.clog 2 len + 1) + 40 := by ring

private lemma drop_cons_getElem {α : Type*} (L : List α) {i : ℕ} (hi : i < L.length) :
    L.drop i = L[i] :: L.drop (i + 1) :=
  (List.cons_getElem_drop_succ (h := hi)).symm

private lemma memSlice_update_snoc {mem : ℕ → ℕ} {scratch k x : ℕ} :
    memSlice (Function.update mem (scratch + k) x) scratch (k + 1) =
      memSlice mem scratch k ++ [x] := by
  refine List.ext_getElem (by simp [memSlice_length]) fun t ht _ => ?_
  simp only [memSlice_length] at ht
  by_cases htl : t < k
  · rw [List.getElem_append_left (by simpa [memSlice_length] using htl),
      memSlice_getElem, memSlice_getElem, Function.update_of_ne (by omega)]
  · have hte : t = k := by omega
    subst hte
    rw [List.getElem_append_right (by simp [memSlice_length]), memSlice_getElem]
    simp [memSlice_length]

@[simp] private lemma keyedMerge_nil_right (keyFn : ℕ → ℕ) :
    ∀ xs, keyedMerge keyFn xs [] = xs
  | [] => by simp [keyedMerge]
  | _ :: _ => by simp [keyedMerge]

private lemma merge_inv_pick_left {mem : ℕ → ℕ} {keyFn : ℕ → ℕ} {L₁ L₂ : List ℕ}
    {scratch k i₀ j₀ x : ℕ} (hhi : i₀ < L₁.length)
    (heq : L₁[i₀]'hhi = x)
    (hperm : memSlice mem scratch k ++ keyedMerge keyFn (L₁.drop i₀) (L₂.drop j₀) =
      keyedMerge keyFn L₁ L₂)
    (hbranch : L₂.drop j₀ = [] ∨ ∃ y ys', L₂.drop j₀ = y :: ys' ∧ ¬ keyFn y < keyFn x) :
    memSlice (Function.update mem (scratch + k) x) scratch (k + 1) ++
      keyedMerge keyFn (L₁.drop (i₀ + 1)) (L₂.drop j₀) = keyedMerge keyFn L₁ L₂ := by
  rw [memSlice_update_snoc]
  rw [drop_cons_getElem L₁ hhi, heq] at hperm
  rcases hbranch with hnil | ⟨y, ys', hcons, hle⟩
  · rw [hnil, keyedMerge_nil_right] at hperm
    simpa [hnil, keyedMerge_nil_right, List.append_assoc] using hperm
  · rw [hcons, keyedMerge] at hperm
    simp only [hle, ↓reduceIte] at hperm
    simpa [hcons, List.append_assoc] using hperm

private lemma merge_inv_pick_right {mem : ℕ → ℕ} {keyFn : ℕ → ℕ} {L₁ L₂ : List ℕ}
    {scratch k i₀ j₀ y : ℕ} (hj : j₀ < L₂.length)
    (heq : L₂[j₀]'hj = y)
    (hperm : memSlice mem scratch k ++ keyedMerge keyFn (L₁.drop i₀) (L₂.drop j₀) =
      keyedMerge keyFn L₁ L₂)
    (hbranch : L₁.drop i₀ = [] ∨ ∃ x xs', L₁.drop i₀ = x :: xs' ∧ keyFn y < keyFn x) :
    memSlice (Function.update mem (scratch + k) y) scratch (k + 1) ++
      keyedMerge keyFn (L₁.drop i₀) (L₂.drop (j₀ + 1)) = keyedMerge keyFn L₁ L₂ := by
  rw [memSlice_update_snoc]
  rw [drop_cons_getElem L₂ hj, heq] at hperm
  rcases hbranch with hnil | ⟨x, xs', hcons, hlt⟩
  · rw [hnil, keyedMerge] at hperm
    simpa [hnil, keyedMerge, List.append_assoc] using hperm
  · rw [hcons, keyedMerge] at hperm
    simp only [hlt, ↓reduceIte] at hperm
    simpa [hcons, List.append_assoc] using hperm

private lemma keyedMergeSort_mergeLoop {w h bULess arr scratch keys L_key lo mid hi : ℕ}
    {p : Program} (mem₁ : ℕ → ℕ) (hw : 1 < 2 ^ w)
    (hpUL : MeetsContract w p bULess (unsignedLessContract w h))
    (hLpos : 1 ≤ L_key) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (harw : arr + hi < 2 ^ w) (hscw : scratch + (hi - lo) < 2 ^ w) (hLw : L_key < 2 ^ w)
    (hdisj : arr + hi ≤ scratch ∨ scratch + (hi - lo) ≤ arr)
    (hkeys : ∀ i, lo ≤ i → i < hi →
      let idx := mem₁ (arr + i)
      keys + idx * L_key + L_key < 2 ^ w ∧
      Valid mem₁ (keys + idx * L_key) h L_key ∧
      (keys + idx * L_key + L_key ≤ arr + lo ∨ arr + hi ≤ keys + idx * L_key) ∧
      (keys + idx * L_key + L_key ≤ scratch ∨ scratch + (hi - lo) ≤ keys + idx * L_key)) :
    let L₁ := memSlice mem₁ (arr + lo) (mid - lo)
    let L₂ := memSlice mem₁ (arr + mid) (hi - mid)
    let keyFn := fun idx => unsignedVal mem₁ (keys + idx * L_key) h L_key
    Triple w p
      (fun st => st.regs 0 = arr ∧ st.regs 1 = scratch ∧ st.regs 2 = keys ∧
        st.regs 3 = L_key ∧ st.regs 4 = lo ∧ st.regs 5 = hi ∧ st.regs 6 = mid ∧
        st.regs 7 = lo ∧ st.regs 8 = mid ∧ st.regs 9 = 0 ∧ st.regs 10 = hi - lo ∧
        st.mem = mem₁)
      (.loop (.bin .lt (.reg 9) (.reg 10))
        (.cond (.bin .lt (.reg 7) (.reg 6))
          (.cond (.bin .lt (.reg 8) (.reg 5))
            (.assign 11 (.load (.bin .add (.reg 0) (.reg 7))) ;;
             .assign 12 (.load (.bin .add (.reg 0) (.reg 8))) ;;
             .call 13 bULess
               [.bin .add (.reg 2) (.bin .mul (.reg 12) (.reg 3)),
                .bin .add (.reg 2) (.bin .mul (.reg 11) (.reg 3)),
                .reg 3] ;;
             .cond (.reg 13)
               (.store (.bin .add (.reg 1) (.reg 9)) (.reg 12) ;;
                .assign 8 (.bin .add (.reg 8) (.const 1)))
               (.store (.bin .add (.reg 1) (.reg 9)) (.reg 11) ;;
                .assign 7 (.bin .add (.reg 7) (.const 1))))
            (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 7))) ;;
             .assign 7 (.bin .add (.reg 7) (.const 1))))
          (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 8))) ;;
           .assign 8 (.bin .add (.reg 8) (.const 1))) ;;
         .assign 9 (.bin .add (.reg 9) (.const 1))))
      (normalPost fun st => st.regs 0 = arr ∧ st.regs 1 = scratch ∧ st.regs 4 = lo ∧
        st.regs 10 = hi - lo ∧
        memSlice st.mem scratch (hi - lo) = keyedMerge keyFn L₁ L₂ ∧
        (∀ z, z < scratch ∨ scratch + (hi - lo) ≤ z → st.mem z = mem₁ z))
      (fun _ => (45 * L_key + 75) * (hi - lo) + 4) := by
  intro L₁ L₂ keyFn
  let Inv : State → Prop := fun st =>
    st.regs 0 = arr ∧ st.regs 1 = scratch ∧ st.regs 2 = keys ∧ st.regs 3 = L_key ∧
    st.regs 4 = lo ∧ st.regs 5 = hi ∧ st.regs 6 = mid ∧ st.regs 10 = hi - lo ∧
    lo ≤ st.regs 7 ∧ st.regs 7 ≤ mid ∧
    mid ≤ st.regs 8 ∧ st.regs 8 ≤ hi ∧
    st.regs 9 = (st.regs 7 - lo) + (st.regs 8 - mid) ∧
    memSlice st.mem scratch (st.regs 9) ++
      keyedMerge keyFn (L₁.drop (st.regs 7 - lo)) (L₂.drop (st.regs 8 - mid)) =
      keyedMerge keyFn L₁ L₂ ∧
    (∀ z, z < scratch ∨ scratch + st.regs 9 ≤ z → st.mem z = mem₁ z)
  let loopBody : Stmt :=
    .cond (.bin .lt (.reg 7) (.reg 6))
      (.cond (.bin .lt (.reg 8) (.reg 5))
        (.assign 11 (.load (.bin .add (.reg 0) (.reg 7))) ;;
         .assign 12 (.load (.bin .add (.reg 0) (.reg 8))) ;;
         .call 13 bULess
           [.bin .add (.reg 2) (.bin .mul (.reg 12) (.reg 3)),
            .bin .add (.reg 2) (.bin .mul (.reg 11) (.reg 3)),
            .reg 3] ;;
         .cond (.reg 13)
           (.store (.bin .add (.reg 1) (.reg 9)) (.reg 12) ;;
            .assign 8 (.bin .add (.reg 8) (.const 1)))
           (.store (.bin .add (.reg 1) (.reg 9)) (.reg 11) ;;
            .assign 7 (.bin .add (.reg 7) (.const 1))))
        (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 7))) ;;
         .assign 7 (.bin .add (.reg 7) (.const 1))))
      (.store (.bin .add (.reg 1) (.reg 9)) (.load (.bin .add (.reg 0) (.reg 8))) ;;
       .assign 8 (.bin .add (.reg 8) (.const 1))) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1))
  have hloop : Triple w p Inv (.loop (.bin .lt (.reg 9) (.reg 10)) loopBody)
      (normalPost fun st => st.regs 0 = arr ∧ st.regs 1 = scratch ∧ st.regs 4 = lo ∧
        st.regs 10 = hi - lo ∧
        memSlice st.mem scratch (hi - lo) = keyedMerge keyFn L₁ L₂ ∧
        (∀ z, z < scratch ∨ scratch + (hi - lo) ≤ z → st.mem z = mem₁ z))
      (fun st => ((Expr.bin .lt (.reg 9) (.reg 10)).size + (45 * L_key + 71) + 1) *
        (hi - lo - st.regs 9) + (Expr.bin .lt (.reg 9) (.reg 10)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => hi - lo - st.regs 9)
      (condVal := fun st => if st.regs 9 < hi - lo then 1 else 0)
      (bodyBound := 45 * L_key + 71)
      (fun st hInv => by
        rcases hInv with ⟨_, _, _, _, _, _, _, hr10, _, _, _, _, hr9, _, _⟩
        have hr9_lt : st.regs 9 < 2 ^ w := by omega
        have hr10_lt : st.regs 10 < 2 ^ w := by rw [hr10]; omega
        eval_expr)
      (fun st hInv hv => by
        rcases hInv with ⟨hr0, hr1, _, _, hr4, _, _, hr10, _, hi_mid, _, hj_hi, hr9, hperm, hfr⟩
        have hk_ge : hi - lo ≤ st.regs 9 := by
          by_contra hlt; simp [show st.regs 9 < hi - lo by omega] at hv
        have hk_eq : st.regs 9 = hi - lo := by omega
        have hi_eq : st.regs 7 = mid := by omega
        have hj_eq : st.regs 8 = hi := by omega
        rw [hk_eq] at hfr
        rw [hk_eq, hi_eq, hj_eq] at hperm
        have hd1 : L₁.drop (mid - lo) = [] :=
          List.drop_of_length_le (by simp [L₁, memSlice_length])
        have hd2 : L₂.drop (hi - mid) = [] :=
          List.drop_of_length_le (by simp [L₂, memSlice_length])
        rw [hd1, hd2, keyedMerge, List.append_nil] at hperm
        exact ⟨hr0, hr1, hr4, hr10, hperm, hfr⟩)
      (fun st hInv hv s ω' hEq => by
        subst hEq
        rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr10, hlo_i, hi_mid,
          hmid_j, hj_hi, hr9, hperm, hfr⟩
        have hk_lt : s.regs 9 < hi - lo := by by_contra hge; simp [hge] at hv
        have hk_w : s.regs 9 < 2 ^ w := by omega
        have hk1_w : s.regs 9 + 1 < 2 ^ w := by omega
        have hscr_w : scratch + s.regs 9 < 2 ^ w := by omega
        have hmid_w : mid < 2 ^ w := by omega
        have hhi_w : hi < 2 ^ w := by omega
        have hkey_elem : ∀ q', lo ≤ q' → q' < hi →
            s.mem (arr + q') = mem₁ (arr + q') ∧
            mem₁ (arr + q') < 2 ^ w ∧
            mem₁ (arr + q') * L_key < 2 ^ w ∧
            keys + mem₁ (arr + q') * L_key < 2 ^ w ∧
            keys + mem₁ (arr + q') * L_key + L_key < 2 ^ w ∧
            Valid s.mem (keys + mem₁ (arr + q') * L_key) h L_key ∧
            unsignedVal s.mem (keys + mem₁ (arr + q') * L_key) h L_key =
              keyFn (mem₁ (arr + q')) := by
          intro q' hqlo hqhi
          have har := hfr (arr + q') (by omega)
          obtain ⟨hkbd, hkv, _, hkdisj2⟩ := hkeys q' hqlo hqhi
          have hmul_lt : mem₁ (arr + q') * L_key < 2 ^ w := by omega
          have hidx_lt : mem₁ (arr + q') < 2 ^ w :=
            lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hLpos) hmul_lt
          have hka_lt : keys + mem₁ (arr + q') * L_key < 2 ^ w := by omega
          have hv' : Valid s.mem (keys + mem₁ (arr + q') * L_key) h L_key := fun t ht => by
            rw [hfr _ (by omega)]; exact hkv t ht
          have huv' : unsignedVal s.mem (keys + mem₁ (arr + q') * L_key) h L_key =
              keyFn (mem₁ (arr + q')) :=
            unsignedVal_congr fun t ht => hfr _ (by omega)
          exact ⟨har, hidx_lt, hmul_lt, hka_lt, hkbd, hv', huv'⟩
        have heval_i : (Expr.bin .lt (.reg 7) (.reg 6)).eval w s =
            some (if s.regs 7 < mid then 1 else 0) := by
          have : s.regs 7 < 2 ^ w := by omega
          eval_expr
        refine runs_start_le (runs_seq_cond_le heval_i ?_ ?_)
        · intro hi_cond
          have hi_lt : s.regs 7 < mid := by by_contra hc; simp [hc] at hi_cond
          have hi1_w : s.regs 7 + 1 < 2 ^ w := by omega
          have harr_i_lt : arr + s.regs 7 < 2 ^ w := by omega
          obtain ⟨hari, hiaw, hiamul, hika, hikbd, hiva, hiuv⟩ :=
            hkey_elem (s.regs 7) hlo_i (by omega)
          have hL1_len : s.regs 7 - lo < L₁.length := by simp [L₁, memSlice_length]; omega
          have hL1_eq : L₁[s.regs 7 - lo]'hL1_len = mem₁ (arr + s.regs 7) := by
            rw [memSlice_getElem]; congr 1; omega
          have heval_j : (Expr.bin .lt (.reg 8) (.reg 5)).eval w s =
              some (if s.regs 8 < hi then 1 else 0) := by
            have : s.regs 8 < 2 ^ w := by omega
            eval_expr
          refine runs_seq_cond_le heval_j ?_ ?_
          · intro hj_cond
            have hj_lt : s.regs 8 < hi := by by_contra hc; simp [hc] at hj_cond
            have hj1_w : s.regs 8 + 1 < 2 ^ w := by omega
            have harr_j_lt : arr + s.regs 8 < 2 ^ w := by omega
            obtain ⟨harj, hjaw, hjmul, hjka, hjkbd, hjva, hjuv⟩ :=
              hkey_elem (s.regs 8) (by omega) hj_lt
            have hL2_len : s.regs 8 - mid < L₂.length := by simp [L₂, memSlice_length]; omega
            have hL2_eq : L₂[s.regs 8 - mid]'hL2_len = mem₁ (arr + s.regs 8) := by
              rw [memSlice_getElem]; congr 1; omega
            refine runs_seq_assoc_le (runs_seq_assign_le (v := mem₁ (arr + s.regs 7))
              (by eval_expr) ?_)
            refine runs_seq_assoc_le (runs_seq_assign_le (v := mem₁ (arr + s.regs 8))
              (by eval_expr) ?_)
            refine runs_seq_assoc_le (runs_seq_call_le hpUL
              (vs := [keys + mem₁ (arr + s.regs 8) * L_key,
                keys + mem₁ (arr + s.regs 7) * L_key, L_key])
              (by eval_expr) (by wram_words) ⟨_, _, L_key, rfl, hjkbd, hikbd, hjva, hiva⟩ ?_)
            rintro res _ pos' ⟨rfl, hres⟩
            change res = if unsignedVal s.mem (keys + mem₁ (arr + s.regs 8) * L_key) h L_key <
                unsignedVal s.mem (keys + mem₁ (arr + s.regs 7) * L_key) h L_key then 1 else 0 at hres
            rw [hiuv, hjuv] at hres
            have hres_w : res < 2 ^ w := by rw [hres]; split_ifs <;> omega
            refine runs_seq_cond_le (by eval_expr) ?_ ?_
            · intro hres_ne
              have hkey_lt : keyFn (mem₁ (arr + s.regs 8)) < keyFn (mem₁ (arr + s.regs 7)) := by
                by_contra hc; simp [hc] at hres hres_ne
              refine runs_seq_assoc_le (runs_seq_store_le (by eval_expr) (by eval_expr) ?_)
              refine runs_seq_assign_le (v := s.regs 8 + 1) (by eval_expr) ?_
              refine runs_assign_le (v := s.regs 9 + 1) (by eval_expr) ?_
                (by simp only [unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ]; wram_cost)
              refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                by simp [hr5], by simp [hr6], by simp [hr10], by simp [hlo_i], by simp [hi_mid],
                by simp; omega, by simp; omega, by simp; omega, ?_, ?_⟩, by simp; omega⟩
              · have := merge_inv_pick_right hL2_len hL2_eq hperm
                  (Or.inr ⟨mem₁ (arr + s.regs 7), L₁.drop (s.regs 7 - lo + 1),
                    by rw [drop_cons_getElem L₁ hL1_len, hL1_eq], hkey_lt⟩)
                simpa [Function.update_of_ne, hr9,
                  show s.regs 8 + 1 - mid = s.regs 8 - mid + 1 by omega] using this
              · intro z hz
                dsimp only at hz ⊢
                simp only [Function.update_self] at hz
                rw [Function.update_of_ne (by omega)]
                exact hfr z (by omega)
            · intro hres_eq
              have hkey_nlt : ¬ keyFn (mem₁ (arr + s.regs 8)) < keyFn (mem₁ (arr + s.regs 7)) := by
                by_contra hc; simp [hc] at hres hres_eq
              refine runs_seq_assoc_le (runs_seq_store_le (by eval_expr) (by eval_expr) ?_)
              refine runs_seq_assign_le (v := s.regs 7 + 1) (by eval_expr) ?_
              refine runs_assign_le (v := s.regs 9 + 1) (by eval_expr) ?_
                (by simp only [unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ]; wram_cost)
              refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                by simp [hr5], by simp [hr6], by simp [hr10], by simp; omega, by simp; omega,
                by simp [hmid_j], by simp [hj_hi], by simp; omega, ?_, ?_⟩, by simp; omega⟩
              · have := merge_inv_pick_left hL1_len hL1_eq hperm
                  (Or.inr ⟨mem₁ (arr + s.regs 8), L₂.drop (s.regs 8 - mid + 1),
                    by rw [drop_cons_getElem L₂ hL2_len, hL2_eq], hkey_nlt⟩)
                simpa [Function.update_of_ne, hr9,
                  show s.regs 7 + 1 - lo = s.regs 7 - lo + 1 by omega] using this
              · intro z hz
                dsimp only at hz ⊢
                simp only [Function.update_self] at hz
                rw [Function.update_of_ne (by omega)]
                exact hfr z (by omega)
          · intro hj_cond
            have hj_eq : s.regs 8 = hi := by
              by_contra hc; simp [show s.regs 8 < hi by omega] at hj_cond
            refine runs_seq_assoc_le (runs_seq_store_le (by eval_expr) (by eval_expr) ?_)
            refine runs_seq_assign_le (v := s.regs 7 + 1) (by eval_expr) ?_
            refine runs_assign_le (v := s.regs 9 + 1) (by eval_expr) ?_ (by wram_cost)
            refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
              by simp [hr5], by simp [hr6], by simp [hr10], by simp; omega, by simp; omega,
              by simp [hmid_j], by simp [hj_hi], by simp; omega, ?_, ?_⟩, by simp; omega⟩
            · have hdrop2 : L₂.drop (s.regs 8 - mid) = [] :=
                List.drop_of_length_le (by simp [L₂, memSlice_length, hj_eq])
              have := merge_inv_pick_left hL1_len hL1_eq hperm (Or.inl hdrop2)
              simpa [Function.update_of_ne, hr9, hari,
                show s.regs 7 + 1 - lo = s.regs 7 - lo + 1 by omega] using this
            · intro z hz
              dsimp only at hz ⊢
              simp only [Function.update_self] at hz
              rw [Function.update_of_ne (by omega)]
              exact hfr z (by omega)
        · intro hi_cond
          have hi_eq : s.regs 7 = mid := by
            by_contra hc; simp [show s.regs 7 < mid by omega] at hi_cond
          have hj_lt : s.regs 8 < hi := by omega
          have hj1_w : s.regs 8 + 1 < 2 ^ w := by omega
          have harr_j_lt : arr + s.regs 8 < 2 ^ w := by omega
          obtain ⟨harj, hjaw, hjmul, hjka, hjkbd, hjva, hjuv⟩ :=
            hkey_elem (s.regs 8) (by omega) hj_lt
          have hL2_len : s.regs 8 - mid < L₂.length := by simp [L₂, memSlice_length]; omega
          have hL2_eq : L₂[s.regs 8 - mid]'hL2_len = mem₁ (arr + s.regs 8) := by
            rw [memSlice_getElem]; congr 1; omega
          refine runs_seq_assoc_le (runs_seq_store_le (by eval_expr) (by eval_expr) ?_)
          refine runs_seq_assign_le (v := s.regs 8 + 1) (by eval_expr) ?_
          refine runs_assign_le (v := s.regs 9 + 1) (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
            by simp [hr5], by simp [hr6], by simp [hr10], by simp [hlo_i], by simp [hi_mid],
            by simp; omega, by simp; omega, by simp; omega, ?_, ?_⟩, by simp; omega⟩
          · have hdrop1 : L₁.drop (s.regs 7 - lo) = [] :=
              List.drop_of_length_le (by simp [L₁, memSlice_length, hi_eq])
            have := merge_inv_pick_right hL2_len hL2_eq hperm (Or.inl hdrop1)
            simpa [Function.update_of_ne, hr9, harj,
              show s.regs 8 + 1 - mid = s.regs 8 - mid + 1 by omega] using this
          · intro z hz
            dsimp only at hz ⊢
            simp only [Function.update_self] at hz
            rw [Function.update_of_ne (by omega)]
            exact hfr z (by omega))
  refine hloop.conseq (fun st hst => ?_) (fun _ _ h => h) (fun st hst => ?_)
  · rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hmem⟩
    subst hmem
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h10, by rw [h7], by rw [h7]; exact hlm,
      by rw [h8], by rw [h8]; exact hmh, ?_, ?_, ?_⟩
    · simp [h7, h8, h9]
    · simp [h7, h8, h9, memSlice]
    · intro z _; rfl
  · rcases hst with ⟨_, _, _, _, _, _, _, _, _, h9, _, _⟩
    dsimp [Expr.size]
    rw [h9]
    calc
      (1 + 1 + 1 + (45 * L_key + 71) + 1) * (hi - lo - 0) + (1 + 1 + 1) + 1
        = (45 * L_key + 75) * (hi - lo) + 4 := by simp only [Nat.sub_zero]; ring
      _ ≤ (45 * L_key + 75) * (hi - lo) + 4 := le_rfl

/-- Verified contract for `keyedMergeSortStmt`. -/
theorem keyedMergeSort_meetsContract {w h bSelf bULess : ℕ} {p : Program}
    (hpSelf : p.procs[bSelf]? = some (keyedMergeSortStmt bSelf bULess))
    (hpUL : MeetsContract w p bULess (unsignedLessContract w h)) :
    MeetsContract w p bSelf (keyedMergeSortContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 5 0 - args.getD 4 0) hpSelf
  intro len ih args mem pos ω hwords hpre hmeas
  rcases hpre with ⟨arr, scratch, keys, L_key, lo, hi, rfl, hw2, hLpos, hle, harw, hscw, hdisj, hkeys⟩
  change hi - lo = len at hmeas
  subst hmeas
  have harw0 : arr < 2 ^ w := hwords arr (by simp)
  have hscw0 : scratch < 2 ^ w := hwords scratch (by simp)
  have hk0 : keys < 2 ^ w := hwords keys (by simp)
  have hLw : L_key < 2 ^ w := hwords L_key (by simp)
  have hlow : lo < 2 ^ w := hwords lo (by simp)
  have hhiw : hi < 2 ^ w := hwords hi (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold keyedMergeSortStmt
  refine runs_cond_le (v := if hi - lo < 2 then 1 else 0) (by eval_expr) ?_ ?_
  · intro hlt2
    have hle1 : hi - lo ≤ 1 := by
      by_contra hc; simp [show ¬ hi - lo < 2 by omega] at hlt2
    refine runs_ret_le (by eval_expr) ⟨arr, scratch, keys, L_key, lo, hi, rfl, rfl, ?_, ?_, ?_⟩
      (by simp [keyedMergeSortContract, Expr.size])
    · change List.Pairwise _ (memSlice mem (arr + lo) (hi - lo))
      cases hms : memSlice mem (arr + lo) (hi - lo) with
      | nil => simp
      | cons a xs =>
        cases xs with
        | nil => simp
        | cons b ys =>
          exfalso
          have hlen_s := congrArg List.length hms
          simp only [memSlice_length, List.length_cons] at hlen_s
          omega
    · exact List.Perm.refl _
    · intro _ _ _; rfl
  · intro hge2
    have hlen2 : 2 ≤ hi - lo := by
      by_contra hc; simp [show hi - lo < 2 by omega] at hge2
    set mid := lo + (hi - lo) / 2
    have hlm : lo ≤ mid := Nat.le_add_right lo _
    have hmh : mid ≤ hi := by dsimp [mid]; omega
    have hmidw : mid < 2 ^ w := lt_of_le_of_lt hmh hhiw
    have hl_lt : mid - lo < hi - lo := by dsimp [mid]; omega
    have hr_lt : hi - mid < hi - lo := by dsimp [mid]; omega
    have harw_mid : arr + mid < 2 ^ w := by omega
    have hscw_l : scratch + (mid - lo) < 2 ^ w := by omega
    have hscw_r : scratch + (hi - mid) < 2 ^ w := by omega
    have hsub_keys : ∀ (lo' hi' : ℕ) (m' : ℕ → ℕ),
        lo ≤ lo' → hi' ≤ hi →
        (∀ i, lo' ≤ i → i < hi' →
          m' (arr + i) = mem (arr + i) ∧
          (∀ z, (keys + mem (arr + i) * L_key ≤ z ∧ z < keys + mem (arr + i) * L_key + L_key) →
            m' z = mem z)) →
        ∀ i, lo' ≤ i → i < hi' →
          let idx := m' (arr + i)
          keys + idx * L_key + L_key < 2 ^ w ∧
          Valid m' (keys + idx * L_key) h L_key ∧
          (keys + idx * L_key + L_key ≤ arr + lo' ∨ arr + hi' ≤ keys + idx * L_key) ∧
          (keys + idx * L_key + L_key ≤ scratch ∨ scratch + (hi' - lo') ≤ keys + idx * L_key) := by
      intro lo' hi' m' hlo' hhi' hmag i hi1 hi2
      have hmi := hmag i hi1 hi2
      rw [hmi.1]
      obtain ⟨hkbd, hkval, hkd1, hkd2⟩ := hkeys i (by omega) (by omega)
      refine ⟨hkbd, fun t ht => ?_, ?_, ?_⟩
      · rw [hmi.2 _ ⟨by omega, by omega⟩]; exact hkval t ht
      · rcases hkd1 with h1 | h2 <;> [left; right] <;> omega
      · rcases hkd2 with h1 | h2 <;> [left; right] <;> omega
    refine runs_seq_assign_le (v := mid) (by eval_expr) ?_
    refine runs_seq_call_le ih (vs := [arr, scratch, keys, L_key, lo, mid]) (by eval_expr)
      (by wram_words) ⟨⟨arr, scratch, keys, L_key, lo, mid, rfl, hw2, hLpos, hlm, harw_mid, hscw_l,
        by rcases hdisj with h1 | h2 <;> [left; right] <;> omega,
        hsub_keys lo mid mem le_rfl hmh fun i _ _ => ⟨rfl, fun _ _ => rfl⟩⟩, hl_lt⟩ ?_
    rintro _ mem₁ pos₁ ⟨_, _, _, _, _, _, hEq₁, _, hp₁, hperm₁, hfr₁⟩
    simp only [List.cons.injEq, and_true] at hEq₁
    rcases hEq₁ with ⟨e1, e2, e3, e4, e5, e6⟩
    subst e1 e2 e3 e4 e5 e6
    have hfr₁_keys : ∀ i, lo ≤ i → i < hi →
        ∀ z, (keys + mem (arr + i) * L_key ≤ z ∧ z < keys + mem (arr + i) * L_key + L_key) →
          mem₁ z = mem z := by
      intro i hi1 hi2 z hz
      obtain ⟨_, _, hkd1, hkd2⟩ := hkeys i hi1 hi2
      exact hfr₁ z (by rcases hkd1 with h | h <;> omega) (by rcases hkd2 with h | h <;> omega)
    have hkeys₁_r : ∀ i, mid ≤ i → i < hi → mem₁ (arr + i) = mem (arr + i) := by
      intro i hi1 hi2
      exact hfr₁ (arr + i) (Or.inr (by omega)) (by rcases hdisj with h | h <;> [left; right] <;> omega)
    refine runs_seq_call_le ih (vs := [arr, scratch, keys, L_key, mid, hi]) (by eval_expr)
      (by wram_words) ⟨⟨arr, scratch, keys, L_key, mid, hi, rfl, hw2, hLpos, hmh, harw, hscw_r,
        by rcases hdisj with h1 | h2 <;> [left; right] <;> omega,
        hsub_keys mid hi mem₁ hlm le_rfl fun i hi1 hi2 =>
          ⟨hkeys₁_r i hi1 hi2, hfr₁_keys i (by omega) hi2⟩⟩, hr_lt⟩ ?_
    rintro _ mem₂ pos₂ ⟨_, _, _, _, _, _, hEq₂, _, hp₂, hperm₂, hfr₂⟩
    simp only [List.cons.injEq, and_true] at hEq₂
    rcases hEq₂ with ⟨e1, e2, e3, e4, e5, e6⟩
    subst e1 e2 e3 e4 e5 e6
    have harr₁₂_lo : memSlice mem₂ (arr + lo) (mid - lo) = memSlice mem₁ (arr + lo) (mid - lo) :=
      memSlice_eq_of_agree fun i hi_lt =>
        hfr₂ (arr + lo + i) (Or.inl (by omega)) (by rcases hdisj with h | h <;> [left; right] <;> omega)
    have hperm_orig : List.Perm
        (memSlice mem₂ (arr + lo) (mid - lo) ++ memSlice mem₂ (arr + mid) (hi - mid))
        (memSlice mem (arr + lo) (hi - lo)) := by
      rw [harr₁₂_lo]
      have hmid_mem : memSlice mem₁ (arr + mid) (hi - mid) = memSlice mem (arr + mid) (hi - mid) :=
        memSlice_eq_of_agree fun i hi_lt => by
          simpa [Nat.add_assoc] using hkeys₁_r (mid + i) (by omega) (by omega)
      rw [memSlice_split mem arr lo mid hi hlm hmh]
      exact List.Perm.append hperm₁ (hmid_mem ▸ hperm₂)
    have hperm_idx : ∀ i, lo ≤ i → i < hi →
        ∃ i₀, lo ≤ i₀ ∧ i₀ < hi ∧ mem₂ (arr + i) = mem (arr + i₀) := by
      intro i hi1 hi2
      have hmem_i : mem₂ (arr + i) ∈
          memSlice mem₂ (arr + lo) (mid - lo) ++ memSlice mem₂ (arr + mid) (hi - mid) := by
        rw [← memSlice_split mem₂ arr lo mid hi hlm hmh]
        have : i - lo < (memSlice mem₂ (arr + lo) (hi - lo)).length := by
          simp [memSlice_length]; omega
        simpa [memSlice_getElem, show arr + lo + (i - lo) = arr + i by omega] using
          List.getElem_mem this
      have hmem_orig : mem₂ (arr + i) ∈ memSlice mem (arr + lo) (hi - lo) :=
        hperm_orig.mem_iff.mp hmem_i
      rcases List.mem_iff_getElem.mp hmem_orig with ⟨t, ht, hteq⟩
      simp only [memSlice_length] at ht
      rw [memSlice_getElem] at hteq
      exact ⟨lo + t, by omega, by omega, by simpa [Nat.add_assoc] using hteq.symm⟩
    have hmem₂_keys_eq : ∀ z, (∃ i, lo ≤ i ∧ i < hi ∧
        keys + mem (arr + i) * L_key ≤ z ∧ z < keys + mem (arr + i) * L_key + L_key) →
        mem₂ z = mem z := by
      rintro z ⟨i, hi1, hi2, hz1, hz2⟩
      obtain ⟨_, _, hkd1, hkd2⟩ := hkeys i hi1 hi2
      rw [hfr₂ z (by rcases hkd1 with h | h <;> omega) (by rcases hkd2 with h | h <;> omega)]
      exact hfr₁ z (by rcases hkd1 with h | h <;> omega) (by rcases hkd2 with h | h <;> omega)
    have hkeys₂ : ∀ i, lo ≤ i → i < hi →
        let idx := mem₂ (arr + i)
        keys + idx * L_key + L_key < 2 ^ w ∧
        Valid mem₂ (keys + idx * L_key) h L_key ∧
        (keys + idx * L_key + L_key ≤ arr + lo ∨ arr + hi ≤ keys + idx * L_key) ∧
        (keys + idx * L_key + L_key ≤ scratch ∨ scratch + (hi - lo) ≤ keys + idx * L_key) := by
      intro i hi1 hi2
      obtain ⟨i₀, hi0_1, hi0_2, hid⟩ := hperm_idx i hi1 hi2
      dsimp only
      rw [hid]
      obtain ⟨hkbd, hkval, hkd1, hkd2⟩ := hkeys i₀ hi0_1 hi0_2
      refine ⟨hkbd, fun t ht => ?_, hkd1, hkd2⟩
      rw [hmem₂_keys_eq _ ⟨i₀, hi0_1, hi0_2, by omega, by omega⟩]
      exact hkval t ht
    refine runs_seq_assign_le (v := lo) (by eval_expr) ?_
    refine runs_seq_assign_le (v := mid) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    refine runs_seq_assign_le (v := hi - lo) (by eval_expr) ?_
    have hmloop := keyedMergeSort_mergeLoop (w := w) (h := h) (bULess := bULess)
      (arr := arr) (scratch := scratch) (keys := keys) (L_key := L_key)
      (lo := lo) (mid := mid) (hi := hi) mem₂ hw1 hpUL hLpos hlm hmh harw hscw hLw hdisj hkeys₂
    refine runs_seq_triple_le hmloop ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun st₃ hm₃ => ?_)
    rcases hm₃ with ⟨hr0, hr1, hr4, hr10, hmerge_eq, hfr₃⟩
    have hkeyFn_eq : ∀ idx, (∃ i, lo ≤ i ∧ i < hi ∧ idx = mem (arr + i)) →
        unsignedVal mem₂ (keys + idx * L_key) h L_key =
          unsignedVal mem (keys + idx * L_key) h L_key := by
      rintro idx ⟨i, hi1, hi2, rfl⟩
      exact unsignedVal_congr fun t ht => hmem₂_keys_eq _ ⟨i, hi1, hi2, by omega, by omega⟩
    have hmem_scr_orig : ∀ j < hi - lo, ∃ i₀, lo ≤ i₀ ∧ i₀ < hi ∧
        st₃.mem (scratch + j) = mem (arr + i₀) := by
      intro j hj
      have hj_len : j < (memSlice st₃.mem scratch (hi - lo)).length := by
        simp [memSlice_length, hj]
      have hmem_scr : st₃.mem (scratch + j) ∈ memSlice st₃.mem scratch (hi - lo) := by
        simpa [memSlice_getElem] using List.getElem_mem hj_len
      rw [hmerge_eq, keyedMerge_mem] at hmem_scr
      have hmem_orig : st₃.mem (scratch + j) ∈ memSlice mem (arr + lo) (hi - lo) :=
        hperm_orig.mem_iff.mp (by
          rcases hmem_scr with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ h)
      rcases List.mem_iff_getElem.mp hmem_orig with ⟨t, ht, hteq⟩
      simp only [memSlice_length] at ht
      rw [memSlice_getElem] at hteq
      exact ⟨lo + t, by omega, by omega, by simpa [Nat.add_assoc] using hteq.symm⟩
    let InvCopy : ℕ → State → Prop := fun t st =>
      st.regs 0 = arr ∧ st.regs 1 = scratch ∧ st.regs 4 = lo ∧ st.regs 10 = hi - lo ∧
      st.regs 11 = t ∧
      (∀ j < t, st.mem (arr + lo + j) = st₃.mem (scratch + j)) ∧
      (∀ z, z < arr + lo ∨ arr + lo + t ≤ z → st.mem z = st₃.mem z)
    have hcopy : Triple w p (fun st => st = st₃)
        (forRange 11 (.const 0) (.reg 10)
          (.store (.bin .add (.bin .add (.reg 0) (.reg 4)) (.reg 11))
            (.load (.bin .add (.reg 1) (.reg 11)))))
        (normalPost (InvCopy (hi - lo))) (fun _ => 20 * (hi - lo) + 7) := by
      refine (Triple.forRange_const 11 0 (hi - lo) (Nat.zero_le _) hw1 (fun _ => by omega)
        (fun st hst => by
          subst hst
          exact ⟨by eval_expr, by simp [hr0], by simp [hr1], by simp [hr4], by simp [hr10],
            by simp, fun _ hj => by omega, fun _ _ => rfl⟩)
        (fun _ _ _ _ hi_inv => hi_inv.2.2.2.2.1)
        (fun _ st _ _ hi_inv => by have h10 := hi_inv.2.2.2.1; eval_expr)
        (fun j _ hj_lt st ω' hi_inv => by
          rcases hi_inv with ⟨c0, c1, c4, c10, c11, hcp, hfr_c⟩
          have hlt_al : arr + lo < 2 ^ w := by omega
          have hlt_alj : arr + lo + j < 2 ^ w := by omega
          have hlt_sj : scratch + j < 2 ^ w := by omega
          have hlt_j : j < 2 ^ w := by omega
          obtain ⟨i₀, hi0_1, hi0_2, hscr_eq⟩ := hmem_scr_orig j hj_lt
          obtain ⟨hkbd_scr, _⟩ := hkeys i₀ hi0_1 hi0_2
          have hscr_w : st₃.mem (scratch + j) < 2 ^ w := by
            rw [hscr_eq]
            exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hLpos) (by omega)
          have hread : st.mem (scratch + j) = st₃.mem (scratch + j) := by
            refine hfr_c (scratch + j) ?_
            rcases hdisj with h | h
            · right; omega
            · left; omega
          refine runs_start_le (runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost))
          refine ⟨⟨c0, c1, c4, c10, by simp, fun j' hj' => ?_, fun z hz => ?_⟩, c11⟩
          · dsimp only
            by_cases hjj : j' = j
            · subst j'; simp [hread]
            · rw [Function.update_of_ne (by omega)]; exact hcp j' (by omega)
          · dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hfr_c z (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
    refine runs_seq_triple_le hcopy rfl (fun st₄ hinv₄ => ?_)
    rcases hinv₄ with ⟨_, _, _, _, _, hcp₄, hfr₄⟩
    have hslice_eq : memSlice st₄.mem (arr + lo) (hi - lo) = memSlice st₃.mem scratch (hi - lo) :=
      List.ext_getElem (by simp [memSlice_length]) fun i hi_lt _ => by
        simp only [memSlice_length] at hi_lt
        rw [memSlice_getElem, memSlice_getElem]
        exact hcp₄ i hi_lt
    rw [hmerge_eq] at hslice_eq
    have hmem_L1 : ∀ x ∈ memSlice mem₂ (arr + lo) (mid - lo),
        ∃ i, lo ≤ i ∧ i < hi ∧ x = mem (arr + i) := by
      intro x hx
      have hx_o : x ∈ memSlice mem (arr + lo) (hi - lo) :=
        hperm_orig.mem_iff.mp (List.mem_append_left _ hx)
      rcases List.mem_iff_getElem.mp hx_o with ⟨t, ht, hteq⟩
      simp only [memSlice_length] at ht
      rw [memSlice_getElem] at hteq
      exact ⟨lo + t, by omega, by omega, by simpa [Nat.add_assoc] using hteq.symm⟩
    have hmem_L2 : ∀ x ∈ memSlice mem₂ (arr + mid) (hi - mid),
        ∃ i, lo ≤ i ∧ i < hi ∧ x = mem (arr + i) := by
      intro x hx
      have hx_o : x ∈ memSlice mem (arr + lo) (hi - lo) :=
        hperm_orig.mem_iff.mp (List.mem_append_right _ hx)
      rcases List.mem_iff_getElem.mp hx_o with ⟨t, ht, hteq⟩
      simp only [memSlice_length] at ht
      rw [memSlice_getElem] at hteq
      exact ⟨lo + t, by omega, by omega, by simpa [Nat.add_assoc] using hteq.symm⟩
    have hpw_imp_mem : ∀ {L : List ℕ} {R₁ R₂ : ℕ → ℕ → Prop},
        L.Pairwise R₁ → (∀ a ∈ L, ∀ b ∈ L, R₁ a b → R₂ a b) → L.Pairwise R₂ := by
      intro L R₁ R₂ hp hR
      induction L with
      | nil => simp
      | cons a xs ih =>
        rw [List.pairwise_cons] at hp ⊢
        exact ⟨fun b hb => hR a List.mem_cons_self b (List.mem_cons_of_mem a hb) (hp.1 b hb),
          ih hp.2 fun x hx y hy => hR x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)⟩
    have hp₁' : (memSlice mem₂ (arr + lo) (mid - lo)).Pairwise
        (fun a b => unsignedVal mem₂ (keys + a * L_key) h L_key ≤
          unsignedVal mem₂ (keys + b * L_key) h L_key) := by
      rw [harr₁₂_lo] at hmem_L1 ⊢
      refine hpw_imp_mem hp₁ fun a ha b hb hab => ?_
      rw [hkeyFn_eq a (hmem_L1 a ha), hkeyFn_eq b (hmem_L1 b hb)]
      exact hab
    have hp₂' : (memSlice mem₂ (arr + mid) (hi - mid)).Pairwise
        (fun a b => unsignedVal mem₂ (keys + a * L_key) h L_key ≤
          unsignedVal mem₂ (keys + b * L_key) h L_key) := by
      refine hpw_imp_mem hp₂ fun a ha b hb hab => ?_
      obtain ⟨ia, hia1, hia2, rfl⟩ := hmem_L2 a ha
      obtain ⟨ib, hib1, hib2, rfl⟩ := hmem_L2 b hb
      have h1a : unsignedVal mem₁ (keys + mem (arr + ia) * L_key) h L_key =
          unsignedVal mem (keys + mem (arr + ia) * L_key) h L_key :=
        unsignedVal_congr fun t ht => hfr₁_keys ia hia1 hia2 _ ⟨by omega, by omega⟩
      have h1b : unsignedVal mem₁ (keys + mem (arr + ib) * L_key) h L_key =
          unsignedVal mem (keys + mem (arr + ib) * L_key) h L_key :=
        unsignedVal_congr fun t ht => hfr₁_keys ib hib1 hib2 _ ⟨by omega, by omega⟩
      rw [hkeyFn_eq _ ⟨ia, hia1, hia2, rfl⟩, hkeyFn_eq _ ⟨ib, hib1, hib2, rfl⟩]
      rw [h1a, h1b] at hab
      exact hab
    have hp_merge2 := keyedMerge_pairwise
      (fun idx => unsignedVal mem₂ (keys + idx * L_key) h L_key) hp₁' hp₂'
    have hmem_merge : ∀ x ∈ memSlice st₄.mem (arr + lo) (hi - lo),
        ∃ i, lo ≤ i ∧ i < hi ∧ x = mem (arr + i) := by
      intro x hx
      rw [hslice_eq, keyedMerge_mem] at hx
      rcases hx with hx | hx
      · exact hmem_L1 x hx
      · exact hmem_L2 x hx
    have hpw_mem : (memSlice st₄.mem (arr + lo) (hi - lo)).Pairwise
        (fun a b => unsignedVal mem (keys + a * L_key) h L_key ≤
          unsignedVal mem (keys + b * L_key) h L_key) := by
      rw [hslice_eq]
      refine hpw_imp_mem hp_merge2 fun a ha b hb hab => ?_
      rw [← hslice_eq] at ha hb
      rw [← hkeyFn_eq a (hmem_merge a ha), ← hkeyFn_eq b (hmem_merge b hb)]
      exact hab
    have hperm_final : List.Perm (memSlice st₄.mem (arr + lo) (hi - lo))
        (memSlice mem (arr + lo) (hi - lo)) := by
      rw [hslice_eq]
      exact (keyedMerge_perm _ _ _).trans hperm_orig
    have hfr_final : ∀ z, (z < arr + lo ∨ arr + hi ≤ z) →
        (z < scratch ∨ scratch + (hi - lo) ≤ z) → st₄.mem z = mem z := by
      intro z hz_arr hz_scr
      have h4 : st₄.mem z = st₃.mem z := hfr₄ z (by rcases hz_arr with h | h <;> omega)
      have h3 : st₃.mem z = mem₂ z := hfr₃ z hz_scr
      have h2 : mem₂ z = mem₁ z := hfr₂ z (by rcases hz_arr with h | h <;> omega)
        (by rcases hz_scr with h | h <;> omega)
      have h1 : mem₁ z = mem z := hfr₁ z (by rcases hz_arr with h | h <;> omega)
        (by rcases hz_scr with h | h <;> omega)
      omega
    refine runs_ret_le (by eval_expr)
      ⟨arr, scratch, keys, L_key, lo, hi, rfl, rfl, hpw_mem, hperm_final, hfr_final⟩ ?_
    have hrec_cost := keyedMergeSort_rec_cost (L_key := L_key) hlen2
    have hln : (45 * L_key + 95) * (hi - lo) = (45 * L_key + 75) * (hi - lo) + 20 * (hi - lo) := by
      ring
    rw [hln] at hrec_cost
    have hmid_diff1 : mid - lo = (hi - lo) / 2 := by dsimp [mid]; omega
    have hmid_diff2 : hi - mid = (hi - lo) - (hi - lo) / 2 := by dsimp [mid]; omega
    simp only [Contract.below, List.getD_cons_zero, List.getD_cons_succ, keyedMergeSortContract,
      argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_bin, Expr.size_const]
    rw [hmid_diff1, hmid_diff2]
    omega

end

end MinCostFlow.LSF.Program
