module

public import MinCostFlow.ExpanderDecomp.Injection
public import MinCostFlow.ExpanderDecomp.BlocksMacro
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equal-block split and leftover attachment (Step A and Step C)

In Step A of `OneShot`, a vertex list `vs` (without duplicates) is
split in its fixed order into full blocks of size `b` and a leftover set `Z`. In Step C, after
building an expanding witness on the union of the full blocks, the leftover vertices `Z` are
attached by an injection matching into the full blocks using
the injection lemma `isExpansionExpanderOn_of_injection` (`Injection.lean`).

This file defines the block split and proves:
* `fullPrefix`, `leftoverList`, `blockList`, `fullVerts`, `leftoverVerts`, `blockSet`, `blockOf`,
  `numFullBlocks`: the split of `vs` into `numFullBlocks vs b` full blocks of size `b` and
  leftover vertices `Z = leftoverVerts vs b`.
* Partition properties: `fullVerts` and `leftoverVerts` are disjoint and cover `vs.toFinset`, each
  fibre of `blockOf` on `fullVerts` equals `blockSet vs b i` and has cardinality `b`, and every
  vertex in `fullVerts` maps under `blockOf` into `Finset.range (numFullBlocks vs b)`.
* Block size facts, `|Z| < b ≤ |V \ Z|`:
  - `card_leftoverVerts_lt`: `|Z| < b` (for `0 < b`);
  - `blockSize_le_card_fullVerts`: `b ≤ |V \ Z|` (for `b ≤ vs.length`);
  - `card_leftoverVerts_le_card_fullVerts`: `|Z| ≤ |V \ Z|` (for `0 < b ≤ vs.length`);
  - `numFullBlocks_le_of_length_le` and `stepA_block_params`: at `b = N ^ (q - 1) / 2` with
    `2 ≤ q`, `4 ∣ N`, and `b ≤ vs.length ≤ N ^ q`, `b` is positive and even, and there are between
    `1` and `2 * N` full blocks.
  - `stepA_singleton_params`: at `q = 1` (`b = 1`), `Z = ∅` and each block is a singleton.
* Step C attachment by the injection lemma:
  - `leftoverInjectionMatching` and `leftoverInjectionMatching_spec`: canonical zip matching of `Z`
    into `fullVerts` when `b ≤ vs.length` (showing the hypotheses can always be met).
  - `isExpansionExpanderOn_of_blockSplit_injection`: any injection matching from `Z` into
    `fullVerts` extends a `γ`-expander on `fullVerts` to a `γ / 2`-expander on `vs.toFinset`.
  - `isExpansionExpanderOn_of_blockSplit_macro_and_injection`: combines the macro block step
    (`BlocksMacro.lean`) with the leftover injection step to yield expansion `α * β / 20` on
    `vs.toFinset`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- The number of full blocks of size `b` in a vertex list `vs`. -/
def numFullBlocks (vs : List ℕ) (b : ℕ) : ℕ :=
  vs.length / b

/-- The prefix of `vs` lying in full blocks of size `b`. -/
def fullPrefix (vs : List ℕ) (b : ℕ) : List ℕ :=
  vs.take (numFullBlocks vs b * b)

/-- The leftover suffix of `vs` after all full blocks of size `b`. -/
def leftoverList (vs : List ℕ) (b : ℕ) : List ℕ :=
  vs.drop (numFullBlocks vs b * b)

/-- The `i`-th full block of `vs` of size `b`, in the fixed order of `vs`. -/
def blockList (vs : List ℕ) (b i : ℕ) : List ℕ :=
  (vs.drop (i * b)).take b

/-- The vertex set of all full blocks. -/
def fullVerts (vs : List ℕ) (b : ℕ) : Finset ℕ :=
  (fullPrefix vs b).toFinset

/-- The leftover vertex set `Z`. -/
def leftoverVerts (vs : List ℕ) (b : ℕ) : Finset ℕ :=
  (leftoverList vs b).toFinset

/-- The `i`-th full block as a finite vertex set. -/
def blockSet (vs : List ℕ) (b i : ℕ) : Finset ℕ :=
  (blockList vs b i).toFinset

/-- The block index of vertex `v` in `vs` for block size `b`. -/
def blockOf (vs : List ℕ) (b : ℕ) (v : ℕ) : ℕ :=
  vs.idxOf v / b

/-- Canonical injection matching pairing `leftoverList vs b` with the prefix of `fullPrefix vs b`. -/
def leftoverInjectionMatching (vs : List ℕ) (b : ℕ) : List (ℕ × ℕ) :=
  (leftoverList vs b).zip (fullPrefix vs b)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-! ### Basic list and cardinality facts for the split -/

private lemma idxOf_getElem_of_nodup {vs : List ℕ} (hnd : vs.Nodup) {idx : ℕ}
    (hidx : idx < vs.length) : vs.idxOf (vs[idx]'hidx) = idx := by
  have hmem : vs[idx]'hidx ∈ vs := List.getElem_mem hidx
  have hlt : vs.idxOf (vs[idx]'hidx) < vs.length := List.idxOf_lt_length_of_mem hmem
  have hget : vs[vs.idxOf (vs[idx]'hidx)]'hlt = vs[idx]'hidx := List.getElem_idxOf hlt
  exact (List.Nodup.getElem_inj_iff hnd).mp hget

theorem fullPrefix_append_leftoverList (vs : List ℕ) (b : ℕ) :
    fullPrefix vs b ++ leftoverList vs b = vs :=
  List.take_append_drop _ vs

theorem fullPrefix_length (vs : List ℕ) (b : ℕ) :
    (fullPrefix vs b).length = numFullBlocks vs b * b := by
  unfold fullPrefix numFullBlocks
  rw [List.length_take]
  exact Nat.min_eq_left (Nat.div_mul_le_self vs.length b)

theorem leftoverList_length (vs : List ℕ) (b : ℕ) :
    (leftoverList vs b).length = vs.length % b := by
  unfold leftoverList numFullBlocks
  rw [List.length_drop]
  have h := Nat.div_add_mod vs.length b
  rw [Nat.mul_comm]
  omega

theorem fullPrefix_nodup {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    (fullPrefix vs b).Nodup :=
  (List.take_sublist _ vs).nodup hnd

theorem leftoverList_nodup {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    (leftoverList vs b).Nodup :=
  (List.drop_sublist _ vs).nodup hnd

theorem blockList_nodup {vs : List ℕ} (hnd : vs.Nodup) (b i : ℕ) :
    (blockList vs b i).Nodup :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ vs)).nodup hnd

theorem blockList_length {vs : List ℕ} {b i : ℕ} (hi : i < numFullBlocks vs b) :
    (blockList vs b i).length = b := by
  unfold blockList
  rw [List.length_take, List.length_drop]
  have hle : (i + 1) * b ≤ vs.length := by
    have h1 : i + 1 ≤ vs.length / b := hi
    calc (i + 1) * b ≤ (vs.length / b) * b := Nat.mul_le_mul_right b h1
      _ ≤ vs.length := Nat.div_mul_le_self vs.length b
  have hsub : b ≤ vs.length - i * b := by
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega
  exact Nat.min_eq_left hsub

theorem card_fullVerts {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    (fullVerts vs b).card = numFullBlocks vs b * b := by
  unfold fullVerts
  rw [List.toFinset_card_of_nodup (fullPrefix_nodup hnd b), fullPrefix_length]

theorem card_leftoverVerts {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    (leftoverVerts vs b).card = vs.length % b := by
  unfold leftoverVerts
  rw [List.toFinset_card_of_nodup (leftoverList_nodup hnd b), leftoverList_length]

theorem card_blockSet {vs : List ℕ} (hnd : vs.Nodup) {b i : ℕ} (hi : i < numFullBlocks vs b) :
    (blockSet vs b i).card = b := by
  unfold blockSet
  rw [List.toFinset_card_of_nodup (blockList_nodup hnd b i), blockList_length hi]

/-! ### Partition and block-fibre identities -/

theorem disjoint_fullVerts_leftoverVerts {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    Disjoint (fullVerts vs b) (leftoverVerts vs b) := by
  rw [Finset.disjoint_left]
  intro v hvF hvZ
  unfold fullVerts fullPrefix at hvF
  unfold leftoverVerts leftoverList at hvZ
  rw [List.mem_toFinset] at hvF hvZ
  exact List.disjoint_take_drop hnd (le_refl _) hvF hvZ

theorem fullVerts_union_leftoverVerts (vs : List ℕ) (b : ℕ) :
    fullVerts vs b ∪ leftoverVerts vs b = vs.toFinset := by
  ext v
  simp only [Finset.mem_union, fullVerts, leftoverVerts, List.mem_toFinset]
  rw [← List.mem_append, fullPrefix_append_leftoverList]

theorem fullVerts_subset_toFinset (vs : List ℕ) (b : ℕ) :
    fullVerts vs b ⊆ vs.toFinset := by
  rw [← fullVerts_union_leftoverVerts vs b]
  exact Finset.subset_union_left

theorem leftoverVerts_subset_toFinset (vs : List ℕ) (b : ℕ) :
    leftoverVerts vs b ⊆ vs.toFinset := by
  rw [← fullVerts_union_leftoverVerts vs b]
  exact Finset.subset_union_right

theorem sdiff_fullVerts_eq_leftoverVerts {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    vs.toFinset \ fullVerts vs b = leftoverVerts vs b := by
  rw [← fullVerts_union_leftoverVerts vs b, Finset.union_sdiff_cancel_left
    (disjoint_fullVerts_leftoverVerts hnd b)]

theorem sdiff_leftoverVerts_eq_fullVerts {vs : List ℕ} (hnd : vs.Nodup) (b : ℕ) :
    vs.toFinset \ leftoverVerts vs b = fullVerts vs b := by
  rw [← fullVerts_union_leftoverVerts vs b, Finset.union_sdiff_cancel_right
    (disjoint_fullVerts_leftoverVerts hnd b)]

theorem mem_fullVerts_iff {vs : List ℕ} {b : ℕ} (hb : 0 < b) {v : ℕ} :
    v ∈ fullVerts vs b ↔ v ∈ vs ∧ blockOf vs b v < numFullBlocks vs b := by
  unfold fullVerts fullPrefix blockOf
  rw [List.mem_toFinset]
  constructor
  · intro hv
    have hmem : v ∈ vs := List.mem_of_mem_take hv
    have hlt := (List.mem_take_iff_idxOf_lt hmem).mp hv
    exact ⟨hmem, (Nat.div_lt_iff_lt_mul hb).mpr hlt⟩
  · rintro ⟨hmem, hlt⟩
    exact (List.mem_take_iff_idxOf_lt hmem).mpr ((Nat.div_lt_iff_lt_mul hb).mp hlt)

theorem blockOf_lt_numFullBlocks {vs : List ℕ} {b : ℕ} (hb : 0 < b) {v : ℕ}
    (hv : v ∈ fullVerts vs b) : blockOf vs b v < numFullBlocks vs b :=
  ((mem_fullVerts_iff hb).mp hv).2

/-- The `i`-th fibre of `blockOf vs b` inside `fullVerts vs b` is `blockSet vs b i`. -/
theorem filter_blockOf_eq_blockSet {vs : List ℕ} (hnd : vs.Nodup) {b i : ℕ} (hb : 0 < b)
    (hi : i < numFullBlocks vs b) :
    ((fullVerts vs b).filter fun v => blockOf vs b v = i) = blockSet vs b i := by
  ext v
  simp only [Finset.mem_filter, blockSet, List.mem_toFinset]
  constructor
  · rintro ⟨hvF, hblk⟩
    have hmem : v ∈ vs := ((mem_fullVerts_iff hb).mp hvF).1
    have hidx_lt : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hmem
    set r := vs.idxOf v % b
    have hr_lt : r < b := Nat.mod_lt _ hb
    have hidx_eq : i * b + r = vs.idxOf v := by
      unfold blockOf at hblk
      have hdiv := Nat.div_add_mod (vs.idxOf v) b
      rw [hblk, Nat.mul_comm] at hdiv
      exact hdiv
    have hlen : (blockList vs b i).length = b := blockList_length hi
    have hr_len : r < (blockList vs b i).length := hlen.symm ▸ hr_lt
    have hget : (blockList vs b i)[r]'hr_len = v := by
      unfold blockList at hr_len ⊢
      rw [List.getElem_take, List.getElem_drop]
      have hidx_eq' : i * b + r = vs.idxOf v := hidx_eq
      simp only [hidx_eq']
      exact List.getElem_idxOf hidx_lt
    rw [← hget]
    exact List.getElem_mem hr_len
  · intro hvB
    obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hvB
    have hlen : (blockList vs b i).length = b := blockList_length hi
    have hr_lt : r < b := hlen ▸ hr
    have hib_lt : i * b + r < vs.length := by
      have h1 : (i + 1) * b ≤ vs.length := by
        calc (i + 1) * b ≤ (vs.length / b) * b := Nat.mul_le_mul_right b hi
          _ ≤ vs.length := Nat.div_mul_le_self vs.length b
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hvs_get : vs[i * b + r]'hib_lt = v := by
      rw [← hget]
      unfold blockList at hr ⊢
      rw [List.getElem_take, List.getElem_drop]
    have hidx : vs.idxOf v = i * b + r := by
      rw [← hvs_get]
      exact idxOf_getElem_of_nodup hnd hib_lt
    have hblk : blockOf vs b v = i := by
      unfold blockOf
      rw [hidx, Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hr_lt, Nat.add_zero]
    have hmem : v ∈ vs := hvs_get ▸ List.getElem_mem hib_lt
    exact ⟨(mem_fullVerts_iff hb).mpr ⟨hmem, hblk ▸ hi⟩, hblk⟩

/-- Every full block fibre of `blockOf vs b` on `fullVerts vs b` has size `b`. -/
theorem card_filter_blockOf {vs : List ℕ} (hnd : vs.Nodup) {b i : ℕ} (hb : 0 < b)
    (hi : i < numFullBlocks vs b) :
    ((fullVerts vs b).filter fun v => blockOf vs b v = i).card = b := by
  rw [filter_blockOf_eq_blockSet hnd hb hi, card_blockSet hnd hi]

/-! ### Block size bounds and Step A bounds -/

/-- Block size bound, first inequality: `|Z| < b_block`. -/
theorem card_leftoverVerts_lt {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ} (hb : 0 < b) :
    (leftoverVerts vs b).card < b := by
  rw [card_leftoverVerts hnd b]
  exact Nat.mod_lt vs.length hb

/-- Block size bound, second inequality: `b_block ≤ |V \ Z|` when `b_block ≤ |V|`. -/
theorem blockSize_le_card_fullVerts {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ}
    (hle : b ≤ vs.length) : b ≤ (vs.toFinset \ leftoverVerts vs b).card := by
  rw [sdiff_leftoverVerts_eq_fullVerts hnd, card_fullVerts hnd]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact Nat.zero_le _
  · have h1 : 1 ≤ numFullBlocks vs b := Nat.div_pos hle hb
    calc b = 1 * b := (Nat.one_mul b).symm
      _ ≤ numFullBlocks vs b * b := Nat.mul_le_mul_right b h1

/-- Block size bounds combined: `|Z| < b_block ≤ |V \ Z|`, and in particular `|Z| ≤ |V \ Z|`. -/
theorem card_leftoverVerts_le_card_sdiff {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ}
    (hb : 0 < b) (hle : b ≤ vs.length) :
    (leftoverVerts vs b).card ≤ (vs.toFinset \ leftoverVerts vs b).card :=
  le_trans (le_of_lt (card_leftoverVerts_lt hnd hb)) (blockSize_le_card_fullVerts hnd hle)

/-- General upper bound on the number of full blocks. -/
theorem numFullBlocks_le_of_length_le {vs : List ℕ} {b k : ℕ} (hb : 0 < b)
    (hlen : vs.length ≤ k * b) : numFullBlocks vs b ≤ k := by
  unfold numFullBlocks
  refine (Nat.div_le_iff_le_mul_add_pred hb).mpr ?_
  rw [Nat.mul_comm]
  omega

/-- Step A parameter facts for `q ≥ 2` with `b_block = N ^ (q - 1) / 2`, `4 ∣ N`, `0 < N`, and
`b_block ≤ |V| ≤ N ^ q`:
1. `0 < b_block` and `Even b_block`;
2. `1 ≤ numFullBlocks vs b_block ≤ 2 * N`;
3. `|Z| < b_block ≤ |V \ Z|`. -/
theorem stepA_block_params {vs : List ℕ} (hnd : vs.Nodup) {N q : ℕ}
    (hq : 2 ≤ q) (hNpos : 0 < N) (hN4 : 4 ∣ N)
    (hlo : N ^ (q - 1) / 2 ≤ vs.length) (hhi : vs.length ≤ N ^ q) :
    let b := N ^ (q - 1) / 2
    0 < b ∧ Even b ∧ 1 ≤ numFullBlocks vs b ∧ numFullBlocks vs b ≤ 2 * N ∧
      (leftoverVerts vs b).card < b ∧ b ≤ (vs.toFinset \ leftoverVerts vs b).card := by
  dsimp only
  set b := N ^ (q - 1) / 2
  obtain ⟨m, rfl⟩ := hN4
  have hm : 1 ≤ m := by omega
  have hq1 : 1 ≤ q - 1 := by omega
  have hpow4 : 4 ∣ (4 * m) ^ (q - 1) := by
    have hsplit : (4 * m) ^ (q - 1) = (4 * m) * (4 * m) ^ (q - 2) := by
      conv_lhs => rw [show q - 1 = (q - 2) + 1 by omega, pow_succ']
    rw [hsplit]
    exact dvd_mul_of_dvd_left (dvd_mul_right 4 m) _
  have hpow_ge : 4 ≤ (4 * m) ^ (q - 1) := by
    calc 4 ≤ 4 * m := by omega
      _ = (4 * m) ^ 1 := (pow_one _).symm
      _ ≤ (4 * m) ^ (q - 1) := Nat.pow_le_pow_right (by omega) hq1
  have hb_pos : 0 < b := by
    dsimp only [b]
    omega
  have hb_even : Even b := by
    obtain ⟨t, ht⟩ := hpow4
    refine ⟨t, ?_⟩
    dsimp only [b]
    omega
  have htwo_b : 2 * b = (4 * m) ^ (q - 1) := by
    obtain ⟨t, ht⟩ := hpow4
    dsimp only [b]
    omega
  have hNq : (4 * m) ^ q = (2 * (4 * m)) * b := by
    have hsplit : (4 * m) ^ q = (4 * m) * (4 * m) ^ (q - 1) := by
      conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ']
    rw [hsplit, ← htwo_b]
    ring
  have hnum_lo : 1 ≤ numFullBlocks vs b := Nat.div_pos hlo hb_pos
  have hnum_hi : numFullBlocks vs b ≤ 2 * (4 * m) :=
    numFullBlocks_le_of_length_le hb_pos (hNq ▸ hhi)
  exact ⟨hb_pos, hb_even, hnum_lo, hnum_hi,
    card_leftoverVerts_lt hnd hb_pos, blockSize_le_card_fullVerts hnd hlo⟩

/-- Step A parameter facts for `q = 1` (`b_block = 1`): there are no leftovers, the number of full
blocks equals `vs.length`, and every block is a singleton. -/
theorem stepA_singleton_params {vs : List ℕ} (hnd : vs.Nodup) :
    leftoverVerts vs 1 = ∅ ∧ numFullBlocks vs 1 = vs.length ∧
      fullVerts vs 1 = vs.toFinset ∧
      ∀ i < vs.length, (blockSet vs 1 i).card = 1 := by
  have hZ : leftoverVerts vs 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [card_leftoverVerts hnd 1, Nat.mod_one]
  have hnum : numFullBlocks vs 1 = vs.length := Nat.div_one vs.length
  have hF : fullVerts vs 1 = vs.toFinset := by
    rw [← sdiff_leftoverVerts_eq_fullVerts hnd 1, hZ, Finset.sdiff_empty]
  refine ⟨hZ, hnum, hF, fun i hi => card_blockSet hnd (hnum.symm ▸ hi)⟩

/-! ### Step C attachment of leftover vertices by the injection lemma -/

private lemma map_snd_zip_sublist {α β : Type*} (l₁ : List α) (l₂ : List β) :
    List.Sublist ((l₁.zip l₂).map Prod.snd) l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    cases l₂ with
    | nil => simp
    | cons b s =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact List.Sublist.cons_cons b (ih s)

/-- The canonical zip matching `leftoverInjectionMatching vs b` injects `leftoverVerts vs b` into
`fullVerts vs b` whenever `0 < b ≤ vs.length` and `vs.Nodup`. -/
theorem leftoverInjectionMatching_spec {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ}
    (hb : 0 < b) (hle : b ≤ vs.length) :
    (∀ e ∈ leftoverInjectionMatching vs b, e.1 ∈ leftoverVerts vs b ∧ e.2 ∈ fullVerts vs b) ∧
    ((leftoverInjectionMatching vs b).map Prod.snd).Nodup ∧
    (∀ v ∈ leftoverVerts vs b, ∃ e ∈ leftoverInjectionMatching vs b, e.1 = v) := by
  have hlen : (leftoverList vs b).length ≤ (fullPrefix vs b).length := by
    rw [leftoverList_length, fullPrefix_length]
    have hlt := Nat.mod_lt vs.length hb
    have h1 : 1 ≤ numFullBlocks vs b := Nat.div_pos hle hb
    have hmul : b ≤ numFullBlocks vs b * b := by
      calc b = 1 * b := (Nat.one_mul b).symm
        _ ≤ numFullBlocks vs b * b := Nat.mul_le_mul_right b h1
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have hmem1 : e.1 ∈ leftoverList vs b := (List.of_mem_zip he).1
    have hmem2 : e.2 ∈ fullPrefix vs b := (List.of_mem_zip he).2
    exact ⟨List.mem_toFinset.mpr hmem1, List.mem_toFinset.mpr hmem2⟩
  · unfold leftoverInjectionMatching
    exact (map_snd_zip_sublist _ _).nodup (fullPrefix_nodup hnd b)
  · intro v hv
    rw [leftoverVerts, List.mem_toFinset] at hv
    unfold leftoverInjectionMatching
    have hfst : ((leftoverList vs b).zip (fullPrefix vs b)).map Prod.fst = leftoverList vs b :=
      List.map_fst_zip hlen
    rw [← hfst] at hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    exact ⟨e, he, rfl⟩

/-- **Injection step of Step C**: given a witness `E_full` with expansion `γ ∈ [0, 1]` on the union
of full blocks `fullVerts vs b`, appending any injection matching `M_Z` from the leftover set
`leftoverVerts vs b` into `fullVerts vs b` yields a spanning witness on `vs.toFinset` with
expansion at least `γ / 2`. -/
theorem isExpansionExpanderOn_of_blockSplit_injection {n b : ℕ} {vs : List ℕ}
    {E_full M_Z : List (ℕ × ℕ)} {γ : ℝ}
    (hnd : vs.Nodup) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hfull : (Graph.mk n E_full).IsExpansionExpanderOn (fullVerts vs b) γ)
    (hMZ : ∀ e ∈ M_Z, e.1 ∈ leftoverVerts vs b ∧ e.2 ∈ fullVerts vs b)
    (hsnd : (M_Z.map Prod.snd).Nodup)
    (hcov : ∀ v ∈ leftoverVerts vs b, ∃ e ∈ M_Z, e.1 = v) :
    (Graph.mk n (E_full ++ M_Z)).IsExpansionExpanderOn vs.toFinset (γ / 2) := by
  have hdisj := disjoint_fullVerts_leftoverVerts hnd b
  refine isExpansionExpanderOn_of_injection hγ0 hγ1 (fullVerts_subset_toFinset vs b) hfull ?_ hsnd ?_
  · intro e he
    obtain ⟨h1, h2⟩ := hMZ e he
    exact ⟨leftoverVerts_subset_toFinset vs b h1,
      fun hF => Finset.disjoint_left.mp hdisj hF h1, h2⟩
  · intro v hvX hvnotF
    have hvZ : v ∈ leftoverVerts vs b := by
      rw [← sdiff_fullVerts_eq_leftoverVerts hnd b]
      exact Finset.mem_sdiff.mpr ⟨hvX, hvnotF⟩
    exact hcov v hvZ

/-- **Combined Step C witness expansion**: if each full block of size `b > 0` expands by `β ∈ [0, 1]`
in `Eint`, a degree-9 `α`-expander macro graph `H` on the `numFullBlocks vs b` blocks supplies
bipartite perfect matchings forming `Eext`, and `M_Z` injects the leftover set `Z` into the full
blocks, then `Eint ++ Eext ++ M_Z` is a spanning witness on `vs.toFinset` with expansion at least
`α * β / 20`. -/
theorem isExpansionExpanderOn_of_blockSplit_macro_and_injection {n b : ℕ} {vs : List ℕ}
    {Eint Eext M_Z : List (ℕ × ℕ)} {H : Graph} {α β : ℝ} {M : ℕ → List (ℕ × ℕ)}
    (hnd : vs.Nodup) (hb : 0 < b)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hHn : H.n = numFullBlocks vs b)
    (hHvalid : H.IsValid) (hHdeg : ∀ i < H.n, H.deg i ≤ 9)
    (hHexp : H.IsExpansionExpanderOn H.verts α)
    (hint : ∀ i < numFullBlocks vs b,
      (Graph.mk n Eint).IsExpansionExpanderOn (blockSet vs b i) β)
    (hM : ∀ j < H.m, IsBipartiteMatching
      (blockSet vs b (edgeAt H.edges j).1)
      (blockSet vs b (edgeAt H.edges j).2) (M j))
    (hperm : Eext.Perm ((List.range H.m).flatMap M))
    (hMZ : ∀ e ∈ M_Z, e.1 ∈ leftoverVerts vs b ∧ e.2 ∈ fullVerts vs b)
    (hsnd : (M_Z.map Prod.snd).Nodup)
    (hcov : ∀ v ∈ leftoverVerts vs b, ∃ e ∈ M_Z, e.1 = v) :
    (Graph.mk n ((Eint ++ Eext) ++ M_Z)).IsExpansionExpanderOn vs.toFinset (α * β / 20) := by
  have hfull : (Graph.mk n (Eint ++ Eext)).IsExpansionExpanderOn (fullVerts vs b) (α * β / 10) := by
    refine isExpansionExpanderOn_of_macro_blocks_nine (b := b) (blockOf vs b)
      hα0 hα1 hβ0 hβ1 hHvalid hHdeg hHexp ?_ ?_ ?_ ?_ hperm
    · intro v hv
      rw [hHn]
      exact blockOf_lt_numFullBlocks hb hv
    · intro i hi
      exact card_filter_blockOf hnd hb (hHn ▸ hi)
    · intro i hi
      rw [filter_blockOf_eq_blockSet hnd hb (hHn ▸ hi)]
      exact hint i (hHn ▸ hi)
    · intro j hj
      have he : edgeAt H.edges j ∈ H.edges := by
        unfold edgeAt
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hv := hHvalid _ he
      rw [filter_blockOf_eq_blockSet hnd hb (hHn ▸ hv.1),
        filter_blockOf_eq_blockSet hnd hb (hHn ▸ hv.2)]
      exact hM j hj
  have hγ0 : 0 ≤ α * β / 10 := by positivity
  have hγ1 : α * β / 10 ≤ 1 := by nlinarith
  have hfinal := isExpansionExpanderOn_of_blockSplit_injection hnd hγ0 hγ1 hfull hMZ hsnd hcov
  have hdiv : α * β / 10 / 2 = α * β / 20 := by ring
  rw [hdiv] at hfinal
  exact hfinal

end MinCostFlow.ExpanderDecomp
