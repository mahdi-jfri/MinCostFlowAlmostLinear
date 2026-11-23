module

public import MinCostFlow.SparseCore.Program.AssemblyWordSize
public import MinCostFlow.SparseCore.Program.OrdStoreImplements
public import WordRAM.Logic

/-!
# Compacting an input order list in linear time (`AssemblyCompactOrd`)

An input order stored as `OrdListAt mem ordPtr ord words` may contain arbitrarily many empty
vertex records `[v, 0]`, so `ordListWords mem ordPtr` can be much larger than `G.m`. Calling the
order store's initialization (`ordStore_implements_cap`) directly on `ordPtr` would incur a cost
factor `ordStoreLog eCap` on `ordListWords`, whereas `sparseCoreOrdMachineContractKF.initCost` pays
`ordListWords` without a log factor and pays `(G.m + 1) * bundleLogFactor M N` inside `tool.cost`.

This file resolves that mismatch cleanly without changing the contract:
1. `asmCompactOrdBody` (`[ordPtr, dst]`) copies only the non-empty vertex records of `ordPtr` to
   `dst` in `O(words + 1)` steps (no log factor) and at most `words` words of heap space.
2. The compacted order `compactRecs` satisfies `OrdListAt` with the exact same order `ord`
   (`ordOfRecords_compactRecs`), has at most `words` words (`ordRecordsWords_compactRecs_le`), and
   for any rotation order of a valid graph `G` has at most `1 + 6 * G.m` words
   (`compactOrdWords_le_of_rotation`).
3. Consequently, P1's initialization cost on the compacted copy is at most
   `32000 * 6 * capExp * (G.m + 1) * bundleLogFactor M N` (`ordStoreInitCost_le_of_compact`), which
   is paid by `tool.cost (initOrd ...)` in `sparseCoreOrdMachineContractKF`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-! ## Pure list lemmas for filtering empty records -/

/-- Drop empty vertex records from an order-record list. -/
def compactRecs (recs : List (ℕ × List End)) : List (ℕ × List End) :=
  recs.filter fun p => !p.2.isEmpty

theorem compactRecs_nodup {recs : List (ℕ × List End)} (hnd : (recs.map Prod.fst).Nodup) :
    ((compactRecs recs).map Prod.fst).Nodup :=
  (List.Sublist.map Prod.fst List.filter_sublist).nodup hnd

theorem ordOfRecords_compactRecs :
    ∀ {recs : List (ℕ × List End)}, (recs.map Prod.fst).Nodup →
      ordOfRecords (compactRecs recs) = ordOfRecords recs
  | [], _ => rfl
  | (v, xs) :: rs, hnd => by
    have hnd_cons : v ∉ rs.map Prod.fst ∧ (rs.map Prod.fst).Nodup := by
      simpa [List.map_cons, List.nodup_cons] using hnd
    have ih := ordOfRecords_compactRecs hnd_cons.2
    funext u
    cases xs with
    | nil =>
      simp only [compactRecs, List.filter_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      change ordOfRecords (compactRecs rs) u = ordOfRecords ((v, []) :: rs) u
      rw [ih]
      by_cases huv : u = v
      · subst huv
        have hnone : rs.find? (fun p => p.1 == u) = none :=
          List.find?_eq_none.mpr fun p hp => by
            simp only [beq_iff_eq]
            exact fun hpeq => hnd_cons.1 (List.mem_map.mpr ⟨p, hp, hpeq⟩)
        simp [ordOfRecords, hnone]
      · simp [ordOfRecords, beq_eq_false_iff_ne.mpr (Ne.symm huv)]
    | cons x rest =>
      simp only [compactRecs, List.filter_cons, List.isEmpty_cons, Bool.not_false, ↓reduceIte]
      change ordOfRecords ((v, x :: rest) :: compactRecs rs) u =
        ordOfRecords ((v, x :: rest) :: rs) u
      by_cases huv : u = v
      · subst huv; simp [ordOfRecords]
      · simp only [ordOfRecords, List.find?_cons, beq_eq_false_iff_ne.mpr (Ne.symm huv)]
        exact congrFun ih u

theorem ordRecordsWords_compactRecs_le :
    ∀ recs : List (ℕ × List End), ordRecordsWords (compactRecs recs) ≤ ordRecordsWords recs
  | [] => le_rfl
  | (_, xs) :: rs => by
    have ih := ordRecordsWords_compactRecs_le rs
    cases xs <;>
      simp only [compactRecs, List.filter_cons, List.isEmpty_nil, List.isEmpty_cons, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte, ordRecordsWords, List.map_cons,
        List.sum_cons] at ih ⊢ <;> omega

theorem ordRecordsWords_compactRecs_le_three_sum :
    ∀ recs : List (ℕ × List End),
      ordRecordsWords (compactRecs recs) ≤ 3 * (recs.map fun p => p.2.length).sum
  | [] => by simp [compactRecs, ordRecordsWords]
  | (_, xs) :: rs => by
    have ih := ordRecordsWords_compactRecs_le_three_sum rs
    cases xs <;>
      simp only [compactRecs, List.filter_cons, List.isEmpty_nil, List.isEmpty_cons, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte, ordRecordsWords, List.map_cons,
        List.sum_cons, List.length_nil, List.length_cons] at ih ⊢ <;> omega

/-- Sum of list lengths in a nodup record list representing a rotation of a valid graph `G` is at
most `2 * G.m`. -/
theorem ordRecords_sum_len_le_two_m {G : MGraph} {recs : List (ℕ × List End)}
    (hG : G.IsValid) (hnd : (recs.map Prod.fst).Nodup)
    (hrot : IsRotationOrder G (ordOfRecords recs)) :
    (recs.map fun p => p.2.length).sum ≤ 2 * G.m := by
  obtain ⟨ρ, hρ⟩ := hrot
  have hlen_eq : ∀ p ∈ recs, p.2.length = (ρ.order p.1).length := by
    intro p hp
    have hfind : ordOfRecords recs p.1 = p.2 := by
      clear hρ
      induction recs with
      | nil => cases hp
      | cons hd tl ih =>
        have hndc : hd.1 ∉ tl.map Prod.fst ∧ (tl.map Prod.fst).Nodup := by
          simpa [List.map_cons, List.nodup_cons] using hnd
        rcases List.mem_cons.mp hp with rfl | hmem
        · simp [ordOfRecords]
        · have hne : hd.1 ≠ p.1 := fun h => hndc.1 (h ▸ List.mem_map.mpr ⟨p, hmem, rfl⟩)
          simp only [ordOfRecords, List.find?_cons, beq_eq_false_iff_ne.mpr hne]
          exact ih hndc.2 hmem
    rw [← hfind, ← hρ]
  have hsum_eq : (recs.map fun p => p.2.length).sum =
      (recs.map Prod.fst).toFinset.sum fun v => (ρ.order v).length := by
    rw [List.sum_toFinset _ hnd, List.map_map]
    congr 1
    exact List.map_congr_left fun p hp => hlen_eq p hp
  rw [hsum_eq]
  have hsub : (recs.map Prod.fst).toFinset.sum (fun v => (ρ.order v).length) ≤
      G.V.sum fun v => (ρ.order v).length := by
    have hzero : ∀ v ∈ (recs.map Prod.fst).toFinset, v ∉ G.V → (ρ.order v).length = 0 := by
      intro v _ hv
      rcases hnil : ρ.order v with _ | ⟨x, xs⟩
      · rfl
      · exfalso
        have hx : x ∈ ρ.order v := by rw [hnil]; exact List.mem_cons_self
        have ⟨he, hsrc⟩ := (ρ.mem_order v x).mp hx
        have : G.src x ∈ G.V := by
          unfold MGraph.src
          split
          · exact (hG x.1 he).1
          · exact (hG x.1 he).2
        exact hv (hsrc ▸ this)
    calc (recs.map Prod.fst).toFinset.sum (fun v => (ρ.order v).length)
        = ((recs.map Prod.fst).toFinset ∩ G.V).sum (fun v => (ρ.order v).length) := by
          symm
          apply Finset.sum_subset Finset.inter_subset_left
          intro v hv hnot
          exact hzero v hv fun hvG => hnot (Finset.mem_inter.mpr ⟨hv, hvG⟩)
      _ ≤ G.V.sum fun v => (ρ.order v).length :=
          Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hrot_sum : G.V.sum (fun v => (ρ.order v).length) ≤ 2 * G.m := by
    have hcard : ∀ v, (ρ.order v).length = (ρ.order v).toFinset.card := fun v =>
      (List.toFinset_card_of_nodup (ρ.nodup v)).symm
    simp_rw [hcard]
    have hdisj : (G.V : Set ℕ).PairwiseDisjoint fun v => (ρ.order v).toFinset := by
      intro u _ v _ huv
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hxu hxv
      have hu := ((ρ.mem_order u x).mp (List.mem_toFinset.mp hxu)).2
      have hv := ((ρ.mem_order v x).mp (List.mem_toFinset.mp hxv)).2
      exact huv (hu.symm.trans hv)
    rw [← Finset.card_biUnion hdisj]
    have hsubE : (G.V.biUnion fun v => (ρ.order v).toFinset) ⊆ G.E ×ˢ ({true, false} : Finset Bool) := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨v, _, hxv⟩
      have he := ((ρ.mem_order v x).mp (List.mem_toFinset.mp hxv)).1
      exact Finset.mem_product.mpr ⟨he, by cases x.2 <;> simp⟩
    calc (G.V.biUnion fun v => (ρ.order v).toFinset).card
        ≤ (G.E ×ˢ ({true, false} : Finset Bool)).card := Finset.card_le_card hsubE
      _ = G.E.card * 2 := by simp
      _ = 2 * G.m := by unfold MGraph.m; ring
  exact le_trans hsub hrot_sum

/-- For a valid graph `G` and a rotation order, the compacted order has at most `1 + 6 * G.m`
words. -/
theorem compactOrdWords_le_of_rotation {G : MGraph} {recs : List (ℕ × List End)}
    (hG : G.IsValid) (hnd : (recs.map Prod.fst).Nodup)
    (hrot : IsRotationOrder G (ordOfRecords recs)) :
    1 + ordRecordsWords (compactRecs recs) ≤ 1 + 6 * G.m := by
  have h1 := ordRecordsWords_compactRecs_le_three_sum recs
  have h2 := ordRecords_sum_len_le_two_m hG hnd hrot
  omega

/-- P1's initialization cost on the compacted order is paid by `(G.m + 1) * bundleLogFactor M N`
with constant `32000 * 6 * capExp`. -/
theorem ordStoreInitCost_le_of_compact {capExp limbMul L M N vCap eCap : ℕ} {G : MGraph}
    {recs : List (ℕ × List End)} (hG : G.IsValid)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hnd : (recs.map Prod.fst).Nodup) (hrot : IsRotationOrder G (ordOfRecords recs)) :
    ordStoreMul * (1 + ordRecordsWords (compactRecs recs)) * ordStoreLog eCap ≤
      ordStoreMul * 6 * capExp * ((G.m + 1) * bundleLogFactor M N) := by
  have h1 := compactOrdWords_le_of_rotation hG hnd hrot
  have hlog := ordStoreLog_le_capExp_mul_lg hcap
  have h2 : 1 + ordRecordsWords (compactRecs recs) ≤ 6 * (G.m + 1) := by omega
  calc ordStoreMul * (1 + ordRecordsWords (compactRecs recs)) * ordStoreLog eCap
      ≤ ordStoreMul * (6 * (G.m + 1)) * (capExp * bundleLogFactor M N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hlog
    _ = ordStoreMul * 6 * capExp * ((G.m + 1) * bundleLogFactor M N) := by ring

/-! ## Word-RAM procedure `asmCompactOrdBody` -/

/-- Inner copy loop: copies `r8` words from `r3` to `r4` using counter `r9`. -/
def asmCompactCopyLoop : Stmt :=
  forRange 9 (.const 0) (.reg 8)
    (.store (.bin .add (.reg 4) (.reg 9)) (.load (.bin .add (.reg 3) (.reg 9))))

/-- Procedure body `asmCompactOrdBody`, called as `[ordPtr, dst]`:
scans the `mem[ordPtr]` records starting at `ordPtr + 1`, writes only those with `len > 0`
starting at `dst + 1`, writes their count at `dst`, and returns the end address `outPtr`. -/
def asmCompactOrdBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 2)
    (.assign 7 (.load (.reg 3)) ;;
     .assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .assign 3 (.bin .add (.reg 3) (.const 2)) ;;
     .cond (.reg 8)
       (.store (.reg 4) (.reg 7) ;;
        .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
        .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
        asmCompactCopyLoop ;;
        .assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
        .assign 5 (.bin .add (.reg 5) (.const 1)))
       .nop ;;
     .assign 3 (.bin .add (.reg 3) (.reg 8))) ;;
  .store (.reg 1) (.reg 5) ;;
  .ret (.reg 4)

theorem asmCompactOrdBody_noRand : asmCompactOrdBody.NoRand := by
  simp [asmCompactOrdBody, asmCompactCopyLoop, forRange, forUp, Stmt.NoRand]

/-! ## Verification of `asmCompactOrdBody` -/

private theorem readOrdRecords_append (mem : ℕ → ℕ) :
    ∀ (c₁ c₂ a : ℕ),
      readOrdRecords mem (c₁ + c₂) a =
        readOrdRecords mem c₁ a ++
          readOrdRecords mem c₂ (a + ordRecordsWords (readOrdRecords mem c₁ a))
  | 0, c₂, a => by simp [readOrdRecords, ordRecordsWords]
  | c₁ + 1, c₂, a => by
    have hsucc : c₁ + 1 + c₂ = (c₁ + c₂) + 1 := by omega
    rw [hsucc]
    simp only [readOrdRecords, ordRecordsWords, List.map_cons, List.sum_cons, List.length_map,
      readList_length, List.cons_append]
    congr 1
    rw [readOrdRecords_append mem c₁ c₂ (a + 2 + mem (a + 1))]
    simp only [ordRecordsWords, Nat.add_assoc]

private theorem readOrdRecords_congr {mem₁ mem₂ : ℕ → ℕ} :
    ∀ (c a : ℕ),
      (∀ x, a ≤ x → x < a + ordRecordsWords (readOrdRecords mem₁ c a) → mem₂ x = mem₁ x) →
      readOrdRecords mem₂ c a = readOrdRecords mem₁ c a
  | 0, _, _ => rfl
  | c + 1, a, h => by
    have hwords : ordRecordsWords (readOrdRecords mem₁ (c + 1) a) =
        2 + mem₁ (a + 1) + ordRecordsWords (readOrdRecords mem₁ c (a + 2 + mem₁ (a + 1))) := by
      simp [readOrdRecords, ordRecordsWords, readList_length]
    have h0 : mem₂ a = mem₁ a := h a le_rfl (by omega)
    have h1 : mem₂ (a + 1) = mem₁ (a + 1) := h (a + 1) (by omega) (by omega)
    have hlist : readList mem₂ (a + 2) (mem₁ (a + 1)) = readList mem₁ (a + 2) (mem₁ (a + 1)) := by
      apply List.ext_getElem (by simp [readList_length])
      intro j hj _
      rw [readList_getElem, readList_getElem]
      rw [readList_length] at hj
      exact h (a + 2 + j) (by omega) (by omega)
    have hrest := readOrdRecords_congr c (a + 2 + mem₁ (a + 1)) fun x hx1 hx2 =>
      h x (by omega) (by omega)
    simp only [readOrdRecords, h0, h1, hlist, hrest]

private theorem ordRecordsWords_append (r₁ r₂ : List (ℕ × List End)) :
    ordRecordsWords (r₁ ++ r₂) = ordRecordsWords r₁ + ordRecordsWords r₂ := by
  simp [ordRecordsWords, List.map_append, List.sum_append]

private theorem compactRecs_append (r₁ r₂ : List (ℕ × List End)) :
    compactRecs (r₁ ++ r₂) = compactRecs r₁ ++ compactRecs r₂ := by
  simp [compactRecs, List.filter_append]

private theorem asmCompactCopyLoop_runs {w src dst len : ℕ} {p : Program} (ω : ℕ → Bool)
    (st₀ : State)
    (hw : 1 < 2 ^ w) (hsrc : src + len ≤ dst) (hdst : dst + len < 2 ^ w)
    (hr3 : st₀.regs 3 = src) (hr4 : st₀.regs 4 = dst) (hr8 : st₀.regs 8 = len)
    (hvals : ∀ j < len, st₀.mem (src + j) < 2 ^ w) (hz : ZeroFrom st₀.mem dst) :
    ∃ st' c,
      Runs w p ω asmCompactCopyLoop st₀ .normal st' c ∧
      (∀ r, r ≠ 9 → st'.regs r = st₀.regs r) ∧
      (∀ a < dst, st'.mem a = st₀.mem a) ∧
      (∀ j < len, st'.mem (dst + j) = st₀.mem (src + j)) ∧
      ZeroFrom st'.mem (dst + len) ∧
      c ≤ 25 * len + 15 := by
  have htrip := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 8)
    (body := .store (.bin .add (.reg 4) (.reg 9)) (.load (.bin .add (.reg 3) (.reg 9))))
    (P := fun st => st = st₀)
    (Inv := fun j st =>
      st.regs 9 = j ∧ (∀ r, r ≠ 9 → st.regs r = st₀.regs r) ∧
      (∀ a < dst, st.mem a = st₀.mem a) ∧
      (∀ t < j, st.mem (dst + t) = st₀.mem (src + t)) ∧
      ZeroFrom st.mem (dst + j))
    12 0 len (Nat.zero_le len) hw (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), by simp, fun r hr => by simp [hr],
        fun _ _ => rfl, fun _ ht => absurd ht (Nat.not_lt_zero _), by simpa using hz⟩)
    (fun _ st _ _ hi => hi.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq ((hi.2.1 8 (by decide)).trans hr8))
    (fun j _ hjlt => by
      intro st ω' ⟨h9, hregs, hlt, hcp, hzj⟩
      have h3 : st.regs 3 = src := (hregs 3 (by decide)).trans hr3
      have h4 : st.regs 4 = dst := (hregs 4 (by decide)).trans hr4
      have hsrcj : st.mem (src + j) = st₀.mem (src + j) := hlt (src + j) (by omega)
      have hload : (Expr.load (.bin .add (.reg 3) (.reg 9))).eval w st = some (st₀.mem (src + j)) :=
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq h3) (Expr.eval_reg_of_eq h9) (by omega))
          hsrcj
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + j) (st₀.mem (src + j)) }, _,
        runs_store_iff.mpr ⟨dst + j, st₀.mem (src + j),
          Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h9) (by omega),
          hload, rfl, rfl, rfl⟩,
        ⟨⟨by simp, fun r hr => by simp [hr, hregs r hr],
          fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt a ha,
          fun t ht => by
            dsimp only
            by_cases htj : t = j
            · subst htj; simp
            · rw [Function.update_of_ne (by omega)]; exact hcp t (by omega),
          fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hzj a (by omega)⟩,
          h9⟩, by simp [Expr.size]⟩)
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htrip st₀ ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    exact ⟨st', c, hrun, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2, by
      simp [Expr.size] at hc; omega⟩

private theorem sum_range_len_le_words (mem : ℕ → ℕ) (ordPtr : ℕ) :
    ∀ (count : ℕ),
      rangeCost (fun i => 25 * ((readOrdRecords mem count (ordPtr + 1)).getD i (0, [])).2.length + 85)
        0 count ≤ 45 * ordRecordsWords (readOrdRecords mem count (ordPtr + 1)) := by
  intro count
  have haux : ∀ (c a : ℕ),
      ((List.range c).map fun i =>
        25 * ((readOrdRecords mem c a).getD i (0, [])).2.length + 85).sum ≤
      45 * ordRecordsWords (readOrdRecords mem c a) := by
    intro c
    induction c with
    | zero => intro _; simp [readOrdRecords, ordRecordsWords]
    | succ c ih =>
      intro a
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have h0 : ((readOrdRecords mem (c + 1) a).getD 0 (0, [])).2.length = mem (a + 1) := by
        simp [readOrdRecords, readList_length]
      have htl : ((List.range c).map (fun x =>
          25 * ((readOrdRecords mem (c + 1) a).getD (x + 1) (0, [])).2.length + 85)).sum =
          ((List.range c).map (fun x =>
            25 * ((readOrdRecords mem c (a + 2 + mem (a + 1))).getD x (0, [])).2.length + 85)).sum := by
        congr 1
      rw [h0]
      change 25 * mem (a + 1) + 85 +
          ((List.range c).map fun x =>
            25 * ((readOrdRecords mem (c + 1) a).getD (x + 1) (0, [])).2.length + 85).sum ≤ _
      rw [htl]
      have ih' := ih (a + 2 + mem (a + 1))
      have hw : ordRecordsWords (readOrdRecords mem (c + 1) a) =
          2 + mem (a + 1) + ordRecordsWords (readOrdRecords mem c (a + 2 + mem (a + 1))) := by
        simp [readOrdRecords, ordRecordsWords, readList_length]
      rw [hw]
      omega
  rw [rangeCost_zero_eq_range]
  exact haux count (ordPtr + 1)

private theorem asmCompactOuterLoop_triple {w ordPtr dst words : ℕ} {ord : ℕ → List End}
    (p : Program) (mem : ℕ → ℕ)
    (hw : 4 < 2 ^ w) (hord : OrdListAt mem ordPtr ord words) (hord_le : ordPtr + words ≤ dst)
    (hvals : ∀ j < words, mem (ordPtr + j) < 2 ^ w)
    (hz : ZeroFrom mem dst)
    (hdst : dst + (1 + ordRecordsWords (compactRecs (readOrdRecordsAt mem ordPtr))) < 2 ^ w) :
    let count := mem ordPtr
    let recs := readOrdRecordsAt mem ordPtr
    Triple w p
      (fun st => st.regs 0 = ordPtr ∧ st.regs 1 = dst ∧ st.regs 2 = count ∧
        st.regs 3 = ordPtr + 1 ∧ st.regs 4 = dst + 1 ∧ st.regs 5 = 0 ∧
        st.mem = mem)
      (forRange 6 (.const 0) (.reg 2)
        (.assign 7 (.load (.reg 3)) ;;
         .assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
         .assign 3 (.bin .add (.reg 3) (.const 2)) ;;
         .cond (.reg 8)
           (.store (.reg 4) (.reg 7) ;;
            .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
            .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
            asmCompactCopyLoop ;;
            .assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
            .assign 5 (.bin .add (.reg 5) (.const 1)))
           .nop ;;
         .assign 3 (.bin .add (.reg 3) (.reg 8))))
      (normalPost fun st' =>
        st'.regs 1 = dst ∧
        st'.regs 4 = dst + 1 + ordRecordsWords (compactRecs recs) ∧
        st'.regs 5 = (compactRecs recs).length ∧
        readOrdRecords st'.mem (compactRecs recs).length (dst + 1) = compactRecs recs ∧
        (∀ a < dst, st'.mem a = mem a) ∧
        ZeroFrom st'.mem (dst + 1 + ordRecordsWords (compactRecs recs)))
      (fun _ => 80 * words + 45) := by
  intro count recs
  change dst + (1 + ordRecordsWords (compactRecs recs)) < 2 ^ w at hdst
  have h1w : 1 < 2 ^ w := by omega
  have hwords_eq : words = 1 + ordRecordsWords recs := hord.2.2
  have hcnt_le : 2 * count ≤ ordRecordsWords recs := by
    have h1 := ordRecordsWords_ge_two_mul recs
    have h2 : recs.length = count := readOrdRecords_length mem count (ordPtr + 1)
    omega
  have hpref_le : ∀ i ≤ count, ordRecordsWords (readOrdRecords mem i (ordPtr + 1)) ≤ ordRecordsWords recs := by
    intro i hi
    have hsp := readOrdRecords_append mem i (count - i) (ordPtr + 1)
    rw [show i + (count - i) = count by omega] at hsp
    change ordRecordsWords (readOrdRecords mem i (ordPtr + 1)) ≤
      ordRecordsWords (readOrdRecords mem count (ordPtr + 1))
    rw [hsp, ordRecordsWords_append]; omega
  let P0 : State → Prop := fun st => st.regs 0 = ordPtr ∧ st.regs 1 = dst ∧ st.regs 2 = count ∧
    st.regs 3 = ordPtr + 1 ∧ st.regs 4 = dst + 1 ∧ st.regs 5 = 0 ∧ st.mem = mem
  let Inv : ℕ → State → Prop := fun i st =>
    let pref := readOrdRecords mem i (ordPtr + 1)
    let comp := compactRecs pref
    st.regs 0 = ordPtr ∧ st.regs 1 = dst ∧ st.regs 2 = count ∧ st.regs 6 = i ∧
    st.regs 3 = ordPtr + 1 + ordRecordsWords pref ∧
    st.regs 4 = dst + 1 + ordRecordsWords comp ∧
    st.regs 5 = comp.length ∧
    readOrdRecords st.mem comp.length (dst + 1) = comp ∧
    (∀ a < dst, st.mem a = mem a) ∧
    ZeroFrom st.mem (dst + 1 + ordRecordsWords comp)
  have htrip := Triple.forRange_le (w := w) (p := p) (P := P0) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body :=
      .assign 7 (.load (.reg 3)) ;;
      .assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
      .assign 3 (.bin .add (.reg 3) (.const 2)) ;;
      .cond (.reg 8)
        (.store (.reg 4) (.reg 7) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
         .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
         asmCompactCopyLoop ;;
         .assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
         .assign 5 (.bin .add (.reg 5) (.const 1)))
        .nop ;;
      .assign 3 (.bin .add (.reg 3) (.reg 8)))
    (Inv := Inv)
    (fun i => 25 * ((readOrdRecords mem count (ordPtr + 1)).getD i (0, [])).2.length + 85)
    0 count (Nat.zero_le count) h1w (fun _ => by omega)
    (fun st hst => by
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, hmem⟩
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only [Inv]
      simp only [readOrdRecords, compactRecs, List.filter_nil, ordRecordsWords, List.map_nil,
        List.sum_nil, List.length_nil, Nat.add_zero]
      refine ⟨by simp [h0], by simp [h1], by simp [h2], by simp, by simp [h3], by simp [h4],
        by simp [h5], trivial, fun _ _ => by simp [hmem], fun a ha => by simp [hmem]; exact hz a (by omega)⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.2.2.1)
    (fun i _ hilt => by
      intro st ω hinv
      dsimp only [Inv] at hinv
      rcases hinv with ⟨h0, h1, h2, h6, h3, h4, h5, hread, hlt, hzc⟩
      set pref := readOrdRecords mem i (ordPtr + 1) with hpref_def
      set comp := compactRecs pref with hcomp_def
      set inP := ordPtr + 1 + ordRecordsWords pref with hinP_def
      set outP := dst + 1 + ordRecordsWords comp with houtP_def
      have hsp1 := readOrdRecords_append mem i 1 (ordPtr + 1)
      have hsp2 := readOrdRecords_append mem (i + 1) (count - (i + 1)) (ordPtr + 1)
      rw [show i + 1 + (count - (i + 1)) = count by omega] at hsp2
      have hrec1 : readOrdRecords mem 1 inP =
          [(mem inP, (readList mem (inP + 2) (mem (inP + 1))).map endOfKey)] := rfl
      set v := mem inP
      set len := mem (inP + 1)
      set xs := (readList mem (inP + 2) len).map endOfKey
      have hpref_succ : readOrdRecords mem (i + 1) (ordPtr + 1) = pref ++ [(v, xs)] := by
        rw [hsp1, hrec1]
      have hwords_succ : ordRecordsWords (readOrdRecords mem (i + 1) (ordPtr + 1)) =
          ordRecordsWords pref + (2 + len) := by
        rw [hpref_succ, ordRecordsWords_append]
        simp [ordRecordsWords, xs, readList_length]
      have hsucc_le : ordRecordsWords pref + (2 + len) ≤ ordRecordsWords recs := by
        rw [← hwords_succ]; exact hpref_le (i + 1) (by omega)
      have hcomp_le : ordRecordsWords comp ≤ ordRecordsWords pref := ordRecordsWords_compactRecs_le pref
      have hlen_getD : ((readOrdRecords mem count (ordPtr + 1)).getD i (0, [])).2.length = len := by
        have hlen_p : pref.length = i := readOrdRecords_length mem i (ordPtr + 1)
        have hsplit : readOrdRecords mem count (ordPtr + 1) =
            pref ++ ((v, xs) :: readOrdRecords mem (count - (i + 1))
              (ordPtr + 1 + ordRecordsWords (readOrdRecords mem (i + 1) (ordPtr + 1)))) := by
          rw [hsp2, hpref_succ, List.append_assoc, List.singleton_append]
        rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen_p,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        simp [xs, readList_length]
      have hinP_lt : inP + 2 + len ≤ dst := by omega
      have hv_mem : st.mem inP = v := hlt inP (by omega)
      have hlen_mem : st.mem (inP + 1) = len := hlt (inP + 1) (by omega)
      have hv_w : v < 2 ^ w := by
        have h := hvals (inP - ordPtr) (by omega)
        simpa [show ordPtr + (inP - ordPtr) = inP by omega] using h
      have hlen_w : len < 2 ^ w := by
        have h := hvals (inP + 1 - ordPtr) (by omega)
        simpa [show ordPtr + (inP + 1 - ordPtr) = inP + 1 by omega] using h
      rw [hlen_getD]
      refine runs_start_le ?_
      have hev7 : (Expr.load (.reg 3)).eval w st = some v :=
        Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq h3) hv_mem
      refine runs_seq_assign_le hev7 ?_
      set st1 : State := { st with regs := Function.update st.regs 7 v }
      have hev8 : (Expr.load (.bin .add (.reg 3) (.const 1))).eval w st1 = some len :=
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := inP) (by simp [st1, h3])) (Expr.eval_const h1w) (by omega))
          hlen_mem
      refine runs_seq_assign_le hev8 ?_
      set st2 : State := { st1 with regs := Function.update st1.regs 8 len }
      refine runs_seq_assign_le
        (Expr.eval_add (Expr.eval_reg_of_eq (v := inP) (by simp [st2, st1, h3])) (Expr.eval_const (by omega)) (by omega)) ?_
      set st3 : State := { st2 with regs := Function.update st2.regs 3 (inP + 2) }
      have hcond_step : ∃ st4 c4,
          Runs w p ω
            (.cond (.reg 8)
              (.store (.reg 4) (.reg 7) ;;
               .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
               .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
               asmCompactCopyLoop ;;
               .assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
               .assign 5 (.bin .add (.reg 5) (.const 1)))
              .nop) st3 .normal st4 c4 ∧
          st4.regs 0 = ordPtr ∧ st4.regs 1 = dst ∧ st4.regs 2 = count ∧ st4.regs 6 = i ∧
          st4.regs 3 = inP + 2 ∧ st4.regs 8 = len ∧
          st4.regs 4 = dst + 1 + ordRecordsWords (compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1))) ∧
          st4.regs 5 = (compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1))).length ∧
          readOrdRecords st4.mem (compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1))).length (dst + 1) =
            compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1)) ∧
          (∀ a < dst, st4.mem a = mem a) ∧
          ZeroFrom st4.mem (dst + 1 + ordRecordsWords (compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1)))) ∧
          c4 ≤ 25 * len + 65 := by
        by_cases hlen0 : len = 0
        · have hxs_nil : xs = [] := by simp [xs, hlen0, readList]
          have hcomp_eq : compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1)) = comp := by
            rw [hpref_succ, compactRecs_append, hxs_nil]; simp [compactRecs, hcomp_def]
          refine ⟨st3, _,
            runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [st3, st2, hlen0]),
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
            by simp [st3, st2, st1, h0], by simp [st3, st2, st1, h1],
            by simp [st3, st2, st1, h2], by simp [st3, st2, st1, h6],
            by simp [st3], by simp [st3, st2],
            by rw [hcomp_eq]; simp [st3, st2, st1, h4, houtP_def],
            by rw [hcomp_eq]; simp [st3, st2, st1, h5],
            by rw [hcomp_eq]; exact hread,
            hlt, by rw [hcomp_eq]; exact hzc, by simp [Expr.size]⟩
        · have hxs_ne : xs ≠ [] := by
            intro h; have := congrArg List.length h; simp [xs, readList_length] at this; omega
          have hcomp_eq : compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1)) = comp ++ [(v, xs)] := by
            rw [hpref_succ, compactRecs_append]; simp [compactRecs, hxs_ne, hcomp_def]
          have hcomp_words : ordRecordsWords (comp ++ [(v, xs)]) = ordRecordsWords comp + 2 + len := by
            rw [ordRecordsWords_append]; simp [ordRecordsWords, xs, readList_length]; omega
          have hcomp_pref_le : ordRecordsWords (comp ++ [(v, xs)]) ≤ ordRecordsWords (compactRecs recs) := by
            rw [← hcomp_eq]
            change ordRecordsWords (compactRecs (readOrdRecords mem (i + 1) (ordPtr + 1))) ≤
              ordRecordsWords (compactRecs (readOrdRecords mem count (ordPtr + 1)))
            rw [hsp2, compactRecs_append, ordRecordsWords_append]; omega
          have hout_end : outP + 2 + len < 2 ^ w := by omega
          have hbranch : ∃ o st4 cB,
              Runs w p ω
                (.store (.reg 4) (.reg 7) ;;
                 .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
                 .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
                 asmCompactCopyLoop ;;
                 .assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
                 .assign 5 (.bin .add (.reg 5) (.const 1))) st3 o st4 cB ∧
              (o = .normal ∧
                st4.regs 0 = ordPtr ∧ st4.regs 1 = dst ∧ st4.regs 2 = count ∧ st4.regs 6 = i ∧
                st4.regs 3 = inP + 2 ∧ st4.regs 8 = len ∧ st4.regs 4 = outP + 2 + len ∧
                st4.regs 5 = comp.length + 1 ∧
                readOrdRecords st4.mem (comp.length + 1) (dst + 1) = comp ++ [(v, xs)] ∧
                (∀ a < dst, st4.mem a = mem a) ∧ ZeroFrom st4.mem (outP + 2 + len)) ∧
              cB ≤ 25 * len + 60 := by
            refine runs_start_le ?_
            refine runs_seq_store_le
              (Expr.eval_reg_of_eq (v := outP) (by simp [st3, st2, st1, h4]))
              (Expr.eval_reg_of_eq (v := v) (by simp [st3, st2, st1])) ?_
            set st3a : State := { st3 with mem := Function.update st3.mem outP v }
            refine runs_seq_store_le
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outP) (by simp [st3a, st3, st2, st1, h4])) (Expr.eval_const h1w) (by omega))
              (Expr.eval_reg_of_eq (v := len) (by simp [st3a, st3, st2])) ?_
            set st3b : State := { st3a with mem := Function.update st3a.mem (outP + 1) len }
            refine runs_seq_assign_le
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outP) (by simp [st3b, st3a, st3, st2, st1, h4])) (Expr.eval_const (by omega)) (by omega)) ?_
            set st3c : State := { st3b with regs := Function.update st3b.regs 4 (outP + 2) }
            have hvals_c : ∀ j < len, st3c.mem (inP + 2 + j) < 2 ^ w := fun j hj => by
              have heq : st3c.mem (inP + 2 + j) = mem (inP + 2 + j) := by
                dsimp only [st3c, st3b, st3a, st3, st2, st1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hlt (inP + 2 + j) (by omega)
              rw [heq]
              have h := hvals (inP + 2 + j - ordPtr) (by omega)
              simpa [show ordPtr + (inP + 2 + j - ordPtr) = inP + 2 + j by omega] using h
            have hz_c : ZeroFrom st3c.mem (outP + 2) := fun a ha => by
              dsimp only [st3c, st3b, st3a, st3, st2, st1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hzc a (by omega)
            obtain ⟨st3d, cCp, hrunCp, hregCp, hltCp, hcpCp, hzCp, hcCp⟩ :=
              asmCompactCopyLoop_runs (p := p) ω st3c h1w (by omega) (by omega)
                (by simp [st3c, st3b, st3a, st3]) (by simp [st3c])
                (by simp [st3c, st3b, st3a, st3, st2]) hvals_c hz_c
            have hrun_rest : ∃ o st4 cR,
                Runs w p ω
                  (.assign 4 (.bin .add (.reg 4) (.reg 8)) ;;
                   .assign 5 (.bin .add (.reg 5) (.const 1))) st3d o st4 cR ∧
                (o = .normal ∧
                  st4.regs 0 = ordPtr ∧ st4.regs 1 = dst ∧ st4.regs 2 = count ∧ st4.regs 6 = i ∧
                  st4.regs 3 = inP + 2 ∧ st4.regs 8 = len ∧ st4.regs 4 = outP + 2 + len ∧
                  st4.regs 5 = comp.length + 1 ∧
                  readOrdRecords st4.mem (comp.length + 1) (dst + 1) = comp ++ [(v, xs)] ∧
                  (∀ a < dst, st4.mem a = mem a) ∧ ZeroFrom st4.mem (outP + 2 + len)) ∧
                cR ≤ 12 := by
              refine runs_start_le ?_
              have hr4d : st3d.regs 4 = outP + 2 := (hregCp 4 (by decide)).trans (by simp [st3c])
              have hr8d : st3d.regs 8 = len := (hregCp 8 (by decide)).trans (by simp [st3c, st3b, st3a, st3, st2])
              have hr5d : st3d.regs 5 = comp.length := (hregCp 5 (by decide)).trans (by simp [st3c, st3b, st3a, st3, st2, st1, h5])
              have hcl_lt : comp.length + 1 < 2 ^ w := by
                have := ordRecordsWords_ge_two_mul comp; omega
              refine runs_seq_assign_le
                (Expr.eval_add (Expr.eval_reg_of_eq hr4d) (Expr.eval_reg_of_eq hr8d) (by omega)) ?_
              set st3e : State := { st3d with regs := Function.update st3d.regs 4 (outP + 2 + len) }
              refine runs_assign_le
                (Expr.eval_add (Expr.eval_reg_of_eq (v := comp.length) (by simp [st3e, hr5d])) (Expr.eval_const h1w) hcl_lt) ?_ ?_
              · refine ⟨rfl,
                  by simp [st3e, hregCp 0 (by decide), st3c, st3b, st3a, st3, st2, st1, h0],
                  by simp [st3e, hregCp 1 (by decide), st3c, st3b, st3a, st3, st2, st1, h1],
                  by simp [st3e, hregCp 2 (by decide), st3c, st3b, st3a, st3, st2, st1, h2],
                  by simp [st3e, hregCp 6 (by decide), st3c, st3b, st3a, st3, st2, st1, h6],
                  by simp [st3e, hregCp 3 (by decide), st3c, st3b, st3a, st3],
                  by simp [st3e, hr8d], by simp [st3e], by simp, ?_, ?_, hzCp⟩
                · change readOrdRecords st3d.mem (comp.length + 1) (dst + 1) = comp ++ [(v, xs)]
                  rw [readOrdRecords_append st3d.mem comp.length 1 (dst + 1)]
                  have hprev_eq : readOrdRecords st3d.mem comp.length (dst + 1) = comp := by
                    trans (readOrdRecords st.mem comp.length (dst + 1))
                    · refine readOrdRecords_congr comp.length (dst + 1) fun x hx1 hx2 => ?_
                      rw [hread] at hx2; rw [hltCp x (by omega)]
                      dsimp only [st3c, st3b, st3a, st3, st2, st1]
                      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                    · exact hread
                  rw [hprev_eq]; congr 1
                  change readOrdRecords st3d.mem 1 outP = [(v, xs)]
                  have hm0 : st3d.mem outP = v := by
                    rw [hltCp outP (by omega)]; dsimp only [st3c, st3b, st3a]
                    rw [Function.update_of_ne (by omega), Function.update_self]
                  have hm1 : st3d.mem (outP + 1) = len := by
                    rw [hltCp (outP + 1) (by omega)]; dsimp only [st3c, st3b]; rw [Function.update_self]
                  have hlist_eq : readList st3d.mem (outP + 2) len = readList mem (inP + 2) len := by
                    apply List.ext_getElem (by simp [readList_length])
                    intro j hj _
                    rw [readList_getElem, readList_getElem]
                    rw [readList_length] at hj; rw [hcpCp j hj]
                    dsimp only [st3c, st3b, st3a, st3, st2, st1]
                    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                    exact hlt (inP + 2 + j) (by omega)
                  simp only [readOrdRecords, hm0, hm1, hlist_eq, xs]
                · intro a ha
                  change st3d.mem a = mem a
                  rw [hltCp a (by omega)]
                  dsimp only [st3c, st3b, st3a, st3, st2, st1]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                  exact hlt a ha
              · simp [Expr.size]
            obtain ⟨o, st4, cR, hrunR, hpostR, hcR⟩ := hrun_rest
            exact ⟨o, st4, cCp + cR + 1, runs_seq_iff.mpr (Or.inr ⟨st3d, cCp, cR, hrunCp, hrunR, rfl⟩),
              hpostR, by simp only [Expr.size]; omega⟩
          obtain ⟨o, st4, cB, hrunB, ⟨rfl, r0, r1, r2, r6, r3, r8, r4, r5, hrd, hlt4, hz4⟩, hcB⟩ := hbranch
          refine ⟨st4, _,
            runs_cond_iff.mpr ⟨len, cB, Expr.eval_reg_of_eq (by simp [st3, st2]),
              by simp only [hlen0, ↓reduceIte]; exact hrunB, rfl⟩,
            r0, r1, r2, r6, r3, r8,
            by rw [hcomp_eq, hcomp_words, houtP_def] at *; omega,
            by rw [hcomp_eq, List.length_append]; simpa using r5,
            by rw [hcomp_eq, List.length_append]; simpa using hrd,
            hlt4, by rw [hcomp_eq, hcomp_words]; simpa [houtP_def, Nat.add_assoc] using hz4,
            by simp [Expr.size]; omega⟩
      obtain ⟨st4, c4, hrun4, r0, r1, r2, r6, r3, r8, r4, r5, hrd, hlt4, hz4, hc4⟩ := hcond_step
      have ha3 : Runs w p ω (.assign 3 (.bin .add (.reg 3) (.reg 8))) st4 .normal
          { st4 with regs := Function.update st4.regs 3 (inP + 2 + len) } _ :=
        runs_assign_iff.mpr ⟨inP + 2 + len,
          Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r8) (by omega), rfl, rfl, rfl⟩
      refine ⟨.normal, { st4 with regs := Function.update st4.regs 3 (inP + 2 + len) }, _,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hrun4, ha3, rfl⟩), ?_, ?_⟩
      · refine ⟨?_, by simp [r6]⟩
        dsimp only [Inv]
        refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp,
          by rw [hwords_succ, hinP_def]; simp; omega,
          by simp [r4], by simp [r5], hrd, hlt4, hz4⟩
      · simp [Expr.size]; omega)
  refine htrip.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      dsimp only [Inv] at h
      exact ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩
  · intro _ _
    have hsum := sum_range_len_le_words mem ordPtr count
    have hreq : readOrdRecords mem count (ordPtr + 1) = recs := rfl
    rw [hreq] at hsum ⊢
    simp only [Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

/-- **Execution of `asmCompactOrdBody`** on `[ordPtr, dst]`: writes a compact copy of the order
(dropping empty vertex records) at `dst` in `compactWords ≤ words` words, leaves memory below `dst`
unchanged and memory from `dst + compactWords` zero, and costs at most `60 * words + 45` (no log
factor!). -/
theorem asmCompactOrdBody_runs {w ordPtr dst words pos : ℕ} {ord : ℕ → List End} {p : Program}
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hw : 4 < 2 ^ w) (hord : OrdListAt mem ordPtr ord words) (hord_le : ordPtr + words ≤ dst)
    (hvals : ∀ j < words, mem (ordPtr + j) < 2 ^ w)
    (hz : ZeroFrom mem dst)
    (hdst : dst + (1 + ordRecordsWords (compactRecs (readOrdRecordsAt mem ordPtr))) < 2 ^ w) :
    let recs := readOrdRecordsAt mem ordPtr
    let cWords := 1 + ordRecordsWords (compactRecs recs)
    ∃ o st' c,
      Runs w p ω asmCompactOrdBody (startState [ordPtr, dst] mem pos) o st' c ∧
      o.value = dst + cWords ∧
      cWords ≤ words ∧
      readOrdRecordsAt st'.mem dst = compactRecs recs ∧
      OrdListAt st'.mem dst ord cWords ∧
      (∀ a < dst, st'.mem a = mem a) ∧
      ZeroFrom st'.mem (dst + cWords) ∧
      c ≤ 80 * words + 75 := by
  intro recs cWords
  have h1w : 1 < 2 ^ w := by omega
  have hwords_eq : words = 1 + ordRecordsWords recs := hord.2.2
  have hcWords_le : cWords ≤ words := by
    have := ordRecordsWords_compactRecs_le recs
    dsimp only [cWords]; omega
  have hcl_w : (compactRecs recs).length < 2 ^ w := by
    have := ordRecordsWords_ge_two_mul (compactRecs recs); omega
  have hmain : ∃ o st' c,
      Runs w p ω asmCompactOrdBody (startState [ordPtr, dst] mem pos) o st' c ∧
      (o.value = dst + cWords ∧
        readOrdRecordsAt st'.mem dst = compactRecs recs ∧
        (∀ a < dst, st'.mem a = mem a) ∧
        ZeroFrom st'.mem (dst + cWords)) ∧
      c ≤ 80 * words + 75 := by
    refine runs_start_le ?_
    unfold asmCompactOrdBody
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := ordPtr) (by simp [startState])) rfl) ?_
    set st1 : State := { startState [ordPtr, dst] mem pos with
      regs := Function.update (startState [ordPtr, dst] mem pos).regs 2 (mem ordPtr) }
    refine runs_seq_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq (v := ordPtr) (by simp [startState])) (Expr.eval_const h1w) (by omega)) ?_
    set st2 : State := { st1 with regs := Function.update st1.regs 3 (ordPtr + 1) }
    refine runs_seq_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) (by simp [startState])) (Expr.eval_const h1w) (by omega)) ?_
    set st3 : State := { st2 with regs := Function.update st2.regs 4 (dst + 1) }
    refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
    set st4 : State := { st3 with regs := Function.update st3.regs 5 0 }
    have hpreL : st4.regs 0 = ordPtr ∧ st4.regs 1 = dst ∧ st4.regs 2 = mem ordPtr ∧
        st4.regs 3 = ordPtr + 1 ∧ st4.regs 4 = dst + 1 ∧ st4.regs 5 = 0 ∧ st4.mem = mem :=
      ⟨by simp [st4, st3, st2, st1, startState], by simp [st4, st3, st2, st1, startState],
       by simp [st4, st3, st2, st1], by simp [st4, st3, st2], by simp [st4, st3], by simp [st4], rfl⟩
    refine runs_seq_triple_le (asmCompactOuterLoop_triple p mem hw hord hord_le hvals hz hdst) hpreL ?_
    intro st5 ⟨hr1, hr4, hr5, hread, hlt, hz5⟩
    refine runs_seq_store_le (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr5) ?_
    set st6 : State := { st5 with mem := Function.update st5.mem dst (compactRecs recs).length }
    refine runs_ret_le (Expr.eval_reg_of_eq (v := dst + 1 + ordRecordsWords (compactRecs recs)) (by exact hr4)) ?_ ?_
    · have hval : (Outcome.returned (dst + 1 + ordRecordsWords (compactRecs recs))).value = dst + cWords := by
        dsimp only [Outcome.value, cWords]; omega
      have hrecs6 : readOrdRecordsAt st6.mem dst = compactRecs recs := by
        unfold readOrdRecordsAt
        have hdst_eq : st6.mem dst = (compactRecs recs).length := by simp [st6]
        rw [hdst_eq]
        trans (readOrdRecords st5.mem (compactRecs recs).length (dst + 1))
        · refine readOrdRecords_congr (compactRecs recs).length (dst + 1) fun x hx1 _ => ?_
          dsimp only [st6]; exact Function.update_of_ne (by omega) _ _
        · exact hread
      refine ⟨hval, hrecs6, fun a ha => by
        dsimp only [st6]; rw [Function.update_of_ne (by omega)]; exact hlt a ha,
        fun a ha => by
          dsimp only [st6]; rw [Function.update_of_ne (by dsimp only [cWords] at ha; omega)]
          exact hz5 a (by dsimp only [cWords, recs] at ha; omega)⟩
    · simp only [Expr.size]; omega
  obtain ⟨o, st', c, hrun, ⟨hval, hrecs6, hlt, hz'⟩, hc⟩ := hmain
  have hord' : OrdListAt st'.mem dst ord cWords := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hrecs6]; exact compactRecs_nodup hord.1
    · unfold readOrd; rw [hrecs6, ordOfRecords_compactRecs hord.1]; exact hord.2.1
    · rw [hrecs6]
  exact ⟨o, st', c, hrun, hval, hcWords_le, hrecs6, hord', hlt, hz', hc⟩

end MinCostFlow.SparseCore.Program
