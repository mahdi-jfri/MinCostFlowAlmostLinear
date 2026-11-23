module

public import MinCostFlow.SparseCore.Program.BundleInitProcs

import WordRAM.Tactic

/-!
# Potential-threaded loop rule and chunking invariant for bundle initialization (`BundleInitScan`)

Provides:
1. `runs_forRange_pot`, `runs_cond_true_le`, `runs_cond_false_le`: reusable Word-RAM control-flow
   and potential-threading loop combinators.
2. `BundleSlotRepAt.of_agree_slot`: per-slot locality of `BundleSlotRepAt` when shared `endPrev` /
   `endNext` arrays change only on edges outside `B.edges`.
3. `initPrefixSlots`, `initMidSlots`, `bundleStateOfSlots`, and `InitScanSlotInv` (with
   `.of_agree`, `.step_skip`, `.step_push`, and `last_initialChunk_length_eq_k_iff`): the
   mathematical and memory invariant for Loop 3 of `bundleInitSlotsStmt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Potential-threading `forRange` rule, `cond` helpers, and per-slot locality -/

/-- Terminal conditional rule (true branch) accumulating prefix cost `k`. -/
theorem runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h1
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, hq, by omega⟩

/-- Terminal conditional rule (false branch) accumulating prefix cost `k`. -/
theorem runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h2 : ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h2
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, hq, by omega⟩

/-- Counter-loop rule for `forRange r lo hi body` that threads a ghost state `a : α` and an
amortized potential `phi : α → State → ℕ` across iterations. -/
theorem runs_forRange_pot {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {lo hi : Expr}
    {body : Stmt} {α : Type*} (phi : α → State → ℕ)
    (Inv : ℕ → α → State → Prop) (stepCost : ℕ → ℕ) (hiVal : ℕ)
    (hw : 1 < 2 ^ w) (hhi_word : 0 < hiVal → hiVal < 2 ^ w)
    {st₀ : State} {a₀ : α}
    (hinit : lo.eval w st₀ = some 0 ∧
      Inv 0 a₀ { st₀ with regs := Function.update st₀.regs r 0 } ∧
      phi a₀ { st₀ with regs := Function.update st₀.regs r 0 } = phi a₀ st₀)
    (hreg : ∀ i a st, i ≤ hiVal → Inv i a st → st.regs r = i)
    (hhi : ∀ i a st, i ≤ hiVal → Inv i a st → hi.eval w st = some hiVal)
    (hbody : ∀ i a st, i < hiVal → Inv i a st →
      ∃ st₁ c₁ a₁, Runs w p ω body st .normal st₁ c₁ ∧
        st₁.regs r = i ∧
        Inv (i + 1) a₁ { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
        phi a₁ { st₁ with regs := Function.update st₁.regs r (i + 1) } = phi a₁ st₁ ∧
        c₁ + phi a₁ st₁ ≤ stepCost i + phi a st) :
    ∃ st' c a', Runs w p ω (forRange r lo hi body) st₀ .normal st' c ∧
      Inv hiVal a' st' ∧
      c + phi a' st' ≤
        rangeCost stepCost 0 hiVal + hiVal * (hi.size + 8) + hi.size + lo.size + 5 + phi a₀ st₀ := by
  have hup : ∀ k i a st, hiVal - i = k → i ≤ hiVal → Inv i a st →
      ∃ st' c a', Runs w p ω (forUp r hi body) st .normal st' c ∧
        Inv hiVal a' st' ∧
        c + phi a' st' ≤
          rangeCost stepCost i hiVal + (hiVal - i) * (hi.size + 8) + (hi.size + 3) + phi a st := by
    intro k
    induction k with
    | zero =>
      intro i a st hk hle hInv
      have heq : i = hiVal := by omega
      subst heq
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 :=
        Expr.eval_lt_false (by simp [Expr.eval, hreg i a st le_rfl hInv])
          (hhi i a st le_rfl hInv) le_rfl hw
      have hcost : (.bin .lt (.reg r) hi : Expr).size + 1 = hi.size + 3 := by simp; omega
      refine ⟨st, hi.size + 3, a,
        runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, hcost.symm⟩), hInv, ?_⟩
      simp
    | succ k ih =>
      intro i a st hk hle hInv
      have hlt : i < hiVal := by omega
      have hi1w : i + 1 < 2 ^ w := Nat.lt_of_le_of_lt hlt (hhi_word (by omega))
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 :=
        Expr.eval_lt_true (by simp [Expr.eval, hreg i a st hle hInv])
          (hhi i a st hle hInv) hlt hw
      have hcondSize : (Expr.bin .lt (.reg r) hi : Expr).size = hi.size + 2 := by simp; omega
      obtain ⟨st₁, c₁, a₁, hr₁, hr1r, hInv₁, hphi₁, hc₁⟩ := hbody i a st hlt hInv
      set st₂ : State := { st₁ with regs := Function.update st₁.regs r (i + 1) }
      have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal st₂ 4 := by
        refine runs_assign_iff.mpr ⟨i + 1, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, BinOp.eval, hr1r, hw, hi1w]
      have hstep : Runs w p ω (body ;; .assign r (.bin .add (.reg r) (.const 1)))
          st .normal st₂ (c₁ + 4 + 1) :=
        bundle_runs_seq_normal hr₁ hinc
      obtain ⟨st', c₂, a', hr₂, hInv', hc₂⟩ := ih (i + 1) a₁ st₂ (by omega) (by omega) hInv₁
      refine ⟨st', (Expr.bin .lt (.reg r) hi).size + (c₁ + 4 + 1) + c₂ + 1, a',
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st₂, c₁ + 4 + 1, c₂, hcond, by decide, hstep, hr₂, rfl⟩)),
        hInv', ?_⟩
      rw [hcondSize, rangeCost_step hlt]
      rw [hphi₁] at hc₂
      have hmul : (hiVal - i) * (hi.size + 8) = (hiVal - (i + 1)) * (hi.size + 8) + (hi.size + 8) := by
        have : hiVal - i = (hiVal - (i + 1)) + 1 := by omega
        rw [this, Nat.add_one_mul]
      omega
  rcases hinit with ⟨hlo, hInv0, hphi0⟩
  set st₁ : State := { st₀ with regs := Function.update st₀.regs r 0 }
  have hassign : Runs w p ω (.assign r lo) st₀ .normal st₁ (lo.size + 1) :=
    runs_assign_iff.mpr ⟨0, hlo, rfl, rfl, rfl⟩
  obtain ⟨st', c₂, a', hr₂, hInv', hc₂⟩ :=
    hup hiVal 0 a₀ st₁ (Nat.sub_zero hiVal) (Nat.zero_le _) hInv0
  refine ⟨st', (lo.size + 1) + c₂ + 1, a', bundle_runs_seq_normal hassign hr₂, hInv', ?_⟩
  rw [hphi0, Nat.sub_zero] at hc₂
  omega

/-- Per-slot locality of `BundleSlotRepAt`: modifying `prevBase`/`nextBase` only at ends whose edge
is outside `B.edges` preserves `BundleSlotRepAt`. -/
lemma BundleSlotRepAt.of_agree_slot {eCap prevBase nextBase p bunCap : ℕ} {B : BundleState}
    {mem mem' : ℕ → ℕ}
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem)
    (hblock : ∀ a, p ≤ a → a < p + bundleSlotBlockSize bunCap → mem a = mem' a)
    (hprev : ∀ k, (endOfKey k).1 ∈ B.edges → mem (prevBase + k) = mem' (prevBase + k))
    (hnext : ∀ k, (endOfKey k).1 ∈ B.edges → mem (nextBase + k) = mem' (nextBase + k)) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap B mem' := by
  rcases hrep with ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, hscr⟩
  have hb : ∀ off < bundleSlotBlockSize bunCap, mem' (p + off) = mem (p + off) :=
    fun off hoff => (hblock (p + off) (Nat.le_add_right _ _) (by omega)).symm
  refine ⟨nB, hV, hnB, hE, hbo, hpar0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)]; exact h0
  · rw [hb bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)]; exact h1
  · rw [hb bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)]; exact h2
  · intro b hb_lt
    obtain ⟨L, hL, hlen, hmem⟩ := hdll b hb_lt
    have hlt_cap : b < bunCap := lt_of_lt_of_le hb_lt hnB
    refine ⟨L, hL.of_agree ?_ ?_ ?_, ?_, hmem⟩
    · have := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsHeadBase, Nat.add_assoc] using this
    · intro k hk
      have hxe : (endOfKey k).1 ∈ B.edges :=
        (mem_edgeEnds B.edges (endOfKey k)).mp (Finset.mem_filter.mp ((hmem k).mp hk)).1
      exact (hprev k hxe).symm
    · intro k hk
      have hxe : (endOfKey k).1 ∈ B.edges :=
        (mem_edgeEnds B.edges (endOfKey k)).mp (Finset.mem_filter.mp ((hmem k).mp hk)).1
      exact (hnext k hxe).symm
    · have := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsSizeBase, Nat.add_assoc] using
        this.trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen)
  · intro b hb_lt hem
    have hlt_cap : b < bunCap := lt_of_lt_of_le hb_lt hnB
    have := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa only [bsParentBase, Nat.add_assoc] using this.trans
      (by simpa [bsParentBase, Nat.add_assoc] using hpar b hb_lt hem)
  · intro b hge hlt
    have hA := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨t1, t2, t3⟩ := htail b hge hlt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsHeadBase, Nat.add_assoc] using
        hA.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1)
    · simpa only [bsSizeBase, Nat.add_assoc] using
        hB.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2)
    · simpa only [bsParentBase, Nat.add_assoc] using
        hC.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)
  · intro b hb_lt
    have hA := hb (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨s1, s2, s3⟩ := hscr b hb_lt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsSeenBase, Nat.add_assoc] using
        hA.trans (by simpa [bsSeenBase, Nat.add_assoc] using s1)
    · simpa only [bsInCandBase, Nat.add_assoc] using
        hB.trans (by simpa [bsInCandBase, Nat.add_assoc] using s2)
    · simpa only [bsCandNextBase, Nat.add_assoc] using
        hC.trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3)

/-! ## 2. Prefix-chunking model for Loop 3 -/

/-- Chunks accumulated over a prefix `rPref` of core vertices for edge set `E`. -/
def initPrefixSlots (cord : ℕ → List End) (rPref : List ℕ) (E : Finset ℕ) (k : ℕ) :
    List (ℕ × List End) :=
  rPref.flatMap fun v => (initialChunks k ((cord v).filter fun x => decide (x.1 ∈ E))).map (v, ·)

/-- Chunks accumulated through prefix `rPref` plus the first `t` ends of `cord v`. -/
def initMidSlots (cord : ℕ → List End) (rPref : List ℕ) (v t : ℕ) (E : Finset ℕ) (k : ℕ) :
    List (ℕ × List End) :=
  initPrefixSlots cord rPref E k ++
    (initialChunks k (((cord v).take t).filter fun x => decide (x.1 ∈ E))).map (v, ·)

/-- `BundleState` constructed directly from a slot list `slots` and edge set `E`. -/
def bundleStateOfSlots (slots : List (ℕ × List End)) (E : Finset ℕ) : BundleState where
  vertices := Finset.range slots.length
  edges := E
  parent := fun b => (slots[b]?.getD (0, [])).1
  bundleOf := fun x => slots.findIdx (fun p => p.2.contains x)

lemma initPrefixSlots_eq_initialSlots {C : MGraph} (ρ : Rotation C) (E : Finset ℕ) (k : ℕ) :
    initPrefixSlots ρ.order (C.V.sort (· ≤ ·)) E k = initialSlots ρ E k := rfl

lemma initMidSlots_zero (cord : ℕ → List End) (rPref : List ℕ) (v : ℕ) (E : Finset ℕ) (k : ℕ) :
    initMidSlots cord rPref v 0 E k = initPrefixSlots cord rPref E k := by
  simp [initMidSlots, initialChunks]

lemma initMidSlots_full (cord : ℕ → List End) (rList : List ℕ) {i : ℕ} (hi : i < rList.length)
    (E : Finset ℕ) (k : ℕ) :
    initMidSlots cord (rList.take i) rList[i] (cord rList[i]).length E k =
      initPrefixSlots cord (rList.take (i + 1)) E k := by
  simp only [initMidSlots, List.take_length, initPrefixSlots, List.take_succ_eq_append_getElem hi,
    List.flatMap_append, List.flatMap_singleton]

lemma initPrefixSlots_take_le (cord : ℕ → List End) (rList : List ℕ) (i : ℕ) (E : Finset ℕ) (k : ℕ) :
    (initPrefixSlots cord (rList.take i) E k).length ≤ (initPrefixSlots cord rList E k).length := by
  rw [initPrefixSlots, initPrefixSlots]
  conv_rhs => rw [← List.take_append_drop i rList]
  rw [List.flatMap_append, List.length_append]
  omega

lemma initMidSlots_le_full (cord : ℕ → List End) (rList : List ℕ) {i : ℕ} (hi : i < rList.length)
    (t : ℕ) (E : Finset ℕ) (k : ℕ) :
    (initMidSlots cord (rList.take i) rList[i] t E k).length ≤
      (initPrefixSlots cord rList E k).length := by
  have h1 : (initMidSlots cord (rList.take i) rList[i] t E k).length ≤
      (initMidSlots cord (rList.take i) rList[i] (cord rList[i]).length E k).length := by
    simp only [initMidSlots, List.take_length, List.length_append, List.length_map,
      initialChunks_length_eq]
    have hfl : (((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E)).length ≤
        ((cord rList[i]).filter fun x => decide (x.1 ∈ E)).length := by
      conv_rhs => rw [← List.take_append_drop t (cord rList[i])]
      rw [List.filter_append, List.length_append]; omega
    have hdiv := Nat.div_le_div_right (c := k) (show (((cord rList[i]).take t).filter fun x =>
      decide (x.1 ∈ E)).length + k - 1 ≤ ((cord rList[i]).filter fun x =>
      decide (x.1 ∈ E)).length + k - 1 by omega)
    omega
  rw [initMidSlots_full cord rList hi E k] at h1
  exact le_trans h1 (initPrefixSlots_take_le cord rList (i + 1) E k)

lemma mem_initMidSlots_end {cord : ℕ → List End} {rPref : List ℕ} {v t : ℕ} {E : Finset ℕ}
    {k : ℕ} (hk : 1 ≤ k) {b : ℕ}
    (hb : b < (initMidSlots cord rPref v t E k).length) {x : End}
    (hx : x ∈ (initMidSlots cord rPref v t E k)[b].2) :
    x.1 ∈ E ∧ ((∃ w ∈ rPref, x ∈ cord w) ∨ x ∈ (cord v).take t) := by
  have hmem : (initMidSlots cord rPref v t E k)[b] ∈ initMidSlots cord rPref v t E k :=
    List.getElem_mem hb
  simp only [initMidSlots, initPrefixSlots, List.mem_append, List.mem_flatMap, List.mem_map] at hmem
  rcases hmem with ⟨w, hw, ch, hch, heq⟩ | ⟨ch, hch, heq⟩
  · have hxch : x ∈ ch := by simpa only [initMidSlots, initPrefixSlots, ← heq] using hx
    have hfl := (initialChunks_spec hk ((cord w).filter fun y => decide (y.1 ∈ E))).1
    have hxf : x ∈ (cord w).filter fun y => decide (y.1 ∈ E) := by
      rw [← hfl]; exact List.mem_flatten.mpr ⟨ch, hch, hxch⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hxf
    exact ⟨hxf.2, Or.inl ⟨w, hw, hxf.1⟩⟩
  · have hxch : x ∈ ch := by simpa only [initMidSlots, initPrefixSlots, ← heq] using hx
    have hfl := (initialChunks_spec hk (((cord v).take t).filter fun y => decide (y.1 ∈ E))).1
    have hxf : x ∈ ((cord v).take t).filter fun y => decide (y.1 ∈ E) := by
      rw [← hfl]; exact List.mem_flatten.mpr ⟨ch, hch, hxch⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hxf
    exact ⟨hxf.2, Or.inr hxf.1⟩

lemma last_initialChunk_length_eq_k_iff {α : Type*} {k : ℕ} (hk : 1 ≤ k) {xs : List α}
    (hne : xs ≠ []) :
    have hpos : 0 < (initialChunks k xs).length := by
      rw [initialChunks_length_eq]
      exact Nat.div_pos (by have := List.length_pos_of_ne_nil hne; omega) hk
    ((initialChunks k xs)[(initialChunks k xs).length - 1]'(by omega)).length = k ↔ xs.length % k = 0 := by
  intro hpos
  have hget := initialChunks_getElem_length (k := k) xs (j := (initialChunks k xs).length - 1) (by omega)
  rw [hget]
  have hdm : (xs.length / k) * k + xs.length % k = xs.length := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod xs.length k
  have hrk : xs.length % k < k := Nat.mod_lt _ hk
  have hx : 0 < xs.length := List.length_pos_of_ne_nil hne
  by_cases hmod : xs.length % k = 0
  · have hq : (initialChunks k xs).length = xs.length / k := by
      rw [initialChunks_length_eq,
        show xs.length + k - 1 = (k - 1) + k * (xs.length / k) by rw [Nat.mul_comm]; omega,
        Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
    have hq_pos : 1 ≤ xs.length / k := by omega
    have hsub : ((initialChunks k xs).length - 1) * k + k = xs.length := by
      rw [hq, show (xs.length / k - 1) * k + k = (xs.length / k - 1 + 1) * k by
        rw [Nat.add_mul, Nat.one_mul], Nat.sub_add_cancel hq_pos]; omega
    simp [hmod, show xs.length - ((initialChunks k xs).length - 1) * k = k by omega]
  · have hq : (initialChunks k xs).length = xs.length / k + 1 := by
      rw [initialChunks_length_eq,
        show xs.length + k - 1 = (xs.length % k - 1) + k * (xs.length / k + 1) by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega,
        Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
    have hrem : xs.length - ((initialChunks k xs).length - 1) * k = xs.length % k := by
      rw [hq, Nat.add_sub_cancel]; omega
    rw [hrem, Nat.min_eq_right (by omega)]
    exact ⟨fun h => by omega, fun h => absurd h hmod⟩

/-! ## 3. Loop 3 per-slot invariant and step lemmas -/

/-- Per-initialized-slot memory invariant maintained throughout Loop 3 of `bundleInitSlotsStmt`. -/
def InitScanSlotInv (eCap prevBase nextBase endBunBase curBunBase curTagBase : ℕ)
    (cord : ℕ → List End) (rList : List ℕ) (i t s p cap k : ℕ) (E : Finset ℕ)
    (mem : ℕ → ℕ) : Prop :=
  let v := rList.getD i 0
  let curEnds := ((cord v).take t).filter fun x => decide (x.1 ∈ E)
  let chunks := initMidSlots cord (rList.take i) v t E k
  chunks.length ≤ cap ∧
  mem (p + bsOffBunCap) = cap ∧
  mem (p + bsOffNB) = chunks.length ∧
  mem (p + bsOffNE) = E.card ∧
  (∀ b (hb : b < chunks.length), ∃ L : List ℕ,
    IsDoublyLinkedList mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L ∧
    mem (bsSizeBase p cap + b) = L.length ∧
    L.length = chunks[b].2.length ∧
    (∀ key, key ∈ L ↔ endOfKey key ∈ chunks[b].2)) ∧
  (∀ b, chunks.length ≤ b → b < cap →
    mem (bsHeadBase p + b) = 0 ∧ mem (bsSizeBase p cap + b) = 0 ∧
    mem (bsParentBase p cap + b) = 0) ∧
  (∀ b < cap,
    mem (bsSeenBase p cap + b) = 0 ∧
    mem (bsInCandBase p cap + b) = 0 ∧
    mem (bsCandNextBase p cap + b) = 0) ∧
  (∀ b (hb : b < chunks.length), ∀ x ∈ chunks[b].2, mem (endBunBase + endKey x) = b) ∧
  (curEnds = [] → mem (curTagBase + s) ≤ i) ∧
  (curEnds ≠ [] → mem (curTagBase + s) = i + 1 ∧ mem (curBunBase + s) + 1 = chunks.length)

lemma InitScanSlotInv.of_agree {eCap prevBase nextBase endBunBase curBunBase curTagBase : ℕ}
    {cord : ℕ → List End} {rList : List ℕ} {i t s p cap k : ℕ} {E : Finset ℕ}
    {mem mem' : ℕ → ℕ}
    (hI : InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i t s p cap k E mem)
    (hk : 1 ≤ k)
    (hblock : ∀ a, p ≤ a → a < p + bundleSlotBlockSize cap → mem a = mem' a)
    (hprev : ∀ key, (endOfKey key).1 ∈ E → mem (prevBase + key) = mem' (prevBase + key))
    (hnext : ∀ key, (endOfKey key).1 ∈ E → mem (nextBase + key) = mem' (nextBase + key))
    (hend : ∀ x : End, x.1 ∈ E → mem (endBunBase + endKey x) = mem' (endBunBase + endKey x))
    (hcurB : mem (curBunBase + s) = mem' (curBunBase + s))
    (hcurT : mem (curTagBase + s) = mem' (curTagBase + s)) :
    InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i t s p cap k E mem' := by
  rcases hI with ⟨hlen_cap, h0, h1, h2, hdll, htail, hscr, hbun, htag0, htag1⟩
  have hb : ∀ off < bundleSlotBlockSize cap, mem' (p + off) = mem (p + off) :=
    fun off hoff => (hblock (p + off) (Nat.le_add_right _ _) (by omega)).symm
  refine ⟨hlen_cap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)]; exact h0
  · rw [hb bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)]; exact h1
  · rw [hb bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)]; exact h2
  · intro b hb_lt
    obtain ⟨L, hL, hlen, hlen2, hmem⟩ := hdll b hb_lt
    have hlt_cap : b < cap := lt_of_lt_of_le hb_lt hlen_cap
    refine ⟨L, hL.of_agree ?_ ?_ ?_, ?_, hlen2, hmem⟩
    · have := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsHeadBase, Nat.add_assoc] using this
    · intro key hkey
      exact (hprev key (mem_initMidSlots_end hk hb_lt ((hmem key).mp hkey)).1).symm
    · intro key hkey
      exact (hnext key (mem_initMidSlots_end hk hb_lt ((hmem key).mp hkey)).1).symm
    · have := hb (3 + cap + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsSizeBase, Nat.add_assoc] using
        this.trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen)
  · intro b hge hlt
    have hA := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + cap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 2 * cap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨t1, t2, t3⟩ := htail b hge hlt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsHeadBase, Nat.add_assoc] using
        hA.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1)
    · simpa only [bsSizeBase, Nat.add_assoc] using
        hB.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2)
    · simpa only [bsParentBase, Nat.add_assoc] using
        hC.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)
  · intro b hb_lt
    have hA := hb (3 + 3 * cap + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + 4 * cap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 5 * cap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨s1, s2, s3⟩ := hscr b hb_lt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsSeenBase, Nat.add_assoc] using
        hA.trans (by simpa [bsSeenBase, Nat.add_assoc] using s1)
    · simpa only [bsInCandBase, Nat.add_assoc] using
        hB.trans (by simpa [bsInCandBase, Nat.add_assoc] using s2)
    · simpa only [bsCandNextBase, Nat.add_assoc] using
        hC.trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3)
  · intro b hb_lt x hx
    exact (hend x (mem_initMidSlots_end hk hb_lt hx).1).symm.trans (hbun b hb_lt x hx)
  · intro he; rw [← hcurT]; exact htag0 he
  · intro hne; rw [← hcurT, ← hcurB]; exact htag1 hne

lemma InitScanSlotInv.step_skip {eCap prevBase nextBase endBunBase curBunBase curTagBase : ℕ}
    {cord : ℕ → List End} {rList : List ℕ} {i t s p cap k : ℕ} {E : Finset ℕ} {mem : ℕ → ℕ}
    (ht : t < (cord (rList.getD i 0)).length)
    (hnot : ((cord (rList.getD i 0))[t]).1 ∉ E)
    (hI : InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i t s p cap k E mem) :
    InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i (t + 1) s p cap k E mem := by
  have hfl : (((cord (rList.getD i 0)).take (t + 1)).filter fun x => decide (x.1 ∈ E)) =
      (((cord (rList.getD i 0)).take t).filter fun x => decide (x.1 ∈ E)) := by
    rw [List.take_succ_eq_append_getElem ht, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, hnot, ↓reduceIte, List.append_nil]
  simpa only [InitScanSlotInv, initMidSlots, hfl] using hI

/-- Abstract state-update lemma for advancing `InitScanSlotInv` on the single slot `s` that owns
`x = (cord v)[t]`. -/
lemma InitScanSlotInv.step_push {eCap prevBase nextBase endBunBase curBunBase curTagBase : ℕ}
    {cord : ℕ → List End} {rList : List ℕ} {i t s p cap k bun : ℕ} {E : Finset ℕ}
    {mem mem' : ℕ → ℕ} {Lnew : List ℕ}
    (hk : 1 ≤ k)
    (hi : i < rList.length)
    (ht : t < (cord rList[i]).length)
    (hx_in : ((cord rList[i])[t]).1 ∈ E)
    (hI : InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i t s p cap k E mem)
    (hcap_next : (initMidSlots cord (rList.take i) rList[i] (t + 1) E k).length ≤ cap)
    (hfresh : ∀ b (hb : b < (initMidSlots cord (rList.take i) rList[i] t E k).length),
      (cord rList[i])[t] ∉ (initMidSlots cord (rList.take i) rList[i] t E k)[b].2)
    (hbun_eq : bun =
      if (((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E)).length % k = 0 then
        (initMidSlots cord (rList.take i) rList[i] t E k).length
      else (initMidSlots cord (rList.take i) rList[i] t E k).length - 1)
    (hdll_new : IsDoublyLinkedList mem' prevBase nextBase (bsHeadBase p + bun) (2 * eCap) Lnew)
    (hLnew_len : Lnew.length =
      if hmod : (((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E)).length % k = 0 then 1
      else ((initMidSlots cord (rList.take i) rList[i] t E k)[bun]'(by
        have hne : (((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E)) ≠ [] :=
          fun h0 => hmod (by simp [h0])
        have hpos : 0 < (initMidSlots cord (rList.take i) rList[i] t E k).length := by
          simp only [initMidSlots, List.length_append, List.length_map, initialChunks_length_eq]
          have : 1 ≤ ((((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E)).length + k - 1) / k :=
            Nat.div_pos (by have := List.length_pos_of_ne_nil hne; omega) hk
          omega
        rw [hbun_eq]; simp only [hmod, ↓reduceIte]; omega)).2.length + 1)
    (hLnew_mem : ∀ key, key ∈ Lnew ↔
      endOfKey key = (cord rList[i])[t] ∨
        (∃ hlt : bun < (initMidSlots cord (rList.take i) rList[i] t E k).length,
          endOfKey key ∈ (initMidSlots cord (rList.take i) rList[i] t E k)[bun].2))
    (hnb' : mem' (p + bsOffNB) = (initMidSlots cord (rList.take i) rList[i] (t + 1) E k).length)
    (hsize' : mem' (bsSizeBase p cap + bun) = Lnew.length)
    (hend' : mem' (endBunBase + endKey (cord rList[i])[t]) = bun)
    (htag' : mem' (curTagBase + s) = i + 1)
    (hcurB' : mem' (curBunBase + s) = bun)
    (hother_block : ∀ off < bundleSlotBlockSize cap,
      p + off ≠ p + bsOffNB → p + off ≠ bsHeadBase p + bun → p + off ≠ bsSizeBase p cap + bun →
      mem' (p + off) = mem (p + off))
    (hother_dll : ∀ b (hb : b < (initMidSlots cord (rList.take i) rList[i] t E k).length),
      b ≠ bun → ∀ key, endOfKey key ∈ (initMidSlots cord (rList.take i) rList[i] t E k)[b].2 →
      mem' (prevBase + key) = mem (prevBase + key) ∧
      mem' (nextBase + key) = mem (nextBase + key))
    (hother_end : ∀ y : End, y.1 ∈ E → y ≠ (cord rList[i])[t] →
      mem' (endBunBase + endKey y) = mem (endBunBase + endKey y)) :
    InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i (t + 1) s p cap k E mem' := by
  have hv : rList.getD i 0 = rList[i] := List.getD_eq_getElem _ _ hi
  let v := rList[i]
  let x := (cord v)[t]
  let pref := initPrefixSlots cord (rList.take i) E k
  let curEnds := ((cord v).take t).filter fun y => decide (y.1 ∈ E)
  let oldChunks := initMidSlots cord (rList.take i) v t E k
  let newChunks := initMidSlots cord (rList.take i) v (t + 1) E k
  have hcurEnds_next : ((cord v).take (t + 1)).filter (fun y => decide (y.1 ∈ E)) = curEnds ++ [x] := by
    rw [List.take_succ_eq_append_getElem ht, List.filter_append]
    simp [curEnds, x, hx_in]; exact ⟨rfl, rfl⟩
  have hold_len : oldChunks.length = pref.length + (initialChunks k curEnds).length := by
    simp [oldChunks, pref, curEnds, initMidSlots]
  have hnew_len : newChunks.length =
      if curEnds.length % k = 0 then oldChunks.length + 1 else oldChunks.length := by
    have h1 : newChunks.length = pref.length + (initialChunks k (curEnds ++ [x])).length := by
      simp only [newChunks, pref, initMidSlots, hcurEnds_next, List.length_append, List.length_map]
    rw [h1, initialChunks_snoc_length hk, hold_len]
    split_ifs <;> omega
  have hcur_len_eq : curEnds.length % k = 0 →
      (initialChunks k curEnds).length = curEnds.length / k := by
    intro hmod
    rw [initialChunks_length_eq]
    have hdm : k * (curEnds.length / k) + curEnds.length % k = curEnds.length :=
      Nat.div_add_mod curEnds.length k
    rw [show curEnds.length + k - 1 = (k - 1) + k * (curEnds.length / k) by omega,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
  have hcur_len_ne : curEnds.length % k ≠ 0 →
      (initialChunks k curEnds).length = curEnds.length / k + 1 := by
    intro hmod
    have hrk : curEnds.length % k < k := Nat.mod_lt _ hk
    have hdm : k * (curEnds.length / k) + curEnds.length % k = curEnds.length :=
      Nat.div_add_mod curEnds.length k
    rw [initialChunks_length_eq,
      show curEnds.length + k - 1 = (curEnds.length % k - 1) + k * (curEnds.length / k + 1) by
        rw [Nat.mul_add, Nat.mul_one]; omega,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
  have hbun_cases : (curEnds.length % k = 0 → bun = oldChunks.length ∧ newChunks.length = oldChunks.length + 1) ∧
      (curEnds.length % k ≠ 0 → bun + 1 = oldChunks.length ∧ newChunks.length = oldChunks.length) := by
    constructor
    · intro hmod
      have h1 : bun = oldChunks.length := by
        change bun = if curEnds.length % k = 0 then oldChunks.length else oldChunks.length - 1 at hbun_eq
        simpa [hmod] using hbun_eq
      have h2 : newChunks.length = oldChunks.length + 1 := by simpa [hmod] using hnew_len
      exact ⟨h1, h2⟩
    · intro hmod
      have hne : curEnds ≠ [] := fun h0 => hmod (by simp [h0])
      have hpos : 0 < oldChunks.length := by
        rw [hold_len, initialChunks_length_eq]
        have : 1 ≤ (curEnds.length + k - 1) / k :=
          Nat.div_pos (by have := List.length_pos_of_ne_nil hne; omega) hk
        omega
      have h1 : bun = oldChunks.length - 1 := by
        change bun = if curEnds.length % k = 0 then oldChunks.length else oldChunks.length - 1 at hbun_eq
        simpa [hmod] using hbun_eq
      have h2 : newChunks.length = oldChunks.length := by simpa [hmod] using hnew_len
      exact ⟨by omega, h2⟩
  have hbun_eq_idx : bun = pref.length + curEnds.length / k := by
    by_cases hmod : curEnds.length % k = 0
    · obtain ⟨h1, _⟩ := hbun_cases.1 hmod
      have h2 := hcur_len_eq hmod
      omega
    · obtain ⟨h1, _⟩ := hbun_cases.2 hmod
      have h2 := hcur_len_ne hmod
      omega
  have hnew_get : ∀ b (hb : b < newChunks.length),
      newChunks[b].2 =
        if hbb : b = bun then
          (if hmod : curEnds.length % k = 0 then [x]
           else (oldChunks[b]'(by rw [hnew_len] at hb; simp [hmod] at hb; exact hb)).2 ++ [x])
        else
          (oldChunks[b]'(by
            by_cases hmod : curEnds.length % k = 0
            · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
            · obtain ⟨_, h2⟩ := hbun_cases.2 hmod; omega)).2 := by
    intro b hb
    have hnew_eq : newChunks = pref ++ (initialChunks k (curEnds ++ [x])).map (v, ·) := by
      simp only [newChunks, pref, initMidSlots, hcurEnds_next]
    by_cases hlt_p : b < pref.length
    · have hne_b : b ≠ bun := fun heq =>
        Nat.not_lt.mpr (Nat.le_add_right pref.length (curEnds.length / k)) (hbun_eq_idx ▸ heq ▸ hlt_p)
      have h1 : newChunks[b] = pref[b] := by
        simp only [newChunks, pref, initMidSlots, hcurEnds_next]
        exact List.getElem_append_left hlt_p
      have h2 : oldChunks[b]'(by rw [hold_len]; omega) = pref[b] := by
        simp only [oldChunks, pref, initMidSlots]
        exact List.getElem_append_left hlt_p
      rw [dite_eq_right hne_b, h1, h2]
    · have hge_p : pref.length ≤ b := by omega
      have hj_lt : b - pref.length < (initialChunks k (curEnds ++ [x])).length := by
        have : newChunks.length = pref.length + (initialChunks k (curEnds ++ [x])).length := by
          rw [hnew_eq, List.length_append, List.length_map]
        omega
      have h1 : newChunks[b].2 = (initialChunks k (curEnds ++ [x]))[b - pref.length]'hj_lt := by
        have he1 : newChunks[b] = ((initialChunks k (curEnds ++ [x])).map (v, ·))[b - pref.length]'(by
            simp [hj_lt]) := by
          simp only [newChunks, pref, initMidSlots, hcurEnds_next]
          exact List.getElem_append_right hge_p
        rw [he1, List.getElem_map]
      rw [h1, initialChunks_snoc_getElem hk curEnds x hj_lt]
      by_cases hbb : b = bun
      · have hjq : b - pref.length = curEnds.length / k := by omega
        rw [dite_eq_left hjq]; simp only [hbb, ↓reduceDIte]
        by_cases hmod : curEnds.length % k = 0
        · simp only [hmod, ↓reduceDIte]
        · simp only [hmod, ↓reduceDIte]
          congr 1
          have hb_old : b < oldChunks.length := by rw [hnew_len] at hb; simp [hmod] at hb; exact hb
          have he2 : oldChunks[b]'hb_old =
              ((initialChunks k curEnds).map (v, ·))[b - pref.length]'(by
                rw [hold_len] at hb_old; simp; omega) := by
            simp only [oldChunks, pref, initMidSlots]
            exact List.getElem_append_right hge_p
          simpa [hbb] using (congrArg Prod.snd (he2.trans (List.getElem_map _))).symm
      · have hjq : b - pref.length ≠ curEnds.length / k := by omega
        rw [dite_eq_right hjq]; simp only [hbb, ↓reduceDIte]
        have hb_old : b < oldChunks.length := by
          by_cases hmod : curEnds.length % k = 0
          · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
          · obtain ⟨_, h2⟩ := hbun_cases.2 hmod; omega
        have he2 : oldChunks[b]'hb_old =
            ((initialChunks k curEnds).map (v, ·))[b - pref.length]'(by
              rw [hold_len] at hb_old; simp; omega) := by
          simp only [oldChunks, pref, initMidSlots]
          exact List.getElem_append_right hge_p
        rw [he2, List.getElem_map]
  simp only [InitScanSlotInv, hv] at hI ⊢
  rcases hI with ⟨hlen_cap, h0, h1, h2, hdll, htail, hscr, hbun, htag0, htag1⟩
  have hbun_lt_new : bun < newChunks.length := by
    by_cases hmod : curEnds.length % k = 0
    · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
    · obtain ⟨h1, h2⟩ := hbun_cases.2 hmod; omega
  have hbun_lt_cap : bun < cap := lt_of_lt_of_le hbun_lt_new hcap_next
  refine ⟨hcap_next, ?_, hnb', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hother_block bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)
      (by unfold bsOffBunCap bsOffNB; omega) (by unfold bsOffBunCap bsHeadBase; omega)
      (by unfold bsOffBunCap bsSizeBase; omega)]; exact h0
  · rw [hother_block bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)
      (by unfold bsOffNE bsOffNB; omega) (by unfold bsOffNE bsHeadBase; omega)
      (by unfold bsOffNE bsSizeBase; omega)]; exact h2
  · intro b hb_lt
    by_cases hbb : b = bun
    · rcases hbb with rfl
      refine ⟨Lnew, hdll_new, hsize', ?_, ?_⟩
      · rw [hnew_get b hb_lt]; simp only [↓reduceDIte, hLnew_len]
        split_ifs with hmod <;> simp <;> rfl
      · intro key
        rw [hLnew_mem key, hnew_get b hb_lt]; simp only [↓reduceDIte]
        split_ifs with hmod
        · simp only [List.mem_singleton]
          constructor
          · rintro (he | ⟨hlt, _⟩)
            · exact he
            · have := (hbun_cases.1 hmod).1; exact absurd (this ▸ hlt) (lt_irrefl _)
          · exact Or.inl
        · have hlt : b < oldChunks.length := by
            change b < newChunks.length at hb_lt; rw [hnew_len] at hb_lt; simp [hmod] at hb_lt; exact hb_lt
          simp only [List.mem_append, List.mem_singleton]
          exact ⟨fun h => h.elim Or.inr (fun ⟨_, hm⟩ => Or.inl hm),
            fun h => h.elim (fun hm => Or.inr ⟨hlt, hm⟩) Or.inl⟩
    · have hlt_old : b < oldChunks.length := by
        change b < newChunks.length at hb_lt
        by_cases hmod : curEnds.length % k = 0
        · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
        · obtain ⟨_, h2⟩ := hbun_cases.2 hmod; omega
      have hlt_cap : b < cap := lt_of_lt_of_le hb_lt hcap_next
      obtain ⟨L, hL, hlen, hlen2, hmem⟩ := hdll b hlt_old
      refine ⟨L, hL.of_agree ?_ ?_ ?_, ?_, ?_, ?_⟩
      · have := hother_block (3 + b) (by unfold bundleSlotBlockSize; omega)
          (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
        simpa only [bsHeadBase, Nat.add_assoc] using this
      · intro key hkey
        exact (hother_dll b hlt_old hbb key ((hmem key).mp hkey)).1
      · intro key hkey
        exact (hother_dll b hlt_old hbb key ((hmem key).mp hkey)).2
      · have := hother_block (3 + cap + b) (by unfold bundleSlotBlockSize; omega)
          (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
        simpa only [bsSizeBase, Nat.add_assoc] using
          this.trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen)
      · rw [hnew_get b hb_lt]; simp only [hbb, ↓reduceDIte]; exact hlen2
      · intro key; rw [hnew_get b hb_lt]; simp only [hbb, ↓reduceDIte]; exact hmem key
  · intro b hge hlt
    have hge_old : oldChunks.length ≤ b := by
      change newChunks.length ≤ b at hge; rw [hnew_len] at hge; split_ifs at hge <;> omega
    have hne_bun : b ≠ bun := by change newChunks.length ≤ b at hge; omega
    obtain ⟨t1, t2, t3⟩ := htail b hge_old hlt
    refine ⟨?_, ?_, ?_⟩
    · have := hother_block (3 + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsHeadBase, Nat.add_assoc] using
        this.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1)
    · have := hother_block (3 + cap + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsSizeBase, Nat.add_assoc] using
        this.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2)
    · have := hother_block (3 + 2 * cap + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsParentBase, Nat.add_assoc] using
        this.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)
  · intro b hb_lt
    obtain ⟨s1, s2, s3⟩ := hscr b hb_lt
    refine ⟨?_, ?_, ?_⟩
    · have := hother_block (3 + 3 * cap + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsSeenBase, Nat.add_assoc] using
        this.trans (by simpa [bsSeenBase, Nat.add_assoc] using s1)
    · have := hother_block (3 + 4 * cap + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsInCandBase, Nat.add_assoc] using
        this.trans (by simpa [bsInCandBase, Nat.add_assoc] using s2)
    · have := hother_block (3 + 5 * cap + b) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
      simpa only [bsCandNextBase, Nat.add_assoc] using
        this.trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3)
  · intro b hb_lt y hy
    rw [hnew_get b hb_lt] at hy
    by_cases hbb : b = bun
    · rcases hbb with rfl
      simp only [↓reduceDIte] at hy
      split_ifs at hy with hmod
      · simp only [List.mem_singleton] at hy; subst hy; exact hend'
      · simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy_old | rfl
        · have hlt_old : b < oldChunks.length := by
            change b < newChunks.length at hb_lt; rw [hnew_len] at hb_lt; simp [hmod] at hb_lt; exact hb_lt
          have hne : y ≠ (cord rList[i])[t] := fun h => hfresh b hlt_old (h ▸ hy_old)
          rw [hother_end y (mem_initMidSlots_end hk hlt_old hy_old).1 hne]; exact hbun b hlt_old y hy_old
        · exact hend'
    · simp only [hbb, ↓reduceDIte] at hy
      have hlt_old : b < oldChunks.length := by
        change b < newChunks.length at hb_lt
        by_cases hmod : curEnds.length % k = 0
        · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
        · obtain ⟨_, h2⟩ := hbun_cases.2 hmod; omega
      have hne : y ≠ (cord rList[i])[t] := fun h => hfresh b hlt_old (h ▸ hy)
      rw [hother_end y (mem_initMidSlots_end hk hlt_old hy).1 hne]; exact hbun b hlt_old y hy
  · intro he; rw [hcurEnds_next] at he; simp at he
  · intro _; refine ⟨htag', ?_⟩
    rw [hcurB']
    change bun + 1 = newChunks.length
    by_cases hmod : curEnds.length % k = 0
    · obtain ⟨h1, h2⟩ := hbun_cases.1 hmod; omega
    · obtain ⟨h1, h2⟩ := hbun_cases.2 hmod; omega

end

end MinCostFlow.SparseCore.Program
