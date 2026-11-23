module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase4Facts
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpacePhases13
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceLen

import MinCostFlow.DynSpanner.Program.DynSpannerSpace
import MinCostFlow.DynSpanner.Program.DynSpannerSpaceStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial space bound for Phase 4 of the first step (`AssemblyFirstStepSpacePhase4`)

Bounds the total heap space of Phase 4 (`asmFirstP4Sel_runs`, `asmFirstPhase4_runs_of_sel`):
```
p4WsSize eCap
+ (tasks.map (p4TaskSpace P S6 mem₃)).sum
+ rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₃ tasks)) lo hi
+ asmFirstPhase4Room eCap nSp nU nEd qE qR
```
by an explicit `PolyBound` in `X = M + N + k + vCap + eCap + L + depth + words + editWords`:
* `p4SlotWalkSum_le_caps`: for any valid dynamic-spanner history at slot `s`, the sum of
  `Read.walkWords (slotWalk P S s e)` over `e ∈ (d.state P).G.E` is at most
  `3 * P.eCap * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊`.
* `p4TaskSpace_le_caps`: each task `t ∈ tasks` uses at most
  `2 * B_t * (180 * B_t * W_len) ^ P.impl.cw + 450 * B_t ^ 3 * g * W_len + 3 * P.eCap * W_len`
  words (`dsUpdateOpSpace_le_caps` + `p4SlotWalkSum_le_caps`).
* `p4SpanAfter_slot_valid`: preserves per-slot history validity across `p4SpanAfter`.
* `asmFirstPhase4Space_le_poly_of_lenBound`: bounds all of Phase 4 by
  `(asmFirstPhase4SpacePoly qE qR P.impl.cw Cγ cγ C_len c_len capExp).eval X` given
  `⌈P.impl.γ_ℓ M⌉₊ ≤ Cγ * (M + 2) ^ cγ` and `⌈lenBound (P.impl.γ_ℓ M) depth⌉₊ ≤ C_len * (M + N + 2) ^ c_len`.
* `asmFirstPhase4Space_le_poly_of_chosenL`: discharges both bounds under
  `depth ≤ Expander.chosenL ((M + N) ^ 2)` and subpolynomial stretch
  `∀ m, impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **Polynomial space bound for Phase 4**, parameterized by tour query spaces `qE, qR`, sparsifier
word exponent `cw`, stretch bound `Cγ · (m + 2) ^ cγ`, walk-length bound
`C_len · (M + N + 2) ^ c_len`, and `capExp`. -/
def asmFirstPhase4SpacePoly (qE qR cw Cγ cγ C_len c_len capExp : ℕ) : PolyBound where
  coeff := 3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 12 * C_len + 98 + qE + 4 * qR
  deg := (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11)

/-- Pure non-word-size validity of one dynamic-spanner history `d` under `P`. -/
def P4HistValid (P : DSParams) (d : DSHist) : Prop :=
  d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < P.eCap) ∧
    d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u)

/-- Pure non-word-size validity of one Phase 4 update task `t` on `S6` and `mem`. -/
def P4TaskValid (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem : ℕ → ℕ)
    (t : SpanUpdTask) : Prop :=
  ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d → mem t.batchPtr ≠ 0 →
    let U := (decodeBatch mem t.batchPtr (d.state P).G).1
    let lens := (decodeBatch mem t.batchPtr (d.state P).G).2
    d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < P.eCap) ∧
      d.G₀.n + P.splitBound ≤ P.vCap ∧
      d.G₀.BatchIsValid (d.flat ++ U) ∧ (∀ u ∈ d.flat ++ U, isDelOrSplit u) ∧
      batchSplitCount (d.flat ++ U) ≤ P.splitBound ∧ lens.sum ≤ t.W

end

/-! ## Helpers -/

private lemma list_sum_map_le_mul_p4 {α : Type*} (l : List α) (f : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ l, f x ≤ K) : (l.map f).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    omega

private lemma rangeCost_le_mul (f : ℕ → ℕ) (lo hi K : ℕ)
    (h : ∀ s, lo ≤ s → s < hi → f s ≤ K) :
    rangeCost f lo hi ≤ (hi - lo) * K := by
  unfold rangeCost
  refine (list_sum_map_le_mul_p4 (List.range' lo (hi - lo)) f K fun s hs => ?_).trans
    (by rw [List.length_range'])
  obtain ⟨i, hi', rfl⟩ := List.mem_range'.mp hs
  simp only [Nat.one_mul]
  exact h (lo + i) (by omega) (by omega)

private lemma p4NewHist_flat (P : DSParams) (mem : ℕ → ℕ) (d : DSHist) (t : SpanUpdTask) :
    (p4NewHist P mem d t).flat = d.flat ++ (decodeBatch mem t.batchPtr (d.state P).G).1 := by
  simp [p4NewHist, DSHist.flat]

private lemma p4SpanStep_valid (P : DSParams) {cap : ℕ} (S6 S : BucketSpannerState cap)
    (mem : ℕ → ℕ) (t : SpanUpdTask)
    (hS : ∀ (j : Fin cap) (d : DSHist), S j = some d → P4HistValid P d)
    (ht : P4TaskValid P S6 mem t) :
    ∀ (j : Fin cap) (d : DSHist), p4SpanStep P S6 mem S t j = some d → P4HistValid P d := by
  intro j d hjd
  unfold p4SpanStep p4OnTask at hjd
  by_cases hs : t.slot < cap
  · simp only [hs, ↓reduceDIte] at hjd
    cases hS6 : S6 ⟨t.slot, hs⟩ with
    | none => simp only [hS6] at hjd; exact hS j d hjd
    | some d0 =>
      simp only [hS6] at hjd
      by_cases hb : mem t.batchPtr = 0
      · simp only [hb, ↓reduceIte] at hjd; exact hS j d hjd
      · simp only [hb, ↓reduceIte] at hjd
        by_cases hj : j = ⟨t.slot, hs⟩
        · subst hj
          simp only [BucketSpannerState.set, Function.update_self, Option.some.injEq] at hjd
          subst hjd
          obtain ⟨hV, hm, hE, -, hBV, hds, -, -⟩ := ht hs d0 hS6 hb
          refine ⟨hV, hm, hE, ?_, ?_⟩
          · rw [p4NewHist_flat]; exact hBV
          · rw [p4NewHist_flat]; exact hds
        · simp only [BucketSpannerState.set, Function.update_of_ne hj] at hjd
          exact hS j d hjd
  · simp only [hs, ↓reduceDIte] at hjd; exact hS j d hjd

/-- Pure arithmetic combination for Phase 4. -/
private lemma asmFirstPhase4_arith {B qE qR cw Cγ cγ C_len c_len : ℕ} (hB : 2 ≤ B)
    {vCap eCap nSp nU nEd spV spE depth W_max g W_len taskLen newLen taskSum newSum : ℕ}
    (hvCap : vCap ≤ B) (heCap : eCap ≤ B) (hnSp : nSp ≤ B) (hnU : nU ≤ B) (hnEd : nEd ≤ B)
    (hsp : spV + spE + 2 ≤ B) (hdepth : depth ≤ B) (hWmax : W_max ≤ 826 * B ^ 3)
    (hg : g ≤ Cγ * B ^ cγ) (hWlen : W_len ≤ C_len * B ^ c_len)
    (htaskLen : taskLen ≤ 2 * B ^ 2) (hnewLen : newLen ≤ 2 * B ^ 2)
    (htaskSum : taskSum ≤ taskLen *
      (2 * (spV + spE + depth + W_max + 2) *
          (180 * (spV + spE + depth + W_max + 2) * W_len) ^ cw +
        450 * (spV + spE + depth + W_max + 2) ^ 3 * g * W_len + 3 * spE * W_len))
    (hnewSum : newSum ≤ newLen * (3 * spE * W_len)) :
    p4WsSize eCap + taskSum + newSum + asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 12 * C_len + 98 + qE + 4 * qR) *
        B ^ (cw * (c_len + 3) + cγ + c_len + 11) := by
  set D := cw * (c_len + 3) + cγ + c_len + 11
  set Bt := spV + spE + depth + W_max + 2
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hB_B3 : B ≤ B ^ 3 := Nat.le_self_pow (by decide) B
  have hB_D : B ≤ B ^ D := by simpa using hpw (a := 1) (b := D) (by omega)
  have h1_D : 1 ≤ B ^ D := Nat.one_le_pow _ _ hBpos
  have hBt : Bt ≤ 828 * B ^ 3 := by
    have : spV + spE + depth + 2 ≤ 2 * B := by omega
    omega
  -- 1. First per-task term
  have hT1_per : 2 * Bt * (180 * Bt * W_len) ^ cw ≤
      1656 * (149040 * C_len) ^ cw * B ^ (cw * (c_len + 3) + 3) := by
    have hbase : 180 * Bt * W_len ≤ (149040 * C_len) * B ^ (c_len + 3) := by
      calc 180 * Bt * W_len ≤ 180 * (828 * B ^ 3) * (C_len * B ^ c_len) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 180 hBt) hWlen
        _ = (149040 * C_len) * B ^ (c_len + 3) := by ring
    have hpow : (180 * Bt * W_len) ^ cw ≤ (149040 * C_len) ^ cw * B ^ (cw * (c_len + 3)) := by
      calc (180 * Bt * W_len) ^ cw ≤ ((149040 * C_len) * B ^ (c_len + 3)) ^ cw :=
            Nat.pow_le_pow_left hbase cw
        _ = (149040 * C_len) ^ cw * (B ^ (c_len + 3)) ^ cw := mul_pow _ _ _
        _ = (149040 * C_len) ^ cw * B ^ (cw * (c_len + 3)) := by
            rw [← pow_mul, Nat.mul_comm (c_len + 3) cw]
    calc 2 * Bt * (180 * Bt * W_len) ^ cw
        ≤ (2 * (828 * B ^ 3)) * ((149040 * C_len) ^ cw * B ^ (cw * (c_len + 3))) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hBt) hpow
      _ = 1656 * (149040 * C_len) ^ cw * B ^ (cw * (c_len + 3) + 3) := by ring
  -- 2. Second per-task term
  have hT2_per : 450 * Bt ^ 3 * g * W_len ≤ 450 * 828 ^ 3 * Cγ * C_len * B ^ (cγ + c_len + 9) := by
    have hBt3 : Bt ^ 3 ≤ 828 ^ 3 * B ^ 9 := by
      calc Bt ^ 3 ≤ (828 * B ^ 3) ^ 3 := Nat.pow_le_pow_left hBt 3
        _ = 828 ^ 3 * B ^ 9 := by ring
    calc 450 * Bt ^ 3 * g * W_len
        ≤ 450 * (828 ^ 3 * B ^ 9) * (Cγ * B ^ cγ) * (C_len * B ^ c_len) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 450 hBt3) hg) hWlen
      _ = 450 * 828 ^ 3 * Cγ * C_len * B ^ (cγ + c_len + 9) := by ring
  -- 3. Walk-sum term `3 * spE * W_len`
  have hW_per : 3 * spE * W_len ≤ 3 * C_len * B ^ (c_len + 1) := by
    calc 3 * spE * W_len ≤ 3 * B * (C_len * B ^ c_len) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 3 (by omega)) hWlen
      _ = 3 * C_len * B ^ (c_len + 1) := by ring
  -- Combine tasks
  have hTasks : taskSum ≤
      (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 6 * C_len) * B ^ D := by
    set E := cw * (c_len + 3) + cγ + c_len + 9
    have h1 : 2 * Bt * (180 * Bt * W_len) ^ cw ≤ 1656 * (149040 * C_len) ^ cw * B ^ E :=
      hT1_per.trans (Nat.mul_le_mul_left _ (hpw (by omega)))
    have h2 : 450 * Bt ^ 3 * g * W_len ≤ 450 * 828 ^ 3 * Cγ * C_len * B ^ E :=
      hT2_per.trans (Nat.mul_le_mul_left _ (hpw (by omega)))
    have h3 : 3 * spE * W_len ≤ 3 * C_len * B ^ E :=
      hW_per.trans (Nat.mul_le_mul_left _ (hpw (by omega)))
    have hsum : 2 * Bt * (180 * Bt * W_len) ^ cw + 450 * Bt ^ 3 * g * W_len + 3 * spE * W_len ≤
        (1656 * (149040 * C_len) ^ cw + 450 * 828 ^ 3 * Cγ * C_len + 3 * C_len) * B ^ E := by
      have he : (1656 * (149040 * C_len) ^ cw + 450 * 828 ^ 3 * Cγ * C_len + 3 * C_len) * B ^ E =
          1656 * (149040 * C_len) ^ cw * B ^ E + 450 * 828 ^ 3 * Cγ * C_len * B ^ E +
            3 * C_len * B ^ E := by ring
      omega
    calc taskSum ≤ (2 * B ^ 2) * ((1656 * (149040 * C_len) ^ cw + 450 * 828 ^ 3 * Cγ * C_len + 3 * C_len) * B ^ E) :=
          htaskSum.trans (Nat.mul_le_mul htaskLen hsum)
      _ = (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 6 * C_len) * B ^ (E + 2) := by
          ring
      _ = (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 6 * C_len) * B ^ D := by
          have hED : E + 2 = D := by omega
          rw [hED]
  -- Combine new slots
  have hNew : newSum ≤ 6 * C_len * B ^ D := by
    calc newSum ≤ (2 * B ^ 2) * (3 * C_len * B ^ (c_len + 1)) :=
          hnewSum.trans (Nat.mul_le_mul hnewLen hW_per)
      _ = 6 * C_len * B ^ (c_len + 3) := by ring
      _ ≤ 6 * C_len * B ^ D := Nat.mul_le_mul_left _ (hpw (by omega))
  -- Combine workspace + room
  have hRoom : p4WsSize eCap + asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (98 + qE + 4 * qR) * B ^ D := by
    unfold p4WsSize asmFirstPhase4Room p4RotSpace
    have hqE : qE ≤ qE * B ^ D := Nat.le_mul_of_pos_right qE h1_D
    have hqR1 : 2 * nU * qR ≤ 2 * qR * B ^ D := by
      calc 2 * nU * qR = 2 * qR * nU := by ring
        _ ≤ 2 * qR * B ^ D := Nat.mul_le_mul_left _ (hnU.trans hB_D)
    have hqR2 : 2 * nEd * qR ≤ 2 * qR * B ^ D := by
      calc 2 * nEd * qR = 2 * qR * nEd := by ring
        _ ≤ 2 * qR * B ^ D := Nat.mul_le_mul_left _ (hnEd.trans hB_D)
    have he : (98 + qE + 4 * qR) * B ^ D = 98 * B ^ D + qE * B ^ D + 2 * qR * B ^ D + 2 * qR * B ^ D := by
      ring
    omega
  have he : (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 12 * C_len + 98 + qE + 4 * qR) * B ^ D =
      (3312 * (149040 * C_len) ^ cw + 900 * 828 ^ 3 * Cγ * C_len + 6 * C_len) * B ^ D +
        6 * C_len * B ^ D + (98 + qE + 4 * qR) * B ^ D := by ring
  omega

/-! ## Public bounds -/

public section

/-- **Per-slot walk-word sum bound.** If slot `s` holds a valid dynamic-spanner history `d`,
the sum of `Read.walkWords (slotWalk P S s e)` over `e ∈ (d.state P).G.E` is at most
`3 * P.eCap * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊`. -/
theorem p4SlotWalkSum_le_caps (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) {s : ℕ}
    (hs : s < cap) {d : DSHist} (hd : S ⟨s, hs⟩ = some d)
    (hL : 1 ≤ P.L) (hval : P4HistValid P d) :
    (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S s e)) ≤
      3 * P.eCap * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊ := by
  obtain ⟨hVG₀, hGm₀, hG₀E, hBV, hds⟩ := hval
  set W_len := ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊
  have hW1 : 1 ≤ W_len := one_le_ceil_lenBound P.impl P.mMax P.L
  have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hInv := (runInv_all hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
    hBV hds d.flat.length le_rfl).1
  have hGE_sub : (d.state P).G.E ⊆ d.G₀.E := by
    change (runState d.G₀ (d.q P) (canonicalSparsify P.impl) d.flat d.flat.length).G.E ⊆ d.G₀.E
    rw [hInv.G_eq, List.take_length]
    exact (batch_delOrSplit_invariants d.flat d.G₀ hVG₀ hBV hds).2.1
  have hcard : (d.state P).G.E.card ≤ P.eCap := by
    have h1 : d.G₀.E.card ≤ P.eCap :=
      (Finset.card_le_card fun e he => Finset.mem_range.mpr (hG₀E e he)).trans (Finset.card_range P.eCap).le
    exact (Finset.card_le_card hGE_sub).trans h1
  have hsum : (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S s e)) ≤
      (d.state P).G.E.card * (3 * W_len) := by
    rw [← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun e he => ?_
    unfold Read.walkWords slotWalk
    simp only [hs, ↓reduceDIte, hd]
    split_ifs
    · simp only [List.length_singleton]; omega
    · have hlen := dsHist_piTotal_length_le P hL hVG₀ hGm₀ hBV hds he
      omega
  calc (d.state P).G.E.sum _ ≤ (d.state P).G.E.card * (3 * W_len) := hsum
    _ ≤ P.eCap * (3 * W_len) := Nat.mul_le_mul_right _ hcard
    _ = 3 * P.eCap * W_len := by ring

/-- **Validity of every occupied slot after `p4SpanAfter`.** Preserved from `S6` when every task
in `tasks` satisfies `P4TaskValid P S6 mem`. -/
theorem p4SpanAfter_slot_valid (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem : ℕ → ℕ) (tasks : List SpanUpdTask)
    (hS6 : ∀ (j : Fin cap) (d : DSHist), S6 j = some d → P4HistValid P d)
    (htasks : ∀ t ∈ tasks, P4TaskValid P S6 mem t) :
    ∀ (j : Fin cap) (d : DSHist), p4SpanAfter P S6 mem tasks j = some d → P4HistValid P d := by
  have hfold : ∀ (ts : List SpanUpdTask) (S : BucketSpannerState cap),
      (∀ (j : Fin cap) (d : DSHist), S j = some d → P4HistValid P d) →
      (∀ t ∈ ts, P4TaskValid P S6 mem t) →
      ∀ (j : Fin cap) (d : DSHist), ts.foldl (p4SpanStep P S6 mem) S j = some d → P4HistValid P d := by
    intro ts
    induction ts with
    | nil => intro S hS _; exact hS
    | cons t rest ih =>
      intro S hS hts
      rw [List.foldl_cons]
      exact ih _ (p4SpanStep_valid P S6 S mem t hS (hts t List.mem_cons_self))
        fun t' ht' => hts t' (List.mem_cons_of_mem t ht')
  exact hfold tasks S6 hS6 htasks

/-- **Per-task space bound of Phase 4.** For any task `t` satisfying `P4TaskValid P S6 mem` with
`t.W ≤ W_max`, `p4TaskSpace P S6 mem t` is bounded in terms of `P.vCap`, `P.eCap`, `P.L`, `W_max`,
`⌈P.impl.γ_ℓ P.mMax⌉₊`, and `⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊`. -/
theorem p4TaskSpace_le_caps (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem : ℕ → ℕ) {t : SpanUpdTask} {W_max : ℕ}
    (hL : 1 ≤ P.L) (ht : P4TaskValid P S6 mem t) (hW : t.W ≤ W_max) :
    let B_t := P.vCap + P.eCap + P.L + W_max + 2
    let g := ⌈P.impl.γ_ℓ P.mMax⌉₊
    let W_len := ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊
    p4TaskSpace P S6 mem t ≤
      2 * B_t * (180 * B_t * W_len) ^ P.impl.cw + 450 * B_t ^ 3 * g * W_len + 3 * P.eCap * W_len := by
  intro B_t g W_len
  unfold p4TaskSpace p4OnTask
  by_cases hs : t.slot < cap
  · simp only [hs, ↓reduceDIte]
    cases hd : S6 ⟨t.slot, hs⟩ with
    | none => simp
    | some d =>
      by_cases hb : mem t.batchPtr = 0
      · simp [hb]
      · simp only [hb, ↓reduceIte]
        obtain ⟨hVG₀, hGm₀, hG₀E, hG₀n, hBV, hds, hsplit, hlens⟩ := ht hs d hd hb
        have hop_eq : opBatch P d [0, t.batchPtr, t.W, 0] mem =
            decodeBatch mem t.batchPtr (d.state P).G := rfl
        have hdsOp := dsUpdateOpSpace_le_caps P (d := d) (b := 0) (batchPtr := t.batchPtr)
          (W := t.W) (h := 0) (mem := mem) hL hVG₀ hGm₀ hG₀E hG₀n
          (hop_eq ▸ hBV) (hop_eq ▸ hds) (hop_eq ▸ hsplit) (hop_eq ▸ hlens)
        have hB_le : P.vCap + P.eCap + P.L + t.W + 2 ≤ B_t := by omega
        have hdsOp' : dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem ≤
            2 * B_t * (180 * B_t * W_len) ^ P.impl.cw + 450 * B_t ^ 3 * g * W_len := by
          refine hdsOp.trans (Nat.add_le_add ?_ ?_)
          · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hB_le)
              (Nat.pow_le_pow_left (Nat.mul_le_mul_right W_len (Nat.mul_le_mul_left 180 hB_le)) _)
          · exact Nat.mul_le_mul_right W_len (Nat.mul_le_mul_right g
              (Nat.mul_le_mul_left 450 (Nat.pow_le_pow_left hB_le 3)))
        have hnewValid : P4HistValid P (p4NewHist P mem d t) := by
          refine ⟨hVG₀, hGm₀, hG₀E, ?_, ?_⟩
          · rw [p4NewHist_flat]; exact hBV
          · rw [p4NewHist_flat]; exact hds
        have hwalk := p4SlotWalkSum_le_caps P (S6.set ⟨t.slot, hs⟩ (some (p4NewHist P mem d t)))
          hs (by simp [BucketSpannerState.set]) hL hnewValid
        exact Nat.add_le_add hdsOp' hwalk
  · simp [hs]

/-- **Phase 4 polynomial space bound given an explicit walk-length bound.** Bounds the full Phase 4
space sum by `(asmFirstPhase4SpacePoly qE qR P.impl.cw Cγ cγ C_len c_len capExp).eval X`. -/
theorem asmFirstPhase4Space_le_poly_of_lenBound
    (P : DSParams) {cap M N k vCap eCap L depth words editWords nSp nU nEd qE qR
      lo hi capExp Cγ cγ C_len c_len W_max : ℕ}
    {S6 : BucketSpannerState cap} {tasks : List SpanUpdTask} {mem : ℕ → ℕ}
    (hL : 1 ≤ P.L) (hP_L : P.L = depth) (hP_mMax : P.mMax = M)
    (hsp : P.vCap + P.eCap + 2 ≤ (M + N + 2) ^ (capExp + 7))
    (hγ : ⌈P.impl.γ_ℓ M⌉₊ ≤ Cγ * (M + 2) ^ cγ)
    (hlen : ⌈lenBound (P.impl.γ_ℓ M) depth⌉₊ ≤ C_len * (M + N + 2) ^ c_len)
    (hWmax : W_max ≤ asmFirstPhase3SpacePoly.eval
      (M + N + k + vCap + eCap + L + depth + words + editWords))
    (htasks_len : tasks.length ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hnew_len : hi - lo ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin cap) (d : DSHist), S6 j = some d → P4HistValid P d)
    (htasks_valid : ∀ t ∈ tasks, P4TaskValid P S6 mem t ∧ t.W ≤ W_max) :
    p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem)).sum +
        rangeCost (p4NewSpace P (p4SpanAfter P S6 mem tasks)) lo hi +
        asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (asmFirstPhase4SpacePoly qE qR P.impl.cw Cγ cγ C_len c_len capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set Z := X + 2
  set B := Z ^ (capExp + 7)
  have hZ2 : 2 ≤ Z := by omega
  have hZ_B : Z ≤ B := Nat.le_self_pow (by omega) Z
  have hB2 : 2 ≤ B := hZ2.trans hZ_B
  have hsp_B : P.vCap + P.eCap + 2 ≤ B :=
    hsp.trans (Nat.pow_le_pow_left (by omega) _)
  have hWmax_B : W_max ≤ 826 * B ^ 3 := by
    unfold asmFirstPhase3SpacePoly PolyBound.eval at hWmax
    exact hWmax.trans (Nat.mul_le_mul_left 826 (Nat.pow_le_pow_left hZ_B 3))
  have hg_B : ⌈P.impl.γ_ℓ P.mMax⌉₊ ≤ Cγ * B ^ cγ := by
    rw [hP_mMax]
    exact hγ.trans (Nat.mul_le_mul_left Cγ (Nat.pow_le_pow_left (by omega) cγ))
  have hWlen_B : ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊ ≤ C_len * B ^ c_len := by
    rw [hP_mMax, hP_L]
    exact hlen.trans (Nat.mul_le_mul_left C_len (Nat.pow_le_pow_left (by omega) c_len))
  have htl_B : tasks.length ≤ 2 * B ^ 2 :=
    htasks_len.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2))
  have hnl_B : hi - lo ≤ 2 * B ^ 2 :=
    hnew_len.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2))
  have htaskSum : (tasks.map (p4TaskSpace P S6 mem)).sum ≤
      tasks.length *
        (2 * (P.vCap + P.eCap + P.L + W_max + 2) *
            (180 * (P.vCap + P.eCap + P.L + W_max + 2) * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊) ^ P.impl.cw +
          450 * (P.vCap + P.eCap + P.L + W_max + 2) ^ 3 * ⌈P.impl.γ_ℓ P.mMax⌉₊ *
            ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊ +
          3 * P.eCap * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊) :=
    list_sum_map_le_mul_p4 tasks _ _ fun t ht =>
      p4TaskSpace_le_caps P S6 mem hL (htasks_valid t ht).1 (htasks_valid t ht).2
  have hAfterValid := p4SpanAfter_slot_valid P S6 mem tasks hS6_valid fun t ht =>
    (htasks_valid t ht).1
  have hnewSum : rangeCost (p4NewSpace P (p4SpanAfter P S6 mem tasks)) lo hi ≤
      (hi - lo) * (3 * P.eCap * ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊) := by
    refine rangeCost_le_mul _ lo hi _ fun s _ _ => ?_
    unfold p4NewSpace
    by_cases hs : s < cap
    · simp only [hs, ↓reduceDIte]
      cases hd : p4SpanAfter P S6 mem tasks ⟨s, hs⟩ with
      | none => simp
      | some d => exact p4SlotWalkSum_le_caps P _ hs hd hL (hAfterValid ⟨s, hs⟩ d hd)
    · simp [hs]
  unfold asmFirstPhase4SpacePoly PolyBound.eval
  dsimp only
  rw [pow_mul]
  exact asmFirstPhase4_arith hB2 (by omega) (by omega) (by omega) (by omega) (by omega) hsp_B
    (by omega) hWmax_B hg_B hWlen_B htl_B hnl_B htaskSum hnewSum

/-- **Phase 4 polynomial space bound under `chosenL` and subpolynomial stretch.** Discharges the
stretch and walk-length bounds from `depth ≤ Expander.chosenL ((M + N) ^ 2)` and
`∀ m, P.impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))` (`0 < C_sp`). -/
theorem asmFirstPhase4Space_le_poly_of_chosenL
    (P : DSParams) {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, P.impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {cap M N k vCap eCap L depth words editWords nSp nU nEd qE qR
      lo hi capExp W_max : ℕ}
    {S6 : BucketSpannerState cap} {tasks : List SpanUpdTask} {mem : ℕ → ℕ}
    (hL : 1 ≤ P.L) (hP_L : P.L = depth) (hP_mMax : P.mMax = M)
    (hdepth : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hsp : P.vCap + P.eCap + 2 ≤ (M + N + 2) ^ (capExp + 7))
    (hWmax : W_max ≤ asmFirstPhase3SpacePoly.eval
      (M + N + k + vCap + eCap + L + depth + words + editWords))
    (htasks_len : tasks.length ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hnew_len : hi - lo ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin cap) (d : DSHist), S6 j = some d → P4HistValid P d)
    (htasks_valid : ∀ t ∈ tasks, P4TaskValid P S6 mem t ∧ t.W ≤ W_max) :
    p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem)).sum +
        rangeCost (p4NewSpace P (p4SpanAfter P S6 mem tasks)) lo hi +
        asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (asmFirstPhase4SpacePoly qE qR P.impl.cw (gammaLinearConst C_sp) 1
        (lenBoundLinearConst C_sp) 1 capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstPhase4Space_le_poly_of_lenBound P hL hP_L hP_mMax hsp
    (by simpa [pow_one] using ceil_gamma_le_linear_of_subpoly hC hγ M)
    (by simpa [pow_one] using ceil_lenBound_le_linear_of_chosenL hC hγ hdepth)
    hWmax htasks_len hnew_len hnSp hnU hnEd hS6_valid htasks_valid

end

end MinCostFlow.SparseCore.Program
