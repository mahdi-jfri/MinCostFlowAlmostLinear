module

public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Narrow.CappedRecurrence
public import MinCostFlow.Narrow.CappedPhase
public import MinCostFlow.Narrow.BitScalingModel
public import MinCostFlow.Scaling.PositiveCapacities
public import MinCostFlow.NarrowProg.AccAdd

/-!
# Stage 2 phase state and transition lemmas

Pure mathematical lemmas for Stage 2 (Gabow bit scaling) in narrow words:
- touch-count bounds `accTouches` keeping every lazy accumulator limb below `2 ^ (w - 1)`;
- erasing zero-capacity dummy loops (`erasedDelta`) from a positive-capacity solver's output;
- preserving optimality (`nextGhostFlow_optimal`), capped residual/flow recurrences
  (`nextCappedResidual_eq`, `nextCappedFlow_eq`), scaled accumulator differences
  (`nextAcc_diff_eq`), and total accumulator bounds (`nextAcc_val_le`).
-/

@[expose] public section

open WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Touch-count and accumulator invariants -/

/-- Number of updates touching limb `j` across phases `0, ..., t - 1` (shifts `T - 1, ..., T - t`). -/
def accTouches (k T t j : ℕ) : ℕ :=
  ((Finset.Ico (T - t) T).filter fun s => s / k = j).card +
  ((Finset.Ico (T - t) T).filter fun s => s / k + 1 = j).card

theorem accTouches_zero (k T j : ℕ) : accTouches k T 0 j = 0 := by
  simp [accTouches]

private theorem card_filter_div_eq_le {k : ℕ} (hk : 1 ≤ k) (S : Finset ℕ) (q : ℕ) :
    (S.filter fun s => s / k = q).card ≤ k := by
  have hsub : (S.filter fun s => s / k = q) ⊆ Finset.Ico (q * k) ((q + 1) * k) := by
    intro s hs
    have hq : s / k = q := (Finset.mem_filter.mp hs).2
    rw [Finset.mem_Ico]
    have h1 : k * (s / k) ≤ s := Nat.mul_div_le s k
    have h2 : s < k * (s / k + 1) := by
      have hdm := Nat.div_add_mod s k
      have hmod := Nat.mod_lt s (by omega : 0 < k)
      nlinarith
    rw [hq] at h1 h2
    exact ⟨by nlinarith, by nlinarith⟩
  calc (S.filter fun s => s / k = q).card
      ≤ (Finset.Ico (q * k) ((q + 1) * k)).card := Finset.card_le_card hsub
    _ = (q + 1) * k - q * k := Nat.card_Ico _ _
    _ = k := by rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

/-- Every limb is touched at most `2 * k` times across all phases. -/
theorem accTouches_le_two_mul {k : ℕ} (hk : 1 ≤ k) (T t j : ℕ) :
    accTouches k T t j ≤ 2 * k := by
  unfold accTouches
  have h1 : ((Finset.Ico (T - t) T).filter fun s => s / k = j).card ≤ k :=
    card_filter_div_eq_le hk _ j
  have h2 : ((Finset.Ico (T - t) T).filter fun s => s / k + 1 = j).card ≤ k := by
    cases j with
    | zero =>
      have hempty : ((Finset.Ico (T - t) T).filter fun s => s / k + 1 = 0) = ∅ := by
        ext s; simp
      rw [hempty, Finset.card_empty]; omega
    | succ j' =>
      have heq : ((Finset.Ico (T - t) T).filter fun s => s / k + 1 = j' + 1) =
          ((Finset.Ico (T - t) T).filter fun s => s / k = j') := by
        ext s; simp
      rw [heq]
      exact card_filter_div_eq_le hk _ j'
  omega

/-- Advancing from phase `t` to `t + 1` adds shift `s = T - 1 - t` to `accTouches`. -/
theorem accTouches_succ {k T t : ℕ} (ht : t < T) (j : ℕ) :
    accTouches k T (t + 1) j =
      accTouches k T t j +
        (if (T - 1 - t) / k = j then 1 else 0) +
        (if (T - 1 - t) / k + 1 = j then 1 else 0) := by
  have hins : Finset.Ico (T - (t + 1)) T = insert (T - 1 - t) (Finset.Ico (T - t) T) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnotmem : T - 1 - t ∉ Finset.Ico (T - t) T := by
    simp only [Finset.mem_Ico]; omega
  unfold accTouches
  rw [hins, Finset.filter_insert, Finset.filter_insert]
  have hnm1 : T - 1 - t ∉ (Finset.Ico (T - t) T).filter (fun s => s / k = j) :=
    fun h => hnotmem (Finset.mem_filter.mp h).1
  have hnm2 : T - 1 - t ∉ (Finset.Ico (T - t) T).filter (fun s => s / k + 1 = j) :=
    fun h => hnotmem (Finset.mem_filter.mp h).1
  split_ifs with h1 h2 <;> simp [Finset.card_insert_of_notMem, hnm1, hnm2] <;> omega

/-- One `accAdd` step at shift `T - 1 - t` preserves the touch-count bound on every limb. -/
theorem accAddResult_limb_bound {k T t x : ℕ} {ls : List ℕ}
    (hk : 1 ≤ k) (ht : t < T) (hx : x < 2 ^ k)
    (hfit : (T - 1 - t) / k + 1 < ls.length)
    (hbound : ∀ j < ls.length, ls.getD j 0 ≤ accTouches k T t j * (2 ^ k - 1)) :
    ∀ j < (accAddResult k ls x (T - 1 - t)).length,
      (accAddResult k ls x (T - 1 - t)).getD j 0 ≤ accTouches k T (t + 1) j * (2 ^ k - 1) := by
  intro j hj
  rw [length_accAddResult] at hj
  set s := T - 1 - t
  set q := s / k
  have ⟨hlo_lt, hhi_lt⟩ := accAdd_parts_lt hk hx (s := s)
  have hlen1 : (ls.set q (ls.getD q 0 + (x * 2 ^ (s % k)) % 2 ^ k)).length = ls.length :=
    List.length_set
  have hacc := accTouches_succ (k := k) ht j
  have hprev := hbound j hj
  unfold accAddResult
  dsimp only
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_set]; exact hj)]
  by_cases hj1 : j = q + 1
  · subst hj1
    rw [List.getElem_set_self (by simp only [List.length_set]; exact hfit)]
    have htouch : accTouches k T t (q + 1) + 1 ≤ accTouches k T (t + 1) (q + 1) := by
      rw [hacc]; dsimp only [q, s]; split_ifs <;> omega
    have hmul := Nat.mul_le_mul_right (2 ^ k - 1) htouch
    rw [Nat.add_mul, Nat.one_mul] at hmul
    dsimp only [q] at hprev hmul ⊢
    omega
  · rw [List.getElem_set_ne (by omega : s / k + 1 ≠ j)]
    by_cases hj0 : j = q
    · subst hj0
      rw [List.getElem_set_self (by simp only [List.length_set]; omega)]
      have htouch : accTouches k T t q + 1 ≤ accTouches k T (t + 1) q := by
        rw [hacc]; dsimp only [q, s]; split_ifs <;> omega
      have hmul := Nat.mul_le_mul_right (2 ^ k - 1) htouch
      rw [Nat.add_mul, Nat.one_mul] at hmul
      dsimp only [q] at hprev hmul ⊢
      omega
    · rw [List.getElem_set_ne (by omega : s / k ≠ j), ← List.getD_eq_getElem ls 0 hj]
      have htouch : accTouches k T t j ≤ accTouches k T (t + 1) j := by
        rw [hacc]; split_ifs <;> omega
      exact le_trans hprev (Nat.mul_le_mul_right _ htouch)

/-- Every lazy limb bounded by `accTouches k T t j * (2 ^ k - 1)` stays below `2 ^ (w - 1)`
when `k + Nat.log 2 (2 * k) + 2 ≤ w`. -/
theorem accTouches_limb_lt_half_word {k w T t j : ℕ}
    (hk : 1 ≤ k) (hw : k + Nat.log 2 (2 * k) + 2 ≤ w) :
    accTouches k T t j * (2 ^ k - 1) < 2 ^ (w - 1) := by
  have h2k : 0 < 2 ^ k := by positivity
  have h1 : accTouches k T t j * (2 ^ k - 1) ≤ 2 * k * (2 ^ k - 1) :=
    Nat.mul_le_mul_right _ (accTouches_le_two_mul hk T t j)
  have h2 : 2 * k * (2 ^ k - 1) ≤ 2 * k * 2 ^ k :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : 2 * k * 2 ^ k < 2 ^ (w - 1) := accAdd_round_bound_half hw
  omega

/-- Both word-fit preconditions for `accAddSpec` follow from the touch-count bound. -/
theorem accAdd_limbs_lt_word {k w T t x : ℕ} {ls : List ℕ}
    (hk : 1 ≤ k) (hw : k + Nat.log 2 (2 * k) + 2 ≤ w) (ht : t < T) (hx : x < 2 ^ k)
    (hfit : (T - 1 - t) / k + 1 < ls.length)
    (hbound : ∀ j < ls.length, ls.getD j 0 ≤ accTouches k T t j * (2 ^ k - 1)) :
    ls.getD ((T - 1 - t) / k) 0 + (x * 2 ^ ((T - 1 - t) % k)) % 2 ^ k < 2 ^ w ∧
    ls.getD ((T - 1 - t) / k + 1) 0 + (x * 2 ^ ((T - 1 - t) % k)) / 2 ^ k < 2 ^ w := by
  have hnext := accAddResult_limb_bound hk ht hx hfit hbound
  have hhalf : 2 ^ (w - 1) < 2 ^ w :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  set s := T - 1 - t
  set q := s / k
  set ls1 := ls.set q (ls.getD q 0 + (x * 2 ^ (s % k)) % 2 ^ k)
  have hlen1 : ls1.length = ls.length := List.length_set
  have hq : (accAddResult k ls x s).getD q 0 = ls.getD q 0 + (x * 2 ^ (s % k)) % 2 ^ k := by
    unfold accAddResult; dsimp only
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_set]; omega),
      List.getElem_set_ne (by omega : s / k + 1 ≠ q),
      List.getElem_set_self (by simp only [List.length_set]; omega)]
  have hq1 : (accAddResult k ls x s).getD (q + 1) 0 =
      ls.getD (q + 1) 0 + (x * 2 ^ (s % k)) / 2 ^ k := by
    unfold accAddResult; dsimp only
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_set]; exact hfit),
      List.getElem_set_self (by simp only [List.length_set]; exact hfit)]
  have hbq := hnext q (by rw [length_accAddResult]; omega)
  have hbq1 := hnext (q + 1) (by rw [length_accAddResult]; omega)
  have hltq := accTouches_limb_lt_half_word (T := T) (t := t + 1) (j := q) hk hw
  have hltq1 := accTouches_limb_lt_half_word (T := T) (t := t + 1) (j := q + 1) hk hw
  rw [hq] at hbq
  rw [hq1] at hbq1
  exact ⟨by omega, by omega⟩

/-! ### Phase transition from positive-capacity solver output -/

/-- Integral residual flow obtained from `flow` by erasing dummy loops (zero-capacity slots of
`bitScalePhaseInstance I T t g`). -/
def erasedDelta (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ) (flow : List ℕ) :
    Fin (I.m + I.m) → ℤ :=
  fun a => if (bitScalePhaseInstance I T t g).capacity a = 0 then 0 else (flow.getD a.val 0 : ℤ)

/-- Next ghost flow after augmenting `2 * g` by `erasedDelta I T t g flow`. -/
def nextGhostFlow (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ) (flow : List ℕ) :
    Fin I.m → ℤ :=
  intAugment I.m (fun e => 2 * g e) (erasedDelta I T t g flow)

/-- Updated positive accumulator for edge `e` after phase `t`. -/
def nextPosAcc (I : Circulation) (k T t : ℕ) (g : Fin I.m → ℤ) (flow : List ℕ)
    (posAcc : Fin I.m → List ℕ) (e : Fin I.m) : List ℕ :=
  accAddResult k (posAcc e) (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat (T - 1 - t)

/-- Updated negative accumulator for edge `e` after phase `t`. -/
def nextNegAcc (I : Circulation) (k T t : ℕ) (g : Fin I.m → ℤ) (flow : List ℕ)
    (negAcc : Fin I.m → List ℕ) (e : Fin I.m) : List ℕ :=
  accAddResult k (negAcc e) (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat (T - 1 - t)

theorem erasedDelta_cast_eq (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ) (flow : List ℕ) :
    (fun a => (erasedDelta I T t g flow a : ℝ)) =
      (bitScalePhaseInstance I T t g).eraseZeroFlow (fun a => ((flow.getD a.val 0 : ℕ) : ℝ)) := by
  funext a
  unfold erasedDelta Circulation.eraseZeroFlow
  split_ifs <;> simp

theorem erasedDelta_optimal {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (hsol : (bitScalePhaseInstance I T t g).positiveInstance.Optimal
      (fun a => ((flow.getD a.val 0 : ℕ) : ℝ))) :
    (bitScalePhaseInstance I T t g).Optimal (fun a => (erasedDelta I T t g flow a : ℝ)) := by
  have h := Circulation.eraseZeroFlow_optimal _ _ hsol
  convert h using 1
  exact erasedDelta_cast_eq I T t g flow

private theorem optimal_of_capacity_eq (I : Circulation) (c₁ c₂ : Fin I.m → ℕ)
    (hc : ∀ e, c₁ e = c₂ e) (f : Fin I.m → ℝ)
    (h : ({ I with capacity := c₁ } : Circulation).Optimal f) :
    ({ I with capacity := c₂ } : Circulation).Optimal f := by
  have hcap : c₁ = c₂ := funext hc
  subst hcap
  exact h

theorem nextGhostFlow_optimal {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (ht : t < T)
    (hg : (truncInstance I (T - t)).Optimal (fun e => (g e : ℝ)))
    (hsol : (bitScalePhaseInstance I T t g).positiveInstance.Optimal
      (fun a => ((flow.getD a.val 0 : ℕ) : ℝ))) :
    (truncInstance I (T - (t + 1))).Optimal (fun e => (nextGhostFlow I T t g flow e : ℝ)) := by
  have hd := erasedDelta_optimal hsol
  have hb : ∀ e, capBit I (T - (t + 1)) e ≤ 1 := fun e => by
    unfold capBit; omega
  have haug := augment_phaseInstance_optimal (truncInstance I (T - t))
    (capBit I (T - (t + 1))) hb g hg (I.m + 1) (Nat.le_succ I.m)
    (erasedDelta I T t g flow) hd
  refine optimal_of_capacity_eq I _ _ (fun e => ?_) _ haug
  have hsub : T - t - 1 = T - (t + 1) := by omega
  have hdiv := div_two_pow_sub_one (I.capacity e) (T - t) (by omega)
  rw [hsub] at hdiv
  exact hdiv.symm

private theorem trunc_feasible_bounds {I : Circulation} {s : ℕ} {g : Fin I.m → ℤ}
    (hg : (truncInstance I s).Feasible (fun e => (g e : ℝ))) (e : Fin I.m) :
    0 ≤ g e ∧ g e ≤ ((truncInstance I s).capacity e : ℤ) := by
  have h1 : 0 ≤ g e := (Int.cast_nonneg_iff (R := ℝ)).mp (hg.2 e).1
  have h2 : g e ≤ ((truncInstance I s).capacity e : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using (hg.2 e).2
  exact ⟨h1, h2⟩

theorem erasedDelta_fwd_toNat {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (hg : (truncInstance I (T - t)).Feasible (fun e => (g e : ℝ))) (e : Fin I.m) :
    (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat =
      if 0 < 2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e then
        flow.getD e.val 0
      else 0 := by
  have hcap : (bitScalePhaseInstance I T t g).capacity (Fin.castAdd I.m e) =
      min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e) (I.m + 1) := by
    have hsub : T - (t + 1) = T - 1 - t := by omega
    simpa only [bitScalePhaseInstance, cappedResidual, phaseResidual, hsub] using
      phaseInstance_capacity_forward (truncInstance I (T - t)) (capBit I (T - (t + 1)))
        g (trunc_feasible_bounds hg) (I.m + 1) e
  unfold erasedDelta
  rw [hcap]
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

theorem erasedDelta_rev_toNat {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (hg : (truncInstance I (T - t)).Feasible (fun e => (g e : ℝ))) (e : Fin I.m) :
    (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat =
      if 0 < cappedFlow g (I.m + 1) e then
        flow.getD (I.m + e.val) 0
      else 0 := by
  have hcap : (bitScalePhaseInstance I T t g).capacity (Fin.natAdd I.m e) =
      min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) := by
    simpa only [bitScalePhaseInstance, cappedFlow] using
      phaseInstance_capacity_reverse (truncInstance I (T - t)) (capBit I (T - (t + 1)))
        g (fun e' => (trunc_feasible_bounds hg e').1) (I.m + 1) e
  unfold erasedDelta
  rw [hcap]
  simp only [Fin.val_natAdd]
  split_ifs <;> omega

theorem erasedDelta_bounds {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (hg : (truncInstance I (T - t)).Feasible (fun e => (g e : ℝ)))
    (hsol : (bitScalePhaseInstance I T t g).positiveInstance.Optimal
      (fun a => ((flow.getD a.val 0 : ℕ) : ℝ)))
    (e : Fin I.m) :
    (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat ≤
        min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e) (I.m + 1) ∧
    (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat ≤
        min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) := by
  have hfeas := (erasedDelta_optimal hsol).1
  have hsub : T - (t + 1) = T - 1 - t := by omega
  have hf := phaseInstance_delta_bounds _ _ _ _ _ hfeas (Fin.castAdd I.m e)
  have hr := phaseInstance_delta_bounds _ _ _ _ _ hfeas (Fin.natAdd I.m e)
  have hcapf : (bitScalePhaseInstance I T t g).capacity (Fin.castAdd I.m e) =
      min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e) (I.m + 1) := by
    simpa only [bitScalePhaseInstance, cappedResidual, phaseResidual, hsub] using
      phaseInstance_capacity_forward (truncInstance I (T - t)) (capBit I (T - (t + 1)))
        g (trunc_feasible_bounds hg) (I.m + 1) e
  have hcapr : (bitScalePhaseInstance I T t g).capacity (Fin.natAdd I.m e) =
      min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) := by
    simpa only [bitScalePhaseInstance, cappedFlow] using
      phaseInstance_capacity_reverse (truncInstance I (T - t)) (capBit I (T - (t + 1)))
        g (fun e' => (trunc_feasible_bounds hg e').1) (I.m + 1) e
  exact ⟨hcapf ▸ hf.2, hcapr ▸ hr.2⟩

theorem nextCappedResidual_eq {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (ht : t < T)
    (hg : (truncInstance I (T - t)).Feasible (fun e => (g e : ℝ)))
    (hsol : (bitScalePhaseInstance I T t g).positiveInstance.Optimal
      (fun a => ((flow.getD a.val 0 : ℕ) : ℝ)))
    (e : Fin I.m) :
    cappedResidual I T (t + 1) (nextGhostFlow I T t g flow) (I.m + 1) e =
      min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e +
        (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat -
        (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat) (I.m + 1) := by
  have hfeas := (erasedDelta_optimal hsol).1
  have hsub : T - (t + 1) = T - 1 - t := by omega
  have hcap_e : (doubled (truncInstance I (T - t)) (capBit I (T - (t + 1)))).capacity e =
      (truncInstance I (T - (t + 1))).capacity e := by
    have hs : T - t - 1 = T - (t + 1) := by omega
    have hdiv := div_two_pow_sub_one (I.capacity e) (T - t) (by omega)
    rw [hs] at hdiv
    exact hdiv.symm
  have hrec := cappedResidual_after_augment (truncInstance I (T - t))
    (capBit I (T - (t + 1))) g (trunc_feasible_bounds hg) (I.m + 1)
    (erasedDelta I T t g flow) hfeas e
  rw [hcap_e] at hrec
  simpa only [cappedResidual, phaseResidual, nextGhostFlow, hsub] using hrec

theorem nextCappedFlow_eq {I : Circulation} {T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    (hg : (truncInstance I (T - t)).Feasible (fun e => (g e : ℝ)))
    (hsol : (bitScalePhaseInstance I T t g).positiveInstance.Optimal
      (fun a => ((flow.getD a.val 0 : ℕ) : ℝ)))
    (e : Fin I.m) :
    cappedFlow (nextGhostFlow I T t g flow) (I.m + 1) e =
      min (2 * cappedFlow g (I.m + 1) e +
        (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat -
        (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat) (I.m + 1) := by
  have hfeas := (erasedDelta_optimal hsol).1
  simpa only [cappedFlow, nextGhostFlow] using
    cappedFlow_after_augment (truncInstance I (T - t))
      (capBit I (T - (t + 1))) g (trunc_feasible_bounds hg) (I.m + 1)
      (erasedDelta I T t g flow) hfeas e

theorem nextAcc_diff_eq {I : Circulation} {k T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    {posAcc negAcc : Fin I.m → List ℕ} {e : Fin I.m}
    (ht : t < T)
    (hfitPos : (T - 1 - t) / k + 1 < (posAcc e).length)
    (hfitNeg : (T - 1 - t) / k + 1 < (negAcc e).length)
    (hdiff : ((Nat.ofDigits (2 ^ k) (posAcc e) : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ k) (negAcc e) : ℕ) : ℤ) = g e * (2 : ℤ) ^ (T - t)) :
    ((Nat.ofDigits (2 ^ k) (nextPosAcc I k T t g flow posAcc e) : ℕ) : ℤ) -
      ((Nat.ofDigits (2 ^ k) (nextNegAcc I k T t g flow negAcc e) : ℕ) : ℤ) =
        nextGhostFlow I T t g flow e * (2 : ℤ) ^ (T - (t + 1)) := by
  have hp := accAdd_ofDigits (k := k) hfitPos
    (x := (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat)
  have hn := accAdd_ofDigits (k := k) hfitNeg
    (x := (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat)
  have hdf_nonneg : 0 ≤ erasedDelta I T t g flow (Fin.castAdd I.m e) := by
    unfold erasedDelta; split_ifs <;> omega
  have hdr_nonneg : 0 ≤ erasedDelta I T t g flow (Fin.natAdd I.m e) := by
    unfold erasedDelta; split_ifs <;> omega
  have hpow : (2 : ℤ) ^ (T - t) = 2 * (2 : ℤ) ^ (T - (t + 1)) := by
    rw [← pow_succ', show T - (t + 1) + 1 = T - t by omega]
  have hsub : T - 1 - t = T - (t + 1) := by omega
  unfold nextPosAcc nextNegAcc nextGhostFlow intAugment intProject
  rw [hp, hn, hsub]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Int.toNat_of_nonneg hdf_nonneg, Int.toNat_of_nonneg hdr_nonneg]
  rw [hpow] at hdiff
  linear_combination hdiff

theorem nextAcc_val_le {I : Circulation} {k T t : ℕ} {g : Fin I.m → ℤ} {flow : List ℕ}
    {acc : Fin I.m → List ℕ} {a : Fin (I.m + I.m)} {e : Fin I.m}
    (ht : t < T) (hfit : (T - 1 - t) / k + 1 < (acc e).length)
    (hda : (erasedDelta I T t g flow a).toNat ≤ I.m + 1)
    (hprev : Nat.ofDigits (2 ^ k) (acc e) ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - t))) :
    Nat.ofDigits (2 ^ k) (accAddResult k (acc e) (erasedDelta I T t g flow a).toNat (T - 1 - t)) ≤
      (I.m + 1) * (2 ^ T - 2 ^ (T - (t + 1))) := by
  rw [accAdd_ofDigits (k := k) hfit]
  have hsub : T - 1 - t = T - (t + 1) := by omega
  rw [hsub]
  have hpow : 2 ^ (T - t) = 2 * 2 ^ (T - (t + 1)) := by
    rw [← pow_succ', show T - (t + 1) + 1 = T - t by omega]
  have hleT : 2 ^ (T - t) ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : (erasedDelta I T t g flow a).toNat * 2 ^ (T - (t + 1)) ≤
      (I.m + 1) * 2 ^ (T - (t + 1)) := Nat.mul_le_mul_right _ hda
  have hge : 2 ^ (T - (t + 1)) ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiff : (2 ^ T - 2 ^ (T - t)) + 2 ^ (T - (t + 1)) = 2 ^ T - 2 ^ (T - (t + 1)) := by
    omega
  calc Nat.ofDigits (2 ^ k) (acc e) + (erasedDelta I T t g flow a).toNat * 2 ^ (T - (t + 1))
      ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - t)) + (I.m + 1) * 2 ^ (T - (t + 1)) := Nat.add_le_add hprev hmul
    _ = (I.m + 1) * ((2 ^ T - 2 ^ (T - t)) + 2 ^ (T - (t + 1))) := (Nat.mul_add _ _ _).symm
    _ = (I.m + 1) * (2 ^ T - 2 ^ (T - (t + 1))) := by rw [hdiff]

end MinCostFlow.NarrowProg
