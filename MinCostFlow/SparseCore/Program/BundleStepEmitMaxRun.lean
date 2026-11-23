module

public import MinCostFlow.SparseCore.Program.BundleStepEmitRunDecomp

/-!
# Phase 3 linear max-run scan verification (`BundleStepEmitMaxRun`)

Verifies `bundleStepEmitMaxRunStmt` on any non-empty sorted packed-key array `vRunsPacked eCap vruns`,
proving it outputs `(winStart, winEnd, winLen)` matching `maxRunIdx vruns` in `≤ 80 * len + 35`
steps with zero heap writes.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-! ## 1. Verification of `bundleStepEmitMaxRunStmt` -/

private lemma maxRun_inner_runs {w eCap arr len vCur : ℕ} {pProg : Program} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (harr_w : arr + len < 2 ^ w)
    (hv_w : vCur < 2 ^ w) :
    ∀ (d idx : ℕ) (st : State),
      idx + d ≤ len →
      (∀ t < d, st.mem (arr + (idx + t)) / (2 * eCap) = vCur ∧ st.mem (arr + (idx + t)) < 2 ^ w) →
      (idx + d < len → st.mem (arr + (idx + d)) / (2 * eCap) ≠ vCur ∧ st.mem (arr + (idx + d)) < 2 ^ w) →
      st.regs 6 = 2 * eCap → st.regs 27 = arr → st.regs 30 = len →
      st.regs 34 = idx → st.regs 36 = vCur → st.regs 37 = 1 →
      ∃ st1 c1,
        Runs w pProg ω
          (.loop (.reg 37)
            (.cond (.bin .lt (.reg 34) (.reg 30))
              (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
                (.assign 34 (.bin .add (.reg 34) (.const 1)))
                (.assign 37 (.const 0)))
              (.assign 37 (.const 0))))
          st .normal st1 c1 ∧
        st1.mem = st.mem ∧
        (∀ r ≤ 36, r ≠ 34 → st1.regs r = st.regs r) ∧
        st1.regs 34 = idx + d ∧
        c1 ≤ 20 * d + 22 := by
  intro d
  induction d with
  | zero =>
    intro idx st hle _ hstop hr6 hr27 hr30 hr34 hr36 hr37
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    by_cases hlt : idx < len
    · obtain ⟨hne, hmem_w⟩ := hstop (by omega)
      simp only [Nat.add_zero] at hne hmem_w
      set st1 : State := { st with regs := Function.update st.regs 37 0 }
      have ha37 : Runs w pProg ω (.assign 37 (.const 0)) st .normal st1 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      have hdiv_w : st.mem (arr + idx) / (2 * eCap) < 2 ^ w :=
        lt_of_le_of_lt (Nat.div_le_self _ _) hmem_w
      have hc2 : Runs w pProg ω
          (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
            (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
          st .normal st1 11 :=
        runs_cond_iff.mpr ⟨0, 2, by
          simp [Expr.eval, BinOp.eval, hr27, hr34, hr6, hr36, show arr + idx < 2 ^ w by omega,
            hdiv_w, hne, h0_w],
          by simpa using ha37, by simp [Expr.size]⟩
      have hc1 : Runs w pProg ω
          (.cond (.bin .lt (.reg 34) (.reg 30))
            (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
              (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
            (.assign 37 (.const 0))) st .normal st1 15 :=
        runs_cond_iff.mpr ⟨1, 11, by simp [Expr.eval, BinOp.eval, hr34, hr30, hlt, h1_w],
          by simpa using hc2, by simp [Expr.size]⟩
      have hexit : Runs w pProg ω
          (.loop (.reg 37)
            (.cond (.bin .lt (.reg 34) (.reg 30))
              (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
                (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
              (.assign 37 (.const 0)))) st1 .normal st1 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, st1], rfl, rfl, rfl⟩)
      have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, 15, 2, by simp [Expr.eval, hr37],
        by decide, hc1, hexit, rfl⟩))
      exact ⟨st1, _, hloop, rfl, fun r hr _ => by simp [st1, show r ≠ 37 by omega],
        by simp [st1, hr34], by simp [Expr.size]⟩
    · set st1 : State := { st with regs := Function.update st.regs 37 0 }
      have ha37 : Runs w pProg ω (.assign 37 (.const 0)) st .normal st1 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      have hc1 : Runs w pProg ω
          (.cond (.bin .lt (.reg 34) (.reg 30))
            (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
              (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
            (.assign 37 (.const 0))) st .normal st1 6 :=
        runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, hr34, hr30, hlt, h0_w],
          by simpa using ha37, by simp [Expr.size]⟩
      have hexit : Runs w pProg ω
          (.loop (.reg 37)
            (.cond (.bin .lt (.reg 34) (.reg 30))
              (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
                (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
              (.assign 37 (.const 0)))) st1 .normal st1 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, st1], rfl, rfl, rfl⟩)
      have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, 6, 2, by simp [Expr.eval, hr37],
        by decide, hc1, hexit, rfl⟩))
      exact ⟨st1, _, hloop, rfl, fun r hr _ => by simp [st1, show r ≠ 37 by omega],
        by simp [st1, hr34], by simp [Expr.size]⟩
  | succ d ih =>
    intro idx st hle hsame hstop hr6 hr27 hr30 hr34 hr36 hr37
    have h1_w : 1 < 2 ^ w := by omega
    have hlt : idx < len := by omega
    obtain ⟨hdiv0, hmem_w⟩ := hsame 0 (by omega)
    simp only [Nat.add_zero] at hdiv0 hmem_w
    set stA : State := { st with regs := Function.update st.regs 34 (idx + 1) }
    have ha34 : Runs w pProg ω (.assign 34 (.bin .add (.reg 34) (.const 1))) st .normal stA 4 :=
      runs_assign_iff.mpr ⟨idx + 1, by simp [Expr.eval, BinOp.eval, hr34, h1_w, show idx + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hc2 : Runs w pProg ω
        (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
          (.assign 34 (.bin .add (.reg 34) (.const 1))) (.assign 37 (.const 0)))
        st .normal stA 13 :=
      runs_cond_iff.mpr ⟨1, 4, by
        simp [Expr.eval, BinOp.eval, hr27, hr34, hr6, hr36, show arr + idx < 2 ^ w by omega,
          hdiv0, hv_w, h1_w],
        by simpa using ha34, by simp [Expr.size]⟩
    have hc1 : Runs w pProg ω
        (.cond (.bin .lt (.reg 34) (.reg 30)) _ (.assign 37 (.const 0))) st .normal stA 17 :=
      runs_cond_iff.mpr ⟨1, 13, by simp [Expr.eval, BinOp.eval, hr34, hr30, hlt, h1_w],
        by simpa using hc2, by simp [Expr.size]⟩
    obtain ⟨st1, c1, hrest, hmem1, hregs1, hr34_1, hc1_le⟩ :=
      ih (idx + 1) stA (by omega)
        (fun t ht => by simpa [stA, Nat.add_assoc, show 1 + t = t + 1 by omega] using hsame (t + 1) (by omega))
        (fun hlt' => by simpa [stA, Nat.add_assoc, show 1 + d = d + 1 by omega] using hstop (by omega))
        (by simp [stA, hr6]) (by simp [stA, hr27]) (by simp [stA, hr30])
        (by simp [stA]) (by simp [stA, hr36]) (by simp [stA, hr37])
    have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stA, 17, c1, by simp [Expr.eval, hr37],
      by decide, hc1, hrest, rfl⟩))
    exact ⟨st1, _, hloop, hmem1, fun r hr h34 => by rw [hregs1 r hr h34]; simp [stA, h34],
      by omega, by simp [Expr.size]; omega⟩

lemma bundleStepEmitMaxRun_runs {w eCap vCap arr : ℕ} {pProg : Program} {ω : ℕ → Bool}
    {vruns : List (ℕ × List End)} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (harr_w : arr + vRunsEndsLen vruns < 2 ^ w)
    (hvr_pos : ∀ vr ∈ vruns, vr.1 < vCap ∧ 0 < vr.2.length)
    (hvr_pw : (vruns.map Prod.fst).Pairwise (· < ·))
    (hvr_keys : ∀ vr ∈ vruns, ∀ x ∈ vr.2, endKey x < 2 * eCap)
    (hpack : ListAt st₀.mem arr (vRunsPacked eCap vruns))
    (hr6 : st₀.regs 6 = 2 * eCap) (hr27 : st₀.regs 27 = arr)
    (hr30 : st₀.regs 30 = vRunsEndsLen vruns) :
    let bestIdx := maxRunIdx vruns
    ∃ stEnd cEnd,
      Runs w pProg ω bundleStepEmitMaxRunStmt st₀ .normal stEnd cEnd ∧
      stEnd.mem = st₀.mem ∧
      (∀ r ≤ 30, stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 31 = vRunsEndsLen (vruns.take bestIdx) ∧
      stEnd.regs 32 = vRunsEndsLen (vruns.take (bestIdx + 1)) ∧
      stEnd.regs 33 = (vruns.getD bestIdx (0, [])).2.length ∧
      cEnd ≤ 80 * vRunsEndsLen vruns + 35 := by
  intro bestIdx
  set len := vRunsEndsLen vruns
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hpk_elt_w : ∀ vr ∈ vruns, ∀ x ∈ vr.2, packEndKey eCap vr.1 (endKey x) < 2 ^ w := fun vr hvr x hx => by
    have hv := (hvr_pos vr hvr).1
    have hk := hvr_keys vr hvr x hx
    have hmul := Nat.mul_le_mul_right (2 * eCap) (show vr.1 + 1 ≤ vCap by omega)
    unfold packEndKey; rw [Nat.add_mul, Nat.one_mul] at hmul; omega
  have hv_w : ∀ vr ∈ vruns, vr.1 < 2 ^ w := fun vr hvr => by
    have hv := (hvr_pos vr hvr).1
    -- The run `vr` has an end, and the key of that end is below `2 * eCap`.
    have h2e_pos : 0 < 2 * eCap := Nat.lt_of_le_of_lt (Nat.zero_le _)
      (hvr_keys vr hvr _ (List.getElem_mem (hvr_pos vr hvr).2))
    have h1 : vr.1 ≤ vr.1 * (2 * eCap) := Nat.le_mul_of_pos_right _ h2e_pos
    have h2 : vr.1 * (2 * eCap) ≤ vCap * (2 * eCap) := Nat.mul_le_mul_right _ (Nat.le_of_lt hv)
    omega
  -- Header: r31 := 0, r32 := 0, r33 := 0, r34 := 0
  let r31 := Function.update st₀.regs 31 0
  let r32 := Function.update r31 32 0
  let r33 := Function.update r32 33 0
  let r34 := Function.update r33 34 0
  let stH : State := { st₀ with regs := r34 }
  have ha31 : Runs w pProg ω (.assign 31 (.const 0)) st₀ .normal { st₀ with regs := r31 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha32 : Runs w pProg ω (.assign 32 (.const 0)) { st₀ with regs := r31 } .normal { st₀ with regs := r32 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha33 : Runs w pProg ω (.assign 33 (.const 0)) { st₀ with regs := r32 } .normal { st₀ with regs := r33 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha34 : Runs w pProg ω (.assign 34 (.const 0)) { st₀ with regs := r33 } .normal stH 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  -- Outer loop by induction on `d = vruns.length - k`
  let stepFn := fun (best : ℕ × ℕ) (p : (ℕ × List End) × ℕ) =>
    if best.2 < p.1.2.length then (p.2, p.1.2.length) else best
  have hloop : ∀ (d k : ℕ) (hk : k + d = vruns.length) (bIdx bLen : ℕ) (st : State),
      st.mem = st₀.mem →
      (∀ r ≤ 30, st.regs r = st₀.regs r) →
      st.regs 31 = (if bLen = 0 then 0 else vRunsEndsLen (vruns.take bIdx)) →
      st.regs 32 = (if bLen = 0 then 0 else vRunsEndsLen (vruns.take (bIdx + 1))) →
      st.regs 33 = bLen →
      st.regs 34 = vRunsEndsLen (vruns.take k) →
      ((bIdx, bLen) = (vruns.take k).zipIdx.foldl stepFn (0, 0)) →
      (bLen = 0 → k = 0) →
      ∃ stEnd cEnd,
        Runs w pProg ω
          (.loop (.bin .lt (.reg 34) (.reg 30))
            (.assign 35 (.reg 34) ;;
             .assign 36 (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) ;;
             .assign 37 (.const 1) ;;
             .loop (.reg 37)
               (.cond (.bin .lt (.reg 34) (.reg 30))
                 (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
                   (.assign 34 (.bin .add (.reg 34) (.const 1)))
                   (.assign 37 (.const 0)))
                 (.assign 37 (.const 0))) ;;
             .assign 38 (.bin .sub (.reg 34) (.reg 35)) ;;
             .cond (.bin .lt (.reg 33) (.reg 38))
               (.assign 31 (.reg 35) ;; .assign 32 (.reg 34) ;; .assign 33 (.reg 38))
               .nop))
          st .normal stEnd cEnd ∧
        stEnd.mem = st₀.mem ∧
        (∀ r ≤ 30, stEnd.regs r = st₀.regs r) ∧
        stEnd.regs 31 = vRunsEndsLen (vruns.take bestIdx) ∧
        stEnd.regs 32 = vRunsEndsLen (vruns.take (bestIdx + 1)) ∧
        stEnd.regs 33 = (vruns.getD bestIdx (0, [])).2.length ∧
        cEnd ≤ 80 * vRunsEndsLen (vruns.drop k) + 6 := by
    intro d
    induction d with
    | zero =>
      intro k hk bIdx bLen st hmem hregs hr31 hr32 hr33 hr34 hfold hb0
      have hkl : k = vruns.length := by omega
      subst hkl
      rw [List.take_length] at hr34 hfold
      have hbest_and_len : bIdx = bestIdx ∧ bLen = (vruns.getD bestIdx (0, [])).2.length := by
        cases hv : vruns with
        | nil =>
          rw [hv] at hfold; simp [List.zipIdx] at hfold
          exact ⟨by simp [bestIdx, hv, maxRunIdx, hfold.1], by simp [hfold.2]⟩
        | cons vr0 tl =>
          have hne_vr : vruns ≠ [] := by rw [hv]; simp
          have hne0 : bLen ≠ 0 := fun h0 => by have := hb0 h0; rw [hv] at this; simp at this
          have hinv : ∀ (l : List (ℕ × List End)) (base : ℕ) (acc : ℕ × ℕ),
              (acc.2 = 0 ∨ ∃ hlt : acc.1 < vruns.length, (vruns[acc.1]'hlt).2.length = acc.2) →
              (∀ j (hj : j < base), ∃ hlt : j < vruns.length, (vruns[j]'hlt).2.length ≤ acc.2) →
              (∀ j (hj : j < acc.1), j < base → ∃ hlt : j < vruns.length, (vruns[j]'hlt).2.length < acc.2) →
              (acc.2 = 0 → base = 0) →
              (acc.2 ≠ 0 → acc.1 < base) →
              (∀ i (hi : i < l.length), ∃ hlt : base + i < vruns.length, l[i]'hi = vruns[base + i]'hlt) →
              let res := (l.zipIdx base).foldl stepFn acc
              (res.2 = 0 ∨ ∃ hlt : res.1 < vruns.length, (vruns[res.1]'hlt).2.length = res.2) ∧
              (∀ j (hj : j < base + l.length), ∃ hlt : j < vruns.length, (vruns[j]'hlt).2.length ≤ res.2) ∧
              (∀ j (hj : j < res.1), j < base + l.length → ∃ hlt : j < vruns.length, (vruns[j]'hlt).2.length < res.2) := by
            intro l; induction l with
            | nil => intro base acc h1 h2 h3 _ _ _; exact ⟨h1, by simpa using h2, by simpa using h3⟩
            | cons a rest ihr =>
              intro base acc h1 h2 h3 h4 h5 hget
              simp only [List.zipIdx_cons, List.foldl_cons]
              obtain ⟨hlt0, heq0⟩ := hget 0 (by simp)
              simp only [Nat.add_zero, List.getElem_cons_zero] at hlt0 heq0
              have ha_mem : a ∈ vruns := by rw [heq0]; exact List.getElem_mem hlt0
              have ha_pos : 0 < a.2.length := (hvr_pos a ha_mem).2
              have ha_len : (vruns[base]'hlt0).2.length = a.2.length := congrArg (fun p : ℕ × List End => p.2.length) heq0.symm
              have hlen_eq : base + 1 + rest.length = base + (a :: rest).length := by simp; omega
              have hres := ihr (base + 1) (stepFn acc (a, base))
                (by dsimp only [stepFn]; split_ifs
                    · right; exact ⟨hlt0, ha_len⟩
                    · exact h1)
                (fun j hj => by
                  dsimp only [stepFn]; split_ifs with hlt
                  · by_cases hjb : j < base
                    · obtain ⟨hjl, hle⟩ := h2 j hjb; exact ⟨hjl, by omega⟩
                    · have : j = base := by omega
                      subst this; exact ⟨hlt0, by omega⟩
                  · by_cases hjb : j < base
                    · exact h2 j hjb
                    · have : j = base := by omega
                      subst this; exact ⟨hlt0, by omega⟩)
                (fun j hj1 hj2 => by
                  dsimp only [stepFn] at hj1 ⊢; split_ifs at hj1 ⊢ with hlt
                  · obtain ⟨hjl, hle⟩ := h2 j hj1; exact ⟨hjl, by omega⟩
                  · have hne_acc : acc.2 ≠ 0 := fun h0 => by omega
                    have hlt_b : j < base := lt_trans hj1 (h5 hne_acc)
                    exact h3 j hj1 hlt_b)
                (fun h0 => by
                  dsimp only [stepFn] at h0; split_ifs at h0 with hlt <;> omega)
                (fun _ => by
                  dsimp only [stepFn]; split_ifs with hlt
                  · omega
                  · have hne_acc : acc.2 ≠ 0 := fun h0 => by omega
                    have := h5 hne_acc; omega)
                (fun i hi => by
                  obtain ⟨h1', heq1⟩ := hget (i + 1) (by simp; omega)
                  exact ⟨by omega, by simpa [show base + (i + 1) = base + 1 + i by omega] using heq1⟩)
              rwa [hlen_eq] at hres
          have ⟨h1, h2, h3⟩ := hinv vruns 0 (0, 0) (Or.inl rfl) (fun _ h => by omega) (fun _ h => by omega)
            (fun _ => rfl) (fun h => absurd rfl h) (fun i hi => ⟨by omega, by simp⟩)
          rw [← hfold] at h1 h2 h3
          rcases h1 with h0 | ⟨hb_lt, hb_len⟩
          · exact absurd h0 hne0
          · have hspec := maxRunIdx_spec hne_vr
            have hbest_lt := maxRunIdx_lt hne_vr
            have hbi_eq : bIdx = bestIdx := by
              dsimp only [bestIdx] at *
              rcases lt_trichotomy bIdx (maxRunIdx vruns) with hlt | heq | hgt
              · have hlt1 := hspec.2 bIdx hlt
                obtain ⟨_, hle2⟩ := h2 (maxRunIdx vruns) (by omega)
                omega
              · exact heq
              · obtain ⟨_, hlt2⟩ := h3 (maxRunIdx vruns) hgt (by omega)
                have hle1 := hspec.1 bIdx hb_lt
                omega
            have hget_b : (vruns.getD bIdx (0, [])).2.length = bLen := by
              rw [List.getD_eq_getElem _ _ hb_lt, hb_len]
            exact ⟨hbi_eq, by rw [← hv, ← hbi_eq, hget_b]⟩
      obtain ⟨hbest_eq, hblen_eq⟩ := hbest_and_len
      have hcond0 : Expr.eval w st (.bin .lt (.reg 34) (.reg 30)) = some 0 := by
        simp [Expr.eval, BinOp.eval, hr34, hregs 30 (le_refl _), hr30, len, h0_w]
      refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
        hmem, hregs, ?_, ?_, by rw [hr33, hblen_eq], by simp [List.drop_of_length_le]⟩
      · rw [hr31]; split_ifs with h0
        · have hk0 := hb0 h0
          have hnil : vruns = [] := List.eq_nil_of_length_eq_zero hk0
          simp [hnil, vRunsEndsLen]
        · rw [hbest_eq]
      · rw [hr32]; split_ifs with h0
        · have hk0 := hb0 h0
          have hnil : vruns = [] := List.eq_nil_of_length_eq_zero hk0
          simp [hnil, vRunsEndsLen]
        · rw [hbest_eq]
    | succ d ih =>
      intro k hk bIdx bLen st hmem hregs hr31 hr32 hr33 hr34 hfold hb0
      have hk_lt : k < vruns.length := by omega
      set vr := vruns[k]'hk_lt
      set idx0 := vRunsEndsLen (vruns.take k)
      set curLen := vr.2.length
      have hvr_mem : vr ∈ vruns := List.getElem_mem hk_lt
      have hcur_pos : 0 < curLen := (hvr_pos vr hvr_mem).2
      have htake_succ : vruns.take (k + 1) = vruns.take k ++ [vr] := List.take_succ_eq_append_getElem hk_lt
      have hdrop_cons : vruns.drop k = vr :: vruns.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
      have hlen_split : idx0 + curLen + vRunsEndsLen (vruns.drop (k + 1)) = len := by
        have h1 := congrArg vRunsEndsLen (List.take_append_drop k vruns)
        rw [vRunsEndsLen_append, hdrop_cons] at h1
        simp only [vRunsEndsLen, List.map_cons, List.sum_cons] at h1
        dsimp only [idx0, curLen, len, vRunsEndsLen] at h1 ⊢
        omega
      have hidx_lt : idx0 < len := by omega
      have hpack_split : vRunsPacked eCap vruns =
          vRunsPacked eCap (vruns.take k) ++ (vr.2.map fun x => packEndKey eCap vr.1 (endKey x)) ++
          vRunsPacked eCap (vruns.drop (k + 1)) := by
        conv_lhs => rw [← List.take_append_drop k vruns, hdrop_cons]
        simp [vRunsPacked, List.append_assoc]
      have hsame : ∀ t < curLen, st.mem (arr + (idx0 + t)) / (2 * eCap) = vr.1 ∧
          st.mem (arr + (idx0 + t)) < 2 ^ w := by
        intro t ht
        have hlt_pk : idx0 + t < (vRunsPacked eCap vruns).length := by
          rw [vRunsPacked_length]; omega
        rw [hmem, hpack (idx0 + t) hlt_pk]
        have hget : (vRunsPacked eCap vruns)[idx0 + t]'hlt_pk =
            packEndKey eCap vr.1 (endKey (vr.2[t]'ht)) := by
          simp only [hpack_split]
          rw [List.getElem_append_left (by simp [vRunsPacked_length, idx0]; omega),
            List.getElem_append_right (by simp [vRunsPacked_length, idx0])]
          simp [vRunsPacked_length, idx0]
        rw [hget]
        exact ⟨packEndKey_div (hvr_keys vr hvr_mem _ (List.getElem_mem ht)),
          hpk_elt_w vr hvr_mem _ (List.getElem_mem ht)⟩
      have hstop : idx0 + curLen < len →
          st.mem (arr + (idx0 + curLen)) / (2 * eCap) ≠ vr.1 ∧ st.mem (arr + (idx0 + curLen)) < 2 ^ w := by
        intro hlt_end
        have hk1_lt : k + 1 < vruns.length := by
          by_contra hge
          have hdrop0 : vruns.drop (k + 1) = [] := List.drop_of_length_le (by omega)
          rw [hdrop0] at hlen_split; simp [vRunsEndsLen] at hlen_split; omega
        set vr' := vruns[k + 1]'hk1_lt
        have hvr'_mem : vr' ∈ vruns := List.getElem_mem hk1_lt
        have hvr'_pos : 0 < vr'.2.length := (hvr_pos vr' hvr'_mem).2
        have hlt_pk : idx0 + curLen < (vRunsPacked eCap vruns).length := by
          rw [vRunsPacked_length]; omega
        rw [hmem, hpack (idx0 + curLen) hlt_pk]
        have hget : (vRunsPacked eCap vruns)[idx0 + curLen]'hlt_pk =
            packEndKey eCap vr'.1 (endKey (vr'.2[0]'hvr'_pos)) := by
          have hps : vRunsPacked eCap vruns =
              (vRunsPacked eCap (vruns.take k) ++ (vr.2.map fun x => packEndKey eCap vr.1 (endKey x))) ++
              ((vr'.2.map fun x => packEndKey eCap vr'.1 (endKey x)) ++ vRunsPacked eCap (vruns.drop (k + 2))) := by
            have hd1 : vruns.drop (k + 1) = vr' :: vruns.drop (k + 2) := by
              rw [List.drop_eq_getElem_cons hk1_lt, show k + 1 + 1 = k + 2 by omega]
            rw [hpack_split, hd1]; simp [vRunsPacked]
          have hlen1 : (vRunsPacked eCap (vruns.take k) ++ (vr.2.map fun x => packEndKey eCap vr.1 (endKey x))).length =
              idx0 + curLen := by
            simp [vRunsPacked_length, idx0, curLen]
          simp only [hps]
          rw [List.getElem_append_right (by omega), List.getElem_append_left (by simp [hlen1]; exact hvr'_pos)]
          simp [hlen1]
        rw [hget]
        have hvlt : vr.1 < vr'.1 := by
          have := List.pairwise_iff_getElem.mp hvr_pw k (k + 1) (by simp; omega) (by simp; omega) (by omega)
          simpa using this
        refine ⟨?_, hpk_elt_w vr' hvr'_mem _ (List.getElem_mem hvr'_pos)⟩
        rw [packEndKey_div (hvr_keys vr' hvr'_mem _ (List.getElem_mem hvr'_pos))]; omega
      -- Body: r35 := idx0, r36 := vr.1, r37 := 1, inner loop, r38 := curLen, cond update
      let r35 := Function.update st.regs 35 idx0
      let r36 := Function.update r35 36 vr.1
      let r37 := Function.update r36 37 1
      let stA : State := { st with regs := r37 }
      have ha35 : Runs w pProg ω (.assign 35 (.reg 34)) st .normal { st with regs := r35 } 2 :=
        runs_assign_iff.mpr ⟨idx0, by simp [Expr.eval, hr34], rfl, rfl, rfl⟩
      have ha36 : Runs w pProg ω (.assign 36 (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)))
          { st with regs := r35 } .normal { st with regs := r36 } 7 :=
        runs_assign_iff.mpr ⟨vr.1, by
          have hs0 := hsame 0 hcur_pos; simp only [Nat.add_zero] at hs0
          simp [Expr.eval, BinOp.eval, r35, hregs 27 (by decide), hr27, hr34, hregs 6 (by decide), hr6,
            show arr + idx0 < 2 ^ w by omega, hs0.1, hv_w vr hvr_mem],
          rfl, rfl, by simp [Expr.size]⟩
      have ha37 : Runs w pProg ω (.assign 37 (.const 1)) { st with regs := r36 } .normal stA 2 :=
        runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
      obtain ⟨stB, cIn, hrunIn, hmemB, hregsB, hr34B, hcIn⟩ :=
        maxRun_inner_runs (arr := arr) (len := len) (vCur := vr.1) hw16 harr_w (hv_w vr hvr_mem)
          curLen idx0 stA (by omega) hsame hstop
          (by simp [stA, r37, r36, r35, hregs 6 (by decide), hr6])
          (by simp [stA, r37, r36, r35, hregs 27 (by decide), hr27])
          (by simp [stA, r37, r36, r35, hregs 30 (le_refl _), hr30])
          (by simp [stA, r37, r36, r35, hr34])
          (by simp [stA, r37, r36]) (by simp [stA, r37])
      let r38 := Function.update stB.regs 38 curLen
      let stC : State := { stB with regs := r38 }
      have hr35B : stB.regs 35 = idx0 := (hregsB 35 (by decide) (by decide)).trans (by simp [stA, r37, r36, r35])
      have ha38 : Runs w pProg ω (.assign 38 (.bin .sub (.reg 34) (.reg 35))) stB .normal stC 4 :=
        runs_assign_iff.mpr ⟨curLen, by
          simp [Expr.eval, BinOp.eval, hr34B, hr35B, show curLen < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hr33C : stC.regs 33 = bLen := by
        simp [stC, r38, hregsB 33 (by decide) (by decide), stA, r37, r36, r35, hr33]
      have hr38C : stC.regs 38 = curLen := by simp [stC, r38]
      have hidx_succ : vRunsEndsLen (vruns.take (k + 1)) = idx0 + curLen := by
        rw [htake_succ, vRunsEndsLen_append]; simp [vRunsEndsLen, idx0, curLen]
      have hfold_succ : (vruns.take (k + 1)).zipIdx.foldl stepFn (0, 0) =
          stepFn (bIdx, bLen) (vr, k) := by
        rw [htake_succ, List.zipIdx_append, List.foldl_append, ← hfold]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ vruns.length)]
      by_cases hlt_b : bLen < curLen
      · let r31' := Function.update stC.regs 31 idx0
        let r32' := Function.update r31' 32 (idx0 + curLen)
        let r33' := Function.update r32' 33 curLen
        let stD : State := { stC with regs := r33' }
        have hu1 : Runs w pProg ω (.assign 31 (.reg 35)) stC .normal { stC with regs := r31' } 2 :=
          runs_assign_iff.mpr ⟨idx0, by simp [Expr.eval, stC, r38, hr35B], rfl, rfl, rfl⟩
        have hu2 : Runs w pProg ω (.assign 32 (.reg 34)) { stC with regs := r31' } .normal { stC with regs := r32' } 2 :=
          runs_assign_iff.mpr ⟨idx0 + curLen, by simp [Expr.eval, r31', stC, r38, hr34B], rfl, rfl, rfl⟩
        have hu3 : Runs w pProg ω (.assign 33 (.reg 38)) { stC with regs := r32' } .normal stD 2 :=
          runs_assign_iff.mpr ⟨curLen, by simp [Expr.eval, r32', r31', stC, r38], rfl, rfl, rfl⟩
        have hcondU : Runs w pProg ω
            (.cond (.bin .lt (.reg 33) (.reg 38))
              (.assign 31 (.reg 35) ;; .assign 32 (.reg 34) ;; .assign 33 (.reg 38)) .nop)
            stC .normal stD 12 :=
          runs_cond_iff.mpr ⟨1, 8, by simp [Expr.eval, BinOp.eval, hr33C, hr38C, hlt_b, h1_w],
            by simpa using bundle_runs_seq_normal hu1 (bundle_runs_seq_normal hu2 hu3), by simp [Expr.size]⟩
        have hbody := bundle_runs_seq_normal ha35 (bundle_runs_seq_normal ha36 (bundle_runs_seq_normal ha37
          (bundle_runs_seq_normal hrunIn (bundle_runs_seq_normal ha38 hcondU))))
        obtain ⟨stEnd, cEnd, hrest, hmemE, hregsE, hr31E, hr32E, hr33E, hcE⟩ :=
          ih (k + 1) (by omega) k curLen stD (hmemB.trans hmem)
            (fun r hr => by
              simp [stD, r33', r32', r31', stC, r38, show r ≠ 33 by omega, show r ≠ 32 by omega,
                show r ≠ 31 by omega, show r ≠ 38 by omega,
                hregsB r (by omega) (by omega), stA, r37, r36, r35,
                show r ≠ 37 by omega, show r ≠ 36 by omega, show r ≠ 35 by omega, hregs r hr])
            (by simp [stD, r33', r32', r31', show curLen ≠ 0 by omega, idx0])
            (by simp [stD, r33', r32', show curLen ≠ 0 by omega, hidx_succ])
            (by simp [stD, r33'])
            (by simp [stD, r33', r32', r31', stC, r38, hr34B, hidx_succ])
            (by rw [hfold_succ]; simp [stepFn, curLen, hlt_b])
            (fun h0 => by omega)
        have hcond1 : Expr.eval w st (.bin .lt (.reg 34) (.reg 30)) = some 1 := by
          simp [Expr.eval, BinOp.eval, hr34, hregs 30 (le_refl _), hr30, hidx_lt, h1_w]
        have hloop1 := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stD, _, cEnd, hcond1, by decide, hbody, hrest, rfl⟩))
        refine ⟨stEnd, _, hloop1, hmemE, hregsE, hr31E, hr32E, hr33E, ?_⟩
        rw [hdrop_cons]; simp only [vRunsEndsLen, List.map_cons, List.sum_cons, Expr.size] at hcE ⊢
        dsimp only [curLen] at hcur_pos hcIn ⊢; omega
      · have hcondU : Runs w pProg ω
            (.cond (.bin .lt (.reg 33) (.reg 38))
              (.assign 31 (.reg 35) ;; .assign 32 (.reg 34) ;; .assign 33 (.reg 38)) .nop)
            stC .normal stC 5 :=
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hr33C, hr38C, hlt_b, h0_w],
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
        have hbody := bundle_runs_seq_normal ha35 (bundle_runs_seq_normal ha36 (bundle_runs_seq_normal ha37
          (bundle_runs_seq_normal hrunIn (bundle_runs_seq_normal ha38 hcondU))))
        obtain ⟨stEnd, cEnd, hrest, hmemE, hregsE, hr31E, hr32E, hr33E, hcE⟩ :=
          ih (k + 1) (by omega) bIdx bLen stC (hmemB.trans hmem)
            (fun r hr => by
              simp [stC, r38, show r ≠ 38 by omega, hregsB r (by omega) (by omega),
                stA, r37, r36, r35, show r ≠ 37 by omega, show r ≠ 36 by omega, show r ≠ 35 by omega, hregs r hr])
            (by simp [stC, r38, hregsB 31 (by decide) (by decide), stA, r37, r36, r35, hr31])
            (by simp [stC, r38, hregsB 32 (by decide) (by decide), stA, r37, r36, r35, hr32])
            hr33C (by simp [stC, r38, hr34B, hidx_succ])
            (by rw [hfold_succ]; simp [stepFn, curLen, hlt_b])
            (fun h0 => by omega)
        have hcond1 : Expr.eval w st (.bin .lt (.reg 34) (.reg 30)) = some 1 := by
          simp [Expr.eval, BinOp.eval, hr34, hregs 30 (le_refl _), hr30, hidx_lt, h1_w]
        have hloop1 := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stC, _, cEnd, hcond1, by decide, hbody, hrest, rfl⟩))
        refine ⟨stEnd, _, hloop1, hmemE, hregsE, hr31E, hr32E, hr33E, ?_⟩
        rw [hdrop_cons]; simp only [vRunsEndsLen, List.map_cons, List.sum_cons, Expr.size] at hcE ⊢
        dsimp only [curLen] at hcur_pos hcIn ⊢; omega
  obtain ⟨stEnd, cL, hrunL, hmemE, hregsE, hr31E, hr32E, hr33E, hcL⟩ :=
    hloop vruns.length 0 (by omega) 0 0 stH rfl
      (fun r hr => by simp [stH, r34, r33, r32, r31, show r ≠ 34 by omega, show r ≠ 33 by omega,
        show r ≠ 32 by omega, show r ≠ 31 by omega])
      (by simp [stH, r34, r33, r32, r31]) (by simp [stH, r34, r33, r32])
      (by simp [stH, r34, r33]) (by simp [stH, r34, vRunsEndsLen])
      (by simp) (fun _ => rfl)
  rw [List.drop_zero] at hcL
  refine ⟨stEnd, _, bundle_runs_seq_normal ha31 (bundle_runs_seq_normal ha32
      (bundle_runs_seq_normal ha33 (bundle_runs_seq_normal ha34 hrunL))),
    hmemE, hregsE, hr31E, hr32E, hr33E, by omega⟩

end

end MinCostFlow.SparseCore.Program
