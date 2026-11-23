module

public import MinCostFlow.Final.AssemblyDryRunSC
public import MinCostFlow.SparseCore.Program.CompModule
import Mathlib.Tactic

/-!
# Cost bounds for the component program P4 in the dry run

This file proves two cost facts about the component program P4 (`compLSFProcs`), which keeps a
low-stretch forest for each connected component, and the window program P3
(`canonicalLSFWindowImpl`).

* `lsfWindowCost_exceeds_log4`: for every constant `C`, there are valid parameters for which the
  cost `lsfWindowCost` of P3 exceeds
  `C * (n0 + m0 + 1 + k * (m0 + n0 + 1) * bundleLogFactor M N ^ 2)`. The reason is the term
  `mwuEdgeStepCost`, which is `positiveExponentialCost L_w P_fp 1 = Θ(P_fp * L_w²) = Θ(log⁶)`.
  So an initialization budget for P3 must allow `bundleLogFactor M N ^ 3`.
* `compBatchCost_polylog`: the full `op 0` batch cost of P4, including canonical split lists, is
  at most `(200000 * (L_w + 1) + 3000) * k * (totalWords + 1)`. A
  cross-component `.insert e a b` projects to `[.insert e a a, .delete e]` in the component of `a`
  and to `[.insert e b b, .delete e]` in the component of `b`, so no ghost end stays in any
  component. A cross-component `.delete e` projects to `[]`, and vertex splits leave out the
  cross edges (`isCross[e] ≠ 0`). The work of forest cuts and of the split lists is paid for by
  drops of the potential `compPhiFull`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program
  MinCostFlow.Num MinCostFlow.MinRatio

/-! ## 1. The window cost `lsfWindowCost` of P3 grows as `Ω(log⁶)` -/

/-- **The bound `bundleLogFactor M N ^ 2` on the initialization cost fails for P3:**
For any input-independent multiplier `C : ℕ`, there exist valid parameters satisfying
`SparseCoreCapHyp 3 1 L M N vCap eCap` and all `CanonicalLSFValid` format inequalities where
`lsfWindowCost` strictly exceeds `C * (n0 + m0 + 1 + k * (m0 + n0 + 1) * bundleLogFactor M N ^ 2)`
because `positiveExponentialCost L_w P_fp 1 = Ω(P_fp * L_w²) = Ω(bundleLogFactor M N ^ 3)`. -/
theorem lsfWindowCost_exceeds_log4 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (C : ℕ) :
    ∃ (M N L P_fp k n0 m0 vCap eCap : ℕ),
      1 ≤ L ∧ 4 ∣ P_fp ∧ P_fp + 6 ≤ 4 * L ∧
      (∃ q, q + 11 ≤ P_fp ∧ 40 * k ≤ 2 ^ q) ∧
      32 * (m0 + 1) * 2 ^ P_fp < 2 ^ (4 * L - 1) ∧
      1 ≤ k ∧ 1 ≤ m0 ∧ n0 ≤ N ∧ m0 ≤ M ∧
      SparseCoreCapHyp 3 1 L M N vCap eCap ∧
      C * (n0 + m0 + 1 + k * (m0 + n0 + 1) * bundleLogFactor M N ^ 2) <
        lsfWindowCost Q_AN c_AN K_AN 4 L P_fp k n0 m0 := by
  set t := max 20 (C + 20)
  set M := 2 ^ t
  set N := 2 ^ t
  set L := bundleLogFactor M N
  set P_fp := 4 * (L / 4)
  have h2t : 2 ^ 20 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hM_ge : 1048576 ≤ M := by simpa [M] using h2t
  have hN_ge : 1048576 ≤ N := by simpa [N] using h2t
  have hlog : t ≤ Nat.log 2 (M + N + 2) :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by dsimp [M]; omega)
  have hC_le_t : C + 20 ≤ t := le_max_right _ _
  have hlg_ge : (C + 20) ^ 2 ≤ L :=
    Nat.pow_le_pow_left (by omega : C + 20 ≤ Nat.log 2 (M + N + 2) + 1) 2
  have hL400 : 400 ≤ L := by
    have : 20 ^ 2 ≤ (C + 20) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  refine ⟨M, N, L, P_fp, 1, 2, 1, 4, 4, by omega, dvd_mul_right 4 _, by dsimp [P_fp]; omega,
    ⟨6, by dsimp [P_fp]; omega, by decide⟩, ?_, le_rfl, le_rfl, by omega, by omega, ?_, ?_⟩
  · have h64 : 32 * (1 + 1) = 2 ^ 6 := by decide
    rw [h64, ← pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [P_fp]; omega)
  · refine ⟨?_, by simp [L]⟩
    have hcube : 10 ^ 3 ≤ (M + N + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  · have hP_ge : L / 2 ≤ P_fp := by dsimp [P_fp]; omega
    have hLw_ge : L ≤ canonLw K_AN L 2 1 := canonLw_ge_Lin K_AN L 2 1
    have hexp_ge : P_fp * (500 * L ^ 2) ≤ positiveExponentialCost (canonLw K_AN L 2 1) P_fp 1 := by
      unfold positiveExponentialCost
      have hsq : L ^ 2 ≤ (canonLw K_AN L 2 1) ^ 2 := Nat.pow_le_pow_left hLw_ge 2
      have h1 : P_fp * (500 * L ^ 2) ≤ (P_fp + 4) * (500 * (canonLw K_AN L 2 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 500 hsq)
      have h2 : (P_fp + 4) * (500 * (canonLw K_AN L 2 1) ^ 2) ≤
          (P_fp + 4) * (500 * (canonLw K_AN L 2 1) ^ 2 + 2000 * canonLw K_AN L 2 1 + 2000) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hmwu_ge : positiveExponentialCost (canonLw K_AN L 2 1) P_fp 1 ≤
        mwuEdgeStepCost L (canonLw K_AN L 2 1) P_fp := by
      unfold mwuEdgeStepCost; omega
    have hl55_ge : mwuEdgeStepCost L (canonLw K_AN L 2 1) P_fp ≤
        lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L 2 1) P_fp 1 2 1 := by
      unfold lemma55Cost; dsimp only; omega
    have hwin_ge : 10 * lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L 2 1) P_fp 1 2 1 ≤
        lsfWindowCost Q_AN c_AN K_AN 4 L P_fp 1 2 1 := by
      unfold lsfWindowCost; exact Nat.mul_le_mul_right _ (by omega)
    have hP500 : 10 * (P_fp * (500 * L ^ 2)) ≤ lsfWindowCost Q_AN c_AN K_AN 4 L P_fp 1 2 1 :=
      le_trans (Nat.mul_le_mul_left 10 (le_trans (le_trans hexp_ge hmwu_ge) hl55_ge)) hwin_ge
    have hC_lt_L : C + 1 < L := by
      have : (C + 20) ≤ (C + 20) ^ 2 := Nat.le_self_pow (by decide) _
      omega
    have hL3 : 2000 * L * L ^ 2 ≤ 10 * (P_fp * (500 * L ^ 2)) := by
      have h1 : 2000 * L ≤ 10 * (P_fp * 500) := by omega
      have h2 := Nat.mul_le_mul_right (L ^ 2) h1
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
    have hLHS : C * (2 + 1 + 1 + 1 * (1 + 2 + 1) * L ^ 2) < 2000 * L * L ^ 2 := by
      have h4 : 2 + 1 + 1 + 1 * (1 + 2 + 1) * L ^ 2 ≤ 5 * L ^ 2 := by
        have : 4 ≤ L ^ 2 := Nat.pow_le_pow_left (by omega : 2 ≤ L) 2
        omega
      have h5 : C * (2 + 1 + 1 + 1 * (1 + 2 + 1) * L ^ 2) ≤ C * (5 * L ^ 2) :=
        Nat.mul_le_mul_left C h4
      have h6 : C * 5 < 2000 * L := by omega
      have h7 : C * (5 * L ^ 2) < (2000 * L) * L ^ 2 := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_lt_mul_of_pos_right h6 (Nat.pow_pos (by omega : 0 < L))
      exact lt_of_le_of_lt h5 h7
    exact lt_of_lt_of_le hLHS (le_trans hL3 hP500)

/-! ## 2. A polylogarithmic batch cost bound (`compBatchCost_polylog`) -/

private lemma applyLSFBatch_G_local (S : LSFState) : ∀ U, (applyLSFBatch S U).G = S.G.applyBatch U
  | [] => rfl
  | u :: us => by
    change (applyLSFBatch (applyLSFUpdate S u) us).G = (S.G.applyUpdate u).applyBatch us
    rw [applyLSFBatch_G_local]; cases u <;> rfl

private lemma dgUpdateMemLen_ge_two {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (h : UpdateAt mem a G u len) : 2 ≤ len ∧ dgUpdateMemLen mem a = len := by
  cases u with
  | insert e x y =>
    rcases h with ⟨rfl, hLA⟩
    have h0 : mem a = 0 := by simpa using hLA 0 (by simp)
    exact ⟨by omega, by simp [dgUpdateMemLen, h0]⟩
  | delete e =>
    rcases h with ⟨rfl, hLA⟩
    have h0 : mem a = 1 := by simpa using hLA 0 (by simp)
    exact ⟨by omega, by simp [dgUpdateMemLen, h0]⟩
  | split v v' St Sh =>
    rcases h with ⟨Lt, Lh, _, _, _, _, rfl, hLA⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hLA⟩
    · have h0 : mem a = 2 := by simpa using hLA 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by simpa using hLA 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by simpa using hLA 4 (by simp)
      exact ⟨by omega, by simp [dgUpdateMemLen, h0, h3, h4]⟩
    · have h0 : mem a = 3 := by simpa using hLA 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by simpa using hLA 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by simpa using hLA 4 (by simp)
      exact ⟨by omega, by simp [dgUpdateMemLen, h0, h3, h4]⟩

private lemma projUpdWords_sum_le {mem : ℕ → ℕ} {cs : CompLSFState} {ptr len : ℕ}
    {u : Update} (hI : ∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ cs)
    (hU : UpdateAt mem ptr cs.G u len) :
    (components cs.G₀).sum (fun C => projUpdWords mem cs C ptr u) ≤ 3 * len := by
  classical
  obtain ⟨C_lsst, ℓ₀, hInv⟩ := hI
  obtain ⟨hlen2, hlen_eq⟩ := dgUpdateMemLen_ge_two hU
  have hAtMostOneV : ∀ (v : ℕ), ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card ≤ 1 := by
    intro v
    rw [Finset.card_le_one]
    intro C₁ h1 C₂ h2
    by_contra hne
    exact Finset.disjoint_left.mp
      (hInv.hV_disj C₁ (Finset.mem_filter.mp h1).1 C₂ (Finset.mem_filter.mp h2).1 hne)
      (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  cases u with
  | insert e a b =>
    have hlen4 : len = 4 := hU.1
    have hpt : ∀ C ∈ components cs.G₀,
        projUpdWords mem cs C ptr (.insert e a b) ≤
          if a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V then 6 else 0 := fun C _ => by
      simp only [projUpdWords]; split_ifs <;> first | omega | tauto
    calc (components cs.G₀).sum (fun C => projUpdWords mem cs C ptr (.insert e a b))
        ≤ (components cs.G₀).sum (fun C =>
            if a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V then 6 else 0) :=
          Finset.sum_le_sum hpt
      _ = ((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V).sum
            (fun _ => 6) := by rw [Finset.sum_filter]
      _ = (((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V).card) * 6 := by
          simp
      _ ≤ 2 * 6 := by
          have hsub : ((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V) ⊆
              ((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V) ∪
              ((components cs.G₀).filter fun C => b ∈ (cs.compSt C).G.V) := by
            intro C hC; simp only [Finset.mem_filter, Finset.mem_union] at hC ⊢; tauto
          have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
          have ha := hAtMostOneV a; have hb := hAtMostOneV b; omega
      _ = 3 * len := by rw [hlen4]
  | delete e =>
    have hlen2' : len = 2 := hU.1
    calc (components cs.G₀).sum (fun C => projUpdWords mem cs C ptr (.delete e))
        = ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).sum (fun _ => 2) := by
          rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun C _ => by simp [projUpdWords]
      _ = ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).card * 2 := by simp
      _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 (hInv.hEdge_atMostTwo e)
      _ ≤ 3 * len := by omega
  | split v v' St Sh =>
    have hval : ∀ C ∈ components cs.G₀, projUpdWords mem cs C ptr (.split v v' St Sh) =
        if v ∈ (cs.compSt C).G.V then len else 0 := fun C _ => by
      simp only [projUpdWords, hlen_eq]
    calc (components cs.G₀).sum (fun C => projUpdWords mem cs C ptr (.split v v' St Sh))
        = (components cs.G₀).sum (fun C => if v ∈ (cs.compSt C).G.V then len else 0) :=
          Finset.sum_congr rfl hval
      _ = ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).sum (fun _ => len) := by
          rw [Finset.sum_filter]
      _ = ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card * len := by simp
      _ ≤ 1 * len := Nat.mul_le_mul_right len (hAtMostOneV v)
      _ ≤ 3 * len := by omega

private lemma projBatchBodyWords_sum_le {mem : ℕ → ℕ} :
    ∀ {U : List Update} {cs : CompLSFState} {ptr bw : ℕ},
      (∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ cs) →
      cs.G.BatchIsValid U →
      BatchBodyAt mem ptr cs.G U bw →
      (components cs.G₀).sum (fun C => projBatchBodyWords mem C cs ptr U) ≤ 3 * bw
  | [], _, _, _, _, _, _ => by simp [projBatchBodyWords]
  | u :: us, cs, ptr, bw, ⟨C_lsst, ℓ₀, hInv⟩, ⟨huV, husV⟩, ⟨len, hle, hU, hB'⟩ => by
    obtain ⟨_, hlen_eq⟩ := dgUpdateMemLen_ge_two hU
    have h1 := projUpdWords_sum_le ⟨C_lsst, ℓ₀, hInv⟩ hU
    have h2 := projBatchBodyWords_sum_le (U := us) (cs := compLSFStepSingle cs u)
      (ptr := ptr + len) (bw := bw - len) ⟨C_lsst, ℓ₀, compLSFInv_step hInv huV⟩ husV hB'
    calc (components cs.G₀).sum (fun C => projBatchBodyWords mem C cs ptr (u :: us))
        = (components cs.G₀).sum (fun C => projUpdWords mem cs C ptr u) +
          (components cs.G₀).sum (fun C =>
            projBatchBodyWords mem C (compLSFStepSingle cs u) (ptr + dgUpdateMemLen mem ptr) us) := by
          simp only [projBatchBodyWords, Finset.sum_add_distrib]
      _ ≤ 3 * len + 3 * (bw - len) := by rw [hlen_eq]; exact Nat.add_le_add h1 h2
      _ = 3 * bw := by omega

private lemma touchedCompsBatch_card_le {cs : CompLSFState} :
    ∀ {U : List Update},
      (∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ cs) →
      cs.G.BatchIsValid U →
      (touchedCompsBatch cs U).card ≤ 2 * U.length
  | [], _, _ => by
    have hemp : touchedCompsBatch cs [] = ∅ := by
      ext C; simp [touchedCompsBatch, projCompBatchG]
    rw [hemp]; simp
  | u :: us, ⟨C_lsst, ℓ₀, hInv⟩, ⟨huV, husV⟩ => by
    classical
    have hsub : touchedCompsBatch cs (u :: us) ⊆
        touchedComps cs u ∪ touchedCompsBatch (compLSFStepSingle cs u) us := by
      intro C hC
      simp only [touchedCompsBatch, touchedComps, Finset.mem_union, Finset.mem_filter] at hC ⊢
      have hG0 : (compLSFStepSingle cs u).G₀ = cs.G₀ := rfl
      rw [hG0]
      have hstep : projCompBatchG cs.G (cs.compSt C).G (u :: us) =
          projCompUpdateG cs.G (cs.compSt C).G u ++
            projCompBatchG (compLSFStepSingle cs u).G ((compLSFStepSingle cs u).compSt C).G us := by
        simp [projCompBatchG, compLSFStepSingle, applyLSFBatch_G_local]
      rw [hstep, ne_eq, List.append_eq_nil_iff, not_and_or] at hC
      tauto
    have hAtMostOneV : ∀ (v : ℕ), ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card ≤ 1 := by
      intro v
      rw [Finset.card_le_one]
      intro C₁ h1 C₂ h2
      by_contra hne
      exact Finset.disjoint_left.mp
        (hInv.hV_disj C₁ (Finset.mem_filter.mp h1).1 C₂ (Finset.mem_filter.mp h2).1 hne)
        (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have h1 : (touchedComps cs u).card ≤ 2 := by
      cases u with
      | insert e a b =>
        have hs : touchedComps cs (.insert e a b) ⊆
            ((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V) ∪
            ((components cs.G₀).filter fun C => b ∈ (cs.compSt C).G.V) := by
          intro C hC
          obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
          simp only [projCompUpdateG] at hne
          simp only [Finset.mem_union, Finset.mem_filter]
          by_cases ha : a ∈ (cs.compSt C).G.V
          · exact Or.inl ⟨hCm, ha⟩
          · by_cases hb : b ∈ (cs.compSt C).G.V
            · exact Or.inr ⟨hCm, hb⟩
            · simp [ha, hb] at hne
        have := le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
        have ha := hAtMostOneV a; have hb := hAtMostOneV b; omega
      | delete e =>
        have hs : touchedComps cs (.delete e) ⊆
            (components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E := by
          intro C hC
          obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
          refine Finset.mem_filter.mpr ⟨hCm, ?_⟩
          by_contra hnot; simp [projCompUpdateG, hnot] at hne
        exact le_trans (Finset.card_le_card hs) (hInv.hEdge_atMostTwo e)
      | split v v' St Sh =>
        have hs : touchedComps cs (.split v v' St Sh) ⊆
            (components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V := by
          intro C hC
          obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
          refine Finset.mem_filter.mpr ⟨hCm, ?_⟩
          by_contra hnot; simp [projCompUpdateG, hnot] at hne
        exact le_trans (Finset.card_le_card hs) (by have := hAtMostOneV v; omega)
    have h2 := touchedCompsBatch_card_le (cs := compLSFStepSingle cs u) (U := us)
      ⟨C_lsst, ℓ₀, compLSFInv_step hInv huV⟩ husV
    have hu := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    simp only [List.length_cons]
    omega

/-- **Polylogarithmic batch cost bound for P4 (`compBatchCost_polylog`):**
Cross-component inserts project to `[.insert e a a, .delete e]` / `[.insert e b b, .delete e]`
leaving zero ghost ends in every component), P4's full `op 0` batch cost (including canonical split lists)
is bounded by `(200000 * (L_w + 1) + 3000) * k * (totalWords + 1)` — polynomial in `log m`
and parameters times batch size, with all forest-cut and split-list extraction work amortized by
`compPhiFull`. -/
theorem compBatchCost_polylog (W : LSFWindowImpl) {w k b batchPtr heap totalWords : ℕ}
    {G₀ : MGraph} (hk : 1 ≤ k) {S : CompLSFFamily k} {mem : ℕ → ℕ} {U : List Update}
    (hI : ∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ (S ⟨0, hk⟩))
    (hB : BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords)
    (hVal : (S ⟨0, hk⟩).G.BatchIsValid U) :
    (compLSFDSFullWithSplits W w k G₀).cost 0 S [b, batchPtr, heap] mem ≤
      (200000 * (mem (b + compOffLW) + 1) + 3000) * k * (totalWords + 1) := by
  classical
  obtain ⟨C_lsst, ℓ₀, hInv⟩ := hI
  set cs0 := S ⟨0, hk⟩
  set L_w := mem (b + compOffLW)
  have hsub : ∀ C ∈ components cs0.G₀, (cs0.compSt C).G.E ⊆ cs0.G.E := fun C hC => hInv.hCE_sub C hC
  have hcost_base := compLSFDS_batchCost_eq W (w := w) (b := b) (heap := heap) (G₀ := G₀) hk hsub hB
  have hcost_full : (compLSFDSFullWithSplits W w k G₀).cost 0 S [b, batchPtr, heap] mem =
      5 * k * sumTouchedLsfBatchCost mem cs0 batchPtr L_w U + 3000 * k * (U.length + 1) := by
    simp only [compLSFDSFullWithSplits, ↓reduceIte, compLSFDSFull, show (0 : ℕ) ≠ 6 by decide,
      hcost_base, compBatchLsfMul, compBatchUpdMul, compBatchUpdMulFull, List.getD_cons_zero,
      List.getD_cons_succ, hB.2.1]
    ring
  rw [hcost_full]
  have h2U_le_tw : 2 * U.length ≤ totalWords := by
    have hgo : ∀ (V : List Update) (G : MGraph) (ptr bw : ℕ),
        BatchBodyAt mem ptr G V bw → 2 * V.length ≤ bw := by
      intro V
      induction V with
      | nil => intro _ _ _ _; simp
      | cons u us ih =>
        intro G ptr bw ⟨len, hle, hU, hB'⟩
        have h2 := (dgUpdateMemLen_ge_two hU).1
        have hih := ih _ _ _ hB'
        simp only [List.length_cons]; omega
    have := hgo U cs0.G (batchPtr + 1) (totalWords - 1) hB.2.2
    omega
  have hU_le_tw : U.length ≤ totalWords := by omega
  have htc_card := touchedCompsBatch_card_le ⟨C_lsst, ℓ₀, hInv⟩ hVal
  have hbw_sum := projBatchBodyWords_sum_le ⟨C_lsst, ℓ₀, hInv⟩ hVal hB.2.2
  set T := (touchedCompsBatch cs0 U).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m
  have hT_sub_comp : T ⊆ components cs0.G₀ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hT_card : T.card ≤ totalWords :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by omega)
  have hsum_proj : T.sum (fun C => projBatchBodyWords mem C cs0 (batchPtr + 1) U) ≤ 3 * totalWords :=
    le_trans (Finset.sum_le_sum_of_subset hT_sub_comp) (by omega)
  have hsum_touched : sumTouchedLsfBatchCost mem cs0 batchPtr L_w U ≤
      40000 * (L_w + 1) * totalWords := by
    unfold sumTouchedLsfBatchCost compProjLsfBatchCost lsfBatchCostFactor
    calc T.sum (fun C => 10000 * ((1 + projBatchBodyWords mem C cs0 (batchPtr + 1) U) * L_w + 1))
        = 10000 * T.sum (fun C => (1 + projBatchBodyWords mem C cs0 (batchPtr + 1) U) * L_w + 1) := by
          rw [Finset.mul_sum]
      _ = 10000 * (T.sum (fun _ => L_w + 1) +
            L_w * T.sum (fun C => projBatchBodyWords mem C cs0 (batchPtr + 1) U)) := by
          congr 1
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun C _ => by ring
      _ ≤ 10000 * (totalWords * (L_w + 1) + L_w * (3 * totalWords)) := by
          refine Nat.mul_le_mul_left 10000 (Nat.add_le_add ?_ (Nat.mul_le_mul_left L_w hsum_proj))
          simp only [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right (L_w + 1) hT_card
      _ ≤ 40000 * (L_w + 1) * totalWords := by
          have h1 : totalWords * (L_w + 1) + L_w * (3 * totalWords) ≤ 4 * (L_w + 1) * totalWords := by
            have : L_w * (3 * totalWords) ≤ (L_w + 1) * (3 * totalWords) :=
              Nat.mul_le_mul_right _ (by omega)
            linarith
          have h2 := Nat.mul_le_mul_left 10000 h1
          linarith
  have h1 : 5 * k * sumTouchedLsfBatchCost mem cs0 batchPtr L_w U ≤
      200000 * (L_w + 1) * k * totalWords := by
    have := Nat.mul_le_mul_left (5 * k) hsum_touched
    linarith
  have h2 : 3000 * k * (U.length + 1) ≤ 3000 * k * (totalWords + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : 200000 * (L_w + 1) * k * totalWords ≤ 200000 * (L_w + 1) * k * (totalWords + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  linarith

end MinCostFlow.Final.DryRun

end
