module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideStep
public import MinCostFlow.SparseCore.Program.AssemblyUpdateOutAux

import Mathlib.Tactic

/-!
# Per-slot `DSUpdatePre` derivation and cost telescoping (`AssemblyFirstStepDSPre`)

Companion to `AssemblyFirstStepSideStep.lean`:
1. **`dsUpdatePre_of_sideModel`**: proves all 10 conjuncts of `DSUpdatePre` for an active bucket
   spanner slot from `AsmBrSideModel`, the bounds `∀ B ∈ d.Us, B ≠ []` and `y.mMax = tr.m₀`,
   `BranchUpdatesBelow` + word-size headroom.
2. **`asmFirst_gapS9_cost_telescope`**: proves that raising `asmBrSideRep.phi` to
   `B5.phi + 320 * (capExp + 1) * bundleLogFactor M N * bucketPhi + 300 * walkPot`
   (with `depth ≤ bundleLogFactor M N`) pays all Phase 4 work (P6 updates, `U_H`/`D`/`R` scanning,
   `stepNewWalks` embedding copies including `142 * depth` per `R_p ∪ L_p` edge, and sorting
   `stepBundleTree_reembList`) cleanly against `branchStepCharge`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

public section

private lemma length_le_m_add_splitCount :
    ∀ {G : MGraph} {U : List Update}, G.BatchIsValid U → (∀ u ∈ U, isDelOrSplit u) →
      U.length ≤ G.m + batchSplitCount U
  | _, [], _, _ => by simp [batchSplitCount]
  | G, u :: rest, ⟨hu, hrest⟩, hds => by
    have hu1 := hds u List.mem_cons_self
    have hrest1 : ∀ u' ∈ rest, isDelOrSplit u' := fun u' hu' => hds u' (List.mem_cons_of_mem _ hu')
    have ih := length_le_m_add_splitCount hrest hrest1
    cases u with
    | insert _ _ _ => cases hu1
    | delete e =>
      have hm : (G.applyUpdate (.delete e)).m + 1 = G.m := by
        simp only [MGraph.m, MGraph.applyUpdate]
        exact Finset.card_erase_add_one hu
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit] at ih ⊢
      omega
    | split v v' St Sh =>
      have hm : (G.applyUpdate (.split v v' St Sh)).m = G.m := rfl
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit, ↓reduceIte] at ih ⊢
      omega

private lemma dsStepGenAt_le (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q : ℕ) (us : List Update)
    (k : ℕ) (hG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    dsStepGenAt G₀ impl L q us k ≤ L + 4 + G₀.m := by
  unfold dsStepGenAt
  cases hk : us[k]? with
  | none => dsimp only; omega
  | some u =>
    dsimp only
    have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
    have hInv := (runInv_all hG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb impl mMax)
      hBV hds k (le_of_lt hklt)).1.G_eq
    have hst_sub : (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.E ⊆ G₀.E := by
      rw [hInv]
      exact applyBatch_E_subset_of_delOrSplit _ _ fun x hx => hds x (List.mem_of_mem_take hx)
    have hu_ds : isDelOrSplit u := hds u (List.mem_of_getElem? hk)
    have hG'_sub : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).E ⊆ G₀.E := by
      cases u with
      | insert _ _ _ => cases hu_ds
      | delete e => exact (Finset.erase_subset e _).trans hst_sub
      | split _ _ _ _ => exact hst_sub
    have hG'_m : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ≤ G₀.m :=
      Finset.card_le_card hG'_sub
    have hcl := chooseLevel_le L q (k + 1)
    split_ifs <;> omega

private lemma decodeUpdate_snd_of_updateAt {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hu : UpdateAt mem a G u len) : (decodeUpdate mem a G).2 = len := by
  cases u with
  | insert e x y =>
    rcases hu with ⟨rfl, hL⟩
    have h0 : mem a = 0 := by simpa using hL 0 (by simp)
    simp [decodeUpdate, h0]
  | delete e =>
    rcases hu with ⟨rfl, hL⟩
    have h0 : mem a = 1 := by simpa using hL 0 (by simp)
    simp [decodeUpdate, h0]
  | split v v' St Sh =>
    rcases hu with ⟨Lt, Lh, _, _, _, _, rfl, hL⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hL⟩
    · have h0 : mem a = 2 := by simpa using hL 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by simpa using hL 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by simpa using hL 4 (by simp)
      simp [decodeUpdate, h0, h3, h4]
    · have h0 : mem a = 3 := by simpa using hL 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by simpa using hL 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by simpa using hL 4 (by simp)
      simp [decodeUpdate, h0, h3, h4]

private lemma batchBodyAt_to_lens {mem : ℕ → ℕ} :
    ∀ {a W : ℕ} {G : MGraph} {U : List Update},
      BatchBodyAt mem a G U W → BatchSplitEndsExact G U →
      let res := decodeBatchBody mem U.length a G
      res.1 = U ∧ BatchBodyLensAt mem a G U res.2 ∧ res.2.sum = W
  | _, _, _, [], hBB, _ => ⟨rfl, trivial, hBB.symm⟩
  | a, W, G, u :: rest, ⟨len, hle, hu, hrest⟩, hEnds => by
    have hEndsU : UpdateSplitEndsExact G u := by
      cases u <;> [trivial; trivial; exact ⟨hEnds.1, hEnds.2.1⟩]
    have hEndsR : BatchSplitEndsExact (G.applyUpdate u) rest := by
      cases u <;> [exact hEnds; exact hEnds; exact hEnds.2.2]
    have hd1 : (decodeUpdate mem a G).1 = u := by
      cases u with
      | insert e x y =>
        rcases hu with ⟨rfl, hL⟩
        have h0 : mem a = 0 := by simpa using hL 0 (by simp)
        have h1 : mem (a + 1) = e := by simpa using hL 1 (by simp)
        have h2 : mem (a + 2) = x := by simpa using hL 2 (by simp)
        have h3 : mem (a + 3) = y := by simpa using hL 3 (by simp)
        simp [decodeUpdate, h0, h1, h2, h3]
      | delete e =>
        rcases hu with ⟨rfl, hL⟩
        have h0 : mem a = 1 := by simpa using hL 0 (by simp)
        have h1 : mem (a + 1) = e := by simpa using hL 1 (by simp)
        simp [decodeUpdate, h0, h1]
      | split v v' St Sh =>
        rcases hu with ⟨Lt, Lh, _, _, hLt, hLh, rfl, hL⟩ | ⟨Lt, Lh, _, _, hLt, hLh, rfl, hL⟩
        · have h0 : mem a = 2 := by simpa using hL 0 (by simp)
          have h1 : mem (a + 1) = v := by simpa using hL 1 (by simp)
          have h2 : mem (a + 2) = v' := by simpa using hL 2 (by simp)
          have h3 : mem (a + 3) = Lt.length := by simpa using hL 3 (by simp)
          have h4 : mem (a + 4) = Lh.length := by simpa using hL 4 (by simp)
          have hrt : readList mem (a + 5) Lt.length = Lt := by
            apply List.ext_getElem (by simp [readList])
            intro i hi _; simp only [readList, List.getElem_map, List.getElem_range]
            have hget := hL (5 + i) (by simp at hi ⊢; omega)
            rw [show a + 5 + i = a + (5 + i) by omega, hget, List.getElem_append_left (by simp at hi ⊢; omega),
              List.getElem_append_right (by simp)]
            congr 1; simp
          have hrh : readList mem (a + 5 + Lt.length) Lh.length = Lh := by
            apply List.ext_getElem (by simp [readList])
            intro i hi _; simp only [readList, List.getElem_map, List.getElem_range]
            have hget := hL (5 + Lt.length + i) (by simp at hi ⊢; omega)
            rw [show a + 5 + Lt.length + i = a + (5 + Lt.length + i) by omega, hget,
              List.getElem_append_right (by simp; omega)]
            congr 1; simp; omega
          simp only [decodeUpdate, h0, h1, h2, h3, h4, hrt, hrh, ↓reduceIte, OfNat.ofNat_ne_zero,
            Nat.reduceEqDiff]
          congr 1
          · ext e; rw [List.mem_toFinset, hLt e]; exact ⟨fun h => h.2.2, fun h => ⟨(hEndsU.1 e h).1, (hEndsU.1 e h).2, h⟩⟩
          · ext e; rw [List.mem_toFinset, hLh e]; exact ⟨fun h => h.2.2, fun h => ⟨(hEndsU.2 e h).1, (hEndsU.2 e h).2, h⟩⟩
        · have h0 : mem a = 3 := by simpa using hL 0 (by simp)
          have h1 : mem (a + 1) = v := by simpa using hL 1 (by simp)
          have h2 : mem (a + 2) = v' := by simpa using hL 2 (by simp)
          have h3 : mem (a + 3) = Lt.length := by simpa using hL 3 (by simp)
          have h4 : mem (a + 4) = Lh.length := by simpa using hL 4 (by simp)
          have hrt : readList mem (a + 5) Lt.length = Lt := by
            apply List.ext_getElem (by simp [readList])
            intro i hi _; simp only [readList, List.getElem_map, List.getElem_range]
            have hget := hL (5 + i) (by simp at hi ⊢; omega)
            rw [show a + 5 + i = a + (5 + i) by omega, hget, List.getElem_append_left (by simp at hi ⊢; omega),
              List.getElem_append_right (by simp)]
            congr 1; simp
          have hrh : readList mem (a + 5 + Lt.length) Lh.length = Lh := by
            apply List.ext_getElem (by simp [readList])
            intro i hi _; simp only [readList, List.getElem_map, List.getElem_range]
            have hget := hL (5 + Lt.length + i) (by simp at hi ⊢; omega)
            rw [show a + 5 + Lt.length + i = a + (5 + Lt.length + i) by omega, hget,
              List.getElem_append_right (by simp; omega)]
            congr 1; simp; omega
          simp only [decodeUpdate, h0, h1, h2, h3, h4, hrt, hrh, ↓reduceIte, OfNat.ofNat_ne_zero,
            Nat.reduceEqDiff]
          congr 1
          · ext e; simp only [Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset, hLt e]
            exact ⟨fun ⟨⟨he, ht⟩, hnot⟩ => by by_contra hns; exact hnot ⟨he, ht, hns⟩,
              fun hs => ⟨hEndsU.1 e hs, fun h => h.2.2 hs⟩⟩
          · ext e; simp only [Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset, hLh e]
            exact ⟨fun ⟨⟨he, hh⟩, hnot⟩ => by by_contra hns; exact hnot ⟨he, hh, hns⟩,
              fun hs => ⟨hEndsU.2 e hs, fun h => h.2.2 hs⟩⟩
    have hd2 : (decodeUpdate mem a G).2 = len := decodeUpdate_snd_of_updateAt hu
    have ih := batchBodyAt_to_lens hrest hEndsR
    simp only [List.length_cons, decodeBatchBody, hd1, hd2, BatchBodyLensAt, List.sum_cons]
    exact ⟨congrArg (u :: ·) ih.1, ⟨hu, ih.2.1⟩, by omega⟩

/-- **`DSUpdatePre` derivation**: proves all 10 conjuncts of `DSUpdatePre` for an
active slot from `AsmBrSideModel`, the bounds `∀ B ∈ d.Us, B ≠ []` and `y.mMax = tr.m₀`,
`BranchUpdatesBelow` + word-size headroom. -/
theorem dsUpdatePre_of_sideModel
    {P : DSParams} {tr : BundleTreeState P.L} {U_glob : List Update} {ord ord' : ℕ → List End}
    {q : Finset ℕ × ℤ} {d : DSHist} {batchPtr W h n : ℕ} {mem : ℕ → ℕ}
    (hL : 1 ≤ P.L) (hw16 : 16 ≤ 2 ^ P.w)
    (hC : q.1 ∈ components tr.cs.G₀)
    (hBUB' : BranchUpdatesBelow P.impl
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').state (n + U_glob.length))
    (hSB : P.splitBound = tr.splitBound) (hmMax : P.mMax = tr.m₀)
    (hG0 : d.G₀ = tr.initBunG q) (hst : d.state P = tr.dyn q)
    (hds0 : ∀ u ∈ d.flat, isDelOrSplit u) (hbv0 : d.G₀.BatchIsValid d.flat)
    (hUs_ne : ∀ B ∈ d.Us, B ≠ [])
    (hBat : BatchAt mem batchPtr (d.state P).G
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').U_B q) W)
    (hEnds : BatchSplitEndsExact (d.state P).G
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').U_B q))
    (hbp_le : batchPtr + W ≤ h) (hwords : ∀ i < W, mem (batchPtr + i) < 2 ^ P.w)
    (hU_valid : (d.state P).G.BatchIsValid
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').U_B q))
    (hU_ds : ∀ u ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').U_B q,
      isDelOrSplit u)
    (hU_caps : BatchWithinCaps P.vCap P.eCap
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U_glob ord ord').U_B q))
    (hG0_E : ∀ e ∈ d.G₀.E, e < P.eCap)
    (hG0_n : d.G₀.n + P.splitBound ≤ P.vCap)
    (hWgen : 3 + d.G₀.m + (d.G₀.m + P.splitBound) * (P.L + 6 + d.G₀.m) < 2 ^ P.w)
    (hWq : 2 * (d.G₀.n + P.splitBound) + 2 < 2 ^ P.w)
    (hcw : (36 * (P.vCap + 2 * P.eCap + 1)) ^ P.impl.cw < 2 ^ P.w) :
    DSUpdatePre P d [0, batchPtr, W, h] mem := by
  set sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
  set info := stepBundleTree sp tr U_glob ord ord'
  set U := info.U_B q
  have hdec := batchBodyAt_to_lens hBat.2.2 hEnds
  have hdec_fst : (decodeBatch mem batchPtr (d.state P).G).1 = U := by
    unfold decodeBatch; rw [hBat.2.1]; exact hdec.1
  have hBL : BatchBodyLensAt mem (batchPtr + 1) (d.state P).G U (decodeBatch mem batchPtr (d.state P).G).2 := by
    unfold decodeBatch; rw [hBat.2.1]; exact hdec.2.1
  have hW_eq : W = 1 + (decodeBatch mem batchPtr (d.state P).G).2.sum := by
    unfold decodeBatch; rw [hBat.2.1, hdec.2.2]; have := hBat.1; omega
  have hC' : q.1 ∈ components info.state.cs.G₀ := by
    simpa [info, stepBundleTree, compLSFBatch_G₀] using hC
  have hVG₀ : d.G₀.IsValid := hG0 ▸ (hBUB'.2 q.1 hC' q.2).1
  have hGm₀ : d.G₀.m ≤ P.mMax := by rw [hG0, hmMax]; exact (hBUB'.2 q.1 hC' q.2).2.1
  have hq1 : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hGeq : (d.state P).G = d.G₀.applyBatch d.flat := by
    have hI := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
      hbv0 hds0 d.flat.length le_rfl).1.G_eq
    simpa [DSHist.state, List.take_length] using hI
  have hbv_all : d.G₀.BatchIsValid (d.flat ++ U) := batchIsValid_append.mpr ⟨hbv0, hGeq ▸ hU_valid⟩
  have hds_all : ∀ u ∈ d.flat ++ U, isDelOrSplit u := fun u hu => by
    rcases List.mem_append.mp hu with h1 | h2
    · exact hds0 u h1
    · exact hU_ds u h2
  have hst' : (⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P = info.state.dyn q := by
    rw [dsHist_append_state_eq_update, hst]; rfl
  have hsplit_all : batchSplitCount (d.flat ++ U) ≤ P.splitBound := by
    rw [hSB]
    have hflat_eq : (⟨d.G₀, d.Us ++ [U]⟩ : DSHist).flat = d.flat ++ U := dsHist_flat_append d U
    rw [← hflat_eq]
    exact batchSplitCount_le_of_branchUpdatesBelow hBUB' hC' hL hGm₀ hG0 hst'
      (hflat_eq ▸ hds_all) (hflat_eq ▸ hbv_all)
  have hlen_all : d.flat.length + U.length ≤ d.G₀.m + P.splitBound := by
    have h1 := length_le_m_add_splitCount hbv_all hds_all
    rw [List.length_append] at h1; omega
  have hUs_le : d.Us.length ≤ d.flat.length := by
    have haux : ∀ L : List (List Update), (∀ B ∈ L, B ≠ []) → L.length ≤ L.flatten.length := by
      intro L; induction L with
      | nil => intro _; simp
      | cons B rest ih =>
        intro hne
        have hB : 1 ≤ B.length := List.length_pos_of_ne_nil (hne B List.mem_cons_self)
        have hR := ih (fun B' hB' => hne B' (List.mem_cons_of_mem _ hB'))
        simp only [List.length_cons, List.flatten_cons, List.length_append]; omega
    exact haux d.Us hUs_ne
  have hgen_lt : d.genBound P + dsUpdateLoopGen d.G₀ P.impl P.L (d.q P) (d.flat ++ U) U.length d.flat.length < 2 ^ P.w := by
    have hsum1 : ∑ r ∈ Finset.range d.flat.length, dsStepGenAt d.G₀ P.impl P.L (d.q P) d.flat r ≤
        d.flat.length * (P.L + 4 + d.G₀.m) := by
      calc _ ≤ ∑ _ ∈ Finset.range d.flat.length, (P.L + 4 + d.G₀.m) :=
            Finset.sum_le_sum fun r _ => dsStepGenAt_le d.G₀ P.impl P.mMax P.L (d.q P) d.flat r hVG₀ hL hq1 hGm₀ hbv0 hds0
        _ = d.flat.length * (P.L + 4 + d.G₀.m) := by simp
    have hsum2 : ∑ r ∈ Finset.range U.length, dsStepGenAt d.G₀ P.impl P.L (d.q P) (d.flat ++ U) (d.flat.length + r) ≤
        U.length * (P.L + 4 + d.G₀.m) := by
      calc _ ≤ ∑ _ ∈ Finset.range U.length, (P.L + 4 + d.G₀.m) :=
            Finset.sum_le_sum fun r _ => dsStepGenAt_le d.G₀ P.impl P.mMax P.L (d.q P) (d.flat ++ U) (d.flat.length + r)
              hVG₀ hL hq1 hGm₀ hbv_all hds_all
        _ = U.length * (P.L + 4 + d.G₀.m) := by simp
    have hmul : (d.flat.length + U.length) * (P.L + 6 + d.G₀.m) ≤
        (d.G₀.m + P.splitBound) * (P.L + 6 + d.G₀.m) := Nat.mul_le_mul_right _ hlen_all
    simp only [DSHist.genBound, dsUpdateLoopGen]
    nlinarith
  have hq_lt : d.q P < 2 ^ P.w := by
    have h1 := phaseBase_le (d.G₀.n + P.splitBound) P.L hL
    have hL1 : (1 : ℝ) / (P.L : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hL)]; exact_mod_cast hL
    have hmx1 : (1 : ℝ) ≤ ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) := by
      exact_mod_cast le_max_right (d.G₀.n + P.splitBound) 1
    have hrp : ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) ^ (1 / (P.L : ℝ)) ≤
        ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) := by
      calc _ ≤ ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hmx1 hL1
        _ = _ := Real.rpow_one _
    have hmx_le : ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) ≤ (d.G₀.n : ℝ) + (P.splitBound : ℝ) + 1 := by
      have h0 : max (d.G₀.n + P.splitBound) 1 ≤ d.G₀.n + P.splitBound + 1 := max_le (by omega) (by omega)
      have h0r : ((max (d.G₀.n + P.splitBound) 1 : ℕ) : ℝ) ≤ ((d.G₀.n + P.splitBound + 1 : ℕ) : ℝ) := by
        exact_mod_cast h0
      simpa [Nat.cast_add] using h0r
    have hnat : phaseBase (d.G₀.n + P.splitBound) P.L ≤ 2 * (d.G₀.n + P.splitBound) + 2 := by
      have : (phaseBase (d.G₀.n + P.splitBound) P.L : ℝ) ≤ ((2 * (d.G₀.n + P.splitBound) + 2 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    change phaseBase (d.G₀.n + P.splitBound) P.L < 2 ^ P.w; omega
  refine ⟨0, batchPtr, W, h, rfl, hw16, ?_, ?_, hbp_le, hwords, ?_, ?_, ?_, ?_, ?_, ?_, hq_lt, ?_⟩
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hBL
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using hW_eq
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hU_valid
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hU_ds
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hU_caps
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hsplit_all
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using hgen_lt
  · have hle1 : d.G₀.m + P.splitBound ≤ (d.G₀.m + P.splitBound) * (P.L + 6 + d.G₀.m) :=
      Nat.le_mul_of_pos_right _ (by omega)
    simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] using (by omega : d.flat.length + U.length < 2 ^ P.w)
  · intro r hr
    simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      hdec_fst] at hr ⊢
    unfold dsStepWordOKAt
    have hidx : (d.flat ++ U)[d.flat.length + r]? = some (U[r]'hr) := by
      simp [List.getElem?_append_right (Nat.le_add_right _ _), List.getElem?_eq_getElem hr]
    rw [hidx]; dsimp only; intro _ _
    set G' := (runState (L := P.L) d.G₀ (d.q P) (canonicalSparsify P.impl) (d.flat ++ U)
      (d.flat.length + r)).G.applyUpdate (U[r]'hr)
    have hG'_eq : G' = d.G₀.applyBatch ((d.flat ++ U).take (d.flat.length + r + 1)) := by
      have hInv0 := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
        hbv_all hds_all (d.flat.length + r) (by simp; omega)).1.G_eq
      have htk : (d.flat ++ U).take (d.flat.length + r + 1) =
          (d.flat ++ U).take (d.flat.length + r) ++ [U[r]'hr] := by
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        congr 1; simp [List.getElem_append_right (Nat.le_add_right _ _)]
      rw [htk, applyBatch_append, ← hInv0]; rfl
    have hbv_tk : d.G₀.BatchIsValid ((d.flat ++ U).take (d.flat.length + r + 1)) :=
      (batchIsValid_append.mp (by rwa [List.take_append_drop])).1
    have hds_tk : ∀ x ∈ (d.flat ++ U).take (d.flat.length + r + 1), isDelOrSplit x :=
      fun x hx => hds_all x (List.mem_of_mem_take hx)
    have hG'_val : G'.IsValid := by
      rw [hG'_eq]
      exact LSF.applyBatch_isValid hVG₀ hbv_tk
    have hG'_m : G'.m ≤ P.eCap := by
      rw [hG'_eq]
      have hsub := applyBatch_E_subset_of_delOrSplit d.G₀ ((d.flat ++ U).take (d.flat.length + r + 1)) hds_tk
      calc (d.G₀.applyBatch _).E.card ≤ d.G₀.E.card := Finset.card_le_card hsub
        _ ≤ (Finset.range P.eCap).card := Finset.card_le_card fun e he => Finset.mem_range.mpr (hG0_E e he)
        _ = P.eCap := Finset.card_range _
    have hG'_n : G'.n ≤ P.vCap := by
      rw [hG'_eq, n_applyBatch_of_delOrSplit _ _ hbv_tk hds_tk]
      have hsc_le : batchSplitCount ((d.flat ++ U).take (d.flat.length + r + 1)) ≤
          batchSplitCount (d.flat ++ U) := by
        have h1 : d.flat ++ U = (d.flat ++ U).take (d.flat.length + r + 1) ++
            (d.flat ++ U).drop (d.flat.length + r + 1) := (List.take_append_drop _ _).symm
        conv_rhs => rw [h1]
        simp only [batchSplitCount, List.countP_append]; omega
      omega
    have hact_n : (activeSubgraph G').n ≤ P.vCap := (activeSubgraph_n_le G').trans hG'_n
    refine le_trans (wordSize_canonSparsifyInput_id_le _ _ hG'_val)
      (mul_log_succ_le_of_pow_lt (by omega) ?_)
    refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ _) hcw
    have hm_act : (activeSubgraph G').m = G'.m := rfl
    omega

/-- **Cost telescoping**: under the potential
`320 * (capExp + 1) * bundleLogFactor M N * bank + 300 * walkPot` and `depth ≤ bundleLogFactor M N`,
the Phase 4 work (`284 * stepNewWalks`, `142 * depth * |R_tot|`, `142 * depth * |L_tot|`, and
`O((capExp + 1) * lg * |R_tot|)` sorting of `stepBundleTree_reembList`) telescopes cleanly against
`branchStepCharge`. -/
theorem asmFirst_gapS9_cost_telescope
    {depth capExp M N : ℕ}
    {stepNewWalks walkPotBefore walkPotAfter bankBefore bankAfter dsCharge
     rCount lCount uhCount dCount : ℕ}
    (hd_le : depth ≤ bundleLogFactor M N)
    (hlg1 : 1 ≤ bundleLogFactor M N)
    (hWalk : stepNewWalks + walkPotAfter + bankAfter ≤ walkPotBefore + bankBefore + dsCharge)
    (hCnt : 90 * dCount + 90 * rCount + 240 * uhCount + bankAfter ≤ bankBefore + dsCharge)
    (hl_le : lCount ≤ dsCharge) :
    let lg := bundleLogFactor M N
    let phiMul := 320 * (capExp + 1) * lg
    (284 * stepNewWalks + 142 * depth * rCount + 142 * depth * lCount +
      5 * (capExp + 1) * lg * (dCount + rCount + uhCount)) +
      (phiMul * bankAfter + 300 * walkPotAfter) ≤
    (phiMul * bankBefore + 300 * walkPotBefore) +
      (phiMul + 442 * lg) * dsCharge := by
  intro lg phiMul
  set K := 2 * lg + 5 * (capExp + 1) * lg
  set C := 90 * dCount + 90 * rCount + 240 * uhCount
  have h1 : 284 * stepNewWalks + 300 * walkPotAfter + 300 * bankAfter ≤
      300 * walkPotBefore + 300 * bankBefore + 300 * dsCharge := by
    have := Nat.mul_le_mul_left 300 hWalk; omega
  have h2 : 142 * depth * rCount ≤ 142 * lg * rCount :=
    Nat.mul_le_mul_right rCount (Nat.mul_le_mul_left 142 hd_le)
  have h3 : 142 * depth * lCount ≤ 142 * lg * dsCharge :=
    (Nat.mul_le_mul_right lCount (Nat.mul_le_mul_left 142 hd_le)).trans
      (Nat.mul_le_mul_left (142 * lg) hl_le)
  have h4 : 142 * lg * rCount + 5 * (capExp + 1) * lg * (dCount + rCount + uhCount) ≤ K * C := by
    have hmul : 142 * lg * rCount ≤ 2 * lg * C := by
      calc 142 * lg * rCount ≤ 180 * lg * rCount := by nlinarith
        _ = 2 * lg * (90 * rCount) := by ring
        _ ≤ 2 * lg * C := Nat.mul_le_mul_left _ (by omega)
    have hmul2 : 5 * (capExp + 1) * lg * (dCount + rCount + uhCount) ≤
        5 * (capExp + 1) * lg * C := Nat.mul_le_mul_left _ (by omega)
    dsimp only [K]; rw [Nat.add_mul]; omega
  have h5 : K + 300 ≤ phiMul := by
    dsimp only [K, phiMul]; nlinarith
  have h6 : K * C + K * bankAfter ≤ K * bankBefore + K * dsCharge := by
    calc K * C + K * bankAfter = K * (C + bankAfter) := (Nat.mul_add K C bankAfter).symm
      _ ≤ K * (bankBefore + dsCharge) := Nat.mul_le_mul_left K hCnt
      _ = K * bankBefore + K * dsCharge := Nat.mul_add K bankBefore dsCharge
  have hrem : (phiMul - K - 300) * bankAfter ≤ (phiMul - K - 300) * bankBefore + (phiMul - K - 300) * dsCharge := by
    have := Nat.mul_le_mul_left (phiMul - K - 300) (show bankAfter ≤ bankBefore + dsCharge by omega)
    rwa [Nat.mul_add] at this
  have hsplit_a : phiMul * bankAfter = 300 * bankAfter + K * bankAfter + (phiMul - K - 300) * bankAfter := by
    have : phiMul = 300 + K + (phiMul - K - 300) := by omega
    conv_lhs => rw [this]
    ring
  have hsplit_b : phiMul * bankBefore = 300 * bankBefore + K * bankBefore + (phiMul - K - 300) * bankBefore := by
    have : phiMul = 300 + K + (phiMul - K - 300) := by omega
    conv_lhs => rw [this]
    ring
  have hsplit_d : phiMul * dsCharge = 300 * dsCharge + K * dsCharge + (phiMul - K - 300) * dsCharge := by
    have : phiMul = 300 + K + (phiMul - K - 300) := by omega
    conv_lhs => rw [this]
    ring
  have hmul_rhs : (phiMul + 442 * lg) * dsCharge = phiMul * dsCharge + 442 * lg * dsCharge :=
    Nat.add_mul phiMul (442 * lg) dsCharge
  rw [hsplit_a, hsplit_b, hmul_rhs, hsplit_d]
  have h142 : 142 * lg * dsCharge ≤ 442 * lg * dsCharge := Nat.mul_le_mul_right _ (by omega)
  omega

end

end MinCostFlow.SparseCore.Program
