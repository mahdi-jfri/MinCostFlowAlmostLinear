module

public import MinCostFlow.MinRatio.DetectOffTreeDrain
public import MinCostFlow.MinRatio.SolverTreeBudgetInv
import WordRAM.Tactic

/-!
# The full off-tree drain of `Detect` (`DetectOffTreeDrainRun`)

Proves `detectOffTreeDrainBody_runs`: the loop of `detectOffTreeDrainStep_triple`
(`DetectOffTreeDrain.lean`) over `offReadyList[0 .. tok.offReadyCount)`. It also shows that the
record blocks of the live off-tree edges stay `2 + 4 L` apart (`OffTreeRecSep`). A block that is
moved lies in `[heap₀, curHeap)`, and the moved blocks are apart. A block that is not moved lies
below `base ≤ heap₀`, since its cells have tag `18`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Full execution of `detectOffTreeDrainBody`: drains `offReadyList[0 .. tok.offReadyCount)`,
emits every live off-tree ready edge without duplicates, resets each emitted off-tree edge's
`PathEdgeAt` detector in freshly allocated memory `[heap₀, curHeap)`, clears `inOffReady` and
`offReadyCount`, and runs in at most `tok.offReadyCount * detectOffTreeDrainUnit L + 70` steps. -/
theorem detectOffTreeDrainBody_runs {w L P m V psi k epsExp drainUnit isNeg reset : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {st : State}
    {root base heap₀ : ℕ} {treeRep : List ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok st.mem)
    (hbelow : ∀ a, tok.tag a ≠ 0 → tok.tag a ≠ 16 → a < base)
    (hExtRange : ∀ e < m, e ∈ model.extG.E)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hfitThr : ∀ e ∈ model.extG.E, Num.Fits 4 L (-detectorThreshold P cfg.ε (model.extℓ e)))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (hr0 : st.regs 0 = root) (hr1 : st.regs 1 = base) (hr2 : st.regs 2 = m)
    (hr3 : st.regs 3 = base + 1 + treeRep.length) (hr4 : st.regs 4 = heap₀) (hr5 : st.regs 5 = L)
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hTreeLen : treeRep.length ≤ m) (hTreeNd : treeRep.Nodup)
    (hTreeList : ListAt st.mem (base + 1) treeRep)
    (hTreeSub : ∀ e ∈ treeRep, e ∈ model.extG.E ∧ model.extToInt e ∈ model.chain.toTreeChain.chainTree.E)
    (hz0 : ZeroFrom st.mem heap₀)
    (hroom : heap₀ + tok.offReadyCount * (2 + 4 * L) < 2 ^ w)
    (hw13 : 13 < 2 ^ w) (hLpos : 0 < L) :
    ∃ out cost offRep curHeap,
      Runs w p ω (detectOffTreeDrainBody isNeg reset) st .normal out cost ∧
      cost ≤ tok.offReadyCount * detectOffTreeDrainUnit L + 70 ∧
      out.regs 0 = root ∧ out.regs 1 = base ∧
      out.regs 3 = base + 1 + (treeRep ++ offRep).length ∧
      out.regs 4 = curHeap ∧
      heap₀ ≤ curHeap ∧ curHeap ≤ heap₀ + tok.offReadyCount * (2 + 4 * L) ∧
      ZeroFrom out.mem curHeap ∧
      (treeRep ++ offRep).Nodup ∧
      ListAt out.mem (base + 1) (treeRep ++ offRep) ∧
      out.mem (root + 11) = 0 ∧
      (∀ e < tok.intCap, out.mem (tok.inOffReady + e) = 0) ∧
      (∀ e, e ∈ offRep ↔ e ∈ model.extG.E ∧
        model.extToInt e ∉ model.chain.toTreeChain.chainTree.E ∧
        e ∈ (algorithm2_detect cfg model).1) ∧
      (∀ e ∈ model.extG.E,
        let ei := model.extToInt e
        ei ∉ model.chain.toTreeChain.chainTree.E →
        if e ∈ offRep then
          heap₀ ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ curHeap ∧
          ∃ val : PathEdgeValue,
            PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some val) ∧
            val.forward = true ∧
            (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
            val.detector = -detectorThreshold P cfg.ε (model.extℓ e) ∧
            (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
            (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e
        else
          out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∧
          ∀ x < 2 + 4 * L, out.mem (st.mem (tok.edgeRecords + ei) + x) =
            st.mem (st.mem (tok.edgeRecords + ei) + x)) ∧
      (∀ a < heap₀, a ≠ root + 11 →
        (a < base + 1 ∨ base + 1 + m ≤ a) →
        (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) →
        (a < tok.edgeRecords ∨ tok.edgeRecords + tok.intCap ≤ a) →
        out.mem a = st.mem a) ∧
      (OffTreeRecSep model L st.mem tok.edgeRecords → OffTreeRecSep model L out.mem tok.edgeRecords) := by
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, _, hfreshInv, _, _, _, _, hoffInv, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, t1, _, _, _, _, _, _, _, _, _, _, _, t13, _, t15, _, t1718, _, _, _⟩ := htags
  have hltB {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16 := by decide) : a < base :=
    hbelow a (ht ▸ hv) (ht ▸ hv16)
  have hroot13W : root + 13 < 2 ^ w := by have := hltB (t1 13 (by omega)) (by decide); omega
  obtain ⟨mid, hrLoad, hmidMem, _, hmidR5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13⟩ :=
    detectOffTreeDrainLoad_runs hr0 hw13 hroot13W
      (by simpa using hrootDir 3 (by simp)) (by simpa using hrootDir 4 (by simp))
      (by simpa using hrootDir 6 (by simp)) (by simpa using hrootDir 9 (by simp))
      (by simpa using hrootDir 10 (by simp)) (by simpa using hrootDir 11 (by simp))
      (by simpa using hrootDir 12 (by simp)) (by simpa using hrootDir 13 (by simp))
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = mid)
    (Inv := DrainInv (P := P) (m := m) model tok st.mem root base heap₀ treeRep)
    (r := 14) (lo := .const 0) (hi := .reg 11) (detectOffTreeStepBudget L) 0 tok.offReadyCount
    (Nat.zero_le _) (by omega)
    (fun _ => by
      have : tok.offReadyCount * 2 ≤ tok.offReadyCount * (2 + 4 * L) :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval], [], heap₀,
        by simp [(hmidR5 0 (by decide)).trans hr0], by simp [(hmidR5 1 (by decide)).trans hr1],
        by simp [(hmidR5 2 (by decide)).trans hr2],
        by simp [(hmidR5 3 (by decide)).trans hr3], by simp [(hmidR5 4 (by decide)).trans hr4],
        by simp [(hmidR5 5 (by decide)).trans hr5], by simp [hm6], by simp [hm7], by simp [hm8],
        by simp [hm9], by simp [hm10], by simp [hm11], by simp [hm12], by simp [hm13],
        by simp, Nat.zero_le _, by simpa using hTreeLen, by simpa using hTreeNd,
        by simpa [hmidMem] using hTreeList, le_rfl, by omega, hmidMem.symm ▸ hz0,
        fun _ hk => absurd hk (Nat.not_lt_zero _),
        fun k _ hk => by rw [hmidMem]; exact (hoffInv.2.1 k hk).2,
        fun _ _ h0 => hmidMem.symm ▸ h0,
        fun _ => by simp,
        fun e he => by
          dsimp only; intro hnot
          rw [ite_eq_right (by simp)]
          exact ⟨hmidMem ▸ rfl, fun _ _ => hmidMem ▸ rfl⟩,
        fun _ _ _ _ _ => hmidMem ▸ rfl, fun _ h => absurd h (by simp)⟩)
    (fun _ _ _ _ hs => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr14, _⟩ := hs; exact hr14)
    (fun _ s _ _ hs => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hr11s, _⟩ := hs
      simp [Expr.eval, hr11s])
    (fun j _ hj => detectOffTreeDrainStep_triple hrep0 hbelow hExtRange heps hlen hfitThr
      hIsNeg hReset hbaseHeap hTreeSub hroom hw13 hLpos hj)
  obtain ⟨o, afterLoop, cLoop, hrLoop, hLoopPost, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hLoopPost
  | normal =>
    obtain ⟨offRep, curHeap, ha0, ha1, _, ha3, ha4, _, _, _, _, _, _, _, _, _, _,
      _, _, hnd, hlist, hcurLo, hcurHi, hzCur, hclr, _, hzero0, hoffIff, hrecInv, hframe0,
      hsepR⟩ := hLoopPost
    let out := { afterLoop with mem := Function.update afterLoop.mem (root + 11) 0 }
    have hroot11W : root + 11 < 2 ^ w := by omega
    have rClearCnt : Runs w p ω (.store (.bin .add (.reg 0) (.const 11)) (.const 0))
        afterLoop .normal out 5 :=
      runs_store_iff.mpr ⟨root + 11, 0,
        by simp [Expr.eval, BinOp.eval, ha0, show 11 < 2 ^ w by omega, hroot11W],
        by simp [Expr.eval], rfl, rfl, rfl⟩
    have hroot11B : root + 11 < base := hltB (t1 11 (by omega)) (by decide)
    have hcostB : 47 + (cLoop + 5 + 1) + 1 ≤ tok.offReadyCount * detectOffTreeDrainUnit L + 70 := by
      simp only [Expr.size, detectOffTreeStepBudget, detectOffTreeDrainUnit] at hcLoop ⊢
      have hmul : (tok.offReadyCount - 0) * (87 * L + 200 + 1 + 8) ≤
          tok.offReadyCount * (87 * L + 220) := by
        rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨out, 47 + (cLoop + 5 + 1) + 1, offRep, curHeap,
      runs_seq_iff.mpr (Or.inr ⟨mid, 47, cLoop + 5 + 1, hrLoad,
        runs_seq_iff.mpr (Or.inr ⟨afterLoop, cLoop, 5, hrLoop, rClearCnt, rfl⟩), rfl⟩),
      hcostB, ha0, ha1, ha3, ha4, hcurLo, hcurHi,
      fun a ha => by
        simp only [out, Function.update_of_ne (show a ≠ root + 11 by omega)]
        exact hzCur a ha,
      hnd,
      fun idx hidx => by
        simp only [out, Function.update_of_ne (show base + 1 + idx ≠ root + 11 by omega)]
        exact hlist idx hidx,
      by simp [out],
      fun e he => by
        have hne : tok.inOffReady + e ≠ root + 11 := fun h => by
          have h1 := t15 e he; have h2 := t1 11 (by omega); rw [h] at h1; omega
        simp only [out, Function.update_of_ne hne]
        rcases hoffInv.2.2.2.1 e he with h0 | h1
        · exact hzero0 e he h0
        · obtain ⟨k, hk, hke⟩ := hoffInv.2.2.2.2 e he h1
          rw [← hke]; exact hclr k hk,
      fun e => by
        rw [hoffIff e]
        constructor
        · rintro ⟨k, _, hR, rfl⟩; exact ⟨hR.1, hR.2.1.symm ▸ hR.2.2.1, hR.2.2.2⟩
        · rintro ⟨heE, hnotT, hdet⟩
          have heiCap := (hedgeAcc.1 e heE).1
          have hdi := solverStateRep_detect_iff hrep0 heE heps (hlen e heE)
          rw [ite_eq_right hnotT] at hdi
          obtain ⟨val, _, hiff, hpush⟩ := hdi
          have h1 := hpush (hiff.mpr hdet)
          obtain ⟨k, hk, hke⟩ := hoffInv.2.2.2.2 _ heiCap h1
          have hinvE : model.intToExt (model.extToInt e) = e := hfreshInv.hLeft e heE
          refine ⟨k, hk, ?_, by rw [hke, hinvE]⟩
          unfold IsOffTreeReady
          rw [hke, hinvE]
          exact ⟨heE, rfl, hnotT, hdet⟩,
      fun e he => by
        dsimp only; intro hnotT
        have heiCap := (hedgeAcc.1 e he).1
        have hneEr : tok.edgeRecords + model.extToInt e ≠ root + 11 := fun h => by
          have h1 := t13 _ heiCap; have h2 := t1 11 (by omega); rw [h] at h1; omega
        have hrec := hrecInv e he hnotT
        split_ifs at hrec ⊢ with heIn
        · obtain ⟨hlo, hhi, val, hpa, hfl, hdet, hgrad, hlen⟩ := hrec
          have hptr : out.mem (tok.edgeRecords + model.extToInt e) =
              afterLoop.mem (tok.edgeRecords + model.extToInt e) := by
            simp [out, Function.update_of_ne hneEr]
          rw [hptr]
          refine ⟨hlo, hhi, val, hpa.congr (fun a halo hahi => by
            simp [out, Function.update_of_ne (show a ≠ root + 11 by omega)]), hfl, hdet, hgrad, hlen⟩
        · obtain ⟨hptr, hcell⟩ := hrec
          refine ⟨by simp [out, Function.update_of_ne hneEr, hptr], fun idx hidx => ?_⟩
          have hne : st.mem (tok.edgeRecords + model.extToInt e) + idx ≠ root + 11 := fun h => by
            have h1 := (t1718 e he).2 hnotT idx hidx; have h2 := t1 11 (by omega); rw [h] at h1; omega
          simp [out, Function.update_of_ne hne, hcell idx hidx],
      fun a ha hne11 h1 h2 h3 => by
        simp only [out, Function.update_of_ne hne11]
        exact hframe0 a ha h1 h2 h3, ?_⟩
    -- Separation of the record blocks: new blocks lie in `[heap₀, curHeap)` and are apart,
    -- old blocks lie below `base ≤ heap₀`.
    intro hsep0 e₁ he₁ e₂ he₂ hne hn₁ hn₂
    have hptr (z : ℕ) (hz : z ∈ model.extG.E) : out.mem (tok.edgeRecords + model.extToInt z) =
        afterLoop.mem (tok.edgeRecords + model.extToInt z) := by
      have hneEr : tok.edgeRecords + model.extToInt z ≠ root + 11 := fun h => by
        have h1 := t13 _ (hedgeAcc.1 z hz).1; have h2 := t1 11 (by omega); rw [h] at h1; omega
      simp [out, Function.update_of_ne hneEr]
    have hold (z : ℕ) (hz : z ∈ model.extG.E)
        (hn : model.extToInt z ∉ model.chain.toTreeChain.chainTree.E) (hzo : z ∉ offRep) :
        afterLoop.mem (tok.edgeRecords + model.extToInt z) = st.mem (tok.edgeRecords + model.extToInt z) := by
      have hrec := hrecInv z hz hn
      rw [if_neg hzo] at hrec
      exact hrec.1
    have hnew (z : ℕ) (hz : z ∈ model.extG.E)
        (hn : model.extToInt z ∉ model.chain.toTreeChain.chainTree.E) (hzo : z ∈ offRep) :
        heap₀ ≤ afterLoop.mem (tok.edgeRecords + model.extToInt z) := by
      have hrec := hrecInv z hz hn
      rw [if_pos hzo] at hrec
      exact hrec.1
    have hlow (z : ℕ) (hz : z ∈ model.extG.E)
        (hn : model.extToInt z ∉ model.chain.toTreeChain.chainTree.E) :
        st.mem (tok.edgeRecords + model.extToInt z) + (2 + 4 * L) ≤ heap₀ := by
      have := hltB ((t1718 z hz).2 hn (1 + 4 * L) (by omega)) (by decide)
      omega
    rw [hptr e₁ he₁, hptr e₂ he₂]
    by_cases h₁ : e₁ ∈ offRep <;> by_cases h₂ : e₂ ∈ offRep
    · exact hsepR e₁ h₁ e₂ h₂ hne
    · rw [hold e₂ he₂ hn₂ h₂]; exact Or.inr ((hlow e₂ he₂ hn₂).trans (hnew e₁ he₁ hn₁ h₁))
    · rw [hold e₁ he₁ hn₁ h₁]; exact Or.inl ((hlow e₁ he₁ hn₁).trans (hnew e₂ he₂ hn₂ h₂))
    · rw [hold e₁ he₁ hn₁ h₁, hold e₂ he₂ hn₂ h₂]; exact hsep0 e₁ he₁ e₂ he₂ hne hn₁ hn₂

end MinCostFlow.MinRatio
