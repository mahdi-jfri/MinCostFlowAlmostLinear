module

public import MinCostFlow.MinRatio.WireSelectEvalKeyLoop
import WordRAM.Tactic
import MinCostFlow.Num.WordBounds

/-!
# Verification of `evalKeyProcBody` and the relocatable deterministic module `evalKeyModule`

This file proves:
1. `evalKeyProc_meetsContract_repaired`: verifies `evalKeyProcBody` against
   `evalCandKeyContractRepaired` using `walkInner_potGrad_eq_chainGrad` (`SelectPotInv`),
   `wlenAt_eq_sum_of_edgeSimple` (`EdgeSimpleEmbeddings`), and `wlenAt_pos_of_pos`.
2. `evalKeyModule_meetsContract_repaired`: wires the full relocatable deterministic 12-procedure
   block `evalKeyModule b h` from a single `p.HasAt b (evalKeyModule b h)` hypothesis, achieving
   step cost `evalKeyCost C.d maxEmbLen mloc.Lk ≤ 600 * (maxEmbLen + 1) * (C.d + 1) * (mloc.Lk + 1) + 240`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 4. Verification of `evalKeyProcBody` and `evalKeyModule` -/

/-- Exact fixed-point fit condition for all candidate keys of `(C, g, ℓ)`: the scaled numerator
and denominator fit in `mloc.Lk` signed `h`-bit limbs at precision `coreLenPrec C.d P pLast lvl`
(`P` on interior levels `< d`, and `P + pLast` on the terminal level `d`). -/
@[expose] def CandidateKeysFit (h P pLast Lk : ℕ) (C : TreeChain) (g ℓ : ℕ → ℝ) : Prop :=
  ∀ lvl ≤ C.d, ∀ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E,
    let Q := coreLenPrec C.d P pLast lvl
    |walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)| * (2 : ℝ) ^ Q <
      (Num.capacity h Lk : ℝ) / 2 ∧
    C.wlenAt ℓ lvl e * (2 : ℝ) ^ Q < (Num.capacity h Lk : ℝ) / 2

private lemma fits_of_mul_pow_lt {h L P : ℕ} {z : ℤ} {r : ℝ}
    (hcast : (z : ℝ) / (2 : ℝ) ^ P = r)
    (hbd : |r| * (2 : ℝ) ^ P < (Num.capacity h L : ℝ) / 2) :
    Num.Fits h L z := by
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
  have hzR : (z : ℝ) = r * (2 : ℝ) ^ P := by
    rw [← hcast, div_mul_cancel₀ _ hP.ne']
  have habs : |(z : ℝ)| < (Num.capacity h L : ℝ) / 2 := by
    rw [hzR, abs_mul, abs_of_pos hP]; exact hbd
  have h2abs : 2 * |(z : ℝ)| < (Num.capacity h L : ℝ) := by linarith
  have hcastAbs : (2 * z : ℤ) < (Num.capacity h L : ℤ) ∧ -(Num.capacity h L : ℤ) ≤ (2 * z : ℤ) := by
    have hlt : ((2 * z : ℤ) : ℝ) < ((Num.capacity h L : ℤ) : ℝ) := by
      push_cast; linarith [le_abs_self (z : ℝ)]
    have hgt : ((-(Num.capacity h L : ℤ) : ℤ) : ℝ) < ((2 * z : ℤ) : ℝ) := by
      push_cast; linarith [neg_le_abs (z : ℝ)]
    exact ⟨Int.cast_lt.mp hlt, le_of_lt (Int.cast_lt.mp hgt)⟩
  exact ⟨hcastAbs.2, hcastAbs.1⟩

/-- `evalKeyProcBody` meets `evalCandKeyContractRepaired` with space
`evalKeySpace C.d maxEmbLen mloc.Lk` and cost `evalKeyCost C.d maxEmbLen mloc.Lk`. -/
theorem evalKeyProc_meetsContract_repaired
    {w h P proc evalEdgePotGrad walkLoop copyTo shiftLeft maxEmbLen : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hh0 : 0 < h) (hw2h : 2 * h + 2 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : C.LastLevelSpans)
    (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f)
    (hEmbBd : ∀ lvl < C.d, ∀ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E,
      (C.activeEmb lvl e).length ≤ maxEmbLen)
    (hFit : CandidateKeysFit h P mloc.pLast mloc.Lk C g ℓ)
    (hp : p.procs[proc]? = some (evalKeyProcBody evalEdgePotGrad walkLoop copyTo shiftLeft))
    (hepg : MeetsContract w p evalEdgePotGrad
      (evalEdgePotGradContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen))
    (hwloop : ∀ W : List (ℕ × Bool), MeetsContract w p walkLoop
      (evalKeyWalkLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen W))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hshift : MeetsContract w p shiftLeft (Num.shiftLeftContract w h)) :
    MeetsContract w p proc
      (evalCandKeyContractRepaired w h P mloc C g ℓ φ coreLen
        (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, e, nDst, dDst, scratch, rfl, hw16, hpLastW, hlvlD, heCand, hndLe, hdsLe, hmetaFull,
    hbd, hz, hroom⟩ := hpre
  have hmeta : SelectLevelMetaReadAt mem mloc h P C g φ coreLen := hmetaFull.toRead
  have hPot : SelectPotInv C g φ := hmetaFull.2.2.2.2.2.2.2.2.2.2.2.1
  have hCLInv : SelectCoreLenInvNext C ℓ coreLen := hmetaFull.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw1 : 1 < 2 ^ w := by omega
  have hbaseLt : Num.base h < 2 ^ w := Num.base_lt_word hw2h
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hnw : nDst < 2 ^ w := hwords nDst (by simp)
  have hdw : dDst < 2 ^ w := hwords dDst (by simp)
  have hLkw : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hmd : mloc.d = C.d := hmeta.1
  have hmD : mem (mloc.metaBase + 1) = mloc.d := hmeta.2.2.1
  have hmsz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmb := hbd.1
  have heCore : e ∈ (C.activeCore lvl).E := (Finset.mem_sdiff.mp heCand).1
  have heG : e ∈ (C.G lvl).E := (Finset.mem_sdiff.mp heCore).1
  have heCap : e < mloc.eCap lvl := (hmeta.2.2.2.2.2.1 lvl hlvlD).2.2.1 e heG
  have heMul : e * mloc.Lk + mloc.Lk ≤ mloc.eCap lvl * mloc.Lk := by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt heCap)
  have hclB := (hbd.2.2.1 lvl hlvlD).2.2
  have hclAddr : mloc.coreLenPtr lvl + e * mloc.Lk + mloc.Lk ≤ scratch := by omega
  have hclPtrEq : mem (mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl)) = mloc.coreLenPtr lvl := by
    simpa [smEntryAddr, smTableOff, Nat.add_assoc] using (hmeta.2.2.2.1 lvl hlvlD).2.2.2.2.1
  have hclAt := hmeta.2.2.2.2.2.2.2.1 lvl hlvlD e heG
  have hembLenLe : (C.activeEmb lvl e).length ≤ maxEmbLen := by
    by_cases hlt : lvl < C.d
    · exact hEmbBd lvl hlt e heCand
    · have hieq : lvl = C.d := Nat.le_antisymm hlvlD (Nat.le_of_not_lt hlt)
      simp [TreeChain.activeEmb, hieq]
  have hspLe : evalKeySpace lvl (C.activeEmb lvl e).length mloc.Lk ≤
      evalKeySpace C.d maxEmbLen mloc.Lk := evalKeySpace_mono hlvlD hembLenLe
  have hcostLe : evalKeyCost lvl (C.activeEmb lvl e).length mloc.Lk ≤
      evalKeyCost C.d maxEmbLen mloc.Lk := evalKeyCost_mono hlvlD hembLenLe
  have hroomLvl : scratch + evalKeySpace lvl (C.activeEmb lvl e).length mloc.Lk < 2 ^ w := by omega
  have hscLk1 : scratch + mloc.Lk < 2 ^ w := by unfold evalKeySpace at hroomLvl; omega
  have hscLk2 : scratch + mloc.Lk + mloc.Lk < 2 ^ w := by unfold evalKeySpace at hroomLvl; omega
  have hscLk3 : scratch + mloc.Lk + mloc.Lk + mloc.Lk < 2 ^ w := by unfold evalKeySpace at hroomLvl; omega
  -- Shared finalization continuation after the `lvl < d` conditional
  have hfinalize : ∀ (scF : ℕ) (memF : ℕ → ℕ) (posF : ℕ) (regsF : ℕ → ℕ) (k0 : ℕ),
      scratch ≤ scF → scF ≤ scratch + evalKeySpace C.d maxEmbLen mloc.Lk →
      scratch + 3 * mloc.Lk ≤ scF →
      regsF 3 = nDst → regsF 4 = dDst → regsF 5 = mloc.Lk →
      regsF 7 = scratch → regsF 8 = scratch + mloc.Lk → regsF 11 = scF →
      Num.Valid memF scratch h mloc.Lk →
      Num.Valid memF (scratch + mloc.Lk) h mloc.Lk →
      Num.intVal memF scratch h mloc.Lk =
        Num.wrap h mloc.Lk ((potGradInt mem mloc h C (lvl + 1) e +
          walkGradSumInt mem mloc h C lvl (C.activeEmb lvl e)) *
          (if lvl < C.d then 1 else (2 : ℤ) ^ mloc.pLast)) →
      Num.intVal memF (scratch + mloc.Lk) h mloc.Lk =
        Num.wrap h mloc.Lk (Num.intVal mem (mloc.coreLenPtr lvl + e * mloc.Lk) h mloc.Lk +
          walkLenSumInt mem mloc h lvl (C.activeEmb lvl e)) →
      ZeroFrom memF scF →
      (∀ a < scratch, memF a = mem a) →
      k0 + 36 * mloc.Lk + 60 ≤ evalKeyCost C.d maxEmbLen mloc.Lk →
      ∃ o st' c, Runs w p ω
        (.call 18 copyTo [.reg 7, .reg 3, .reg 5] ;;
         .call 19 copyTo [.reg 8, .reg 4, .reg 5] ;;
         .ret (.reg 11))
        ⟨memF, regsF, posF⟩ o st' c ∧
        (evalCandKeyContractRepaired w h P mloc C g ℓ φ coreLen
          (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)).post
          [mloc.metaBase, lvl, e, nDst, dDst, mloc.Lk, scratch] mem o.value st'.mem ∧
        k0 + c ≤ (evalCandKeyContractRepaired w h P mloc C g ℓ φ coreLen
          (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)).cost
          [mloc.metaBase, lvl, e, nDst, dDst, mloc.Lk, scratch] mem := by
    intro scF memF posF regsF k0 hscFLo hscFHi hscF3 hr3 hr4 hr5 hr7 hr8 hr11
      hvNF hvDF hNFval hDFval hzF hfrF hk0
    have hscFW : scF < 2 ^ w := by omega
    -- Compute the exact real values of the integer sums
    have hEmbMem : ∀ x ∈ C.activeEmb lvl e, x.1 ∈ (C.G lvl).E := by
      intro x hx
      by_cases hlt : lvl < C.d
      · have hSp := C.activeS_isSparsified hH hlt
        have hxS : x.1 ∈ (C.activeS lvl).E :=
          MGraph.isWalk_edges_mem (hSp.2.1.2 e heCore) x hx
        exact (Finset.mem_sdiff.mp (hSp.1.2.1 hxS)).1
      · have hieq : lvl = C.d := Nat.le_antisymm hlvlD (Nat.le_of_not_lt hlt)
        simp [TreeChain.activeEmb, hieq] at hx
    set Q : ℕ := coreLenPrec C.d P mloc.pLast lvl
    set zN0 : ℤ := potGradInt mem mloc h C (lvl + 1) e +
      walkGradSumInt mem mloc h C lvl (C.activeEmb lvl e)
    set zN : ℤ := zN0 * (if lvl < C.d then 1 else (2 : ℤ) ^ mloc.pLast)
    set zD : ℤ := Num.intVal mem (mloc.coreLenPtr lvl + e * mloc.Lk) h mloc.Lk +
      walkLenSumInt mem mloc h lvl (C.activeEmb lvl e)
    have hzN0Cast : (zN0 : ℝ) / (2 : ℝ) ^ P =
        walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e) := by
      dsimp only [zN0]
      rw [Int.cast_add, add_div, potGradInt_cast hH hmeta hlvlD le_rfl heG,
          walkGradSumInt_cast hH hmeta hlvlD hEmbMem,
          ← walkInner_sparsifierCycle_eq C (potGrad C g φ (lvl + 1)) lvl e]
      exact walkInner_potGrad_eq_chainGrad C hH hSpan φ hlvlD
        (fun j hj => hPot j (le_trans hj hlvlD)) heCand
    have hzNCast : (zN : ℝ) / (2 : ℝ) ^ Q =
        walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e) := by
      dsimp only [zN, Q, coreLenPrec]
      split_ifs with hlt
      · simpa using hzN0Cast
      · have h2l : ((2 : ℝ) ^ mloc.pLast) ≠ 0 := (pow_pos zero_lt_two mloc.pLast).ne'
        rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, pow_add,
          mul_div_mul_right _ _ h2l]
        exact hzN0Cast
    have hzDCast : (zD : ℝ) / (2 : ℝ) ^ Q = C.wlenAt ℓ lvl e := by
      dsimp only [zD]
      have hclEq : ((Num.intVal mem (mloc.coreLenPtr lvl + e * mloc.Lk) h mloc.Lk : ℤ) : ℝ) /
          (2 : ℝ) ^ Q = coreLen lvl e := hclAt.2
      rw [Int.cast_add, add_div, hclEq, walkLenSumInt_cast hmeta hlvlD hEmbMem,
          hCLInv lvl hlvlD e heG, wlenAt_eq_sum_of_edgeSimple hH hlvlD heCand]
      congr 1
      apply congrArg List.sum
      exact List.map_congr_left fun x hx => hCLInv lvl hlvlD x.1 (hEmbMem x hx)
    have hFitN : Num.Fits h mloc.Lk zN :=
      fits_of_mul_pow_lt hzNCast (hFit lvl hlvlD e heCand).1
    have hFitD : Num.Fits h mloc.Lk zD := by
      have hpos := wlenAt_pos_of_pos hH hℓPos hlvlD heCand
      have hbdD := (hFit lvl hlvlD e heCand).2
      rw [← abs_of_pos hpos] at hbdD
      exact fits_of_mul_pow_lt hzDCast hbdD
    have hzDPos : 0 < zD := by
      have hpos := wlenAt_pos_of_pos hH hℓPos hlvlD heCand
      have hQpos : (0 : ℝ) < (2 : ℝ) ^ Q := pow_pos zero_lt_two Q
      have hR : (0 : ℝ) < (zD : ℝ) := by
        have := mul_pos hpos hQpos
        rwa [← hzDCast, div_mul_cancel₀ _ hQpos.ne'] at this
      exact Int.cast_pos.mp hR
    -- Copy `accN` to `nDst`
    refine runs_seq_call_flat hcopy (vs := [scratch, nDst, mloc.Lk])
      (by simp [evalArgs, Expr.eval, hr3, hr5, hr7]) (by wram_words) ?_ ?_
    · exact ⟨scratch, nDst, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
        fun i hi => lt_trans (hvNF i hi) hbaseLt⟩
    · intro _ memG posG hpG
      obtain ⟨_, hcpG, hfrG⟩ := hpG
      change (∀ i < mloc.Lk, memG (nDst + i) = memF (scratch + i)) at hcpG
      change (∀ a, (a < nDst ∨ nDst + mloc.Lk ≤ a) → memG a = memF a) at hfrG
      have hvDG : Num.Valid memG (scratch + mloc.Lk) h mloc.Lk :=
        fun i hi => by rw [hfrG (scratch + mloc.Lk + i) (Or.inr (by omega))]; exact hvDF i hi
      -- Copy `accD` to `dDst`
      refine runs_seq_call_flat hcopy (vs := [scratch + mloc.Lk, dDst, mloc.Lk])
        (by simp [evalArgs, Expr.eval, hr4, hr5, hr8]) (by wram_words) ?_ ?_
      · exact ⟨scratch + mloc.Lk, dDst, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
          fun i hi => lt_trans (hvDG i hi) hbaseLt⟩
      · intro _ memH posH hpH
        obtain ⟨_, hcpH, hfrH⟩ := hpH
        change (∀ i < mloc.Lk, memH (dDst + i) = memG (scratch + mloc.Lk + i)) at hcpH
        change (∀ a, (a < dDst ∨ dDst + mloc.Lk ≤ a) → memH a = memG a) at hfrH
        have hvNH : Num.Valid memH nDst h mloc.Lk := fun i hi => by
          rw [hfrH (nDst + i) (Or.inl (by omega)), hcpG i hi]; exact hvNF i hi
        have hvDH : Num.Valid memH dDst h mloc.Lk := fun i hi => by
          rw [hcpH i hi]; exact hvDG i hi
        have hNHint : Num.intVal memH nDst h mloc.Lk = zN := by
          have h1 : Num.intVal memH nDst h mloc.Lk = Num.intVal memF scratch h mloc.Lk :=
            Num.intVal_congr fun i hi => (hfrH (nDst + i) (Or.inl (by omega))).trans (hcpG i hi)
          rw [h1, hNFval, Num.wrap_of_fits hFitN]
        have hDHint : Num.intVal memH dDst h mloc.Lk = zD := by
          have h1 : Num.intVal memH dDst h mloc.Lk = Num.intVal memF (scratch + mloc.Lk) h mloc.Lk :=
            Num.intVal_congr fun i hi => (hcpH i hi).trans (hfrG (scratch + mloc.Lk + i) (Or.inr (by omega)))
          rw [h1, hDFval, Num.wrap_of_fits hFitD]
        refine WordRAM.runs_ret_le (v := scF) (by simp [Expr.eval, hr11]) ?_ ?_
        · dsimp only [evalCandKeyContractRepaired]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
          refine ⟨hscFLo, hscFHi, hvNH, hvDH,
            fun i hi => lt_trans (hvNH i hi) hbaseLt,
            fun i hi => lt_trans (hvDH i hi) hbaseLt,
            by unfold Num.fixVal; rw [hNHint]; exact hzNCast,
            by unfold Num.fixVal; rw [hDHint]; exact hzDCast,
            by rw [hDHint]; exact hzDPos,
            fun a ha => (hfrH a (Or.inr (by omega))).trans ((hfrG a (Or.inr (by omega))).trans (hzF a ha)),
            fun a ha hnotN hnotD => (hfrH a hnotD).trans ((hfrG a hnotN).trans (hfrF a ha))⟩
        · simp only [evalCandKeyContractRepaired, copyLimbsToContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega
  -- Main body of `evalKeyProcBody`
  apply runs_start_le
  dsimp only [startState]
  unfold evalKeyProcBody
  simp only [smDOff, smTableOff]
  refine runs_seq_assign_flat (v := scratch) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + mloc.Lk) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + mloc.Lk + mloc.Lk) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + mloc.Lk + mloc.Lk + mloc.Lk) (by eval_expr) ?_
  -- Step 1: `evalEdgePotGrad [meta, lvl, e, accN, Lk, sc0]`
  refine runs_seq_call_flat hepg
    (vs := [mloc.metaBase, lvl, e, scratch, mloc.Lk, scratch + mloc.Lk + mloc.Lk + mloc.Lk])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨lvl, e, scratch, scratch + mloc.Lk + mloc.Lk + mloc.Lk, rfl, hw16, hh0, hw2h, hH,
      hlvlD, heG, by omega, hmeta, hbd, fun a ha => hz a (by omega),
      by unfold evalKeySpace at hroomLvl; omega⟩
  · intro sc1 mem1 pos1 hp1
    obtain ⟨hsc1Eq, hvN1, hN1val, hz1, hfr1⟩ := hp1
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc1Eq hN1val hfr1
    have hsc1W : sc1 < 2 ^ w := by unfold evalKeySpace at hroomLvl; omega
    have hfr1Sc : ∀ a < scratch, mem1 a = mem a := fun a ha => hfr1 a (by omega) (Or.inl ha)
    have hmD1 : mem1 (mloc.metaBase + 1) = mloc.d := (hfr1Sc _ (by omega)).trans hmD
    have hclPtr1 : mem1 (mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl)) = mloc.coreLenPtr lvl :=
      (hfr1Sc _ (by omega)).trans hclPtrEq
    refine runs_seq_assign_flat (v := mloc.d) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.coreLenPtr lvl) (by
      have ha1 : mloc.metaBase + 2 < 2 ^ w := by omega
      have ha2 : mloc.d + 1 < 2 ^ w := by omega
      have ha3 : 4 * (mloc.d + 1) < 2 ^ w := by omega
      have ha4 : 4 * (mloc.d + 1) + lvl < 2 ^ w := by omega
      have ha5 : mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl) < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, hw1, show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
        ha1, ha2, ha3, ha4, ha5, hclPtr1]) ?_
    -- Step 2: `copyTo [coreLenPtr[lvl] + e * Lk, accD, Lk]`
    refine runs_seq_call_flat hcopy
      (vs := [mloc.coreLenPtr lvl + e * mloc.Lk, scratch + mloc.Lk, mloc.Lk])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨mloc.coreLenPtr lvl + e * mloc.Lk, scratch + mloc.Lk, mloc.Lk, rfl, hw1,
        by omega, by omega, Or.inl (by omega),
        fun i hi => by
          rw [hfr1Sc (mloc.coreLenPtr lvl + e * mloc.Lk + i) (by omega)]
          exact lt_trans (hclAt.1 i hi) hbaseLt⟩
    · intro _ mem2 pos2 hp2
      obtain ⟨_, hcp2, hfr2⟩ := hp2
      change (∀ i < mloc.Lk, mem2 (scratch + mloc.Lk + i) = mem1 (mloc.coreLenPtr lvl + e * mloc.Lk + i)) at hcp2
      change (∀ a, (a < scratch + mloc.Lk ∨ scratch + mloc.Lk + mloc.Lk ≤ a) → mem2 a = mem1 a) at hfr2
      have hfr2Sc : ∀ a < scratch, mem2 a = mem a := fun a ha =>
        (hfr2 a (Or.inl (by omega))).trans (hfr1Sc a ha)
      have hvN2 : Num.Valid mem2 scratch h mloc.Lk := fun i hi => by
        rw [hfr2 (scratch + i) (Or.inl (by omega))]; exact hvN1 i hi
      have hN2val : Num.intVal mem2 scratch h mloc.Lk =
          Num.wrap h mloc.Lk (potGradInt mem mloc h C (lvl + 1) e) := by
        rw [Num.intVal_congr fun i hi => hfr2 (scratch + i) (Or.inl (by omega)), hN1val]
      have hvD2 : Num.Valid mem2 (scratch + mloc.Lk) h mloc.Lk := fun i hi => by
        rw [hcp2 i hi, hfr1Sc (mloc.coreLenPtr lvl + e * mloc.Lk + i) (by omega)]; exact hclAt.1 i hi
      have hD2val : Num.intVal mem2 (scratch + mloc.Lk) h mloc.Lk =
          Num.intVal mem (mloc.coreLenPtr lvl + e * mloc.Lk) h mloc.Lk :=
        Num.intVal_congr fun i hi => (hcp2 i hi).trans (hfr1Sc (mloc.coreLenPtr lvl + e * mloc.Lk + i) (by omega))
      have hz2 : ZeroFrom mem2 sc1 := fun a ha => (hfr2 a (Or.inr (by omega))).trans (hz1 a ha)
      -- Step 3: branch on `lvl < d`
      by_cases hlt : lvl < C.d
      · have hembB := hbd.2.2.2 lvl hlt
        obtain ⟨_, hembHi, hembBody⟩ := hembB
        obtain ⟨_, _, hwpHi, hWalkAt⟩ := hembBody e heCore
        have hembPtrEq : mem (mloc.metaBase + 2 + (5 * (mloc.d + 1) + lvl)) = mloc.embPtr lvl := by
          simpa [smEntryAddr, smTableOff, Nat.add_assoc] using (hmeta.2.2.2.1 lvl hlvlD).2.2.2.2.2
        have hembPtr2 : mem2 (mloc.metaBase + 2 + (5 * (mloc.d + 1) + lvl)) = mloc.embPtr lvl :=
          (hfr2Sc _ (by omega)).trans hembPtrEq
        have hwp2 : mem2 (mloc.embPtr lvl + e) = mem (mloc.embPtr lvl + e) :=
          hfr2Sc _ (by omega)
        have hlen2 : mem2 (mem (mloc.embPtr lvl + e)) = (C.activeEmb lvl e).length := by
          have hEncLen := mWalkEncode_length (C.activeEmb lvl e)
          exact (hfr2Sc _ (by omega)).trans (MWalkAt_head hWalkAt)
        have hWalk2 : MWalkAt mem2 (mem (mloc.embPtr lvl + e)) (C.activeEmb lvl e) :=
          hWalkAt.of_agree fun a _ ha => by
            have hEncLen := mWalkEncode_length (C.activeEmb lvl e)
            exact hfr2Sc a (by omega)
        have hEmbMem : ∀ x ∈ C.activeEmb lvl e, x.1 ∈ (C.G lvl).E := by
          intro x hx
          have hSp := C.activeS_isSparsified hH hlt
          have hxS : x.1 ∈ (C.activeS lvl).E := MGraph.isWalk_edges_mem (hSp.2.1.2 e heCore) x hx
          exact (Finset.mem_sdiff.mp (hSp.1.2.1 hxS)).1
        have hwpW : mem (mloc.embPtr lvl + e) < 2 ^ w := by omega
        have hlenW : (C.activeEmb lvl e).length < 2 ^ w := by
          have hEncLen := mWalkEncode_length (C.activeEmb lvl e); omega
        refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hmd, hlt, hw1])
          ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := mloc.embPtr lvl) (by
          have ha1 : mloc.metaBase + 2 < 2 ^ w := by omega
          have ha2 : mloc.d + 1 < 2 ^ w := by omega
          have ha3 : 5 * (mloc.d + 1) < 2 ^ w := by omega
          have ha4 : 5 * (mloc.d + 1) + lvl < 2 ^ w := by omega
          have ha5 : mloc.metaBase + 2 + (5 * (mloc.d + 1) + lvl) < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, hw1, show 2 < 2 ^ w by omega, show 5 < 2 ^ w by omega,
            ha1, ha2, ha3, ha4, ha5, hembPtr2]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := mem (mloc.embPtr lvl + e)) (by eval_expr) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := (C.activeEmb lvl e).length) (by eval_expr) ?_
        refine runs_seq_call_flat (hwloop (C.activeEmb lvl e))
          (vs := [mloc.metaBase, lvl, mem (mloc.embPtr lvl + e), (C.activeEmb lvl e).length, 0,
            scratch, scratch + mloc.Lk, scratch + mloc.Lk + mloc.Lk, mloc.Lk, sc1])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨lvl, mem (mloc.embPtr lvl + e), 0, scratch, scratch + mloc.Lk,
            scratch + mloc.Lk + mloc.Lk, sc1, rfl, hw16, hh0, hw2h, hH, hlvlD, Nat.zero_le _,
            hEmbMem, hWalk2, hwpHi, by omega, by omega, by omega,
            selectLevelMetaReadAt_of_agree hmeta hbd hfr2Sc,
            selectLevelMetaBounded_of_agree hbd hfr2Sc, hvN2, hvD2, hz2,
            by rw [Nat.sub_zero]; unfold evalKeySpace at hroomLvl; omega⟩
        · intro scF memF posF hpF
          obtain ⟨hloF, hhiF, hvNF, hvDF, hNFval, hDFval, hzF, hfrF⟩ := hpF
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.drop_zero, Nat.sub_zero] at hloF hhiF hNFval hDFval hfrF
          have hgs2 : walkGradSumInt mem2 mloc h C lvl (C.activeEmb lvl e) =
              walkGradSumInt mem mloc h C lvl (C.activeEmb lvl e) :=
            walkGradSumInt_congr hH hmeta hbd hfr2Sc hlvlD hEmbMem
          have hls2 : walkLenSumInt mem2 mloc h lvl (C.activeEmb lvl e) =
              walkLenSumInt mem mloc h lvl (C.activeEmb lvl e) :=
            walkLenSumInt_congr hmeta hbd hfr2Sc hlvlD hEmbMem
          apply hfinalize scF memF posF _ _ (by omega)
            (by
              have h1 : evalKeySpace lvl (C.activeEmb lvl e).length mloc.Lk =
                  4 * mloc.Lk + evalEdgePotGradSpace lvl mloc.Lk +
                    evalKeyWalkLoopSpace (C.activeEmb lvl e).length lvl mloc.Lk := rfl
              omega) (by omega)
            (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hvNF hvDF
            (by simp only [hlt, ↓reduceIte, mul_one]; rw [hNFval, hN2val, hgs2, wrap_add_left])
            (by rw [hDFval, hD2val, hls2])
            hzF (fun a ha => (hfrF a ha).trans (hfr2Sc a ha))
            (by
              simp only [evalEdgePotGradContract, evalKeyWalkLoopContract, copyLimbsToContract,
                List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, Expr.size, argsSize] at *
              have h1 : evalKeyCost lvl (C.activeEmb lvl e).length mloc.Lk =
                  evalEdgePotGradCostExact lvl mloc.Lk +
                    evalKeyWalkLoopCost (C.activeEmb lvl e).length lvl mloc.Lk + 120 * mloc.Lk + 380 := rfl
              omega)
      · have hieq : lvl = C.d := Nat.le_antisymm hlvlD (Nat.le_of_not_lt hlt)
        have hembNil : C.activeEmb lvl e = [] := by simp [TreeChain.activeEmb, hieq]
        have hpLastEq : mem (mloc.metaBase + 2 + (7 * (mloc.d + 1) + mloc.d)) = mloc.pLast := by
          simpa [smEntryAddr, smTableOff, Nat.add_assoc] using hmeta.2.2.2.2.2.2.2.2.2
        have hpLast2 : mem2 (mloc.metaBase + 2 + (7 * (mloc.d + 1) + mloc.d)) = mloc.pLast :=
          (hfr2Sc _ (by omega)).trans hpLastEq
        -- `potGradInt` fits before shifting left by `pLast` because `2^P ≤ 2^(P + pLast)`.
        have hFitN0 : Num.Fits h mloc.Lk (potGradInt mem mloc h C (lvl + 1) e) := by
          have hcast0 : ((potGradInt mem mloc h C (lvl + 1) e : ℤ) : ℝ) / (2 : ℝ) ^ P =
              walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e) := by
            rw [potGradInt_cast hH hmeta hlvlD le_rfl heG,
                ← walkInner_potGrad_eq_chainGrad C hH hSpan φ hlvlD
                  (fun j hj => hPot j (le_trans hj hlvlD)) heCand,
                walkInner_sparsifierCycle_eq, hembNil]
            simp
          have hbd := (hFit lvl hlvlD e heCand).1
          simp only [coreLenPrec, hlt, ↓reduceIte] at hbd
          have hpowLe : (2 : ℝ) ^ P ≤ (2 : ℝ) ^ (P + mloc.pLast) :=
            pow_le_pow_right₀ (by norm_num) (Nat.le_add_right P mloc.pLast)
          have hbdP : |walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)| * (2 : ℝ) ^ P <
              (Num.capacity h mloc.Lk : ℝ) / 2 :=
            lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpowLe (abs_nonneg _)) hbd
          exact fits_of_mul_pow_lt hcast0 hbdP
        refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hmd, hlt, show 0 < 2 ^ w by omega])
          (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := mloc.pLast) (by
          have ha1 : mloc.metaBase + 2 < 2 ^ w := by omega
          have ha2 : mloc.d + 1 < 2 ^ w := by omega
          have ha3 : 7 * (mloc.d + 1) < 2 ^ w := by omega
          have ha4 : 7 * (mloc.d + 1) + mloc.d < 2 ^ w := by omega
          have ha5 : mloc.metaBase + 2 + (7 * (mloc.d + 1) + mloc.d) < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, hw1, show 2 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
            ha1, ha2, ha3, ha4, ha5, hpLast2]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := sc1) (by eval_expr) ?_
        refine runs_seq_assoc_le ?_
        have hsc2W : sc1 + mloc.Lk < 2 ^ w := by
          unfold evalKeySpace at hroomLvl; omega
        refine runs_seq_call_flat hshift (vs := [scratch, mloc.Lk, mloc.pLast, sc1])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨scratch, mloc.Lk, mloc.pLast, sc1, rfl, by omega, hvN2⟩, hz2, hsc2W⟩
        · intro sc2 mem3 pos3 hp3
          obtain ⟨hsc2Eq, hlo3, hhi3, hfr3, hz3, hvS3, hS3val⟩ := hp3
          change sc2 = sc1 + mloc.Lk at hsc2Eq
          change ∀ a < sc1, mem3 a = mem2 a at hfr3
          change ZeroFrom mem3 sc2 at hz3
          change Num.Valid mem3 sc1 h mloc.Lk at hvS3
          change Num.intVal mem3 sc1 h mloc.Lk =
            Num.wrap h mloc.Lk (Num.intVal mem2 scratch h mloc.Lk * (2 : ℤ) ^ mloc.pLast) at hS3val
          refine runs_seq_call_flat hcopy (vs := [sc1, scratch, mloc.Lk])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨sc1, scratch, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
              fun i hi => lt_trans (hvS3 i hi) hbaseLt⟩
          · intro _ mem4 pos4 hp4
            obtain ⟨_, hcp4, hfr4⟩ := hp4
            change ∀ i < mloc.Lk, mem4 (scratch + i) = mem3 (sc1 + i) at hcp4
            change ∀ a, (a < scratch ∨ scratch + mloc.Lk ≤ a) → mem4 a = mem3 a at hfr4
            have hfr4Sc : ∀ a < scratch, mem4 a = mem a := fun a ha =>
              (hfr4 a (Or.inl ha)).trans ((hfr3 a (by omega)).trans (hfr2Sc a ha))
            have hvN4 : Num.Valid mem4 scratch h mloc.Lk := fun i hi => by
              rw [hcp4 i hi]; exact hvS3 i hi
            have hvD4 : Num.Valid mem4 (scratch + mloc.Lk) h mloc.Lk := fun i hi => by
              rw [hfr4 _ (Or.inr (by omega)), hfr3 _ (by omega)]; exact hvD2 i hi
            have hN4val : Num.intVal mem4 scratch h mloc.Lk =
                Num.wrap h mloc.Lk ((potGradInt mem mloc h C (lvl + 1) e +
                  walkGradSumInt mem mloc h C lvl (C.activeEmb lvl e)) *
                  (if lvl < C.d then 1 else (2 : ℤ) ^ mloc.pLast)) := by
              rw [Num.intVal_congr hcp4, hS3val, hN2val, Num.wrap_of_fits hFitN0]
              simp [hembNil, hlt, walkGradSumInt]
            have hD4val : Num.intVal mem4 (scratch + mloc.Lk) h mloc.Lk =
                Num.wrap h mloc.Lk (Num.intVal mem (mloc.coreLenPtr lvl + e * mloc.Lk) h mloc.Lk +
                  walkLenSumInt mem mloc h lvl (C.activeEmb lvl e)) := by
              have hEq : Num.intVal mem4 (scratch + mloc.Lk) h mloc.Lk =
                  Num.intVal mem2 (scratch + mloc.Lk) h mloc.Lk :=
                Num.intVal_congr fun i hi => (hfr4 _ (Or.inr (by omega))).trans (hfr3 _ (by omega))
              rw [hEq, hembNil]; unfold walkLenSumInt
              rw [add_zero, hD2val, Num.wrap_of_fits (Num.intVal_fits hclAt.1)]
            have hz4 : ZeroFrom mem4 sc2 := fun a ha => (hfr4 a (Or.inr (by omega))).trans (hz3 a ha)
            apply hfinalize sc2 mem4 pos4 _ _ (by omega)
              (by
                have h1 : evalKeySpace lvl (C.activeEmb lvl e).length mloc.Lk =
                    4 * mloc.Lk + evalEdgePotGradSpace lvl mloc.Lk +
                      evalKeyWalkLoopSpace (C.activeEmb lvl e).length lvl mloc.Lk := rfl
                omega) (by omega)
              (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hvN4 hvD4
              hN4val hD4val hz4 hfr4Sc
              (by
                simp only [evalEdgePotGradContract, copyLimbsToContract, Num.shiftLeftContract,
                  heapContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize] at *
                have h1 : evalKeyCost lvl (C.activeEmb lvl e).length mloc.Lk =
                    evalEdgePotGradCostExact lvl mloc.Lk +
                      evalKeyWalkLoopCost (C.activeEmb lvl e).length lvl mloc.Lk + 120 * mloc.Lk + 380 := rfl
                omega)

/-- **Main theorem for `evalKeyModule b h`**: placing the relocatable deterministic 14-procedure
block `evalKeyModule b h` at `b` in `p` gives a procedure at `b` meeting
`evalCandKeyContractRepaired` with space `evalKeySpace C.d maxEmbLen mloc.Lk` and cost
`evalKeyCost C.d maxEmbLen mloc.Lk ≤ 600 * (maxEmbLen + 1) * (C.d + 1) * (mloc.Lk + 1) + 400`. -/
theorem evalKeyModule_meetsContract_repaired
    {w h P b maxEmbLen : ℕ} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hh0 : 0 < h) (hw2h : 2 * h + 2 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : C.LastLevelSpans)
    (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f)
    (hEmbBd : ∀ lvl < C.d, ∀ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E,
      (C.activeEmb lvl e).length ≤ maxEmbLen)
    (hFit : CandidateKeysFit h P mloc.pLast mloc.Lk C g ℓ)
    (hAt : p.HasAt b (evalKeyModule b h)) :
    MeetsContract w p b
      (evalCandKeyContractRepaired w h P mloc C g ℓ φ coreLen
        (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)) := by
  have hproc : ∀ k (hk : k < 14), p.procs[b + k]? = some ((evalKeyModule b h)[k]'(by rw [evalKeyModule_length]; exact hk)) :=
    fun k hk => hAt k (by rw [evalKeyModule_length]; exact hk)
  have h0 : p.procs[b]? = some (evalKeyProcBody (b + 1) (b + 3) (b + 4) (b + 12)) := by
    simpa [evalKeyModule] using hproc 0 (by decide)
  have h1 : p.procs[b + 1]? = some (evalEdgePotGradBody (b + 2) (b + 4)) := by
    simpa [evalKeyModule] using hproc 1 (by decide)
  have h2 : p.procs[b + 2]? = some (evalEdgePotGradLoopBody (b + 2) (b + 4) (b + 5) (b + 7)) := by
    simpa [evalKeyModule] using hproc 2 (by decide)
  have h3 : p.procs[b + 3]? = some (evalKeyWalkLoopBody (b + 3) (b + 1) (b + 4) (b + 5) (b + 7)) := by
    simpa [evalKeyModule] using hproc 3 (by decide)
  have h4 : p.procs[b + 4]? = some copyLimbsToBody := by
    simpa [evalKeyModule] using hproc 4 (by decide)
  have haddAt : p.HasAt (b + 5) (Num.addModule (b + 5) h) := by
    intro i hi
    have hi2 : i < 2 := by simpa [Num.addModule] using hi
    have hp := hproc (5 + i) (by omega)
    rw [show b + 5 + i = b + (5 + i) by omega, hp]
    congr 1
    rcases i with _ | _ | i
    · rfl
    · rfl
    · omega
  have hsubAt : p.HasAt (b + 7) (Num.subtractModule (b + 7) h) := by
    intro i hi
    have hi5 : i < 5 := by simpa [Num.subtractModule, Num.negateModule, Num.addModule] using hi
    have hp := hproc (7 + i) (by omega)
    rw [show b + 7 + i = b + (7 + i) by omega, hp]
    congr 1
    rcases i with _ | _ | _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  have hshAt : p.HasAt (b + 12) (Num.shiftLeftModule (b + 12) h) := by
    intro i hi
    have hi2 : i < 2 := by simpa [Num.shiftLeftModule] using hi
    have hp := hproc (12 + i) (by omega)
    rw [show b + 12 + i = b + (12 + i) by omega, hp]
    congr 1
    rcases i with _ | _ | i
    · rfl
    · rfl
    · omega
  have hcopy := copyLimbsTo_meetsContract (w := w) h4
  have hadd := Num.add_meetsContract hh0 hw2h haddAt
  have hsub := Num.subtract_meetsContract hh0 hw2h hsubAt
  have hsh := Num.shiftLeft_meetsContract hh0 hw2h hshAt
  have hloop := evalEdgePotGradLoop_meetsContract (P := P) (mloc := mloc) (C := C) (G := G)
    (g := g) (ℓ := ℓ) (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c) (φ := φ)
    (coreLen := coreLen) h2 hcopy hadd hsub
  have hepg := evalEdgePotGrad_meetsContract h1 hloop hcopy
  have hwloop : ∀ W : List (ℕ × Bool), MeetsContract w p (b + 3)
      (evalKeyWalkLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen W) :=
    fun W => evalKeyWalkLoop_meetsContract h3 hepg hcopy hadd hsub
  exact evalKeyProc_meetsContract_repaired hh0 hw2h hH hSpan hℓPos hEmbBd hFit h0 hepg hwloop hcopy hsh

end MinCostFlow.MinRatio
