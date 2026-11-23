module

public import MinCostFlow.MinRatio.WireSelectEvalKeyMath
import WordRAM.Tactic
import MinCostFlow.Num.WordBounds

/-!
# Verification of `evalEdgePotGradLoopBody` and `evalEdgePotGradBody`

Verifies `evalEdgePotGradLoopBody` and `evalEdgePotGradBody` (`WireSelectKeyEval.lean`) in
`evalEdgePotGradCostExact lvl Lk = O((lvl + 1) · Lk)` steps and
`evalEdgePotGradSpace lvl Lk = (lvl + 1) * (3 * Lk)` scratch words, computing
`Num.wrap h Lk (potGradInt mem mloc h C (lvl + 1) f)`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-- Contract for `evalEdgePotGradLoopBody` (`[meta, lvl, f, dstPtr, Lk, cur, scratch]`). -/
def evalEdgePotGradLoopContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ)
    (φ coreLen : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ lvl f dstPtr cur scratch,
      args = [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, cur, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      lvl ≤ C.d ∧ cur ≤ lvl + 1 ∧ f ∈ (C.G lvl).E ∧
      dstPtr + mloc.Lk ≤ scratch ∧
      SelectLevelMetaReadAt mem mloc h P C g φ coreLen ∧
      SelectLevelMetaBounded mem mloc C dstPtr ∧
      Num.Valid mem dstPtr h mloc.Lk ∧
      Num.intVal mem dstPtr h mloc.Lk = Num.wrap h mloc.Lk (potGradInt mem mloc h C cur f) ∧
      ZeroFrom mem scratch ∧ scratch + (lvl + 1 - cur) * (3 * mloc.Lk) < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let f := args.getD 2 0
    let dstPtr := args.getD 3 0
    let cur := args.getD 5 0
    let scratch := args.getD 6 0
    ret = scratch + (lvl + 1 - cur) * (3 * mloc.Lk) ∧
    Num.Valid mem' dstPtr h mloc.Lk ∧
    Num.intVal mem' dstPtr h mloc.Lk = Num.wrap h mloc.Lk (potGradInt mem mloc h C (lvl + 1) f) ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem' a = mem a)
  cost args _ := evalEdgePotGradLoopCost (args.getD 1 0 + 1 - args.getD 5 0) mloc.Lk

/-- Contract for `evalEdgePotGradBody` (`[meta, lvl, f, dstPtr, Lk, scratch]`). -/
def evalEdgePotGradContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ)
    (φ coreLen : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ lvl f dstPtr scratch,
      args = [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      lvl ≤ C.d ∧ f ∈ (C.G lvl).E ∧
      dstPtr + mloc.Lk ≤ scratch ∧
      SelectLevelMetaReadAt mem mloc h P C g φ coreLen ∧
      SelectLevelMetaBounded mem mloc C dstPtr ∧
      ZeroFrom mem scratch ∧ scratch + evalEdgePotGradSpace lvl mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let f := args.getD 2 0
    let dstPtr := args.getD 3 0
    let scratch := args.getD 5 0
    ret = scratch + evalEdgePotGradSpace lvl mloc.Lk ∧
    Num.Valid mem' dstPtr h mloc.Lk ∧
    Num.intVal mem' dstPtr h mloc.Lk = Num.wrap h mloc.Lk (potGradInt mem mloc h C (lvl + 1) f) ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem' a = mem a)
  cost args _ := evalEdgePotGradCostExact (args.getD 1 0) mloc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Verification of `evalEdgePotGradLoopBody` and `evalEdgePotGradBody` -/

/-- `evalEdgePotGradLoopBody` meets `evalEdgePotGradLoopContract` in `O((lvl + 1 - cur) · Lk)`
steps and `(lvl + 1 - cur) * (3 * Lk)` scratch words. -/
theorem evalEdgePotGradLoop_meetsContract {w h P self copyTo addProc subProc : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[self]? = some (evalEdgePotGradLoopBody self copyTo addProc subProc))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hadd : MeetsContract w p addProc (Num.addContract w h))
    (hsub : MeetsContract w p subProc (Num.subtractContract w h)) :
    MeetsContract w p self
      (evalEdgePotGradLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0 + 1 - args.getD 5 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨lvl, f, dstPtr, cur, scratch, rfl, hw16, hh0, hw2h, hH, hlvlD, hcurLe, hfG,
    hdstLe, hmeta, hbd, hvdst, hdstVal, hz, hroom⟩ := hpre
  change lvl + 1 - cur = rem at hremEq
  subst hremEq
  have hw1 : 1 < 2 ^ w := by omega
  have hbaseLt : Num.base h < 2 ^ w := Num.base_lt_word hw2h
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hfw : f < 2 ^ w := hwords f (by simp)
  have hdstw : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hLkw : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hcurw : cur < 2 ^ w := hwords cur (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold evalEdgePotGradLoopBody
  simp only [smDOff, smTableOff]
  by_cases hgt : lvl < cur
  · have hcurEq : cur = lvl + 1 := by omega
    have hrem0 : lvl + 1 - cur = 0 := by omega
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hgt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [evalEdgePotGradLoopContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hrem0, Nat.zero_mul,
        Nat.add_zero]
      exact ⟨trivial, hvdst, by rwa [hcurEq] at hdstVal, hz, fun _ _ _ => trivial⟩
    · simp only [evalEdgePotGradLoopContract, evalEdgePotGradLoopCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]; omega
  · have hcurLvl : cur ≤ lvl := by omega
    have hcurD : cur ≤ C.d := le_trans hcurLvl hlvlD
    have hmetaKeep := hmeta
    have hbdKeep := hbd
    obtain ⟨hmd, _, hmD, hmTab, _, hGAt, hPhiAt, _, _⟩ := hmeta
    obtain ⟨hmb, hg0b, hlevb, _⟩ := hbd
    have htab := hmTab cur hcurD
    have hcurB := hlevb cur hcurD
    have hGcur := hGAt cur hcurD
    have hPhicur := hPhiAt cur hcurD
    have hfcur : f ∈ (C.G cur).E := C.G_E_subset_of_le hH hcurLvl hlvlD hfG
    have hfEcap : f < mloc.eCap cur := hGcur.2.2.1 f hfcur
    have hvalF := C.G_isValid hH cur hcurD f hfcur
    have htCap : (C.G cur).tail f < mloc.vCap cur := hGcur.2.1 _ hvalF.1
    have hhCap : (C.G cur).head f < mloc.vCap cur := hGcur.2.1 _ hvalF.2
    have hends := dynGraphAt_read_endpoints hGcur hfcur
    have htslotLt : mem (dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) < mloc.vCap cur := by
      have hth := hGcur.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfcur
      rw [hth.1]
      exact hGcur.2.1 _ (hGcur.2.2.2.2.2.2.2.2.2.1 _ hvalF.1).1
    have hhslotLt : mem (dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) < mloc.vCap cur := by
      have hth := hGcur.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfcur
      rw [hth.2]
      exact hGcur.2.1 _ (hGcur.2.2.2.2.2.2.2.2.2.1 _ hvalF.2).1
    have hmsz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have hgsz : dynGraphSize (mloc.vCap cur) (mloc.eCap cur) =
        4 + 7 * mloc.vCap cur + 9 * mloc.eCap cur := rfl
    have hGP : mem (mloc.metaBase + 2 + cur) = mloc.GPtr cur := by
      simpa [smEntryAddr, smTableOff] using htab.1
    have hvC : mem (mloc.metaBase + 2 + ((mloc.d + 1) + cur)) = mloc.vCap cur := by
      simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htab.2.1
    have heC : mem (mloc.metaBase + 2 + (2 * (mloc.d + 1) + cur)) = mloc.eCap cur := by
      simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htab.2.2.1
    have hpP : mem (mloc.metaBase + 2 + (3 * (mloc.d + 1) + cur)) = mloc.phiPtr cur := by
      simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htab.2.2.2.1
    have hheadMul : (C.G cur).head f * mloc.Lk + mloc.Lk ≤ mloc.vCap cur * mloc.Lk := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hhCap)
    have htailMul : (C.G cur).tail f * mloc.Lk + mloc.Lk ≤ mloc.vCap cur * mloc.Lk := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt htCap)
    have hspSplit : 3 * mloc.Lk + (lvl + 1 - (cur + 1)) * (3 * mloc.Lk) =
        (lvl + 1 - cur) * (3 * mloc.Lk) := by
      have h1 : lvl + 1 - cur = (lvl + 1 - (cur + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcostSplit : (130 * mloc.Lk + 240) + evalEdgePotGradLoopCost (lvl + 1 - (cur + 1)) mloc.Lk =
        evalEdgePotGradLoopCost (lvl + 1 - cur) mloc.Lk := by
      unfold evalEdgePotGradLoopCost
      have h1 : lvl + 1 - cur = (lvl + 1 - (cur + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul]
      omega
    have hsc3 : scratch + 3 * mloc.Lk < 2 ^ w := by omega
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hgt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_assign_flat (v := mloc.d) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.d + 1) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.vCap cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.eCap cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.phiPtr cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr cur + 4 + 4 * mloc.vCap cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := (C.G cur).tail f) (by
      have htEq : mem (mloc.GPtr cur + 4 + 4 * mloc.vCap cur +
          mem (mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + f)) = (C.G cur).tail f := by
        simpa [dgIntToExtBase, dgETailSlotBase] using hends.1
      have hts : mloc.GPtr cur + 4 + 4 * mloc.vCap cur +
          mem (mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + f) < 2 ^ w := by
        simpa [dgETailSlotBase] using (show mloc.GPtr cur + 4 + 4 * mloc.vCap cur +
          mem (dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) < 2 ^ w by omega)
      eval_expr) ?_
    refine runs_seq_assign_flat (v := (C.G cur).head f) (by
      have hhEq : mem (mloc.GPtr cur + 4 + 4 * mloc.vCap cur +
          mem (mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur + f)) =
          (C.G cur).head f := by
        have hbase : mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur =
            dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) := by
          unfold dgEHeadSlotBase; omega
        rw [hbase]; simpa [dgIntToExtBase] using hends.2
      have hhs : mloc.GPtr cur + 4 + 4 * mloc.vCap cur +
          mem (mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur + f) < 2 ^ w := by
        have hbase : mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur =
            dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) := by
          unfold dgEHeadSlotBase; omega
        rw [hbase]; omega
      eval_expr) ?_
    have hphiHeadAddr : mloc.phiPtr cur + (C.G cur).head f * mloc.Lk + mloc.Lk ≤ dstPtr := by omega
    have hphiTailAddr : mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk + mloc.Lk ≤ dstPtr := by omega
    -- Call 1: `addProc [dstPtr, phiPtr[cur] + head * Lk, Lk, scratch]`
    refine runs_seq_call_flat hadd
      (vs := [dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, scratch, rfl,
        ⟨⟨dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, 0, scratch, rfl,
          by omega, by omega, by decide, hvdst, (hPhicur _ hvalF.2).1⟩, hz,
          by change scratch + mloc.Lk < 2 ^ w; omega⟩⟩
    · intro sc1 mem1 pos1 hp1
      rcases hp1 with ⟨hsc1Eq, _, _, hfr1, hz1, hlist1⟩
      change sc1 = scratch + mloc.Lk at hsc1Eq
      change (∀ x < scratch, mem1 x = mem x) at hfr1
      change ListAt mem1 scratch
        (Num.digits h mloc.Lk
          (Num.unsignedVal mem dstPtr h mloc.Lk +
            Num.unsignedVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk + 0)) at hlist1
      have haddVal := Num.addCarry_value hlist1
      have hsc1W : sc1 < 2 ^ w := by omega
      have hphiTailV1 : Num.Valid mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk :=
        fun i hi => by
          rw [hfr1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk + i) (by omega)]
          exact (hPhicur _ hvalF.1).1 i hi
      -- Call 2: `subProc [scratch, phiPtr[cur] + tail * Lk, Lk, sc1]`
      refine runs_seq_call_flat hsub
        (vs := [scratch, mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk, mloc.Lk, sc1])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨scratch, mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk, mloc.Lk, sc1, rfl,
          by omega, by omega, haddVal.1, hphiTailV1⟩, hz1, by change sc1 + 2 * mloc.Lk < 2 ^ w; omega⟩
      · intro sc2 mem2 pos2 hp2
        rcases hp2 with ⟨hsc2Eq, _, _, hfr2, hz2, hvSub, hsubVal⟩
        change sc2 = sc1 + 2 * mloc.Lk at hsc2Eq
        change (∀ x < sc1, mem2 x = mem1 x) at hfr2
        change Num.Valid mem2 (sc1 + mloc.Lk) h mloc.Lk at hvSub
        change Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk =
          Num.wrap h mloc.Lk (Num.intVal mem1 scratch h mloc.Lk -
            Num.intVal mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk) at hsubVal
        have hsc2W : sc2 < 2 ^ w := by omega
        -- Call 3: `copyTo [sc1 + Lk, dstPtr, Lk]`
        refine runs_seq_call_flat hcopy (vs := [sc1 + mloc.Lk, dstPtr, mloc.Lk])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨sc1 + mloc.Lk, dstPtr, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
            fun i hi => lt_trans (hvSub i hi) hbaseLt⟩
        · intro _ mem3 pos3 hp3
          obtain ⟨_, hcp3, hfr3⟩ := hp3
          change (∀ i < mloc.Lk, mem3 (dstPtr + i) = mem2 (sc1 + mloc.Lk + i)) at hcp3
          change (∀ a, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
          have hagDst : ∀ a < dstPtr, mem3 a = mem a := fun a ha =>
            (hfr3 a (Or.inl ha)).trans ((hfr2 a (by omega)).trans (hfr1 a (by omega)))
          have hfr3_out : ∀ a < scratch, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem3 a = mem a :=
            fun a ha hout => (hfr3 a hout).trans ((hfr2 a (by omega)).trans (hfr1 a ha))
          have hvdst3 : Num.Valid mem3 dstPtr h mloc.Lk :=
            fun i hi => by rw [hcp3 i hi]; exact hvSub i hi
          have hdstVal3 : Num.intVal mem3 dstPtr h mloc.Lk =
              Num.wrap h mloc.Lk (potGradInt mem3 mloc h C (cur + 1) f) := by
            have h1 : Num.intVal mem3 dstPtr h mloc.Lk = Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk :=
              Num.intVal_congr hcp3
            have htailEq : Num.intVal mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk =
                Num.intVal mem (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk :=
              Num.intVal_congr fun i hi => hfr1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk + i) (by omega)
            rw [h1, hsubVal, haddVal.2, hdstVal, htailEq]
            simp only [Int.natCast_zero, add_zero]
            rw [wrap_add_left, wrap_sub_left]
            have hpgEq : potGradInt mem3 mloc h C (cur + 1) f = potGradInt mem mloc h C (cur + 1) f :=
              potGradInt_congr hH hmetaKeep hbdKeep hagDst hlvlD (by omega) hfG
            rw [hpgEq]; rfl
          have hz3 : ZeroFrom mem3 sc2 := fun a ha => (hfr3 a (Or.inr (by omega))).trans (hz2 a ha)
          have hmeta3 : SelectLevelMetaReadAt mem3 mloc h P C g φ coreLen :=
            selectLevelMetaReadAt_of_agree hmetaKeep hbdKeep hagDst
          have hbd3 : SelectLevelMetaBounded mem3 mloc C dstPtr :=
            selectLevelMetaBounded_of_agree hbdKeep hagDst
          have hcur1W : cur + 1 < 2 ^ w := by omega
          -- Call 4: recursive call on `cur + 1`, `sc2`
          refine runs_seq_call_flat ih
            (vs := [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, cur + 1, sc2])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨lvl, f, dstPtr, cur + 1, sc2, rfl, hw16, hh0, hw2h, hH, hlvlD, by omega,
              hfG, by omega, hmeta3, hbd3, hvdst3, hdstVal3, hz3, by omega⟩,
              by change lvl + 1 - (cur + 1) < lvl + 1 - cur; omega⟩
          · intro ret mem4 pos4 hp4
            obtain ⟨hretEq, hvdst4, hdstVal4, hz4, hfr4⟩ := hp4
            simp only [List.getD_cons_zero, List.getD_cons_succ] at hretEq hdstVal4 hfr4
            have hretW : ret < 2 ^ w := by omega
            have hpgFinal : potGradInt mem3 mloc h C (lvl + 1) f =
                potGradInt mem mloc h C (lvl + 1) f :=
              potGradInt_congr hH hmetaKeep hbdKeep hagDst hlvlD le_rfl hfG
            refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
            · dsimp only [evalEdgePotGradLoopContract]
              simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
              refine ⟨by omega, hvdst4, by rwa [← hpgFinal], hz4, fun a ha hout => ?_⟩
              exact (hfr4 a (by omega) hout).trans (hfr3_out a ha hout)
            · simp only [Contract.below, evalEdgePotGradLoopContract, Num.addContract,
                Num.subtractContract, heapContract, copyLimbsToContract, List.getD_cons_zero,
                List.getD_cons_succ, Expr.size, argsSize]
              omega

/-- `evalEdgePotGradBody` meets `evalEdgePotGradContract` in `evalEdgePotGradCostExact lvl Lk`
steps (`O((lvl + 1) · Lk)`) and `evalEdgePotGradSpace lvl Lk` scratch words. -/
theorem evalEdgePotGrad_meetsContract {w h P proc loopProc copyTo : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (evalEdgePotGradBody loopProc copyTo))
    (hloop : MeetsContract w p loopProc
      (evalEdgePotGradLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc
      (evalEdgePotGradContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, f, dstPtr, scratch, rfl, hw16, hh0, hw2h, hH, hlvlD, hfG, hdstLe, hmeta, hbd,
    hz, hroom⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hbaseLt : Num.base h < 2 ^ w := Num.base_lt_word hw2h
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hfw : f < 2 ^ w := hwords f (by simp)
  have hdstw : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hLkw : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le lvl) hlvlD hfG
  have hfcap0 : f < mloc.eCap 0 := (hmeta.2.2.2.2.2.1 0 (Nat.zero_le _)).2.2.1 f hf0
  have hmul0 : f * mloc.Lk + mloc.Lk ≤ mloc.eCap 0 * mloc.Lk := by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hfcap0)
  have hg0Addr : mloc.g0Ptr + f * mloc.Lk + mloc.Lk ≤ dstPtr := by have := hbd.2.1; omega
  have hg0Val := hmeta.2.2.2.2.1 f hf0
  have hmG0 : mem (mloc.metaBase + 0) = mloc.g0Ptr := hmeta.2.1
  have hmsz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmb := hbd.1
  apply runs_start_le
  dsimp only [startState]
  unfold evalEdgePotGradBody
  simp only [smG0Off]
  refine runs_seq_assign_flat (v := mloc.g0Ptr) (by eval_expr) ?_
  refine runs_seq_call_flat hcopy
    (vs := [mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk, rfl, hw1, by omega, by omega,
      Or.inl hg0Addr, fun i hi => lt_trans (hg0Val.1 i hi) hbaseLt⟩
  · intro _ mem1 pos1 hp1
    obtain ⟨_, hcp1, hfr1⟩ := hp1
    change (∀ i < mloc.Lk, mem1 (dstPtr + i) = mem (mloc.g0Ptr + f * mloc.Lk + i)) at hcp1
    change (∀ a, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem1 a = mem a) at hfr1
    have hagDst : ∀ a < dstPtr, mem1 a = mem a := fun a ha => hfr1 a (Or.inl ha)
    have hvdst1 : Num.Valid mem1 dstPtr h mloc.Lk :=
      fun i hi => (hcp1 i hi).symm ▸ hg0Val.1 i hi
    have hdstVal1 : Num.intVal mem1 dstPtr h mloc.Lk =
        Num.wrap h mloc.Lk (potGradInt mem1 mloc h C 0 f) := by
      have h1 : Num.intVal mem1 dstPtr h mloc.Lk = Num.intVal mem (mloc.g0Ptr + f * mloc.Lk) h mloc.Lk :=
        Num.intVal_congr hcp1
      have h2 : potGradInt mem1 mloc h C 0 f = Num.intVal mem (mloc.g0Ptr + f * mloc.Lk) h mloc.Lk :=
        potGradInt_congr hH hmeta hbd hagDst hlvlD (Nat.zero_le _) hfG
      rw [h1, h2, Num.wrap_of_fits (Num.intVal_fits hg0Val.1)]
    have hz1 : ZeroFrom mem1 scratch := fun a ha => (hfr1 a (Or.inr (by omega))).trans (hz a ha)
    have hmeta1 : SelectLevelMetaReadAt mem1 mloc h P C g φ coreLen :=
      selectLevelMetaReadAt_of_agree hmeta hbd hagDst
    have hbd1 : SelectLevelMetaBounded mem1 mloc C dstPtr :=
      selectLevelMetaBounded_of_agree hbd hagDst
    refine runs_seq_call_flat hloop
      (vs := [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, 0, scratch]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨lvl, f, dstPtr, 0, scratch, rfl, hw16, hh0, hw2h, hH, hlvlD, Nat.zero_le _, hfG,
        hdstLe, hmeta1, hbd1, hvdst1, hdstVal1, hz1, by simpa [evalEdgePotGradSpace] using hroom⟩
    · intro ret mem2 pos2 hp2
      obtain ⟨hretEq, hvdst2, hdstVal2, hz2, hfr2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero] at hretEq hdstVal2 hfr2
      have hretW : ret < 2 ^ w := by unfold evalEdgePotGradSpace at hroom; omega
      have hpgEq : potGradInt mem1 mloc h C (lvl + 1) f = potGradInt mem mloc h C (lvl + 1) f :=
        potGradInt_congr hH hmeta hbd hagDst hlvlD le_rfl hfG
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [evalEdgePotGradContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        refine ⟨by simpa [evalEdgePotGradSpace] using hretEq, hvdst2, by rwa [← hpgEq], hz2,
          fun a ha hout => (hfr2 a ha hout).trans (hfr1 a hout)⟩
      · simp only [evalEdgePotGradContract, evalEdgePotGradCostExact, evalEdgePotGradLoopContract,
          evalEdgePotGradLoopCost, copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Nat.sub_zero, Expr.size, argsSize]
        omega

end MinCostFlow.MinRatio
