module

public import MinCostFlow.MinRatio.WireSelectEvalKeyPotGrad
import WordRAM.Tactic
import MinCostFlow.Num.WordBounds

/-!
# Verification of `evalKeyWalkLoopBody`

Defines `walkGradSumInt`, `walkLenSumInt`, and `evalKeyWalkLoopContract`, proves their congruence
and real-cast lemmas, and verifies `evalKeyWalkLoopBody` in `evalKeyWalkLoopCost` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Exact integer walk sums and contract for `evalKeyWalkLoopBody` -/

/-- Exact integer-scaled signed sum of `potGrad C g φ (lvl + 1)` over the reversed steps of `P`. -/
def walkGradSumInt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h : ℕ) (C : TreeChain)
    (lvl : ℕ) : List (ℕ × Bool) → ℤ
  | [] => 0
  | x :: xs =>
    (if x.2 then -potGradInt mem mloc h C (lvl + 1) x.1
     else potGradInt mem mloc h C (lvl + 1) x.1) +
    walkGradSumInt mem mloc h C lvl xs

/-- Exact integer-scaled sum of `coreLen lvl` over the edges of `P`. -/
def walkLenSumInt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h : ℕ) (lvl : ℕ) :
    List (ℕ × Bool) → ℤ
  | [] => 0
  | x :: xs =>
    Num.intVal mem (mloc.coreLenPtr lvl + x.1 * mloc.Lk) h mloc.Lk +
    walkLenSumInt mem mloc h lvl xs

/-- Contract for `evalKeyWalkLoopBody`
(`args = [meta, lvl, walkPtr, P.length, idx, accN, accD, tmpG, Lk, scratch]`). -/
def evalKeyWalkLoopContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ)
    (φ coreLen : ℕ → ℕ → ℝ) (W : List (ℕ × Bool)) : Contract where
  pre args mem :=
    ∃ lvl walkPtr idx accN accD tmpG scratch,
      args = [mloc.metaBase, lvl, walkPtr, W.length, idx, accN, accD, tmpG, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      lvl ≤ C.d ∧ idx ≤ W.length ∧
      (∀ x ∈ W, x.1 ∈ (C.G lvl).E) ∧
      MWalkAt mem walkPtr W ∧
      walkPtr + (mWalkEncode W).length ≤ accN ∧
      accN + mloc.Lk ≤ accD ∧ accD + mloc.Lk ≤ tmpG ∧ tmpG + mloc.Lk ≤ scratch ∧
      SelectLevelMetaReadAt mem mloc h P C g φ coreLen ∧
      SelectLevelMetaBounded mem mloc C accN ∧
      Num.Valid mem accN h mloc.Lk ∧ Num.Valid mem accD h mloc.Lk ∧
      ZeroFrom mem scratch ∧
      scratch + evalKeyWalkLoopSpace (W.length - idx) lvl mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let idx := args.getD 4 0
    let accN := args.getD 5 0
    let accD := args.getD 6 0
    let scratch := args.getD 9 0
    scratch ≤ ret ∧ ret ≤ scratch + evalKeyWalkLoopSpace (W.length - idx) lvl mloc.Lk ∧
    Num.Valid mem' accN h mloc.Lk ∧ Num.Valid mem' accD h mloc.Lk ∧
    Num.intVal mem' accN h mloc.Lk =
      Num.wrap h mloc.Lk (Num.intVal mem accN h mloc.Lk +
        walkGradSumInt mem mloc h C lvl (W.drop idx)) ∧
    Num.intVal mem' accD h mloc.Lk =
      Num.wrap h mloc.Lk (Num.intVal mem accD h mloc.Lk +
        walkLenSumInt mem mloc h lvl (W.drop idx)) ∧
    ZeroFrom mem' ret ∧
    (∀ a < accN, mem' a = mem a)
  cost args _ := evalKeyWalkLoopCost (W.length - args.getD 4 0) (args.getD 1 0) mloc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 2. Congruence and real-cast lemmas for `walkGradSumInt` and `walkLenSumInt` -/

theorem walkGradSumInt_congr {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P hi : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    (hb : SelectLevelMetaBounded mem mloc C hi)
    (hag : ∀ a < hi, mem' a = mem a)
    {lvl : ℕ} (hlvl : lvl ≤ C.d) {W : List (ℕ × Bool)} (hW : ∀ x ∈ W, x.1 ∈ (C.G lvl).E) :
    walkGradSumInt mem' mloc h C lvl W = walkGradSumInt mem mloc h C lvl W := by
  induction W with
  | nil => rfl
  | cons x xs ih =>
    unfold walkGradSumInt
    have hx := potGradInt_congr hH hm hb hag hlvl le_rfl (hW x List.mem_cons_self)
    rw [hx, ih (fun y hy => hW y (List.mem_cons_of_mem _ hy))]

theorem walkLenSumInt_congr {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P hi : ℕ}
    {C : TreeChain} {g : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    (hb : SelectLevelMetaBounded mem mloc C hi)
    (hag : ∀ a < hi, mem' a = mem a)
    {lvl : ℕ} (hlvl : lvl ≤ C.d) {W : List (ℕ × Bool)} (hW : ∀ x ∈ W, x.1 ∈ (C.G lvl).E) :
    walkLenSumInt mem' mloc h lvl W = walkLenSumInt mem mloc h lvl W := by
  induction W with
  | nil => rfl
  | cons x xs ih =>
    unfold walkLenSumInt
    have hxf : x.1 ∈ (C.G lvl).E := hW x List.mem_cons_self
    have hxcap : x.1 < mloc.eCap lvl := (hm.2.2.2.2.2.1 lvl hlvl).2.2.1 x.1 hxf
    have hmul : x.1 * mloc.Lk + mloc.Lk ≤ mloc.eCap lvl * mloc.Lk := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hxcap)
    have hclb := (hb.2.2.1 lvl hlvl).2.2
    have h1 : Num.intVal mem' (mloc.coreLenPtr lvl + x.1 * mloc.Lk) h mloc.Lk =
        Num.intVal mem (mloc.coreLenPtr lvl + x.1 * mloc.Lk) h mloc.Lk :=
      Num.intVal_congr fun i hiL => hag _ (by omega)
    rw [h1, ih (fun y hy => hW y (List.mem_cons_of_mem _ hy))]

theorem walkGradSumInt_cast {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    {lvl : ℕ} (hlvl : lvl ≤ C.d) {W : List (ℕ × Bool)} (hW : ∀ x ∈ W, x.1 ∈ (C.G lvl).E) :
    ((walkGradSumInt mem mloc h C lvl W : ℤ) : ℝ) / (2 : ℝ) ^ P =
      (W.map fun x => if x.2 then -potGrad C g φ (lvl + 1) x.1
        else potGrad C g φ (lvl + 1) x.1).sum := by
  induction W with
  | nil => simp [walkGradSumInt]
  | cons x xs ih =>
    unfold walkGradSumInt
    rw [Int.cast_add, add_div, ih (fun y hy => hW y (List.mem_cons_of_mem _ hy))]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    have hc := potGradInt_cast hH hm hlvl le_rfl (hW x List.mem_cons_self)
    cases hx2 : x.2
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hc
    · simp only [↓reduceIte, Int.cast_neg, neg_div]; rw [hc]

theorem walkLenSumInt_cast {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P : ℕ}
    {C : TreeChain} {g : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    {lvl : ℕ} (hlvl : lvl ≤ C.d) {W : List (ℕ × Bool)} (hW : ∀ x ∈ W, x.1 ∈ (C.G lvl).E) :
    ((walkLenSumInt mem mloc h lvl W : ℤ) : ℝ) / (2 : ℝ) ^ (coreLenPrec C.d P mloc.pLast lvl) =
      (W.map fun x => coreLen lvl x.1).sum := by
  induction W with
  | nil => simp [walkLenSumInt]
  | cons x xs ih =>
    unfold walkLenSumInt
    rw [Int.cast_add, add_div, ih (fun y hy => hW y (List.mem_cons_of_mem _ hy))]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    exact (hm.2.2.2.2.2.2.2.1 lvl hlvl x.1 (hW x List.mem_cons_self)).2

/-! ## 3. Verification of `evalKeyWalkLoopBody` -/

/-- `evalKeyWalkLoopBody` meets `evalKeyWalkLoopContract` in `evalKeyWalkLoopCost` steps. -/
theorem evalKeyWalkLoop_meetsContract {w h P self evalEdgePotGrad copyTo addProc subProc : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ coreLen : ℕ → ℕ → ℝ} {W : List (ℕ × Bool)} {p : Program}
    (hp : p.procs[self]? = some (evalKeyWalkLoopBody self evalEdgePotGrad copyTo addProc subProc))
    (hepg : MeetsContract w p evalEdgePotGrad
      (evalEdgePotGradContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hadd : MeetsContract w p addProc (Num.addContract w h))
    (hsub : MeetsContract w p subProc (Num.subtractContract w h)) :
    MeetsContract w p self
      (evalKeyWalkLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen W) := by
  apply meetsContract_of_rec (fun args _ => W.length - args.getD 4 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨lvl, walkPtr, idx, accN, accD, tmpG, scratch, rfl, hw16, hh0, hw2h, hH, hlvlD, hidxLe,
    hWmem, hWalkAt, hwpBd, hND, hDT, hTS, hmeta, hbd, hvN, hvD, hz, hroom⟩ := hpre
  change W.length - idx = rem at hremEq
  subst hremEq
  have hw1 : 1 < 2 ^ w := by omega
  have hbaseLt : Num.base h < 2 ^ w := Num.base_lt_word hw2h
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hwpw : walkPtr < 2 ^ w := hwords walkPtr (by simp)
  have hlenw : W.length < 2 ^ w := hwords W.length (by simp)
  have hidxw : idx < 2 ^ w := hwords idx (by simp)
  have haccNw : accN < 2 ^ w := hwords accN (by simp)
  have haccDw : accD < 2 ^ w := hwords accD (by simp)
  have htmpGw : tmpG < 2 ^ w := hwords tmpG (by simp)
  have hLkw : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold evalKeyWalkLoopBody
  simp only [smDOff, smTableOff]
  by_cases hlt : idx < W.length
  · have hstepEdge := MWalkAt_step_edge hWalkAt hlt
    have hstepDir := MWalkAt_step_dir hWalkAt hlt
    have hEncLen : (mWalkEncode W).length = 1 + 2 * W.length := mWalkEncode_length W
    have hfG : W[idx].1 ∈ (C.G lvl).E := hWmem W[idx] (List.getElem_mem hlt)
    have hfCap : W[idx].1 < mloc.eCap lvl := (hmeta.2.2.2.2.2.1 lvl hlvlD).2.2.1 _ hfG
    have hfMul : W[idx].1 * mloc.Lk + mloc.Lk ≤ mloc.eCap lvl * mloc.Lk := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hfCap)
    have hclB := (hbd.2.2.1 lvl hlvlD).2.2
    have hclAddr : mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk + mloc.Lk ≤ accN := by omega
    have hmsz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have hmb := hbd.1
    have hmd : mloc.d = C.d := hmeta.1
    have hmD : mem (mloc.metaBase + 1) = mloc.d := hmeta.2.2.1
    have hclPtrEq : mem (mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl)) = mloc.coreLenPtr lvl := by
      simpa [smEntryAddr, smTableOff, Nat.add_assoc] using (hmeta.2.2.2.1 lvl hlvlD).2.2.2.2.1
    have hfw : W[idx].1 < 2 ^ w := by
      have hgsz : dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) =
          4 + 7 * mloc.vCap lvl + 9 * mloc.eCap lvl := rfl
      have := (hbd.2.2.1 lvl hlvlD).1
      omega
    have hdirW : (if W[idx].2 then 1 else 0) < 2 ^ w := by split <;> omega
    have hspSplit : evalKeyStepSpace lvl mloc.Lk +
        evalKeyWalkLoopSpace (W.length - (idx + 1)) lvl mloc.Lk =
        evalKeyWalkLoopSpace (W.length - idx) lvl mloc.Lk := by
      unfold evalKeyWalkLoopSpace
      have h1 : W.length - idx = (W.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcostSplit : (evalKeyStepCost lvl mloc.Lk + 40) +
        evalKeyWalkLoopCost (W.length - (idx + 1)) lvl mloc.Lk =
        evalKeyWalkLoopCost (W.length - idx) lvl mloc.Lk := by
      unfold evalKeyWalkLoopCost
      have h1 : W.length - idx = (W.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul]
      omega
    have hstepSp : evalEdgePotGradSpace lvl mloc.Lk + 3 * mloc.Lk = evalKeyStepSpace lvl mloc.Lk := rfl
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := W[idx].1) (by
      have h1 : walkPtr + 1 + 2 * idx < 2 ^ w := by omega
      eval_expr) ?_
    refine runs_seq_assign_flat (v := if W[idx].2 then 1 else 0) (by
      have h1 : walkPtr + 2 + 2 * idx = walkPtr + 1 + 2 * idx + 1 := by omega
      have h2 : walkPtr + 2 + 2 * idx < 2 ^ w := by omega
      have h3 : mem (walkPtr + 2 + 2 * idx) = if W[idx].2 then 1 else 0 := by rw [h1]; exact hstepDir
      eval_expr) ?_
    -- Call 1: `evalEdgePotGrad [meta, lvl, W[idx].1, tmpG, Lk, scratch]`
    refine runs_seq_call_flat hepg
      (vs := [mloc.metaBase, lvl, W[idx].1, tmpG, mloc.Lk, scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨lvl, W[idx].1, tmpG, scratch, rfl, hw16, hh0, hw2h, hH, hlvlD, hfG, hTS,
        hmeta, selectLevelMetaBounded_mono hbd (by omega), hz, by omega⟩
    · intro sc1 mem1 pos1 hp1
      obtain ⟨hsc1Eq, hvTmp1, htmpVal1, hz1, hfr1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc1Eq htmpVal1 hfr1
      have hsc1W : sc1 < 2 ^ w := by omega
      have hvN1 : Num.Valid mem1 accN h mloc.Lk := fun i hi => by
        rw [hfr1 (accN + i) (by omega) (Or.inl (by omega))]; exact hvN i hi
      have hvD1 : Num.Valid mem1 accD h mloc.Lk := fun i hi => by
        rw [hfr1 (accD + i) (by omega) (Or.inl (by omega))]; exact hvD i hi
      have hN1eq : Num.intVal mem1 accN h mloc.Lk = Num.intVal mem accN h mloc.Lk :=
        Num.intVal_congr fun i hi => hfr1 (accN + i) (by omega) (Or.inl (by omega))
      have hD1eq : Num.intVal mem1 accD h mloc.Lk = Num.intVal mem accD h mloc.Lk :=
        Num.intVal_congr fun i hi => hfr1 (accD + i) (by omega) (Or.inl (by omega))
      -- Continuation after updating `accN` (shared by both `dir = 1` and `dir = 0` branches)
      have hcontAfterN : ∀ (sc2 : ℕ) (mem2 : ℕ → ℕ) (pos2 : ℕ) (regs2 : ℕ → ℕ) (k0 : ℕ),
          sc1 ≤ sc2 → sc2 ≤ sc1 + 2 * mloc.Lk →
          regs2 0 = mloc.metaBase → regs2 1 = lvl → regs2 2 = walkPtr →
          regs2 3 = W.length → regs2 4 = idx → regs2 5 = accN → regs2 6 = accD →
          regs2 7 = tmpG → regs2 8 = mloc.Lk → regs2 10 = W[idx].1 → regs2 13 = sc2 →
          Num.Valid mem2 accN h mloc.Lk →
          Num.intVal mem2 accN h mloc.Lk =
            Num.wrap h mloc.Lk (Num.intVal mem accN h mloc.Lk +
              (if W[idx].2 then -potGradInt mem mloc h C (lvl + 1) W[idx].1
               else potGradInt mem mloc h C (lvl + 1) W[idx].1)) →
          ZeroFrom mem2 sc2 →
          (∀ a < accN, mem2 a = mem a) →
          (∀ i < mloc.Lk, mem2 (accD + i) = mem (accD + i)) →
          k0 + 56 * mloc.Lk + evalKeyWalkLoopCost (W.length - (idx + 1)) lvl mloc.Lk + 100 ≤
            evalKeyWalkLoopCost (W.length - idx) lvl mloc.Lk →
          ∃ o st' c, Runs w p ω
            (.assign 15 (.load (.bin .add (.reg 0) (.const 1))) ;;
             .assign 16 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
               (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 15) (.const 1))) (.reg 1)))) ;;
             .call 17 addProc [.reg 6, .bin .add (.reg 16) (.bin .mul (.reg 10) (.reg 8)), .reg 8, .reg 13] ;;
             .call 18 copyTo [.reg 13, .reg 6, .reg 8] ;;
             .call 19 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1),
               .reg 5, .reg 6, .reg 7, .reg 8, .reg 17] ;;
             .ret (.reg 19))
            ⟨mem2, regs2, pos2⟩ o st' c ∧
            (evalKeyWalkLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen W).post
              [mloc.metaBase, lvl, walkPtr, W.length, idx, accN, accD, tmpG, mloc.Lk, scratch]
              mem o.value st'.mem ∧
            k0 + c ≤ (evalKeyWalkLoopContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen W).cost
              [mloc.metaBase, lvl, walkPtr, W.length, idx, accN, accD, tmpG, mloc.Lk, scratch] mem := by
        intro sc2 mem2 pos2 regs2 k0 hsc2Lo hsc2Hi hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr10 hr13
          hvN2 hN2val hz2 hfr2A hD2cp hk0
        have hsc2W : sc2 < 2 ^ w := by omega
        have hmD2 : mem2 (mloc.metaBase + 1) = mloc.d := (hfr2A _ (by omega)).trans hmD
        have hclPtr2 : mem2 (mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl)) = mloc.coreLenPtr lvl :=
          (hfr2A _ (by omega)).trans hclPtrEq
        have hvD2 : Num.Valid mem2 accD h mloc.Lk := fun i hi => by rw [hD2cp i hi]; exact hvD i hi
        have hclAt := hmeta.2.2.2.2.2.2.2.1 lvl hlvlD W[idx].1 hfG
        have hvCL2 : Num.Valid mem2 (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk :=
          fun i hi => by
            rw [hfr2A (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk + i) (by omega)]
            exact hclAt.1 i hi
        refine runs_seq_assign_flat (v := mloc.d)
          (by simp [Expr.eval, BinOp.eval, hr0, hw1, show mloc.metaBase + 1 < 2 ^ w by omega, hmD2]) ?_
        refine runs_seq_assign_flat (v := mloc.coreLenPtr lvl)
          (by
            have ha1 : mloc.metaBase + 2 < 2 ^ w := by omega
            have ha2 : mloc.d + 1 < 2 ^ w := by omega
            have ha3 : 4 * (mloc.d + 1) < 2 ^ w := by omega
            have ha4 : 4 * (mloc.d + 1) + lvl < 2 ^ w := by omega
            have ha5 : mloc.metaBase + 2 + (4 * (mloc.d + 1) + lvl) < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, hr0, hr1, show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
              hw1, ha1, ha2, ha3, ha4, ha5, hclPtr2]) ?_
        -- Call `addProc [accD, coreLenPtr[lvl] + f * Lk, Lk, sc2]`
        refine runs_seq_call_flat hadd
          (vs := [accD, mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk, mloc.Lk, sc2])
          (by
            have hm1 : W[idx].1 * mloc.Lk < 2 ^ w := by omega
            have hm2 : mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk < 2 ^ w := by omega
            simp [evalArgs, Expr.eval, BinOp.eval, hr6, hr8, hr10, hr13, hm1, hm2])
          (by wram_words) ?_ ?_
        · exact ⟨accD, mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk, mloc.Lk, sc2, rfl,
            ⟨⟨accD, mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk, mloc.Lk, 0, sc2, rfl,
              by omega, by omega, by decide, hvD2, hvCL2⟩, hz2, by change sc2 + mloc.Lk < 2 ^ w; omega⟩⟩
        · intro sc3 mem3 pos3 hp3
          rcases hp3 with ⟨hsc3Eq, _, _, hfr3, hz3, hlist3⟩
          change sc3 = sc2 + mloc.Lk at hsc3Eq
          change (∀ x < sc2, mem3 x = mem2 x) at hfr3
          change ListAt mem3 sc2
            (Num.digits h mloc.Lk
              (Num.unsignedVal mem2 accD h mloc.Lk +
                Num.unsignedVal mem2 (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk + 0)) at hlist3
          have haddD := Num.addCarry_value hlist3
          have hsc3W : sc3 < 2 ^ w := by omega
          -- Call `copyTo [sc2, accD, Lk]`
          refine runs_seq_call_flat hcopy (vs := [sc2, accD, mloc.Lk])
            (by simp [evalArgs, Expr.eval, hr6, hr8, hr13]) (by wram_words) ?_ ?_
          · exact ⟨sc2, accD, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
              fun i hi => lt_trans (haddD.1 i hi) hbaseLt⟩
          · intro _ mem4 pos4 hp4
            obtain ⟨_, hcp4, hfr4⟩ := hp4
            change (∀ i < mloc.Lk, mem4 (accD + i) = mem3 (sc2 + i)) at hcp4
            change (∀ a, (a < accD ∨ accD + mloc.Lk ≤ a) → mem4 a = mem3 a) at hfr4
            have hagAccN : ∀ a < accN, mem4 a = mem a := fun a ha =>
              (hfr4 a (Or.inl (by omega))).trans ((hfr3 a (by omega)).trans (hfr2A a ha))
            have hvN4 : Num.Valid mem4 accN h mloc.Lk := fun i hi => by
              rw [hfr4 (accN + i) (Or.inl (by omega)), hfr3 (accN + i) (by omega)]; exact hvN2 i hi
            have hvD4 : Num.Valid mem4 accD h mloc.Lk := fun i hi => by rw [hcp4 i hi]; exact haddD.1 i hi
            have hN4eq : Num.intVal mem4 accN h mloc.Lk = Num.intVal mem2 accN h mloc.Lk :=
              Num.intVal_congr fun i hi => (hfr4 (accN + i) (Or.inl (by omega))).trans (hfr3 (accN + i) (by omega))
            have hD4val : Num.intVal mem4 accD h mloc.Lk =
                Num.wrap h mloc.Lk (Num.intVal mem accD h mloc.Lk +
                  Num.intVal mem (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk) := by
              have h1 : Num.intVal mem4 accD h mloc.Lk = Num.intVal mem3 sc2 h mloc.Lk :=
                Num.intVal_congr hcp4
              have h2 : Num.intVal mem2 accD h mloc.Lk = Num.intVal mem accD h mloc.Lk :=
                Num.intVal_congr hD2cp
              have h3 : Num.intVal mem2 (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk =
                  Num.intVal mem (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk :=
                Num.intVal_congr fun i hi => hfr2A (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk + i) (by omega)
              rw [h1, haddD.2, h2, h3]
              simp only [Int.natCast_zero, add_zero]
            have hz4 : ZeroFrom mem4 sc3 := fun a ha => (hfr4 a (Or.inr (by omega))).trans (hz3 a ha)
            have hWalk4 : MWalkAt mem4 walkPtr W :=
              hWalkAt.of_agree fun a _ ha => hagAccN a (by omega)
            have hmeta4 : SelectLevelMetaReadAt mem4 mloc h P C g φ coreLen :=
              selectLevelMetaReadAt_of_agree hmeta hbd hagAccN
            have hbd4 : SelectLevelMetaBounded mem4 mloc C accN :=
              selectLevelMetaBounded_of_agree hbd hagAccN
            have hidx1W : idx + 1 < 2 ^ w := by omega
            -- Recursive call on `idx + 1`, `sc3`
            refine runs_seq_call_flat ih
              (vs := [mloc.metaBase, lvl, walkPtr, W.length, idx + 1, accN, accD, tmpG, mloc.Lk, sc3])
              (by simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8,
                hw1, hidx1W]) (by wram_words) ?_ ?_
            · exact ⟨⟨lvl, walkPtr, idx + 1, accN, accD, tmpG, sc3, rfl, hw16, hh0, hw2h, hH, hlvlD,
                by omega, hWmem, hWalk4, hwpBd, hND, hDT, by omega, hmeta4, hbd4, hvN4, hvD4, hz4,
                by omega⟩, by change W.length - (idx + 1) < W.length - idx; omega⟩
            · intro ret mem5 pos5 hp5
              obtain ⟨hlo5, hhi5, hvN5, hvD5, hN5val, hD5val, hz5, hfr5⟩ := hp5
              simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo5 hhi5 hN5val hD5val hfr5
              have hretW : ret < 2 ^ w := by omega
              have hdropEq : W.drop idx = W[idx] :: W.drop (idx + 1) := List.drop_eq_getElem_cons hlt
              have hDropMem : ∀ y ∈ W.drop (idx + 1), y.1 ∈ (C.G lvl).E :=
                fun y hy => hWmem y (List.mem_of_mem_drop hy)
              have hgs4 : walkGradSumInt mem4 mloc h C lvl (W.drop (idx + 1)) =
                  walkGradSumInt mem mloc h C lvl (W.drop (idx + 1)) :=
                walkGradSumInt_congr hH hmeta hbd hagAccN hlvlD hDropMem
              have hls4 : walkLenSumInt mem4 mloc h lvl (W.drop (idx + 1)) =
                  walkLenSumInt mem mloc h lvl (W.drop (idx + 1)) :=
                walkLenSumInt_congr hmeta hbd hagAccN hlvlD hDropMem
              refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
              · dsimp only [evalKeyWalkLoopContract]
                simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
                refine ⟨by omega, by omega, hvN5, hvD5, ?_, ?_, hz5, fun a ha => (hfr5 a ha).trans (hagAccN a ha)⟩
                · rw [hN5val, hN4eq, hN2val, hgs4, wrap_add_left, hdropEq]
                  have hdef : walkGradSumInt mem mloc h C lvl (W[idx] :: W.drop (idx + 1)) =
                      (if W[idx].2 then -potGradInt mem mloc h C (lvl + 1) W[idx].1
                       else potGradInt mem mloc h C (lvl + 1) W[idx].1) +
                      walkGradSumInt mem mloc h C lvl (W.drop (idx + 1)) := rfl
                  rw [hdef]; congr 1; ring
                · rw [hD5val, hD4val, hls4, wrap_add_left, hdropEq]
                  have hdef : walkLenSumInt mem mloc h lvl (W[idx] :: W.drop (idx + 1)) =
                      Num.intVal mem (mloc.coreLenPtr lvl + W[idx].1 * mloc.Lk) h mloc.Lk +
                      walkLenSumInt mem mloc h lvl (W.drop (idx + 1)) := rfl
                  rw [hdef]; congr 1; ring
              · simp only [Contract.below, evalKeyWalkLoopContract, Num.addContract,
                  copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
                omega
      -- Branch on `W[idx].2` (`1` = subtract `tmpG` from `accN`, `0` = add `tmpG` to `accN`)
      cases hdir : W[idx].2
      · -- `W[idx].2 = false` (`dir = 0`): add `tmpG` to `accN`
        refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval])
          (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_call_flat hadd (vs := [accN, tmpG, mloc.Lk, sc1])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨accN, tmpG, mloc.Lk, sc1, rfl,
            ⟨⟨accN, tmpG, mloc.Lk, 0, sc1, rfl, by omega, by omega, by decide, hvN1, hvTmp1⟩,
              hz1, by change sc1 + mloc.Lk < 2 ^ w; omega⟩⟩
        · intro sc2 mem2 pos2 hp2
          rcases hp2 with ⟨hsc2Eq, _, _, hfr2, hz2, hlist2⟩
          change sc2 = sc1 + mloc.Lk at hsc2Eq
          change (∀ x < sc1, mem2 x = mem1 x) at hfr2
          change ListAt mem2 sc1
            (Num.digits h mloc.Lk
              (Num.unsignedVal mem1 accN h mloc.Lk +
                Num.unsignedVal mem1 tmpG h mloc.Lk + 0)) at hlist2
          have haddN := Num.addCarry_value hlist2
          have hsc2W : sc2 < 2 ^ w := by omega
          refine runs_seq_call_flat hcopy (vs := [sc1, accN, mloc.Lk])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨sc1, accN, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
              fun i hi => lt_trans (haddN.1 i hi) hbaseLt⟩
          · intro _ mem3 pos3 hp3
            obtain ⟨_, hcp3, hfr3⟩ := hp3
            change (∀ i < mloc.Lk, mem3 (accN + i) = mem2 (sc1 + i)) at hcp3
            change (∀ a, (a < accN ∨ accN + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
            apply hcontAfterN sc2 mem3 pos3 _ _ (by omega) (by omega)
              (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (by simp)
              (fun i hi => (hcp3 i hi).symm ▸ haddN.1 i hi)
              (by
                have h1 : Num.intVal mem3 accN h mloc.Lk = Num.intVal mem2 sc1 h mloc.Lk := Num.intVal_congr hcp3
                rw [h1, haddN.2, hN1eq, htmpVal1]
                simp only [Int.natCast_zero, add_zero, hdir, Bool.false_eq_true, ↓reduceIte, Num.wrap_add_wrap])
              (fun a ha => (hfr3 a (Or.inr (by omega))).trans (hz2 a ha))
              (fun a ha => (hfr3 a (Or.inl ha)).trans ((hfr2 a (by omega)).trans (hfr1 a (by omega) (Or.inl (by omega)))))
              (fun i hi => (hfr3 (accD + i) (Or.inr (by omega))).trans ((hfr2 (accD + i) (by omega)).trans (hfr1 (accD + i) (by omega) (Or.inl (by omega)))))
              (by
                simp only [evalEdgePotGradContract, Num.addContract, copyLimbsToContract,
                  evalKeyStepCost, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize] at *
                omega)
      · -- `W[idx].2 = true` (`dir = 1`): subtract `tmpG` from `accN`
        refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval])
          ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_call_flat hsub (vs := [accN, tmpG, mloc.Lk, sc1])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨accN, tmpG, mloc.Lk, sc1, rfl, by omega, by omega, hvN1, hvTmp1⟩,
            hz1, by change sc1 + 2 * mloc.Lk < 2 ^ w; omega⟩
        · intro sc2 mem2 pos2 hp2
          rcases hp2 with ⟨hsc2Eq, _, _, hfr2, hz2, hvSub, hsubVal⟩
          change sc2 = sc1 + 2 * mloc.Lk at hsc2Eq
          change (∀ x < sc1, mem2 x = mem1 x) at hfr2
          change Num.Valid mem2 (sc1 + mloc.Lk) h mloc.Lk at hvSub
          change Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk =
            Num.wrap h mloc.Lk (Num.intVal mem1 accN h mloc.Lk -
              Num.intVal mem1 tmpG h mloc.Lk) at hsubVal
          have hsc2W : sc2 < 2 ^ w := by omega
          refine runs_seq_call_flat hcopy (vs := [sc1 + mloc.Lk, accN, mloc.Lk])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨sc1 + mloc.Lk, accN, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
              fun i hi => lt_trans (hvSub i hi) hbaseLt⟩
          · intro _ mem3 pos3 hp3
            obtain ⟨_, hcp3, hfr3⟩ := hp3
            change (∀ i < mloc.Lk, mem3 (accN + i) = mem2 (sc1 + mloc.Lk + i)) at hcp3
            change (∀ a, (a < accN ∨ accN + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
            apply hcontAfterN sc2 mem3 pos3 _ _ (by omega) (by omega)
              (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (by simp)
              (fun i hi => (hcp3 i hi).symm ▸ hvSub i hi)
              (by
                have h1 : Num.intVal mem3 accN h mloc.Lk = Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk :=
                  Num.intVal_congr hcp3
                rw [h1, hsubVal, hN1eq, htmpVal1]
                simp only [hdir, ↓reduceIte]
                rw [← sub_eq_add_neg]
                apply Num.wrap_congr
                rw [Int.sub_emod, Num.wrap_emod, ← Int.sub_emod])
              (fun a ha => (hfr3 a (Or.inr (by omega))).trans (hz2 a ha))
              (fun a ha => (hfr3 a (Or.inl ha)).trans ((hfr2 a (by omega)).trans (hfr1 a (by omega) (Or.inl (by omega)))))
              (fun i hi => (hfr3 (accD + i) (Or.inr (by omega))).trans ((hfr2 (accD + i) (by omega)).trans (hfr1 (accD + i) (by omega) (Or.inl (by omega)))))
              (by
                simp only [evalEdgePotGradContract, Num.subtractContract, heapContract,
                  copyLimbsToContract, evalKeyStepCost, List.getD_cons_zero, List.getD_cons_succ,
                  Expr.size, argsSize] at *
                omega)
  · have hdropNil : W.drop idx = [] := List.drop_eq_nil_of_le (by omega)
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hlt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [evalKeyWalkLoopContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hdropNil, walkGradSumInt,
        walkLenSumInt, add_zero]
      exact ⟨le_rfl, Nat.le_add_right _ _, hvN, hvD, (Num.wrap_of_fits (Num.intVal_fits hvN)).symm,
        (Num.wrap_of_fits (Num.intVal_fits hvD)).symm, hz, fun _ _ => trivial⟩
    · simp only [evalKeyWalkLoopContract, evalKeyWalkLoopCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]; omega


end MinCostFlow.MinRatio
