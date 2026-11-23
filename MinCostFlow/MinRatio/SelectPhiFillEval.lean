module

public import MinCostFlow.MinRatio.SelectPhiFillMath
public import MinCostFlow.MinRatio.WireSelectHeapRebal
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
import WordRAM.Tactic

/-!
# Verification of `zeroLimbsBody`, `evalEdgePotGradBody`, and `evalLevelPotGradBody` (`SelectPhiFillEval`)

Verifies the fixed-point building blocks called by `selectPhiFill`:
* `zeroLimbsBody` (`[dst, L]`): zeroes `L` consecutive words in `15 * L + 15` steps, establishing
  `Num.Valid` with value `0`.
* `evalEdgePotGradLoopBody` and `evalEdgePotGradBody` (defined in `WireSelectKeyEval.lean`):
  computes `potGrad C g φ (lvl + 1) f` into `dstPtr` in `(lvl + 1) * (130 * Lk + 240) + 18 * Lk + 60`
  steps and `(lvl + 1) * (3 * Lk)` scratch words.
* `evalLevelPotGradBody` (`[meta, j, f, dstPtr, Lk, scratch]`): handles both `j = 0` (`g0[f]`)
  and `j > 0` (`evalEdgePotGradBody` at `lvl = j - 1`) uniformly, computing `potGrad C g φ j f`
  in `j * (130 * Lk + 240) + 18 * Lk + 80` steps and `j * (3 * Lk)` scratch words.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. `zeroLimbsBody` -/

/-- Zero `L` consecutive words starting at `dst`: args `[dst, L]`, returns `0`. -/
def zeroLimbsBody : Stmt :=
  forRange 2 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)) ;;
  .ret (.const 0)

theorem zeroLimbsBody_noRand : zeroLimbsBody.NoRand := by
  simp [zeroLimbsBody, forRange, forUp, Stmt.NoRand]

/-- Step cost bound for `zeroLimbsBody`. -/
def zeroLimbsCost (L : ℕ) : ℕ := 15 * L + 15

/-- Contract for `zeroLimbsBody`: zeroes `[dst, dst + L)`, leaving all other memory unchanged. -/
def zeroLimbsContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ dst L, args = [dst, L] ∧ 1 < 2 ^ w ∧ dst + L < 2 ^ w
  post args mem ret mem' :=
    let dst := args.getD 0 0
    let L := args.getD 1 0
    ret = 0 ∧
    (∀ i < L, mem' (dst + i) = 0) ∧
    (∀ a, (a < dst ∨ dst + L ≤ a) → mem' a = mem a)
  cost args _ := zeroLimbsCost (args.getD 1 0)

/-! ## 2. Exact contracts for `evalEdgePotGradLoopBody`, `evalEdgePotGradBody`, `evalLevelPotGradBody` -/

/-- Verified step cost bound for `evalEdgePotGradLoopBody` for `rem` remaining levels. -/
def pfEvalEdgePotGradLoopCost (rem Lk : ℕ) : ℕ :=
  rem * (130 * Lk + 240) + 12

/-- Verified step cost bound for `evalEdgePotGradBody` at `lvl` (`0 .. lvl` inclusive). -/
def evalEdgePotGradExactCost (lvl Lk : ℕ) : ℕ :=
  (lvl + 1) * (130 * Lk + 240) + 18 * Lk + 60

/-- Wrapper evaluating `potGrad C g φ j f` for any `j ≥ 0`: copies `g0[f]` when `j = 0`, and
delegates to `evalEdgePotGradBody` at `lvl = j - 1` when `j > 0`.
Args: `[meta, j, f, dstPtr, Lk, scratch]`. -/
def evalLevelPotGradBody (evalProc copyTo : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.assign 6 (.load (.bin .add (.reg 0) (.const smG0Off))) ;;
     .call 7 copyTo [.bin .add (.reg 6) (.bin .mul (.reg 2) (.reg 4)), .reg 3, .reg 4] ;;
     .ret (.reg 5))
    (.call 6 evalProc [.reg 0, .bin .sub (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5] ;;
     .ret (.reg 6))

theorem evalLevelPotGradBody_noRand (evalProc copyTo : ℕ) :
    (evalLevelPotGradBody evalProc copyTo).NoRand := by
  simp [evalLevelPotGradBody, Stmt.NoRand]

/-- Scratch space for `evalLevelPotGradBody` at level `j`: `j * (3 * Lk)`. -/
def evalLevelPotGradSpace (j Lk : ℕ) : ℕ := j * (3 * Lk)

/-- Step cost bound for `evalLevelPotGradBody` at level `j`: `O((j + 1) * Lk)`. -/
def evalLevelPotGradCost (j Lk : ℕ) : ℕ :=
  j * (130 * Lk + 240) + 18 * Lk + 80

/-- Contract for `evalEdgePotGradLoopBody` (`[meta, lvl, f, dstPtr, Lk, cur, scratch]`). -/
def pfEvalEdgePotGradLoopContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ lvl f dstPtr cur scratch,
      args = [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, cur, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      lvl ≤ C.d ∧ cur ≤ lvl + 1 ∧
      f ∈ (C.G 0).E ∧ f < mloc.eCap 0 ∧
      (∀ k ≤ lvl, f ∈ (C.G k).E) ∧
      SelectPhiPrefixAt mem mloc h P C g φ (lvl + 1) ∧
      SelectPhiPrefixBelow mloc (lvl + 1) dstPtr ∧
      dstPtr + mloc.Lk ≤ scratch ∧
      Num.Valid mem dstPtr h mloc.Lk ∧
      Num.fixVal mem dstPtr h mloc.Lk P = potGrad C g φ cur f ∧
      PotGradEvalFits h mloc.Lk P C g φ (lvl + 1) f ∧
      ZeroFrom mem scratch ∧
      scratch + (lvl + 1 - cur) * (3 * mloc.Lk) < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let f := args.getD 2 0
    let dstPtr := args.getD 3 0
    let Lk := args.getD 4 0
    let cur := args.getD 5 0
    let scratch := args.getD 6 0
    ret = scratch + (lvl + 1 - cur) * (3 * Lk) ∧
    Num.Valid mem' dstPtr h Lk ∧
    Num.fixVal mem' dstPtr h Lk P = potGrad C g φ (lvl + 1) f ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dstPtr ∨ dstPtr + Lk ≤ a) → mem' a = mem a)
  cost args _ := pfEvalEdgePotGradLoopCost (args.getD 1 0 + 1 - args.getD 5 0) (args.getD 4 0)

/-- Contract for `evalEdgePotGradBody` (`[meta, lvl, f, dstPtr, Lk, scratch]`). -/
def pfEvalEdgePotGradContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ lvl f dstPtr scratch,
      args = [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      lvl ≤ C.d ∧
      f ∈ (C.G 0).E ∧ f < mloc.eCap 0 ∧
      (∀ k ≤ lvl, f ∈ (C.G k).E) ∧
      SelectPhiPrefixAt mem mloc h P C g φ (lvl + 1) ∧
      SelectPhiPrefixBelow mloc (lvl + 1) dstPtr ∧
      dstPtr + mloc.Lk ≤ scratch ∧
      PotGradEvalFits h mloc.Lk P C g φ (lvl + 1) f ∧
      ZeroFrom mem scratch ∧
      scratch + evalEdgePotGradSpace lvl mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let f := args.getD 2 0
    let dstPtr := args.getD 3 0
    let Lk := args.getD 4 0
    let scratch := args.getD 5 0
    ret = scratch + evalEdgePotGradSpace lvl Lk ∧
    Num.Valid mem' dstPtr h Lk ∧
    Num.fixVal mem' dstPtr h Lk P = potGrad C g φ (lvl + 1) f ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dstPtr ∨ dstPtr + Lk ≤ a) → mem' a = mem a)
  cost args _ := evalEdgePotGradExactCost (args.getD 1 0) (args.getD 4 0)

/-- Contract for `evalLevelPotGradBody` (`[meta, j, f, dstPtr, Lk, scratch]`): computes
`potGrad C g φ j f` for any `j ≤ C.d` (handling `j = 0` and `j > 0` uniformly). -/
def evalLevelPotGradContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ j f dstPtr scratch,
      args = [mloc.metaBase, j, f, dstPtr, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      j ≤ C.d ∧
      f ∈ (C.G 0).E ∧ f < mloc.eCap 0 ∧
      (∀ k < j, f ∈ (C.G k).E) ∧
      SelectPhiPrefixAt mem mloc h P C g φ j ∧
      SelectPhiPrefixBelow mloc j dstPtr ∧
      dstPtr + mloc.Lk ≤ scratch ∧
      PotGradEvalFits h mloc.Lk P C g φ j f ∧
      ZeroFrom mem scratch ∧
      scratch + evalLevelPotGradSpace j mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let j := args.getD 1 0
    let f := args.getD 2 0
    let dstPtr := args.getD 3 0
    let Lk := args.getD 4 0
    let scratch := args.getD 5 0
    ret = scratch + evalLevelPotGradSpace j Lk ∧
    Num.Valid mem' dstPtr h Lk ∧
    Num.fixVal mem' dstPtr h Lk P = potGrad C g φ j f ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dstPtr ∨ dstPtr + Lk ≤ a) → mem' a = mem a)
  cost args _ := evalLevelPotGradCost (args.getD 1 0) (args.getD 4 0)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Verification of `zeroLimbsBody` -/

/-- `zeroLimbsBody` meets `zeroLimbsContract` in `15 * L + 15` steps. -/
theorem zeroLimbs_meetsContract {w proc : ℕ} {p : Program}
    (hp : p.procs[proc]? = some zeroLimbsBody) :
    MeetsContract w p proc (zeroLimbsContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨dst, L, rfl, hw1, hdstW⟩ := hpre
  have hLw : L < 2 ^ w := hwords L (by simp)
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [zeroLimbsBody]
  let P0 : State → Prop := fun st =>
    st.regs 0 = dst ∧ st.regs 1 = L ∧ st.mem = mem
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ L ∧ st.regs 0 = dst ∧ st.regs 1 = L ∧ st.regs 2 = k ∧
    (∀ i < k, st.mem (dst + i) = 0) ∧
    (∀ a, a < dst ∨ dst + L ≤ a → st.mem a = mem a)
  let body : Stmt := .store (.bin .add (.reg 0) (.reg 2)) (.const 0)
  have hLoop : Triple w p P0 (forRange 2 (.const 0) (.reg 1) body) (normalPost (Inv L))
      (fun _ => (L - 0) * (6 + Expr.size (.reg 1) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 1) + 5)) := by
    refine Triple.forRange_const 6 0 L (Nat.zero_le _) hw1 (fun _ => hLw)
      (fun st hst => by
        rcases hst with ⟨h0, h1, hmem⟩
        exact ⟨by simp [Expr.eval, h0w],
          ⟨Nat.zero_le _, by simp [h0], by simp [h1], by simp, fun i hi => by omega,
            fun _ _ => hmem ▸ rfl⟩⟩)
      (fun k st _ _ hk => hk.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hz, hfr⟩
        have hk_w : dst + k < 2 ^ w := by omega
        refine ⟨.normal, { st with mem := Function.update st.mem (dst + k) 0 }, 5,
          runs_store_iff.mpr ⟨dst + k, 0,
            by simp [Expr.eval, BinOp.eval, hr0, hr2, hk_w],
            by simp [Expr.eval, h0w], rfl, rfl, rfl⟩,
          ⟨⟨by omega, by simp [hr0], by simp [hr1], by simp, ?_, ?_⟩, by simp [hr2]⟩,
          by simp⟩
        · intro i hi
          dsimp only
          by_cases hik : i = k
          · subst hik; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hz i (by omega)
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr a ha)
  refine runs_seq_triple_le hLoop ⟨by simp [startState], by simp [startState], rfl⟩ ?_
  intro st1 ⟨_, _, _, _, hz1, hfr1⟩
  refine runs_ret_le (v := 0) (by simp [Expr.eval, h0w]) ?_ ?_
  · simp only [zeroLimbsContract, Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨trivial, hz1, hfr1⟩
  · simp only [zeroLimbsContract, zeroLimbsCost, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

/-! ## 4. Verification of `evalEdgePotGradLoopBody`, `evalEdgePotGradBody`, `evalLevelPotGradBody` -/

private lemma mul_add_lt_mul_eval {v c L i : ℕ} (hv : v < c) (hi : i < L) :
    v * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  omega

private lemma mul_add_le_mul_eval {v c L : ℕ} (hv : v < c) :
    v * L + L ≤ c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  exact this

private lemma base_lt_word_eval {w h : ℕ} (hw : 2 * h + 2 ≤ w) :
    Num.base h < 2 ^ w := by
  unfold Num.base
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- `evalEdgePotGradLoopBody` meets `pfEvalEdgePotGradLoopContract`. -/
theorem pfEvalEdgePotGradLoop_meetsContract {w h P self copyTo addProc subProc : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[self]? = some (evalEdgePotGradLoopBody self copyTo addProc subProc))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hadd : MeetsContract w p addProc (Num.addContract w h))
    (hsub : MeetsContract w p subProc (Num.subtractContract w h)) :
    MeetsContract w p self (pfEvalEdgePotGradLoopContract w h P mloc C g φ) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0 + 1 - args.getD 5 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨lvl, f, dstPtr, cur, scratch, rfl, hw16, hh, hw2, hlvlD, hcurLe, hf0, hfCap0,
    hfAll, hPref, hBel, hdstSc, hvDst, hfixDst, hFits, hz, hroom⟩ := hpre
  change lvl + 1 - cur = rem at hremEq
  have hbaseW : Num.base h < 2 ^ w := base_lt_word_eval hw2
  have hLkW : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hmetaW : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlW : lvl < 2 ^ w := hwords lvl (by simp)
  have hfW : f < 2 ^ w := hwords f (by simp)
  have hdstW : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hcurW : cur < 2 ^ w := hwords cur (by simp)
  have hscW : scratch < 2 ^ w := hwords scratch (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold evalEdgePotGradLoopBody
  by_cases hgt : lvl < cur
  · have hrem0 : rem = 0 := by omega
    have hcurEq : cur = lvl + 1 := by omega
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hgt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [pfEvalEdgePotGradLoopContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hremEq, hrem0,
        Nat.zero_mul, Nat.add_zero]
      exact ⟨trivial, hvDst, hcurEq ▸ hfixDst, hz, fun _ _ _ => trivial⟩
    · simp only [pfEvalEdgePotGradLoopContract, pfEvalEdgePotGradLoopCost,
        List.getD_cons_zero, List.getD_cons_succ, hremEq, hrem0, Nat.zero_mul, Expr.size]
      omega
  · have hcurLt : cur < lvl + 1 := by omega
    have hcurLeLvl : cur ≤ lvl := by omega
    have hremPos : 1 ≤ rem := by omega
    have hremStep : lvl + 1 - (cur + 1) = rem - 1 := by omega
    have hPref0 := hPref
    have hBel0 := hBel
    obtain ⟨hdEq, hg0p, hdMem, hg0Ev, hPrefK⟩ := hPref
    obtain ⟨hmetaHi, hg0Hi, hBelK⟩ := hBel
    obtain ⟨hGPtrM, hvCapM, heCapM, hPhiPtrM, hGcur, hPhicur⟩ := hPrefK cur hcurLt
    obtain ⟨hGcurHi, hPhicurHi⟩ := hBelK cur hcurLt
    have hfCur : f ∈ (C.G cur).E := hfAll cur hcurLeLvl
    have hGcurValid := hGcur.1 f hfCur
    have htailV : (C.G cur).tail f ∈ (C.G cur).V := hGcurValid.1
    have hheadV : (C.G cur).head f ∈ (C.G cur).V := hGcurValid.2
    have htailCap : (C.G cur).tail f < mloc.vCap cur := hGcur.2.1 _ htailV
    have hheadCap : (C.G cur).head f < mloc.vCap cur := hGcur.2.1 _ hheadV
    have hfCapCur : f < mloc.eCap cur := hGcur.2.2.1 f hfCur
    have hEnds := dynGraphAt_read_endpoints hGcur hfCur
    have hszCur : dynGraphSize (mloc.vCap cur) (mloc.eCap cur) =
        4 + 7 * mloc.vCap cur + 9 * mloc.eCap cur := rfl
    have hsmSz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have htailSlotCap : mem (dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) <
        mloc.vCap cur := by
      have hth := hGcur.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfCur
      rw [hth.1]
      exact hGcur.2.1 _ (hGcur.2.2.2.2.2.2.2.2.2.1 _ htailV).1
    have hheadSlotCap : mem (dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) <
        mloc.vCap cur := by
      have hth := hGcur.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfCur
      rw [hth.2]
      exact hGcur.2.1 _ (hGcur.2.2.2.2.2.2.2.2.2.1 _ hheadV).1
    have htailPtrEnd : mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk + mloc.Lk ≤ dstPtr := by
      have := mul_add_le_mul_eval (L := mloc.Lk) htailCap; omega
    have hheadPtrEnd : mloc.phiPtr cur + (C.G cur).head f * mloc.Lk + mloc.Lk ≤ dstPtr := by
      have := mul_add_le_mul_eval (L := mloc.Lk) hheadCap; omega
    have hroom3 : scratch + 3 * mloc.Lk < 2 ^ w := by
      have : 1 * (3 * mloc.Lk) ≤ (lvl + 1 - cur) * (3 * mloc.Lk) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hcur1W : cur + 1 < 2 ^ w := by omega
    have hsc1W : scratch + mloc.Lk < 2 ^ w := by omega
    have hsc2W : scratch + 2 * mloc.Lk < 2 ^ w := by omega
    have hsc3W : scratch + 3 * mloc.Lk < 2 ^ w := by omega
    have htailPtrW : mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk < 2 ^ w := by omega
    have hheadPtrW : mloc.phiPtr cur + (C.G cur).head f * mloc.Lk < 2 ^ w := by omega
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hgt])
      (fun h => absurd rfl h) ?_
    intro _
    -- Load d, d+1, GPtr[cur], vCap[cur], eCap[cur], phiPtr[cur]
    have hm0 : mem (mloc.metaBase + smTableOff + cur) = mloc.GPtr cur := by
      simpa [smEntryAddr] using hGPtrM
    have hm1 : mem (mloc.metaBase + smTableOff + ((mloc.d + 1) + cur)) = mloc.vCap cur := by
      simpa [smEntryAddr, Nat.add_assoc] using hvCapM
    have hm2 : mem (mloc.metaBase + smTableOff + (2 * (mloc.d + 1) + cur)) = mloc.eCap cur := by
      simpa [smEntryAddr, Nat.add_assoc] using heCapM
    have hm3 : mem (mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + cur)) = mloc.phiPtr cur := by
      simpa [smEntryAddr, Nat.add_assoc] using hPhiPtrM
    have hmd_lt : mloc.metaBase + smDOff < 2 ^ w := by unfold smDOff; omega
    have hd_lt : mloc.d + 1 < 2 ^ w := by omega
    have h2d_lt : 2 * (mloc.d + 1) < 2 ^ w := by omega
    have h3d_lt : 3 * (mloc.d + 1) < 2 ^ w := by omega
    have hm0_lt : mloc.metaBase + smTableOff + cur < 2 ^ w := by unfold smTableOff; omega
    have hm1_lt : mloc.metaBase + smTableOff + ((mloc.d + 1) + cur) < 2 ^ w := by unfold smTableOff; omega
    have hm2_lt : mloc.metaBase + smTableOff + (2 * (mloc.d + 1) + cur) < 2 ^ w := by unfold smTableOff; omega
    have hm3_lt : mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + cur) < 2 ^ w := by unfold smTableOff; omega
    have h13_lt : mloc.GPtr cur + 4 + 4 * mloc.vCap cur < 2 ^ w := by omega
    have h14_lt : mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur < 2 ^ w := by omega
    have h15_lt : mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur < 2 ^ w := by omega
    have h15_eq : mloc.GPtr cur + 4 + 7 * mloc.vCap cur + 3 * mloc.eCap cur + mloc.eCap cur =
        dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) := by
      unfold dgEHeadSlotBase; omega
    refine runs_seq_assign_flat (v := mloc.d)
      (Expr.eval_load_of_eq (by eval_expr) (by simpa using hdMem)) ?_
    refine runs_seq_assign_flat (v := mloc.d + 1) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr cur)
      (Expr.eval_load_of_eq (by eval_expr) hm0) ?_
    refine runs_seq_assign_flat (v := mloc.vCap cur)
      (Expr.eval_load_of_eq (by eval_expr) hm1) ?_
    refine runs_seq_assign_flat (v := mloc.eCap cur)
      (Expr.eval_load_of_eq (by eval_expr) hm2) ?_
    refine runs_seq_assign_flat (v := mloc.phiPtr cur)
      (Expr.eval_load_of_eq (by eval_expr) hm3) ?_
    refine runs_seq_assign_flat (v := dgIntToExtBase (mloc.GPtr cur) (mloc.vCap cur))
      (by unfold dgIntToExtBase; eval_expr) ?_
    refine runs_seq_assign_flat (v := dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur))
      (by unfold dgETailSlotBase; eval_expr) ?_
    refine runs_seq_assign_flat (v := dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur))
      (by rw [← h15_eq]; unfold dgETailSlotBase; eval_expr) ?_
    -- Load tail_cur(f) and head_cur(f)
    have htsAddr_lt : dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f < 2 ^ w := by
      unfold dgETailSlotBase; omega
    have hhsAddr_lt : dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f < 2 ^ w := by
      unfold dgEHeadSlotBase; omega
    have htiAddr_lt : dgIntToExtBase (mloc.GPtr cur) (mloc.vCap cur) +
        mem (dgETailSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) < 2 ^ w := by
      unfold dgIntToExtBase; omega
    have hhiAddr_lt : dgIntToExtBase (mloc.GPtr cur) (mloc.vCap cur) +
        mem (dgEHeadSlotBase (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) + f) < 2 ^ w := by
      unfold dgIntToExtBase; omega
    refine runs_seq_assign_flat (v := (C.G cur).tail f)
      (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
        (Expr.eval_load_of_eq (by eval_expr) rfl) htiAddr_lt) hEnds.1) ?_
    refine runs_seq_assign_flat (v := (C.G cur).head f)
      (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
        (Expr.eval_load_of_eq (by eval_expr) rfl) hhiAddr_lt) hEnds.2) ?_
    -- Call 1: addProc [dstPtr, phiPtr[cur] + head * Lk, Lk, scratch]
    have hvh : Num.Valid mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk :=
      (hPhicur _ hheadV).1
    have hvt : Num.Valid mem (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk :=
      (hPhicur _ htailV).1
    have hheadMulW : (C.G cur).head f * mloc.Lk < 2 ^ w := by omega
    have htailMulW : (C.G cur).tail f * mloc.Lk < 2 ^ w := by omega
    refine runs_seq_call_flat hadd
      (vs := [dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, scratch])
      (by eval_expr) (by wram_words)
      ⟨dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, scratch, rfl,
        ⟨dstPtr, mloc.phiPtr cur + (C.G cur).head f * mloc.Lk, mloc.Lk, 0, scratch, rfl,
          hdstSc, by omega, Nat.zero_le 1, hvDst, hvh⟩,
        hz, by change scratch + mloc.Lk < 2 ^ w; omega⟩ ?_
    intro sc1 mem1 pos1 hp1
    rcases hp1 with ⟨hsc1Eq, _, _, hf1, hz1, hlist1⟩
    change sc1 = scratch + mloc.Lk at hsc1Eq
    change (∀ x < scratch, mem1 x = mem x) at hf1
    change ZeroFrom mem1 sc1 at hz1
    change ListAt mem1 scratch (Num.digits h mloc.Lk
      (Num.unsignedVal mem dstPtr h mloc.Lk +
        Num.unsignedVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk + 0)) at hlist1
    have hsc1W' : sc1 < 2 ^ w := hsc1Eq ▸ hsc1W
    have hvSum : Num.Valid mem1 scratch h mloc.Lk := by
      have hv := Num.valid_listAt hlist1 (Num.digits_lt _ _ _)
      simpa [Num.digits_length] using hv
    have hvalSum : Num.intVal mem1 scratch h mloc.Lk =
        Num.intVal mem dstPtr h mloc.Lk +
          Num.intVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk := by
      have hfit1 : Num.Fits h mloc.Lk
          (Num.intVal mem dstPtr h mloc.Lk +
            Num.intVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk) := by
        refine fits_of_real_scaled (P := P)
          (x := potGrad C g φ cur f + φ cur ((C.G cur).head f)) ?_
          (hFits cur hcurLt).1.1 (hFits cur hcurLt).1.2
        rw [← hfixDst, ← (hPhicur _ hheadV).2]
        unfold Num.fixVal
        push_cast
        ring
      have hwrap := (Num.addCarry_value (h := h) (L := mloc.Lk) (c := 0) hlist1).2
      simpa only [Nat.cast_zero, add_zero, Num.wrap_of_fits hfit1] using hwrap
    have hvt1 : Num.Valid mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk :=
      fun i hi => by rw [hf1 _ (by omega)]; exact hvt i hi
    have htailVal1 : Num.intVal mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk =
        Num.intVal mem (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk :=
      Num.intVal_congr fun i hi => hf1 _ (by omega)
    -- Call 2: subProc [scratch, phiPtr[cur] + tail * Lk, Lk, sc1]
    refine runs_seq_call_flat hsub
      (vs := [scratch, mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk, mloc.Lk, sc1])
      (by eval_expr) (by wram_words)
      ⟨⟨scratch, mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk, mloc.Lk, sc1, rfl,
        by omega, by omega, hvSum, hvt1⟩, hz1, by change sc1 + 2 * mloc.Lk < 2 ^ w; omega⟩ ?_
    intro sc2 mem2 pos2 hp2
    rcases hp2 with ⟨hsc2Eq, _, _, hf2, hz2, hvDiff, hvalDiff⟩
    change sc2 = sc1 + 2 * mloc.Lk at hsc2Eq
    change (∀ x < sc1, mem2 x = mem1 x) at hf2
    change ZeroFrom mem2 sc2 at hz2
    change Num.Valid mem2 (sc1 + mloc.Lk) h mloc.Lk at hvDiff
    change Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk =
      Num.wrap h mloc.Lk (Num.intVal mem1 scratch h mloc.Lk -
        Num.intVal mem1 (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk) at hvalDiff
    have hsc2W' : sc2 < 2 ^ w := by omega
    have hsc1PlusLkW : sc1 + mloc.Lk < 2 ^ w := by omega
    have hvalDiffExact : Num.intVal mem2 (sc1 + mloc.Lk) h mloc.Lk =
        Num.intVal mem dstPtr h mloc.Lk +
          Num.intVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk -
          Num.intVal mem (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk := by
      rw [hvalDiff, hvalSum, htailVal1]
      have hfit2 : Num.Fits h mloc.Lk
          (Num.intVal mem dstPtr h mloc.Lk +
            Num.intVal mem (mloc.phiPtr cur + (C.G cur).head f * mloc.Lk) h mloc.Lk -
            Num.intVal mem (mloc.phiPtr cur + (C.G cur).tail f * mloc.Lk) h mloc.Lk) := by
        refine fits_of_real_scaled (P := P)
          (x := potGrad C g φ (cur + 1) f) ?_
          (hFits cur hcurLt).2.1 (hFits cur hcurLt).2.2
        rw [potGrad, ← hfixDst, ← (hPhicur _ hheadV).2, ← (hPhicur _ htailV).2]
        unfold Num.fixVal
        push_cast
        ring
      exact Num.wrap_of_fits hfit2
    -- Call 3: copyTo [sc1 + Lk, dstPtr, Lk]
    refine runs_seq_call_flat hcopy
      (vs := [sc1 + mloc.Lk, dstPtr, mloc.Lk])
      (by eval_expr) (by wram_words)
      ⟨sc1 + mloc.Lk, dstPtr, mloc.Lk, rfl, hw1, by omega, by omega, Or.inr (by omega),
        fun i hi => lt_trans (hvDiff i hi) hbaseW⟩ ?_
    intro _ mem3 pos3 hp3
    obtain ⟨_, hcp3, hfr3⟩ := hp3
    change (∀ i < mloc.Lk, mem3 (dstPtr + i) = mem2 (sc1 + mloc.Lk + i)) at hcp3
    change (∀ a, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
    have hdstV3 : Num.Valid mem3 dstPtr h mloc.Lk := fun i hi => (hcp3 i hi) ▸ hvDiff i hi
    have hdstFix3 : Num.fixVal mem3 dstPtr h mloc.Lk P = potGrad C g φ (cur + 1) f := by
      unfold Num.fixVal
      rw [Num.intVal_congr hcp3, hvalDiffExact, potGrad, ← hfixDst,
        ← (hPhicur _ hheadV).2, ← (hPhicur _ htailV).2]
      unfold Num.fixVal
      push_cast
      ring
    have hfrBelowDst : ∀ a < dstPtr, mem3 a = mem a := fun a ha =>
      (hfr3 a (Or.inl ha)).trans ((hf2 a (by omega)).trans (hf1 a (by omega)))
    have hPref3 : SelectPhiPrefixAt mem3 mloc h P C g φ (lvl + 1) :=
      hPref0.of_agree_below hBel0 (by omega)
        (fun e he => (hPrefK 0 (by omega)).2.2.2.2.1.2.2.1 e he) hfrBelowDst
    have hz3 : ZeroFrom mem3 sc2 := fun a ha =>
      (hfr3 a (Or.inr (by omega))).trans (hz2 a ha)
    have hroomNext : sc2 + (lvl + 1 - (cur + 1)) * (3 * mloc.Lk) < 2 ^ w := by
      have heq : (lvl + 1 - cur) * (3 * mloc.Lk) =
          3 * mloc.Lk + (lvl + 1 - (cur + 1)) * (3 * mloc.Lk) := by
        rw [show lvl + 1 - cur = (lvl + 1 - (cur + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
        omega
      omega
    -- Call 4: recursive call self [meta, lvl, f, dstPtr, Lk, cur + 1, sc2]
    refine runs_seq_call_flat ih
      (vs := [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, cur + 1, sc2])
      (by eval_expr) (by wram_words)
      ⟨⟨lvl, f, dstPtr, cur + 1, sc2, rfl, hw16, hh, hw2, hlvlD, by omega, hf0, hfCap0,
          hfAll, hPref3, hBel0, by omega, hdstV3, hdstFix3, hFits, hz3, hroomNext⟩,
        by simp only [List.getD_cons_zero, List.getD_cons_succ]; omega⟩ ?_
    intro scFinal mem4 pos4 hp4
    obtain ⟨hret4, hv4, hfix4, hz4, hfr4⟩ := hp4
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hret4 hv4 hfix4 hz4 hfr4
    have hretFinalEq : scFinal = scratch + (lvl + 1 - cur) * (3 * mloc.Lk) := by
      have heq : (lvl + 1 - cur) * (3 * mloc.Lk) =
          3 * mloc.Lk + (lvl + 1 - (cur + 1)) * (3 * mloc.Lk) := by
        rw [show lvl + 1 - cur = (lvl + 1 - (cur + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
        omega
      omega
    have hscFinalW : scFinal < 2 ^ w := by omega
    refine WordRAM.runs_ret_le (v := scFinal) (by eval_expr) ?_ ?_
    · dsimp only [pfEvalEdgePotGradLoopContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨hretFinalEq, hv4, hfix4, hz4, fun a ha hout => ?_⟩
      exact (hfr4 a (by omega) hout).trans
        ((hfr3 a hout).trans ((hf2 a (by omega)).trans (hf1 a ha)))
    · simp only [pfEvalEdgePotGradLoopContract, pfEvalEdgePotGradLoopCost, Num.addContract,
        Num.subtractContract, copyLimbsToContract, heapContract, Contract.below,
        List.getD_cons_zero, List.getD_cons_succ, hremEq, hremStep, argsSize, Expr.size]
      have hmulStep : rem * (130 * mloc.Lk + 240) =
          (rem - 1) * (130 * mloc.Lk + 240) + (130 * mloc.Lk + 240) := by
        conv_lhs => rw [show rem = (rem - 1) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      omega

/-- `evalEdgePotGradBody` meets `pfEvalEdgePotGradContract`. -/
theorem pfEvalEdgePotGrad_meetsContract {w h P proc loopProc copyTo : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (evalEdgePotGradBody loopProc copyTo))
    (hloop : MeetsContract w p loopProc (pfEvalEdgePotGradLoopContract w h P mloc C g φ))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (pfEvalEdgePotGradContract w h P mloc C g φ) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, f, dstPtr, scratch, rfl, hw16, hh, hw2, hlvlD, hf0, hfCap0, hfAll,
    hPref, hBel, hdstSc, hFits, hz, hroom⟩ := hpre
  have hbaseW : Num.base h < 2 ^ w := base_lt_word_eval hw2
  have hw1 : 1 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlW : lvl < 2 ^ w := hwords lvl (by simp)
  have hfW : f < 2 ^ w := hwords f (by simp)
  have hdstW : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hLkW : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscW : scratch < 2 ^ w := hwords scratch (by simp)
  have hg0PtrEnd : mloc.g0Ptr + f * mloc.Lk + mloc.Lk ≤ dstPtr := by
    have := mul_add_le_mul_eval (L := mloc.Lk) hfCap0
    have := hBel.2.1
    omega
  have hg0PtrW : mloc.g0Ptr + f * mloc.Lk < 2 ^ w := by omega
  have hg0MulW : f * mloc.Lk < 2 ^ w := by omega
  have hg0OffW : mloc.metaBase + smG0Off < 2 ^ w := by
    have := hBel.1; unfold smG0Off selectLevelMetaSize at *; omega
  apply runs_start_le
  dsimp only [startState]
  unfold evalEdgePotGradBody
  refine runs_seq_assign_flat (v := mloc.g0Ptr)
    (Expr.eval_load_of_eq (by eval_expr) hPref.2.1) ?_
  have hvg0 : Num.Valid mem (mloc.g0Ptr + f * mloc.Lk) h mloc.Lk := (hPref.2.2.2.1 f hf0).1
  refine runs_seq_call_flat hcopy
    (vs := [mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk])
    (by eval_expr) (by wram_words)
    ⟨mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk, rfl, hw1, by omega, by omega,
      Or.inl hg0PtrEnd, fun i hi => lt_trans (hvg0 i hi) hbaseW⟩ ?_
  intro _ mem1 pos1 hp1
  obtain ⟨_, hcp1, hfr1⟩ := hp1
  change (∀ i < mloc.Lk, mem1 (dstPtr + i) = mem (mloc.g0Ptr + f * mloc.Lk + i)) at hcp1
  change (∀ a, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem1 a = mem a) at hfr1
  have hdstV1 : Num.Valid mem1 dstPtr h mloc.Lk := fun i hi => (hcp1 i hi) ▸ hvg0 i hi
  have hdstFix1 : Num.fixVal mem1 dstPtr h mloc.Lk P = potGrad C g φ 0 f := by
    unfold Num.fixVal potGrad
    rw [Num.intVal_congr hcp1]
    exact (hPref.2.2.2.1 f hf0).2
  have hPref1 : SelectPhiPrefixAt mem1 mloc h P C g φ (lvl + 1) :=
    hPref.of_agree_below hBel (by omega)
      (fun e he => (hPref.2.2.2.2 0 (by omega)).2.2.2.2.1.2.2.1 e he)
      (fun a ha => hfr1 a (Or.inl ha))
  have hz1 : ZeroFrom mem1 scratch := fun a ha => (hfr1 a (Or.inr (by omega))).trans (hz a ha)
  refine runs_seq_call_flat hloop
    (vs := [mloc.metaBase, lvl, f, dstPtr, mloc.Lk, 0, scratch])
    (by eval_expr) (by wram_words)
    ⟨lvl, f, dstPtr, 0, scratch, rfl, hw16, hh, hw2, hlvlD, Nat.zero_le _, hf0, hfCap0,
      hfAll, hPref1, hBel, hdstSc, hdstV1, hdstFix1, hFits, hz1, by simpa [evalEdgePotGradSpace] using hroom⟩ ?_
  intro scFinal mem2 pos2 hp2
  obtain ⟨hret2, hv2, hfix2, hz2, hfr2⟩ := hp2
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero] at hret2 hv2 hfix2 hz2 hfr2
  have hscFinalW : scFinal < 2 ^ w := by rw [hret2]; simpa [evalEdgePotGradSpace] using hroom
  refine WordRAM.runs_ret_le (v := scFinal) (by eval_expr) ?_ ?_
  · dsimp only [pfEvalEdgePotGradContract]
    simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, evalEdgePotGradSpace]
    exact ⟨hret2, hv2, hfix2, hz2, fun a ha hout => (hfr2 a ha hout).trans (hfr1 a hout)⟩
  · simp only [pfEvalEdgePotGradContract, pfEvalEdgePotGradLoopContract, copyLimbsToContract,
      evalEdgePotGradExactCost, pfEvalEdgePotGradLoopCost,
      List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, argsSize, Expr.size]
    omega

/-- `evalLevelPotGradBody` meets `evalLevelPotGradContract`. -/
theorem evalLevelPotGrad_meetsContract {w h P proc evalProc copyTo : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (evalLevelPotGradBody evalProc copyTo))
    (heval : MeetsContract w p evalProc (pfEvalEdgePotGradContract w h P mloc C g φ))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (evalLevelPotGradContract w h P mloc C g φ) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨j, f, dstPtr, scratch, rfl, hw16, hh, hw2, hjD, hf0, hfCap0, hfAll,
    hPref, hBel, hdstSc, hFits, hz, hroom⟩ := hpre
  have hbaseW : Num.base h < 2 ^ w := base_lt_word_eval hw2
  have hw1 : 1 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hjW : j < 2 ^ w := hwords j (by simp)
  have hfW : f < 2 ^ w := hwords f (by simp)
  have hdstW : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hLkW : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscW : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold evalLevelPotGradBody
  cases j with
  | zero =>
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    have hg0PtrEnd : mloc.g0Ptr + f * mloc.Lk + mloc.Lk ≤ dstPtr := by
      have := mul_add_le_mul_eval (L := mloc.Lk) hfCap0
      have := hBel.2.1; omega
    have hg0PtrW : mloc.g0Ptr + f * mloc.Lk < 2 ^ w := by omega
    have hg0MulW : f * mloc.Lk < 2 ^ w := by omega
    have hg0OffW : mloc.metaBase + smG0Off < 2 ^ w := by
      have := hBel.1; unfold smG0Off selectLevelMetaSize at *; omega
    refine runs_seq_assign_flat (v := mloc.g0Ptr)
      (Expr.eval_load_of_eq (by eval_expr) hPref.2.1) ?_
    have hvg0 : Num.Valid mem (mloc.g0Ptr + f * mloc.Lk) h mloc.Lk := (hPref.2.2.2.1 f hf0).1
    refine runs_seq_call_flat hcopy
      (vs := [mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk])
      (by eval_expr) (by wram_words)
      ⟨mloc.g0Ptr + f * mloc.Lk, dstPtr, mloc.Lk, rfl, hw1, by omega, by omega,
        Or.inl hg0PtrEnd, fun i hi => lt_trans (hvg0 i hi) hbaseW⟩ ?_
    intro _ mem1 pos1 hp1
    obtain ⟨_, hcp1, hfr1⟩ := hp1
    change (∀ i < mloc.Lk, mem1 (dstPtr + i) = mem (mloc.g0Ptr + f * mloc.Lk + i)) at hcp1
    change (∀ a, (a < dstPtr ∨ dstPtr + mloc.Lk ≤ a) → mem1 a = mem a) at hfr1
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [evalLevelPotGradContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ,
        evalLevelPotGradSpace, Nat.zero_mul, Nat.add_zero]
      refine ⟨trivial, fun i hi => (hcp1 i hi) ▸ hvg0 i hi, ?_,
        fun a ha => (hfr1 a (Or.inr (by omega))).trans (hz a ha),
        fun a _ hout => hfr1 a hout⟩
      unfold Num.fixVal potGrad
      rw [Num.intVal_congr hcp1]
      exact (hPref.2.2.2.1 f hf0).2
    · simp only [evalLevelPotGradContract, copyLimbsToContract, evalLevelPotGradCost,
        List.getD_cons_zero, List.getD_cons_succ, Nat.zero_mul, Nat.zero_add, argsSize, Expr.size]
      omega
  | succ k =>
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval])
      (fun h => absurd rfl h) ?_
    intro _
    have hkW : k < 2 ^ w := by omega
    refine runs_seq_call_flat heval
      (vs := [mloc.metaBase, k, f, dstPtr, mloc.Lk, scratch])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hw1, hkW]) (by wram_words)
      ⟨k, f, dstPtr, scratch, rfl, hw16, hh, hw2, by omega, hf0, hfCap0,
        fun i hi => hfAll i (by omega), hPref, hBel, hdstSc, hFits, hz,
        by simpa [evalEdgePotGradSpace, evalLevelPotGradSpace] using hroom⟩ ?_
    intro scFinal mem1 pos1 hp1
    obtain ⟨hret1, hv1, hfix1, hz1, hfr1⟩ := hp1
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hret1 hv1 hfix1 hz1 hfr1
    have hscFinalW : scFinal < 2 ^ w := by
      rw [hret1]; simpa [evalEdgePotGradSpace, evalLevelPotGradSpace] using hroom
    refine WordRAM.runs_ret_le (v := scFinal) (by eval_expr) ?_ ?_
    · dsimp only [evalLevelPotGradContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, evalLevelPotGradSpace]
      exact ⟨by simpa [evalEdgePotGradSpace] using hret1, hv1, hfix1, hz1, hfr1⟩
    · simp only [evalLevelPotGradContract, pfEvalEdgePotGradContract, evalLevelPotGradCost,
        evalEdgePotGradExactCost, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
      omega

end MinCostFlow.MinRatio

end
