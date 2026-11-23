module

public import MinCostFlow.SparseCore.Program.CompSplitListUF
public import WordRAM.Contract
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Word-RAM Reverse Union-Find Procedures (`CompSplitListUFProc`)

Implements and verifies the three deterministic (`NoRand`) Word-RAM helper procedures used by P4's
canonical split-list emitter:

1. `compUFInitFindProc` (`[ufBase, vCap, r]`): lazily initializes `r` as a singleton if `sz[r] = 0`
   (appending `r` to `actList`), walks `par` to the root `rep`, and returns `rep` in
   `O(log(act.length + 1))` steps.
2. `compUFPairUnionProc` (`[ufBase, vCap, ra, rb, outSlot, isRelFlag, edgeVal, doUnion]`):
   computes `(kept, fresh) = ufPair U ra rb`, stores `[isRelFlag, edgeVal, kept, fresh]` at
   `[outSlot, outSlot + 4)`, and if `doUnion ≠ 0` performs union-by-size `ufUnion U ra rb` in `O(1)`
   steps.
3. `compUFCleanProc` (`[ufBase, vCap]`): zeroes `par[r], sz[r], minF[r], oldR[r]` for every
   `r ∈ actList`, zeroes `actList[0..actLen-1]` and `actLen`, in `O(actList.length + 1)` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Scratch memory layout and `RevUFMemAt` -/

def ufIsNewBase (ufBase : ℕ) : ℕ := ufBase
def ufParBase (ufBase vCap : ℕ) : ℕ := ufBase + vCap
def ufSzBase (ufBase vCap : ℕ) : ℕ := ufBase + 2 * vCap
def ufMinFBase (ufBase vCap : ℕ) : ℕ := ufBase + 3 * vCap
def ufOldRBase (ufBase vCap : ℕ) : ℕ := ufBase + 4 * vCap
def ufActBase (ufBase vCap : ℕ) : ℕ := ufBase + 5 * vCap
def ufActLenAddr (ufBase vCap : ℕ) : ℕ := ufBase + 6 * vCap
def ufScratchSize (vCap : ℕ) : ℕ := 6 * vCap + 1

/-- Concrete Word-RAM representation of `RevUFState` at `[ufBase, ufBase + 6 * vCap + 1)` with
active-vertex list `act` (`isNew[v] = 1` iff `v` is a newly created root in this step). -/
structure RevUFMemAt (mem : ℕ → ℕ) (ufBase vCap : ℕ) (isNew : ℕ → Bool)
    (U : RevUFState) (act : List ℕ) : Prop where
  hIsNew : ∀ v < vCap, mem (ufIsNewBase ufBase + v) = if isNew v then 1 else 0
  hArrs : ∀ v < vCap,
    mem (ufParBase ufBase vCap + v) = U.par v ∧
    mem (ufSzBase ufBase vCap + v) = U.sz v ∧
    mem (ufMinFBase ufBase vCap + v) = U.minF v ∧
    mem (ufOldRBase ufBase vCap + v) = U.oldR v
  hActNd : act.Nodup
  hActLt : ∀ x ∈ act, x < vCap
  hActIff : ∀ v < vCap, U.sz v ≠ 0 ↔ v ∈ act
  hZeroRest : ∀ v < vCap, U.sz v = 0 → U.par v = 0 ∧ U.minF v = 0 ∧ U.oldR v = 0
  hActLen : mem (ufActLenAddr ufBase vCap) = act.length
  hActAt : ListAt mem (ufActBase ufBase vCap) act
  hActZero : ∀ i, act.length ≤ i → i < vCap → mem (ufActBase ufBase vCap + i) = 0
  hRootSum : (act.toFinset.filter fun r => U.par r = r).sum U.sz = act.length

lemma RevUFMemAt.act_len_le {mem : ℕ → ℕ} {ufBase vCap : ℕ} {isNew : ℕ → Bool}
    {U : RevUFState} {act : List ℕ} (h : RevUFMemAt mem ufBase vCap isNew U act) :
    act.length ≤ vCap := by
  rw [← List.toFinset_card_of_nodup h.hActNd]
  exact (Finset.card_le_card (t := Finset.range vCap) fun x hx =>
    Finset.mem_range.mpr (h.hActLt x (List.mem_toFinset.mp hx))).trans (by simp)

lemma RevUFMemAt.sz_le_act {mem : ℕ → ℕ} {ufBase vCap : ℕ} {isNew : ℕ → Bool}
    {U : RevUFState} {act : List ℕ} (h : RevUFMemAt mem ufBase vCap isNew U act)
    {r : ℕ} (hr_lt : r < vCap) (hr_act : 1 ≤ U.sz r) (hr_par : U.par r = r) :
    U.sz r ≤ act.length := by
  have hr_mem : r ∈ act.toFinset.filter fun x => U.par x = x :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((h.hActIff r hr_lt).mp (by omega)), hr_par⟩
  calc U.sz r ≤ (act.toFinset.filter fun x => U.par x = x).sum U.sz :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr_mem
    _ = act.length := h.hRootSum

lemma revUFMemAt_zero {mem : ℕ → ℕ} {ufBase vCap : ℕ} {isNew : ℕ → Bool}
    (hIsNew : ∀ v < vCap, mem (ufIsNewBase ufBase + v) = if isNew v then 1 else 0)
    (hZero : ∀ a, ufBase + vCap ≤ a → a < ufBase + ufScratchSize vCap → mem a = 0) :
    RevUFMemAt mem ufBase vCap isNew RevUFState.zero [] := by
  refine ⟨hIsNew, fun v hv => ⟨?_, ?_, ?_, ?_⟩, List.nodup_nil, fun _ h => by simp at h,
    fun v _ => by simp [RevUFState.zero], fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    hZero _ (by dsimp [ufActLenAddr]; omega) (by dsimp [ufActLenAddr, ufScratchSize]; omega),
    fun _ hi => by simp at hi,
    fun i _ hi => hZero _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase, ufScratchSize]; omega),
    by simp⟩
  · exact hZero _ (by dsimp [ufParBase]; omega) (by dsimp [ufParBase, ufScratchSize]; omega)
  · exact hZero _ (by dsimp [ufSzBase]; omega) (by dsimp [ufSzBase, ufScratchSize]; omega)
  · exact hZero _ (by dsimp [ufMinFBase]; omega) (by dsimp [ufMinFBase, ufScratchSize]; omega)
  · exact hZero _ (by dsimp [ufOldRBase]; omega) (by dsimp [ufOldRBase, ufScratchSize]; omega)

lemma revUFMemAt_of_agree {mem mem' : ℕ → ℕ} {ufBase vCap : ℕ} {isNew : ℕ → Bool}
    {U : RevUFState} {act : List ℕ}
    (h : RevUFMemAt mem ufBase vCap isNew U act)
    (hag : ∀ a, ufBase ≤ a → a < ufBase + ufScratchSize vCap → mem' a = mem a) :
    RevUFMemAt mem' ufBase vCap isNew U act := by
  refine ⟨fun v hv => (hag _ (by dsimp [ufIsNewBase]; omega) (by dsimp [ufIsNewBase, ufScratchSize]; omega)).trans (h.hIsNew v hv),
    fun v hv => ⟨
      (hag _ (by dsimp [ufParBase]; omega) (by dsimp [ufParBase, ufScratchSize]; omega)).trans (h.hArrs v hv).1,
      (hag _ (by dsimp [ufSzBase]; omega) (by dsimp [ufSzBase, ufScratchSize]; omega)).trans (h.hArrs v hv).2.1,
      (hag _ (by dsimp [ufMinFBase]; omega) (by dsimp [ufMinFBase, ufScratchSize]; omega)).trans (h.hArrs v hv).2.2.1,
      (hag _ (by dsimp [ufOldRBase]; omega) (by dsimp [ufOldRBase, ufScratchSize]; omega)).trans (h.hArrs v hv).2.2.2⟩,
    h.hActNd, h.hActLt, h.hActIff, h.hZeroRest,
    (hag _ (by dsimp [ufActLenAddr]; omega) (by dsimp [ufActLenAddr, ufScratchSize]; omega)).trans h.hActLen,
    fun i hi => (hag _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase, ufScratchSize]; have := h.act_len_le; omega)).trans (h.hActAt i hi),
    fun i hi1 hi2 => (hag _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase, ufScratchSize]; omega)).trans (h.hActZero i hi1 hi2),
    h.hRootSum⟩

/-! ## 2. Procedure 1: `compUFInitFindProc` (`[ufBase, vCap, r]`) -/

/-- `args = [ufBase, vCap, r]`: lazily initializes `r` if `sz[r] = 0` (appending `r` to `actList`),
then walks `par` until `par[cur] = cur`, returning `cur`. -/
def compUFInitFindProc : Stmt :=
  .assign 3 (.bin .add (.reg 0) (.reg 1)) ;;
  .assign 4 (.bin .add (.reg 3) (.reg 1)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 1)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 1)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 1)) ;;
  .assign 9 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .cond (.bin .eq (.reg 9) (.const 0))
    (.assign 10 (.load (.reg 8)) ;;
     .store (.bin .add (.reg 7) (.reg 10)) (.reg 2) ;;
     .store (.reg 8) (.bin .add (.reg 10) (.const 1)) ;;
     .store (.bin .add (.reg 3) (.reg 2)) (.reg 2) ;;
     .store (.bin .add (.reg 4) (.reg 2)) (.const 1) ;;
     .store (.bin .add (.reg 5) (.reg 2)) (.reg 2) ;;
     .assign 11 (.load (.bin .add (.reg 0) (.reg 2))) ;;
     .cond (.bin .eq (.reg 11) (.const 0))
       (.store (.bin .add (.reg 6) (.reg 2)) (.bin .add (.reg 2) (.const 1)))
       (.store (.bin .add (.reg 6) (.reg 2)) (.const 0)))
    .nop ;;
  .assign 12 (.reg 2) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
  .loop (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 13) (.reg 12)) (.bin .lt (.reg 12) (.reg 13))))
    (.assign 12 (.reg 13) ;;
     .assign 13 (.load (.bin .add (.reg 3) (.reg 12)))) ;;
  .ret (.reg 12)

lemma compUFInitFindProc_noRand : compUFInitFindProc.NoRand := by
  simp [compUFInitFindProc, Stmt.NoRand]

/-- Helper: parent-walk loop verification for `compUFInitFindProc`. -/
private lemma compUFFindLoop_runs {w parBase vCap : ℕ} {par : ℕ → ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hpar_w : parBase + vCap < 2 ^ w)
    (hpar_mem : ∀ v < vCap, st.mem (parBase + v) = par v)
    (hr3 : st.regs 3 = parBase)
    {cur rep steps : ℕ}
    (hchain : ∀ j ≤ steps, (par^[j] cur) < vCap)
    (hstop : par (par^[steps] cur) = par^[steps] cur)
    (hrep : par^[steps] cur = rep)
    (hneq : ∀ j < steps, par (par^[j] cur) ≠ par^[j] cur)
    (hr12 : st.regs 12 = cur) (hr13 : st.regs 13 = par cur) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 13) (.reg 12)) (.bin .lt (.reg 12) (.reg 13))))
          (.assign 12 (.reg 13) ;;
           .assign 13 (.load (.bin .add (.reg 3) (.reg 12)))))
        st .normal st' c ∧
      st'.mem = st.mem ∧ st'.regs 12 = rep ∧ c ≤ 20 * steps + 12 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  induction steps generalizing cur st with
  | zero =>
    have hcur_eq : cur = rep := hrep
    subst hcur_eq
    have heq : par cur = cur := hstop
    refine ⟨st, 10, runs_loop_iff.mpr (Or.inl ⟨?_, rfl, rfl, by simp [Expr.size]⟩), rfl, hr12, by omega⟩
    simp [Expr.eval, BinOp.eval, hr12, hr13, heq, hw0']
  | succ k ih =>
    have hne : par cur ≠ cur := hneq 0 (Nat.zero_lt_succ k)
    have hlt_or : par cur < cur ∨ cur < par cur := lt_or_gt_of_ne hne
    have hcond_val : (if par cur < cur then 1 else 0) + (if cur < par cur then 1 else 0) = 1 := by
      rcases hlt_or with h | h <;> simp [h, Nat.not_lt_of_gt h]
    have hp_lt : par cur < vCap := by simpa using hchain 1 (by omega)
    let s1 : State := { st with regs := Function.update st.regs 12 (par cur) }
    let s2 : State := { s1 with regs := Function.update s1.regs 13 (par (par cur)) }
    have h1 : Runs w p ω (.assign 12 (.reg 13)) st .normal s1 2 :=
      runs_assign_iff.mpr ⟨par cur, by simp [Expr.eval, hr13], rfl, rfl, by simp [Expr.size]⟩
    have h2 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 3) (.reg 12)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨par (par cur), Expr.eval_load_of_eq (by
        simp [s1, Expr.eval, BinOp.eval, hr3, show parBase + par cur < 2 ^ w by omega])
        (hpar_mem (par cur) hp_lt), rfl, rfl, by simp [Expr.size]⟩
    have hbody : Runs w p ω _ st .normal s2 8 :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, 5, h1, h2, rfl⟩)
    obtain ⟨st', cRest, hrest, hmem', hr12', hcRest⟩ :=
      ih (st := s2) (cur := par cur) hpar_mem (by simp [s2, s1, hr3])
        (fun j hj => by simpa [Function.iterate_succ_apply] using hchain (j + 1) (by omega))
        (by simpa [Function.iterate_succ_apply] using hstop)
        (by simpa [Function.iterate_succ_apply] using hrep)
        (fun j hj => by simpa [Function.iterate_succ_apply] using hneq (j + 1) (by omega))
        (by simp [s2, s1]) (by simp [s2])
    have hcond_eval : Expr.eval w st
        (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 13) (.reg 12)) (.bin .lt (.reg 12) (.reg 13)))) = some 1 := by
      have h1_lt : (1 : ℕ) < 2 ^ w := by omega
      rcases hlt_or with h | h <;>
        simp [Expr.eval, BinOp.eval, hr12, hr13, hw0', h, Nat.not_lt_of_gt h, h1_lt]
    have hfull : Runs w p ω
        (.loop (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 13) (.reg 12)) (.bin .lt (.reg 12) (.reg 13))))
          (.assign 12 (.reg 13) ;;
           .assign 13 (.load (.bin .add (.reg 3) (.reg 12))))) st .normal st' (8 + cRest + 10) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s2, 8, cRest, hcond_eval, by decide,
        hbody, hrest, by simp [Expr.size]; omega⟩))
    exact ⟨st', 8 + cRest + 10, hfull, hmem', hr12', by omega⟩

/-- Helper: `ufFindFuel` translates directly to `par^[j]` chain hypotheses for `compUFFindLoop_runs`. -/
private lemma ufFindFuel_to_iter {par : ℕ → ℕ} {x rep : ℕ} :
    ∀ steps, ufFindFuel steps par x = rep → par rep = rep →
      ∃ k ≤ steps, par^[k] x = rep ∧ (∀ j < k, par (par^[j] x) ≠ par^[j] x) := by
  intro steps
  induction steps generalizing x with
  | zero =>
    intro hf _
    exact ⟨0, le_rfl, hf, fun _ h => by omega⟩
  | succ s ih =>
    intro hf hrep
    by_cases hpx : par x = x
    · simp only [ufFindFuel, hpx, ↓reduceIte] at hf
      exact ⟨0, Nat.zero_le _, hf, fun _ h => by omega⟩
    · simp only [ufFindFuel, hpx, ↓reduceIte] at hf
      obtain ⟨k, hk, heq, hne⟩ := ih hf hrep
      refine ⟨k + 1, Nat.succ_le_succ hk, by simpa [Function.iterate_succ_apply] using heq, fun j hj => ?_⟩
      cases j with
      | zero => simpa using hpx
      | succ j => simpa [Function.iterate_succ_apply] using hne j (Nat.lt_of_succ_lt_succ hj)

set_option maxHeartbeats 600000 in
/-- Verification of `compUFInitFindProc`: lazily initializes `r` if needed, preserves `RevUFInv`
and `RevUFMemAt`, returns active UF root `rep` connected to `r` in `F`, frames outside
`[ufBase + vCap, ufBase + 6 * vCap + 1)`, and costs `≤ 20 * Nat.log 2 (act'.length) + 120`. -/
theorem compUFInitFind_runs {w ufBase vCap r : ℕ} {F : MGraph} {RF' : RootedForest}
    {R_old : Finset ℕ} {isNew : ℕ → Bool} {U : RevUFState} {act : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (huf_w : ufBase + ufScratchSize vCap < 2 ^ w)
    (hR_lt : ∀ x ∈ RF'.R, x < vCap)
    (hOld : R_old ⊆ RF'.R)
    (hRF'V : ∀ x ∈ RF'.R, x ∈ F.V)
    (hisNew : ∀ x ∈ RF'.R, isNew x = false ↔ x ∈ R_old)
    (hU : RevUFInv F RF' R_old U)
    (hMem : RevUFMemAt mem ufBase vCap isNew U act)
    (hrR : r ∈ RF'.R) :
    let U' := ufInitOne (fun x => !isNew x) U r
    let act' := if U.sz r = 0 then act ++ [r] else act
    ∃ rep st' c,
      Runs w p ω compUFInitFindProc (startState [ufBase, vCap, r] mem pos) (.returned rep) st' c ∧
      RevUFInv F RF' R_old U' ∧
      RevUFMemAt st'.mem ufBase vCap isNew U' act' ∧
      rep ∈ RF'.R ∧ 1 ≤ U'.sz rep ∧ U'.par rep = rep ∧ F.Connected r rep ∧
      (∀ a, a < ufBase + vCap ∨ ufBase + ufScratchSize vCap ≤ a → st'.mem a = mem a) ∧
      c ≤ 20 * Nat.log 2 act'.length + 125 := by
  intro U' act'
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hr_lt : r < vCap := hR_lt r hrR
  have hisOld : ∀ x ∈ RF'.R, (!isNew x) = true ↔ x ∈ R_old := fun x hx => by
    simp [hisNew x hx]
  obtain ⟨hU', hrAct'⟩ := revUFInv_initOne hU hOld hRF'V hisOld hrR
  -- Prefix: compute the 6 base addresses and load `sz[r]`
  set st0 := startState [ufBase, vCap, r] mem pos
  have huf_sz : ufScratchSize vCap = 6 * vCap + 1 := rfl
  let st1 : State := { st0 with regs := Function.update st0.regs 3 (ufParBase ufBase vCap) }
  let st2 : State := { st1 with regs := Function.update st1.regs 4 (ufSzBase ufBase vCap) }
  let st3 : State := { st2 with regs := Function.update st2.regs 5 (ufMinFBase ufBase vCap) }
  let st4 : State := { st3 with regs := Function.update st3.regs 6 (ufOldRBase ufBase vCap) }
  let st5 : State := { st4 with regs := Function.update st4.regs 7 (ufActBase ufBase vCap) }
  let st6 : State := { st5 with regs := Function.update st5.regs 8 (ufActLenAddr ufBase vCap) }
  let st7 : State := { st6 with regs := Function.update st6.regs 9 (U.sz r) }
  have hp1 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.reg 1))) st0 .normal st1 4 :=
    runs_assign_iff.mpr ⟨ufParBase ufBase vCap, by
      simp [st0, startState, Expr.eval, BinOp.eval, ufParBase, show ufBase + vCap < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.reg 1))) st1 .normal st2 4 :=
    runs_assign_iff.mpr ⟨ufSzBase ufBase vCap, by
      simp [st1, st0, startState, Expr.eval, BinOp.eval, ufParBase, ufSzBase, show ufBase + vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 1))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨ufMinFBase ufBase vCap, by
      simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, ufSzBase, ufMinFBase, show ufBase + 2 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 1))) st3 .normal st4 4 :=
    runs_assign_iff.mpr ⟨ufOldRBase ufBase vCap, by
      simp [st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, ufOldRBase, show ufBase + 3 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 1))) st4 .normal st5 4 :=
    runs_assign_iff.mpr ⟨ufActBase ufBase vCap, by
      simp [st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, ufActBase, show ufBase + 4 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 1))) st5 .normal st6 4 :=
    runs_assign_iff.mpr ⟨ufActLenAddr ufBase vCap, by
      simp [st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufActBase, ufActLenAddr, show ufBase + 5 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 4) (.reg 2)))) st6 .normal st7 5 :=
    runs_assign_iff.mpr ⟨U.sz r, Expr.eval_load_of_eq (by
      simp [st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufSzBase, show ufBase + 2 * vCap + r < 2 ^ w by omega])
      (hMem.hArrs r hr_lt).2.1, rfl, rfl, by simp [Expr.size]⟩
  -- Conditional lazy initialization
  have hinit_branch : ∃ st8 c8,
      Runs w p ω
        (.cond (.bin .eq (.reg 9) (.const 0))
          (.assign 10 (.load (.reg 8)) ;;
           .store (.bin .add (.reg 7) (.reg 10)) (.reg 2) ;;
           .store (.reg 8) (.bin .add (.reg 10) (.const 1)) ;;
           .store (.bin .add (.reg 3) (.reg 2)) (.reg 2) ;;
           .store (.bin .add (.reg 4) (.reg 2)) (.const 1) ;;
           .store (.bin .add (.reg 5) (.reg 2)) (.reg 2) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.reg 2))) ;;
           .cond (.bin .eq (.reg 11) (.const 0))
             (.store (.bin .add (.reg 6) (.reg 2)) (.bin .add (.reg 2) (.const 1)))
             (.store (.bin .add (.reg 6) (.reg 2)) (.const 0)))
          .nop)
        st7 .normal st8 c8 ∧
      st8.regs 2 = r ∧ st8.regs 3 = ufParBase ufBase vCap ∧
      RevUFMemAt st8.mem ufBase vCap isNew U' act' ∧
      (∀ a, a < ufBase + vCap ∨ ufBase + ufScratchSize vCap ≤ a → st8.mem a = mem a) ∧
      c8 ≤ 60 := by
    by_cases hsz0 : U.sz r = 0
    · have hr_notin : r ∉ act := fun hm => ((hMem.hActIff r hr_lt).mpr hm) hsz0
      have hact_lt : act.length < vCap := by
        have hsub : insert r act.toFinset ⊆ Finset.range vCap := by
          intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Finset.mem_range.mpr hr_lt
          · exact Finset.mem_range.mpr (hMem.hActLt x (List.mem_toFinset.mp hx'))
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hr_notin]), List.toFinset_card_of_nodup hMem.hActNd, Finset.card_range] at hcard
        omega
      let a1 : State := { st7 with regs := Function.update st7.regs 10 act.length }
      let a2 : State := { a1 with mem := Function.update a1.mem (ufActBase ufBase vCap + act.length) r }
      let a3 : State := { a2 with mem := Function.update a2.mem (ufActLenAddr ufBase vCap) (act.length + 1) }
      let a4 : State := { a3 with mem := Function.update a3.mem (ufParBase ufBase vCap + r) r }
      let a5 : State := { a4 with mem := Function.update a4.mem (ufSzBase ufBase vCap + r) 1 }
      let a6 : State := { a5 with mem := Function.update a5.mem (ufMinFBase ufBase vCap + r) r }
      set newFlag := if isNew r then 1 else 0
      let a7 : State := { a6 with regs := Function.update a6.regs 11 newFlag }
      set oldVal := if !isNew r then r + 1 else 0
      let a8 : State := { a7 with mem := Function.update a7.mem (ufOldRBase ufBase vCap + r) oldVal }
      have hne_isNew : ufIsNewBase ufBase + r ≠ ufMinFBase ufBase vCap + r ∧
          ufIsNewBase ufBase + r ≠ ufSzBase ufBase vCap + r ∧
          ufIsNewBase ufBase + r ≠ ufParBase ufBase vCap + r ∧
          ufIsNewBase ufBase + r ≠ ufActLenAddr ufBase vCap ∧
          ufIsNewBase ufBase + r ≠ ufActBase ufBase vCap + act.length := by
        dsimp only [ufIsNewBase, ufParBase, ufSzBase, ufMinFBase, ufActBase, ufActLenAddr]
        exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      have hs1 : Runs w p ω (.assign 10 (.load (.reg 8))) st7 .normal a1 3 :=
        runs_assign_iff.mpr ⟨act.length, Expr.eval_load_of_eq (by simp [st7, st6, Expr.eval]) hMem.hActLen,
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 7) (.reg 10)) (.reg 2)) a1 .normal a2 5 :=
        runs_store_iff.mpr ⟨ufActBase ufBase vCap + act.length, r,
          by simp [a1, st7, st6, st5, Expr.eval, BinOp.eval, ufActBase, show ufBase + 5 * vCap + act.length < 2 ^ w by omega],
          by simp [a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w p ω (.store (.reg 8) (.bin .add (.reg 10) (.const 1))) a2 .normal a3 5 :=
        runs_store_iff.mpr ⟨ufActLenAddr ufBase vCap, act.length + 1,
          by simp [a2, a1, st7, st6, Expr.eval],
          by simp [a2, a1, Expr.eval, BinOp.eval, hw1, show act.length + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hs4 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 2)) (.reg 2)) a3 .normal a4 5 :=
        runs_store_iff.mpr ⟨ufParBase ufBase vCap + r, r,
          by simp [a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufParBase, show ufBase + vCap + r < 2 ^ w by omega],
          by simp [a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hs5 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 2)) (.const 1)) a4 .normal a5 5 :=
        runs_store_iff.mpr ⟨ufSzBase ufBase vCap + r, 1,
          by simp [a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufSzBase, show ufBase + 2 * vCap + r < 2 ^ w by omega],
          by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
      have hs6 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 2)) (.reg 2)) a5 .normal a6 5 :=
        runs_store_iff.mpr ⟨ufMinFBase ufBase vCap + r, r,
          by simp [a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, show ufBase + 3 * vCap + r < 2 ^ w by omega],
          by simp [a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have ha6_new : a6.mem (ufBase + r) = newFlag := by
        dsimp only [a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState]
        have hm := hMem.hIsNew r hr_lt
        dsimp only [ufIsNewBase] at hm hne_isNew
        rw [Function.update_of_ne hne_isNew.1, Function.update_of_ne hne_isNew.2.1,
            Function.update_of_ne hne_isNew.2.2.1, Function.update_of_ne hne_isNew.2.2.2.1,
            Function.update_of_ne hne_isNew.2.2.2.2]
        exact hm
      have hs7 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.reg 2)))) a6 .normal a7 5 :=
        runs_assign_iff.mpr ⟨newFlag, Expr.eval_load_of_eq
          (by simp [a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, show ufBase + r < 2 ^ w by omega])
          ha6_new, rfl, rfl, by simp [Expr.size]⟩
      have hs8 : Runs w p ω
          (.cond (.bin .eq (.reg 11) (.const 0))
            (.store (.bin .add (.reg 6) (.reg 2)) (.bin .add (.reg 2) (.const 1)))
            (.store (.bin .add (.reg 6) (.reg 2)) (.const 0))) a7 .normal a8 (if isNew r then 9 else 11) := by
        cases hnr : isNew r
        · have hnf : newFlag = 0 := by simp [newFlag, hnr]
          have hov : oldVal = r + 1 := by simp [oldVal, hnr]
          refine runs_cond_iff.mpr ⟨1, 7, by simp [a7, Expr.eval, BinOp.eval, hnf, hw0, hw0'], ?_, by simp [Expr.size]⟩
          simp only [one_ne_zero, ↓reduceIte]
          exact runs_store_iff.mpr ⟨ufOldRBase ufBase vCap + r, oldVal,
            by simp [a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, show ufBase + 4 * vCap + r < 2 ^ w by omega],
            by simp [a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, hw1, hov, show r + 1 < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        · have hnf : newFlag = 1 := by simp [newFlag, hnr]
          have hov : oldVal = 0 := by simp [oldVal, hnr]
          refine runs_cond_iff.mpr ⟨0, 5, by simp [a7, Expr.eval, BinOp.eval, hnf, hw0'], ?_, by simp [Expr.size]⟩
          simp only [↓reduceIte]
          exact runs_store_iff.mpr ⟨ufOldRBase ufBase vCap + r, oldVal,
            by simp [a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, show ufBase + 4 * vCap + r < 2 ^ w by omega],
            by simp [Expr.eval, hov, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have h78 := runs_seq_iff.mpr (Or.inr ⟨a7, 5, _, hs7, hs8, rfl⟩)
      have h68 := runs_seq_iff.mpr (Or.inr ⟨a6, 5, _, hs6, h78, rfl⟩)
      have h58 := runs_seq_iff.mpr (Or.inr ⟨a5, 5, _, hs5, h68, rfl⟩)
      have h48 := runs_seq_iff.mpr (Or.inr ⟨a4, 5, _, hs4, h58, rfl⟩)
      have h38 := runs_seq_iff.mpr (Or.inr ⟨a3, 5, _, hs3, h48, rfl⟩)
      have h28 := runs_seq_iff.mpr (Or.inr ⟨a2, 5, _, hs2, h38, rfl⟩)
      have hthen := runs_seq_iff.mpr (Or.inr ⟨a1, 3, _, hs1, h28, rfl⟩)
      have hU'_eq : U' = ⟨Function.update U.par r r, Function.update U.sz r 1,
          Function.update U.minF r r, Function.update U.oldR r oldVal⟩ := by
        simp [U', ufInitOne, hsz0, oldVal]
      have hact'_eq : act' = act ++ [r] := by simp [act', hsz0]
      have ha8_fr : ∀ a, a < ufBase + vCap ∨ ufBase + ufScratchSize vCap ≤ a → a8.mem a = mem a := fun a ha => by
        dsimp only [a8, a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState]
        dsimp only [ufOldRBase, ufMinFBase, ufSzBase, ufParBase, ufActLenAddr, ufActBase, ufScratchSize] at ha ⊢
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hMem8 : RevUFMemAt a8.mem ufBase vCap isNew U' act' := by
        rw [hU'_eq, hact'_eq]
        refine ⟨fun v hv => (ha8_fr _ (Or.inl (by dsimp [ufIsNewBase]; omega))).trans (hMem.hIsNew v hv),
          fun v hv => ?_, List.nodup_append.mpr ⟨hMem.hActNd, List.nodup_singleton r, fun x hx y hy => by
            simp only [List.mem_singleton] at hy; subst hy; exact fun h => hr_notin (h ▸ hx)⟩,
          fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hMem.hActLt x hx
            · simp only [List.mem_singleton] at hx; subst hx; exact hr_lt,
          fun v hv => by
            dsimp only; by_cases hvr : v = r
            · subst hvr; simp
            · rw [Function.update_of_ne hvr]; simp [hvr, hMem.hActIff v hv],
          fun v hv hzv => by
            dsimp only at hzv ⊢; by_cases hvr : v = r
            · subst hvr; simp at hzv
            · rw [Function.update_of_ne hvr] at hzv ⊢
              rw [Function.update_of_ne hvr, Function.update_of_ne hvr]
              exact hMem.hZeroRest v hv hzv,
          by dsimp only [a8, a7, a6, a5, a4, a3, a2, a1]; simp only [List.length_append, List.length_singleton]
             dsimp only [ufOldRBase, ufMinFBase, ufSzBase, ufParBase, ufActLenAddr]
             rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                 Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
          fun i hi => by
            dsimp only [a8, a7, a6, a5, a4, a3, a2, a1]
            dsimp only [ufOldRBase, ufMinFBase, ufSzBase, ufParBase, ufActLenAddr, ufActBase]
            simp only [List.length_append, List.length_singleton] at hi
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
            by_cases hil : i < act.length
            · rw [Function.update_of_ne (by omega), List.getElem_append_left hil]; exact hMem.hActAt i hil
            · have hie : i = act.length := by omega
              subst hie; simp,
          fun i hi1 hi2 => by
            simp only [List.length_append, List.length_singleton] at hi1
            dsimp only [a8, a7, a6, a5, a4, a3, a2, a1, ufOldRBase, ufMinFBase, ufSzBase, ufParBase, ufActLenAddr, ufActBase]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hMem.hActZero i (by omega) hi2, ?_⟩
        · dsimp only [a8, a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState,
            ufOldRBase, ufMinFBase, ufSzBase, ufParBase, ufActLenAddr, ufActBase]
          have ha := hMem.hArrs v hv
          dsimp only [ufOldRBase, ufMinFBase, ufSzBase, ufParBase] at ha
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            by_cases hvr : v = r
            · subst hvr; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne hvr]; exact ha.1
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            by_cases hvr : v = r
            · subst hvr; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne hvr]; exact ha.2.1
          · rw [Function.update_of_ne (by omega)]
            by_cases hvr : v = r
            · subst hvr; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne hvr]; exact ha.2.2.1
          · by_cases hvr : v = r
            · subst hvr; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne hvr]; exact ha.2.2.2
        · -- `hRootSum`: inserting `r` adds `1` to root sum
          dsimp only
          have hset : ((act ++ [r]).toFinset.filter fun x => Function.update U.par r r x = x) =
              insert r (act.toFinset.filter fun x => U.par x = x) := by
            ext x; simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
              Finset.mem_filter, Finset.mem_insert]
            by_cases hxr : x = r
            · subst hxr; simp
            · simp [hxr]
          have hr_not_f : r ∉ act.toFinset.filter fun x => U.par x = x := by simp [hr_notin]
          rw [hset, Finset.sum_insert hr_not_f, Function.update_self]
          have hsum_eq : (act.toFinset.filter fun x => U.par x = x).sum (Function.update U.sz r 1) =
              (act.toFinset.filter fun x => U.par x = x).sum U.sz :=
            Finset.sum_congr rfl fun x hx =>
              Function.update_of_ne (show x ≠ r from fun h => hr_not_f (h ▸ hx)) _ _
          rw [hsum_eq, hMem.hRootSum, List.length_append, List.length_singleton]; omega
      refine ⟨a8, _, runs_cond_iff.mpr ⟨1, _, by simp [st7, Expr.eval, BinOp.eval, hsz0, hw0, hw0'],
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩,
        by simp [a8, a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1, st0, startState],
        by simp [a8, a7, a6, a5, a4, a3, a2, a1, st7, st6, st5, st4, st3, st2, st1],
        hMem8, ha8_fr, by simp only [Expr.size]; split_ifs <;> omega⟩
    · have hU'_eq : U' = U := by simp [U', ufInitOne, hsz0]
      have hact'_eq : act' = act := by simp [act', hsz0]
      refine ⟨st7, 5, runs_cond_iff.mpr ⟨0, 1, by simp [st7, Expr.eval, BinOp.eval, hsz0, hw0'],
        by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState],
        by simp [st7, st6, st5, st4, st3, st2, st1],
        by rw [hU'_eq, hact'_eq]; exact hMem, fun _ _ => rfl, by omega⟩
  obtain ⟨st8, c8, hrun8, hr8_2, hr8_3, hMem8, hfr8, hc8⟩ := hinit_branch
  -- Parent-walk loop using `RevUFInv.find_terminates`
  obtain ⟨rep, steps0, hrepR, hrepAct, hrepPar, hconn, hfind, _, _, hlog0⟩ :=
    hU'.find_terminates hrR hrAct'
  obtain ⟨kSteps, hk_le, hk_rep, hk_ne⟩ := ufFindFuel_to_iter steps0 hfind hrepPar
  have hchain_R : ∀ j ≤ kSteps, (U'.par^[j] r) ∈ RF'.R ∧ 1 ≤ U'.sz (U'.par^[j] r) := by
    intro j hj
    induction j with
    | zero => exact ⟨hrR, hrAct'⟩
    | succ j ih =>
      obtain ⟨hjR, hjAct⟩ := ih (Nat.le_of_succ_le hj)
      have hp := hU'.hActivePar _ hjR hjAct
      simpa [Function.iterate_succ_apply'] using ⟨hp.1, hp.2.1⟩
  let st9 : State := { st8 with regs := Function.update st8.regs 12 r }
  let st10 : State := { st9 with regs := Function.update st9.regs 13 (U'.par r) }
  have h9 : Runs w p ω (.assign 12 (.reg 2)) st8 .normal st9 2 :=
    runs_assign_iff.mpr ⟨r, by simp [Expr.eval, hr8_2], rfl, rfl, by simp [Expr.size]⟩
  have h10 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 3) (.reg 12)))) st9 .normal st10 5 :=
    runs_assign_iff.mpr ⟨U'.par r, Expr.eval_load_of_eq (by
      simp [st9, Expr.eval, BinOp.eval, hr8_3, ufParBase, show ufBase + vCap + r < 2 ^ w by omega])
      (hMem8.hArrs r hr_lt).1, rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st11, cLoop, hloop, hmem11, hr11_12, hcLoop⟩ :=
    compUFFindLoop_runs (p := p) (ω := ω) (st := st10) (parBase := ufParBase ufBase vCap)
      (vCap := vCap) (par := U'.par) (cur := r) (rep := rep) (steps := kSteps)
      hw16 (by dsimp [ufParBase]; omega) (fun v hv => (hMem8.hArrs v hv).1) (by simp [st10, st9, hr8_3])
      (fun j hj => hR_lt _ (hchain_R j hj).1) (hk_rep ▸ hrepPar) hk_rep hk_ne
      (by simp [st10, st9]) (by simp [st10])
  have hret : Runs w p ω (.ret (.reg 12)) st11 (.returned rep) st11 2 :=
    runs_ret_iff.mpr ⟨rep, by simp [Expr.eval, hr11_12], rfl, rfl, by simp [Expr.size]⟩
  -- Chain everything
  have hrun_full : Runs w p ω compUFInitFindProc st0 (.returned rep) st11 (49 + c8 + cLoop) := by
    have t10 := runs_seq_iff.mpr (Or.inr ⟨st11, cLoop, 2, hloop, hret, rfl⟩)
    have t9 := runs_seq_iff.mpr (Or.inr ⟨st10, 5, _, h10, t10, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨st9, 2, _, h9, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨st8, c8, _, hrun8, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨st7, 5, _, hp7, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨st6, 4, _, hp6, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨st5, 4, _, hp5, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨st4, 4, _, hp4, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, hp3, t3, rfl⟩)
    have t1 := runs_seq_iff.mpr (Or.inr ⟨st2, 4, _, hp2, t2, rfl⟩)
    have t0 := runs_seq_iff.mpr (Or.inr ⟨st1, 4, _, hp1, t1, rfl⟩)
    unfold compUFInitFindProc; convert t0 using 1; omega
  have hsz_le_act : U'.sz rep ≤ act'.length := hMem8.sz_le_act (hR_lt rep hrepR) hrepAct hrepPar
  have hlog_act : kSteps ≤ Nat.log 2 act'.length :=
    le_trans hk_le (le_trans hlog0 (Nat.log_mono_right hsz_le_act))
  refine ⟨rep, st11, 49 + c8 + cLoop, hrun_full, hU', hmem11.symm ▸ hMem8,
    hrepR, hrepAct, hrepPar, hconn, fun a ha => (congrFun hmem11 a).trans (hfr8 a ha), by omega⟩

/-! ## 3. Procedure 2: `compUFPairUnionProc` and Procedure 3: `compUFCleanProc` -/

/-- `args = [ufBase, vCap, ra, rb, outSlot, isRelFlag, edgeVal, doUnion]`:
computes `(kept, fresh) = ufPair U ra rb`, stores `[isRelFlag, edgeVal, kept, fresh]` at
`[outSlot, outSlot + 4)`, and if `doUnion ≠ 0` updates `par, sz, minF, oldR` by `ufUnion U ra rb`. -/
def compUFPairUnionProc : Stmt :=
  .assign 8 (.bin .add (.reg 0) (.reg 1)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 1)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 1)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 1)) ;;
  .assign 12 (.load (.bin .add (.reg 11) (.reg 2))) ;;
  .assign 13 (.load (.bin .add (.reg 10) (.reg 2))) ;;
  .assign 14 (.load (.bin .add (.reg 11) (.reg 3))) ;;
  .assign 15 (.load (.bin .add (.reg 10) (.reg 3))) ;;
  .cond (.bin .lt (.const 0) (.reg 12))
    (.assign 16 (.bin .sub (.reg 12) (.const 1)) ;;
     .assign 17 (.reg 15))
    (.cond (.bin .lt (.const 0) (.reg 14))
      (.assign 16 (.bin .sub (.reg 14) (.const 1)) ;;
       .assign 17 (.reg 13))
      (.cond (.bin .lt (.reg 15) (.reg 13))
        (.assign 16 (.reg 15) ;; .assign 17 (.reg 13))
        (.assign 16 (.reg 13) ;; .assign 17 (.reg 15)))) ;;
  .store (.reg 4) (.reg 5) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 6) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 16) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.reg 17) ;;
  .cond (.reg 7)
    (.assign 18 (.load (.bin .add (.reg 9) (.reg 2))) ;;
     .assign 19 (.load (.bin .add (.reg 9) (.reg 3))) ;;
     .cond (.bin .lt (.reg 18) (.reg 19))
       (.assign 20 (.reg 3) ;; .assign 21 (.reg 2) ;;
        .assign 22 (.reg 14) ;; .assign 23 (.reg 12))
       (.assign 20 (.reg 2) ;; .assign 21 (.reg 3) ;;
        .assign 22 (.reg 12) ;; .assign 23 (.reg 14)) ;;
     .store (.bin .add (.reg 8) (.reg 21)) (.reg 20) ;;
     .store (.bin .add (.reg 9) (.reg 20)) (.bin .add (.reg 18) (.reg 19)) ;;
     .cond (.bin .lt (.reg 13) (.reg 15))
       (.store (.bin .add (.reg 10) (.reg 20)) (.reg 13))
       (.store (.bin .add (.reg 10) (.reg 20)) (.reg 15)) ;;
     .cond (.reg 22)
       (.store (.bin .add (.reg 11) (.reg 20)) (.reg 22))
       (.store (.bin .add (.reg 11) (.reg 20)) (.reg 23)))
    .nop ;;
  .ret (.const 0)

lemma compUFPairUnionProc_noRand : compUFPairUnionProc.NoRand := by
  simp [compUFPairUnionProc, Stmt.NoRand]

/-- `args = [ufBase, vCap]`: zeroes `par, sz, minF, oldR` at every vertex in `actList`, zeroes
`actList[0..actLen-1]` and `actLen`, returning `0`. -/
def compUFCleanProc : Stmt :=
  .assign 2 (.bin .add (.reg 0) (.reg 1)) ;;
  .assign 3 (.bin .add (.reg 2) (.reg 1)) ;;
  .assign 4 (.bin .add (.reg 3) (.reg 1)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 1)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 1)) ;;
  .assign 8 (.load (.reg 7)) ;;
  .assign 9 (.const 0) ;;
  .loop (.bin .lt (.reg 9) (.reg 8))
    (.assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
     .store (.bin .add (.reg 2) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 3) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 4) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 5) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 6) (.reg 9)) (.const 0) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1))) ;;
  .store (.reg 7) (.const 0) ;;
  .ret (.const 0)

lemma compUFCleanProc_noRand : compUFCleanProc.NoRand := by
  simp [compUFCleanProc, Stmt.NoRand]

end

end MinCostFlow.SparseCore.Program
