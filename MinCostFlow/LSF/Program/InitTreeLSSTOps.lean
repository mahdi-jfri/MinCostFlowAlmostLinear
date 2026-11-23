module

public import MinCostFlow.LSF.Program.InitTreeLSSTOpsBase
public import MinCostFlow.LSF.Program.SharedProcs
public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.Machine.WideWord.LSSTProgram
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.DynGraphInsert
import MinCostFlow.LSF.Model
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Word-RAM sub-procedures for LSST tree lifting (`InitTreeLSSTOps`)

Provides verified Word-RAM helper procedures and contracts used by `InitTreeLSST`:
* `dgInitEmptyLocal_meetsContract`: local-zero version of `dgInitEmpty_meetsContract`.
* `lsstFrontierContract` / `lsstFrontier_meetsContract`: `MeetsContract` wrapper for
  `lsstFrontierProc`.
* `initCopyGStmt` / `initCopyG_meetsContract`: copies `G₀` into `lsfDgGPtr` with capacity `(vCap, eCap)`.
* `initMarkBridgesStmt` / `initMarkBridges_meetsContract`: computes `copyMod G₀` and marks bridge
  collision slots in `[usedBridgePtr, usedBridgePtr + 2 * m0 + n0)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow.DynSpanner.Program
open MinCostFlow.WideWord
open MinCostFlow.LSF

@[expose] public section

/-! ## Mark colliding bridge indices in `usedBridgePtr` -/

/-- Mark bridge IDs in `[eCap, eCap + 2 * m0 + n0)` that collide with `(weightedCopyGraph G₀ v).E + copyMod G₀`.
Args: `[eListPtr, multPtr, usedBridgePtr, m0, n0, eCap]`. -/
def initMarkBridgesStmt (bUtils : ℕ) : Stmt :=
  .call 6 (bUtils + idxUtilMemFill)
    [.reg 2, .bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4), .const 0] ;;
  ((.assign 6 (.const 0) ;;
    forRange 7 (.const 0) (.reg 3)
      (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
       .cond (.bin .lt (.reg 6) (.reg 8)) (.assign 6 (.reg 8)) .nop)) ;;
   (.cond (.bin .eq (.reg 3) (.const 0))
      (.assign 6 (.const 1))
      (.assign 6 (.bin .add (.reg 6) (.const 1))) ;;
    .assign 7 (.bin .add (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4))))) ;;
  forRange 8 (.const 0) (.reg 3)
    (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
     .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
     .assign 11 (.bin .add (.reg 9) (.reg 6)) ;;
     forRange 12 (.const 0) (.reg 10)
       (.cond (.bin .lt (.reg 11) (.reg 7))
         (.cond (.bin .lt (.reg 11) (.reg 5)) .nop
           (.store (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) (.const 1)) ;;
          .assign 11 (.bin .add (.reg 11) (.reg 6)))
         .nop)) ;;
  .ret (.const 0)

lemma initMarkBridgesStmt_noRand (bUtils : ℕ) : (initMarkBridgesStmt bUtils).NoRand := by
  simp [initMarkBridgesStmt, forRange, forUp, Stmt.NoRand]

def initMarkBridgesContract (w : ℕ) (G₀ : MGraph) (eList : List ℕ) (mult : ℕ → ℕ) : Contract where
  pre args mem := ∃ eListPtr multPtr usedBridgePtr m0 n0 eCap,
    args = [eListPtr, multPtr, usedBridgePtr, m0, n0, eCap] ∧
    16 ≤ 2 ^ w ∧ G₀.E.card = m0 ∧ G₀.n = n0 ∧
    (∀ e ∈ G₀.E, e < eCap) ∧
    eCap + (2 * m0 + n0) + eCap < 2 ^ w ∧
    usedBridgePtr + (2 * m0 + n0) < 2 ^ w ∧
    eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
    ListAt mem eListPtr eList ∧
    eListPtr + m0 < 2 ^ w ∧
    (eListPtr + m0 ≤ usedBridgePtr ∨ usedBridgePtr + (2 * m0 + n0) ≤ eListPtr) ∧
    (∀ j < m0, mem (multPtr + j) = mult j ∧ mult j < 2 ^ w) ∧
    multPtr + m0 < 2 ^ w ∧
    (multPtr + m0 ≤ usedBridgePtr ∨ usedBridgePtr + (2 * m0 + n0) ≤ multPtr)
  post args mem ret mem' := ∃ eListPtr multPtr usedBridgePtr m0 n0 eCap,
    args = [eListPtr, multPtr, usedBridgePtr, m0, n0, eCap] ∧ ret = 0 ∧
    (∀ z < 2 * m0 + n0,
      (mem' (usedBridgePtr + z) = 1 ↔
        ∃ j < m0, ∃ k < mult j, eList.getD j 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem' (usedBridgePtr + z) = 0 ∨ mem' (usedBridgePtr + z) = 1)) ∧
    ∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + (2 * m0 + n0) ≤ addr → mem' addr = mem addr
  cost args mem :=
    let m0 := args.getD 3 0
    let n0 := args.getD 4 0
    let M_copies := (List.map (fun j => mem (args.getD 1 0 + j)) (List.range m0)).sum
    120 * m0 + 40 * M_copies + 20 * n0 + 120

private lemma copyMod_eq_foldl {G₀ : MGraph} {eList : List ℕ}
    (heMem : ∀ e, e ∈ eList ↔ e ∈ G₀.E) :
    (if eList.length = 0 then 1 else eList.foldl max 0 + 1) = copyMod G₀ := by
  by_cases hm : eList.length = 0
  · have hE : G₀.E = ∅ := by
      ext e; rw [← heMem, List.length_eq_zero_iff.mp hm]; simp
    simp [hm, copyMod, hE]
  · rw [ite_eq_right hm]
    have hsup : eList.foldl max 0 = G₀.E.sup id := by
      apply le_antisymm
      · have hle : ∀ (L : List ℕ) (acc : ℕ), acc ≤ G₀.E.sup id →
            (∀ x ∈ L, x ∈ G₀.E) → L.foldl max acc ≤ G₀.E.sup id := by
          intro L acc hacc hL
          induction L generalizing acc with
          | nil => exact hacc
          | cons hd tl ih =>
            refine ih (max acc hd) (max_le hacc ?_) (fun x hx => hL x (List.mem_cons_of_mem hd hx))
            exact Finset.le_sup (f := id) (hL hd (by simp))
        exact hle eList 0 (Nat.zero_le _) (fun x hx => (heMem x).mp hx)
      · refine Finset.sup_le fun e he => ?_
        have hmem := (heMem e).mpr he
        have hge : ∀ (L : List ℕ) (acc : ℕ), e ∈ L → e ≤ L.foldl max acc := by
          intro L acc hx
          induction L generalizing acc with
          | nil => cases hx
          | cons hd tl ih =>
            rcases List.mem_cons.mp hx with rfl | hx
            · have hacc : ∀ (M : List ℕ) (b : ℕ), b ≤ M.foldl max b := by
                intro M b
                induction M generalizing b with
                | nil => simp
                | cons y ys ihy => exact le_trans (le_max_left b y) (ihy (max b y))
              exact le_trans (le_max_right acc e) (hacc tl (max acc e))
            · exact ih (max acc hd) hx
        exact hge eList 0 hmem
    rw [hsup]; rfl

private lemma foldl_max_take_succ (L : List ℕ) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).foldl max 0 = max ((L.take i).foldl max 0) L[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Verified contract for `initMarkBridgesStmt`. -/
theorem initMarkBridges_meetsContract {w bSelf bUtils : ℕ} {G₀ : MGraph} {eList : List ℕ}
    {mult : ℕ → ℕ} {p : Program}
    (hpSelf : p.procs[bSelf]? = some (initMarkBridgesStmt bUtils))
    (hpFill : MeetsContract w p (bUtils + idxUtilMemFill) (memFillContract w)) :
    MeetsContract w p bSelf (initMarkBridgesContract w G₀ eList mult) := by
  refine meetsContract_of_runs hpSelf fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨eListPtr, multPtr, usedBridgePtr, m0, n0, eCap, rfl, h16, hEm, hVn,
    heCap, hLimW, hUBW, heLen, heNd, heMem, heAt, heLw_bd, heDisj, hmultMem, hmult_bd, hmultDisj⟩
  subst hEm hVn
  have hw1 : 1 < 2 ^ w := by omega
  have huBw : usedBridgePtr < 2 ^ w := hwords usedBridgePtr (by simp)
  have hm0w : G₀.E.card < 2 ^ w := hwords G₀.E.card (by simp)
  have hn0w : G₀.n < 2 ^ w := hwords G₀.n (by simp)
  have heCw : eCap < 2 ^ w := hwords eCap (by simp)
  let ubLen := 2 * G₀.E.card + G₀.n
  let lim := eCap + ubLen
  have hcopyMod_ge : 1 ≤ copyMod G₀ := by dsimp [copyMod]; omega
  have hcopyMod_w : copyMod G₀ < 2 ^ w := by
    by_cases hm0 : G₀.E.card = 0
    · have hE : G₀.E = ∅ := Finset.card_eq_zero.mp hm0
      dsimp only [copyMod]
      have hsup : G₀.E.sup id = 0 := by rw [hE, Finset.sup_empty]; rfl
      rw [hsup]
      simpa using hw1
    · have hne : G₀.E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hm0)
      have hePos : 0 < eCap := by
        obtain ⟨e₀, he₀⟩ := hne
        exact Nat.lt_of_le_of_lt (Nat.zero_le e₀) (heCap e₀ he₀)
      have hsup : G₀.E.sup id < eCap := (Finset.sup_lt_iff hePos).mpr heCap
      have hcm_le : copyMod G₀ ≤ eCap := Nat.succ_le_of_lt hsup
      exact Nat.lt_of_le_of_lt hcm_le heCw
  have hcopyMod_le_of_pos : 0 < G₀.E.card → copyMod G₀ ≤ eCap := by
    intro hmpos
    have hne : G₀.E.Nonempty := Finset.card_pos.mp hmpos
    have hePos : 0 < eCap := by
      obtain ⟨e₀, he₀⟩ := hne
      exact Nat.lt_of_le_of_lt (Nat.zero_le e₀) (heCap e₀ he₀)
    have hsup : G₀.E.sup id < eCap := (Finset.sup_lt_iff hePos).mpr heCap
    dsimp only [copyMod]; exact Nat.succ_le_of_lt hsup
  have hlim_w : lim < 2 ^ w := by dsimp [lim, ubLen] at *; omega
  have hstep1 : Triple w p
      (fun st => st = startState [eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap] mem pos)
      (.call 6 (bUtils + idxUtilMemFill)
        [.reg 2, .bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4), .const 0])
      (normalPost fun st =>
        st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
        st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
        (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
        (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
      (fun _ => 16 * ubLen + 25) := by
    intro st ω' hst
    subst hst
    have hpreF : (memFillContract w).pre [usedBridgePtr, ubLen, 0] mem :=
      ⟨usedBridgePtr, ubLen, 0, rfl, hUBW⟩
    have h2m_w : 2 * G₀.E.card < 2 ^ w := by dsimp [ubLen] at *; omega
    have hubLen_w : ubLen < 2 ^ w := by dsimp [ubLen] at *; omega
    have hevalF : evalArgs w (startState [eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap] mem pos)
        [.reg 2, .bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4), .const 0] =
        some [usedBridgePtr, ubLen, 0] :=
      evalArgs_cons (by eval_expr)
        (evalArgs_cons (by
          have h2m' : 2 * (startState [eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap] mem pos).regs 3 < 2 ^ w := h2m_w
          have hub' : 2 * (startState [eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap] mem pos).regs 3 +
              (startState [eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap] mem pos).regs 4 < 2 ^ w := hubLen_w
          eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    rcases runs_call_of_meetsContract (r := 6) hpFill hevalF
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> first | exact huBw | exact hubLen_w | omega)
        hpreF ω' with ⟨st1, c1, _, hruns1, hpost1, _, hregs1, hcost1⟩
    rcases hpost1 with ⟨dst1, len1, val1, hargs1, _, hfill1, hfr1⟩
    simp only [List.cons.injEq, and_true] at hargs1
    rcases hargs1 with ⟨hdst1, hlen1, hval1⟩
    have hu_eq : ∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st1.mem addr = mem addr :=
      fun addr ha => hfr1 addr (by rw [← hdst1, ← hlen1]; exact ha)
    refine ⟨.normal, st1, c1, hruns1, ⟨by rw [hregs1 0 (by omega)]; rfl,
      by rw [hregs1 1 (by omega)]; rfl, by rw [hregs1 2 (by omega)]; rfl,
      by rw [hregs1 3 (by omega)]; rfl, by rw [hregs1 4 (by omega)]; rfl,
      by rw [hregs1 5 (by omega)]; rfl, fun z hz => ?_, hu_eq⟩, ?_⟩
    · have hz' := hfill1 z (by rw [← hlen1]; exact hz)
      rw [← hdst1, ← hval1] at hz'; exact hz'
    dsimp only [memFillContract, argsSize, Expr.size, List.getD] at hcost1 ⊢
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hcost1
    omega
  let InvMax : ℕ → State → Prop := fun i st =>
    st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
    st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
    st.regs 6 = (eList.take i).foldl max 0 ∧ st.regs 7 = i ∧
    (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
    (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr)
  have hmax_init : ∀ st,
      (st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
        st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
        st.regs 6 = 0 ∧
        (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
        (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr)) →
      Expr.eval w st (.const 0) = some 0 ∧
        InvMax 0 { mem := st.mem, regs := Function.update st.regs 7 0, pos := st.pos } := by
    intro st ⟨h0, h1, h2, h3, h4, h5, h6, hz, hfr⟩
    exact ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      by simp [h5], by simp [h6], by simp, hz, hfr⟩
  have hfold_le : ∀ i ≤ G₀.E.card, (eList.take i).foldl max 0 ≤ eCap := by
    intro i _
    have hsub : ∀ (L : List ℕ) (acc : ℕ), acc ≤ eCap → (∀ x ∈ L, x < eCap) → L.foldl max acc ≤ eCap := by
      intro L acc ha hL
      induction L generalizing acc with
      | nil => exact ha
      | cons hd tl ih => exact ih _ (max_le ha (le_of_lt (hL hd (by simp)))) (fun x hx => hL x (by simp [hx]))
    exact hsub _ 0 (Nat.zero_le _) fun x hx =>
      heCap _ ((heMem _).mp (List.mem_of_mem_take hx))
  have hmax_body : ∀ i, 0 ≤ i → i < G₀.E.card →
      Triple w p (InvMax i)
        (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
         .cond (.bin .lt (.reg 6) (.reg 8)) (.assign 6 (.reg 8)) .nop)
        (normalPost fun st₁ =>
          InvMax (i + 1) { mem := st₁.mem, regs := Function.update st₁.regs 7 (i + 1), pos := st₁.pos } ∧
          st₁.regs 7 = i) (fun _ => 20) := by
    intro i _ hi st ω' hinv
    rcases hinv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hz, hfr⟩
    have hi_len : i < eList.length := by omega
    have hei_bd : eListPtr + i < 2 ^ w := by rcases heDisj with hle | hge <;> omega
    have hmem_ei : st.mem (eListPtr + i) = eList[i] := by
      rw [hfr (eListPtr + i) (by rcases heDisj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact heAt i hi_len
    have hei_lt : eList[i] < eCap := heCap _ ((heMem _).mp (List.getElem_mem hi_len))
    have hfold_lt : (eList.take i).foldl max 0 < 2 ^ w := by
      have hfl := hfold_le i (by omega)
      omega
    refine runs_start_le ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    let stA : State := { mem := st.mem, regs := Function.update st.regs 8 (st.mem (eListPtr + i)), pos := st.pos }
    have h8A : stA.regs 8 = eList[i] := by simp [stA, hmem_ei]
    have h6A : stA.regs 6 = (eList.take i).foldl max 0 := by simp [stA, h6]
    have htake_eq : (eList.take (i + 1)).foldl max 0 = max ((eList.take i).foldl max 0) eList[i] :=
      foldl_max_take_succ eList hi_len
    by_cases hlt : (eList.take i).foldl max 0 < eList[i]
    · have hcond : (Expr.bin .lt (.reg 6) (.reg 8)).eval w stA = some 1 := by
        simp only [Expr.eval, BinOp.eval, h6A, h8A, hlt, hw1, ↓reduceIte]
      have hmaxEq : eList[i] = (eList.take (i + 1)).foldl max 0 := by
        rw [htake_eq]; exact (max_eq_right hlt.le).symm
      have hasg : ∃ o st' c₁, Runs w p ω' (.assign 6 (.reg 8)) stA o st' c₁ ∧
          (normalPost fun st₁ =>
            InvMax (i + 1) { mem := st₁.mem, regs := Function.update st₁.regs 7 (i + 1), pos := st₁.pos } ∧
            st₁.regs 7 = i) o st' ∧ (6 + (Expr.bin .lt (.reg 6) (.reg 8)).size + c₁ + 1 ≤ 20) := by
        refine ⟨.normal, { mem := stA.mem, regs := Function.update stA.regs 6 (stA.regs 8), pos := stA.pos }, 2,
          runs_assign_iff.mpr ⟨stA.regs 8, by eval_expr, rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp [stA, h0], by simp [stA, h1], by simp [stA, h2], by simp [stA, h3],
          by simp [stA, h4], by simp [stA, h5], ?_, by simp, hz, hfr⟩, by simp [stA, h7]⟩
        simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7), Function.update_self, h8A, hmaxEq]
      rcases hasg with ⟨o, st', c₁, hr1, hq1, hc1⟩
      exact ⟨o, st', (Expr.bin .lt (.reg 6) (.reg 8)).size + c₁ + 1,
        runs_cond_iff.mpr ⟨1, c₁, hcond, hr1, rfl⟩, hq1, by dsimp [Expr.size] at hc1 ⊢; omega⟩
    · have hcond : (Expr.bin .lt (.reg 6) (.reg 8)).eval w stA = some 0 := by
        simp [Expr.eval, BinOp.eval, h6A, h8A, hlt]
      have hmaxEq : (eList.take i).foldl max 0 = (eList.take (i + 1)).foldl max 0 := by
        rw [htake_eq]; exact (max_eq_left (Nat.not_lt.mp hlt)).symm
      obtain ⟨o, st', c₁, hr1, hq1, hc1⟩ := runs_nop_le (w := w) (p := p) (ω := ω') (st := stA)
        (k := 6 + (Expr.bin .lt (.reg 6) (.reg 8)).size + 1) (T := 20)
        (Q := normalPost fun st₁ =>
          InvMax (i + 1) { mem := st₁.mem, regs := Function.update st₁.regs 7 (i + 1), pos := st₁.pos } ∧
          st₁.regs 7 = i)
        ⟨⟨by simp [stA, h0], by simp [stA, h1], by simp [stA, h2], by simp [stA, h3],
          by simp [stA, h4], by simp [stA, h5], by simp [stA, h6, hmaxEq], by simp, hz, hfr⟩,
          by simp [stA, h7]⟩
        (by simp [Expr.size])
      exact ⟨o, st', (Expr.bin .lt (.reg 6) (.reg 8)).size + c₁ + 1,
        runs_cond_iff.mpr ⟨0, c₁, hcond, hr1, rfl⟩, hq1, by dsimp [Expr.size] at hc1 ⊢; omega⟩
  have hmax_loop : Triple w p
      (fun st => st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
        st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
        (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
        (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
      ((.assign 6 (.const 0) ;;
        forRange 7 (.const 0) (.reg 3)
          (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
           .cond (.bin .lt (.reg 6) (.reg 8)) (.assign 6 (.reg 8)) .nop)) ;;
       (.cond (.bin .eq (.reg 3) (.const 0)) (.assign 6 (.const 1)) (.assign 6 (.bin .add (.reg 6) (.const 1))) ;;
        .assign 7 (.bin .add (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4)))))
      (normalPost fun st =>
        st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
        st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
        st.regs 6 = copyMod G₀ ∧ st.regs 7 = lim ∧
        (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
        (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
      (fun _ => 29 * G₀.E.card + 45) := by
    have hassign6 : Triple w p
        (fun st => st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
          st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
          (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
          (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
        (.assign 6 (.const 0))
        (normalPost fun st =>
          st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
          st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
          st.regs 6 = 0 ∧
          (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
          (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
        (fun _ => 2) := by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, hz, hfr⟩
      refine ⟨.normal, { mem := st.mem, regs := Function.update st.regs 6 0, pos := st.pos }, 2,
        runs_assign_iff.mpr ⟨0, by eval_expr, rfl, rfl, by simp [Expr.size]⟩, ?_, le_rfl⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
        by simp [h5], by simp, hz, hfr⟩
    have hfor7 := Triple.forRange_const 20 0 G₀.E.card (Nat.zero_le G₀.E.card) hw1
      (fun _ => hm0w) hmax_init
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h := hi.2.2.2.1; eval_expr)
      hmax_body
    have hcm : Triple w p (InvMax G₀.E.card)
        (.cond (.bin .eq (.reg 3) (.const 0)) (.assign 6 (.const 1)) (.assign 6 (.bin .add (.reg 6) (.const 1))) ;;
         .assign 7 (.bin .add (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4))))
        (normalPost fun st =>
          st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
          st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
          st.regs 6 = copyMod G₀ ∧ st.regs 7 = lim ∧
          (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
          (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr))
        (fun _ => 25) := by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, _, hz, hfr⟩
      have hfold_take : (eList.take G₀.E.card).foldl max 0 = eList.foldl max 0 := by
        rw [List.take_of_length_le heLen.le]
      rw [hfold_take] at h6
      have hfold_cm := copyMod_eq_foldl heMem
      refine runs_start_le ?_
      have h2mw : 2 * G₀.E.card < 2 ^ w := by dsimp [ubLen] at *; omega
      have heval_lim : ∀ r6Val,
          Expr.eval w { mem := st.mem, regs := Function.update st.regs 6 r6Val, pos := st.pos }
            (.bin .add (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.reg 4))) = some lim := by
        intro r6Val
        let st6 : State := { mem := st.mem, regs := Function.update st.regs 6 r6Val, pos := st.pos }
        have h3' : st6.regs 3 = G₀.E.card := by simp [st6, h3]
        have h4' : st6.regs 4 = G₀.n := by simp [st6, h4]
        have h5' : st6.regs 5 = eCap := by simp [st6, h5]
        have he5 : Expr.eval w st6 (.reg 5) = some eCap := by simp [Expr.eval, h5']
        have he2 : Expr.eval w st6 (.const 2) = some 2 := by
          have hm2 : 2 < 2 ^ w := by omega
          simp [Expr.eval, hm2]
        have he3 : Expr.eval w st6 (.reg 3) = some G₀.E.card := by simp [Expr.eval, h3']
        have he4 : Expr.eval w st6 (.reg 4) = some G₀.n := by simp [Expr.eval, h4']
        have hub_sum : 2 * G₀.E.card + G₀.n < 2 ^ w := by dsimp [lim, ubLen] at hlim_w; omega
        rw [show lim = eCap + (2 * G₀.E.card + G₀.n) by rfl]
        exact Expr.eval_add he5 (Expr.eval_add (Expr.eval_mul he2 he3 h2mw) he4 hub_sum) hlim_w
      by_cases hm0 : G₀.E.card = 0
      · have hcond : (Expr.bin .eq (.reg 3) (.const 0)).eval w st = some 1 := by
          simp [Expr.eval, BinOp.eval, h3, hm0, hw1]
        have hcm1 : 1 = copyMod G₀ := by rw [← hfold_cm, ite_eq_left (by omega)]
        refine runs_seq_cond_le hcond (fun _ => ?_) (fun hne => by omega)
        refine runs_seq_assign_le (by eval_expr) ?_
        refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨lim, heval_lim 1, rfl, rfl, rfl⟩, ?_, by simp [Expr.size]⟩
        exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
          by simp [hcm1], by simp, hz, hfr⟩
      · have hcond : (Expr.bin .eq (.reg 3) (.const 0)).eval w st = some 0 := by
          simp [Expr.eval, BinOp.eval, h3, hm0]
        have hcm1 : eList.foldl max 0 + 1 = copyMod G₀ := by rw [← hfold_cm, ite_eq_right (by omega)]
        have h6w : st.regs 6 + 1 < 2 ^ w := by rw [h6, hcm1]; exact hcopyMod_w
        refine runs_seq_cond_le hcond (fun hne => by omega) (fun _ => ?_)
        refine runs_seq_assign_le (by eval_expr) ?_
        refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨lim, heval_lim (st.regs 6 + 1), rfl, rfl, rfl⟩, ?_, by simp [Expr.size]⟩
        exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
          by simp [hcm1], by simp, hz, hfr⟩
    have h12 := hassign6.seq_normal
      (T := fun _ => 29 * G₀.E.card + 12)
      hfor7 (fun _ _ _ _ => by dsimp only [Expr.size]; omega)
    exact (h12.seq_normal (T := fun _ => 29 * G₀.E.card + 40)
      hcm (fun _ _ _ _ => by omega)).mono_cost
      (fun _ _ => by omega)
  let InvMark : ℕ → State → Prop := fun j st =>
    st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
    st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
    st.regs 6 = copyMod G₀ ∧ st.regs 7 = lim ∧ st.regs 8 = j ∧
    (∀ z < ubLen,
      (st.mem (usedBridgePtr + z) = 1 ↔
        ∃ j' < j, ∃ k < mult j', eList.getD j' 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (st.mem (usedBridgePtr + z) = 0 ∨ st.mem (usedBridgePtr + z) = 1)) ∧
    (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr)
  have hmark_init : ∀ st,
      (st.regs 0 = eListPtr ∧ st.regs 1 = multPtr ∧ st.regs 2 = usedBridgePtr ∧
        st.regs 3 = G₀.E.card ∧ st.regs 4 = G₀.n ∧ st.regs 5 = eCap ∧
        st.regs 6 = copyMod G₀ ∧ st.regs 7 = lim ∧
        (∀ z < ubLen, st.mem (usedBridgePtr + z) = 0) ∧
        (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → st.mem addr = mem addr)) →
      Expr.eval w st (.const 0) = some 0 ∧
        InvMark 0 { mem := st.mem, regs := Function.update st.regs 8 0, pos := st.pos } := by
    intro st ⟨h0, h1, h2, h3, h4, h5, h6, h7, hz, hfr⟩
    refine ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      by simp [h5], by simp [h6], by simp [h7], by simp, fun z hzu => ?_, hfr⟩
    have hzz := hz z hzu
    dsimp only
    exact ⟨⟨fun h1' => by omega, fun ⟨j', hj', _⟩ => by omega⟩, Or.inl hzz⟩
  let outerStepCost : ℕ → ℕ := fun j => 40 + 35 * mult j
  have hmark_body : ∀ j, 0 ≤ j → j < G₀.E.card →
      Triple w p (InvMark j)
        (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
         .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
         .assign 11 (.bin .add (.reg 9) (.reg 6)) ;;
         forRange 12 (.const 0) (.reg 10)
           (.cond (.bin .lt (.reg 11) (.reg 7))
             (.cond (.bin .lt (.reg 11) (.reg 5)) .nop
               (.store (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) (.const 1)) ;;
              .assign 11 (.bin .add (.reg 11) (.reg 6)))
             .nop))
        (normalPost fun st₁ =>
          InvMark (j + 1) { mem := st₁.mem, regs := Function.update st₁.regs 8 (j + 1), pos := st₁.pos } ∧
          st₁.regs 8 = j)
        (fun _ => outerStepCost j) := by
    intro j _ hj st ω' hinv
    rcases hinv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmark, hfr⟩
    have hcopyMod_le : copyMod G₀ ≤ eCap := hcopyMod_le_of_pos (by omega)
    have hj_len : j < eList.length := by omega
    have hej_bd : eListPtr + j < 2 ^ w := by rcases heDisj with hle | hge <;> omega
    have hmj_bd : multPtr + j < 2 ^ w := by rcases hmultDisj with hle | hge <;> omega
    have hmem_ej : st.mem (eListPtr + j) = eList[j] := by
      rw [hfr (eListPtr + j) (by rcases heDisj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact heAt j hj_len
    have hmem_mj : st.mem (multPtr + j) = mult j := by
      rw [hfr (multPtr + j) (by rcases hmultDisj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact (hmultMem j hj).1
    let ej := eList[j]
    have hej_getD : eList.getD j 0 = ej := List.getD_eq_getElem _ _ hj_len
    have hej_lt : ej < eCap := heCap _ ((heMem _).mp (List.getElem_mem hj_len))
    have hcur0_lt : ej + copyMod G₀ < lim + copyMod G₀ := by dsimp [lim, ubLen]; omega
    have hcur0_w : ej + copyMod G₀ < 2 ^ w := by omega
    have hmj_w : mult j < 2 ^ w := (hmultMem j hj).2
    let InvK : ℕ → State → Prop := fun k stK =>
      stK.regs 0 = eListPtr ∧ stK.regs 1 = multPtr ∧ stK.regs 2 = usedBridgePtr ∧
      stK.regs 3 = G₀.E.card ∧ stK.regs 4 = G₀.n ∧ stK.regs 5 = eCap ∧
      stK.regs 6 = copyMod G₀ ∧ stK.regs 7 = lim ∧ stK.regs 8 = j ∧
      stK.regs 9 = ej ∧ stK.regs 10 = mult j ∧ stK.regs 12 = k ∧
      stK.regs 11 < lim + copyMod G₀ ∧
      ((stK.regs 11 < lim ∧ stK.regs 11 = ej + copyMod G₀ * (k + 1)) ∨
        (lim ≤ stK.regs 11 ∧ lim ≤ ej + copyMod G₀ * (k + 1))) ∧
      (∀ z < ubLen,
        (stK.mem (usedBridgePtr + z) = 1 ↔
          (∃ j' < j, ∃ k' < mult j', eList.getD j' 0 + copyMod G₀ * (k' + 1) = eCap + z) ∨
          (∃ k' < k, ej + copyMod G₀ * (k' + 1) = eCap + z)) ∧
        (stK.mem (usedBridgePtr + z) = 0 ∨ stK.mem (usedBridgePtr + z) = 1)) ∧
      (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → stK.mem addr = mem addr)
    have hk_init : ∀ stK,
        (stK.regs 0 = eListPtr ∧ stK.regs 1 = multPtr ∧ stK.regs 2 = usedBridgePtr ∧
          stK.regs 3 = G₀.E.card ∧ stK.regs 4 = G₀.n ∧ stK.regs 5 = eCap ∧
          stK.regs 6 = copyMod G₀ ∧ stK.regs 7 = lim ∧ stK.regs 8 = j ∧
          stK.regs 9 = ej ∧ stK.regs 10 = mult j ∧
          stK.regs 11 = ej + copyMod G₀ ∧
          (∀ z < ubLen,
            (stK.mem (usedBridgePtr + z) = 1 ↔
              ∃ j' < j, ∃ k' < mult j', eList.getD j' 0 + copyMod G₀ * (k' + 1) = eCap + z) ∧
            (stK.mem (usedBridgePtr + z) = 0 ∨ stK.mem (usedBridgePtr + z) = 1)) ∧
          (∀ addr, addr < usedBridgePtr ∨ usedBridgePtr + ubLen ≤ addr → stK.mem addr = mem addr)) →
        Expr.eval w stK (.const 0) = some 0 ∧
          InvK 0 { mem := stK.mem, regs := Function.update stK.regs 12 0, pos := stK.pos } := by
      intro stK ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, hmK, hfrK⟩
      refine ⟨by eval_expr, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
        by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9], by simp [r10],
        by simp, ?_, ?_, fun z hzu => ?_, hfrK⟩
      · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), r11]
        exact hcur0_lt
      · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), r11]
        by_cases hltL : ej + copyMod G₀ < lim
        · exact Or.inl ⟨hltL, by ring⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · have hzz := hmK z hzu
        exact ⟨⟨fun h1' => Or.inl (hzz.1.mp h1'), fun h => by
          rcases h with hprev | ⟨k', hk', _⟩
          · exact hzz.1.mpr hprev
          · omega⟩, hzz.2⟩
    have hk_body : ∀ k, 0 ≤ k → k < mult j →
        Triple w p (InvK k)
          (.cond (.bin .lt (.reg 11) (.reg 7))
            (.cond (.bin .lt (.reg 11) (.reg 5)) .nop
              (.store (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) (.const 1)) ;;
             .assign 11 (.bin .add (.reg 11) (.reg 6)))
            .nop)
          (normalPost fun st₁ =>
            InvK (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 12 (k + 1), pos := st₁.pos } ∧
            st₁.regs 12 = k)
          (fun _ => 25) := by
      intro k _ hk stK ω'' hinvK
      rcases hinvK with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r12, hr11_bd, hr11_case, hmK, hfrK⟩
      have h11w : stK.regs 11 < 2 ^ w := by omega
      by_cases hltLim : stK.regs 11 < lim
      · have hr11_eq : stK.regs 11 = ej + copyMod G₀ * (k + 1) := by
          rcases hr11_case with ⟨_, hEq⟩ | ⟨hge, _⟩
          · exact hEq
          · omega
        have hcond1 : (Expr.bin .lt (.reg 11) (.reg 7)).eval w stK = some 1 := by
          simp [Expr.eval, BinOp.eval, r7, hltLim, hw1]
        have hnxt_bd : stK.regs 11 + copyMod G₀ < lim + copyMod G₀ := by omega
        have hnxt_w : stK.regs 11 + copyMod G₀ < 2 ^ w := by omega
        by_cases hltCap : stK.regs 11 < eCap
        · have hcond2 : (Expr.bin .lt (.reg 11) (.reg 5)).eval w stK = some 1 := by
            simp [Expr.eval, BinOp.eval, r5, hltCap, hw1]
          have hinner1 : ∃ o st' c₁,
              Runs w p ω''
                (.cond (.bin .lt (.reg 11) (.reg 5)) .nop
                   (.store (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) (.const 1)) ;;
                 .assign 11 (.bin .add (.reg 11) (.reg 6)))
                stK o st' c₁ ∧
              (normalPost fun st₁ =>
                InvK (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 12 (k + 1), pos := st₁.pos } ∧
                st₁.regs 12 = k) o st' ∧
              4 + c₁ ≤ 25 := by
            refine runs_seq_cond_le hcond2 (fun _ => ?_) (fun h0' => by omega)
            · refine runs_seq_nop_le ?_
              refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨stK.regs 11 + copyMod G₀,
                by rw [← r6]; exact Expr.eval_add (by eval_expr) (by eval_expr) (by rw [r6]; exact hnxt_w),
                rfl, rfl, rfl⟩, ⟨⟨by simp [r0], by simp [r1],
                by simp [r2], by simp [r3], by simp [r4], by simp [r5], by simp [r6], by simp [r7],
                by simp [r8], by simp [r9], by simp [r10], by simp, ?_, ?_, fun z hzu => ?_, hfrK⟩,
                by simp [r12]⟩, by simp [Expr.size]⟩
              · simp [hnxt_bd]
              · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), Function.update_self]
                have hstep_eq : stK.regs 11 + copyMod G₀ = ej + copyMod G₀ * (k + 1 + 1) := by
                  rw [hr11_eq]; ring
                by_cases h2 : stK.regs 11 + copyMod G₀ < lim
                · exact Or.inl ⟨h2, hstep_eq⟩
                · exact Or.inr ⟨by omega, by omega⟩
              · have hzz := hmK z hzu
                refine ⟨⟨fun h1' => ?_, fun h => ?_⟩, hzz.2⟩
                · rcases hzz.1.mp h1' with hprev | ⟨k', hk', hkeq⟩
                  · exact Or.inl hprev
                  · exact Or.inr ⟨k', by omega, hkeq⟩
                · rcases h with hprev | ⟨k', hk', hkeq⟩
                  · exact hzz.1.mpr (Or.inl hprev)
                  · by_cases hk_eq : k' = k
                    · subst k'; omega
                    · exact hzz.1.mpr (Or.inr ⟨k', by omega, hkeq⟩)
          rcases hinner1 with ⟨o, st', c₁, hr1, hq1, hc1⟩
          exact ⟨o, st', (Expr.bin .lt (.reg 11) (.reg 7)).size + c₁ + 1,
            runs_cond_iff.mpr ⟨1, c₁, hcond1, hr1, rfl⟩, hq1, by dsimp [Expr.size] at hc1 ⊢; omega⟩
        · have hcond2 : (Expr.bin .lt (.reg 11) (.reg 5)).eval w stK = some 0 := by
            simp [Expr.eval, BinOp.eval, r5, hltCap]
          let z₀ := stK.regs 11 - eCap
          have hz₀_lt : z₀ < ubLen := by dsimp [z₀, lim] at *; omega
          have had_lt : usedBridgePtr + z₀ < 2 ^ w := by omega
          have hinner1 : ∃ o st' c₁,
              Runs w p ω''
                (.cond (.bin .lt (.reg 11) (.reg 5)) .nop
                   (.store (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) (.const 1)) ;;
                 .assign 11 (.bin .add (.reg 11) (.reg 6)))
                stK o st' c₁ ∧
              (normalPost fun st₁ =>
                InvK (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 12 (k + 1), pos := st₁.pos } ∧
                st₁.regs 12 = k) o st' ∧
              4 + c₁ ≤ 25 := by
            refine runs_seq_cond_le hcond2 (fun h1' => by omega) (fun _ => ?_)
            have hstore_addr : Expr.eval w stK (.bin .add (.reg 2) (.bin .sub (.reg 11) (.reg 5))) =
                some (usedBridgePtr + z₀) := by
              rw [show usedBridgePtr + z₀ = stK.regs 2 + (stK.regs 11 - stK.regs 5) by simp [r2, r5, z₀]]
              exact Expr.eval_add (by eval_expr) (Expr.eval_sub (by eval_expr) (by eval_expr) h11w)
                (by simp [r2, r5]; exact had_lt)
            refine runs_seq_store_le hstore_addr (by eval_expr) ?_
            refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨stK.regs 11 + copyMod G₀,
              by rw [← r6]; exact Expr.eval_add (by eval_expr) (by eval_expr) (by rw [r6]; exact hnxt_w),
              rfl, rfl, rfl⟩, ⟨⟨by simp [r0], by simp [r1],
              by simp [r2], by simp [r3], by simp [r4], by simp [r5], by simp [r6], by simp [r7],
              by simp [r8], by simp [r9], by simp [r10], by simp, ?_, ?_, fun z hzu => ?_, fun addr ha => ?_⟩,
              by simp [r12]⟩, by simp [Expr.size]⟩
            · simp [hnxt_bd]
            · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), Function.update_self]
              have hstep_eq : stK.regs 11 + copyMod G₀ = ej + copyMod G₀ * (k + 1 + 1) := by
                rw [hr11_eq]; ring
              by_cases h2 : stK.regs 11 + copyMod G₀ < lim
              · exact Or.inl ⟨h2, hstep_eq⟩
              · exact Or.inr ⟨by omega, by omega⟩
            · change (Function.update stK.mem (usedBridgePtr + z₀) 1 (usedBridgePtr + z) = 1 ↔ _) ∧
                (Function.update stK.mem (usedBridgePtr + z₀) 1 (usedBridgePtr + z) = 0 ∨
                  Function.update stK.mem (usedBridgePtr + z₀) 1 (usedBridgePtr + z) = 1)
              by_cases hz0 : z = z₀
              · subst z
                have heq_z₀ : ej + copyMod G₀ * (k + 1) = eCap + z₀ := by
                  dsimp [z₀]; rw [← hr11_eq]; omega
                simp only [Function.update_self, true_iff, or_true, and_true]
                exact Or.inr ⟨k, Nat.lt_succ_self k, heq_z₀⟩
              · have hne : usedBridgePtr + z ≠ usedBridgePtr + z₀ := by omega
                rw [Function.update_of_ne hne]
                have hzz := hmK z hzu
                refine ⟨⟨fun h1' => ?_, fun h => ?_⟩, hzz.2⟩
                · rcases hzz.1.mp h1' with hprev | ⟨k', hk', hkeq⟩
                  · exact Or.inl hprev
                  · exact Or.inr ⟨k', by omega, hkeq⟩
                · rcases h with hprev | ⟨k', hk', hkeq⟩
                  · exact hzz.1.mpr (Or.inl hprev)
                  · by_cases hk_eq : k' = k
                    · subst k'
                      dsimp only [z₀] at hz0
                      exact False.elim (hz0 (Nat.eq_sub_of_add_eq (by rw [Nat.add_comm, ← hkeq, hr11_eq])))
                    · exact hzz.1.mpr (Or.inr ⟨k', by omega, hkeq⟩)
            · dsimp only
              have hne_addr : addr ≠ usedBridgePtr + z₀ := by
                dsimp only [z₀] at hz₀_lt ⊢
                rcases ha with h | h <;> omega
              rw [Function.update_of_ne hne_addr]
              exact hfrK addr ha
          rcases hinner1 with ⟨o, st', c₁, hr1, hq1, hc1⟩
          exact ⟨o, st', (Expr.bin .lt (.reg 11) (.reg 7)).size + c₁ + 1,
            runs_cond_iff.mpr ⟨1, c₁, hcond1, hr1, rfl⟩, hq1, by dsimp [Expr.size] at hc1 ⊢; omega⟩
      · have hge_lim : lim ≤ ej + copyMod G₀ * (k + 1) := by
          rcases hr11_case with ⟨hlt, _⟩ | ⟨_, hge⟩
          · exact absurd hlt hltLim
          · exact hge
        have hcond1 : (Expr.bin .lt (.reg 11) (.reg 7)).eval w stK = some 0 := by
          simp [Expr.eval, BinOp.eval, r7, hltLim]
        have hinv_next :
            InvK (k + 1)
              { mem := stK.mem, regs := Function.update stK.regs 12 (k + 1), pos := stK.pos } ∧
            stK.regs 12 = k := by
          refine ⟨⟨by simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 12), r0],
            by simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 12), r1],
            by simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 12), r2],
            by simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 12), r3],
            by simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 12), r4],
            by simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 12), r5],
            by simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 12), r6],
            by simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 12), r7],
            by simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 12), r8],
            by simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 12), r9],
            by simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 12), r10],
            by simp only [Function.update_self],
            by simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), hr11_bd],
            ?_, fun z hzu => ?_, hfrK⟩, by exact r12⟩
          · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12)]
            refine Or.inr ⟨by omega, ?_⟩
            have hle : ej + copyMod G₀ * (k + 1) ≤ ej + copyMod G₀ * (k + 1 + 1) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) ej
            exact le_trans hge_lim hle
          · have hzz := hmK z hzu
            refine ⟨⟨fun h1' => ?_, fun h => ?_⟩, hzz.2⟩
            · rcases hzz.1.mp h1' with hprev | ⟨k', hk', hkeq⟩
              · exact Or.inl hprev
              · exact Or.inr ⟨k', by omega, hkeq⟩
            · rcases h with hprev | ⟨k', hk', hkeq⟩
              · exact hzz.1.mpr (Or.inl hprev)
              · by_cases hk_eq : k' = k
                · subst k'; dsimp [lim] at hge_lim; omega
                · exact hzz.1.mpr (Or.inr ⟨k', by omega, hkeq⟩)
        obtain ⟨o, st', c₁, hr1, hq1, hc1⟩ := runs_nop_le (w := w) (p := p) (ω := ω'') (st := stK)
          (k := (Expr.bin .lt (.reg 11) (.reg 7)).size + 1) (T := 25)
          (Q := normalPost fun st₁ =>
            InvK (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 12 (k + 1), pos := st₁.pos } ∧
            st₁.regs 12 = k)
          hinv_next
          (by simp [Expr.size])
        exact ⟨o, st', (Expr.bin .lt (.reg 11) (.reg 7)).size + c₁ + 1,
          runs_cond_iff.mpr ⟨0, c₁, hcond1, hr1, rfl⟩, hq1, by dsimp [Expr.size] at hc1 ⊢; omega⟩
    have hinner := Triple.forRange_const 25 0 (mult j) (Nat.zero_le (mult j)) hw1 (fun _ => hmj_w)
      hk_init (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ stK _ _ hi => by have h10 := hi.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
      hk_body
    refine runs_start_le ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    refine runs_triple_le hinner ?_ ?_ (by simp [Expr.size, outerStepCost]; omega)
    · refine ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
        by simp [h5], by simp [h6], by simp [h7], by simp [h8],
        by simp [hmem_ej, ej], by simp [hmem_mj], by simp [hmem_ej, ej], hmark, hfr⟩
    · intro o stD ho
      cases o with
      | returned u => exact False.elim ho
      | normal =>
        rcases ho with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, _, _, _, _, _, hmD, hfrD⟩
        refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
          by simp [r5], by simp [r6], by simp [r7], by simp, fun z hzu => ?_, hfrD⟩, r8⟩
        have hzz := hmD z hzu
        refine ⟨⟨fun h1' => ?_, fun h => ?_⟩, hzz.2⟩
        · rcases hzz.1.mp h1' with ⟨j', hj', k', hk', hkeq⟩ | ⟨k', hk', hkeq⟩
          · exact ⟨j', by omega, k', hk', hkeq⟩
          · exact ⟨j, by omega, k', hk', by rw [hej_getD]; exact hkeq⟩
        · rcases h with ⟨j', hj', k', hk', hkeq⟩
          by_cases hj_eq : j' = j
          · subst j'; rw [hej_getD] at hkeq; exact hzz.1.mpr (Or.inr ⟨k', hk', hkeq⟩)
          · exact hzz.1.mpr (Or.inl ⟨j', by omega, k', hk', hkeq⟩)
  have houter := Triple.forRange_le outerStepCost 0 G₀.E.card (Nat.zero_le G₀.E.card) hw1
    (fun _ => hm0w) hmark_init (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h := hi.2.2.2.1; eval_expr) hmark_body
  refine runs_start_le ?_
  dsimp only [initMarkBridgesStmt]
  refine runs_seq_triple_le hstep1 rfl fun st1 h1 => ?_
  refine runs_seq_triple_le hmax_loop h1 fun st2 h2 => ?_
  refine runs_seq_triple_le houter h2 fun stF hinvF => ?_
  rcases hinvF with ⟨_, _, _, _, _, _, _, _, _, hmarkF, hfrF⟩
  have hrange_sum : rangeCost outerStepCost 0 G₀.E.card =
      40 * G₀.E.card + 35 * (List.map mult (List.range G₀.E.card)).sum := by
    dsimp only [outerStepCost]
    rw [rangeCost_add, rangeCost_const, Nat.sub_zero, Nat.mul_comm G₀.E.card 40]
    have hsmul : ∀ n, rangeCost (fun j => 35 * mult j) 0 n =
        35 * (List.map mult (List.range n)).sum := by
      intro n
      induction n with
      | zero => simp [rangeCost]
      | succ k ih =>
        rw [rangeCost_zero_eq_range] at ih ⊢
        simp only [List.range_succ, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
        omega
    rw [hsmul]
  have hmem_sum : (List.map (fun j => mem (multPtr + j)) (List.range G₀.E.card)).sum =
      (List.map mult (List.range G₀.E.card)).sum := by
    congr 1; apply List.map_congr_left
    intro j hj; exact (hmultMem j (List.mem_range.mp hj)).1
  refine runs_ret_le (by eval_expr)
    ⟨eListPtr, multPtr, usedBridgePtr, G₀.E.card, G₀.n, eCap, rfl, rfl, hmarkF, hfrF⟩ ?_
  dsimp only [initMarkBridgesContract, Expr.size, ubLen, List.getD]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [hrange_sum, hmem_sum]
  omega
