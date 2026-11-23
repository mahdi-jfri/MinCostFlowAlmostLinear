module

public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.DynSpanner.Program.DynGraphInsert
public import MinCostFlow.DynSpanner.Program.DynGraphDelete
import Mathlib.Tactic.Linarith

/-!
# Stretch-One Writer and `T`-Block Insert Procedure (`BatchTBlockOpsBase`)

Defines `lsfSetWstrOneProc`, `lsfTBlockInsertProc`, `lsfTBlockDeleteProc` and their contracts,
and proves `lsfSetWstrOne_meetsContract`, `wstrAt_after_setOne`, and
`lsfTBlockInsert_meetsContract`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Reassociate `(.seq (.seq s₁ s₂) s₃)` to `(.seq s₁ (.seq s₂ s₃))` with at most `+ 1` step. -/
lemma runs_seq_assoc_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ : Stmt} {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω (.seq s₁ (.seq s₂ s₃)) st o st' c ∧ Q o st' ∧ (k + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.seq s₁ s₂) s₃) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  rcases runs_seq_iff.mp hr with ⟨u, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂₃, hr₁, hr₂₃, rfl⟩
  · refine ⟨.returned u, st', (c₁ + 1) + 1,
      runs_seq_iff.mpr (Or.inl ⟨u, c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨u, c₁, hr₁, rfl, rfl⟩), rfl, rfl⟩),
      hq, by omega⟩
  · rcases runs_seq_iff.mp hr₂₃ with ⟨u, c₂, hr₂, rfl, rfl⟩ | ⟨st₂, c₂, c₃, hr₂, hr₃, rfl⟩
    · refine ⟨.returned u, st', (c₁ + c₂ + 1) + 1,
        runs_seq_iff.mpr (Or.inl ⟨u, c₁ + c₂ + 1,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), rfl, rfl⟩),
        hq, by omega⟩
    · refine ⟨o, st', (c₁ + c₂ + 1) + c₃ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₂, c₁ + c₂ + 1, c₃,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hr₃, rfl⟩),
        hq, by omega⟩

/-! ## Procedure definitions -/

/-- Set `wstrNum[e]` and `wstrDen[e]` (`L_w` limbs each) to `1` (`[wstrNumPtr, wstrDenPtr, e, L_w]`). -/
def lsfSetWstrOneProc : Stmt :=
  .assign 4 (.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 3))) ;;
  .assign 5 (.bin .add (.reg 1) (.bin .mul (.reg 2) (.reg 3))) ;;
  .store (.reg 4) (.const 1) ;;
  .store (.reg 5) (.const 1) ;;
  .assign 6 (.const 1) ;;
  .loop (.bin .lt (.reg 6) (.reg 3))
    (.store (.bin .add (.reg 4) (.reg 6)) (.const 0) ;;
     .store (.bin .add (.reg 5) (.reg 6)) (.const 0) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1))) ;;
  .ret (.const 0)

lemma lsfSetWstrOneProc_noRand : lsfSetWstrOneProc.NoRand := by
  dsimp [lsfSetWstrOneProc]; trivial

/-- Update `TBlockAt` on edge insertion `(e, u, v)` (`[tPtr, vCap, eCap, tM, e, u, v]`). -/
def lsfTBlockInsertProc (idxDgIns : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const tOffIdxOfEdgePtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const tOffDgTPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const tOffFrozenTailPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const tOffFrozenHeadPtr))) ;;
  .cond (.bin .lt (.reg 4) (.reg 2))
    (.assign 11 (.load (.bin .add (.reg 7) (.reg 4))) ;;
     .cond (.reg 11)
       (.assign 12 (.bin .sub (.reg 11) (.const 1)) ;;
        .cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 12))) (.reg 5))
          (.call 13 idxDgIns [.reg 8, .bin .mul (.const 2) (.reg 12), .reg 5, .reg 5])
          .nop ;;
        .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 12))) (.reg 6))
          (.call 13 idxDgIns
            [.reg 8, .bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1), .reg 6, .reg 6])
          .nop)
       .nop)
    .nop ;;
  .ret (.const 0)

lemma lsfTBlockInsertProc_noRand (idxDgIns : ℕ) : (lsfTBlockInsertProc idxDgIns).NoRand := by
  dsimp [lsfTBlockInsertProc]; trivial

/-- Update `TBlockAt` on edge deletion `(e, u, v)` (`[tPtr, vCap, eCap, tM, e, u, v]`), where
`u = G.tail e` and `v = G.head e` before deleting `e` from `G`. -/
def lsfTBlockDeleteProc (idxDgDel : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const tOffIdxOfEdgePtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const tOffDgTPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const tOffFrozenTailPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const tOffFrozenHeadPtr))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 8) (.const 4)) (.bin .mul (.const 7) (.reg 1))) ;;
  .cond (.bin .lt (.reg 4) (.reg 2))
    (.assign 12 (.load (.bin .add (.reg 7) (.reg 4))) ;;
     .cond (.reg 12)
       (.assign 13 (.bin .sub (.reg 12) (.const 1)) ;;
        .cond (.load (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 13))))
          (.store (.bin .add (.reg 9) (.reg 13)) (.reg 5) ;;
           .call 14 idxDgDel [.reg 8, .bin .mul (.const 2) (.reg 13)])
          .nop ;;
        .cond (.load (.bin .add (.reg 11) (.bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1))))
          (.store (.bin .add (.reg 10) (.reg 13)) (.reg 6) ;;
           .call 14 idxDgDel
             [.reg 8, .bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1)])
          .nop)
       .nop)
    .nop ;;
  .ret (.const 0)

lemma lsfTBlockDeleteProc_noRand (idxDgDel : ℕ) : (lsfTBlockDeleteProc idxDgDel).NoRand := by
  dsimp [lsfTBlockDeleteProc]; trivial

/-! ## Contracts -/

/-- Contract for `lsfSetWstrOneProc` (`[wstrNumPtr, wstrDenPtr, e, L_w]`). -/
def lsfSetWstrOneContract (w h : ℕ) : Contract where
  pre args _ := ∃ wstrNumPtr wstrDenPtr e L_w,
    args = [wstrNumPtr, wstrDenPtr, e, L_w] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ h ∧ 1 ≤ L_w ∧ 2 ≤ h * L_w ∧
    wstrNumPtr + (e + 1) * L_w < 2 ^ w ∧
    wstrDenPtr + (e + 1) * L_w < 2 ^ w ∧
    (wstrNumPtr + (e + 1) * L_w ≤ wstrDenPtr + e * L_w ∨
      wstrDenPtr + (e + 1) * L_w ≤ wstrNumPtr + e * L_w)
  post args mem ret mem' := ∃ wstrNumPtr wstrDenPtr e L_w,
    args = [wstrNumPtr, wstrDenPtr, e, L_w] ∧ ret = 0 ∧
    Num.Valid mem' (wstrNumPtr + e * L_w) h L_w ∧
    Num.Valid mem' (wstrDenPtr + e * L_w) h L_w ∧
    Num.intVal mem' (wstrNumPtr + e * L_w) h L_w = 1 ∧
    Num.intVal mem' (wstrDenPtr + e * L_w) h L_w = 1 ∧
    ∀ a, ¬ (wstrNumPtr + e * L_w ≤ a ∧ a < wstrNumPtr + (e + 1) * L_w) →
         ¬ (wstrDenPtr + e * L_w ≤ a ∧ a < wstrDenPtr + (e + 1) * L_w) →
         mem' a = mem a
  cost args _ := 50 * (args.getD 3 0) + 50

/-- Contract for `lsfTBlockInsertProc` (`[tPtr, vCap, eCap, tM, e, u, v]`). -/
def lsfTBlockInsertContract (w vCap eCap tM : ℕ) (G T_cur T₀ : MGraph)
    (π : ℕ → ℕ) (tOrigList : List ℕ) : Contract where
  pre args mem := ∃ tPtr e u v,
    args = [tPtr, vCap, eCap, tM, e, u, v] ∧
    16 ≤ 2 ^ w ∧ tPtr + tBlockSize vCap eCap tM < 2 ^ w ∧
    G.UpdateIsValid (.insert e u v) ∧ e < eCap ∧
    T_cur.IsValid ∧ T_cur.V = G.V ∧ T_cur.E = T₀.E ∧
    TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList
  post args mem ret mem' := ∃ tPtr e u v,
    args = [tPtr, vCap, eCap, tM, e, u, v] ∧ ret = 0 ∧
    TBlockAt mem' tPtr vCap eCap tM (G.applyUpdate (.insert e u v)) T_cur T₀ π tOrigList ∧
    ∀ a, a < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ a → mem' a = mem a
  cost _ _ := 1100

/-- Contract for `lsfTBlockDeleteProc` (`[tPtr, vCap, eCap, tM, e, u, v]`). -/
def lsfTBlockDeleteContract (w vCap eCap tM : ℕ) (G T_cur T₀ : MGraph)
    (π : ℕ → ℕ) (tOrigList : List ℕ) : Contract where
  pre args mem := ∃ tPtr e u v,
    args = [tPtr, vCap, eCap, tM, e, u, v] ∧
    16 ≤ 2 ^ w ∧ tPtr + tBlockSize vCap eCap tM < 2 ^ w ∧
    G.IsValid ∧ e ∈ G.E ∧ u = G.tail e ∧ v = G.head e ∧ e < eCap ∧
    TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList
  post args mem ret mem' := ∃ tPtr e u v,
    args = [tPtr, vCap, eCap, tM, e, u, v] ∧ ret = 0 ∧
    TBlockAt mem' tPtr vCap eCap tM (G.applyUpdate (.delete e)) T_cur T₀ π tOrigList ∧
    ∀ a, a < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ a → mem' a = mem a
  cost _ _ := 1100

/-! ## Verification of `lsfSetWstrOneProc` -/

private lemma num_intVal_one_of_limbs {mem : ℕ → ℕ} {a h L : ℕ}
    (hh : 1 ≤ h) (hL : 1 ≤ L) (hhL : 2 ≤ h * L)
    (h0 : mem a = 1) (hrest : ∀ i, 1 ≤ i → i < L → mem (a + i) = 0) :
    Num.Valid mem a h L ∧ Num.intVal mem a h L = 1 := by
  have hb2 : 2 ≤ Num.base h := by
    dsimp [Num.base]; exact Nat.pow_le_pow_right (by omega : 0 < 2) hh
  have hval : Num.Valid mem a h L := by
    intro i hi
    rcases i with _ | i
    · simpa [h0] using (by omega : 1 < Num.base h)
    · rw [hrest (i + 1) (by omega) hi]; omega
  have hu : Num.unsignedVal mem a h L = 1 := by
    cases L with
    | zero => omega
    | succ L' =>
      rw [Num.unsignedVal, h0]
      have hz : Num.unsignedVal mem (a + 1) h L' = 0 :=
        Num.unsignedVal_zero fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm 1] using hrest (j + 1) (by omega) (by omega)
      rw [hz, mul_zero, add_zero]
  have hcap4 : 4 ≤ Num.capacity h L := by
    dsimp [Num.capacity, Num.base]
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hhL
  refine ⟨hval, ?_⟩
  dsimp [Num.intVal, Num.signedVal]
  rw [hu]
  split_ifs with hc
  · omega
  · simp

private lemma setWstrOneLoop_runs {w numBase denBase L_w : ℕ} {p : Program} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hnum_lt : numBase + L_w < 2 ^ w) (hden_lt : denBase + L_w < 2 ^ w)
    (hdisj : numBase + L_w ≤ denBase ∨ denBase + L_w ≤ numBase) :
    ∀ (rem i : ℕ) (st : State),
      i + rem = L_w → 1 ≤ i →
      st.regs 3 = L_w → st.regs 4 = numBase → st.regs 5 = denBase → st.regs 6 = i →
      st.mem numBase = 1 → st.mem denBase = 1 →
      (∀ j, 1 ≤ j → j < i → st.mem (numBase + j) = 0 ∧ st.mem (denBase + j) = 0) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 6) (.reg 3))
            (.store (.bin .add (.reg 4) (.reg 6)) (.const 0) ;;
             .store (.bin .add (.reg 5) (.reg 6)) (.const 0) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1))))
          st .normal st' c ∧
        st'.mem numBase = 1 ∧ st'.mem denBase = 1 ∧
        (∀ j, 1 ≤ j → j < L_w → st'.mem (numBase + j) = 0 ∧ st'.mem (denBase + j) = 0) ∧
        (∀ a, ¬ (numBase ≤ a ∧ a < numBase + L_w) →
              ¬ (denBase ≤ a ∧ a < denBase + L_w) → st'.mem a = st.mem a) ∧
        c ≤ 30 * rem + 10 := by
  intro rem
  induction rem with
  | zero =>
    intro i st hsum hi hr3 hr4 hr5 hr6 hn0 hd0 hprev
    have hiL : i = L_w := by omega
    have hL_lt : L_w < 2 ^ w := by omega
    have hi_ltw : i < 2 ^ w := by omega
    have hcond : (Expr.bin .lt (.reg 6) (.reg 3)).eval w st = some 0 := by
      rw [show (0 : ℕ) = BinOp.lt.eval i L_w by dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]; omega)
    refine ⟨st, 4, ?_, hn0, hd0, fun j hj1 hj2 => hprev j hj1 (by omega), fun _ _ _ => rfl, by omega⟩
    rw [runs_loop_iff]
    exact Or.inl ⟨hcond, rfl, rfl, by decide⟩
  | succ rem ih =>
    intro i st hsum hi hr3 hr4 hr5 hr6 hn0 hd0 hprev
    have hi_lt : i < L_w := by omega
    have hL_lt : L_w < 2 ^ w := by omega
    have hi_ltw : i < 2 ^ w := by omega
    have hnb_ltw : numBase < 2 ^ w := by omega
    have hdb_ltw : denBase < 2 ^ w := by omega
    have hcond : (Expr.bin .lt (.reg 6) (.reg 3)).eval w st = some 1 := by
      rw [show (1 : ℕ) = BinOp.lt.eval i L_w by dsimp [BinOp.eval]; rw [ite_eq_left hi_lt]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_left hi_lt]; omega)
    let mem1 := Function.update (Function.update st.mem (numBase + i) 0) (denBase + i) 0
    let st1 : State := { mem := mem1, regs := Function.update st.regs 6 (i + 1), pos := st.pos }
    have hbody : ∃ c_b,
        Runs w p ω
          (.store (.bin .add (.reg 4) (.reg 6)) (.const 0) ;;
           .store (.bin .add (.reg 5) (.reg 6)) (.const 0) ;;
           .assign 6 (.bin .add (.reg 6) (.const 1)))
          st .normal st1 c_b ∧ c_b ≤ 24 := by
      suffices h : ∃ o st' c,
          Runs w p ω
            (.store (.bin .add (.reg 4) (.reg 6)) (.const 0) ;;
             .store (.bin .add (.reg 5) (.reg 6)) (.const 0) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1)))
            st o st' c ∧ (o = .normal ∧ st' = st1) ∧ 0 + c ≤ 24 by
        rcases h with ⟨_, _, c, hr, ⟨rfl, rfl⟩, hc⟩; exact ⟨c, hr, by omega⟩
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_assign_le (v := i + 1) (by eval_expr) ⟨rfl, rfl⟩ ?_
      dsimp only [Expr.size]; omega
    rcases hbody with ⟨c_b, hrun_b, hcb⟩
    have hn0_1 : st1.mem numBase = 1 := by
      dsimp only [st1, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hn0]
    have hd0_1 : st1.mem denBase = 1 := by
      dsimp only [st1, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hd0]
    have hprev_1 : ∀ j, 1 ≤ j → j < i + 1 → st1.mem (numBase + j) = 0 ∧ st1.mem (denBase + j) = 0 := by
      intro j hj1 hj2
      dsimp only [st1, mem1]
      by_cases hji : j = i
      · subst hji
        refine ⟨?_, Function.update_self _ _ _⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
      · have hlt : j < i := by omega
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hprev j hj1 hlt).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hprev j hj1 hlt).2
    obtain ⟨st', c_r, hrun_r, hn0', hd0', hprev', hfr', hcr⟩ :=
      ih (i + 1) st1 (by omega) (by omega)
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr3])
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr4])
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr5])
        (by dsimp [st1]; rw [Function.update_self])
        hn0_1 hd0_1 hprev_1
    refine ⟨st', 3 + c_b + c_r + 1, ?_, hn0', hd0', hprev', fun a ha1 ha2 => ?_, by omega⟩
    · rw [runs_loop_iff]
      exact Or.inr (Or.inr ⟨1, st1, c_b, c_r, hcond, by decide, hrun_b, hrun_r, rfl⟩)
    · refine (hfr' a ha1 ha2).trans ?_
      dsimp only [st1, mem1]
      rw [Function.update_of_ne (fun h => ha2 ⟨by omega, by omega⟩),
        Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩)]

/-- `lsfSetWstrOneProc` meets `lsfSetWstrOneContract w h`. -/
theorem lsfSetWstrOne_meetsContract {w h idx : ℕ} {p : Program}
    (hp : p.procs[idx]? = some lsfSetWstrOneProc) :
    MeetsContract w p idx (lsfSetWstrOneContract w h) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨wstrNumPtr, wstrDenPtr, e, L_w, rfl, hw16, hh, hL, hhL, hnum_lt, hden_lt, hdisj⟩
  have heL_le : e * L_w + L_w = (e + 1) * L_w := by ring
  have hnb_lt : wstrNumPtr + e * L_w + L_w < 2 ^ w := by omega
  have hdb_lt : wstrDenPtr + e * L_w + L_w < 2 ^ w := by omega
  have hst0 : (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos).regs 0 = wstrNumPtr ∧
      (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos).regs 1 = wstrDenPtr ∧
      (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos).regs 2 = e ∧
      (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos).regs 3 = L_w := by
    simp [startState]
  rcases hst0 with ⟨hr0, hr1, hr2, hr3⟩
  have he_ltw : e < 2 ^ w := by nlinarith
  have hL_ltw : L_w < 2 ^ w := by nlinarith
  have h0_ltw : wstrNumPtr < 2 ^ w := by omega
  have h1_ltw : wstrDenPtr < 2 ^ w := by omega
  have hnb0_ltw : wstrNumPtr + e * L_w < 2 ^ w := by omega
  have hdb0_ltw : wstrDenPtr + e * L_w < 2 ^ w := by omega
  have heL_ltw : e * L_w < 2 ^ w := by omega
  have hgoal : ∃ o st' c,
      Runs w p ω lsfSetWstrOneProc (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (lsfSetWstrOneContract w h).post [wstrNumPtr, wstrDenPtr, e, L_w] mem 0 st'.mem) ∧
      0 + c ≤ 50 * L_w + 50 := by
    dsimp only [lsfSetWstrOneProc]
    refine runs_seq_assign_le (v := wstrNumPtr + e * L_w) (by eval_expr) ?_
    refine runs_seq_assign_le (v := wstrDenPtr + e * L_w) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
    let st1 : State :=
      { mem := Function.update (Function.update mem (wstrNumPtr + e * L_w) 1) (wstrDenPtr + e * L_w) 1
        regs := Function.update (Function.update (Function.update
          (startState [wstrNumPtr, wstrDenPtr, e, L_w] mem pos).regs
          4 (wstrNumPtr + e * L_w)) 5 (wstrDenPtr + e * L_w)) 6 1
        pos := pos }
    have hnb_eq : st1.mem (wstrNumPtr + e * L_w) = 1 := by
      dsimp only [st1]
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hdb_eq : st1.mem (wstrDenPtr + e * L_w) = 1 := by
      dsimp only [st1]; exact Function.update_self _ _ _
    obtain ⟨st2, c_loop, hrun_l, hn0', hd0', hrest', hfr_l, hc_l⟩ :=
      setWstrOneLoop_runs (p := p) (ω := ω) hw16 hnb_lt hdb_lt (by omega)
        (L_w - 1) 1 st1 (by omega) le_rfl
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr3])
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
        (by dsimp [st1]; rw [Function.update_of_ne (by decide), Function.update_self])
        (by dsimp [st1]; rw [Function.update_self])
        hnb_eq hdb_eq (fun j hj1 hj2 => by omega)
    have hrun_ret : Runs w p ω (.ret (.const 0)) st2 (.returned 0) st2 ((Expr.const 0).size + 1) :=
      runs_ret_iff.mpr ⟨0, by eval_expr, rfl, rfl, rfl⟩
    refine ⟨.returned 0, st2, c_loop + ((Expr.const 0).size + 1) + 1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c_loop, (Expr.const 0).size + 1, hrun_l, hrun_ret, rfl⟩),
      ⟨rfl, ?_⟩, ?_⟩
    · have ⟨hVN, hIN⟩ := num_intVal_one_of_limbs hh hL hhL hn0' (fun j hj1 hj2 => (hrest' j hj1 hj2).1)
      have ⟨hVD, hID⟩ := num_intVal_one_of_limbs hh hL hhL hd0' (fun j hj1 hj2 => (hrest' j hj1 hj2).2)
      refine ⟨wstrNumPtr, wstrDenPtr, e, L_w, rfl, rfl, hVN, hVD, hIN, hID, fun a ha1 ha2 => ?_⟩
      refine (hfr_l a (by omega) (by omega)).trans ?_
      dsimp only [st1]
      rw [Function.update_of_ne (fun h => ha2 ⟨by omega, by omega⟩),
        Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩)]
    · dsimp only [Expr.size]; omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hc⟩ := hgoal
  exact ⟨lsfSetWstrOneProc, hp, .returned 0, st', c, hrun, hpost, by simpa [lsfSetWstrOneContract] using hc⟩

/-- Updating `wstrNum[e] = wstrDen[e] = 1` preserves `WstrAt` across edge insertion `(e, u, v)`. -/
lemma wstrAt_after_setOne {mem mem' : ℕ → ℕ} {wstrNumPtr wstrDenPtr eCap h L_w e u v : ℕ}
    {G : MGraph} {wstr : ℕ → ℝ}
    (hw : WstrAt mem wstrNumPtr wstrDenPtr eCap h L_w G wstr)
    (he_lt : e < eCap)
    (hVN : Num.Valid mem' (wstrNumPtr + e * L_w) h L_w)
    (hVD : Num.Valid mem' (wstrDenPtr + e * L_w) h L_w)
    (hIN : Num.intVal mem' (wstrNumPtr + e * L_w) h L_w = 1)
    (hID : Num.intVal mem' (wstrDenPtr + e * L_w) h L_w = 1)
    (hdisj : wstrNumPtr + eCap * L_w ≤ wstrDenPtr ∨ wstrDenPtr + eCap * L_w ≤ wstrNumPtr)
    (hfr : ∀ a, ¬ (wstrNumPtr + e * L_w ≤ a ∧ a < wstrNumPtr + (e + 1) * L_w) →
                ¬ (wstrDenPtr + e * L_w ≤ a ∧ a < wstrDenPtr + (e + 1) * L_w) →
                mem' a = mem a) :
    WstrAt mem' wstrNumPtr wstrDenPtr eCap h L_w
      (G.applyUpdate (.insert e u v)) (Function.update wstr e 1) := by
  rcases hw with ⟨hhL, hL, hE⟩
  refine ⟨hhL, hL, fun f hf => ?_⟩
  change f ∈ insert e G.E at hf
  rw [Finset.mem_insert] at hf
  by_cases hfe : f = e
  · subst hfe
    rw [Function.update_self, hIN, hID]
    exact ⟨he_lt, hVN, hVD, le_rfl, le_rfl, by norm_num⟩
  · have hfG : f ∈ G.E := hf.resolve_left hfe
    rw [Function.update_of_ne hfe]
    rcases hE f hfG with ⟨hf_lt, hVNf, hVDf, hINf, hIDf, hvalf⟩
    have hne_mul : ∀ i < L_w,
        ¬ (e * L_w ≤ f * L_w + i ∧ f * L_w + i < (e + 1) * L_w) := by
      intro i hi ⟨h1, h2⟩
      by_cases hlt : f < e
      · have : (f + 1) * L_w ≤ e * L_w := Nat.mul_le_mul_right L_w hlt
        nlinarith
      · have : (e + 1) * L_w ≤ f * L_w := Nat.mul_le_mul_right L_w (by omega)
        omega
    have heN : ∀ i < L_w, mem' (wstrNumPtr + f * L_w + i) = mem (wstrNumPtr + f * L_w + i) := by
      intro i hi
      refine hfr _ (fun ⟨h1, h2⟩ => hne_mul i hi ⟨by omega, by omega⟩) (fun ⟨h1, h2⟩ => ?_)
      have hf1 : (f + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w hf_lt
      have he1 : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w he_lt
      rcases hdisj with hd | hd <;> nlinarith
    have heD : ∀ i < L_w, mem' (wstrDenPtr + f * L_w + i) = mem (wstrDenPtr + f * L_w + i) := by
      intro i hi
      refine hfr _ (fun ⟨h1, h2⟩ => ?_) (fun ⟨h1, h2⟩ => hne_mul i hi ⟨by omega, by omega⟩)
      have hf1 : (f + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w hf_lt
      have he1 : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w he_lt
      rcases hdisj with hd | hd <;> nlinarith
    have hVNf' : Num.Valid mem' (wstrNumPtr + f * L_w) h L_w := fun i hi => by
      rw [heN i hi]; exact hVNf i hi
    have hVDf' : Num.Valid mem' (wstrDenPtr + f * L_w) h L_w := fun i hi => by
      rw [heD i hi]; exact hVDf i hi
    rw [Num.intVal_congr heN, Num.intVal_congr heD]
    exact ⟨hf_lt, hVNf', hVDf', hINf, hIDf, hvalf⟩

/-! ## Verification of `lsfTBlockInsertProc` -/

private lemma tBlock_insert_step_notMem {mem : ℕ → ℕ} {tPtr vCap eCap tM e u v : ℕ}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hT : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (he_lt : e < eCap) (hzero : mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0) :
    TBlockAt mem tPtr vCap eCap tM (G.applyUpdate (.insert e u v)) T_cur T₀ π tOrigList := by
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, fun i hi => ?_⟩
  have hne : tOrigList[i] ≠ e := by
    intro hEq
    have h1' := hidx1 i hi (hEq ▸ he_lt)
    rw [hEq, hzero] at h1'; omega
  have htr := htrack i hi
  simp only [MGraph.applyUpdate, Finset.mem_insert, hne, false_or, Function.update_of_ne hne]
  exact htr

private lemma tBlock_insert_post {mem mem' : ℕ → ℕ} {tPtr vCap eCap tM i e u v : ℕ}
    {G T_cur T₀ dgT : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hT : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (hdgT_eq : DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT ∧
      dgT.V = G.V ∧ (∀ k ∈ dgT.E, k < 2 * tM) ∧
      ∀ j (hj : j < tOrigList.length),
        let f := tOrigList[j]
        (2 * j ∈ dgT.E ↔ f ∈ G.E ∧ G.tail f = T_cur.tail f) ∧
        (2 * j ∈ dgT.E → dgT.tail (2 * j) = T_cur.tail f ∧ dgT.head (2 * j) = T_cur.tail f) ∧
        (2 * j ∉ dgT.E → mem (tFrozenTailBase tPtr vCap tM + j) = T_cur.tail f) ∧
        (2 * j + 1 ∈ dgT.E ↔ f ∈ G.E ∧ G.head f = T_cur.head f) ∧
        (2 * j + 1 ∈ dgT.E →
          dgT.tail (2 * j + 1) = T_cur.head f ∧ dgT.head (2 * j + 1) = T_cur.head f) ∧
        (2 * j + 1 ∉ dgT.E → mem (tFrozenHeadBase tPtr vCap tM + j) = T_cur.head f))
    (hi_len : i < tOrigList.length) (hi_eq : tOrigList[i] = e) (he_notG : e ∉ G.E)
    (hfr : ∀ a, a < tDgTPtr tPtr ∨ tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ a → mem' a = mem a)
    (dgT2 : MGraph)
    (hdgT2_def : dgT2 =
      (let dgT1 := if T_cur.tail e = u then dgT.applyUpdate (.insert (2 * i) u u) else dgT
       if T_cur.head e = v then dgT1.applyUpdate (.insert (2 * i + 1) v v) else dgT1))
    (hdgT2_at : DynGraphAt mem' (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2) :
    TBlockAt mem' tPtr vCap eCap tM (G.applyUpdate (.insert e u v)) T_cur T₀ π tOrigList := by
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2, _⟩
  rcases hdgT_eq with ⟨_, hdgTV, hdgTE, htrack⟩
  have hhd : ∀ off < tHdrSize, mem' (tPtr + off) = mem (tPtr + off) := fun off hoff =>
    hfr _ (Or.inl (by dsimp [tDgTPtr]; omega))
  have hafter : ∀ a, tOrigIdBase tPtr vCap tM ≤ a → mem' a = mem a := fun a ha =>
    hfr _ (Or.inr (by dsimp [tOrigIdBase] at ha; omega))
  have hft_eq : ∀ j < tM, mem' (tFrozenTailBase tPtr vCap tM + j) = mem (tFrozenTailBase tPtr vCap tM + j) :=
    fun j _ => hafter _ (by dsimp [tFrozenTailBase, tPiBase]; omega)
  have hfh_eq : ∀ j < tM, mem' (tFrozenHeadBase tPtr vCap tM + j) = mem (tFrozenHeadBase tPtr vCap tM + j) :=
    fun j _ => hafter _ (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)
  have hidx_eq : ∀ a, tIdxOfEdgeBase tPtr vCap tM ≤ a → mem' a = mem a := fun a ha =>
    hafter _ (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase] at ha; omega)
  have hdgT2_V : dgT2.V = (G.applyUpdate (.insert e u v)).V := by
    rw [hdgT2_def]; split_ifs <;> simp [MGraph.applyUpdate, hdgTV]
  have hdgT2_E : ∀ k ∈ dgT2.E, k < 2 * tM := by
    intro k hk; rw [hdgT2_def] at hk
    by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v <;>
      simp only [ht, hh, ↓reduceIte, MGraph.applyUpdate, Finset.mem_insert] at hk
    · rcases hk with rfl | rfl | hk <;> [omega; omega; exact hdgTE k hk]
    · rcases hk with rfl | hk <;> [omega; exact hdgTE k hk]
    · rcases hk with rfl | hk <;> [omega; exact hdgTE k hk]
    · exact hdgTE k hk
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
    (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
    (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7,
    hlen, hnd, hmemT,
    fun j hj => (hafter _ (Nat.le_add_right _ _)).trans (hLO j hj),
    fun j hj => (hafter _ (by dsimp [tPiBase]; omega)).trans (hLPi j hj),
    fun j hj hlt => (hidx_eq _ (Nat.le_add_right _ _)).trans (hidx1 j hj hlt),
    fun f hf hne => by
      have hm := hidx_eq (tIdxOfEdgeBase tPtr vCap tM + f) (Nat.le_add_right _ _)
      rw [hm] at hne ⊢; exact hidx2 f hf hne,
    dgT2, hdgT2_at, hdgT2_V, hdgT2_E, fun j hj => ?_⟩
  have htrj := htrack j hj
  by_cases hji : j = i
  · subst hji
    rw [hi_eq] at htrj ⊢
    have h2i_not : 2 * j ∉ dgT.E := fun h => he_notG (htrj.1.mp h).1
    have h2i1_not : 2 * j + 1 ∉ dgT.E := fun h => he_notG (htrj.2.2.2.1.mp h).1
    have h2i_ne : 2 * j ≠ 2 * j + 1 := by omega
    rw [hdgT2_def]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v
      · simp [ht, hh, MGraph.applyUpdate, h2i_not]
      · simp [ht, hh, MGraph.applyUpdate, h2i_not]
      · have ht' : u ≠ T_cur.tail e := Ne.symm ht
        simp [ht, ht', hh, MGraph.applyUpdate, h2i_not]
      · have ht' : u ≠ T_cur.tail e := Ne.symm ht
        simp [ht, ht', hh, MGraph.applyUpdate, h2i_not]
    · intro hmem
      by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v <;>
        simp [ht, hh, MGraph.applyUpdate, h2i_not, Function.update_of_ne] at hmem ⊢
    · intro _
      rw [hft_eq j (by omega)]; exact htrj.2.2.1 h2i_not
    · by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v
      · simp [ht, hh, MGraph.applyUpdate, h2i1_not]
      · have hh' : v ≠ T_cur.head e := Ne.symm hh
        simp [ht, hh, hh', MGraph.applyUpdate, h2i1_not]
      · simp [ht, hh, MGraph.applyUpdate, h2i1_not]
      · have hh' : v ≠ T_cur.head e := Ne.symm hh
        simp [ht, hh, hh', MGraph.applyUpdate, h2i1_not]
    · intro hmem
      by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v <;>
        simp [ht, hh, MGraph.applyUpdate, h2i1_not] at hmem ⊢
    · intro _
      rw [hfh_eq j (by omega)]; exact htrj.2.2.2.2.2 h2i1_not
  · have hf_ne : tOrigList[j] ≠ e := fun h => hji (hnd.getElem_inj_iff.mp (h.trans hi_eq.symm))
    have h2j_ne1 : 2 * j ≠ 2 * i := by omega
    have h2j_ne2 : 2 * j ≠ 2 * i + 1 := by omega
    have h2j1_ne1 : 2 * j + 1 ≠ 2 * i := by omega
    have h2j1_ne2 : 2 * j + 1 ≠ 2 * i + 1 := by omega
    rw [hdgT2_def]
    by_cases ht : T_cur.tail e = u <;> by_cases hh : T_cur.head e = v <;>
      simp only [ht, hh, ↓reduceIte, MGraph.applyUpdate, Finset.mem_insert,
        hf_ne, h2j_ne1, h2j_ne2, h2j1_ne1, h2j1_ne2, false_or,
        Function.update_of_ne hf_ne, Function.update_of_ne h2j_ne1,
        Function.update_of_ne h2j_ne2, Function.update_of_ne h2j1_ne1,
        Function.update_of_ne h2j1_ne2,
        hft_eq j (by omega), hfh_eq j (by omega)] <;> exact htrj

/-- `lsfTBlockInsertProc` meets `lsfTBlockInsertContract`. -/
theorem lsfTBlockInsert_meetsContract {w idx idxDgIns vCap eCap tM : ℕ} {p : Program}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hp : p.procs[idx]? = some (lsfTBlockInsertProc idxDgIns))
    (hDgIns : ∀ H, MeetsContract w p idxDgIns (dgInsertEdgeContract w vCap (2 * tM + 1) H)) :
    MeetsContract w p idx (lsfTBlockInsertContract w vCap eCap tM G T_cur T₀ π tOrigList) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨tPtr, e, u, v, rfl, hw16, hbound, hval_ins, he_lt, hTval, hTV, hTE, hT⟩
  have hT_copy := hT
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  rcases hval_ins with ⟨he_notG, huG, hvG⟩
  have hdgT_lt : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) < 2 ^ w := by
    dsimp [tDgTPtr, tBlockSize] at hbound ⊢; omega
  have hdgT_sub : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tDgTPtr, tBlockSize]; omega
  have hidx_base_lt : tIdxOfEdgeBase tPtr vCap tM + eCap ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hft_base_lt : tFrozenTailBase tPtr vCap tM + tM ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hfh_base_lt : tFrozenHeadBase tPtr vCap tM + tM ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hu_dgT : u ∈ dgT.V := hdgTV.symm ▸ huG
  have hv_dgT : v ∈ dgT.V := hdgTV.symm ▸ hvG
  have hu_lt : u < vCap := hdgT.2.1 u hu_dgT
  have hv_lt : v < vCap := hdgT.2.1 v hv_dgT
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgT_lt; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [tBlockSize] at hbound; omega
  have htM_ltw : tM < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hbound; omega
  have h2tM1_ltw : 2 * tM + 1 < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hbound; omega
  have htPtr_ltw : tPtr + tHdrSize < 2 ^ w := by dsimp [tBlockSize] at hbound; omega
  have hst0 : (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 0 = tPtr ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 2 = eCap ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 4 = e ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 5 = u ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 6 = v := by
    simp [startState]
  rcases hst0 with ⟨hr0, hr2, hr4, hr5, hr6⟩
  have hgoal : ∃ o st' c,
      Runs w p ω (lsfTBlockInsertProc idxDgIns)
        (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (lsfTBlockInsertContract w vCap eCap tM G T_cur T₀ π tOrigList).post
          [tPtr, vCap, eCap, tM, e, u, v] mem 0 st'.mem) ∧
      0 + c ≤ 1100 := by
    dsimp only [lsfTBlockInsertProc]
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tIdxOfEdgeBase tPtr vCap tM)
      (by dsimp [tOffIdxOfEdgePtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h6) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tDgTPtr tPtr)
      (by dsimp [tOffDgTPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h1) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tFrozenTailBase tPtr vCap tM)
      (by dsimp [tOffFrozenTailPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h4) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tFrozenHeadBase tPtr vCap tM)
      (by dsimp [tOffFrozenHeadPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h5) ?_
    refine runs_seq_cond_le (v := 1) (by
      rw [show (1 : ℕ) = BinOp.lt.eval e eCap by dsimp [BinOp.eval]; simp [he_lt]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_left he_lt]; omega))
      ?_ (fun h0' => by omega)
    intro _
    refine runs_seq_assoc_le ?_
    have hidx0_ltw : tIdxOfEdgeBase tPtr vCap tM < 2 ^ w := by omega
    have hidx_e_ltw : tIdxOfEdgeBase tPtr vCap tM + e < 2 ^ w := by omega
    set idx1 := mem (tIdxOfEdgeBase tPtr vCap tM + e)
    by_cases hidx0 : idx1 = 0
    · refine runs_seq_assign_le (v := 0) ?_ ?_
      · exact Expr.eval_load_of_eq (by eval_expr) hidx0
      refine runs_seq_cond_le (v := 0) (by eval_expr) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_nop_le ?_
      refine runs_ret_le (v := 0) (by eval_expr)
        ⟨rfl, tPtr, e, u, v, rfl, rfl, tBlock_insert_step_notMem hT_copy he_lt hidx0,
          fun _ _ => rfl⟩ ?_
      dsimp only [Expr.size]; omega
    · obtain ⟨i, hi_len, hi_eq, hidx_eq⟩ := hidx2 e he_lt hidx0
      have hi_lt : i < tM := by omega
      have hidx1_ltw : i + 1 < 2 ^ w := by omega
      have heT0 : e ∈ T₀.E := hi_eq ▸ (hmemT _).mp (List.getElem_mem hi_len)
      have hTe_val := hTval e (hTE.symm ▸ heT0)
      have hft_ltw : T_cur.tail e < 2 ^ w := by
        have : T_cur.tail e < vCap := hdgT.2.1 _ (hdgTV.symm ▸ hTV ▸ hTe_val.1)
        omega
      have hfh_ltw : T_cur.head e < 2 ^ w := by
        have : T_cur.head e < vCap := hdgT.2.1 _ (hdgTV.symm ▸ hTV ▸ hTe_val.2)
        omega
      have htri := htrack i hi_len
      rw [hi_eq] at htri
      have h2i_not : 2 * i ∉ dgT.E := fun h => he_notG (htri.1.mp h).1
      have h2i1_not : 2 * i + 1 ∉ dgT.E := fun h => he_notG (htri.2.2.2.1.mp h).1
      have hft_i : mem (tFrozenTailBase tPtr vCap tM + i) = T_cur.tail e := htri.2.2.1 h2i_not
      have hfh_i : mem (tFrozenHeadBase tPtr vCap tM + i) = T_cur.head e := htri.2.2.2.2.2 h2i1_not
      refine runs_seq_assign_le (v := i + 1) ?_ ?_
      · exact Expr.eval_load_of_eq (by eval_expr) hidx_eq
      refine runs_seq_cond_le (v := i + 1) (by eval_expr) ?_ (fun h => by omega)
      intro _
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := i) (by
        rw [show some i = some (BinOp.sub.eval (i + 1) 1) from rfl]
        exact Expr.eval_bin (by eval_expr) (by eval_expr) (by dsimp [BinOp.eval]; omega)) ?_
      refine runs_seq_assoc_le ?_
      let dgT1 : MGraph := if T_cur.tail e = u then dgT.applyUpdate (.insert (2 * i) u u) else dgT
      let dgT2 : MGraph := if T_cur.head e = v then dgT1.applyUpdate (.insert (2 * i + 1) v v) else dgT1
      have hstep2 : ∀ (mem1 : ℕ → ℕ) (r13 : ℕ) (pos1 : ℕ) (k1 : ℕ),
          DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 →
          (∀ a, a < tDgTPtr tPtr ∨ tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ a → mem1 a = mem a) →
          k1 ≤ 550 →
          ∃ o st' c,
            Runs w p ω
              (.cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 12))) (.reg 6))
                (.call 13 idxDgIns
                  [.reg 8, .bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1), .reg 6, .reg 6])
                .nop ;; .ret (.const 0))
              { mem := mem1,
                regs := Function.update (Function.update (Function.update (Function.update
                  (Function.update (Function.update (Function.update
                    (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
                    7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
                    9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
                    11 (i + 1)) 12 i) 13 r13,
                pos := pos1 } o st' c ∧
            (o = .returned 0 ∧
              (lsfTBlockInsertContract w vCap eCap tM G T_cur T₀ π tOrigList).post
                [tPtr, vCap, eCap, tM, e, u, v] mem 0 st'.mem) ∧
            k1 + c ≤ 1100 := by
        intro mem1 r13 pos1 k1 hdgT1 hfr1 hk1
        have hfh_m1 : mem1 (tFrozenHeadBase tPtr vCap tM + i) = T_cur.head e :=
          (hfr1 _ (Or.inr (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega))).trans hfh_i
        refine runs_seq_cond_le (v := if T_cur.head e = v then 1 else 0) ?_ ?_ ?_
        · exact Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) hfh_m1) (by eval_expr)
            (by dsimp [BinOp.eval]; split_ifs <;> omega)
        · intro hne
          have hhh : T_cur.head e = v := by by_contra hc; simp [hc] at hne
          have hv_dgT1 : v ∈ dgT1.V := by dsimp [dgT1]; split_ifs <;> simpa [MGraph.applyUpdate] using hv_dgT
          have h2i1_not1 : 2 * i + 1 ∉ dgT1.E := by
            dsimp [dgT1]; split_ifs
            · simp only [MGraph.applyUpdate, Finset.mem_insert]
              intro hc
              rcases hc with h | h
              · omega
              · exact h2i1_not h
            · exact h2i1_not
          have hpre_i2 : (dgInsertEdgeContract w vCap (2 * tM + 1) dgT1).pre
              [tDgTPtr tPtr, 2 * i + 1, v, v] mem1 :=
            ⟨tDgTPtr tPtr, 2 * i + 1, v, v, rfl, hw16, hdgT_lt, hv_dgT1, hv_dgT1, hdgT1⟩
          refine runs_seq_call_le (hDgIns dgT1) (by eval_expr)
            (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl | rfl | rfl <;> omega)
            hpre_i2 ?_
          intro _ mem2 _ hpost2
          rcases hpost2 with ⟨_, _, _, _, hargs2, _, hdgT2_raw, hfr2⟩
          simp only [List.cons.injEq, and_true] at hargs2
          rcases hargs2 with ⟨rfl, rfl, rfl, rfl⟩
          have hdgT2_at : DynGraphAt mem2 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2 := by
            have hcond_e : 2 * i + 1 < 2 * tM + 1 ∧ 2 * i + 1 ∉ dgT1.E := ⟨by omega, h2i1_not1⟩
            rw [ite_eq_left hcond_e] at hdgT2_raw
            simpa only [dgT2, hhh, ↓reduceIte] using hdgT2_raw
          have hfr12 : ∀ a, a < tDgTPtr tPtr ∨ tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ a →
              mem2 a = mem a := fun a ha => (hfr2 a ha).trans (hfr1 a ha)
          refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, tPtr, e, u, v, rfl, rfl,
            tBlock_insert_post hT_copy ⟨hdgT, hdgTV, hdgTE, htrack⟩ hi_len hi_eq he_notG hfr12
              dgT2 rfl hdgT2_at,
            fun a ha => hfr12 a (by dsimp [tDgTPtr, tBlockSize] at ha ⊢; omega)⟩ ?_
          dsimp only [dgInsertEdgeContract, argsSize, Expr.size]; omega
        · intro heq0
          have hhh : T_cur.head e ≠ v := fun hc => by simp [hc] at heq0
          have hdgT2_at : DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2 := by
            simpa only [dgT2, hhh, ↓reduceIte] using hdgT1
          refine runs_seq_nop_le ?_
          refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, tPtr, e, u, v, rfl, rfl,
            tBlock_insert_post hT_copy ⟨hdgT, hdgTV, hdgTE, htrack⟩ hi_len hi_eq he_notG hfr1
              dgT2 rfl hdgT2_at,
            fun a ha => hfr1 a (by dsimp [tDgTPtr, tBlockSize] at ha ⊢; omega)⟩ ?_
          dsimp only [Expr.size]; omega
      refine runs_seq_cond_le (v := if T_cur.tail e = u then 1 else 0) ?_ ?_ ?_
      · exact Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) hft_i) (by eval_expr)
          (by dsimp [BinOp.eval]; split_ifs <;> omega)
      · intro hne
        have htt : T_cur.tail e = u := by by_contra hc; simp [hc] at hne
        have hpre_i1 : (dgInsertEdgeContract w vCap (2 * tM + 1) dgT).pre
            [tDgTPtr tPtr, 2 * i, u, u] mem :=
          ⟨tDgTPtr tPtr, 2 * i, u, u, rfl, hw16, hdgT_lt, hu_dgT, hu_dgT, hdgT⟩
        refine runs_seq_call_le (hDgIns dgT) (by eval_expr)
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl <;> omega)
          hpre_i1 ?_
        intro r13 mem1 pos1 hpost1
        rcases hpost1 with ⟨_, _, _, _, hargs1, _, hdgT1_raw, hfr1⟩
        simp only [List.cons.injEq, and_true] at hargs1
        rcases hargs1 with ⟨rfl, rfl, rfl, rfl⟩
        have hdgT1_at : DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 := by
          have hcond_e : 2 * i < 2 * tM + 1 ∧ 2 * i ∉ dgT.E := ⟨by omega, h2i_not⟩
          rw [ite_eq_left hcond_e] at hdgT1_raw
          simpa only [dgT1, htt, ↓reduceIte] using hdgT1_raw
        exact hstep2 mem1 r13 pos1 _ hdgT1_at hfr1
          (by dsimp only [dgInsertEdgeContract, argsSize, Expr.size]; omega)
      · intro heq0
        have htt : T_cur.tail e ≠ u := fun hc => by simp [hc] at heq0
        have hdgT1_at : DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 := by
          simpa only [dgT1, htt, ↓reduceIte] using hdgT
        refine runs_seq_nop_le ?_
        have hreg_eq : (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update
              (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
              7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
              9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
              11 (i + 1)) 12 i) =
            Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update
              (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
              7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
              9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
              11 (i + 1)) 12 i) 13
              ((startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 13) := by
          funext r; by_cases hr : r = 13
          · subst hr; simp
          · simp [Function.update_of_ne hr]
        rw [hreg_eq]
        exact hstep2 mem ((startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 13) pos _ hdgT1_at
          (fun _ _ => rfl) (by dsimp only [Expr.size]; omega)
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hc⟩ := hgoal
  exact ⟨lsfTBlockInsertProc idxDgIns, hp, .returned 0, st', c, hrun, hpost, by simpa [lsfTBlockInsertContract] using hc⟩

end

end MinCostFlow.LSF.Program
