module

public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.WireCoreLenK
public import MinCostFlow.Num.ShiftLeft
import WordRAM.Tactic

/-!
# Filling the core lengths of a level (`SelectCoreLenFill`)

The keys of level `j` read the core lengths `C.chainLen ℓ (j + 1)` on the edges of `G_j`
(`SelectCoreLenInv`), stored in the owned table `B.lenPtr j` (`SelPartLen`,
`SelectBlocksParts.lean`) at precision `P` for `j < d` and `P + pLast` for `j = d`. Each entry is
the previous length times the stretch `num / den` of the edge in the active forest of level `j`,
where the stretch table has `Lw` limbs (possibly distinct from `L` under
`sparseCoreOrdMachineContractKFBL`) and arbitrary positive denominators `den`.

This file uses `Num.shiftLeft` (to scale the previous length by `2 ^ shift`, with `shift = 0` on
levels `< d` and `shift = pLast` on level `d`) followed by `wireCoreLenEdgeBody` (`WireCoreLenK`)
at index `0` to compute exact `num / den · prev` for every edge of a list:
* `selCoreLenEdgeBody shiftLeft wireEdge` (`[prevBase, numBase, denBase, dst, e, L, Lw, shift, heap]`):
  computes entry `e` of `dst` at precision `P + shift` in `O((max L Lw)^2)` steps and scratch words.
* `selCoreLenFillBody edgeProc` (`[prevBase, numBase, denBase, dst, listPtr, len, L, Lw, shift, heap]`):
  runs `edgeProc` over the listed edges in `O(len · (max L Lw)^2)` steps and scratch words.
* `selCoreLenEdge_meetsContract` and `selCoreLenFill_meetsContract`: exact correctness, frame, and
  zero-tail proofs.
* `edgeValuesAt_of_coreLenFill` and `selCoreLenFill_setLen`: updates `B.lenPtr j` while preserving
  all other parts of the select blocks.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- Scratch space per listed edge of `selCoreLenEdgeBody`: `L` words for the shifted previous
length plus `wireCoreLenEdgeSpace (max L Lw)`. -/
def selCoreLenEdgeSpace (L Lw : ℕ) : ℕ :=
  L + wireCoreLenEdgeSpace (max L Lw)

/-- Step cost per listed edge of `selCoreLenEdgeBody`. -/
def selCoreLenEdgeCost (L Lw : ℕ) : ℕ :=
  35 * L + wireCoreLenEdgeCost (max L Lw) + 120

/-- Per-edge core-length update (`[prevBase, numBase, denBase, dst, e, L, Lw, shift, heap]`):
shifts `prevBase + e * L` left by `shift` bits into `heap`, then runs `wireEdge`
(`wireCoreLenEdgeBody`) at index `0` to write `(num / den) * prev` at precision `P + shift` into
`dst + e * L`. Returns `heap + selCoreLenEdgeSpace L Lw`. -/
def selCoreLenEdgeBody (shiftLeft wireEdge : ℕ) : Stmt :=
  .assign 9 (.bin .add (.reg 0) (.bin .mul (.reg 4) (.reg 5))) ;;
  .assign 10 (.bin .add (.reg 1) (.bin .mul (.reg 4) (.reg 6))) ;;
  .assign 11 (.bin .add (.reg 2) (.bin .mul (.reg 4) (.reg 6))) ;;
  .assign 12 (.bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5))) ;;
  .call 13 shiftLeft [.reg 9, .reg 5, .reg 7, .reg 8] ;;
  .call 14 wireEdge [.reg 10, .reg 11, .reg 8, .reg 12, .const 0, .reg 5, .reg 6, .reg 13] ;;
  .ret (.reg 14)

theorem selCoreLenEdgeBody_noRand (shiftLeft wireEdge : ℕ) :
    (selCoreLenEdgeBody shiftLeft wireEdge).NoRand := by
  simp [selCoreLenEdgeBody, Stmt.NoRand]

/-- Rewrite the core lengths of the listed edges
(`[prevBase, numBase, denBase, dst, listPtr, len, L, Lw, shift, heap]`). -/
def selCoreLenFillBody (edgeProc : ℕ) : Stmt :=
  forRange 10 (.const 0) (.reg 5)
    (.assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
     .call 9 edgeProc
       [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11, .reg 6, .reg 7, .reg 8, .reg 9]) ;;
  .ret (.reg 9)

theorem selCoreLenFillBody_noRand (edgeProc : ℕ) : (selCoreLenFillBody edgeProc).NoRand := by
  simp [selCoreLenFillBody, forRange, forUp, Stmt.NoRand]

/-- The new length of entry `e`: `(num / den) · prev`, read from `prevBase` (`L` limbs) and
`(numBase, denBase)` (`Lw` limbs) in `mem`. -/
noncomputable def selCoreLenVal (mem : ℕ → ℕ) (P prevBase numBase denBase L Lw e : ℕ) : ℝ :=
  Num.fixVal mem (numBase + e * Lw) 4 Lw P / Num.fixVal mem (denBase + e * Lw) 4 Lw P *
    Num.fixVal mem (prevBase + e * L) 4 L P

/-- What `selCoreLenEdgeBody` asks of entry `e`: valid limbs in `prevBase` (`L` limbs) and
`(numBase, denBase)` (`Lw` limbs), a positive denominator, the shifted previous value fits in `L`
limbs, and the target value `(num / den) * prev` is representable on the `2 ^ (-(P + shift))` grid
in `L` limbs. -/
def SelCoreLenEntryOk (P shift L Lw : ℕ) (mem : ℕ → ℕ)
    (prevBase numBase denBase e : ℕ) : Prop :=
  Num.Valid mem (prevBase + e * L) 4 L ∧
  Num.Valid mem (numBase + e * Lw) 4 Lw ∧
  Num.Valid mem (denBase + e * Lw) 4 Lw ∧
  0 < Num.fixVal mem (denBase + e * Lw) 4 Lw P ∧
  Num.Fits 4 L (Num.intVal mem (prevBase + e * L) 4 L * (2 : ℤ) ^ shift) ∧
  ∃ q : ℤ, Num.Fits 4 L q ∧
    (q : ℝ) / (2 : ℝ) ^ (P + shift) = selCoreLenVal mem P prevBase numBase denBase L Lw e

/-- Contract of `selCoreLenEdgeBody` for one edge `e`. -/
def selCoreLenEdgeContract (w P : ℕ) : Contract where
  pre args mem :=
    ∃ prevBase numBase denBase dst e L Lw shift heap,
      args = [prevBase, numBase, denBase, dst, e, L, Lw, shift, heap] ∧
      16 < 2 ^ w ∧
      prevBase + e * L + L ≤ heap ∧
      numBase + e * Lw + Lw ≤ heap ∧
      denBase + e * Lw + Lw ≤ heap ∧
      dst + e * L + L ≤ heap ∧
      SelCoreLenEntryOk P shift L Lw mem prevBase numBase denBase e ∧
      ZeroFrom mem heap ∧
      heap + selCoreLenEdgeSpace L Lw < 2 ^ w
  post args mem ret mem' :=
    let prevBase := args.getD 0 0
    let numBase := args.getD 1 0
    let denBase := args.getD 2 0
    let dst := args.getD 3 0
    let e := args.getD 4 0
    let L := args.getD 5 0
    let Lw := args.getD 6 0
    let shift := args.getD 7 0
    let heap := args.getD 8 0
    ret = heap + selCoreLenEdgeSpace L Lw ∧
    Num.Valid mem' (dst + e * L) 4 L ∧
    Num.fixVal mem' (dst + e * L) 4 L (P + shift) =
      selCoreLenVal mem P prevBase numBase denBase L Lw e ∧
    ZeroFrom mem' ret ∧
    ∀ a < heap, (a < dst + e * L ∨ dst + e * L + L ≤ a) → mem' a = mem a
  cost args _ := selCoreLenEdgeCost (args.getD 5 0) (args.getD 6 0)

/-- Contract of `selCoreLenFillBody` for the list `L_list` of edges below `eCap`. -/
def selCoreLenFillContract (w P eCap : ℕ) (L_list : List ℕ) : Contract where
  pre args mem :=
    ∃ prevBase numBase denBase dst listPtr L Lw shift heap,
      args = [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap] ∧
      16 < 2 ^ w ∧ eCap ≤ 2 ^ w ∧
      prevBase + eCap * L ≤ heap ∧ dst + eCap * L ≤ heap ∧
      listPtr + L_list.length ≤ heap ∧
      (prevBase + eCap * L ≤ dst ∨ dst + eCap * L ≤ prevBase) ∧
      (listPtr + L_list.length ≤ dst ∨ dst + eCap * L ≤ listPtr) ∧
      ListAt mem listPtr L_list ∧ (∀ e ∈ L_list, e < eCap) ∧
      (∀ e ∈ L_list, numBase + e * Lw + Lw ≤ heap ∧ denBase + e * Lw + Lw ≤ heap ∧
        (numBase + e * Lw + Lw ≤ dst ∨ dst + eCap * L ≤ numBase + e * Lw) ∧
        (denBase + e * Lw + Lw ≤ dst ∨ dst + eCap * L ≤ denBase + e * Lw) ∧
        SelCoreLenEntryOk P shift L Lw mem prevBase numBase denBase e) ∧
      ZeroFrom mem heap ∧
      heap + L_list.length * selCoreLenEdgeSpace L Lw < 2 ^ w
  post args mem ret mem' :=
    ∃ prevBase numBase denBase dst listPtr L Lw shift heap,
      args = [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap] ∧
      ret = heap + L_list.length * selCoreLenEdgeSpace L Lw ∧
      (∀ e ∈ L_list, Num.Valid mem' (dst + e * L) 4 L ∧
        Num.fixVal mem' (dst + e * L) 4 L (P + shift) =
          selCoreLenVal mem P prevBase numBase denBase L Lw e) ∧
      ZeroFrom mem' ret ∧
      (∀ a < heap, (a < dst ∨ dst + eCap * L ≤ a) → mem' a = mem a) ∧
      (∀ e < eCap, e ∉ L_list → ∀ t < L, mem' (dst + e * L + t) = mem (dst + e * L + t))
  cost args _ := L_list.length * (selCoreLenEdgeCost (args.getD 6 0) (args.getD 7 0) + 40) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

private theorem ent_disj {e e' L t : ℕ} (hne : e ≠ e') (ht : t < L) :
    e * L + t < e' * L ∨ e' * L + L ≤ e * L + t := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega
  · right
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega

private theorem entry_congr {mem mem' : ℕ → ℕ} {a h L P : ℕ}
    (heq : ∀ t < L, mem' (a + t) = mem (a + t)) :
    (Num.Valid mem' a h L ↔ Num.Valid mem a h L) ∧
      Num.fixVal mem' a h L P = Num.fixVal mem a h L P := by
  refine ⟨⟨fun hv t ht => heq t ht ▸ hv t ht, fun hv t ht => (heq t ht).symm ▸ hv t ht⟩, ?_⟩
  unfold Num.fixVal
  rw [Num.intVal_congr heq]

private theorem SelCoreLenEntryOk.congr {P shift L Lw : ℕ} {mem mem' : ℕ → ℕ}
    {prevBase numBase denBase e : ℕ}
    (hok : SelCoreLenEntryOk P shift L Lw mem prevBase numBase denBase e)
    (hp : ∀ t < L, mem' (prevBase + e * L + t) = mem (prevBase + e * L + t))
    (hn : ∀ t < Lw, mem' (numBase + e * Lw + t) = mem (numBase + e * Lw + t))
    (hd : ∀ t < Lw, mem' (denBase + e * Lw + t) = mem (denBase + e * Lw + t)) :
    SelCoreLenEntryOk P shift L Lw mem' prevBase numBase denBase e ∧
      selCoreLenVal mem' P prevBase numBase denBase L Lw e =
        selCoreLenVal mem P prevBase numBase denBase L Lw e := by
  have cp := entry_congr (h := 4) (P := P) hp
  have cn := entry_congr (h := 4) (P := P) hn
  have cd := entry_congr (h := 4) (P := P) hd
  have hval : selCoreLenVal mem' P prevBase numBase denBase L Lw e =
      selCoreLenVal mem P prevBase numBase denBase L Lw e := by
    unfold selCoreLenVal; rw [cp.2, cn.2, cd.2]
  obtain ⟨v1, v2, v3, hdPos, hshFit, q, hqFit, hqVal⟩ := hok
  refine ⟨⟨cp.1.2 v1, cn.1.2 v2, cd.1.2 v3, cd.2 ▸ hdPos, ?_, q, hqFit, hqVal.trans hval.symm⟩, hval⟩
  rw [Num.intVal_congr hp]; exact hshFit

private def dummyLSFConst (wstrVal : ℝ) : LSF where
  T := { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  F := { F := { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }, R := ∅ }
  wstr := fun _ => wstrVal

/-- **Per-edge core-length update.** `selCoreLenEdgeBody` meets `selCoreLenEdgeContract`. -/
theorem selCoreLenEdge_meetsContract {w P proc shiftLeft wireEdge signExt mul intDiv copy : ℕ}
    {p : Program}
    (hp : p.procs[proc]? = some (selCoreLenEdgeBody shiftLeft wireEdge))
    (hShift : MeetsContract w p shiftLeft (Num.shiftLeftContract w 4))
    (hWire : p.procs[wireEdge]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p proc (selCoreLenEdgeContract w P) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨prevBase, numBase, denBase, dst, e, L, Lw, shift, heap, rfl, hw16,
    hPrevLe, hNumLe, hDenLe, hDstLe, hOk, hz, hRoom⟩ := hpre
  obtain ⟨hPrevV, hNumV, hDenV, hDenPos, hShFit, q, hqFit, hqVal⟩ := hOk
  have hRoom' : heap + L + wireCoreLenEdgeSpace (max L Lw) < 2 ^ w := by
    unfold selCoreLenEdgeSpace at hRoom; omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw0 : 0 < 2 ^ w := by omega
  have hprevA : prevBase + e * L < 2 ^ w := by omega
  have hnumA : numBase + e * Lw < 2 ^ w := by omega
  have hdenA : denBase + e * Lw < 2 ^ w := by omega
  have hdstA : dst + e * L < 2 ^ w := by omega
  have hLW : L < 2 ^ w := hwords L (by simp)
  have hLwW : Lw < 2 ^ w := hwords Lw (by simp)
  have hShW : shift < 2 ^ w := hwords shift (by simp)
  have hHeapW : heap < 2 ^ w := by omega
  have h1W : heap + L < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold selCoreLenEdgeBody
  refine runs_seq_assign_flat (v := prevBase + e * L) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := numBase + e * Lw) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := denBase + e * Lw) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := dst + e * L) (by eval_expr) ?_
  -- Call 1: `shiftLeft [prevBase + e * L, L, shift, heap]` -> `heap + L`
  refine runs_seq_call_flat hShift (vs := [prevBase + e * L, L, shift, heap])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨prevBase + e * L, L, shift, heap, rfl, hPrevLe, hPrevV⟩, hz, h1W⟩
  · intro h1 mem1 pos1 hp1
    obtain ⟨hh1Eq, _, _, hFr1, hz1, hShV, hShVal⟩ := hp1
    change h1 = heap + L at hh1Eq; subst hh1Eq
    change ∀ a < heap, mem1 a = mem a at hFr1
    change ZeroFrom mem1 (heap + L) at hz1
    change Num.Valid mem1 heap 4 L at hShV
    change Num.intVal mem1 heap 4 L =
      Num.wrap 4 L (Num.intVal mem (prevBase + e * L) 4 L * (2 : ℤ) ^ shift) at hShVal
    rw [Num.wrap_of_fits hShFit] at hShVal
    -- Set up `wireCoreLenEdge_runs` at index `0` and precision `P + shift`.
    let wstrVal : ℝ :=
      Num.fixVal mem (numBase + e * Lw) 4 Lw P / Num.fixVal mem (denBase + e * Lw) 4 Lw P
    let prevVal : ℝ := Num.fixVal mem (prevBase + e * L) 4 L P
    have hNumV1 : Num.Valid mem1 (numBase + e * Lw + 0 * Lw) 4 Lw := by
      intro i hi
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hFr1 (numBase + e * Lw + i) (by omega)]
      exact hNumV i hi
    have hDenV1 : Num.Valid mem1 (denBase + e * Lw + 0 * Lw) 4 Lw := by
      intro i hi
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hFr1 (denBase + e * Lw + i) (by omega)]
      exact hDenV i hi
    have hDenEq1 : Num.intVal mem1 (denBase + e * Lw) 4 Lw =
        Num.intVal mem (denBase + e * Lw) 4 Lw := Num.intVal_congr fun i hi => hFr1 _ (by omega)
    have hNumEq1 : Num.intVal mem1 (numBase + e * Lw) 4 Lw =
        Num.intVal mem (numBase + e * Lw) 4 Lw := Num.intVal_congr fun i hi => hFr1 _ (by omega)
    have h2P : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
    have h2PS : (0 : ℝ) < (2 : ℝ) ^ (P + shift) := pow_pos zero_lt_two (P + shift)
    have hDenPos1 : 0 < Num.fixVal mem1 (denBase + e * Lw + 0 * Lw) 4 Lw (P + shift) := by
      simp only [Nat.zero_mul, Nat.add_zero, Num.fixVal, hDenEq1]
      have hDint : (0 : ℝ) < (Num.intVal mem (denBase + e * Lw) 4 Lw : ℝ) := by
        unfold Num.fixVal at hDenPos
        exact (div_pos_iff_of_pos_right h2P).mp hDenPos
      exact div_pos hDint h2PS
    have hWstr1 :
        Num.fixVal mem1 (numBase + e * Lw + 0 * Lw) 4 Lw (P + shift) /
          Num.fixVal mem1 (denBase + e * Lw + 0 * Lw) 4 Lw (P + shift) =
        (dummyLSFConst wstrVal).wstr 0 := by
      simp only [Nat.zero_mul, Nat.add_zero, Num.fixVal, hNumEq1, hDenEq1, dummyLSFConst, wstrVal]
      rw [div_div_div_cancel_right₀ h2PS.ne', div_div_div_cancel_right₀ h2P.ne']
    have hLen1 : Num.fixVal mem1 (heap + 0 * L) 4 L (P + shift) = prevVal := by
      simp only [Nat.zero_mul, Nat.add_zero, Num.fixVal, hShVal, prevVal]
      have h2S : (0 : ℝ) < (2 : ℝ) ^ shift := pow_pos zero_lt_two shift
      rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, pow_add, mul_div_mul_right _ _ h2S.ne']
    have hqVal1 : (q : ℝ) / (2 : ℝ) ^ (P + shift) =
        coreLen (dummyLSFConst wstrVal) (fun _ => prevVal) 0 := by
      simpa [coreLen, dummyLSFConst, selCoreLenVal, wstrVal, prevVal] using hqVal
    obtain ⟨out2, c2, r2, hc2, hV2, hFix2, hz2, hFr2⟩ :=
      wireCoreLenEdge_runs (w := w) (L := L) (Lw := Lw) (P := P + shift)
        (numPtr := numBase + e * Lw) (denPtr := denBase + e * Lw) (lenPtr := heap)
        (outPtr := dst + e * L) (e := 0) (heap := heap + L)
        (forest := dummyLSFConst wstrVal) (ℓ := fun _ => prevVal) (q := q)
        (pos := pos1) (ω := ω) (mem := mem1)
        hSign hMul hDiv hCopy hNumV1 hDenV1 (by simpa using hShV)
        hDenPos1 hWstr1 hLen1 hqFit hqVal1
        (by omega) (by omega) (by omega) (by omega) hz1 hRoom' hw4
    have hNextEq : heap + L + wireCoreLenEdgeSpace (max L Lw) =
        heap + selCoreLenEdgeSpace L Lw := by unfold selCoreLenEdgeSpace; omega
    have hcall2 : ∀ regs1 : ℕ → ℕ,
        regs1 5 = L → regs1 6 = Lw → regs1 8 = heap →
        regs1 10 = numBase + e * Lw → regs1 11 = denBase + e * Lw →
        regs1 12 = dst + e * L → regs1 13 = heap + L →
        Runs w p ω
          (.call 14 wireEdge [.reg 10, .reg 11, .reg 8, .reg 12, .const 0, .reg 5, .reg 6, .reg 13])
          ⟨mem1, regs1, pos1⟩ .normal
          ⟨out2.mem, Function.update regs1 14 (heap + L + wireCoreLenEdgeSpace (max L Lw)), out2.pos⟩
          (c2 + 9) := by
      intro regs1 r5 r6 r8 r10 r11 r12 r13
      refine runs_call_iff.mpr ⟨[numBase + e * Lw, denBase + e * Lw, heap, dst + e * L, 0, L, Lw,
          heap + L], wireCoreLenEdgeBody signExt mul intDiv copy,
        .returned (heap + L + wireCoreLenEdgeSpace (max L Lw)), out2, c2,
        by simp [evalArgs, Expr.eval, r5, r6, r8, r10, r11, r12, r13, hw0],
        hWire, r2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have hretW : heap + selCoreLenEdgeSpace L Lw < 2 ^ w := by omega
    refine ⟨.returned (heap + selCoreLenEdgeSpace L Lw),
      ⟨out2.mem, Function.update _ 14 (heap + L + wireCoreLenEdgeSpace (max L Lw)), out2.pos⟩,
      (c2 + 9) + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _,
        hcall2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        runs_ret_iff.mpr ⟨heap + selCoreLenEdgeSpace L Lw, by simp [Expr.eval, hNextEq], rfl, rfl, rfl⟩,
        rfl⟩), ?_, ?_⟩
    · dsimp only [selCoreLenEdgeContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨by simp, by simpa using hV2, ?_, hNextEq ▸ hz2, fun a ha hout => ?_⟩
      · simpa [coreLen, dummyLSFConst, selCoreLenVal, wstrVal, prevVal] using hFix2
      · exact (hFr2 a (by omega) (by simpa using hout)).trans (hFr1 a ha)
    · simp only [selCoreLenEdgeContract, selCoreLenEdgeCost, Num.shiftLeftContract, heapContract,
        List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
      omega

set_option maxHeartbeats 600000 in
/-- **The core lengths of the listed edges.** `selCoreLenFillBody` meets
`selCoreLenFillContract`. -/
theorem selCoreLenFill_meetsContract {w P proc edgeProc eCap : ℕ} {L_list : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selCoreLenFillBody edgeProc))
    (hEdge : MeetsContract w p edgeProc (selCoreLenEdgeContract w P)) :
    MeetsContract w p proc (selCoreLenFillContract w P eCap L_list) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨prevBase, numBase, denBase, dst, listPtr, L, Lw, shift, heap, rfl, hw16, heCapW,
    hPrevLe, hDstLe, hListLe, hpd, hld, hlist, hcap, hok, hz, hRoom⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hNumW : numBase < 2 ^ w := hwords numBase (by simp)
  have hDenW : denBase < 2 ^ w := hwords denBase (by simp)
  have hLW : L < 2 ^ w := hwords L (by simp)
  have hLwW : Lw < 2 ^ w := hwords Lw (by simp)
  have hShW : shift < 2 ^ w := hwords shift (by simp)
  have hentEnd : ∀ e ∈ L_list, e * L + L ≤ eCap * L := fun e he => by
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hcap e he))
    rw [Nat.succ_mul] at this; exact this
  have hloop := Triple.forRange_const (p := p) (r := 10) (lo := .const 0) (hi := .reg 5)
    (body := .assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
      .call 9 edgeProc
        [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11, .reg 6, .reg 7, .reg 8, .reg 9])
    (P := fun st => st = startState
      [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap] mem pos)
    (Inv := fun i st =>
      st.regs 0 = prevBase ∧ st.regs 1 = numBase ∧ st.regs 2 = denBase ∧ st.regs 3 = dst ∧
      st.regs 4 = listPtr ∧ st.regs 5 = L_list.length ∧ st.regs 6 = L ∧ st.regs 7 = Lw ∧
      st.regs 8 = shift ∧ st.regs 9 = heap + i * selCoreLenEdgeSpace L Lw ∧ st.regs 10 = i ∧
      ZeroFrom st.mem (heap + i * selCoreLenEdgeSpace L Lw) ∧
      (∀ i' < i, ∀ (hi' : i' < L_list.length),
        Num.Valid st.mem (dst + L_list[i'] * L) 4 L ∧
        Num.fixVal st.mem (dst + L_list[i'] * L) 4 L (P + shift) =
          selCoreLenVal mem P prevBase numBase denBase L Lw L_list[i']) ∧
      (∀ a < heap, (∀ i' < i, ∀ (hi' : i' < L_list.length),
        a < dst + L_list[i'] * L ∨ dst + L_list[i'] * L + L ≤ a) → st.mem a = mem a))
    (selCoreLenEdgeCost L Lw + 30) 0 L_list.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst st
      exact ⟨by eval_expr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [startState],
        by simp, by simpa [startState] using hz, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ _ => rfl⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h5 := hi.2.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hzI, hdone, hout⟩
      have heL : L_list[i] ∈ L_list := List.getElem_mem hi
      have heCap : L_list[i] < eCap := hcap _ heL
      have heEnd := hentEnd _ heL
      obtain ⟨hNumLeI, hDenLeI, hNumDisjI, hDenDisjI, hOkI⟩ := hok _ heL
      have hiSp : (i + 1) * selCoreLenEdgeSpace L Lw ≤ L_list.length * selCoreLenEdgeSpace L Lw :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      have hcurSp : heap + i * selCoreLenEdgeSpace L Lw + selCoreLenEdgeSpace L Lw =
          heap + (i + 1) * selCoreLenEdgeSpace L Lw := by rw [Nat.succ_mul]; omega
      have hmemList : st.mem (listPtr + i) = L_list[i] := by
        rw [hout (listPtr + i) (by omega) (fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi'); omega)]
        exact hlist i hi
      have hOkSt : SelCoreLenEntryOk P shift L Lw st.mem prevBase numBase denBase L_list[i] ∧
          selCoreLenVal st.mem P prevBase numBase denBase L Lw L_list[i] =
            selCoreLenVal mem P prevBase numBase denBase L Lw L_list[i] :=
        hOkI.congr
          (fun t ht => hout _ (by omega) fun i' _ hi' => by have := hentEnd _ (List.getElem_mem hi'); omega)
          (fun t ht => hout _ (by omega) fun i' _ hi' => by have := hentEnd _ (List.getElem_mem hi'); omega)
          (fun t ht => hout _ (by omega) fun i' _ hi' => by have := hentEnd _ (List.getElem_mem hi'); omega)
      apply runs_start_le
      refine runs_seq_assign_le (v := L_list[i]) (by eval_expr) ?_
      refine runs_call_le hEdge
        (vs := [prevBase, numBase, denBase, dst, L_list[i], L, Lw, shift,
          heap + i * selCoreLenEdgeSpace L Lw])
        (by eval_expr) (by wram_words)
        ⟨prevBase, numBase, denBase, dst, L_list[i], L, Lw, shift,
          heap + i * selCoreLenEdgeSpace L Lw, rfl, hw16,
          by omega, by omega, by omega, by omega, hOkSt.1, hzI, by omega⟩ ?_
      intro ret mem' pos' hpE
      obtain ⟨hret, hvE, hvalE, hzE, hfrE⟩ := hpE
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hret hvE hvalE hfrE
      rw [hcurSp] at hret
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
        by simpa using h8, by simp [hret], by simp, hret ▸ hzE,
        fun i' hi' hlt' => ?_, fun a ha hout' => ?_⟩, by simpa using h10⟩, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
        · by_cases heq : L_list[i'] = L_list[i]
          · rw [heq]; exact ⟨hvE, hvalE.trans hOkSt.2⟩
          · have hkeep : ∀ t < L, mem' (dst + L_list[i'] * L + t) = st.mem (dst + L_list[i'] * L + t) :=
              fun t ht => hfrE _ (by have := hentEnd _ (List.getElem_mem hlt'); omega)
                (by rcases ent_disj heq ht with h | h <;> [left; right] <;> omega)
            have c := entry_congr (h := 4) (P := P + shift) hkeep
            exact ⟨c.1.2 (hdone i' hlt hlt').1, c.2.trans (hdone i' hlt hlt').2⟩
        · exact ⟨hvE, hvalE.trans hOkSt.2⟩
      · dsimp only
        have hdisjI := hout' i (Nat.lt_succ_self i) hi
        rw [hfrE a (by omega) hdisjI]
        exact hout a ha fun i' hi' hlt' => hout' i' (Nat.lt_succ_of_lt hi') hlt'
      · simp only [selCoreLenEdgeContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
          argsSize]
        omega)
  apply runs_start_le
  unfold selCoreLenFillBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, _, _, _, _, h9, _, hz1, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := heap + L_list.length * selCoreLenEdgeSpace L Lw)
    (by simp [Expr.eval, h9]) ?_ ?_
  · refine ⟨prevBase, numBase, denBase, dst, listPtr, L, Lw, shift, heap, rfl, rfl,
      fun e he => ?_, hz1, fun a ha hnotDst => ?_, fun e he hnot t ht => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact hdone i hi hi
    · refine hout a ha fun i' _ hi' => ?_
      have := hentEnd _ (List.getElem_mem hi')
      omega
    · refine hout _ (by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
        rw [Nat.succ_mul] at this; omega) fun i' _ hi' => ?_
      have hne : e ≠ L_list[i'] := fun h => hnot (h ▸ List.getElem_mem hi')
      rcases ent_disj hne ht with h | h
      · left; omega
      · right; omega
  · simp only [selCoreLenFillContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    nlinarith

/-- **The table after the fill.** Suppose the listed edges have stretch `num / den = wstr e`
(`Lw` limbs) and old length `prev e` (`L` limbs, precision `P`), the table at `dst` holds `vold`
on `Eold` at precision `P + shift`, and every new edge is listed or old. Then after the fill the
table holds `vnew` at precision `P + shift`: `wstr e · prev e` on the listed edges and `vold` on
the others. -/
theorem edgeValuesAt_of_coreLenFill {w P eCap : ℕ} {L_list : List ℕ} {args : List ℕ}
    {mem mem' : ℕ → ℕ} {ret : ℕ} {Eold Enew : Finset ℕ} {wstr prev vold vnew : ℕ → ℝ}
    (hpost : (selCoreLenFillContract w P eCap L_list).post args mem ret mem')
    (hprev : ∀ e ∈ L_list,
      Num.fixVal mem (args.getD 0 0 + e * args.getD 6 0) 4 (args.getD 6 0) P = prev e)
    (hstr : ∀ e ∈ L_list,
      Num.fixVal mem (args.getD 1 0 + e * args.getD 7 0) 4 (args.getD 7 0) P /
        Num.fixVal mem (args.getD 2 0 + e * args.getD 7 0) 4 (args.getD 7 0) P = wstr e)
    (hold : EdgeValuesAt mem (args.getD 3 0) 4 (args.getD 6 0) (P + args.getD 8 0) Eold vold)
    (hcapOld : ∀ e ∈ Eold, e < eCap)
    (hnew : ∀ e ∈ Enew, e ∈ L_list ∨ e ∈ Eold)
    (hvL : ∀ e ∈ Enew, e ∈ L_list → vnew e = wstr e * prev e)
    (hvO : ∀ e ∈ Enew, e ∉ L_list → vnew e = vold e) :
    EdgeValuesAt mem' (args.getD 3 0) 4 (args.getD 6 0) (P + args.getD 8 0) Enew vnew := by
  obtain ⟨prevBase, numBase, denBase, dst, listPtr, L, Lw, shift, heap, rfl, _, hcp, _, _,
    hkeep⟩ := hpost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hprev hstr hold ⊢
  intro e he
  by_cases heL : e ∈ L_list
  · obtain ⟨hv, hf⟩ := hcp e heL
    refine ⟨hv, ?_⟩
    rw [hf, hvL e he heL, selCoreLenVal, hstr e heL, hprev e heL]
  · have heO := (hnew e he).resolve_left heL
    have hs := hold e heO
    have c := entry_congr (P := P + shift) (h := 4) (a := dst + e * L)
      (hkeep e (hcapOld e heO) heL)
    exact ⟨c.1.2 hs.1, c.2.trans (hs.2.trans (hvO e he heL).symm)⟩

/-- **The core lengths of level `j` after a fill.** A fill into `B.lenPtr j` with
`shift = if j < B.d then 0 else pLast` and `B.endAddr ≤ heap` keeps every other part of the blocks,
and gives the new lengths `lenj'` on the new edges `E'` at precision `coreLenPrec B.d P pLast j`:
`wstr e · prev e` on the listed edges and the old lengths on the others. -/
theorem selCoreLenFill_setLen {w P j pLast Lw heap : ℕ} {B : SelectBlocksLoc} {L_list : List ℕ}
    {prevBase numBase denBase listPtr : ℕ} {mem mem' : ℕ → ℕ} {ret : ℕ} {D : SelBlocksData}
    {E' : Finset ℕ} {wstr prev lenj' : ℕ → ℝ}
    (hpost : (selCoreLenFillContract w P B.eCap L_list).post
      [prevBase, numBase, denBase, B.lenPtr j, listPtr, L_list.length, B.Lk, Lw,
        if j < B.d then 0 else pLast, heap] mem ret mem')
    (hblk : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d) (hEndLe : B.endAddr ≤ heap)
    (hprev : ∀ e ∈ L_list, Num.fixVal mem (prevBase + e * B.Lk) 4 B.Lk P = prev e)
    (hstr : ∀ e ∈ L_list, Num.fixVal mem (numBase + e * Lw) 4 Lw P /
      Num.fixVal mem (denBase + e * Lw) 4 Lw P = wstr e)
    (hLcap : ∀ e ∈ L_list, e < B.eCap)
    (hnew : ∀ e ∈ E', e ∈ L_list ∨ e ∈ D.E j)
    (hvL : ∀ e ∈ E', e ∈ L_list → lenj' e = wstr e * prev e)
    (hvO : ∀ e ∈ E', e ∉ L_list → lenj' e = D.len j e) :
    SelBlocksDataAt mem' B P
      { D with E := Function.update D.E j E', len := Function.update D.len j lenj' } pLast := by
  have hLen := hblk.2.2.1 j hj
  have hPrec : P + (if j < B.d then 0 else pLast) = coreLenPrec B.d P pLast j := by
    unfold coreLenPrec; split_ifs <;> omega
  have hfr := hpost
  obtain ⟨_, _, _, _, _, _, _, _, _, hargs, _, _, _, hout, _⟩ := hfr
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl, rfl, rfl, -⟩ := hargs
  have hblkEnd : ∀ a, a < B.endAddr → a < heap := fun a ha => lt_of_lt_of_le ha hEndLe
  -- Every region inside the blocks lies below `B.endAddr ≤ heap`.
  have hKeepBlk : ∀ a, B.base ≤ a → a < B.endAddr → ¬ B.regLen j a → mem' a = mem a :=
    fun a _ ha hnot => hout a (hblkEnd a ha) (by
      unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr at hnot; omega)
  have hLenNew : SelPartLen mem' B P j E' lenj' pLast := by
    refine ⟨fun e he => (hnew e he).elim (hLcap e) (hLen.1 e), ?_⟩
    rw [← hPrec]
    exact edgeValuesAt_of_coreLenFill hpost hprev hstr (hPrec ▸ hLen.2) hLen.1 hnew hvL hvO
  -- Update the `len` part while keeping all other parts via `B.endAddr ≤ heap`.
  have hF0 := hblk.1
  have hPhi0 := hblk.2.1
  have hLen0 := hblk.2.2.1
  have hEmb0 := hblk.2.2.2.1
  have hLast0 := hblk.2.2.2.2.1
  have hG00 := hblk.2.2.2.2.2
  have hb : ∀ k a, B.regBlk k a → B.base ≤ a := fun k a h => by
    unfold SelectBlocksLoc.regBlk SelectBlocksLoc.fPtr at h; omega
  have he : ∀ k a, k ≤ B.d → B.regBlk k a → a < B.endAddr := fun k a hk h => by
    have := B.blk_le_last hk
    unfold SelectBlocksLoc.regBlk at h; unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  refine ⟨fun j' hj' => (hF0 j' hj').of_agree fun a ha =>
      hKeepBlk a (hb j' a (B.regF_blk ha)) (he j' a hj' (B.regF_blk ha))
        fun h' => B.regF_not_len ha h',
    fun j' hj' => (hPhi0 j' hj').of_agree fun a ha =>
      hKeepBlk a (hb j' a (B.regPhi_blk ha)) (he j' a hj' (B.regPhi_blk ha))
        fun h' => B.regPhi_not_len ha h',
    fun j' hj' => ?_,
    fun j' hj' => (hEmb0 j' hj').of_agree fun a ha =>
      hKeepBlk a (hb j' a (B.regEmb_blk ha)) (he j' a hj'.le (B.regEmb_blk ha))
        fun h' => B.regLen_not_emb h' ha,
    hLast0.of_agree fun a ha =>
      hKeepBlk a (by unfold SelectBlocksLoc.regLast SelectBlocksLoc.lastGPtr at ha; omega)
        (by unfold SelectBlocksLoc.regLast at ha; unfold SelectBlocksLoc.endAddr; omega)
        fun h' => B.regBlk_not_last hj (B.regLen_blk h') ha,
    hG00.of_agree fun a ha =>
      hKeepBlk a (by unfold SelectBlocksLoc.regG0 SelectBlocksLoc.g0Ptr SelectBlocksLoc.lastGPtr at ha; omega)
        ha.2 fun h' => B.regBlk_not_g0 hj (B.regLen_blk h') ha⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hLenNew
  · simp only [Function.update_of_ne hjj]
    exact (hLen0 j' hj').of_agree fun a ha =>
      hKeepBlk a (hb j' a (B.regLen_blk ha)) (he j' a hj' (B.regLen_blk ha))
        fun h' => B.regLen_disj (Ne.symm hjj) h' ha

end MinCostFlow.MinRatio
