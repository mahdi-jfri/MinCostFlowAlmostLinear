module

public import MinCostFlow.MinRatio.DetectorThresholdProgram
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.Negate
public import WordRAM.CopyWords
public import MinCostFlow.Num.IPM.AlphaFacts
import WordRAM.Logic

/-!
# Initial Detect thresholds and edge payload records

At initialization of Algorithm 2 (Theorem 5.1, pages 29–30), each live edge `e`
starts with zero flow, zero detection account, positive integer threshold
`detectorThreshold P ε (ℓ₀ e)`, and initial path-edge payload record
`[1, 1, g₀ e, ℓ₀ e, 0, -detectorThreshold P ε (ℓ₀ e)]`. This module builds the
dyadic block `-ε` once and loops over `e = 0 .. m - 1` to populate the
per-edge threshold pointer array and initial payload record array.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Heap words allocated per edge for its negative residual, positive
threshold block, and initial path-edge payload record. -/
@[expose] def initEdgeRecordSpace (L : ℕ) : ℕ :=
  Num.fixedDivideSpace L + 5 * L + 2

/-- Initial path-edge payload for an edge with encoded gradient `gInt`,
encoded positive length `lInt`, precision `P`, and detection parameter `ε`. -/
@[expose] noncomputable def initialPathEdgeValue (P : ℕ) (ε : ℝ)
    (gInt : ℤ) (lInt : ℕ) : PathEdgeValue where
  forward := true
  gradient := gInt
  length := (lInt : ℤ)
  flow := 0
  detector := -detectorThreshold P ε ((lInt : ℝ) / (2 : ℝ) ^ P)

/-- The concrete Algorithm 2 detection threshold `(1 / 2^k) * alphaPrime m V / 1024`
equals `2 ^ (P - epsExp) / 2 ^ P` whenever `epsExp ≤ P`. -/
theorem concreteDetectEps_eq_dyadic (m V k P : ℕ)
    (hle : Num.IPM.alphaExponent m V + k + 10 ≤ P) :
    let epsExp := Num.IPM.alphaExponent m V + k + 10
    (1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m V / 1024) =
      (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P := by
  dsimp only
  let epsExp := Num.IPM.alphaExponent m V + k + 10
  have h1024 : (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
  have hpow : (2 : ℝ) ^ P = (2 : ℝ) ^ (P - epsExp) * (2 : ℝ) ^ epsExp := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [Num.IPM.alphaPrime, h1024, Int.cast_pow, Int.cast_ofNat, hpow,
    div_mul_eq_div_div, div_self (by positivity), one_div, one_div, one_div,
    div_eq_mul_inv, mul_comm ((2 : ℝ) ^ k)⁻¹, mul_assoc, ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  congr 2
  dsimp only [epsExp]
  omega

/-- Allocate an `L`-limb block storing `-(2 ^ (P - epsExp))` at `heap + 2 * L`
using `regs 67 = L`, `regs 68 = P`, `regs 73 = epsExp`, and `regs 99 = heap`.
Saves the pointer in `regs 95` and advances `regs 99` to `heap + 3 * L`. -/
@[expose] def initNegEpsilonBlock (shift negate : ℕ) : Stmt :=
  .store (.reg 99) (.const 1) ;;
  .assign 1 (.bin .sub (.reg 68) (.reg 73)) ;;
  .call 2 shift [.reg 99, .reg 67, .reg 1, .bin .add (.reg 99) (.reg 67)] ;;
  .assign 95 (.reg 2) ;;
  .call 99 negate [.bin .add (.reg 99) (.reg 67), .reg 67, .reg 2]

theorem initNegEpsilonBlock_noRand (shift negate : ℕ) :
    (initNegEpsilonBlock shift negate).NoRand := by
  simp [initNegEpsilonBlock, Stmt.NoRand]

private theorem unitBlock_valid_and_val {mem : ℕ → ℕ} {heap L : ℕ}
    (hL : 0 < L) (hz : ZeroFrom mem heap) :
    Num.Valid (Function.update mem heap 1) heap 4 L ∧
    Num.intVal (Function.update mem heap 1) heap 4 L = 1 := by
  have hval : Num.Valid (Function.update mem heap 1) heap 4 L := by
    intro j hj
    cases j with
    | zero => simp [Num.base]
    | succ j =>
      rw [Function.update_of_ne (by omega), hz _ (by omega)]
      decide
  refine ⟨hval, ?_⟩
  have huns : Num.unsignedVal (Function.update mem heap 1) heap 4 L = 1 := by
    cases L with
    | zero => omega
    | succ L' =>
      rw [Num.unsignedVal]
      have hz' : Num.unsignedVal (Function.update mem heap 1) (heap + 1) 4 L' = 0 := by
        apply Num.unsignedVal_zero
        intro j _
        rw [Function.update_of_ne (by omega)]
        exact hz _ (by omega)
      rw [hz']
      simp
  rw [Num.intVal, huns]
  have hcap : 2 * 1 < Num.capacity 4 L := by
    unfold Num.capacity Num.base
    rw [← pow_mul]
    have h4 : 4 ≤ 4 * L := by omega
    exact lt_of_lt_of_le (by decide : 2 * 1 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) h4)
  simp [Num.signedVal, hcap]

/-- Build the `L`-limb block storing `-(2 ^ (P - epsExp))` in `O(L)` steps. -/
theorem initNegEpsilonBlock_runs {w shift negate L P epsExp heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = P)
    (h73 : st.regs 73 = epsExp) (h99 : st.regs 99 = heap)
    (hLpos : 0 < L) (hPword : P < 2 ^ w) (hle : epsExp ≤ P) (hfitPos : P - epsExp + 1 < 4 * L)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 3 * L < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (initNegEpsilonBlock shift negate) st .normal out cost ∧
      out.regs 95 = heap + 2 * L ∧ out.regs 99 = heap + 3 * L ∧
      PathIntAt out.mem (heap + 2 * L) 4 L (-((2 : ℤ) ^ (P - epsExp))) ∧
      ZeroFrom out.mem (heap + 3 * L) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 95 → r ≠ 99 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + 76 := by
  let s1 := { st with mem := Function.update st.mem heap 1 }
  let s2 := { s1 with regs := Function.update s1.regs 1 (P - epsExp) }
  have hr1 : Runs w p ω (.store (.reg 99) (.const 1)) st .normal s1 3 :=
    runs_store_iff.mpr ⟨heap, 1, by simp [Expr.eval, h99], by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 1 (.bin .sub (.reg 68) (.reg 73))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨P - epsExp, by
      simp [Expr.eval, BinOp.eval, s1, h68, h73, show P - epsExp < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨hunitVal, hunitInt⟩ := unitBlock_valid_and_val hLpos hz
  have hz1 : ZeroFrom s1.mem (heap + L) := by
    intro a ha
    simp only [s1]
    rw [Function.update_of_ne (by omega)]
    exact hz a (by omega)
  have hshiftPre : (Num.shiftLeftContract w 4).pre [heap, L, P - epsExp, heap + L] s2.mem :=
    ⟨⟨heap, L, P - epsExp, heap + L, rfl, le_rfl, hunitVal⟩, hz1, by
      change heap + L + L < 2 ^ w; omega⟩
  have hargs1 : evalArgs w s2 [.reg 99, .reg 67, .reg 1, .bin .add (.reg 99) (.reg 67)] =
      some [heap, L, P - epsExp, heap + L] := by
    simp [evalArgs, Expr.eval, BinOp.eval, s2, s1, h99, h67, show heap + L < 2 ^ w by omega]
  have hwords1 : ∀ a ∈ [heap, L, P - epsExp, heap + L], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨s3, c1, ret1, hr3, hpost1, hreg3, hkeep3, hc1⟩ :=
    runs_call_of_meetsContract (st := s2) (r := 2) hshift hargs1 hwords1 hshiftPre ω
  obtain ⟨hret1, _, _, hframe1, hz3, hvalEps, hintEps⟩ := hpost1
  change ret1 = heap + L + L at hret1
  change ∀ x < heap + L, s3.mem x = s2.mem x at hframe1
  have hret1' : ret1 = heap + 2 * L := by omega
  have hcap : Num.capacity 4 L = 2 ^ (4 * L) := by
    unfold Num.capacity Num.base; rw [← pow_mul]
  have hfitsEps : Num.Fits 4 L ((2 : ℤ) ^ (P - epsExp)) := by
    unfold Num.Fits
    obtain ⟨k, hk⟩ : ∃ k, 4 * L = k + 1 := ⟨4 * L - 1, by omega⟩
    have hcap2 : (Num.capacity 4 L : ℤ) = 2 * (2 : ℤ) ^ k := by
      rw [hcap, hk, pow_succ, mul_comm]; norm_cast
    have hp : (2 : ℤ) ^ (P - epsExp) < (2 : ℤ) ^ k :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    have hnn : (0 : ℤ) ≤ (2 : ℤ) ^ (P - epsExp) := by positivity
    omega
  have hintEps' : Num.intVal s3.mem (heap + L) 4 L = (2 : ℤ) ^ (P - epsExp) := by
    change Num.intVal s3.mem (heap + L) 4 L = Num.wrap 4 L (Num.intVal s2.mem heap 4 L * (2 : ℤ) ^ (P - epsExp)) at hintEps
    rw [hintEps, show s2.mem = s1.mem from rfl, hunitInt, one_mul, Num.wrap_of_fits hfitsEps]
  let s4 := { s3 with regs := Function.update s3.regs 95 ret1 }
  have hr4 : Runs w p ω (.assign 95 (.reg 2)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨ret1, by simp [Expr.eval, hreg3], rfl, rfl, rfl⟩
  have hnegPre : (Num.negateContract w 4).pre [heap + L, L, ret1] s4.mem :=
    ⟨heap + L, L, ret1, rfl,
      ⟨⟨heap + L, L, 1, ret1, rfl, by omega, le_rfl, hvalEps⟩, hz3, by
        change ret1 + L < 2 ^ w; omega⟩⟩
  have hargs2 : evalArgs w s4 [.bin .add (.reg 99) (.reg 67), .reg 67, .reg 2] =
      some [heap + L, L, ret1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, s4, Function.update_of_ne,
      hkeep3 99 (by decide), hkeep3 67 (by decide), hreg3, s2, s1, h99, h67,
      show heap + L < 2 ^ w by omega]
  have hwords2 : ∀ a ∈ [heap + L, L, ret1], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨out, c2, ret2, hr5, hpost2, hregOut, hkeepOut, hc2⟩ :=
    runs_call_of_meetsContract (st := s4) (r := 99) hneg hargs2 hwords2 hnegPre ω
  obtain ⟨hret2, _, _, hframe2, hzOut, hdigits⟩ := hpost2
  change ret2 = ret1 + L at hret2
  change ∀ x < ret1, out.mem x = s4.mem x at hframe2
  obtain ⟨hvalNeg, hintNeg⟩ := Num.negateCarry_value_one hvalEps hdigits
  have hfitsNeg : Num.Fits 4 L (-((2 : ℤ) ^ (P - epsExp))) := by
    unfold Num.Fits at hfitsEps ⊢
    have hnn : (0 : ℤ) ≤ (2 : ℤ) ^ (P - epsExp) := by positivity
    omega
  change Num.intVal out.mem ret1 4 L = Num.wrap 4 L (-Num.intVal s3.mem (heap + L) 4 L) at hintNeg
  rw [hintEps', Num.wrap_of_fits hfitsNeg] at hintNeg
  refine ⟨out, 3 + (4 + (c1 + (2 + c2 + 1) + 1) + 1) + 1, ?_,
    (hkeepOut 95 (by decide)).trans (by simp [s4, hret1']),
    hregOut.trans (by omega), hret1' ▸ ⟨hvalNeg, hintNeg⟩,
    (show ret2 = heap + 3 * L by omega) ▸ hzOut, ?_, ?_, ?_⟩
  · unfold initNegEpsilonBlock
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, c1, _, hr3, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s4, 2, c2, hr4, hr5, rfl⟩)
  · intro x hx
    have h2 : out.mem x = s3.mem x := hframe2 x (by omega)
    have h1 : s3.mem x = s1.mem x := hframe1 x (by omega)
    rw [h2, h1]
    exact Function.update_of_ne (by omega) _ _
  · intro r h1 h2 h95 h99'
    rw [hkeepOut r h99']
    simp only [s4, Function.update_of_ne h95]
    rw [hkeep3 r h2]
    simp [s2, s1, Function.update_of_ne h1]
  · simp only [Num.shiftLeftContract, Num.negateContract, heapContract, argsSize, Expr.size,
      List.getD_cons_zero, List.getD_cons_succ] at hc1 hc2
    omega

/-- Compute and store the positive Detect threshold and initial `PathEdgeAt`
record for the edge index in register `0`.
Uses `regs 67 = L`, `regs 68 = P`, `regs 70 = gradient`, `regs 71 = lengths`,
`regs 83 = edgeThresholds`, `regs 86 = edgeRecords`, `regs 95 = negEpsPtr`,
and `regs 99 = cursor`. Advances `regs 99` by `initEdgeRecordSpace L`. -/
@[expose] def initSingleEdgeThresholdAndRecord (divide negate copy : ℕ) : Stmt :=
  .assign 1 (.bin .mul (.reg 0) (.reg 67)) ;;
  .assign 2 (.bin .add (.reg 71) (.reg 1)) ;;
  .call 3 divide [.reg 95, .reg 2, .reg 67, .reg 68, .reg 99] ;;
  .assign 4 (.bin .sub (.reg 3) (.reg 67)) ;;
  .call 5 negate [.reg 4, .reg 67, .reg 3] ;;
  .store (.bin .add (.reg 83) (.reg 0)) (.reg 3) ;;
  .store (.reg 5) (.const 1) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.const 1) ;;
  .assign 6 (.bin .add (.reg 5) (.const 2)) ;;
  .call 7 copy [.bin .add (.reg 70) (.reg 1), .reg 6, .reg 67] ;;
  .assign 6 (.bin .add (.reg 6) (.reg 67)) ;;
  .call 7 copy [.reg 2, .reg 6, .reg 67] ;;
  .assign 6 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 67))) ;;
  .call 7 copy [.reg 4, .reg 6, .reg 67] ;;
  .store (.bin .add (.reg 86) (.reg 0)) (.reg 5) ;;
  .assign 99 (.bin .add (.reg 6) (.reg 67))

theorem initSingleEdgeThresholdAndRecord_noRand (divide negate copy : ℕ) :
    (initSingleEdgeThresholdAndRecord divide negate copy).NoRand := by
  simp [initSingleEdgeThresholdAndRecord, Stmt.NoRand]

/-- One iteration of threshold and initial record construction for edge `e`. -/
theorem initSingleEdgeThresholdAndRecord_runs
    {w divide negate copy e L P gradient lengths edgeThresholds edgeRecords negEpsPtr cursor : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (epsInt : ℤ) (lenInt : ℕ) (gradInt : ℤ)
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h0 : st.regs 0 = e) (h67 : st.regs 67 = L) (h68 : st.regs 68 = P)
    (h70 : st.regs 70 = gradient) (h71 : st.regs 71 = lengths)
    (h83 : st.regs 83 = edgeThresholds) (h86 : st.regs 86 = edgeRecords)
    (h95 : st.regs 95 = negEpsPtr) (h99 : st.regs 99 = cursor)
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L)
    (hlenPos : 0 < lenInt)
    (hnegEpsEnd : negEpsPtr + L ≤ cursor)
    (hlenEnd : lengths + e * L + L ≤ cursor)
    (hgradEnd : gradient + e * L + L ≤ cursor)
    (hthAddr : edgeThresholds + e < cursor)
    (hrecAddr : edgeRecords + e < cursor)
    (hdisjTR : edgeThresholds + e ≠ edgeRecords + e)
    (hgradNeTh : ∀ j < L, gradient + e * L + j ≠ edgeThresholds + e)
    (hlenNeTh : ∀ j < L, lengths + e * L + j ≠ edgeThresholds + e)
    (hnegEpsAt : PathIntAt st.mem negEpsPtr 4 L (-epsInt))
    (hlenAt : PathIntAt st.mem (lengths + e * L) 4 L lenInt)
    (hgradAt : PathIntAt st.mem (gradient + e * L) 4 L gradInt)
    (hepsPos : 0 < (epsInt : ℝ) / (2 : ℝ) ^ P)
    (hfitNeg : Num.Fits 4 L (-detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lenInt : ℝ) / (2 : ℝ) ^ P)))
    (hfitPos : Num.Fits 4 L (detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lenInt : ℝ) / (2 : ℝ) ^ P)))
    (hz : ZeroFrom st.mem cursor)
    (hroom : cursor + initEdgeRecordSpace L < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    let ε := (epsInt : ℝ) / (2 : ℝ) ^ P
    let posTh := cursor + Num.fixedDivideSpace L
    let recPtr := posTh + L
    let nextCursor := cursor + initEdgeRecordSpace L
    ∃ out cost, Runs w p ω (initSingleEdgeThresholdAndRecord divide negate copy) st .normal out cost ∧
      out.regs 99 = nextCursor ∧
      out.mem (edgeThresholds + e) = posTh ∧
      out.mem (edgeRecords + e) = recPtr ∧
      PathIntAt out.mem posTh 4 L (detectorThreshold P ε ((lenInt : ℝ) / (2 : ℝ) ^ P)) ∧
      PathEdgeAt out.mem recPtr 4 L (some (initialPathEdgeValue P ε gradInt lenInt)) ∧
      ZeroFrom out.mem nextCursor ∧
      (∀ a < cursor, a ≠ edgeThresholds + e → a ≠ edgeRecords + e → out.mem a = st.mem a) ∧
      (∀ r, 8 ≤ r → r ≠ 99 → out.regs r = st.regs r) ∧
      out.regs 0 = e ∧
      cost ≤ 2700 * L ^ 2 + 2920 * L + 860 := by
  dsimp only
  let ε := (epsInt : ℝ) / (2 : ℝ) ^ P
  let th := detectorThreshold P ε ((lenInt : ℝ) / (2 : ℝ) ^ P)
  let posTh := cursor + Num.fixedDivideSpace L
  let negTh := posTh - L
  let recPtr := posTh + L
  let nextCursor := cursor + initEdgeRecordSpace L
  have hfds : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hnextEq : recPtr + 2 + 4 * L = nextCursor := by
    simp only [recPtr, posTh, nextCursor, initEdgeRecordSpace]; omega
  let s1 := { st with regs := Function.update st.regs 1 (e * L) }
  let s2 := { s1 with regs := Function.update s1.regs 2 (lengths + e * L) }
  have hr1 : Runs w p ω (.assign 1 (.bin .mul (.reg 0) (.reg 67))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨e * L, by
      simp [Expr.eval, BinOp.eval, h0, h67, show e * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 2 (.bin .add (.reg 71) (.reg 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨lengths + e * L, by
      simp [Expr.eval, BinOp.eval, s1, h71, show lengths + e * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hdivC := detectorResidual_meetsContract (w := w) (h := 4) epsInt lenInt hdiv
  have hdivPre : (detectorResidualContract w 4 epsInt lenInt).pre
      [negEpsPtr, lengths + e * L, L, P, cursor] s2.mem :=
    ⟨negEpsPtr, lengths + e * L, L, P, cursor, rfl, hPdiv, hnegEpsEnd, hlenEnd, hlenPos,
      hnegEpsAt, hlenAt, hfitNeg, hz, by unfold initEdgeRecordSpace at hroom; omega⟩
  have hargs1 : evalArgs w s2 [.reg 95, .reg 2, .reg 67, .reg 68, .reg 99] =
      some [negEpsPtr, lengths + e * L, L, P, cursor] := by
    simp [evalArgs, Expr.eval, s2, s1, h95, h67, h68, h99]
  have hwords1 : ∀ a ∈ [negEpsPtr, lengths + e * L, L, P, cursor], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨s3, cDiv, retDiv, hr3, hpostDiv, hreg3, hkeep3, hcDiv⟩ :=
    runs_call_of_meetsContract (st := s2) (r := 3) hdivC hargs1 hwords1 hdivPre ω
  obtain ⟨_, _, _, _, _, hargsEqDiv, hretDiv, hnegThAt, hframeDiv, hzDiv⟩ := hpostDiv
  simp only [List.cons.injEq, and_true] at hargsEqDiv
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargsEqDiv
  have hretDivEq : retDiv = posTh := hretDiv
  have hnegThAt' : PathIntAt s3.mem negTh 4 L (-th) := by
    rwa [hretDivEq] at hnegThAt
  have hz3 : ZeroFrom s3.mem posTh := hretDivEq ▸ hzDiv
  let s4 := { s3 with regs := Function.update s3.regs 4 negTh }
  have hr4 : Runs w p ω (.assign 4 (.bin .sub (.reg 3) (.reg 67))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨negTh, by
      simp [Expr.eval, BinOp.eval, hreg3, hretDivEq, hkeep3 67 (by decide), s2, s1, h67, negTh,
        show posTh - L < 2 ^ w by unfold posTh initEdgeRecordSpace at *; omega],
      rfl, rfl, rfl⟩
  have hnegPre : (Num.negateContract w 4).pre [negTh, L, posTh] s4.mem :=
    ⟨negTh, L, posTh, rfl, ⟨⟨negTh, L, 1, posTh, rfl, by omega, le_rfl, hnegThAt'.1⟩, hz3,
      by change posTh + L < 2 ^ w; unfold posTh; unfold initEdgeRecordSpace at hroom; omega⟩⟩
  have hargs2 : evalArgs w s4 [.reg 4, .reg 67, .reg 3] = some [negTh, L, posTh] := by
    simp [evalArgs, Expr.eval, s4, hkeep3 67 (by decide), hreg3, hretDivEq, s2, s1, h67]
  have hwords2 : ∀ a ∈ [negTh, L, posTh], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> (unfold posTh negTh initEdgeRecordSpace at *; omega)
  obtain ⟨s5, cNeg, retNeg, hr5, hpostNeg, hreg5, hkeep5, hcNeg⟩ :=
    runs_call_of_meetsContract (st := s4) (r := 5) hneg hargs2 hwords2 hnegPre ω
  obtain ⟨hretNeg, _, _, hframeNeg, hz5, hdigitsNeg⟩ := hpostNeg
  change retNeg = posTh + L at hretNeg
  change ∀ x < posTh, s5.mem x = s4.mem x at hframeNeg
  have hretNegEq : retNeg = recPtr := hretNeg
  obtain ⟨hposVal, hposInt⟩ := Num.negateCarry_value_one hnegThAt'.1 hdigitsNeg
  rw [hnegThAt'.2, neg_neg, Num.wrap_of_fits hfitPos] at hposInt
  have hposThAt5 : PathIntAt s5.mem posTh 4 L th := ⟨hposVal, hposInt⟩
  have hz5' : ZeroFrom s5.mem recPtr := hretNegEq ▸ hz5
  have hs5Keep (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) (h5 : r ≠ 5) :
      s5.regs r = st.regs r := by
    rw [hkeep5 r h5]
    simp only [s4, Function.update_of_ne h4]
    rw [hkeep3 r h3]
    simp [s2, s1, Function.update_of_ne h2, Function.update_of_ne h1]
  have hs5_0 : s5.regs 0 = e := (hs5Keep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0
  have hs5_1 : s5.regs 1 = e * L := by
    rw [hkeep5 1 (by decide)]
    simp only [s4, Function.update_of_ne (by decide : (1 : ℕ) ≠ 4)]
    rw [hkeep3 1 (by decide)]; simp [s2, s1]
  have hs5_2 : s5.regs 2 = lengths + e * L := by
    rw [hkeep5 2 (by decide)]
    simp only [s4, Function.update_of_ne (by decide : (2 : ℕ) ≠ 4)]
    rw [hkeep3 2 (by decide)]; simp [s2]
  have hs5_3 : s5.regs 3 = posTh := by
    rw [hkeep5 3 (by decide)]
    simp only [s4, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)]
    exact hreg3.trans hretDivEq
  have hs5_4 : s5.regs 4 = negTh := by
    rw [hkeep5 4 (by decide)]; simp [s4]
  have hs5_5 : s5.regs 5 = recPtr := hreg5.trans hretNegEq
  have hs5_67 : s5.regs 67 = L := (hs5Keep 67 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67
  have hs5_70 : s5.regs 70 = gradient := (hs5Keep 70 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h70
  have hs5_83 : s5.regs 83 = edgeThresholds := (hs5Keep 83 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h83
  have hs5_86 : s5.regs 86 = edgeRecords := (hs5Keep 86 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h86
  let s6 := { s5 with mem := Function.update s5.mem (edgeThresholds + e) posTh }
  let s7 := { s6 with mem := Function.update s6.mem recPtr 1 }
  let s8 := { s7 with mem := Function.update s7.mem (recPtr + 1) 1 }
  let s9 := { s8 with regs := Function.update s8.regs 6 (recPtr + 2) }
  have hr6 : Runs w p ω (.store (.bin .add (.reg 83) (.reg 0)) (.reg 3)) s5 .normal s6 5 :=
    runs_store_iff.mpr ⟨edgeThresholds + e, posTh,
      by simp [Expr.eval, BinOp.eval, hs5_83, hs5_0, show edgeThresholds + e < 2 ^ w by omega],
      by simp [Expr.eval, hs5_3], rfl, rfl, rfl⟩
  have hr7 : Runs w p ω (.store (.reg 5) (.const 1)) s6 .normal s7 3 :=
    runs_store_iff.mpr ⟨recPtr, 1, by simp [Expr.eval, s6, hs5_5], by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hr8 : Runs w p ω (.store (.bin .add (.reg 5) (.const 1)) (.const 1)) s7 .normal s8 5 :=
    runs_store_iff.mpr ⟨recPtr + 1, 1,
      by simp [Expr.eval, BinOp.eval, s7, s6, hs5_5, hw1, show recPtr + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hr9 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.const 2))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨recPtr + 2,
      by simp [Expr.eval, BinOp.eval, s8, s7, s6, hs5_5, hw2, show recPtr + 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  -- Copy 1: gradient + e * L -> recPtr + 2
  have hargsC1 : evalArgs w s9 [.bin .add (.reg 70) (.reg 1), .reg 6, .reg 67] =
      some [gradient + e * L, recPtr + 2, L] := by
    simp [evalArgs, Expr.eval, BinOp.eval, s9, s8, s7, s6, hs5_70, hs5_1, hs5_67,
      show gradient + e * L < 2 ^ w by omega]
  have hpreC1 : (copyWordsContract w).pre [gradient + e * L, recPtr + 2, L] s9.mem :=
    ⟨gradient + e * L, recPtr + 2, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨s10, cC1, _, hr10, hpostC1, _, hkeep10, hcC1⟩ :=
    runs_call_of_meetsContract (st := s9) (r := 7) hcopy hargsC1
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      hpreC1 ω
  obtain ⟨_, _, _, hEqC1, _, hcopyC1, hframeC1⟩ := hpostC1
  simp only [List.cons.injEq, and_true] at hEqC1
  obtain ⟨rfl, rfl, rfl⟩ := hEqC1
  let s11 := { s10 with regs := Function.update s10.regs 6 (recPtr + 2 + L) }
  have hr11 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.reg 67))) s10 .normal s11 4 :=
    runs_assign_iff.mpr ⟨recPtr + 2 + L,
      by simp [Expr.eval, BinOp.eval, hkeep10 6 (by decide), hkeep10 67 (by decide), s9, s8, s7, s6,
        hs5_67, show recPtr + 2 + L < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Copy 2: lengths + e * L -> recPtr + 2 + L
  have hargsC2 : evalArgs w s11 [.reg 2, .reg 6, .reg 67] = some [lengths + e * L, recPtr + 2 + L, L] := by
    simp [evalArgs, Expr.eval, s11, hkeep10 2 (by decide), hkeep10 67 (by decide), s9, s8, s7, s6,
      hs5_2, hs5_67]
  have hpreC2 : (copyWordsContract w).pre [lengths + e * L, recPtr + 2 + L, L] s11.mem :=
    ⟨lengths + e * L, recPtr + 2 + L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨s12, cC2, _, hr12, hpostC2, _, hkeep12, hcC2⟩ :=
    runs_call_of_meetsContract (st := s11) (r := 7) hcopy hargsC2
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      hpreC2 ω
  obtain ⟨_, _, _, hEqC2, _, hcopyC2, hframeC2⟩ := hpostC2
  simp only [List.cons.injEq, and_true] at hEqC2
  obtain ⟨rfl, rfl, rfl⟩ := hEqC2
  let s13 := { s12 with regs := Function.update s12.regs 6 (recPtr + 2 + 3 * L) }
  have hr13 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 67)))) s12 .normal s13 6 :=
    runs_assign_iff.mpr ⟨recPtr + 2 + 3 * L,
      by simp [Expr.eval, BinOp.eval, hkeep12 6 (by decide), hkeep12 67 (by decide), s11,
        hkeep10 67 (by decide), s9, s8, s7, s6, hs5_67, hw2,
        show 2 * L < 2 ^ w by omega, show recPtr + 2 + L + 2 * L = recPtr + 2 + 3 * L by omega,
        show recPtr + 2 + 3 * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Copy 3: negTh -> recPtr + 2 + 3 * L
  have hargsC3 : evalArgs w s13 [.reg 4, .reg 6, .reg 67] = some [negTh, recPtr + 2 + 3 * L, L] := by
    simp [evalArgs, Expr.eval, s13, hkeep12 4 (by decide), hkeep12 67 (by decide), s11,
      hkeep10 4 (by decide), hkeep10 67 (by decide), s9, s8, s7, s6, hs5_4, hs5_67]
  have hpreC3 : (copyWordsContract w).pre [negTh, recPtr + 2 + 3 * L, L] s13.mem :=
    ⟨negTh, recPtr + 2 + 3 * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨s14, cC3, _, hr14, hpostC3, _, hkeep14, hcC3⟩ :=
    runs_call_of_meetsContract (st := s13) (r := 7) hcopy hargsC3
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      hpreC3 ω
  obtain ⟨_, _, _, hEqC3, _, hcopyC3, hframeC3⟩ := hpostC3
  simp only [List.cons.injEq, and_true] at hEqC3
  obtain ⟨rfl, rfl, rfl⟩ := hEqC3
  have hs14Keep (r : ℕ) (hr6 : r ≠ 6) (hr7 : r ≠ 7) : s14.regs r = s5.regs r := by
    rw [hkeep14 r hr7]
    simp only [s13, Function.update_of_ne hr6]
    rw [hkeep12 r hr7]
    simp only [s11, Function.update_of_ne hr6]
    rw [hkeep10 r hr7]
    simp [s9, s8, s7, s6, Function.update_of_ne hr6]
  let s15 := { s14 with mem := Function.update s14.mem (edgeRecords + e) recPtr }
  let out := { s15 with regs := Function.update s15.regs 99 nextCursor }
  have hr15 : Runs w p ω (.store (.bin .add (.reg 86) (.reg 0)) (.reg 5)) s14 .normal s15 5 :=
    runs_store_iff.mpr ⟨edgeRecords + e, recPtr,
      by simp [Expr.eval, BinOp.eval, hs14Keep 86 (by decide) (by decide),
        hs14Keep 0 (by decide) (by decide), hs5_86, hs5_0, show edgeRecords + e < 2 ^ w by omega],
      by simp [Expr.eval, hs14Keep 5 (by decide) (by decide), hs5_5], rfl, rfl, rfl⟩
  have hr16 : Runs w p ω (.assign 99 (.bin .add (.reg 6) (.reg 67))) s15 .normal out 4 :=
    runs_assign_iff.mpr ⟨nextCursor,
      by simp [Expr.eval, BinOp.eval, s15, hkeep14 6 (by decide), hs14Keep 67 (by decide) (by decide),
        s13, hs5_67, show recPtr + 2 + 3 * L + L = nextCursor by omega,
        show nextCursor < 2 ^ w from hroom], rfl, rfl, rfl⟩
  let totalCost := cDiv + cNeg + cC1 + cC2 + cC3 + 63
  have hrun : Runs w p ω (initSingleEdgeThresholdAndRecord divide negate copy) st .normal out totalCost := by
    unfold initSingleEdgeThresholdAndRecord
    have h15 := runs_seq_iff.mpr (Or.inr ⟨s15, 5, 4, hr15, hr16, rfl⟩)
    have h14 := runs_seq_iff.mpr (Or.inr ⟨s14, cC3, _, hr14, h15, rfl⟩)
    have h13 := runs_seq_iff.mpr (Or.inr ⟨s13, 6, _, hr13, h14, rfl⟩)
    have h12 := runs_seq_iff.mpr (Or.inr ⟨s12, cC2, _, hr12, h13, rfl⟩)
    have h11 := runs_seq_iff.mpr (Or.inr ⟨s11, 4, _, hr11, h12, rfl⟩)
    have h10 := runs_seq_iff.mpr (Or.inr ⟨s10, cC1, _, hr10, h11, rfl⟩)
    have h9 := runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, hr9, h10, rfl⟩)
    have h8 := runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, hr8, h9, rfl⟩)
    have h7 := runs_seq_iff.mpr (Or.inr ⟨s7, 3, _, hr7, h8, rfl⟩)
    have h6 := runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, hr6, h7, rfl⟩)
    have h5 := runs_seq_iff.mpr (Or.inr ⟨s5, cNeg, _, hr5, h6, rfl⟩)
    have h4 := runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, hr4, h5, rfl⟩)
    have h3 := runs_seq_iff.mpr (Or.inr ⟨s3, cDiv, _, hr3, h4, rfl⟩)
    have h2 := runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, hr2, h3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, hr1, h2, by dsimp only [totalCost]; omega⟩)
  -- Memory helper: `s14.mem` agrees with `s5.mem` below `recPtr` outside `edgeThresholds + e`
  have hs14Below (a : ℕ) (ha : a < recPtr) (hne : a ≠ edgeThresholds + e) : s14.mem a = s5.mem a := by
    rw [hframeC3 a (Or.inl (by omega)), hframeC2 a (Or.inl (by omega)),
      hframeC1 a (Or.inl (by omega))]
    simp only [s9, s8, s7, s6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne hne]
  have houtBelow (a : ℕ) (ha : a < cursor) (h1 : a ≠ edgeThresholds + e) (h2 : a ≠ edgeRecords + e) :
      out.mem a = st.mem a := by
    simp only [out, s15]
    rw [Function.update_of_ne h2, hs14Below a (by omega) h1,
      hframeNeg a (by omega), hframeDiv a ha]
  have hposThOut : PathIntAt out.mem posTh 4 L th :=
    hposThAt5.congr (fun j hj => by
      simp only [out, s15]
      rw [Function.update_of_ne (by omega), hs14Below _ (by omega) (by omega)])
  have hrecOut : PathEdgeAt out.mem recPtr 4 L (some (initialPathEdgeValue P ε gradInt lenInt)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [out, s15]
      rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)),
        hframeC2 _ (Or.inl (by omega)), hframeC1 _ (Or.inl (by omega))]
      simp [s9, s8, s7]
    · simp only [out, s15]
      rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)),
        hframeC2 _ (Or.inl (by omega)), hframeC1 _ (Or.inl (by omega))]
      simp [s9, s8, initialPathEdgeValue]
    · exact hgradAt.congr (fun j hj => by
        simp only [out, s15]
        rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)),
          hframeC2 _ (Or.inl (by omega)), hcopyC1 j hj]
        simp only [s9, s8, s7, s6]
        have hgt : gradient + e * L + j < cursor := by omega
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (hgradNeTh j hj)]
        exact (hframeNeg _ (by omega)).trans (hframeDiv _ hgt))
    · exact hlenAt.congr (fun j hj => by
        simp only [out, s15]
        rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)), hcopyC2 j hj]
        simp only [s11]
        have hlt : lengths + e * L + j < cursor := by omega
        rw [hframeC1 _ (Or.inl (by omega))]
        simp only [s9, s8, s7, s6]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (hlenNeTh j hj)]
        exact (hframeNeg _ (by omega)).trans (hframeDiv _ hlt))
    · refine ⟨fun j hj => ?_, ?_⟩
      · have hzFlow : out.mem (recPtr + 2 + 2 * L + j) = 0 := by
          simp only [out, s15]
          rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)),
            hframeC2 _ (Or.inr (by omega)), hframeC1 _ (Or.inr (by omega))]
          simp only [s9, s8, s7, s6]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hz5' _ (by omega)
        rw [hzFlow]; decide
      · apply Num.intVal_zero
        intro j hj
        simp only [out, s15]
        rw [Function.update_of_ne (by omega), hframeC3 _ (Or.inl (by omega)),
          hframeC2 _ (Or.inr (by omega)), hframeC1 _ (Or.inr (by omega))]
        simp only [s9, s8, s7, s6]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hz5' _ (by omega)
    · exact hnegThAt'.congr (fun j hj => by
        simp only [out, s15]
        rw [Function.update_of_ne (by omega), hcopyC3 j hj]
        simp only [s13]
        rw [hframeC2 _ (Or.inl (by omega)), hframeC1 _ (Or.inl (by omega))]
        simp only [s9, s8, s7, s6]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), hframeNeg _ (by omega)])
  have hzOut : ZeroFrom out.mem nextCursor := by
    intro a ha
    simp only [out, s15]
    rw [Function.update_of_ne (by omega), hframeC3 a (Or.inr (by omega)),
      hframeC2 a (Or.inr (by omega)), hframeC1 a (Or.inr (by omega))]
    simp only [s9, s8, s7, s6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hz5' a (by omega)
  refine ⟨out, totalCost, hrun, by simp [out]; rfl, ?_, by simp [out, s15]; rfl, hposThOut, hrecOut, hzOut,
    houtBelow, ?_, ?_, ?_⟩
  · simp only [out, s15]
    rw [Function.update_of_ne hdisjTR, hframeC3 _ (Or.inl (by omega)),
      hframeC2 _ (Or.inl (by omega)), hframeC1 _ (Or.inl (by omega))]
    simp only [s9, s8, s7, s6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · intro r hr8 hr99
    simp only [out, s15, Function.update_of_ne hr99]
    rw [hs14Keep r (by omega) (by omega)]
    exact hs5Keep r (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [out, s15, Function.update_of_ne (by decide : 0 ≠ 99)]
    exact (hs14Keep 0 (by decide) (by decide)).trans hs5_0
  · simp only [detectorResidualContract, Num.negateContract, copyWordsContract, argsSize, Expr.size,
      List.getD_cons_zero, List.getD_cons_succ] at hcDiv hcNeg hcC1 hcC2 hcC3
    dsimp only [totalCost]
    omega

/-- Build `-ε`, then populate the per-edge Detect threshold table and initial
`PathEdgeAt` record table for every edge `e < m`. -/
@[expose] def initDetectThresholdsAndRecords (shift divide negate copy : ℕ) : Stmt :=
  initNegEpsilonBlock shift negate ;;
  forRange 0 (.const 0) (.reg 84) (initSingleEdgeThresholdAndRecord divide negate copy)

theorem initDetectThresholdsAndRecords_noRand (shift divide negate copy : ℕ) :
    (initDetectThresholdsAndRecords shift divide negate copy).NoRand := by
  simp [initDetectThresholdsAndRecords, initNegEpsilonBlock_noRand,
    initSingleEdgeThresholdAndRecord_noRand, forRange, forUp, Stmt.NoRand]

/-- Populate the initial Detect threshold pointer table `edgeThresholds[0..m)`
and initial `PathEdgeAt` record pointer table `edgeRecords[0..m)` from the input
gradient and length vectors, in `O(m * L^2)` steps. -/
theorem initDetectThresholdsAndRecords_runs
    {w shift divide negate copy m L P epsExp gradient lengths edgeThresholds edgeRecords heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (lenInt : ℕ → ℕ) (gradInt : ℕ → ℤ)
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = P)
    (h70 : st.regs 70 = gradient) (h71 : st.regs 71 = lengths)
    (h73 : st.regs 73 = epsExp) (h83 : st.regs 83 = edgeThresholds)
    (h84 : st.regs 84 = m) (h86 : st.regs 86 = edgeRecords) (h99 : st.regs 99 = heap)
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L)
    (hle : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hlenEnd : lengths + m * L ≤ heap) (hgradEnd : gradient + m * L ≤ heap)
    (hthBelow : edgeThresholds + m ≤ heap) (hrecBelow : edgeRecords + m ≤ heap)
    (hdisjTR : edgeThresholds + m ≤ edgeRecords ∨ edgeRecords + m ≤ edgeThresholds)
    (hdisjLenTh : lengths + m * L ≤ edgeThresholds ∨ edgeThresholds + m ≤ lengths)
    (hdisjLenRec : lengths + m * L ≤ edgeRecords ∨ edgeRecords + m ≤ lengths)
    (hdisjGradTh : gradient + m * L ≤ edgeThresholds ∨ edgeThresholds + m ≤ gradient)
    (hdisjGradRec : gradient + m * L ≤ edgeRecords ∨ edgeRecords + m ≤ gradient)
    (hlenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt st.mem (lengths + e * L) 4 L (lenInt e))
    (hgradAt : ∀ e < m, PathIntAt st.mem (gradient + e * L) 4 L (gradInt e))
    (hfits : ∀ e < m,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
      Num.Fits 4 L (-th) ∧ Num.Fits 4 L th)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + 3 * L + m * initEdgeRecordSpace L < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
    let finalCursor := heap + 3 * L + m * initEdgeRecordSpace L
    ∃ out cost, Runs w p ω (initDetectThresholdsAndRecords shift divide negate copy) st .normal out cost ∧
      out.regs 99 = finalCursor ∧
      (∀ e < m,
        let base := heap + 3 * L + e * initEdgeRecordSpace L
        let posTh := base + Num.fixedDivideSpace L
        let recPtr := posTh + L
        out.mem (edgeThresholds + e) = posTh ∧
        out.mem (edgeRecords + e) = recPtr ∧
        PathIntAt out.mem posTh 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt out.mem recPtr 4 L (some (initialPathEdgeValue P ε (gradInt e) (lenInt e)))) ∧
      ZeroFrom out.mem finalCursor ∧
      (∀ a < heap, (a < edgeThresholds ∨ edgeThresholds + m ≤ a) →
        (a < edgeRecords ∨ edgeRecords + m ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, 8 ≤ r → r ≠ 95 → r ≠ 99 → out.regs r = st.regs r) ∧
      cost ≤ m * (2700 * L ^ 2 + 2920 * L + 869) + 71 * L + 84 := by
  dsimp only
  let epsInt : ℤ := (2 : ℤ) ^ (P - epsExp)
  let ε : ℝ := (epsInt : ℝ) / (2 : ℝ) ^ P
  have hepsPos : 0 < ε := by
    unfold ε epsInt
    positivity
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨mid, cEps, hrEps, h95M, h99M, hnegEpsM, hzM, hframeM, hregsM, hcEps⟩ :=
    initNegEpsilonBlock_runs (ω := ω) hshift hneg h67 h68 h73 h99 hLpos hPword hle hfitEps hz
      (by omega) hw1
  have hmW : m < 2 ^ w := by
    have : 2 ≤ initEdgeRecordSpace L := by unfold initEdgeRecordSpace; omega
    have : m * 2 ≤ m * initEdgeRecordSpace L := Nat.mul_le_mul_left m this
    omega
  let Inv (i : ℕ) (s : State) : Prop :=
    s.regs 0 = i ∧ s.regs 95 = heap + 2 * L ∧
    s.regs 99 = heap + 3 * L + i * initEdgeRecordSpace L ∧
    (∀ r, 8 ≤ r → r ≠ 95 → r ≠ 99 → s.regs r = st.regs r) ∧
    PathIntAt s.mem (heap + 2 * L) 4 L (-epsInt) ∧
    ZeroFrom s.mem (heap + 3 * L + i * initEdgeRecordSpace L) ∧
    (∀ e < i,
      let base := heap + 3 * L + e * initEdgeRecordSpace L
      let posTh := base + Num.fixedDivideSpace L
      let recPtr := posTh + L
      s.mem (edgeThresholds + e) = posTh ∧
      s.mem (edgeRecords + e) = recPtr ∧
      PathIntAt s.mem posTh 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
      PathEdgeAt s.mem recPtr 4 L (some (initialPathEdgeValue P ε (gradInt e) (lenInt e)))) ∧
    (∀ a < heap, (a < edgeThresholds ∨ edgeThresholds + i ≤ a) →
      (a < edgeRecords ∨ edgeRecords + i ≤ a) → s.mem a = st.mem a)
  let stepCost := 2700 * L ^ 2 + 2920 * L + 860
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 0) (lo := .const 0) (hi := .reg 84)
    (P := fun s => s = mid) (Inv := Inv) (fun _ => stepCost) 0 m (Nat.zero_le m) hw1 (fun _ => hmW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        rfl, by simpa using h95M, by simpa using h99M,
        fun r hr8 h95 h99 => by
          simp only [Function.update_of_ne (show r ≠ 0 by omega)]
          exact hregsM r (by omega) (by omega) h95 h99,
        hnegEpsM, by simpa using hzM, fun _ h => absurd h (Nat.not_lt_zero _),
        fun a ha _ _ => hframeM a ha⟩)
    (fun _ _ _ _ hs => hs.1)
    (fun _ s _ _ hs => by simp [Expr.eval, (hs.2.2.2.1 84 (by decide) (by decide) (by decide)).trans h84])
    (fun i _ hi => by
      intro s ω' hs
      obtain ⟨h0s, h95s, h99s, hregss, hnegEpss, hzs, hdone, hframes⟩ := hs
      have hmul : (i + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hmul
      have hcurLe : heap + 3 * L + (i + 1) * initEdgeRecordSpace L ≤ heap + 3 * L + m * initEdgeRecordSpace L :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)) _
      rw [Nat.succ_mul] at hcurLe
      have hlenS : PathIntAt s.mem (lengths + i * L) 4 L (lenInt i) :=
        (hlenAt i hi).2.congr (fun j hj => hframes _ (by omega) (by rcases hdisjLenTh with h | h <;> omega)
          (by rcases hdisjLenRec with h | h <;> omega))
      have hgradS : PathIntAt s.mem (gradient + i * L) 4 L (gradInt i) :=
        (hgradAt i hi).congr (fun j hj => hframes _ (by omega) (by rcases hdisjGradTh with h | h <;> omega)
          (by rcases hdisjGradRec with h | h <;> omega))
      have hfitNegI : Num.Fits 4 L (-detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
          ((lenInt i : ℝ) / (2 : ℝ) ^ P)) := by
        simpa only [epsInt, Int.cast_pow, Int.cast_ofNat] using (hfits i hi).1
      have hfitPosI : Num.Fits 4 L (detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
          ((lenInt i : ℝ) / (2 : ℝ) ^ P)) := by
        simpa only [epsInt, Int.cast_pow, Int.cast_ofNat] using (hfits i hi).2
      have hroomI : heap + 3 * L + i * initEdgeRecordSpace L + initEdgeRecordSpace L < 2 ^ w := by
        have h1 : heap + 3 * L + i * initEdgeRecordSpace L + initEdgeRecordSpace L =
            heap + 3 * L + (i + 1) * initEdgeRecordSpace L := by ring
        omega
      obtain ⟨after, cStep, hrStep, h99a, hthA, hrecA, hposThA, hrecValA, hza, hframeA,
          hregsA, h0a, hcStep⟩ :=
        initSingleEdgeThresholdAndRecord_runs (ω := ω') (st := s) epsInt (lenInt i) (gradInt i)
          hdiv hneg hcopy h0s
          ((hregss 67 (by decide) (by decide) (by decide)).trans h67)
          ((hregss 68 (by decide) (by decide) (by decide)).trans h68)
          ((hregss 70 (by decide) (by decide) (by decide)).trans h70)
          ((hregss 71 (by decide) (by decide) (by decide)).trans h71)
          ((hregss 83 (by decide) (by decide) (by decide)).trans h83)
          ((hregss 86 (by decide) (by decide) (by decide)).trans h86)
          h95s h99s hPdiv hPword hLpos (hlenAt i hi).1
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by rcases hdisjTR with h | h <;> omega)
          (fun j hj => by rcases hdisjGradTh with h | h <;> omega)
          (fun j hj => by rcases hdisjLenTh with h | h <;> omega)
          hnegEpss hlenS hgradS hepsPos hfitNegI hfitPosI hzs hroomI hw2
      have hcurNext : heap + 3 * L + i * initEdgeRecordSpace L + initEdgeRecordSpace L =
          heap + 3 * L + (i + 1) * initEdgeRecordSpace L := by ring
      refine ⟨.normal, after, cStep, hrStep, ⟨⟨by simp,
        by simp only [Function.update_of_ne (by decide : 95 ≠ 0)]; exact (hregsA 95 (by decide) (by decide)).trans h95s,
        by simp only [Function.update_of_ne (by decide : 99 ≠ 0)]; exact h99a.trans hcurNext,
        fun r hr8 h95 h99 => by
          simp only [Function.update_of_ne (show r ≠ 0 by omega)]
          exact (hregsA r hr8 h99).trans (hregss r hr8 h95 h99),
        hnegEpss.congr (fun j hj => hframeA _ (by omega) (by omega) (by omega)),
        hcurNext ▸ hza, ?_, ?_⟩, h0a⟩, hcStep⟩
      · intro e he
        by_cases hei : e = i
        · subst hei; exact ⟨hthA, hrecA, hposThA, hrecValA⟩
        · have he' : e < i := by omega
          obtain ⟨hthe, hrece, hpthe, hrve⟩ := hdone e he'
          have hbaseLe : heap + 3 * L + e * initEdgeRecordSpace L + initEdgeRecordSpace L ≤
              heap + 3 * L + i * initEdgeRecordSpace L := by
            have h1 := Nat.add_le_add_left (Nat.mul_le_mul_right (initEdgeRecordSpace L) (show e + 1 ≤ i by omega)) (heap + 3 * L)
            have h2 : heap + 3 * L + e * initEdgeRecordSpace L + initEdgeRecordSpace L =
                heap + 3 * L + (e + 1) * initEdgeRecordSpace L := by ring
            omega
          have hrecEnd : Num.fixedDivideSpace L + L + 2 + 4 * L = initEdgeRecordSpace L := by
            unfold initEdgeRecordSpace; omega
          refine ⟨(hframeA _ (by omega) (by omega) (by rcases hdisjTR with h | h <;> omega)).trans hthe,
            (hframeA _ (by omega) (by rcases hdisjTR with h | h <;> omega) (by omega)).trans hrece,
            hpthe.congr (fun j hj => hframeA _ (by omega) (by omega) (by omega)),
            hrve.congr (fun a hlo hhi => hframeA a (by omega) (by omega) (by omega))⟩
      · intro a ha hthOut hrecOut
        exact (hframeA a (by omega) (by omega) (by omega)).trans (hframes a ha (by omega) (by omega)))
  obtain ⟨o, out, cLoop, hrLoop, hout, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    have hrc : rangeCost (fun _ => stepCost) 0 m = m * stepCost := by
      simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    refine ⟨out, cEps + cLoop + 1,
      runs_seq_iff.mpr (Or.inr ⟨mid, cEps, cLoop, hrEps, hrLoop, rfl⟩),
      hout.2.2.1,
      by simpa only [ε, epsInt, Int.cast_pow, Int.cast_ofNat] using hout.2.2.2.2.2.2.1,
      hout.2.2.2.2.2.1, hout.2.2.2.2.2.2.2,
      hout.2.2.2.1, ?_⟩
    have hmulStep : m * stepCost + m * 9 = m * (2700 * L ^ 2 + 2920 * L + 869) := by
      dsimp only [stepCost]; ring
    omega

end MinCostFlow.MinRatio
