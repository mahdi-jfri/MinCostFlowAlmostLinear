module

public import MinCostFlow.MinRatio.InitThresholdLogProduct

/-!
# Affine constant in the second rebuild growth term

Allocate and shift the constant, then add it to the product at the same
fractional precision.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Encode the constant term before shifting it to the product precision. -/
@[expose] def loadSparseCoreSecondConstant (load : ℕ) : Stmt :=
  .call 114 load [.const 1265, .reg 118, .reg 115]

/-- The constant block preserves the previously allocated growth product. -/
theorem loadSparseCoreSecondConstant_runs
    {w h load heap limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (h115 : st.regs 115 = heap) (h118 : st.regs 118 = limbs)
    (hword : 1265 < 2 ^ w) (hroom : heap + limbs < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hfit : 2 * 1265 < Num.capacity h limbs) :
    ∃ out cost, Runs w p ω (loadSparseCoreSecondConstant load) st .normal out cost ∧
      out.regs 114 = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = (1265 : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ 114 → out.regs r = st.regs r) ∧ cost ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.const 1265, .reg 118, .reg 115] = some [1265, limbs, heap] := by
    simp [evalArgs, Expr.eval, hword, h118, h115]
  have hpre : (Num.loadSmallContract w h).pre [1265, limbs, heap] st.mem :=
    ⟨⟨1265, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 114) hload hargs (by wram_words) hpre ω
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.digits h limbs 1265) at hp
  obtain ⟨heq, _, _, hframe, hzero, hdigits⟩ := hp
  obtain ⟨hvalid, hu, _⟩ := Num.loadSmall_value hdigits
  have hsmall : 1265 < Num.capacity h limbs := by omega
  have hi : Num.intVal out.mem heap h limbs = (1265 : ℤ) := by
    rw [Num.intVal, hu, Nat.mod_eq_of_lt hsmall, Num.signedVal, ite_eq_right (not_le_of_gt hfit), sub_zero]
    rfl
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hi, hframe, heq ▸ hzero, hf, by simp [Num.loadSmallContract, heapContract, argsSize, Expr.size] at hc; omega⟩

/-- Allocate and scale the affine constant to the precision of the
second growth product. -/
@[expose] def scaleSparseCoreSecondConstant (load shift : ℕ) : Stmt :=
  loadSparseCoreSecondConstant load ;;
  shiftRebuildGrowth shift 115 118 121 114 116

/-- The shifted constant occupies the next block after its unscaled
encoding. Both allocations preserve the product. -/
theorem scaleSparseCoreSecondConstant_runs
    {w h load shift heap limbs P : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (h115 : st.regs 115 = heap) (h118 : st.regs 118 = limbs) (h121 : st.regs 121 = P)
    (hw : 1265 < 2 ^ w) (hP : P < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 2 * limbs < 2 ^ w) (hfit : 2 * 1265 < Num.capacity h limbs)
    (hshiftFit : Num.Fits h limbs (1265 * (2 : ℤ) ^ P)) :
    ∃ out cost, Runs w p ω (scaleSparseCoreSecondConstant load shift) st .normal out cost ∧
      out.regs 116 = heap + 2 * limbs ∧ out.regs 114 = heap + limbs ∧ Num.Valid out.mem (heap + limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs) h limbs = 1265 * (2 : ℤ) ^ P ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 2 * limbs) ∧
      (∀ r, r ≠ 114 → r ≠ 116 → out.regs r = st.regs r) ∧ cost ≤ 58 * limbs + 51 := by
  obtain ⟨mid, c, hr, h114, hv, hi, hf, hz', hk, hc⟩ :=
    loadSparseCoreSecondConstant_runs (ω := ω) hload h115 h118 hw (by omega) hz hfit
  obtain ⟨out, d, ht, h116, hv', hi', hf', hz'', hk', hd⟩ :=
    shiftRebuildGrowth_runs (ω := ω) hshift ((hk 115 (by decide)).trans h115)
      ((hk 118 (by decide)).trans h118) ((hk 121 (by decide)).trans h121) h114
      hP le_rfl hv hz' (by omega) (hi.symm ▸ hshiftFit)
  have he : heap + limbs + limbs = heap + 2 * limbs := by omega
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h116.trans he, (hk' 114 (by decide)).trans h114, hv', hi'.trans (congrArg (· * (2 : ℤ) ^ P) hi),
    fun x hx => (hf' x (by omega)).trans (hf x hx), he ▸ hz'',
    fun r hr hs => (hk' r hs).trans (hk r hr), by omega⟩

/-- Add the scaled constant to the product. The result starts at the
incoming cursor in register 116. -/
@[expose] def addSparseCoreSecondConstant (add : ℕ) : Stmt :=
  .call 115 add [.reg 117, .reg 114, .reg 118, .reg 116]

/-- The affine numerator is exact when its signed sum fits. -/
theorem addSparseCoreSecondConstant_runs
    {w h add product constant limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h117 : st.regs 117 = product) (h114 : st.regs 114 = constant)
    (h118 : st.regs 118 = limbs) (h116 : st.regs 116 = heap)
    (hp : product + limbs ≤ heap) (hc : constant + limbs ≤ heap)
    (hvp : Num.Valid st.mem product h limbs) (hvc : Num.Valid st.mem constant h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs < 2 ^ w)
    (hfit : Num.Fits h limbs
      (Num.intVal st.mem product h limbs + Num.intVal st.mem constant h limbs)) :
    ∃ out cost, Runs w p ω (addSparseCoreSecondConstant add) st .normal out cost ∧
      out.regs 115 = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs =
        Num.intVal st.mem product h limbs + Num.intVal st.mem constant h limbs ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r ≠ 115, out.regs r = st.regs r) ∧ cost ≤ 38 * limbs + 20 := by
  let args := [product, constant, limbs, heap]
  have he : evalArgs w st [.reg 117, .reg 114, .reg 118, .reg 116] = some args := by
    simp [evalArgs, Expr.eval, h117, h114, h118, h116, args]
  have hpre : (Num.addContract w h).pre args st.mem :=
    ⟨product, constant, limbs, heap, rfl,
      ⟨⟨product, constant, limbs, 0, heap, rfl, hp, hc, by decide, hvp, hvc⟩, hz, hroom⟩⟩
  obtain ⟨out, cost, ret, hr, hpost, hret, hkeep, hcost⟩ :=
    runs_call_of_meetsContract (r := 115) hadd he (by dsimp [args]; wram_words) hpre ω
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.digits h limbs
      (Num.unsignedVal st.mem product h limbs + Num.unsignedVal st.mem constant h limbs + 0)) at hpost
  obtain ⟨hret', _, _, hf, hzero, hdigits⟩ := hpost
  obtain ⟨hv, hval⟩ := Num.addCarry_value hdigits
  simp only [Int.natCast_zero, add_zero, Num.wrap_of_fits hfit] at hval
  refine ⟨out, cost, hr, hret.trans hret', hv, hval, hf, hret' ▸ hzero, hkeep, ?_⟩
  simp [Num.addContract, args, argsSize, Expr.size] at hcost
  omega

/-- Recover the product address from the cursor returned by multiplication.
The width is twice the common width used by that call. -/
@[expose] def stageSparseCoreSecondProduct : Stmt :=
  .assign 118 (.bin .add (.reg 111) (.reg 111)) ;;
  .assign 117 (.bin .sub (.reg 115) (.reg 118))

/-- Staging leaves the product precision and all allocated blocks intact. -/
theorem stageSparseCoreSecondProduct_runs
    {w width heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h111 : st.regs 111 = width) (h115 : st.regs 115 = heap)
    (hle : width + width ≤ heap) (hroom : heap < 2 ^ w) :
    ∃ out, Runs w p ω stageSparseCoreSecondProduct st .normal out 9 ∧
      out.regs 118 = width + width ∧ out.regs 117 = heap - (width + width) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 117 → r ≠ 118 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 118 (width + width)}
  let out := {mid with regs := Function.update mid.regs 117 (heap - (width + width))}
  have hwidth : width + width < 2 ^ w := hle.trans_lt hroom
  have haddr : heap - (width + width) < 2 ^ w := (Nat.sub_le ..).trans_lt hroom
  have hr : Runs w p ω (.assign 118 (.bin .add (.reg 111) (.reg 111))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h111, hwidth], rfl, rfl, rfl⟩
  have ht : Runs w p ω (.assign 117 (.bin .sub (.reg 115) (.reg 118))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h115, haddr], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hr, ht, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r hr₁ hr₂ => by simp [out, mid, hr₁, hr₂]⟩

/-- Add the affine constant and pass the sum block to the rounding routine. -/
@[expose] def finishSparseCoreSecondGrowth (load shift add : ℕ) : Stmt :=
  scaleSparseCoreSecondConstant load shift ;;
  addSparseCoreSecondConstant add ;;
  .assign 117 (.reg 116)

/-- The affine sum occupies a fresh block at the original precision. -/
theorem finishSparseCoreSecondGrowth_runs
    {w h load shift add heap product limbs P : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h115 : st.regs 115 = heap) (h118 : st.regs 118 = limbs) (h121 : st.regs 121 = P)
    (h117 : st.regs 117 = product) (hbelow : product + limbs ≤ heap)
    (hv : Num.Valid st.mem product h limbs)
    (hw : 1265 < 2 ^ w) (hP : P < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 3 * limbs < 2 ^ w) (hfit : 2 * 1265 < Num.capacity h limbs)
    (hshiftFit : Num.Fits h limbs (1265 * (2 : ℤ) ^ P))
    (hsumFit : Num.Fits h limbs (Num.intVal st.mem product h limbs + 1265 * (2 : ℤ) ^ P)) :
    ∃ out cost, Runs w p ω (finishSparseCoreSecondGrowth load shift add) st .normal out cost ∧
      out.regs 117 = heap + 2 * limbs ∧ out.regs 115 = heap + 3 * limbs ∧
      Num.Valid out.mem (heap + 2 * limbs) h limbs ∧
      Num.intVal out.mem (heap + 2 * limbs) h limbs =
        Num.intVal st.mem product h limbs + 1265 * (2 : ℤ) ^ P ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 3 * limbs) ∧
      (∀ r, r ≠ 114 → r ≠ 115 → r ≠ 116 → r ≠ 117 → out.regs r = st.regs r) ∧
      cost ≤ 96 * limbs + 75 := by
  obtain ⟨mid, c, hr, h116, hcAddr, hcValid, hcValue, hf, hz', hk, hc⟩ :=
    scaleSparseCoreSecondConstant_runs (ω := ω) hload hshift h115 h118 h121 hw hP hz
      (by omega) hfit hshiftFit
  have hpValid : Num.Valid mid.mem product h limbs := by
    intro j hj
    rw [hf _ (by omega)]
    exact hv j hj
  have hpValue : Num.intVal mid.mem product h limbs = Num.intVal st.mem product h limbs :=
    Num.intVal_congr (fun j hj => hf _ (by omega))
  obtain ⟨ready, d, ht, hout, hv', hi, hf', hz'', hk', hd⟩ :=
    addSparseCoreSecondConstant_runs (ω := ω) hadd ((hk 117 (by decide) (by decide)).trans h117)
      hcAddr ((hk 118 (by decide) (by decide)).trans h118) h116
      (by omega) (by omega) hpValid hcValid hz' (by omega) (by rwa [hpValue, hcValue])
  let out := {ready with regs := Function.update ready.regs 117 (heap + 2 * limbs)}
  have hu : Runs w p ω (.assign 117 (.reg 116)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some ((hk' 116 (by decide)).trans h116), rfl, rfl, rfl⟩
  have he : heap + 2 * limbs + limbs = heap + 3 * limbs := by omega
  refine ⟨out, c + d + 4, ?_, by simp [out], ?_, hv', hi.trans (by rw [hpValue, hcValue]),
    fun x hx => (hf' x (by omega)).trans (hf x hx), he ▸ hz'', ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, d, 2, ht, hu, rfl⟩), by omega⟩)
  · simpa [out] using hout.trans he
  · intro r h114r h115r h116r h117r
    simpa [out, h117r] using (hk' r h115r).trans (hk r h114r h116r)

/-- Stage the multiplication result and complete the affine numerator. -/
@[expose] def completeSparseCoreSecondGrowth (load shift add : ℕ) : Stmt :=
  stageSparseCoreSecondProduct ;; finishSparseCoreSecondGrowth load shift add

/-- The multiplication cursor determines the product's address and
the fresh storage for its affine correction. -/
theorem completeSparseCoreSecondGrowth_runs
    {w h load shift add heap width P : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h115 : st.regs 115 = heap) (h111 : st.regs 111 = width) (h121 : st.regs 121 = P)
    (hle : width + width ≤ heap)
    (hv : Num.Valid st.mem (heap - (width + width)) h (width + width))
    (hw : 1265 < 2 ^ w) (hP : P < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 3 * (width + width) < 2 ^ w)
    (hfit : 2 * 1265 < Num.capacity h (width + width))
    (hshiftFit : Num.Fits h (width + width) (1265 * (2 : ℤ) ^ P))
    (hsumFit : Num.Fits h (width + width)
      (Num.intVal st.mem (heap - (width + width)) h (width + width) + 1265 * (2 : ℤ) ^ P)) :
    ∃ out cost, Runs w p ω (completeSparseCoreSecondGrowth load shift add) st .normal out cost ∧
      out.regs 117 = heap + 2 * (width + width) ∧
      out.regs 115 = heap + 3 * (width + width) ∧ out.regs 118 = width + width ∧
      Num.Valid out.mem (heap + 2 * (width + width)) h (width + width) ∧
      Num.intVal out.mem (heap + 2 * (width + width)) h (width + width) =
        Num.intVal st.mem (heap - (width + width)) h (width + width) + 1265 * (2 : ℤ) ^ P ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 3 * (width + width)) ∧
      (∀ r, r ≠ 114 → r ≠ 115 → r ≠ 116 → r ≠ 117 → r ≠ 118 → out.regs r = st.regs r) ∧
      cost ≤ 96 * (width + width) + 85 := by
  obtain ⟨mid, hr, h118, h117, hm, hk⟩ :=
    stageSparseCoreSecondProduct_runs (w := w) (p := p) (ω := ω) h111 h115 hle (by omega)
  obtain ⟨out, c, ht, ha, hc, hv', hi, hf, hz', hk', hcost⟩ :=
    finishSparseCoreSecondGrowth_runs (ω := ω) hload hshift hadd
      ((hk 115 (by decide) (by decide)).trans h115) h118
      ((hk 121 (by decide) (by decide)).trans h121) h117 (by omega)
      (hm.symm ▸ hv) hw hP (hm.symm ▸ hz) hroom hfit hshiftFit (hm.symm ▸ hsumFit)
  exact ⟨out, 9 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 9, c, hr, ht, rfl⟩),
    ha, hc, (hk' 118 (by decide) (by decide) (by decide) (by decide)).trans h118,
    hv', hi.trans (by rw [hm]), fun x hx => (hf x hx).trans (congrFun hm x), hz',
    fun r h114 h115r h116 h117r h118r =>
      (hk' r h114 h115r h116 h117r).trans (hk r h117r h118r), by omega⟩

end MinCostFlow.MinRatio
