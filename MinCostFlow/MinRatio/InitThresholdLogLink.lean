module

public import MinCostFlow.MinRatio.InitDepthLink
import MinCostFlow.Num.WordBounds

/-!
# Integer rebuild thresholds from the sparse-core logarithm

The logarithm supplies the sparsity factor and the fresh table cursor.
The integer writer uses the same scale and heap to form the level counts.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Including the sparse-core logarithm allowance gives enough bits for
both that logarithm and the coefficient's log-two calculation. -/
theorem rebuildWorkingBits_logAccuracy (L cap coarse err bound input : ℕ)
    (hc : 0 < cap) (hs : 0 < coarse) (hb : 0 < bound) :
    max 16 ((input + 2).size + 11) ≤
      growthWorkingBits L cap coarse (max err (4096 * (input + 2))) bound := by
  let n := input + 2
  let allowance := max err (4096 * n)
  let bits := growthWorkingBits L cap coarse allowance bound
  have hsize : 0 < n.size := by
    have hn := Nat.lt_size_self n
    by_contra! h
    rw [show n.size = 0 by omega, pow_zero] at hn
    dsimp [n] at hn
    omega
  have hlow : 2 ^ (n.size - 1) ≤ n := by
    by_contra! h
    have hsmall := Nat.size_le.mpr h
    omega
  have hlarge : 2 ^ 17 * n ≤ 2 ^ bits := by
    have hbase : 2 ^ 17 * n ≤ 33 * (4096 * n) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right n (by decide)
    have hallow : 4096 * n ≤ allowance := le_max_right _ _
    calc
      _ ≤ 33 * (4096 * n) := hbase
      _ ≤ 33 * allowance := Nat.mul_le_mul_left _ hallow
      _ ≤ 33 * cap * (allowance * bound ^ 2) :=
        Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hc)
          (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb))
      _ ≤ 33 * cap * (allowance * bound ^ 2) * coarse := Nat.le_mul_of_pos_right _ hs
      _ ≤ _ := (growthWorkingBits_bounds L cap coarse allowance bound).2.2
  apply max_le
  · have hf : 2 ^ 16 ≤ 2 ^ bits :=
      (Nat.pow_le_pow_right (by decide) (by decide : 16 ≤ 17)).trans
        ((Nat.le_mul_of_pos_right _ (by dsimp [n]; omega)).trans hlarge)
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hf
  · have hf : 2 ^ (n.size + 11) ≤ 2 ^ bits := by
      calc
        _ ≤ 2 ^ (17 + (n.size - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ 17 * 2 ^ (n.size - 1) := by rw [pow_add]
        _ ≤ 2 ^ 17 * n := Nat.mul_le_mul_left _ hlow
        _ ≤ _ := hlarge
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hf

/-- Round the stretch precision up to a limb boundary and materialize
the scale. Register 127 holds the bit length of the logarithm input. -/
@[expose] def stageRebuildLogWorkspace (radixBits : ℕ) : Stmt :=
  .assign 68 (.bin .mul
    (.bin .div (.bin .add (.reg 37) (.const (radixBits - 1))) (.const radixBits))
    (.const radixBits)) ;;
  .assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4)) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 68))

/-- Alignment increases the requested precision by fewer than one limb.
The workspace leaves room for the integer part and the logarithm guard bits. -/
theorem stageRebuildLogWorkspace_runs
    {w radixBits bits range : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : 0 < radixBits) (hrw : radixBits < 2 ^ w)
    (h37 : st.regs 37 = bits) (h127 : st.regs 127 = range)
    (htop : bits + (radixBits - 1) < 2 ^ w) :
    let precision := (bits + (radixBits - 1)) / radixBits * radixBits
    let limbs := precision + range + 4
    limbs < 2 ^ w → 2 ^ precision < 2 ^ w →
    ∃ out, Runs w p ω (stageRebuildLogWorkspace radixBits) st .normal out 20 ∧
      out.regs 68 = precision ∧ out.regs 67 = limbs ∧ out.regs 4 = 2 ^ precision ∧
      bits ≤ precision ∧ precision < bits + radixBits ∧ radixBits ∣ precision ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 4 → r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) := by
  dsimp only
  intro hlimbs hscale
  let top := bits + (radixBits - 1)
  let q := top / radixBits
  let prec := q * radixBits
  let limbs := prec + range + 4
  have hp : prec ≤ top := Nat.div_mul_le_self _ _
  have hm := Nat.mod_lt top hr
  have he := Nat.mod_add_div top radixBits
  rw [Nat.mul_comm radixBits] at he
  have he' : top % radixBits + prec = top := he
  have hlow : bits ≤ prec := by change top % radixBits + prec = bits + (radixBits - 1) at he'; omega
  have hhigh : prec < bits + radixBits := by dsimp [top] at hp; omega
  have hq : q < 2 ^ w := (Nat.div_le_self _ _).trans_lt htop
  have hprec : prec < 2 ^ w := hp.trans_lt htop
  have hlimbs' : limbs < 2 ^ w := hlimbs
  have hword : 4 < 2 ^ w := by omega
  have hpart : prec + range < 2 ^ w := by omega
  have hsub : radixBits - 1 < 2 ^ w := (Nat.sub_le _ _).trans_lt hrw
  let s₁ := {st with regs := Function.update st.regs 68 prec}
  let s₂ := {s₁ with regs := Function.update s₁.regs 67 limbs}
  let out := {s₂ with regs := Function.update s₂.regs 4 (2 ^ prec)}
  have hr₁ : Runs w p ω
      (.assign 68 (.bin .mul (.bin .div (.bin .add (.reg 37) (.const (radixBits - 1)))
        (.const radixBits)) (.const radixBits))) st .normal s₁ 8 :=
    runs_assign_iff.mpr ⟨prec, by simp [Expr.eval, BinOp.eval, h37, hsub, hrw, htop,
      show top / radixBits < 2 ^ w from hq, show q * radixBits < 2 ^ w from hprec,
      prec, q, top], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4))) s₁ .normal s₂ 6 :=
    runs_assign_iff.mpr ⟨limbs, by simp [Expr.eval, BinOp.eval, s₁, h127, hword, hpart,
      show prec + range + 4 < 2 ^ w from hlimbs', limbs], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 68))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, Nat.shiftLeft_eq, s₂, s₁,
      show 1 < 2 ^ w by omega, show 2 ^ prec < 2 ^ w from hscale], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₂, s₁, prec, q, top], by simp [out, s₂, limbs, prec, q, top],
    by simp [out, prec, q, top], hlow, hhigh, dvd_mul_left _ _, rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 8, 11, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 6, 4, hr₂, hr₃, rfl⟩), by decide⟩)
  · intro r h4 h67 h68
    simp [out, s₂, s₁, h4, h67, h68]

/-- Determine the bit length of the sparse-core logarithm input from the
padded edge bound. Restore the original graph's vertex count afterward. -/
@[expose] def stageRebuildLogRange (bitLength : ℕ) : Stmt :=
  prepareInitSparseCoreLogInput ;; stageInitDepthLogBlock 92 bitLength ;;
  .assign 92 (.reg 57)

/-- The range word is available before allocating the logarithm workspace. -/
theorem stageRebuildLogRange_runs
    {w bitLength M N : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : MeetsContract w p bitLength Num.IPM.bitLengthContract)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hpos : 0 < M)
    (hfit : SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2 < 2 ^ w) :
    let range := (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2).size
    ∃ out cost, Runs w p ω (stageRebuildLogRange bitLength) st .normal out cost ∧
      out.regs 127 = range ∧ out.regs 124 = SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2 ∧
      out.regs 126 = 1 ∧ out.regs 57 = N ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 24 → r ≠ 57 → r ≠ 124 → r ≠ 126 → r ≠ 127 → out.regs r = st.regs r) ∧
      cost ≤ 14 * range + 36 := by
  dsimp only
  let m := M ^ 2
  let input := SparseCore.coreNMax m + m
  have he : m * (2 * m + 60) = input := by
    dsimp [input, SparseCore.coreNMax, SparseCore.coreSplitMax]
    ring
  have hprod : m * (2 * m + 60) < 2 ^ w := by
    rw [he]
    exact (Nat.le_add_right input 2).trans_lt hfit
  have hlinear := (Nat.le_mul_of_pos_left _ (Nat.pow_pos hpos)).trans_lt hprod
  have hm := (Nat.le_mul_of_pos_right m (by omega : 0 < 2 * m + 60)).trans_lt hprod
  obtain ⟨mid, hr₁, _, h57, h92, hf₁, hm₁, _⟩ :=
    prepareInitSparseCoreLogInput_runs (p := p) (ω := ω) hM hN hm (by omega) hlinear hprod
  obtain ⟨ready, cost, hr₂, h124, h126, h127, hm₂, hf₂, hc⟩ :=
    stageInitDepthLogBlock_runs (ω := ω) hb h92 hfit
  have hsaved := (hf₂ 57 (by decide) (by decide) (by decide)).trans h57
  let out := {ready with regs := Function.update ready.regs 92 N}
  have hr₃ : Runs w p ω (.assign 92 (.reg 57)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨N, by simp [Expr.eval, hsaved], rfl, rfl, rfl⟩
  refine ⟨out, cost + 20, ?_, by simpa [out] using h127, by simpa [out, input, m] using h124,
    by simpa [out] using h126, by simpa [out] using hsaved, hm₂.trans hm₁, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 16, cost + 3, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, cost, 2, hr₂, hr₃, by omega⟩), by omega⟩)
  · intro r h24r h57r h124r h126r h127r
    by_cases hn : r = 92
    · subst r
      simp [out, hN]
    · simpa [out, hn] using (hf₂ r h124r h126r h127r).trans (hf₁ r h24r h57r hn)

/-- Choose the working scale and initialize the aligned fixed-point
workspace used by the two rebuild logarithms. -/
@[expose] def initRebuildLogWorkspace (clog bitLength radixBits : ℕ) : Stmt :=
  stageRebuildLogRange bitLength ;;
    initRebuildScalesWithLogAllowance clog ;; stageRebuildLogWorkspace radixBits

/-- The aligned workspace meets the required accuracy for both logarithms
and preserves the graph inputs. -/
theorem initRebuildLogWorkspace_runs
    {w clog bitLength h M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hbit : MeetsContract w p bitLength Num.IPM.bitLengthContract)
    (hh : 0 < h)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (h75 : st.regs 75 = depth) (h44 : st.regs 44 = L)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (hbuckets : 0 < buckets) (hb : 0 < bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let coarse := Chain.concreteThresholdScale depth
    let bits := growthWorkingBits L cap coarse (max err (4096 * (input + 2))) bound
    let precision := (bits + (h - 1)) / h * h
    let limbs := precision + range + 4
    precision < w →
    ∃ out cost, Runs w p ω (initRebuildLogWorkspace clog bitLength h) st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = limbs ∧ out.regs 4 = 2 ^ precision ∧
      bits ≤ precision ∧ max 16 (range + 11) ≤ precision ∧ precision < bits + h ∧ h ∣ precision ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 24 → r ≠ 57 → r ≠ 67 → r ≠ 68 →
        r ≠ 124 → r ≠ 126 → r ≠ 127 → r < 27 ∨ 38 < r → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L + 40 * bits + 14 * range + 224 := by
  dsimp only
  intro hwidth
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let cap := (L + 1) * buckets * (2 * degree + 190)
  let coarse := Chain.concreteThresholdScale depth
  let bits := growthWorkingBits L cap coarse (max err (4096 * (input + 2))) bound
  let top := bits + (h - 1)
  let precision := top / h * h
  change precision < w at hwidth
  have hle : bits ≤ precision := by
    have hmod := Nat.mod_lt top hh
    have he := Nat.mod_add_div top h
    rw [Nat.mul_comm h] at he
    change top % h + precision = bits + (h - 1) at he
    omega
  have hscale : 2 ^ precision < 2 ^ w := Nat.pow_lt_pow_right (by decide) hwidth
  have hbits : 2 ^ bits < 2 ^ w := (Nat.pow_le_pow_right (by decide) hle).trans_lt hscale
  have hcap : 0 < cap := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hbuckets) (by omega)
  have hcPos : 0 < coarse := Nat.two_pow_pos _
  have haccuracy := (rebuildWorkingBits_logAccuracy L cap coarse err bound input hcap hcPos hb).trans hle
  have h16 : 16 ≤ precision := (le_max_left _ _).trans haccuracy
  have hrange : (input + 2).size + 11 ≤ precision := (le_max_right _ _).trans haccuracy
  have hwpos : 0 < w := by omega
  have htwice : 2 * w ≤ 2 ^ w := by
    have hsmall : w ≤ 2 ^ (w - 1) := by
      have ht := Nat.lt_two_pow_self (n := w - 1)
      omega
    calc
      _ ≤ 2 * 2 ^ (w - 1) := Nat.mul_le_mul_left 2 hsmall
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ w)]
  have hprecPos : 0 < precision := by omega
  have hdvd : h ∣ precision := dvd_mul_left _ _
  have hhw : h < 2 ^ w := ((Nat.le_of_dvd hprecPos hdvd).trans_lt hwidth).trans Nat.lt_two_pow_self
  have htop : top < 2 ^ w := by
    have := Nat.le_of_dvd hprecPos hdvd
    change bits + (h - 1) < 2 ^ w
    omega
  have hlimbs : precision + (input + 2).size + 4 < 2 ^ w := by omega
  have hInput : input + 2 < 2 ^ w := by
    let budget := max err (4096 * (input + 2))
    have h₁ : input + 2 ≤ budget :=
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 4096)).trans (le_max_right _ _)
    have h₂ : budget ≤ 33 * cap * (budget * bound ^ 2) * coarse :=
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)).trans
        ((Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hcap)).trans
          (Nat.le_mul_of_pos_right _ hcPos))
    exact (h₁.trans h₂).trans_lt ((growthWorkingBits_bounds L cap coarse budget bound).2.2.trans_lt hbits)
  obtain ⟨start, cr, hrun, h127, _, _, _, hmr, hfr, hcr⟩ :=
    stageRebuildLogRange_runs (ω := ω) hbit hM hN hMpos hInput
  have keep (r : ℕ) (h24 : r ≠ 24) (h57 : r ≠ 57) (h124 : r ≠ 124)
      (h126 : r ≠ 126) (h127 : r ≠ 127) := hfr r h24 h57 h124 h126 h127
  obtain ⟨mid, c, hr₁, _, _, h37, _, hm₁, hf₁, hc⟩ :=
    initRebuildScalesWithLogAllowance_runs (ω := ω) hp
      ((keep 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hM)
      ((keep 92 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN) hMpos
      ((keep 75 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h75)
      ((keep 44 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h44)
      ((keep 47 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h47)
      ((keep 48 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h48)
      ((keep 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h35)
      ((keep 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h36)
      hbuckets hb hbits
  obtain ⟨out, hr₂, h68, h67, h4, hmin, hmax, hdvd, hm₂, hf₂⟩ :=
    stageRebuildLogWorkspace_runs (p := p) (ω := ω) hh hhw h37
      ((hf₁ 127 (by decide) (by decide) (by decide) (Or.inr (by decide))).trans h127)
      htop hlimbs hscale
  refine ⟨out, cr + c + 22, ?_, h68, h67, h4, hmin, haccuracy, hmax, hdvd,
    hm₂.trans (hm₁.trans hmr), ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨start, cr, c + 21, hrun,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 20, hr₁, hr₂, rfl⟩), by omega⟩)
  · intro r h4r h24r h57r h67r h68r h124r h126r h127r hr
    exact (hf₂ r h4r h67r h68r).trans ((hf₁ r h4r h24r h57r hr).trans (keep r h24r h57r h124r h126r h127r))
  · change cr ≤ 14 * (input + 2).size + 36 at hcr
    change c ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L + 40 * bits + 166 at hc
    change cr + c + 22 ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L +
      40 * bits + 14 * (input + 2).size + 224
    omega

/-- Allowing one extra limb in the word budget covers upward rounding
of the logarithm precision. -/
theorem rebuildAlignedPrecision_wordBudget (L cap coarse err bound h : ℕ) :
    let bits := growthWorkingBits L cap coarse err bound
    let aligned := (bits + (h - 1)) / h * h
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (L + 3)
    aligned * max (L + 1) 3 + extra ≤
      (Nat.clog 2 coarse + Nat.clog 2 err + Nat.clog 2 (L + 1) + extra + (h - 1)) *
        max (L + 1) 3 + extra := by
  dsimp only
  have hbudget := (Nat.div_mul_le_self _ h).trans
    (Nat.add_le_add_right (growthWorkingBits_budget L cap coarse err bound) (h - 1))
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hbudget) _

/-- The threshold assembly's word budget also covers the scaled
sparse-core logarithm input. -/
theorem rebuildLogInput_wordFits {w L cap bound input bits : ℕ}
    (hb : input + 3 ≤ bound)
    (hw : bits * max (L + 1) 3 +
      (12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (L + 3)) < w) :
    (input + 3) * 2 ^ bits < 2 ^ w := by
  let b := Nat.clog 2 bound
  have hbits : bits ≤ bits * max (L + 1) 3 :=
    Nat.le_mul_of_pos_right _ ((by decide : 0 < 3).trans_le (le_max_right _ _))
  have hb' : b ≤ 12 + Nat.clog 2 cap + (b + 2) * (L + 3) :=
    (Nat.le_add_right b 2).trans
      ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _))
  calc
    _ ≤ 2 ^ b * 2 ^ bits := Nat.mul_le_mul_right _
      (hb.trans (Nat.le_pow_clog Nat.one_lt_two _))
    _ = 2 ^ (bits + b) := by rw [← pow_add, Nat.add_comm]
    _ < _ := Nat.pow_lt_pow_right (by decide) ((Nat.add_le_add hbits hb').trans_lt hw)

/-- The threshold word budget covers a squared scale times any factor
bounded by twice the common stretch factor bound. -/
theorem rebuildSquaredScale_wordFits {w L cap bound factor bits : ℕ}
    (hf : factor ≤ 2 * bound)
    (hw : bits * max (L + 1) 3 +
      (12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (L + 3)) < w) :
    factor * (2 ^ bits) ^ 2 < 2 ^ w := by
  let b := Nat.clog 2 bound
  have hp : bits * 2 ≤ bits * max (L + 1) 3 :=
    Nat.mul_le_mul_left _ ((by decide : 2 ≤ 3).trans (le_max_right _ _))
  have he : 1 + b ≤ 12 + Nat.clog 2 cap + (b + 2) * (L + 3) :=
    (by omega : 1 + b ≤ b + 2).trans
      ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _))
  calc
    _ ≤ (2 * 2 ^ b) * (2 ^ bits) ^ 2 :=
      Nat.mul_le_mul_right _ (hf.trans (Nat.mul_le_mul_left 2 (Nat.le_pow_clog Nat.one_lt_two _)))
    _ = 2 ^ (bits * 2 + (1 + b)) := by
      rw [← pow_mul, Nat.add_comm, pow_add, pow_add, pow_one]
    _ < _ := Nat.pow_lt_pow_right (by decide) ((Nat.add_le_add hp he).trans_lt hw)

/-- The selected limb block can represent the positive logarithm input
at the aligned precision. -/
theorem rebuildLogInput_capacity {h limbs input bits : ℕ}
    (hfit : bits + (input + 2).size + 4 ≤ h * limbs) :
    2 * ((input + 2) * 2 ^ bits) < Num.capacity h limbs := by
  rw [Num.capacity_eq_two_pow]
  have hsize := Nat.lt_size_self (input + 2)
  calc
    _ < 2 * (2 ^ (input + 2).size * 2 ^ bits) :=
      Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hsize (Nat.two_pow_pos _)) (by decide)
    _ = 2 ^ (bits + (input + 2).size + 1) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The concrete logarithm and integer writer fill the threshold table
of Algorithm 2 (page 28) from the coefficient and length enclosures. -/
theorem initIntegerThresholdsFromLog_concrete_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c power clog bits load log pack h heap N limbs kl ku sl su lsstConstant err bound workBits : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hpow : MeetsContract (wordSize c J.solverWords) p power
      (initStretchPowerContract (wordSize c J.solverWords))) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let m := M ^ 2
    let P := Chain.concreteChainParams M hM
    let TP := SparseCore.sparseCoreParams E
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let coarse := Chain.concreteThresholdScale P.d
    let exponent := max (E.L + 1) 3
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let input := SparseCore.coreNMax m + m
    let allowance := max err (4096 * (input + 2))
    let work := 2 ^ workBits
    let precision := workBits * exponent
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    let factor := 3 ^ E.L * work ^ (exponent - (E.L + 1))
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let range := (input + 2).size
    let space := limbs + limbs + Num.logarithmSpace limbs workBits range
    growthWorkingBits E.L cap coarse allowance bound ≤ workBits →
    TP.Valid → TP.γ_ℓ m ≤ M → TP.γ_ℓ m ≤ P.k →
    st.regs 4 = work → st.regs 44 = E.L → st.regs 47 = E.B_fn m → st.regs 48 = E.d_fn m →
    st.regs 49 = kl → st.regs 51 = ku → st.regs 50 = sl → st.regs 52 = su →
    st.regs 22 = M → st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 76 = P.k → st.regs 75 = P.d →
    st.regs 25 = (E.P_fn m).p_s → (E.P_fn m).p_s ≤ 1 →
    st.regs 92 = N → st.regs 67 = limbs → st.regs 68 = workBits → st.regs 98 = heap →
    MeetsContract w p bits Num.IPM.bitLengthContract →
    MeetsContract w p load (Num.loadSmallContract w h) →
    MeetsContract w p pack (Num.packWordContract w h) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - range - 10)) →
    heap + space + P.d + 1 < 2 ^ w → ZeroFrom st.mem heap → h ∣ workBits →
    workBits + range + 4 ≤ h * limbs →
    0 < E.B_fn m → 0 < sl → kl ≤ ku → sl ≤ su →
    (kl : ℝ) / work ≤ (E.P_fn m).K_s → (E.P_fn m).K_s ≤ (ku : ℝ) / work →
    (sl : ℝ) / work ≤ (E.P_fn m).γ_ℓ → (E.P_fn m).γ_ℓ ≤ (su : ℝ) / work →
    precision + extra < w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    ku ≤ bound * work → su ≤ bound * work →
    input + 3 ≤ bound →
    ku - kl ≤ err → su - sl ≤ err →
    ∃ out cost base lu, Runs w p ω (initIntegerThresholdsFromLog power clog bits load log pack)
      st .normal out cost ∧
      let upper := max (first su) (second ku su lu)
      let divisor := 2 ^ (precision - e)
      let a := (upper + divisor - 1) / divisor
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a coarse j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs workBits range + 14 * range + 125 +
        (100 * exponent + 50 * P.d + 40 * e + 295) := by
  dsimp only
  intro hbitsMin hTP hγM hγk h4 h44 h47 h48 h49 h51 h50 h52 h22 h14 h76 h75
    h25 hps h92 h67 h68 h98 hbits hload hpack hlog hroom hz
    hdiv hlimbs hB hsl hk hs hklB hkuB hslB hsuB hbudget
    hstretch hku hsu hbound hke hse
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let m := M ^ 2
  let input := SparseCore.coreNMax m + m
  let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
  let coarse := Chain.concreteThresholdScale P.d
  have hcapPos : 0 < cap := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hB) (by omega)
  have hboundPos : 0 < bound := (by omega : 0 < input + 3).trans_le hbound
  have haccuracy :=
    (rebuildWorkingBits_logAccuracy E.L cap coarse err bound input hcapPos (Nat.two_pow_pos _) hboundPos).trans hbitsMin
  have hprec : 2 * workBits + 9 < 2 ^ wordSize c J.solverWords := by
    have he : 2 * workBits ≤ workBits * max (E.L + 1) 3 := by
      rw [Nat.mul_comm 2]
      exact Nat.mul_le_mul_left _ ((by decide : 2 ≤ 3).trans (le_max_right _ _))
    have hx : 9 ≤ 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3) := by omega
    exact ((Nat.add_le_add he hx).trans_lt hbudget).trans Nat.lt_two_pow_self
  have hacc := (le_max_right _ _).trans haccuracy
  have hwidth : workBits < wordSize c J.solverWords :=
    (Nat.le_mul_of_pos_right workBits (lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _))).trans_lt
      ((Nat.le_add_right _ _).trans_lt hbudget)
  have hwork : 0 < 2 ^ workBits := Nat.two_pow_pos _
  have hendpoint := rebuildLogInput_wordFits (L := E.L) (input := input) hbound hbudget
  have hcapacity := rebuildLogInput_capacity (input := input) hlimbs
  have hword : (input + 2) * 2 ^ workBits < 2 ^ wordSize c J.solverWords :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans_lt hendpoint
  have hinput := (Nat.le_mul_of_pos_right (input + 2) hwork).trans_lt hword
  have hEq : m * (2 * m + 60) = input := by
    dsimp [input, SparseCore.coreNMax, SparseCore.coreSplitMax]
    ring
  have hprod := hEq.symm ▸ (Nat.le_add_right input 2).trans_lt hinput
  have hm : 0 < m := Nat.pow_pos hM
  have hlinear := (Nat.le_mul_of_pos_left (2 * m + 60) hm).trans_lt hprod
  have hmfit := (Nat.le_mul_of_pos_right m (by omega : 0 < 2 * m + 60)).trans_lt hprod
  change heap + (limbs + limbs + Num.logarithmSpace limbs workBits (input + 2).size) +
    P.d + 1 < 2 ^ wordSize c J.solverWords at hroom
  have hlogRoom : heap + limbs + limbs + Num.logarithmSpace limbs workBits (input + 2).size <
      2 ^ wordSize c J.solverWords := by omega
  obtain ⟨mid, cLog, base, hr, hlo, hhi, hlow, _, horder, hupper, hgap,
    hscale, _, h77, _, hheap, _, hret, hf, hmem, hzero, hcost⟩ :=
    initSparseCoreLogForThresholds_runs (ω := ω) E M hbits hload hpack h25 hps hwidth
      h22 h92 h4 h67 h68 h98 hmfit (by omega) hlinear hprod hlog
      hinput hword hcapacity hlogRoom hz hdiv hacc hlimbs hprec hendpoint
  change base ≤ heap + limbs + limbs + Num.logarithmSpace limbs workBits (input + 2).size at hret
  have hbase : base + P.d + 1 < 2 ^ wordSize c J.solverWords := by omega
  obtain ⟨out, ct, ht, h83, h98', htable, hf', hz', hc'⟩ :=
    initIntegerThresholdsFromGrowth_concrete_runs J E (ω := ω) hM hc hclog hpow
      (workBits := workBits) hbitsMin hTP hγM hγk hscale ((hf 44 (by decide) (by decide)).trans h44)
      ((hf 47 (by decide) (by decide)).trans h47) ((hf 48 (by decide) (by decide)).trans h48)
      ((hf 49 (by decide) (by decide)).trans h49) ((hf 51 (by decide) (by decide)).trans h51)
      ((hf 50 (by decide) (by decide)).trans h50) ((hf 52 (by decide) (by decide)).trans h52)
      rfl rfl ((hf 22 (by decide) (by decide)).trans h22)
      ((hf 14 (by decide) (by decide)).trans h14) h77
      ((hf 76 (by decide) (by decide)).trans h76) ((hf 75 (by decide) (by decide)).trans h75)
      hbase hzero hB hsl hlow hk hs horder hklB hkuB hslB hsuB hlo hhi hbudget
      hstretch hku hsu hupper hbound hke hse hgap
  change cLog ≤ 71 * limbs + Num.logarithmCost limbs workBits (input + 2).size +
    14 * (input + 2).size + 124 at hcost
  have htotal : cLog + ct + 1 ≤
      71 * limbs + Num.logarithmCost limbs workBits (input + 2).size + 14 * (input + 2).size + 125 +
      (100 * max (E.L + 1) 3 + 50 * P.d + 40 * Nat.clog 2 (2 * (P.d + 1)) + 295) := by
    change ct ≤ 100 * max (E.L + 1) 3 + 50 * P.d + 40 * Nat.clog 2 (2 * (P.d + 1)) + 295 at hc'
    omega
  exact ⟨out, cLog + ct + 1, base, mid.regs 27,
    runs_seq_iff.mpr (Or.inr ⟨mid, cLog, ct, hr, ht, rfl⟩), h83, h98', htable,
    fun x hx => (hf' x (hx.trans_le hheap)).trans (hmem x hx), hz', htotal⟩

/-- Compute both logarithm enclosures and fill the integer rebuild thresholds. -/
@[expose] def initIntegerThresholdsFromCoefficient (power clog bits load log pack coefficient : ℕ) : Stmt :=
  initRebuildCoefficient bits load log pack coefficient ;;
    initIntegerThresholdsFromLog power clog bits load log pack

/-- The coefficient initializer supplies the first factor enclosure of
Algorithm 2 (page 28). The remaining length bounds are shared with the
sparsifier's query setup. -/
theorem initIntegerThresholdsFromCoefficient_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c power clog bits load log pack h heap N limbs coefficient sl su lsstConstant err bound workBits : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hpow : MeetsContract (wordSize c J.solverWords) p power
      (initStretchPowerContract (wordSize c J.solverWords))) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let m := M ^ 2
    let P := Chain.concreteChainParams M hM
    let TP := SparseCore.sparseCoreParams E
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let coarse := Chain.concreteThresholdScale P.d
    let exponent := max (E.L + 1) 3
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let input := SparseCore.coreNMax m + m
    let allowance := max err (4096 * (input + 2))
    let work := 2 ^ workBits
    let precision := workBits * exponent
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    let factor := 3 ^ E.L * work ^ (exponent - (E.L + 1))
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let range := (input + 2).size
    let space := limbs + limbs + Num.logarithmSpace limbs workBits range
    growthWorkingBits E.L cap coarse allowance bound ≤ workBits →
    TP.Valid → TP.γ_ℓ m ≤ M → TP.γ_ℓ m ≤ P.k →
    st.regs 4 = work → st.regs 44 = E.L → st.regs 47 = E.B_fn m → st.regs 48 = E.d_fn m →
    st.regs 50 = sl → st.regs 52 = su →
    st.regs 22 = M → st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 76 = P.k → st.regs 75 = P.d →
    st.regs 25 = (E.P_fn m).p_s → (E.P_fn m).p_s ≤ 1 →
    st.regs 92 = N → st.regs 67 = limbs → st.regs 68 = workBits → st.regs 98 = heap →
    MeetsContract w p bits Num.IPM.bitLengthContract →
    MeetsContract w p load (Num.loadSmallContract w h) →
    MeetsContract w p pack (Num.packWordContract w h) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - range - 10)) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - 12)) →
    let coefficientSpace := limbs + limbs + Num.logarithmSpace limbs workBits 2
    heap + coefficientSpace + space + P.d + 1 < 2 ^ w → ZeroFrom st.mem heap → h ∣ workBits →
    workBits + range + 4 ≤ h * limbs →
    0 < E.B_fn m → 0 < sl → sl ≤ su →
    (E.P_fn m).K_s = 1 + coefficient / Real.log 2 →
    (sl : ℝ) / work ≤ (E.P_fn m).γ_ℓ → (E.P_fn m).γ_ℓ ≤ (su : ℝ) / work →
    precision + extra < w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    2 * coefficient + 2 ≤ bound → su ≤ bound * work →
    input + 3 ≤ bound →
    65536 * coefficient + 2 ≤ err → su - sl ≤ err →
    ∃ out cost base ku lu, Runs w p ω (initIntegerThresholdsFromCoefficient power clog bits load log pack coefficient)
      st .normal out cost ∧
      let upper := max (first su) (second ku su lu)
      let divisor := 2 ^ (precision - e)
      let a := (upper + divisor - 1) / divisor
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a coarse j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 142 * limbs + Num.logarithmCost limbs workBits 2 + 158 + 1 + Num.logarithmCost limbs workBits range + 14 * range + 125 +
        (100 * exponent + 50 * P.d + 40 * e + 295) := by
  dsimp only
  intro hmin hTP hγM hγk h4 h44 h47 h48 h50 h52 h22 h14 h76 h75
    h25 hps h92 h67 h68 h98 hbits hload hpack hlog hlogTwo
    hroom hz hdiv hlimbs hB hsl hs hKs hslB hsuB
    hbudget hstretch hcoefBound hsu hbound hcoefErr hse
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let range := (input + 2).size
  let w := wordSize c J.solverWords
  let coeffSpace := limbs + limbs + Num.logarithmSpace limbs workBits 2
  let logSpace := limbs + limbs + Num.logarithmSpace limbs workBits range
  change heap + coeffSpace + logSpace + P.d + 1 < 2 ^ w at hroom
  let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
  let coarse := Chain.concreteThresholdScale P.d
  have hcapPos : 0 < cap := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hB) (by omega)
  have hboundPos : 0 < bound := (by omega : 0 < input + 3).trans_le hbound
  have haccuracy :=
    (rebuildWorkingBits_logAccuracy E.L cap coarse err bound input hcapPos (Nat.two_pow_pos _) hboundPos).trans hmin
  have hprec : 2 * workBits + 9 < 2 ^ wordSize c J.solverWords := by
    have he : 2 * workBits ≤ workBits * max (E.L + 1) 3 := by
      rw [Nat.mul_comm 2]
      exact Nat.mul_le_mul_left _ ((by decide : 2 ≤ 3).trans (le_max_right _ _))
    have hx : 9 ≤ 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3) := by omega
    exact ((Nat.add_le_add he hx).trans_lt hbudget).trans Nat.lt_two_pow_self
  have h16 := (le_max_left _ _).trans haccuracy
  have hwidth : workBits < w :=
    (Nat.le_mul_of_pos_right workBits (lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _))).trans_lt
      ((Nat.le_add_right _ _).trans_lt hbudget)
  have hrange : 2 ≤ range := Nat.lt_size.mpr (by omega)
  have hcapacity := rebuildLogInput_capacity (input := input) hlimbs
  have hcoefWord := rebuildSquaredScale_wordFits (L := E.L) (factor := coefficient + 3)
    (by omega : coefficient + 3 ≤ 2 * bound) hbudget
  have hcapTwo : 4 * 2 ^ workBits < Num.capacity h limbs :=
    (by
      have hle := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ workBits)
        (show 2 ≤ input + 2 by omega))
      simpa only [← Nat.mul_assoc] using hle : _ ≤ _).trans_lt hcapacity
  have hroomTwo : heap + limbs + limbs + Num.logarithmSpace limbs workBits 2 < 2 ^ w := by
    rw [show heap + limbs + limbs + Num.logarithmSpace limbs workBits 2 = heap + coeffSpace by
      simp [coeffSpace, Nat.add_assoc]]
    omega
  obtain ⟨mid, c₁, next, hr₁, hlo, hhi, hord, hu, hg, hs₁, hn, hN, hretLo, hretHi,
    hm, hz', hf, hc₁⟩ :=
    initRebuildCoefficient_runs (ω := ω) hbits hload hpack hlogTwo h92 h4 h67 h68 h98
      h16 hwidth hdiv ((Nat.add_le_add_right (Nat.add_le_add_left hrange workBits) 4).trans hlimbs) hprec hcapTwo hroomTwo hz hcoefWord
  have hkeep (r : ℕ) (hr : r < 95) (hr' : r ∉ ([2, 3, 4, 28, 29, 37, 49, 51, 57] : List ℕ)) :=
    hf r hr hr'
  have hnext : next + logSpace + P.d + 1 < 2 ^ w := by
    rw [show heap + limbs + limbs + Num.logarithmSpace limbs workBits 2 = heap + coeffSpace by
      simp [coeffSpace, Nat.add_assoc]] at hretHi
    omega
  obtain ⟨out, c₂, base, lu, hr₂, h83, h98', htable, hmem, hzero, hc₂⟩ :=
    initIntegerThresholdsFromLog_concrete_runs J E (ω := ω) hM hc hclog hpow
      hmin hTP hγM hγk hs₁ ((hkeep 44 (by decide) (by decide)).trans h44)
      ((hkeep 47 (by decide) (by decide)).trans h47) ((hkeep 48 (by decide) (by decide)).trans h48)
      rfl rfl ((hkeep 50 (by decide) (by decide)).trans h50) ((hkeep 52 (by decide) (by decide)).trans h52)
      ((hkeep 22 (by decide) (by decide)).trans h22) ((hkeep 14 (by decide) (by decide)).trans h14)
      ((hkeep 76 (by decide) (by decide)).trans h76) ((hkeep 75 (by decide) (by decide)).trans h75)
      ((hkeep 25 (by decide) (by decide)).trans h25) hps hN
      ((hkeep 67 (by decide) (by decide)).trans h67) ((hkeep 68 (by decide) (by decide)).trans h68)
      hn hbits hload hpack hlog hnext hz' hdiv hlimbs hB hsl hord hs
      (hlo.trans_eq hKs.symm) (hKs.trans_le hhi) hslB hsuB hbudget hstretch
      (hu.trans (Nat.mul_le_mul_right _ hcoefBound)) hsu hbound (hg.trans hcoefErr) hse
  refine ⟨out, c₁ + c₂ + 1, base, mid.regs 51, lu,
    runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩), h83, h98', htable,
    fun x hx => (hmem x (hx.trans_le (Nat.le_add_right heap limbs |>.trans hretLo))).trans (hm x hx),
    hzero, ?_⟩
  let tableCost := 100 * max (E.L + 1) 3 + 50 * P.d + 40 * Nat.clog 2 (2 * (P.d + 1)) + 295
  change c₂ ≤ 71 * limbs + Num.logarithmCost limbs workBits range + 14 * range + 125 + tableCost at hc₂
  change _ ≤ 142 * limbs + Num.logarithmCost limbs workBits 2 + 158 + 1 +
    Num.logarithmCost limbs workBits range + 14 * range + 125 + tableCost
  omega

/-- Form the sparsifier length enclosure before computing the other two
factors and writing the integer rebuild thresholds. -/
@[expose] def initIntegerThresholdsFromPathBounds (power clog bits load log pack coefficient : ℕ) : Stmt :=
  finishInitSparsifierLengthFactor ;;
    initIntegerThresholdsFromCoefficient power clog bits load log pack coefficient

/-- Path endpoint bounds imply the width and magnitude needed by the
rebuild threshold table of Algorithm 2 (page 28). -/
theorem initIntegerThresholdsFromPathBounds_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c power clog bits load log pack h heap N limbs coefficient pathBound pathErr lo₁ lo₂ hi₁ hi₂ lsstConstant err bound workBits : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (paths : Spanner.PathDSTool) (cDeg phiConst phiMin : ℝ)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hpow : MeetsContract (wordSize c J.solverWords) p power
      (initStretchPowerContract (wordSize c J.solverWords))) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let m := M ^ 2
    let P := Chain.concreteChainParams M hM
    let TP := SparseCore.sparseCoreParams E
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let coarse := Chain.concreteThresholdScale P.d
    let exponent := max (E.L + 1) 3
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let input := SparseCore.coreNMax m + m
    let allowance := max err (4096 * (input + 2))
    let work := 2 ^ workBits
    let precision := workBits * exponent
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    let factor := 3 ^ E.L * work ^ (exponent - (E.L + 1))
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let range := (input + 2).size
    let space := limbs + limbs + Num.logarithmSpace limbs workBits range
    growthWorkingBits E.L cap coarse allowance bound ≤ workBits →
    TP.Valid → TP.γ_ℓ m ≤ M → TP.γ_ℓ m ≤ P.k →
    st.regs 4 = work → st.regs 44 = E.L → st.regs 47 = E.B_fn m → st.regs 48 = E.d_fn m →
    st.regs 60 = lo₁ → st.regs 40 = lo₂ → st.regs 61 = hi₁ → st.regs 42 = hi₂ →
    st.regs 22 = M → st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 76 = P.k → st.regs 75 = P.d →
    st.regs 25 = (E.P_fn m).p_s → (E.P_fn m).p_s ≤ 1 →
    st.regs 92 = N → st.regs 67 = limbs → st.regs 68 = workBits → st.regs 98 = heap →
    MeetsContract w p bits Num.IPM.bitLengthContract →
    MeetsContract w p load (Num.loadSmallContract w h) →
    MeetsContract w p pack (Num.packWordContract w h) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - range - 10)) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - 12)) →
    let coefficientSpace := limbs + limbs + Num.logarithmSpace limbs workBits 2
    heap + coefficientSpace + space + P.d + 1 < 2 ^ w → ZeroFrom st.mem heap → h ∣ workBits →
    workBits + range + 4 ≤ h * limbs →
    0 < E.B_fn m →
    (E.P_fn m).K_s = 1 + coefficient / Real.log 2 →
    (E.P_fn m).γ_ℓ = Spanner.capGammaL cDeg phiConst paths phiMin m →
    (lo₁ : ℝ) / work ≤ paths.γ_ExpPath phiMin m →
    paths.γ_ExpPath phiMin m ≤ (hi₁ : ℝ) / work →
    (lo₂ : ℝ) / work ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin m) →
    paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin m) ≤ (hi₂ : ℝ) / work →
    work ≤ max lo₁ lo₂ →
    hi₁ ≤ pathBound * work → hi₂ ≤ pathBound * work →
    hi₁ - lo₁ ≤ pathErr → hi₂ - lo₂ ≤ pathErr →
    precision + extra < w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    2 * coefficient + 2 ≤ bound → pathBound ^ 2 ≤ bound →
    input + 3 ≤ bound →
    65536 * coefficient + 2 ≤ err → 2 * pathBound * pathErr + 2 ≤ err →
    ∃ out cost base ku su lu, Runs w p ω (initIntegerThresholdsFromPathBounds power clog bits load log pack coefficient)
      st .normal out cost ∧
      let upper := max (first su) (second ku su lu)
      let divisor := 2 ^ (precision - e)
      let a := (upper + divisor - 1) / divisor
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a coarse j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 142 * limbs + Num.logarithmCost limbs workBits 2 + 158 + 48 + Num.logarithmCost limbs workBits range + 14 * range + 125 +
        (100 * exponent + 50 * P.d + 40 * e + 295) := by
  dsimp only
  intro hmin hTP hγM hγk h4 h44 h47 h48 h60 h40 h61 h42 h22 h14 h76 h75
    h25 hps h92 h67 h68 h98 hbits hload hpack hlog hlogTwo
    hroom hz hdiv hlimbs hB hKs hLength
    hLo₁ hHi₁ hLo₂ hHi₂ hpos hBound₁ hBound₂ hErr₁ hErr₂
    hbudget hstretch hcoefBound hpathBound hbound hcoefErr hpathErr
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let m := M ^ 2
  have hcoefWord := rebuildSquaredScale_wordFits (L := E.L) (factor := coefficient + 3)
    (by omega : coefficient + 3 ≤ 2 * bound) hbudget
  let scale := 2 ^ workBits
  have hsPos : 0 < scale := Nat.two_pow_pos _
  have hsq : scale ≤ scale ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hsPos (by decide : 1 ≤ 2)
  have hPathRoom : (pathBound * scale) ^ 2 + (scale - 1) < 2 ^ wordSize c J.solverWords := by
    calc
      _ ≤ (bound + 1) * scale ^ 2 := by
        rw [mul_pow, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hpathBound) ((Nat.sub_le _ _).trans hsq)
      _ < _ := rebuildSquaredScale_wordFits (L := E.L) (by omega : bound + 1 ≤ 2 * bound) hbudget
  have hword : 1 < 2 ^ wordSize c J.solverWords := by
    have hs : 0 < 2 ^ workBits := Nat.two_pow_pos _
    have hs' : 0 < (2 ^ workBits) ^ 2 := Nat.pow_pos hs
    have hw : 3 ≤ (coefficient + 3) * (2 ^ workBits) ^ 2 :=
      (Nat.le_add_left 3 coefficient).trans (Nat.le_mul_of_pos_right _ hs')
    omega
  obtain ⟨mid, hr₁, hlo, hhi, hpos', horder, hu, hg, hm, hf⟩ :=
    finishInitSparsifierLengthFactor_withGap_runs cDeg phiConst phiMin paths m (ω := ω)
      h4 (Nat.two_pow_pos _) h60 h40 h61 h42 hLo₁ hHi₁ hLo₂ hHi₂ hpos
      hBound₁ hBound₂ hErr₁ hErr₂ hword hPathRoom
  obtain ⟨out, cost, base, ku, lu, hr₂, h83, h98', htable, hmem, hzero, hcost⟩ :=
    initIntegerThresholdsFromCoefficient_runs J E (ω := ω) hM hc hclog hpow
      hmin hTP hγM hγk ((hf 4 (by decide)).trans h4) ((hf 44 (by decide)).trans h44)
      ((hf 47 (by decide)).trans h47) ((hf 48 (by decide)).trans h48)
      rfl rfl ((hf 22 (by decide)).trans h22) ((hf 14 (by decide)).trans h14)
      ((hf 76 (by decide)).trans h76) ((hf 75 (by decide)).trans h75)
      ((hf 25 (by decide)).trans h25) hps ((hf 92 (by decide)).trans h92)
      ((hf 67 (by decide)).trans h67) ((hf 68 (by decide)).trans h68)
      ((hf 98 (by decide)).trans h98) hbits hload hpack hlog hlogTwo
      hroom (hm.symm ▸ hz) hdiv hlimbs hB hpos' horder hKs
      (hlo.trans_eq hLength.symm) (hLength.trans_le hhi) hbudget hstretch hcoefBound
      (hu.trans (Nat.mul_le_mul_right _ hpathBound)) hbound hcoefErr (hg.trans hpathErr)
  refine ⟨out, 46 + cost + 1, base, ku, mid.regs 52, lu,
    runs_seq_iff.mpr (Or.inr ⟨mid, 46, cost, hr₁, hr₂, rfl⟩), h83, h98', htable,
    fun x hx => (hmem x hx).trans (congrFun hm x), hzero, ?_⟩
  omega

/-- Save the chain words used again after path evaluation. -/
@[expose] def saveRebuildPathInputs : Stmt :=
  .assign 130 (.reg 14) ;;
  .assign 131 (.reg 44) ;;
  .assign 132 (.reg 47) ;;
  .assign 133 (.reg 48) ;;
  .assign 134 (.reg 92)

/-- The register copies preserve the heap and all other registers. -/
theorem saveRebuildPathInputs_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω saveRebuildPathInputs st .normal out 14 ∧
      out.regs 130 = st.regs 14 ∧
      out.regs 131 = st.regs 44 ∧
      out.regs 132 = st.regs 47 ∧
      out.regs 133 = st.regs 48 ∧
      out.regs 134 = st.regs 92 ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 130 → r ≠ 131 → r ≠ 132 → r ≠ 133 → r ≠ 134 → out.regs r = st.regs r) := by
  let s1 := {st with regs := Function.update st.regs 130 (st.regs 14)}
  let s2 := {s1 with regs := Function.update s1.regs 131 (st.regs 44)}
  let s3 := {s2 with regs := Function.update s2.regs 132 (st.regs 47)}
  let s4 := {s3 with regs := Function.update s3.regs 133 (st.regs 48)}
  let out := {s4 with regs := Function.update s4.regs 134 (st.regs 92)}
  have hr1 : Runs w p ω (.assign 130 (.reg 14)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 131 (.reg 44)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 132 (.reg 47)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 133 (.reg 48)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s3, s2, s1], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 134 (.reg 92)) s4 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s4, s3, s2, s1], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s4, s3, s2, s1], by simp [out, s4, s3, s2, s1], by simp [out, s4, s3, s2, s1], by simp [out, s4, s3, s2, s1], by simp [out, s4, s3, s2, s1], rfl, ?_⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨s1, 2, 11, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 2, 8, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 2, 5, hr3, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s4, 2, 2, hr4, hr5, rfl⟩)
  · intro r h130 h131 h132 h133 h134
    simp [out, s4, s3, s2, s1, h130, h131, h132, h133, h134]

/-- Restore the chain words and take the path routine’s returned heap cursor. -/
@[expose] def restoreRebuildPathInputs : Stmt :=
  .assign 14 (.reg 130) ;;
  .assign 44 (.reg 131) ;;
  .assign 47 (.reg 132) ;;
  .assign 48 (.reg 133) ;;
  .assign 92 (.reg 134) ;;
  .assign 98 (.reg 99)

/-- The register copies preserve the heap and all other registers. -/
theorem restoreRebuildPathInputs_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω restoreRebuildPathInputs st .normal out 17 ∧
      out.regs 14 = st.regs 130 ∧
      out.regs 44 = st.regs 131 ∧
      out.regs 47 = st.regs 132 ∧
      out.regs 48 = st.regs 133 ∧
      out.regs 92 = st.regs 134 ∧
      out.regs 98 = st.regs 99 ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 14 → r ≠ 44 → r ≠ 47 → r ≠ 48 → r ≠ 92 → r ≠ 98 → out.regs r = st.regs r) := by
  let s1 := {st with regs := Function.update st.regs 14 (st.regs 130)}
  let s2 := {s1 with regs := Function.update s1.regs 44 (st.regs 131)}
  let s3 := {s2 with regs := Function.update s2.regs 47 (st.regs 132)}
  let s4 := {s3 with regs := Function.update s3.regs 48 (st.regs 133)}
  let s5 := {s4 with regs := Function.update s4.regs 92 (st.regs 134)}
  let out := {s5 with regs := Function.update s5.regs 98 (st.regs 99)}
  have hr1 : Runs w p ω (.assign 14 (.reg 130)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 44 (.reg 131)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 47 (.reg 132)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 48 (.reg 133)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s3, s2, s1], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 92 (.reg 134)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s4, s3, s2, s1], rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 98 (.reg 99)) s5 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s5, s4, s3, s2, s1], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s5, s4, s3, s2, s1], by simp [out, s5, s4, s3, s2, s1], by simp [out, s5, s4, s3, s2, s1], by simp [out, s5, s4, s3, s2, s1], by simp [out, s5, s4, s3, s2, s1], by simp [out, s5, s4, s3, s2, s1], rfl, ?_⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨s1, 2, 14, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 2, 11, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 2, 8, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 2, 5, hr4, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s5, 2, 2, hr5, hr6, rfl⟩)
  · intro r h14 h44 h47 h48 h92 h98
    simp [out, s5, s4, s3, s2, s1, h14, h44, h47, h48, h92, h98]

/-- Set the aligned workspace before constructing the table from
the path bounds at its selected scale. -/
@[expose] def initIntegerThresholdsWithWorkspace (h power clog bits load log pack coefficient : ℕ) : Stmt :=
  initRebuildLogWorkspace clog bits h ;;
    initIntegerThresholdsFromPathBounds power clog bits load log pack coefficient

/-- Algorithm 2 (page 28) uses an integer rebuild table. The machine
chooses the scale and workspace, then computes the table from the
path endpoints staged at that scale. -/
theorem initIntegerThresholdsWithWorkspace_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c power clog bits load log pack h heap N coefficient pathBound pathErr lo₁ lo₂ hi₁ hi₂ lsstConstant err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (paths : Spanner.PathDSTool) (cDeg phiConst phiMin : ℝ)
    (hh : 0 < h)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hpow : MeetsContract (wordSize c J.solverWords) p power
      (initStretchPowerContract (wordSize c J.solverWords))) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let m := M ^ 2
    let P := Chain.concreteChainParams M hM
    let TP := SparseCore.sparseCoreParams E
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let coarse := Chain.concreteThresholdScale P.d
    let exponent := max (E.L + 1) 3
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let input := SparseCore.coreNMax m + m
    let allowance := max err (4096 * (input + 2))
    let bitsMin := growthWorkingBits E.L cap coarse allowance bound
    let workBits := (bitsMin + (h - 1)) / h * h
    let work := 2 ^ workBits
    let precision := workBits * exponent
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    let factor := 3 ^ E.L * work ^ (exponent - (E.L + 1))
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let range := (input + 2).size
    let limbs := workBits + range + 4
    let space := limbs + limbs + Num.logarithmSpace limbs workBits range
    TP.Valid → TP.γ_ℓ m ≤ M → TP.γ_ℓ m ≤ P.k →
    st.regs 35 = err → st.regs 36 = bound → st.regs 44 = E.L → st.regs 47 = E.B_fn m → st.regs 48 = E.d_fn m →
    st.regs 60 = lo₁ → st.regs 40 = lo₂ → st.regs 61 = hi₁ → st.regs 42 = hi₂ →
    st.regs 22 = M → st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 76 = P.k → st.regs 75 = P.d →
    st.regs 25 = (E.P_fn m).p_s → (E.P_fn m).p_s ≤ 1 →
    st.regs 92 = N → st.regs 98 = heap →
    MeetsContract w p bits Num.IPM.bitLengthContract →
    MeetsContract w p load (Num.loadSmallContract w h) →
    MeetsContract w p pack (Num.packWordContract w h) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - range - 10)) →
    MeetsContract w p log (Num.logarithmContract w h (workBits - 12)) →
    let coefficientSpace := limbs + limbs + Num.logarithmSpace limbs workBits 2
    heap + coefficientSpace + space + P.d + 1 < 2 ^ w → ZeroFrom st.mem heap →
    0 < E.B_fn m →
    (E.P_fn m).K_s = 1 + coefficient / Real.log 2 →
    (E.P_fn m).γ_ℓ = Spanner.capGammaL cDeg phiConst paths phiMin m →
    (lo₁ : ℝ) / work ≤ paths.γ_ExpPath phiMin m →
    paths.γ_ExpPath phiMin m ≤ (hi₁ : ℝ) / work →
    (lo₂ : ℝ) / work ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin m) →
    paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin m) ≤ (hi₂ : ℝ) / work →
    work ≤ max lo₁ lo₂ →
    hi₁ ≤ pathBound * work → hi₂ ≤ pathBound * work →
    hi₁ - lo₁ ≤ pathErr → hi₂ - lo₂ ≤ pathErr →
    (Nat.clog 2 coarse + Nat.clog 2 allowance + Nat.clog 2 (E.L + 1) + extra + (h - 1)) *
      exponent + extra < w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    2 * coefficient + 2 ≤ bound → pathBound ^ 2 ≤ bound →
    input + 3 ≤ bound →
    65536 * coefficient + 2 ≤ err → 2 * pathBound * pathErr + 2 ≤ err →
    ∃ out cost base ku su lu, Runs w p ω (initIntegerThresholdsWithWorkspace h power clog bits load log pack coefficient)
      st .normal out cost ∧
      let upper := max (first su) (second ku su lu)
      let divisor := 2 ^ (precision - e)
      let a := (upper + divisor - 1) / divisor
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a coarse j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 40 * e + 13 * E.L + 40 * bitsMin + 14 * range + 225 +
        (142 * limbs + Num.logarithmCost limbs workBits 2 + 158 + 48 + Num.logarithmCost limbs workBits range + 14 * range + 125 +
        (100 * exponent + 50 * P.d + 40 * e + 295)) := by
  dsimp only
  intro hTP hγM hγk h35 h36 h44 h47 h48 h60 h40 h61 h42 h22 h14 h76 h75
    h25 hps h92 h98 hbits hload hpack hlog hlogTwo hroom hz hB hKs hLength
    hLo₁ hHi₁ hLo₂ hHi₂ hpos hBound₁ hBound₂ hErr₁ hErr₂
    hwordBudget hstretch hcoefBound hpathBound hbound hcoefErr hpathErr
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let range := (input + 2).size
  let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
  let coarse := Chain.concreteThresholdScale P.d
  let bitsMin := growthWorkingBits E.L cap coarse (max err (4096 * (input + 2))) bound
  let workBits := (bitsMin + (h - 1)) / h * h
  let limbs := workBits + range + 4
  have hb : 0 < bound := (by omega : 0 < input + 3).trans_le hbound
  have hbudget := (rebuildAlignedPrecision_wordBudget E.L cap coarse
    (max err (4096 * (input + 2))) bound h).trans_lt hwordBudget
  have hwidth : workBits < wordSize c J.solverWords :=
    (Nat.le_mul_of_pos_right workBits (lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _))).trans_lt
      ((Nat.le_add_right _ _).trans_lt hbudget)
  obtain ⟨mid, c₁, hr₁, h68, h67, h4, hmin, _, _, hdvd, hm, hf, hc₁⟩ :=
    initRebuildLogWorkspace_runs (ω := ω) hclog hbits hh h22 h92 hM h75 h44 h47 h48 h35 h36 hB hb hwidth
  have hlimbs : workBits + range + 4 ≤ h * limbs := Nat.le_mul_of_pos_left _ hh
  have keep (r : ℕ) (hr : r ≠ 4 ∧ r ≠ 24 ∧ r ≠ 57 ∧ r ≠ 67 ∧ r ≠ 68 ∧
      r ≠ 124 ∧ r ≠ 126 ∧ r ≠ 127 ∧ (r < 27 ∨ 38 < r)) :=
    hf r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1
      hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2
  obtain ⟨out, c₂, base, ku, su, lu, hr₂, h83, h98', htable, hmem, hzero, hc₂⟩ :=
    initIntegerThresholdsFromPathBounds_runs J E paths cDeg phiConst phiMin (ω := ω) hM hc hclog hpow
      hmin hTP hγM hγk h4 ((keep 44 (by decide)).trans h44)
      ((keep 47 (by decide)).trans h47) ((keep 48 (by decide)).trans h48)
      ((keep 60 (by decide)).trans h60) ((keep 40 (by decide)).trans h40)
      ((keep 61 (by decide)).trans h61) ((keep 42 (by decide)).trans h42)
      ((keep 22 (by decide)).trans h22) ((keep 14 (by decide)).trans h14)
      ((keep 76 (by decide)).trans h76) ((keep 75 (by decide)).trans h75)
      ((keep 25 (by decide)).trans h25) hps ((keep 92 (by decide)).trans h92)
      h67 h68 ((keep 98 (by decide)).trans h98) hbits hload hpack hlog hlogTwo
      hroom (hm.symm ▸ hz) hdvd hlimbs hB hKs hLength hLo₁ hHi₁ hLo₂ hHi₂ hpos
      hBound₁ hBound₂ hErr₁ hErr₂ hbudget hstretch hcoefBound hpathBound hbound hcoefErr hpathErr
  refine ⟨out, c₁ + c₂ + 1, base, ku, su, lu,
    runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩), h83, h98', htable,
    fun x hx => (hmem x hx).trans (congrFun hm x), hzero, ?_⟩
  let initCost := 40 * Nat.clog 2 (2 * (P.d + 1)) + 13 * E.L + 40 * bitsMin + 14 * range + 224
  let tableCost := 142 * limbs + Num.logarithmCost limbs workBits 2 + 158 + 48 +
    Num.logarithmCost limbs workBits range + 14 * range + 125 +
    (100 * max (E.L + 1) 3 + 50 * P.d + 40 * Nat.clog 2 (2 * (P.d + 1)) + 295)
  change c₁ ≤ initCost at hc₁
  change c₂ ≤ tableCost at hc₂
  change c₁ + c₂ + 1 ≤ initCost + 1 + tableCost
  exact (Nat.add_le_add_right (Nat.add_le_add hc₁ hc₂) 1).trans_eq (Nat.add_right_comm _ _ _)

end MinCostFlow.MinRatio
