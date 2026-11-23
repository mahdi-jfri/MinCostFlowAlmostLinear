module

public import MinCostFlow.HierPaths.DelProgFields
public import MinCostFlow.HierPaths.DelProgPairTest

/-!
# One level of the loss counters in the `Delete` program

When a terminal `u` fails directly, `Delete` climbs from the leaf to the root and updates, at each
depth `j`, the counters of the group `X` of `u` (`levelStep`, `HierPaths/LossCounters.lean`): the
sum of the children `s = sum j X + Δ` and the own count `newOwn s`, which is all members of `X`
when `4 s` exceeds the group size and `s` otherwise. The group is `X = u >>> (x - j b)` and the
group size is `1 <<< (x - j b)`, since `x - min x (j b) = x - j b` in `ℕ`.

`ctrStmt` makes this update with the terminal in register `10`, the depth in register `11` and
the change `Δ` in register `12`. It leaves the shift, the group, the group size, the new sum, the
old own count and the new own count in registers `13` to `18`, so that the caller can test
whether the group became full and pass `o' - o` up. `ctr_triple` gives the registers and the block
afterwards: the counters of `X` at depth `j` are set as in `levelStep`.

The register-exact rule `triple_assign_exact` helps here and later: an assignment from a state
with known registers gives the registers updated at one place, and keeps the memory.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- An assignment from a state with registers `R`: the registers become `R` updated at `r`, and
the memory is kept. -/
theorem triple_assign_exact {w : ℕ} {p : Program} {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop} {r : ℕ}
    {e : Expr} {v : ℕ} (he : ∀ s, s.regs = R → M s.mem → e.eval w s = some v) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign r e)
      (normalPost fun s => s.regs = Function.update R r v ∧ M s.mem) (fun _ => e.size + 1) :=
  Triple.assign (val := fun _ => v) (fun s hs => he s hs.1 hs.2) fun s hs => by
    refine ⟨?_, hs.2⟩
    show Function.update s.regs r v = _
    rw [hs.1]

/-- A header word, read from the block whose handle is in register `0`. -/
def readHdr (k : ℕ) : Expr := readSec numSec 0 0 (.const k)

/-- The word of the counter of the group in register `14` at the depth in register `11`, in
section `i` (`18` or `19`). -/
def ctrWord (i : ℕ) : Expr :=
  .bin .add (.bin .add (readHdr 7) (.const 2)) (.bin .add (readSec numSec 0 i (.reg 11)) (.reg 14))

/-- One level of the loss counters. -/
def ctrStmt : Stmt :=
  .seq (.assign 13 (.bin .sub (readHdr 5) (.bin .mul (.reg 11) (readHdr 6))))
  (.seq (.assign 14 (.bin .shiftRight (.reg 10) (.reg 13)))
  (.seq (.assign 15 (.bin .shiftLeft (.const 1) (.reg 13)))
  (.seq (.assign 16 (.bin .add (readSec numSec 0 19 (ctrWord 19)) (.reg 12)))
  (.seq (.assign 17 (readSec numSec 0 18 (ctrWord 18)))
  (.seq (.cond (.bin .lt (.reg 15) (.bin .mul (.const 4) (.reg 16)))
      (.assign 18 (.reg 15)) (.assign 18 (.reg 16)))
  (.seq (.store (secAddr numSec 0 18 (ctrWord 18)) (.reg 18))
    (.store (secAddr numSec 0 19 (ctrWord 19)) (.reg 16))))))))

theorem ctrStmt_noRand : ctrStmt.NoRand := by
  simp [ctrStmt, Stmt.NoRand]

theorem groupOf_eq_shiftRight (x b j u : ℕ) : groupOf x b j u = u >>> (x - j * b) := by
  rw [groupOf, groupSize, Nat.shiftRight_eq_div_pow]
  congr 2
  omega

theorem groupSize_eq_shiftLeft (x b j : ℕ) : groupSize x b j = 1 <<< (x - j * b) := by
  rw [groupSize, Nat.shiftLeft_eq, one_mul]
  congr 1
  omega

/-- The registers after `ctrStmt`. -/
def ctrRegs (R : ℕ → ℕ) (sh X sz s o o' : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update R 13 sh) 14 X) 15 sz) 16 s) 17 o) 18 o'

/-- The concrete state after `ctrStmt`: the counters of group `X` at depth `j` set. -/
def HierConcrete.setCtr (x : HierConcrete) (j X o' s : ℕ) : HierConcrete :=
  x.withSt { x.ms.st with loss := { x.ms.st.loss with
    own := setAt x.ms.st.loss.own j X o', sum := setAt x.ms.st.loss.sum j X s } }

namespace HierConcrete

variable (y : HierConcrete)

theorem length_sections' : y.sections.length = numSec := rfl

theorem le_length_encode : 25 ≤ y.encode.length := by
  simp [HierConcrete.encode, layoutList, csrList]

theorem sections_getD_0 : y.sections.getD 0 [] = y.header := by simp [HierConcrete.sections]

theorem sections_getD_18 : y.sections.getD 18 [] = csrList (y.depth + 1) fun i =>
    tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.own i) := by simp [HierConcrete.sections]

theorem sections_getD_19 : y.sections.getD 19 [] = csrList (y.depth + 1) fun i =>
    tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.sum i) := by simp [HierConcrete.sections]

theorem ctrIdx_eq (j X : ℕ) : y.ctrIdx j X = y.depth + 1 + 1 +
    ((List.range j).map fun i => numGroups y.H.A.x y.H.A.b i).sum + X := by
  simp [HierConcrete.ctrIdx]

theorem ctrIdx_lt_18 {j X : ℕ} (hj : j ≤ y.depth) (hX : X < numGroups y.H.A.x y.H.A.b j) :
    y.ctrIdx j X < (y.sections.getD 18 []).length := by
  have := csrList_data_lt (fun i => tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.own i))
    (n := y.depth + 1) (j := j) (by omega) (k := X) (by simpa using hX)
  rw [sections_getD_18, ctrIdx_eq]; simpa using this

theorem ctrIdx_lt_19 {j X : ℕ} (hj : j ≤ y.depth) (hX : X < numGroups y.H.A.x y.H.A.b j) :
    y.ctrIdx j X < (y.sections.getD 19 []).length := by
  have := csrList_data_lt (fun i => tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.sum i))
    (n := y.depth + 1) (j := j) (by omega) (k := X) (by simpa using hX)
  rw [sections_getD_19, ctrIdx_eq]; simpa using this

theorem ctrIdx_lt_pow {w b j X : ℕ} (hb : b + y.encode.length < 2 ^ w) (hj : j ≤ y.depth)
    (hX : X < numGroups y.H.A.x y.H.A.b j) : y.ctrIdx j X < 2 ^ w := by
  have := lt_length_of_sec (by rw [length_sections']; norm_num) (y.ctrIdx_lt_18 hj hX)
  have h' : (layoutList y.sections).length = y.encode.length := rfl
  omega

theorem eval_readHdr {w b : ℕ} {s : State} (hb : b + y.encode.length < 2 ^ w)
    (hr : s.regs 0 = b) (hl : ListAt s.mem b y.encode) {k : ℕ} (hk : k < 15) :
    (readHdr k).eval w s = some (y.header.getD k 0) := by
  have hl' : ListAt s.mem b (layoutList y.sections) := hl
  have := y.le_length_encode
  have h := eval_readSec' (w := w) hl' hb hr (i := 0) (by rw [length_sections']; norm_num)
    (ke := .const k) (k := k) (Expr.eval_const (by omega))
    (by rw [sections_getD_0]; simp [HierConcrete.header]; omega)
  rw [length_sections', sections_getD_0] at h
  exact h

theorem eval_ctrWord {w b j X : ℕ} {s : State} (hb : b + y.encode.length < 2 ^ w)
    (hr0 : s.regs 0 = b) (hr11 : s.regs 11 = j) (hr14 : s.regs 14 = X)
    (hl : ListAt s.mem b y.encode) (hj : j ≤ y.depth) (hX : X < numGroups y.H.A.x y.H.A.b j) :
    (ctrWord 18).eval w s = some (y.ctrIdx j X) ∧ (ctrWord 19).eval w s = some (y.ctrIdx j X) := by
  have hl' : ListAt s.mem b (layoutList y.sections) := hl
  have hidxw := y.ctrIdx_lt_pow hb hj hX
  have hidx := y.ctrIdx_eq j X
  have h7 := y.eval_readHdr hb hr0 hl (k := 7) (by norm_num)
  simp [HierConcrete.header] at h7
  have hjl : j < (y.sections.getD 18 []).length := by
    rw [sections_getD_18]; simp [csrList]; omega
  have hjl' : j < (y.sections.getD 19 []).length := by
    rw [sections_getD_19]; simp [csrList]; omega
  have h18 := eval_readSec' (w := w) hl' hb hr0 (i := 18) (by rw [length_sections']; norm_num)
    (ke := .reg 11) (k := j) (Expr.eval_reg_of_eq hr11) hjl
  have h19 := eval_readSec' (w := w) hl' hb hr0 (i := 19) (by rw [length_sections']; norm_num)
    (ke := .reg 11) (k := j) (Expr.eval_reg_of_eq hr11) hjl'
  rw [length_sections', sections_getD_18, csrList_getD_offset _ (by omega)] at h18
  rw [length_sections', sections_getD_19, csrList_getD_offset _ (by omega)] at h19
  simp only [length_tabList] at h18 h19
  constructor
  · unfold ctrWord
    rw [hidx]
    refine Expr.eval_add (Expr.eval_add h7 (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_add h18 (Expr.eval_reg_of_eq hr14) (by omega)) (by omega) |>.trans ?_
    congr 1; omega
  · unfold ctrWord
    rw [hidx]
    refine Expr.eval_add (Expr.eval_add h7 (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_add h19 (Expr.eval_reg_of_eq hr14) (by omega)) (by omega) |>.trans ?_
    congr 1; omega

theorem getD_ctr_18 {j X : ℕ} (hj : j ≤ y.depth) (hX : X < numGroups y.H.A.x y.H.A.b j) :
    (y.sections.getD 18 []).getD (y.ctrIdx j X) 0 = y.ms.st.loss.own j X := by
  rw [sections_getD_18, ctrIdx_eq]
  have := csrList_getD_data (fun i => tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.own i))
    (n := y.depth + 1) (j := j) (by omega) (k := X) (by simpa using hX)
  simp only [length_tabList] at this
  rw [this, tabList, List.getD_eq_getElem _ _ (by simpa using hX)]
  simp

theorem getD_ctr_19 {j X : ℕ} (hj : j ≤ y.depth) (hX : X < numGroups y.H.A.x y.H.A.b j) :
    (y.sections.getD 19 []).getD (y.ctrIdx j X) 0 = y.ms.st.loss.sum j X := by
  rw [sections_getD_19, ctrIdx_eq]
  have := csrList_getD_data (fun i => tabList (numGroups y.H.A.x y.H.A.b i) (y.ms.st.loss.sum i))
    (n := y.depth + 1) (j := j) (by omega) (k := X) (by simpa using hX)
  simp only [length_tabList] at this
  rw [this, tabList, List.getD_eq_getElem _ _ (by simpa using hX)]
  simp

end HierConcrete

/-- **One level of the loss counters.** -/
theorem ctr_triple {w : ℕ} {p : Program} (x : HierConcrete) {b u j Δ : ℕ} {R : ℕ → ℕ}
    {mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hR10 : R 10 = u) (hR11 : R 11 = j) (hR12 : R 12 = Δ)
    (hu : u < 2 ^ x.H.A.x) (hj : j ≤ x.depth) (hb : b + x.encode.length < 2 ^ w)
    (hjb : j * x.H.A.b < 2 ^ w) (h2x : 2 ^ x.H.A.x < 2 ^ w)
    (hs4 : 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a) ctrStmt
      (normalPost fun s => s.regs = ctrRegs R (x.H.A.x - j * x.H.A.b)
          (groupOf x.H.A.x x.H.A.b j u) (groupSize x.H.A.x x.H.A.b j)
          (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)
          (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u))
          (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) ∧
        ListAt s.mem b (x.setCtr j (groupOf x.H.A.x x.H.A.b j u)
          (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ))
          (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)).encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => 400) := by
  have h25 := x.le_length_encode
  have hxw : x.H.A.x < 2 ^ w := lt_trans (Nat.lt_two_pow_self) h2x
  have huw : u < 2 ^ w := lt_trans hu h2x
  have hXlt : groupOf x.H.A.x x.H.A.b j u < numGroups x.H.A.x x.H.A.b j := groupOf_lt_numGroups hu
  have hszle : groupSize x.H.A.x x.H.A.b j ≤ 2 ^ x.H.A.x := by
    have := numGroups_mul_groupSize (x := x.H.A.x) (b := x.H.A.b) (j := j)
    have h1 : 1 ≤ numGroups x.H.A.x x.H.A.b j := Nat.one_le_two_pow
    rw [← this]; exact Nat.le_mul_of_pos_left _ h1
  have hidxw := x.ctrIdx_lt_pow hb hj hXlt
  let M : (ℕ → ℕ) → Prop := fun mem => ListAt mem b x.encode ∧
    ∀ a, (a < b ∨ b + x.encode.length ≤ a) → mem a = mem0 a
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = Function.update R 13 (x.H.A.x - j * x.H.A.b) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2, R2 = Function.update R1 14 (groupOf x.H.A.x x.H.A.b j u) := ⟨_, rfl⟩
  obtain ⟨R3, hR3⟩ : ∃ R3, R3 = Function.update R2 15 (groupSize x.H.A.x x.H.A.b j) := ⟨_, rfl⟩
  obtain ⟨R4, hR4⟩ : ∃ R4, R4 = Function.update R3 16 (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) := ⟨_, rfl⟩
  obtain ⟨R5, hR5⟩ : ∃ R5, R5 = Function.update R4 17 (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) := ⟨_, rfl⟩
  obtain ⟨R6, hR6⟩ : ∃ R6, R6 = Function.update R5 18 (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) := ⟨_, rfl⟩
  have rg : ∀ r, r < 13 → R6 r = R r := by
    intro r hr
    subst hR6 hR5 hR4 hR3 hR2 hR1
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  have rg1 : ∀ r, r < 13 → R1 r = R r := by
    intro r hr; subst hR1; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega
  have rg2 : ∀ r, r < 13 → R2 r = R r := by
    intro r hr; subst hR2 hR1; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega
  have rg3 : ∀ r, r < 13 → R3 r = R r := by
    intro r hr; subst hR3 hR2 hR1; simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  have rg4 : ∀ r, r < 13 → R4 r = R r := by
    intro r hr; subst hR4 hR3 hR2 hR1; simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  have rg5 : ∀ r, r < 13 → R5 r = R r := by
    intro r hr; subst hR5 hR4 hR3 hR2 hR1; simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  have r1_13 : R1 13 = x.H.A.x - j * x.H.A.b := by rw [hR1]; simp
  have r2_13 : R2 13 = x.H.A.x - j * x.H.A.b := by rw [hR2, ← r1_13]; simp
  have r2_14 : R2 14 = (groupOf x.H.A.x x.H.A.b j u) := by rw [hR2]; simp
  have r3_14 : R3 14 = (groupOf x.H.A.x x.H.A.b j u) := by rw [hR3, ← r2_14]; simp
  have r4_14 : R4 14 = (groupOf x.H.A.x x.H.A.b j u) := by rw [hR4, ← r3_14]; simp
  have r5_15 : R5 15 = (groupSize x.H.A.x x.H.A.b j) := by rw [hR5, hR4, hR3]; simp
  have r5_16 : R5 16 = (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) := by rw [hR5, hR4]; simp
  have t1 : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 13 (.bin .sub (readHdr 5) (.bin .mul (.reg 11) (readHdr 6))))
      (normalPost fun s => s.regs = R1 ∧ M s.mem) (fun _ => (Expr.bin .sub (readHdr 5) (.bin .mul (.reg 11) (readHdr 6))).size + 1) := by
    rw [hR1]
    exact triple_assign_exact fun s hs hm => by
      have h5 := x.eval_readHdr hb (by rw [hs, hR0]) hm.1 (k := 5) (by norm_num)
      have h6 := x.eval_readHdr hb (by rw [hs, hR0]) hm.1 (k := 6) (by norm_num)
      simp [HierConcrete.header] at h5 h6
      exact Expr.eval_sub h5 (Expr.eval_mul (Expr.eval_reg_of_eq (by rw [hs, hR11])) h6 hjb) hxw
  have t2 : Triple w p (fun s => s.regs = R1 ∧ M s.mem)
      (.assign 14 (.bin .shiftRight (.reg 10) (.reg 13)))
      (normalPost fun s => s.regs = R2 ∧ M s.mem) (fun _ => (Expr.bin .shiftRight (.reg 10) (.reg 13)).size + 1) := by
    rw [hR2]
    exact triple_assign_exact fun s hs hm => by
      have e := Expr.eval_shiftRight (w := w) (st := s) (a := .reg 10) (b := .reg 13)
        (Expr.eval_reg_of_eq (v := u) (by rw [hs, rg1 10 (by norm_num), hR10]))
        (Expr.eval_reg_of_eq (v := x.H.A.x - j * x.H.A.b) (by rw [hs, r1_13])) huw
      rw [e, ← groupOf_eq_shiftRight]
  have t3 : Triple w p (fun s => s.regs = R2 ∧ M s.mem)
      (.assign 15 (.bin .shiftLeft (.const 1) (.reg 13)))
      (normalPost fun s => s.regs = R3 ∧ M s.mem) (fun _ => (Expr.bin .shiftLeft (.const 1) (.reg 13)).size + 1) := by
    rw [hR3]
    exact triple_assign_exact fun s hs hm => by
      have e := Expr.eval_shiftLeft (w := w) (st := s) (a := .const 1) (b := .reg 13)
        (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (v := x.H.A.x - j * x.H.A.b) (by rw [hs, r2_13]))
        (by rw [← groupSize_eq_shiftLeft]; omega)
      rw [e, ← groupSize_eq_shiftLeft]
  have t4 : Triple w p (fun s => s.regs = R3 ∧ M s.mem)
      (.assign 16 (.bin .add (readSec numSec 0 19 (ctrWord 19)) (.reg 12)))
      (normalPost fun s => s.regs = R4 ∧ M s.mem) (fun _ => (Expr.bin .add (readSec numSec 0 19 (ctrWord 19)) (.reg 12)).size + 1) := by
    rw [hR4]
    exact triple_assign_exact fun s hs hm => by
      have h0 : s.regs 0 = b := by rw [hs, rg3 0 (by norm_num), hR0]
      have hc := x.eval_ctrWord hb h0 (by rw [hs, rg3 11 (by norm_num), hR11])
        (by rw [hs, r3_14]) hm.1 hj hXlt
      have hl' : ListAt s.mem b (layoutList x.sections) := hm.1
      have hr := eval_readSec' (w := w) hl' hb h0
        (i := 19) (by rw [x.length_sections']; norm_num) hc.2 (x.ctrIdx_lt_19 hj hXlt)
      rw [x.length_sections', x.getD_ctr_19 hj hXlt] at hr
      exact Expr.eval_add hr (Expr.eval_reg_of_eq (by rw [hs, rg3 12 (by norm_num), hR12]))
        (by omega)
  have t5 : Triple w p (fun s => s.regs = R4 ∧ M s.mem)
      (.assign 17 (readSec numSec 0 18 (ctrWord 18)))
      (normalPost fun s => s.regs = R5 ∧ M s.mem) (fun _ => (readSec numSec 0 18 (ctrWord 18)).size + 1) := by
    rw [hR5]
    exact triple_assign_exact fun s hs hm => by
      have h0 : s.regs 0 = b := by rw [hs, rg4 0 (by norm_num), hR0]
      have hc := x.eval_ctrWord hb h0 (by rw [hs, rg4 11 (by norm_num), hR11])
        (by rw [hs, r4_14]) hm.1 hj hXlt
      have hl' : ListAt s.mem b (layoutList x.sections) := hm.1
      have hr := eval_readSec' (w := w) hl' hb h0
        (i := 18) (by rw [x.length_sections']; norm_num) hc.1 (x.ctrIdx_lt_18 hj hXlt)
      rw [x.length_sections', x.getD_ctr_18 hj hXlt] at hr
      exact hr
  have t6 : Triple w p (fun s => s.regs = R5 ∧ M s.mem)
      (.cond (.bin .lt (.reg 15) (.bin .mul (.const 4) (.reg 16)))
        (.assign 18 (.reg 15)) (.assign 18 (.reg 16)))
      (normalPost fun s => s.regs = R6 ∧ M s.mem) (fun _ => 10) := by
    have hev : ∀ s : State, s.regs = R5 ∧ M s.mem →
        (Expr.bin .lt (.reg 15) (.bin .mul (.const 4) (.reg 16))).eval w s =
          some (if (groupSize x.H.A.x x.H.A.b j) < 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) then 1 else 0) := by
      intro s hs
      exact Expr.eval_lt_op (Expr.eval_reg_of_eq (by rw [hs.1, r5_15]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [hs.1, r5_16]))
          (by omega)) (by omega)
    by_cases hcmp : (groupSize x.H.A.x x.H.A.b j) < 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)
    · have hO : (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) := by simp only [newOwn, hcmp, ite_true]
      refine (Triple.cond (val := fun _ => if (groupSize x.H.A.x x.H.A.b j) < 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) then 1 else 0) hev
        ((triple_assign_exact (R := R5) (r := 18) (v := (groupSize x.H.A.x x.H.A.b j))
          fun s hs _ => Expr.eval_reg_of_eq (by rw [hs, r5_15])).conseq (fun s h => h.1)
          (fun o s h => ?_) (fun _ _ => le_refl _))
        (fun s ω h => by simp [hcmp] at h) (T_f := fun _ => 0)).mono_cost ?_
      · cases o with
        | normal => exact ⟨by rw [h.1, hR6, hO], h.2⟩
        | returned => exact h.elim
      · intro _ _; simp [hcmp, Expr.size]
    · have hO : (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) := by simp only [newOwn, hcmp, ite_false]
      refine (Triple.cond (val := fun _ => if (groupSize x.H.A.x x.H.A.b j) < 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) then 1 else 0) hev
        (fun s ω h => by simp [hcmp] at h) (T_t := fun _ => 0)
        ((triple_assign_exact (R := R5) (r := 18) (v := (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ))
          fun s hs _ => Expr.eval_reg_of_eq (by rw [hs, r5_16])).conseq (fun s h => h.1)
          (fun o s h => ?_) (fun _ _ => le_refl _))).mono_cost ?_
      · cases o with
        | normal => exact ⟨by rw [h.1, hR6, hO], h.2⟩
        | returned => exact h.elim
      · intro _ _; simp [hcmp, Expr.size]
  -- the two stores
  set x1 := x.withSt { x.ms.st with loss := { x.ms.st.loss with
    own := setAt x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) } } with hx1
  have hsec1 : x1.sections = x.sections.set 18 ((x.sections.getD 18 []).set (x.ctrIdx j (groupOf x.H.A.x x.H.A.b j u)) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ))) :=
    x.sections_setOwn hj hXlt (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ))
  have hlen1 : x1.encode.length = x.encode.length := by
    show (layoutList x1.sections).length = (layoutList x.sections).length
    rw [hsec1, length_layoutList_set_set]
  have hb1 : b + x1.encode.length < 2 ^ w := by rw [hlen1]; exact hb
  have r6_0 : R6 0 = b := by rw [rg 0 (by norm_num), hR0]
  have r6_11 : R6 11 = j := by rw [rg 11 (by norm_num), hR11]
  have r6_14 : R6 14 = (groupOf x.H.A.x x.H.A.b j u) := by rw [hR6, hR5, hR4, ← r3_14]; simp
  have r6_16 : R6 16 = (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) := by rw [hR6, ← r5_16]; simp
  have r6_18 : R6 18 = (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) := by rw [hR6]; simp
  have t7 : Triple w p (fun s => s.regs = R6 ∧ M s.mem)
      (.store (secAddr numSec 0 18 (ctrWord 18)) (.reg 18))
      (normalPost fun s => s.regs = R6 ∧ ListAt s.mem b x1.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => (secAddr numSec 0 18 (ctrWord 18)).size + (Expr.reg 18).size + 1) := by
    have t := triple_writeSec' (w := w) (p := p) (P := fun s => s.regs = R6 ∧ M s.mem) (b := b)
      (bs := x.sections) (r := 0) (by rw [x.length_sections']; norm_num)
      (ke := ctrWord 18) (ve := .reg 18) (k := fun _ => x.ctrIdx j (groupOf x.H.A.x x.H.A.b j u)) (v := fun _ => (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)))
      (fun s hs => ⟨hs.2.1, by rw [hs.1, r6_0],
        (x.eval_ctrWord hb (by rw [hs.1, r6_0]) (by rw [hs.1, r6_11]) (by rw [hs.1, r6_14])
          hs.2.1 hj hXlt).1, x.ctrIdx_lt_18 hj hXlt, Expr.eval_reg_of_eq (by rw [hs.1, r6_18])⟩) hb
    rw [x.length_sections'] at t
    refine t.strengthen_post fun o s h => ?_
    cases o with
    | normal =>
      obtain ⟨s0, hs0, hregs, _, hl, hfr⟩ := h
      refine ⟨hregs.trans hs0.1, ?_, fun a ha => (hfr a ha).trans (hs0.2.2 a ha)⟩
      show ListAt s.mem b (layoutList x1.sections)
      rw [hsec1]; exact hl
    | returned => exact h.elim
  have hsec2 : (x.setCtr j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)).sections =
      x1.sections.set 19 ((x1.sections.getD 19 []).set (x1.ctrIdx j (groupOf x.H.A.x x.H.A.b j u)) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) :=
    x1.sections_setSum hj hXlt (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)
  have t8 : Triple w p (fun s => s.regs = R6 ∧ ListAt s.mem b x1.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (.store (secAddr numSec 0 19 (ctrWord 19)) (.reg 16))
      (normalPost fun s => s.regs = R6 ∧ ListAt s.mem b (x.setCtr j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)).encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => (secAddr numSec 0 19 (ctrWord 19)).size + (Expr.reg 16).size + 1) := by
    have t := triple_writeSec' (w := w) (p := p)
      (P := fun s => s.regs = R6 ∧ ListAt s.mem b x1.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a) (b := b)
      (bs := x1.sections) (r := 0) (by rw [x1.length_sections']; norm_num)
      (ke := ctrWord 19) (ve := .reg 16) (k := fun _ => x1.ctrIdx j (groupOf x.H.A.x x.H.A.b j u)) (v := fun _ => (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ))
      (fun s hs => ⟨hs.2.1, by rw [hs.1, r6_0],
        (x1.eval_ctrWord hb1 (by rw [hs.1, r6_0]) (by rw [hs.1, r6_11]) (by rw [hs.1, r6_14])
          hs.2.1 hj hXlt).2, x1.ctrIdx_lt_19 hj hXlt, Expr.eval_reg_of_eq (by rw [hs.1, r6_16])⟩)
      hb1
    rw [x1.length_sections'] at t
    refine t.strengthen_post fun o s h => ?_
    cases o with
    | normal =>
      obtain ⟨s0, hs0, hregs, _, hl, hfr⟩ := h
      have hl1 : (layoutList x1.sections).length = x.encode.length := hlen1
      refine ⟨hregs.trans hs0.1, ?_, fun a ha => (hfr a (by rw [hl1]; exact ha)).trans
        (hs0.2.2 a ha)⟩
      show ListAt s.mem b (layoutList (x.setCtr j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)).sections)
      rw [hsec2]; exact hl
    | returned => exact h.elim
  have hR6' : R6 = ctrRegs R (x.H.A.x - j * x.H.A.b) (groupOf x.H.A.x x.H.A.b j u) (groupSize x.H.A.x x.H.A.b j) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) := by
    rw [hR6, hR5, hR4, hR3, hR2, hR1]; rfl
  refine ((Triple.seq_normal_const t1 (Triple.seq_normal_const t2 (Triple.seq_normal_const t3
    (Triple.seq_normal_const t4 (Triple.seq_normal_const t5 (Triple.seq_normal_const t6
      (Triple.seq_normal_const t7 t8))))))).conseq (fun s h => h) (fun o s h => ?_)
      (fun _ _ => ?_))
  · cases o with
    | normal => exact ⟨h.1.trans hR6', h.2⟩
    | returned => exact h.elim
  · simp [readHdr, readSec, secAddr, ctrWord, Expr.size]

end MinCostFlow.HierPaths

end
