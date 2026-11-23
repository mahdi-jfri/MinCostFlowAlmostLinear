module

public import MinCostFlow.HierPaths.DelProgClimb
public import MinCostFlow.HierPaths.LossCountersRun
public import MinCostFlow.HierPaths.DelProgRegFrame

/-!
# The leaf step of a first failure

When a terminal `u` fails directly for the first time, `Delete` sets its failed bit and adds one to
the own counter of its leaf group (`failStep`, `HierPaths/LossCounters.lean`). At the leaf depth
each group has one member, so the leaf group of `u` is `u` itself. `failLeafStmt` makes these two
writes. It also leaves the leaf depth in register `11` and `u` in register `14`, which the climb
and the enumeration use next.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- The block after the leaf step for `u`. -/
def HierConcrete.failLeaf (x : HierConcrete) (u : ℕ) : HierConcrete :=
  x.withSt { x.ms.st with loss := { x.ms.st.loss with
    failed := insert u x.ms.st.loss.failed,
    own := setAt x.ms.st.loss.own x.depth u (x.ms.st.loss.own x.depth u + 1) } }

/-- The leaf step: set the failed bit of the terminal in register `10`, then add one to its leaf
own counter. -/
def failLeafStmt : Stmt :=
  .seq (.store (secAddr numSec 0 13 (.reg 10)) (.const 1))
  (.seq (.assign 11 (readHdr 7))
  (.seq (.assign 14 (.reg 10))
  (.seq (.assign 17 (readSec numSec 0 18 (ctrWord 18)))
    (.store (secAddr numSec 0 18 (ctrWord 18)) (.bin .add (.reg 17) (.const 1))))))

theorem failLeafStmt_noRand : failLeafStmt.NoRand := by
  simp [failLeafStmt, Stmt.NoRand]

theorem failLeaf_triple {w : ℕ} {p : Program} (x : HierConcrete) {b u : ℕ} {R : ℕ → ℕ}
    {mem0 : ℕ → ℕ} (hR0 : R 0 = b) (hR10 : R 10 = u) (hu : u < x.H.A.C.numTerm)
    (hun : u < numGroups x.H.A.x x.H.A.b x.depth) (hb : b + x.encode.length < 2 ^ w)
    (hown : x.ms.st.loss.own x.depth u + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a) failLeafStmt
      (normalPost fun s => s.regs = Function.update (Function.update (Function.update R 11
          x.depth) 14 u) 17 (x.ms.st.loss.own x.depth u) ∧
        ListAt s.mem b (x.failLeaf u).encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => 200) := by
  have h25 := x.le_length_encode
  obtain ⟨x1, hx1⟩ : ∃ x1 : HierConcrete, x1 = x.withSt { x.ms.st with loss :=
      { x.ms.st.loss with failed := insert u x.ms.st.loss.failed } } := ⟨_, rfl⟩
  have hsec1 : x1.sections = x.sections.set 13 ((x.sections.getD 13 []).set u 1) := by
    rw [hx1]; exact x.sections_setFailed u
  have hlen1 : x1.encode.length = x.encode.length := by
    show (layoutList x1.sections).length = (layoutList x.sections).length
    rw [hsec1, length_layoutList_set_set]
  have hb1 : b + x1.encode.length < 2 ^ w := by rw [hlen1]; exact hb
  have hd1 : x1.depth = x.depth := by rw [hx1]; rfl
  have hown1 : x1.ms.st.loss.own = x.ms.st.loss.own := by rw [hx1]; rfl
  have hun1 : u < numGroups x1.H.A.x x1.H.A.b x1.depth := by rw [hx1]; exact hun
  -- the failed bit
  have t1 : Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (.store (secAddr numSec 0 13 (.reg 10)) (.const 1))
      (normalPost fun s => s.regs = R ∧ ListAt s.mem b x1.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => (secAddr numSec 0 13 (.reg 10)).size + (Expr.const 1).size + 1) := by
    have t := triple_writeSec' (w := w) (p := p) (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a) (b := b)
      (bs := x.sections) (r := 0) (i := 13) (by rw [x.length_sections']; norm_num)
      (ke := .reg 10) (ve := .const 1) (k := fun _ => u) (v := fun _ => 1)
      (fun s hs => ⟨hs.2.1, by rw [hs.1, hR0], Expr.eval_reg_of_eq (by rw [hs.1, hR10]),
        by simp [HierConcrete.sections]; exact hu, Expr.eval_const (by omega)⟩) hb
    rw [x.length_sections'] at t
    refine t.strengthen_post fun o s h => ?_
    cases o with
    | normal =>
      obtain ⟨s0, hs0, hregs, _, hl, hfr⟩ := h
      refine ⟨hregs.trans hs0.1, ?_, fun a ha => (hfr a ha).trans (hs0.2.2 a ha)⟩
      show ListAt s.mem b (layoutList x1.sections)
      rw [hsec1]; exact hl
    | returned => exact h.elim
  -- the reads
  let M : (ℕ → ℕ) → Prop := fun mem => ListAt mem b x1.encode ∧
    ∀ a, (a < b ∨ b + x.encode.length ≤ a) → mem a = mem0 a
  have t2 : Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign 11 (readHdr 7))
      (normalPost fun s => s.regs = Function.update R 11 x.depth ∧ M s.mem)
      (fun _ => (readHdr 7).size + 1) :=
    triple_assign_exact fun s hs hm => by
      have h7 := x1.eval_readHdr hb1 (by rw [hs, hR0]) hm.1 (k := 7) (by norm_num)
      simp [HierConcrete.header] at h7
      rw [h7, hd1]
  have t3 : Triple w p (fun s => s.regs = Function.update R 11 x.depth ∧ M s.mem)
      (.assign 14 (.reg 10))
      (normalPost fun s => s.regs = Function.update (Function.update R 11 x.depth) 14 u ∧ M s.mem)
      (fun _ => (Expr.reg 10).size + 1) :=
    triple_assign_exact fun s hs hm => Expr.eval_reg_of_eq (by rw [hs]; simpa using hR10)
  obtain ⟨R3, hR3⟩ : ∃ R3, R3 = Function.update (Function.update R 11 x.depth) 14 u := ⟨_, rfl⟩
  have r3_0 : R3 0 = b := by rw [hR3]; simpa using hR0
  have r3_11 : R3 11 = x1.depth := by rw [hR3, hd1]; simp
  have r3_14 : R3 14 = u := by rw [hR3]; simp
  have t4 : Triple w p (fun s => s.regs = R3 ∧ M s.mem)
      (.assign 17 (readSec numSec 0 18 (ctrWord 18)))
      (normalPost fun s => s.regs = Function.update R3 17 (x.ms.st.loss.own x.depth u) ∧ M s.mem)
      (fun _ => (readSec numSec 0 18 (ctrWord 18)).size + 1) :=
    triple_assign_exact fun s hs hm => by
      have h0 : s.regs 0 = b := by rw [hs, r3_0]
      have hc := x1.eval_ctrWord hb1 h0 (by rw [hs, r3_11]) (by rw [hs, r3_14]) hm.1 le_rfl hun1
      have hl' : ListAt s.mem b (layoutList x1.sections) := hm.1
      have hr := eval_readSec' (w := w) hl' hb1 h0
        (i := 18) (by rw [x1.length_sections']; norm_num) hc.1 (x1.ctrIdx_lt_18 le_rfl hun1)
      rw [x1.length_sections', x1.getD_ctr_18 le_rfl hun1, hown1, hd1] at hr
      exact hr
  obtain ⟨R4, hR4⟩ : ∃ R4, R4 = Function.update R3 17 (x.ms.st.loss.own x.depth u) := ⟨_, rfl⟩
  have r4_0 : R4 0 = b := by rw [hR4]; simpa using r3_0
  have r4_11 : R4 11 = x1.depth := by rw [hR4]; simpa using r3_11
  have r4_14 : R4 14 = u := by rw [hR4]; simpa using r3_14
  have r4_17 : R4 17 = x.ms.st.loss.own x.depth u := by rw [hR4]; simp
  have hsec2 : (x.failLeaf u).sections =
      x1.sections.set 18 ((x1.sections.getD 18 []).set (x1.ctrIdx x1.depth u)
        (x.ms.st.loss.own x.depth u + 1)) := by
    have := x1.sections_setOwn (j := x1.depth) (g := u) le_rfl hun1
      (x.ms.st.loss.own x.depth u + 1)
    rw [← this, hx1]; rfl
  have t5 : Triple w p (fun s => s.regs = R4 ∧ M s.mem)
      (.store (secAddr numSec 0 18 (ctrWord 18)) (.bin .add (.reg 17) (.const 1)))
      (normalPost fun s => s.regs = R4 ∧ ListAt s.mem b (x.failLeaf u).encode ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a)
      (fun _ => (secAddr numSec 0 18 (ctrWord 18)).size +
        (Expr.bin .add (.reg 17) (.const 1)).size + 1) := by
    have t := triple_writeSec' (w := w) (p := p) (P := fun s => s.regs = R4 ∧ M s.mem) (b := b)
      (bs := x1.sections) (r := 0) (i := 18) (by rw [x1.length_sections']; norm_num)
      (ke := ctrWord 18) (ve := .bin .add (.reg 17) (.const 1))
      (k := fun _ => x1.ctrIdx x1.depth u) (v := fun _ => x.ms.st.loss.own x.depth u + 1)
      (fun s hs => ⟨hs.2.1, by rw [hs.1, r4_0],
        (x1.eval_ctrWord hb1 (by rw [hs.1, r4_0]) (by rw [hs.1, r4_11]) (by rw [hs.1, r4_14])
          hs.2.1 le_rfl hun1).1, x1.ctrIdx_lt_18 le_rfl hun1,
        Expr.eval_add (Expr.eval_reg_of_eq (by rw [hs.1, r4_17])) (Expr.eval_const (by omega))
          hown⟩) hb1
    rw [x1.length_sections'] at t
    refine t.strengthen_post fun o s h => ?_
    cases o with
    | normal =>
      obtain ⟨s0, hs0, hregs, _, hl, hfr⟩ := h
      refine ⟨hregs.trans hs0.1, ?_, fun a ha => ?_⟩
      · show ListAt s.mem b (layoutList (x.failLeaf u).sections)
        rw [hsec2]; exact hl
      · have ha' : a < b ∨ b + (layoutList x1.sections).length ≤ a := by
          have : (layoutList x1.sections).length = x.encode.length := hlen1
          rw [this]; exact ha
        exact (hfr a ha').trans (hs0.2.2 a ha)
    | returned => exact h.elim
  have t := Triple.seq_normal_const t1 (Triple.seq_normal_const t2 (Triple.seq_normal_const t3
    ((hR3 ▸ Triple.seq_normal_const t4 (hR4 ▸ t5)))))
  refine (t.strengthen_post fun o s h => ?_).mono_cost fun _ _ => ?_
  · cases o with
    | normal => exact h
    | returned => exact h.elim
  · decide

/-! ### The whole failure step -/

/-- The loss state after the leaf step of `failStep`, before the enumeration of `u`. -/
def failSt1 (x b u : ℕ) (st : LossState) : LossState :=
  ⟨setAt st.own (leafDepth x b) (groupOf x b (leafDepth x b) u)
      (st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) + 1), st.sum,
    insert u st.failed, st.glob, st.updates + 1, st.enumerated⟩

theorem failStep_eq (x b u : ℕ) (st : LossState) :
    failStep x b u st =
      ((climb x b u (leafDepth x b) 1 (enumerate (failSt1 x b u st) [u]).1).1,
        (enumerate (failSt1 x b u st) [u]).2 ++
          (climb x b u (leafDepth x b) 1 (enumerate (failSt1 x b u st) [u]).1).2) := rfl

/-- A first direct failure of the terminal in register `10`: the leaf step, the enumeration of the
terminal itself (its leaf group has one member), then the climb from the leaf depth. -/
def failStepStmt : Stmt :=
  .seq failLeafStmt (.seq (.assign 20 (.reg 10))
    (.seq enumBody (.seq (.assign 12 (.const 1)) climbStmt)))

theorem failStepStmt_noRand : failStepStmt.NoRand := by
  simp [failStepStmt, Stmt.NoRand, failLeafStmt_noRand, climbStmt_noRand, enumBody]

/-- The failure starts with one leaf step, then charges the climb by its events. -/
def delFailureCost (x b u : ℕ) (L : LossState) : ℕ :=
  delClimbCost (enumerate (failSt1 x b u L) [u]).1 (failStep x b u L).1 + 400

theorem delFailureCost_le (x b u : ℕ) (L : LossState) :
    delFailureCost x b u L ≤ leafDepth x b * (130 * 2 ^ x + 700) + 408 := by
  unfold delFailureCost
  rw [failStep_eq]
  have h := delClimbCost_le x b u (leafDepth x b) 1 (enumerate (failSt1 x b u L) [u]).1
  dsimp only at h ⊢
  omega

theorem delFailureCost_events_le (x b u : ℕ) (L : LossState) :
    delFailureCost x b u L ≤ delClimbCost L (failStep x b u L).1 + 400 := by
  unfold delFailureCost delClimbCost
  simp only [enumerate, failSt1, List.length_singleton]
  omega

theorem failStep_triple {w : ℕ} {p : Program} (x : HierConcrete) {F : Finset ℕ}
    {b u WB c0 : ℕ} {R : ℕ → ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hR10 : R 10 = u) (hR22 : R 22 = WB) (hR23 : R 23 = c0)
    (hL0 : L0.length = c0) (hinv : LossInv x.H.A.x x.H.A.b F x.ms.st.loss)
    (hu : u < 2 ^ x.H.A.x) (huF : u ∉ F) (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x)
    (hb0 : 0 < x.H.A.b) (hown : x.ms.st.loss.own x.depth u + 1 < 2 ^ w)
    (hb : b + x.encode.length < 2 ^ w) (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w)
    (hd : x.depth < 2 ^ w) (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hblk : b + x.encode.length ≤ WB)
    (hw : WB + c0 + (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2.length + 2 ^ x.H.A.x <
      2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) failStepStmt
      (normalPost fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 22 = WB ∧
        s.regs 23 = c0 + (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2.length ∧
        ListAt s.mem b (x.withLoss (failStep x.H.A.x x.H.A.b u x.ms.st.loss).1).encode ∧
        ListAt s.mem WB (L0 ++ (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
          WB + c0 + (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2.length ≤ a) →
          s.mem a = mem0 a)
      (fun _ => delFailureCost x.H.A.x x.H.A.b u x.ms.st.loss) := by
  have h25 := x.le_length_encode
  have hgs1 : groupSize x.H.A.x x.H.A.b x.depth = 1 := groupSize_eq_one hb0 le_rfl
  have hlu : groupOf x.H.A.x x.H.A.b x.depth u = u := by
    rw [groupOf, hgs1, Nat.div_one]
  have hun : u < numGroups x.H.A.x x.H.A.b x.depth := by
    have := numGroups_mul_groupSize (x := x.H.A.x) (b := x.H.A.b) (j := x.depth)
    rw [hgs1, Nat.mul_one] at this; omega
  have hfs := failStep_eq x.H.A.x x.H.A.b u x.ms.st.loss
  have hlenfs := congrArg (fun q => q.2.length) hfs
  simp only [List.length_append] at hlenfs
  -- the three blocks
  obtain ⟨y, hy⟩ : ∃ y : HierConcrete,
      y = x.withLoss (failSt1 x.H.A.x x.H.A.b u x.ms.st.loss) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : HierConcrete,
      z = x.withLoss (enumerate (failSt1 x.H.A.x x.H.A.b u x.ms.st.loss) [u]).1 := ⟨_, rfl⟩
  have hyenc : (x.failLeaf u).encode = y.encode := by
    rw [hy]
    show (x.withLoss { x.ms.st.loss with failed := insert u x.ms.st.loss.failed, own := setAt x.ms.st.loss.own x.depth u (x.ms.st.loss.own x.depth u + 1) }).encode = _
    refine x.encode_withLoss_congr ?_ rfl rfl rfl
    show _ = setAt x.ms.st.loss.own x.depth (groupOf x.H.A.x x.H.A.b x.depth u)
      (x.ms.st.loss.own x.depth (groupOf x.H.A.x x.H.A.b x.depth u) + 1)
    rw [hlu]
  have hylen : y.encode.length = x.encode.length := by
    rw [hy]; exact x.length_encode_withLoss _
  have hzlen : z.encode.length = x.encode.length := by
    rw [hz]; exact x.length_encode_withLoss _
  have hyglob : y.ms.st.loss.glob = x.ms.st.loss.glob := by rw [hy]; rfl
  have hzenc : (y.withGlob (enumSet y.ms.st.loss.glob u (u + 1))).encode = z.encode := by
    rw [hz, hy]
    show (x.withLoss { failSt1 x.H.A.x x.H.A.b u x.ms.st.loss with glob := enumSet x.ms.st.loss.glob u (u + 1) }).encode = _
    refine x.encode_withLoss_congr rfl rfl rfl ?_
    simp [enumSet, enumerate, failSt1]
  have hout1 : enumOut y.ms.st.loss.glob u (u + 1) =
      (enumerate (failSt1 x.H.A.x x.H.A.b u x.ms.st.loss) [u]).2 := by
    rw [hyglob]; simp only [enumOut, enumerate, failSt1, Nat.add_sub_cancel_left, List.range'_one]
    exact List.filter_congr fun v _ => by by_cases h : v ∈ x.ms.st.loss.glob <;> simp [h]
  have hzinv : ClimbInv z.H.A.x z.H.A.b F u z.depth 1 z.ms.st.loss := by
    rw [hz]; exact failStart_climbInv hinv huF
  -- step 1: the leaf step, keeping the work list
  refine fun st₀ ω₀ hst₀ => ?_
  have hL0m : ListAt mem0 WB L0 := by rw [← hst₀.2.2.2]; exact hst₀.2.2.1
  revert st₀ ω₀ hst₀
  show Triple _ _ _ _ _ _
  have hL0f : ∀ mem : ℕ → ℕ,
      (∀ a, (a < b ∨ b + x.encode.length ≤ a) → mem a = mem0 a) → ListAt mem WB L0 :=
    fun mem hfr => listAt_congr (fun i _ => (hfr _ (Or.inr (by omega))).symm) hL0m
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = Function.update (Function.update (Function.update R 11
      x.depth) 14 u) 17 (x.ms.st.loss.own x.depth u) := ⟨_, rfl⟩
  have r1 : ∀ r, r ≠ 11 → r ≠ 14 → r ≠ 17 → R1 r = R r := by
    intro r h1 h2 h3; rw [hR1]; simp [h1, h2, h3]
  have r1_11 : R1 11 = x.depth := by rw [hR1]; simp
  have t1 : Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) failLeafStmt (normalPost fun s => s.regs = R1 ∧ (ListAt s.mem b y.encode ∧
          ListAt s.mem WB L0 ∧ ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a))
        (fun _ => 200) := by
    refine ((failLeaf_triple (w := w) (p := p) x (mem0 := mem0) hR0 hR10 (by omega) hun hb
      hown).weaken_pre fun s hs => ⟨hs.1, hs.2.1, fun a _ => by rw [hs.2.2.2]⟩).strengthen_post
      fun o s h => ?_
    cases o with
    | normal =>
      exact ⟨by rw [h.1, hR1], by rw [← hyenc]; exact h.2.1, hL0f s.mem h.2.2, h.2.2⟩
    | returned => exact h.elim
  -- step 2: the terminal to enumerate
  obtain ⟨E, hE⟩ : ∃ E, E = enumerate (failSt1 x.H.A.x x.H.A.b u x.ms.st.loss) [u] := ⟨_, rfl⟩
  rw [← hE] at hfs hz hout1 hlenfs
  obtain ⟨R2, hR2⟩ : ∃ R2, R2 = Function.update R1 20 u := ⟨_, rfl⟩
  have r2 : ∀ r, r ≠ 11 → r ≠ 14 → r ≠ 17 → r ≠ 20 → R2 r = R r := by
    intro r h1 h2 h3 h4; rw [hR2, Function.update_of_ne h4]; exact r1 r h1 h2 h3
  have t2 : Triple w p (fun s => s.regs = R1 ∧ (ListAt s.mem b y.encode ∧
          ListAt s.mem WB L0 ∧ ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a))
      (.assign 20 (.reg 10))
      (normalPost fun s => s.regs = R2 ∧ (ListAt s.mem b y.encode ∧
          ListAt s.mem WB L0 ∧ ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a))
      (fun _ => (Expr.reg 10).size + 1) := by
    rw [hR2]
    exact triple_assign_exact (R := R1) (r := 20) (M := fun mem => ListAt mem b y.encode ∧
      ListAt mem WB L0 ∧ ∀ a, (a < b ∨ b + x.encode.length ≤ a) → mem a = mem0 a) fun s hs _ => Expr.eval_reg_of_eq (v := u)
      (by rw [hs, r1 10 (by norm_num) (by norm_num) (by norm_num), hR10])
  -- step 3: the enumeration of `u`
  have t3 := (enumBody_triple (w := w) (p := p) y (b := b) (WB := WB) (lo := u) (hi := u + 1)
    (c0 := c0) (R := R2) (L0 := L0) (mem0 := mem0)
    (by rw [r2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR0])
    (by rw [r2 22 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR22]) hL0
    (show u + 1 ≤ y.H.A.C.numTerm by rw [hy]; show u + 1 ≤ x.H.A.C.numTerm; omega) (by rw [hylen]; exact hblk)
    (by omega) le_rfl (Nat.lt_succ_self u)).weaken_pre
    (P' := fun s => s.regs = R2 ∧ (ListAt s.mem b y.encode ∧
          ListAt s.mem WB L0 ∧ ∀ a, (a < b ∨ b + x.encode.length ≤ a) → s.mem a = mem0 a))
    (fun s hs => ⟨by rw [hs.1, hR2]; simp, fun r _ _ _ => by rw [hs.1],
      by rw [hs.1, r2 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR23]
         simp [enumOut],
      by simp only [enumSet, Nat.sub_self, List.range'_zero, List.toFinset_nil,
           Finset.union_empty, HierConcrete.withGlob_self]
         exact hs.2.1,
      by simpa [enumOut] using hs.2.2.1,
      fun a ha _ => hs.2.2.2 a (by rw [← hylen]; exact ha)⟩)
  -- step 4: the climb
  have t4 : Triple w p (fun s => EnumInv y b WB u (u + 1) c0 R2 L0 mem0 (u + 1)
        { s with regs := Function.update s.regs 20 (u + 1) } ∧ s.regs 20 = u)
      (.seq (.assign 12 (.const 1)) climbStmt)
      (normalPost fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 22 = WB ∧
        s.regs 23 = c0 + (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2.length ∧
        ListAt s.mem b (x.withLoss (failStep x.H.A.x x.H.A.b u x.ms.st.loss).1).encode ∧
        ListAt s.mem WB (L0 ++ (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
          WB + c0 + (failStep x.H.A.x x.H.A.b u x.ms.st.loss).2.length ≤ a) →
          s.mem a = mem0 a)
      (fun _ => 2 + delClimbCost E.1 (failStep x.H.A.x x.H.A.b u x.ms.st.loss).1 + 1) := by
    intro s ω hs
    obtain ⟨⟨_, eregs, e23, ebl, ewl, efr⟩, _⟩ := hs
    have g : ∀ r, r ≠ 20 → r ≠ 23 → r ≠ 24 → s.regs r = R2 r := fun r h1 h2 h3 => by
      have := eregs r h1 h2 h3; simpa [Function.update_apply, h1] using this
    have g23 : s.regs 23 = c0 + E.2.length := by
      have : s.regs 23 = c0 + (enumOut y.ms.st.loss.glob u (u + 1)).length := by simpa using e23
      rw [this, hout1]
    have ebl' : ListAt s.mem b z.encode := by rw [← hzenc]; exact ebl
    have ewl' : ListAt s.mem WB (L0 ++ E.2) := by rw [← hout1]; exact ewl
    have tc := climb_triple (w := w) (p := p) z (F := F) (b := b) (u := u) (WB := WB)
      (c0 := c0 + E.2.length) (L0 := L0 ++ E.2) (mem0 := s.mem)
      (by rw [hz]; exact hnt) (by rw [hz]; exact hu) hzinv (by simp [hL0])
      (by rw [hzlen]; exact hb) (by rw [hz]; exact hdb) (by rw [hz]; exact hd)
      (by rw [hz]; exact h4x) (by rw [hzlen]; exact hblk)
      (by rw [hz]; show WB + (c0 + E.2.length) +
            (climb x.H.A.x x.H.A.b u (leafDepth x.H.A.x x.H.A.b) 1 E.1).2.length +
            2 ^ x.H.A.x < 2 ^ w
          rw [hfs] at hw; simp only [List.length_append] at hw; omega)
    have tA : Triple w p (fun s' => s' = s) (.assign 12 (.const 1))
        (normalPost fun s' => s'.regs 0 = b ∧ s'.regs 10 = u ∧ s'.regs 11 = z.depth ∧
          s'.regs 12 = 1 ∧ s'.regs 22 = WB ∧ s'.regs 23 = c0 + E.2.length ∧
          ListAt s'.mem b z.encode ∧ ListAt s'.mem WB (L0 ++ E.2) ∧ s'.mem = s.mem)
        (fun _ => (Expr.const 1).size + 1) :=
      Triple.assign (val := fun _ => 1) (fun s' hs' => Expr.eval_const (by omega))
        (fun s' hs' => by
          subst hs'
          refine ⟨?_, ?_, ?_, by simp, ?_, ?_, ebl', ewl', rfl⟩
          · simp only [Function.update_apply]
            rw [_root_.if_neg (by norm_num)]
            rw [g 0 (by norm_num) (by norm_num) (by norm_num),
              r2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR0]
          · simp only [Function.update_apply]
            rw [_root_.if_neg (by norm_num)]
            rw [g 10 (by norm_num) (by norm_num) (by norm_num),
              r2 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR10]
          · simp only [Function.update_apply]
            rw [_root_.if_neg (by norm_num)]
            rw [g 11 (by norm_num) (by norm_num) (by norm_num), hR2,
              Function.update_of_ne (by norm_num), r1_11, hz]; rfl
          · simp only [Function.update_apply]
            rw [_root_.if_neg (by norm_num)]
            rw [g 22 (by norm_num) (by norm_num) (by norm_num),
              r2 22 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hR22]
          · simp only [Function.update_apply]
            rw [_root_.if_neg (by norm_num)]
            exact g23)
    obtain ⟨o, s', c, hr, h, hc⟩ := (Triple.seq_normal_const tA tc) s ω rfl
    have hc' : c ≤ 2 + delClimbCost E.1 (failStep x.H.A.x x.H.A.b u x.ms.st.loss).1 + 1 := by
      rw [hz] at hc
      rw [hfs]
      exact hc
    refine ⟨o, s', c, hr, ?_, by omega⟩
    · cases o with
      | returned => exact h.elim
      | normal =>
        obtain ⟨g0, g10, g22, g23', gbl, gwl, gfr⟩ := h
        rw [hfs]
        refine ⟨g0, g10, g22, ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, ← Nat.add_assoc]; rw [hz] at g23'; exact g23'
        · rw [hz] at gbl; exact gbl
        · rw [← List.append_assoc]; rw [hz] at gwl; exact gwl
        · intro a ha ha2
          rw [List.length_append] at ha2
          have hza : a < b ∨ b + z.encode.length ≤ a := by rw [hzlen]; exact ha
          rcases ha2 with h2 | h2
          · rw [gfr a hza (Or.inl (by omega))]
            exact efr a (by rw [hylen]; exact ha) (Or.inl h2)
          · rw [gfr a hza (Or.inr (by
              rw [hz]; exact Nat.le_trans (Nat.le_of_eq (by simp only [Nat.add_assoc]; rfl)) h2))]
            exact efr a (by rw [hylen]; exact ha) (Or.inr (by rw [hout1]; omega))
  refine (Triple.seq_normal_const t1 (Triple.seq_normal_const t2
    (Triple.seq_normal_const t3 t4))).mono_cost fun _ _ => ?_
  simp only [Expr.size, delFailureCost]
  rw [hE]
  omega

/-- The failure step writes only registers below `25`. -/
theorem failStepStmt_writesBelow : Stmt.WritesBelow 25 failStepStmt := by
  simp [failStepStmt, failLeafStmt, enumBody, climbStmt, levelStmt, ctrStmt, enumStmt, forRange,
    forUp, Stmt.WritesBelow]
