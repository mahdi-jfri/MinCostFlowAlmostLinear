module

public import MinCostFlow.HierPaths.DelProgCursorCost

/-!
# Starting the Delete procedure

The first stage reserves the output region by placing scratch above it. It marks the edge,
scans its reverse list, and leaves the newly lost terminals in the first work list.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The lost list begins above the length word and the space for the reported vertices. -/
def delLostBase (h n : ℕ) : ℕ := h + 2 + 2 * n

/-- Set the heap and lost-list registers from the entry arguments and graph header. -/
def delEntrySetup : Stmt :=
  .seq (.assign 70 (.reg 2))
    (.seq (.assign 22 (.bin .add (.bin .add (.reg 2) (.const 2))
      (.bin .mul (.const 2) (readHdr 0))))
      (.seq (.assign 71 (.reg 22)) (.assign 23 (.const 0))))

theorem delEntrySetup_noRand : delEntrySetup.NoRand := by
  simp [delEntrySetup, Stmt.NoRand]

/-- The scratch setup preserves memory and the handle and edge registers. -/
theorem delEntrySetup_triple {w : ℕ} {p : Program} (x : HierConcrete) {b h : ℕ}
    {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop}
    (h0 : R 0 = b) (h2 : R 2 = h) (hb : b + x.encode.length < 2 ^ w)
    (hw : delLostBase h x.n < 2 ^ w) (hM : ∀ mem, M mem → ListAt mem b x.encode) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) delEntrySetup
      (normalPost fun s => s.regs =
        Function.update (Function.update (Function.update (Function.update R 70 h)
          22 (delLostBase h x.n)) 71 (delLostBase h x.n)) 23 0 ∧ M s.mem)
      (fun _ => 40) := by
  let wb := delLostBase h x.n
  let R₁ := Function.update R 70 h
  let R₂ := Function.update R₁ 22 wb
  let R₃ := Function.update R₂ 71 wb
  have H1 : Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign 70 (.reg 2))
      (normalPost fun s => s.regs = R₁ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hr _ => Expr.eval_reg_of_eq (hr ▸ h2)
  have H2 : Triple w p (fun s => s.regs = R₁ ∧ M s.mem)
      (.assign 22 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 2) (readHdr 0))))
      (normalPost fun s => s.regs = R₂ ∧ M s.mem) (fun _ => 24) := by
    refine (triple_assign_exact (v := wb) ?_).mono_cost (fun _ _ => by decide)
    intro s hs hm
    have hr0 : s.regs 0 = b := by simpa [hs, R₁] using h0
    have hr2 : s.regs 2 = h := by simpa [hs, R₁] using h2
    have hn := x.eval_readHdr hb hr0 (hM _ hm) (k := 0) (by decide)
    change (readHdr 0).eval w s = some x.n at hn
    unfold delLostBase at hw
    exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) hn (by omega)) hw
  have H3 : Triple w p (fun s => s.regs = R₂ ∧ M s.mem) (.assign 71 (.reg 22))
      (normalPost fun s => s.regs = R₃ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hr _ => Expr.eval_reg_of_eq (by simp [hr, R₂])
  have H4 : Triple w p (fun s => s.regs = R₃ ∧ M s.mem) (.assign 23 (.const 0))
      (normalPost fun s => s.regs = Function.update R₃ 23 0 ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ _ _ => Expr.eval_const (Nat.two_pow_pos _)
  exact (Triple.seq_normal_const H1 (Triple.seq_normal_const H2
    (Triple.seq_normal_const H3 H4))).mono_cost (fun _ _ => by decide)

/-- The first three steps of the entry, ending with the lost-terminal work list. -/
def delEntryStart : Stmt := .seq delEntrySetup (.seq markDelStmt (.seq scanSetupStmt scanStmt))

theorem delEntryStart_noRand : delEntryStart.NoRand := by
  simp [delEntryStart, Stmt.NoRand, delEntrySetup_noRand, markDelStmt_noRand,
    scanSetupStmt_noRand, scanStmt_noRand]

/-- Marking the deleted bit and count preserves the block length. -/
theorem HierConcrete.length_encode_markDeleted (x : HierConcrete) {e : ℕ}
    (he : e ∉ x.ms.st.deleted) : (x.markDeleted e).encode.length = x.encode.length := by
  show (layoutList (x.markDeleted e).sections).length = (layoutList x.sections).length
  rw [x.sections_markDeleted he, length_layoutList_set_set, length_layoutList_set_set]

/-- The state encoded after marking the edge and running the loss counters. -/
def HierConcrete.afterDelLoss (x : HierConcrete) (e : ℕ) : HierConcrete :=
  (x.markDeleted e).withLoss (x.H.A.newLoss x.ms.st e)

/-- The work to start Delete, including the actual losses found by the reverse scan. -/
def delEntryStartCost (x : HierConcrete) (e : ℕ) : ℕ :=
  let y := x.markDeleted e
  let l := x.H.A.revList e
  rangeCost (delScanStepCost y l (y.revStart e)) (y.revStart e) (y.revStart e + l.length) +
    9 * l.length + 150

/-- Run the mark and loss scan, preserving every cell outside the block and the lost list. -/
theorem delEntryStart_triple {w : ℕ} {p : Program} (x : HierConcrete) {b e h : ℕ}
    {R mem0 : ℕ → ℕ} (h0 : R 0 = b) (h1 : R 1 = e) (h2 : R 2 = h)
    (he : e < x.m) (hnew : e ∉ x.ms.st.deleted)
    (hA : x.H.A.Spec x.ms.abs.G x.H.ξ x.H.κ)
    (hinv : x.H.A.DelInv x.ms.abs.G x.ms.st)
    (hb : b + x.encode.length ≤ h)
    (hcw : x.ms.st.deleted.card + 1 < 2 ^ w)
    (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w) (hd : x.depth < 2 ^ w)
    (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hw : delLostBase h x.n + 2 * 2 ^ x.H.A.x < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delEntryStart (normalPost fun s =>
        let lost := x.H.A.newLost x.ms.st e
        let wb := delLostBase h x.n
        s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧ s.regs 23 = lost.length ∧
        ListAt s.mem b (x.afterDelLoss e).encode ∧ ListAt s.mem wb lost ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < wb ∨ wb + lost.length ≤ j) → s.mem j = mem0 j)
      (fun _ => delEntryStartCost x e) := by
  let wb := delLostBase h x.n
  let regs := Function.update (Function.update (Function.update (Function.update R 70 h)
    22 wb) 71 wb) 23 0
  let y := x.markDeleted e
  let lost := x.H.A.newLost x.ms.st e
  have hwb : h ≤ wb := by unfold wb delLostBase; omega
  have hby : b + y.encode.length ≤ h := by rw [x.length_encode_markDeleted hnew]; exact hb
  have hb' : b + x.encode.length < 2 ^ w := by omega
  have hby' : b + y.encode.length < 2 ^ w := by omega
  have hfit : b + y.encode.length ≤ wb := hby.trans hwb
  have H := delEntrySetup_triple (w := w) (p := p) (M := fun mem =>
    ListAt mem b x.encode ∧ mem = mem0) x h0 h2 hb' (by omega : wb < 2 ^ w) (fun _ h => h.1)
  have HM := markDel_triple (w := w) (p := p) (R := regs) (mem0 := mem0)
    x (by simpa [regs] using h0) (by simpa [regs] using h1) he hnew hb' hcw
  have hHL : ∀ t ∈ y.H.A.revList e, t < 2 ^ y.H.A.x := by
    intro t ht
    change t < 2 ^ x.H.A.x
    rw [← hA.numTerm_eq]
    exact hA.rev_lt e t ht
  have tail : Triple w p (fun s => s.regs = regs ∧ ListAt s.mem b y.encode ∧
      ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j) (.seq scanSetupStmt scanStmt)
      (normalPost fun s => s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧
        s.regs 23 = lost.length ∧ ListAt s.mem b (x.afterDelLoss e).encode ∧
        ListAt s.mem wb lost ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < wb ∨ wb + lost.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delScanStepCost y (y.H.A.revList e) (y.revStart e)) (y.revStart e)
        (y.revStart e + (y.H.A.revList e).length) + 9 * (y.H.A.revList e).length + 68) := by
    intro s ω hs
    have HS := deleteScan_triple (w := w) (p := p) (R := regs) (mem0 := s.mem)
      (WB := wb) (c0 := 0) (L0 := []) y (by simpa [regs] using h0) (by simpa [regs] using h1)
      (by simp [regs]) (by simp [regs]) he hinv.loss hHL rfl hA.numTerm_eq hA.b_pos
      hby' hdb hd h4x hfit (by change delLostBase h x.n + 2 * 2 ^ x.H.A.x < 2 ^ w; exact hw)
    have HF := Triple.regs_frame (n := 28)
      (show Stmt.WritesBelow 28 (.seq scanSetupStmt scanStmt) by
        simp [scanSetupStmt, scanStmt, scanBody, forRange, forUp, Stmt.WritesBelow,
          failStepStmt, failLeafStmt, enumBody, climbStmt, levelStmt, ctrStmt, enumStmt]) HS regs
    obtain ⟨o, s', c, hr, hp, hc⟩ := HF s ω
      ⟨⟨hs.1, hs.2.1, (fun _ hh => by simp at hh), rfl⟩, fun j _ => congrFun hs.1 j⟩
    cases o <;> try exact False.elim hp.1
    obtain ⟨⟨h0', _, h23, hblock, hlist, hf⟩, hregs⟩ := hp
    have hLost : (scan y.H.A.x y.H.A.b y.ms.st.loss (y.H.A.revList e)).2 = lost := rfl
    rw [hLost, Nat.zero_add] at h23
    rw [hLost, List.nil_append] at hlist
    rw [hLost, Nat.add_zero] at hf
    refine ⟨_, s', c, hr, ?_, ?_⟩
    · refine ⟨h0', by simp [hregs 70 (by decide), regs], by simp [hregs 71 (by decide), regs],
        h23, hblock, hlist, ?_⟩
      intro j hj hscratch
      have hj' : j < b ∨ b + y.encode.length ≤ j := by rwa [x.length_encode_markDeleted hnew]
      exact (hf j hj' (by simpa only [Nat.add_zero] using hscratch)).trans (hs.2.2 j hj)
    · dsimp only at hc ⊢
      simp only [Expr.size, Nat.add_sub_cancel_left] at hc
      omega
  unfold delEntryStart
  refine (Triple.seq_normal_const H (Triple.seq_normal_const HM tail)).mono_cost ?_
  intro s _
  let l := x.H.A.revList e
  let C := rangeCost (delScanStepCost y l (y.revStart e)) (y.revStart e) (y.revStart e + l.length)
  change 40 + (40 + (C + 9 * l.length + 68) + 1) + 1 ≤ C + 9 * l.length + 150
  omega

end MinCostFlow.HierPaths

end
