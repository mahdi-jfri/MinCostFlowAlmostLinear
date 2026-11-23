module

public import MinCostFlow.HierPaths.DelProgOutputPass
public import WordRAM.Layout
public import MinCostFlow.Expander.PathDSProg.RuntimeHelpers

/-!
# Finishing the Delete output

The output header records the number of reported vertices. Scratch cleanup clears the two
work lists without touching the output or the block.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Expander

/-- Store the output length at the heap address in register 70. -/
def delWriteOutputLength : Stmt := .store (.reg 70) (.reg 59)

theorem delWriteOutputLength_noRand : delWriteOutputLength.NoRand := by
  simp [delWriteOutputLength, Stmt.NoRand]

/-- The count word completes the length-prefixed output. -/
theorem delWriteOutputLength_triple {w : ℕ} {p : Program}
    {h b : ℕ} {L block : List ℕ} {R mem0 : ℕ → ℕ}
    (h70 : R 70 = h) (h59 : R 59 = L.length)
    (hb : b + block.length ≤ h) (_hw : h < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b block ∧
        ListAt s.mem (h + 1) L ∧ s.mem = mem0) delWriteOutputLength
      (normalPost fun s => s.regs = R ∧ ListAt s.mem b block ∧ SeqAt s.mem h L ∧
        s.mem = Function.update mem0 h L.length)
      (fun _ => 3) := by
  unfold delWriteOutputLength
  refine Triple.store (addr := fun _ => h) (val := fun _ => L.length)
    (fun _ hs => Expr.eval_reg_of_eq (hs.1 ▸ h70))
    (fun _ hs => Expr.eval_reg_of_eq (hs.1 ▸ h59)) ?_
  intro s hs
  obtain ⟨hr, hB, hL, hm⟩ := hs
  refine ⟨hr, ?_, ⟨Function.update_self .., ?_⟩, by rw [hm]⟩
  · refine listAt_congr (fun i hi => ?_) hB
    exact (Function.update_of_ne (by omega) _ _).symm
  · refine listAt_congr (fun i _ => ?_) hL
    exact (Function.update_of_ne (by omega) _ _).symm

/-- Zero the scratch interval beginning at register `r`, whose length is in register `n`. -/
def delClearList (r n : ℕ) : Stmt :=
  .seq (.assign 20 (.reg r))
    (.seq (.assign 21 (.bin .add (.reg 20) (.reg n)))
      MinCostFlow.Expander.PathDSProg.zeroRangeStmt)

theorem delClearList_noRand (r n : ℕ) : (delClearList r n).NoRand := by
  simp [delClearList, Stmt.NoRand, MinCostFlow.Expander.PathDSProg.zeroRangeStmt_noRand]

/-- Clear just the used scratch words. The cost depends on the list length. -/
theorem delClearList_triple {w : ℕ} {p : Program}
    {r n lo len : ℕ} {R mem0 : ℕ → ℕ} (hn : n ≠ 20)
    (hr : R r = lo) (hRn : R n = len)
    (hw : lo + len < 2 ^ w) (hone : 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ s.mem = mem0) (delClearList r n)
      (normalPost fun s => MemFrame mem0 s.mem lo (lo + len) ∧
        (∀ j, lo ≤ j → j < lo + len → s.mem j = 0))
      (fun _ => 12 * len + 20) := by
  let R' := Function.update R 20 lo
  let R'' := Function.update R' 21 (lo + len)
  let M := fun mem => mem = mem0
  have h1 : Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign 20 (.reg r))
      (normalPost fun s => s.regs = R' ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (hs ▸ hr)
  have h2 : Triple w p (fun s => s.regs = R' ∧ M s.mem)
      (.assign 21 (.bin .add (.reg 20) (.reg n)))
      (normalPost fun s => s.regs = R'' ∧ M s.mem) (fun _ => 4) :=
    triple_assign_exact fun _ hs _ => Expr.eval_add
      (Expr.eval_reg_of_eq (by rw [hs]; simp [R']))
      (Expr.eval_reg_of_eq (by rw [hs]; simpa [R', Function.update_of_ne hn] using hRn)) hw
  have h3 : Triple w p (fun s => s.regs = R'' ∧ M s.mem)
      MinCostFlow.Expander.PathDSProg.zeroRangeStmt
      (normalPost fun s => MemFrame mem0 s.mem lo (lo + len) ∧
        (∀ j, lo ≤ j → j < lo + len → s.mem j = 0)) (fun _ => 12 * len + 10) := by
    intro s ω hs
    have he20 : s.regs 20 = lo := by simp [hs.1, R'', R']
    have he21 : s.regs 21 = lo + len := by simp [hs.1, R'']
    have H := MinCostFlow.Expander.PathDSProg.zeroRangeStmt_triple (w := w) (p := p)
      s he20 he21 (Nat.le_add_right ..) (fun _ => hw) hone
    obtain ⟨o, s', c, hrun, hp, hh⟩ := H s ω rfl
    cases o <;> try contradiction
    refine ⟨_, s', c, hrun, ⟨?_, hp.2.1⟩, ?_⟩
    · have hm : s.mem = mem0 := hs.2
      exact hm ▸ hp.1
    · simpa using hh
  exact (Triple.seq_normal_const h1 (Triple.seq_normal_const h2 h3)).mono_cost (fun _ _ => by omega)

/-- Write the output header, clear both work lists and return the end of the output. -/
def delFinish : Stmt :=
  .seq delWriteOutputLength
    (.seq (delClearList 71 72) (.seq (delClearList 73 74)
      (.ret (.bin .add (.bin .add (.reg 70) (.const 1)) (.reg 59)))))

theorem delFinish_noRand : delFinish.NoRand := by
  simp [delFinish, Stmt.NoRand, delWriteOutputLength_noRand, delClearList_noRand]

private theorem delClearList_frame (r n : ℕ) : Stmt.WritesBelow 23 (delClearList r n) := by
  simp [delClearList, MinCostFlow.Expander.PathDSProg.zeroRangeStmt, forRange, forUp, Stmt.WritesBelow]

/-- The returned heap ends immediately after the result. All scratch cells above it are zero. -/
theorem delFinish_triple {w : ℕ} {p : Program}
    {h b lostBase lostCount connBase connCount : ℕ} {L block : List ℕ} {R mem0 : ℕ → ℕ}
    (h70 : R 70 = h) (h59 : R 59 = L.length)
    (h71 : R 71 = lostBase) (h72 : R 72 = lostCount)
    (h73 : R 73 = connBase) (h74 : R 74 = connCount)
    (hb : b + block.length ≤ h) (hout : h + 1 + L.length ≤ lostBase)
    (hlost : lostBase + lostCount ≤ connBase) (hw : connBase + connCount < 2 ^ w)
    (hz : ∀ j, h + 1 + L.length ≤ j → (j < lostBase ∨ lostBase + lostCount ≤ j) →
      (j < connBase ∨ connBase + connCount ≤ j) → mem0 j = 0) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b block ∧
        ListAt s.mem (h + 1) L ∧ s.mem = mem0) delFinish
      (retPost fun u s => u = h + 1 + L.length ∧ ListAt s.mem b block ∧ SeqAt s.mem h L ∧
        ZeroFrom s.mem u ∧ (∀ j < h, s.mem j = mem0 j))
      (fun _ => 12 * (lostCount + connCount) + 55) := by
  have hhw : h < 2 ^ w := by omega
  have hLw : lostBase + lostCount < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  let mem₁ := Function.update mem0 h L.length
  let Pre := fun s : State => s.regs = R ∧ ListAt s.mem b block ∧ SeqAt s.mem h L ∧ s.mem = mem₁
  let Q := fun u (s : State) => u = h + 1 + L.length ∧ ListAt s.mem b block ∧ SeqAt s.mem h L ∧
    ZeroFrom s.mem u ∧ (∀ j < h, s.mem j = mem0 j)
  have H := delWriteOutputLength_triple (w := w) (p := p) (mem0 := mem0) h70 h59 hb hhw
  have htail : Triple w p Pre (.seq (delClearList 71 72)
      (.seq (delClearList 73 74) (.ret (.bin .add (.bin .add (.reg 70) (.const 1)) (.reg 59)))))
      (retPost Q) (fun _ => 12 * (lostCount + connCount) + 50) := by
    intro s ω hs
    let Mid := fun t : State => MemFrame s.mem t.mem lostBase (lostBase + lostCount) ∧
      (∀ j, lostBase ≤ j → j < lostBase + lostCount → t.mem j = 0) ∧
      ∀ j, 23 ≤ j → t.regs j = R j
    have C₁ := Triple.regs_frame (delClearList_frame 71 72)
      (delClearList_triple (w := w) (p := p) (mem0 := s.mem) (by decide) h71 h72 hLw hone) R
    have C₁' := C₁.strengthen_post (Q' := normalPost Mid) (fun o t hp => by
      cases o <;> try exact False.elim hp.1
      exact ⟨hp.1.1, hp.1.2, hp.2⟩)
    have C₂ : Triple w p Mid
        (.seq (delClearList 73 74) (.ret (.bin .add (.bin .add (.reg 70) (.const 1)) (.reg 59))))
        (retPost Q) (fun _ => 12 * connCount + 27) := by
      intro t ω' ht
      let Ready := fun v : State => Q (h + 1 + L.length) v ∧
        v.regs 70 = h ∧ v.regs 59 = L.length
      have C := Triple.regs_frame (delClearList_frame 73 74)
        (delClearList_triple (w := w) (p := p) (mem0 := t.mem) (by decide)
          ((ht.2.2 73 (by decide)).trans h73) ((ht.2.2 74 (by decide)).trans h74) hw hone) t.regs
      have C' := C.strengthen_post (Q' := normalPost Ready) (fun o v hp => by
        cases o <;> try exact False.elim hp.1
        obtain ⟨⟨hf, hzc⟩, hr⟩ := hp
        have hframe : ∀ j < lostBase, v.mem j = s.mem j := by
          intro j hj
          exact (hf j (Or.inl (by omega))).trans (ht.1 j (Or.inl hj))
        refine ⟨⟨rfl, ?_, ?_, ?_, ?_⟩, (hr 70 (by decide)).trans
          ((ht.2.2 70 (by decide)).trans h70), (hr 59 (by decide)).trans
          ((ht.2.2 59 (by decide)).trans h59)⟩
        · exact listAt_congr (fun j hj => (hframe _ (by omega)).symm) hs.2.1
        · exact ⟨(hframe h (by omega)).trans hs.2.2.1.1,
            listAt_congr (fun j hj => (hframe _ (by omega)).symm) hs.2.2.1.2⟩
        · intro j hj
          change h + 1 + L.length ≤ j at hj
          by_cases hc : connBase ≤ j ∧ j < connBase + connCount
          · exact hzc j hc.1 hc.2
          have hfC : j < connBase ∨ connBase + connCount ≤ j := by omega
          rw [hf j hfC]
          by_cases hl : lostBase ≤ j ∧ j < lostBase + lostCount
          · exact ht.2.1 j hl.1 hl.2
          have hfL : j < lostBase ∨ lostBase + lostCount ≤ j := by omega
          rw [ht.1 j hfL, hs.2.2.2]
          simp only [mem₁, Function.update_of_ne (show j ≠ h by omega)]
          exact hz j hj hfL hfC
        · intro j hj
          rw [hframe j (by omega), hs.2.2.2]
          exact Function.update_of_ne (by omega) _ _)
      have Ret : Triple w p Ready
          (.ret (.bin .add (.bin .add (.reg 70) (.const 1)) (.reg 59)))
          (retPost Q) (fun _ => 6) := by
        exact Triple.ret (val := fun _ => h + 1 + L.length)
          (fun _ ht => Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ht.2.1)
            (Expr.eval_const hone) (by omega)) (Expr.eval_reg_of_eq ht.2.2) (by omega))
          (fun _ ht => ht.1)
      exact (Triple.seq_normal_const C' Ret) t ω' ⟨⟨rfl, rfl⟩, fun _ _ => rfl⟩
    have HC := (Triple.seq_normal_const C₁' C₂).mono_cost
      (T' := fun _ => 12 * (lostCount + connCount) + 50) (fun _ _ => by omega)
    exact HC s ω ⟨⟨hs.1, rfl⟩, fun j _ => congrFun hs.1 j⟩
  exact (Triple.seq_normal_const H htail).mono_cost (fun _ _ => by omega)

end MinCostFlow.HierPaths

end
