module

public import MinCostFlow.MinRatio.UpdateIntTablesGrowBase
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
import WordRAM.Tactic

/-!
# Dynamic internal-table growth specification for `Update` and `Init`

Proves:
- `growIntTablesFromReg7_runs`: reallocates all six `intCap`-indexed tables to an arbitrary target
  capacity `newCap > tok.intCap` in `[heap, heap + 6 * newCap)`, preserving `solverStateRep`, all
  potentials, tree tokens, and off-tree edge records.
- `growIntTablesBody_runs`: conditional wrapper used by `Update`, setting
  `tok'.intCap = if tok.intCap < model.nextFresh + batchLen then 2 * (model.nextFresh + batchLen)
  else tok.intCap`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

set_option maxHeartbeats 600000 in
/-- Core table-growth execution `growIntTablesFromReg7 copyWords`: given `reg 0 = root`,
`reg 5 = tok.intCap`, `reg 7 = newCap > tok.intCap`, and `reg 8 = heap`, reallocates all six
`intCap`-indexed tables to `newCap` in `[heap, heap + 6 * newCap)`, sets `reg 14 = heap + 6 * newCap`,
preserves `solverStateRep`, all potentials, tree tokens, and every tag-18 record below `heap`. -/
theorem growIntTablesFromReg7_runs {w L P m V psi k epsExp drainUnit copyWords root heap newCap : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hr0 : st.regs 0 = root) (hr5 : st.regs 5 = tok.intCap)
    (hr7 : st.regs 7 = newCap) (hr8 : st.regs 8 = heap)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok st.mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hcapPos : 0 < tok.intCap) (hcapLt : tok.intCap < newCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (hw15 : 15 < 2 ^ w)
    (hroom : heap + 6 * newCap < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ cost out tok',
      Runs w p ω (growIntTablesFromReg7 copyWords) st .normal out cost ∧
      out.regs 14 = heap + 6 * newCap ∧
      tok'.intCap = newCap ∧
      tok'.tree = tok.tree ∧ tok'.trees = tok.trees ∧
      (∀ j < tok.intCap, out.mem (tok'.edgeRecords + j) = st.mem (tok.edgeRecords + j)) ∧
      (∀ a < heap, tok.tag a = 18 → out.mem a = st.mem a) ∧
      Rrep.rep root model tok' out.mem ∧
      PreservesLevelMeta tok tok' st.mem out.mem ∧
      Rrep.phi root tok' out.mem = Rrep.phi root tok st.mem ∧
      ZeroFrom out.mem (heap + 6 * newCap) ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = st.mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < heap + 6 * newCap)) ∧
      cost ≤ 102 * tok.intCap + 17 * newCap + 220 := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, _, t8, t9, _, _, t12, t13, t14, t15, _⟩ := htags
  have hltH {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hheapW : heap < 2 ^ w := by omega
  have hroot15W : root + 15 < 2 ^ w := lt_trans (hltH (t1 15 (by omega)) (by decide)) hheapW
  let s7 := { st with regs := Function.update st.regs 9 (heap + newCap) }
  let s8 := { s7 with regs := Function.update s7.regs 10 (heap + 2 * newCap) }
  let s9 := { s8 with regs := Function.update s8.regs 11 (heap + 3 * newCap) }
  let s10 := { s9 with regs := Function.update s9.regs 12 (heap + 4 * newCap) }
  let s11 := { s10 with regs := Function.update s10.regs 13 (heap + 5 * newCap) }
  let s12 := { s11 with regs := Function.update s11.regs 14 (heap + 6 * newCap) }
  have r7 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 7))) st .normal s7 4 :=
    runs_assign_iff.mpr ⟨heap + newCap, by
      simp [Expr.eval, BinOp.eval, hr8, hr7, show heap + newCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 10 (.bin .add (.reg 9) (.reg 7))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨heap + 2 * newCap, by
      simp [Expr.eval, BinOp.eval, s7, hr7, show heap + newCap + newCap = heap + 2 * newCap by omega,
        show heap + 2 * newCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.reg 7))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨heap + 3 * newCap, by
      simp [Expr.eval, BinOp.eval, s8, s7, hr7, show heap + 2 * newCap + newCap = heap + 3 * newCap by omega,
        show heap + 3 * newCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.reg 7))) s9 .normal s10 4 :=
    runs_assign_iff.mpr ⟨heap + 4 * newCap, by
      simp [Expr.eval, BinOp.eval, s9, s8, s7, hr7, show heap + 3 * newCap + newCap = heap + 4 * newCap by omega,
        show heap + 4 * newCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 13 (.bin .add (.reg 12) (.reg 7))) s10 .normal s11 4 :=
    runs_assign_iff.mpr ⟨heap + 5 * newCap, by
      simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, hr7, show heap + 4 * newCap + newCap = heap + 5 * newCap by omega,
        show heap + 5 * newCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 7))) s11 .normal s12 4 :=
    runs_assign_iff.mpr ⟨heap + 6 * newCap, by
      simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, hr7, show heap + 5 * newCap + newCap = heap + 6 * newCap by omega,
        hroom], rfl, rfl, rfl⟩
  have holdEnd {base v : ℕ} (ht : ∀ j < tok.intCap, tok.tag (base + j) = v) (hv : v ≠ 0) :
      base + tok.intCap ≤ heap := by
    have hlast := hltH (ht (tok.intCap - 1) (by omega)) hv; omega
  obtain ⟨m1, c1, hrC1, hc1, hm1R, hm1Cp, hm1Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := s12)
    (root := root) (dstR := 8) (off := 4) (oldPtr := tok.inverse) (dst := heap) (intCap := tok.intCap) hCopy
    (by simp [s12, s11, s10, s9, s8, s7, hr0])
    (by simp [s12, s11, s10, s9, s8, s7, hr5])
    (by simp [s12, s11, s10, s9, s8, s7, hr8]) (by decide) (by omega) (by omega)
    (by simpa [s12, s11, s10, s9, s8, s7] using hrootDir 4 (by simp))
    (by omega) (holdEnd t8 (by decide)) (by omega)
  obtain ⟨m2, c2, hrFill, hc2, hm2R, hm2Fill, hm2Fr⟩ := fillInverseTail_runs (w := w) (ω := ω) (st := m1)
    (base := heap) (lo := tok.intCap) (hi := newCap) (by omega)
    (by rw [hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm1R 7 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr7])
    (by rw [hm1R 8 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr8])
    (by omega) (by omega)
  have hlt_m2 (a : ℕ) (ha : a < heap) : m2.mem a = st.mem a :=
    (hm2Fr a (Or.inl (by omega))).trans (hm1Fr a (Or.inl ha))
  obtain ⟨m3, c3, hrC3, hc3, hm3R, hm3Cp, hm3Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := m2)
    (root := root) (dstR := 9) (off := 6) (oldPtr := tok.slots) (dst := heap + newCap) (intCap := tok.intCap) hCopy
    (by rw [hm2R 0 (by decide), hm1R 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
    (by rw [hm2R 5 (by decide), hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm2R 9 (by decide), hm1R 9 (by decide)]; simp [s12, s11, s10, s9, s8, s7])
    (by decide) (by omega) (by omega)
    ((hlt_m2 _ (hltH (t1 6 (by omega)) (by decide))).trans (by simpa using hrootDir 6 (by simp)))
    (by omega) (le_trans (holdEnd t9 (by decide)) (by omega)) (by omega)
  have hlt_m3 (a : ℕ) (ha : a < heap) : m3.mem a = st.mem a :=
    (hm3Fr a (Or.inl (by omega))).trans (hlt_m2 a ha)
  obtain ⟨m4, c4, hrC4, hc4, hm4R, hm4Cp, hm4Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := m3)
    (root := root) (dstR := 10) (off := 9) (oldPtr := tok.edgeThresholds) (dst := heap + 2 * newCap) (intCap := tok.intCap) hCopy
    (by rw [hm3R 0 (by decide), hm2R 0 (by decide), hm1R 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
    (by rw [hm3R 5 (by decide), hm2R 5 (by decide), hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm3R 10 (by decide), hm2R 10 (by decide), hm1R 10 (by decide)]; simp [s12, s11, s10, s9, s8])
    (by decide) (by omega) (by omega)
    ((hlt_m3 _ (hltH (t1 9 (by omega)) (by decide))).trans (by simpa using hrootDir 9 (by simp)))
    (by omega) (le_trans (holdEnd t12 (by decide)) (by omega)) (by omega)
  have hlt_m4 (a : ℕ) (ha : a < heap) : m4.mem a = st.mem a :=
    (hm4Fr a (Or.inl (by omega))).trans (hlt_m3 a ha)
  obtain ⟨m5, c5, hrC5, hc5, hm5R, hm5Cp, hm5Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := m4)
    (root := root) (dstR := 11) (off := 10) (oldPtr := tok.edgeRecords) (dst := heap + 3 * newCap) (intCap := tok.intCap) hCopy
    (by rw [hm4R 0 (by decide), hm3R 0 (by decide), hm2R 0 (by decide), hm1R 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
    (by rw [hm4R 5 (by decide), hm3R 5 (by decide), hm2R 5 (by decide), hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm4R 11 (by decide), hm3R 11 (by decide), hm2R 11 (by decide), hm1R 11 (by decide)]; simp [s12, s11, s10, s9])
    (by decide) (by omega) (by omega)
    ((hlt_m4 _ (hltH (t1 10 (by omega)) (by decide))).trans (by simpa using hrootDir 10 (by simp)))
    (by omega) (le_trans (holdEnd t13 (by decide)) (by omega)) (by omega)
  have hlt_m5 (a : ℕ) (ha : a < heap) : m5.mem a = st.mem a :=
    (hm5Fr a (Or.inl (by omega))).trans (hlt_m4 a ha)
  obtain ⟨m6, c6, hrC6, hc6, hm6R, hm6Cp, hm6Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := m5)
    (root := root) (dstR := 12) (off := 12) (oldPtr := tok.offReadyList) (dst := heap + 4 * newCap) (intCap := tok.intCap) hCopy
    (by rw [hm5R 0 (by decide), hm4R 0 (by decide), hm3R 0 (by decide), hm2R 0 (by decide), hm1R 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
    (by rw [hm5R 5 (by decide), hm4R 5 (by decide), hm3R 5 (by decide), hm2R 5 (by decide), hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm5R 12 (by decide), hm4R 12 (by decide), hm3R 12 (by decide), hm2R 12 (by decide), hm1R 12 (by decide)]; simp [s12, s11, s10])
    (by decide) (by omega) (by omega)
    ((hlt_m5 _ (hltH (t1 12 (by omega)) (by decide))).trans (by simpa using hrootDir 12 (by simp)))
    (by omega) (le_trans (holdEnd t14 (by decide)) (by omega)) (by omega)
  have hlt_m6 (a : ℕ) (ha : a < heap) : m6.mem a = st.mem a :=
    (hm6Fr a (Or.inl (by omega))).trans (hlt_m5 a ha)
  obtain ⟨m7, c7, hrC7, hc7, hm7R, hm7Cp, hm7Fr⟩ := copyOneTable_runs (w := w) (ω := ω) (st := m6)
    (root := root) (dstR := 13) (off := 13) (oldPtr := tok.inOffReady) (dst := heap + 5 * newCap) (intCap := tok.intCap) hCopy
    (by rw [hm6R 0 (by decide), hm5R 0 (by decide), hm4R 0 (by decide), hm3R 0 (by decide), hm2R 0 (by decide), hm1R 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
    (by rw [hm6R 5 (by decide), hm5R 5 (by decide), hm4R 5 (by decide), hm3R 5 (by decide), hm2R 5 (by decide), hm1R 5 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr5])
    (by rw [hm6R 13 (by decide), hm5R 13 (by decide), hm4R 13 (by decide), hm3R 13 (by decide), hm2R 13 (by decide), hm1R 13 (by decide)]; simp [s12, s11])
    (by decide) (by omega) (by omega)
    ((hlt_m6 _ (hltH (t1 13 (by omega)) (by decide))).trans (by simpa using hrootDir 13 (by simp)))
    (by omega) (le_trans (holdEnd t15 (by decide)) (by omega)) (by omega)
  have hlt_m7 (a : ℕ) (ha : a < heap) : m7.mem a = st.mem a :=
    (hm7Fr a (Or.inl (by omega))).trans (hlt_m6 a ha)
  have hm7R_all (r : ℕ) (hr : r ≤ 14) : m7.regs r = s12.regs r := by
    rw [hm7R r hr, hm6R r hr, hm5R r hr, hm4R r hr, hm3R r hr, hm2R r hr, hm1R r hr]
  obtain ⟨out, hrPatch, houtR, ho4, ho6, ho9, ho10, ho12, ho13, ho15, hoh2, hoFr⟩ :=
    growIntTablesPatch_runs (ω := ω) (st := m7) (root := root) (handle := tok.handle) (newCap := newCap)
      (newInv := heap) (newSl := heap + newCap) (newET := heap + 2 * newCap)
      (newER := heap + 3 * newCap) (newOL := heap + 4 * newCap) (newIO := heap + 5 * newCap)
      (by rw [hm7R_all 0 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr0])
      (by rw [hm7R_all 7 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr7])
      (by rw [hm7R_all 8 (by decide)]; simp [s12, s11, s10, s9, s8, s7, hr8])
      (by rw [hm7R_all 9 (by decide)]; simp [s12, s11, s10, s9, s8, s7])
      (by rw [hm7R_all 10 (by decide)]; simp [s12, s11, s10, s9, s8])
      (by rw [hm7R_all 11 (by decide)]; simp [s12, s11, s10, s9])
      (by rw [hm7R_all 12 (by decide)]; simp [s12, s11, s10])
      (by rw [hm7R_all 13 (by decide)]; simp [s12, s11])
      ((hlt_m7 root (hltH (t1 0 (by omega)) (by decide))).trans (by simpa using hrootDir 0 (by simp)))
      (fun j _ hj => by omega) hw15 hroot15W (lt_trans (hltH (t2 2 (by omega)) (by decide)) hheapW)
      (fun j hj h => by have ht := t2 2 (by omega); rw [h, t1 j hj] at ht; omega)
  have hgeHeap (a : ℕ) (ha : heap ≤ a) : out.mem a = m7.mem a :=
    hoFr a
      (by have := hltH (t1 4 (by omega)) (by decide); omega)
      (by have := hltH (t1 6 (by omega)) (by decide); omega)
      (by have := hltH (t1 9 (by omega)) (by decide); omega)
      (by have := hltH (t1 10 (by omega)) (by decide); omega)
      (by have := hltH (t1 12 (by omega)) (by decide); omega)
      (by have := hltH (t1 13 (by omega)) (by decide); omega)
      (by have := hltH (t1 15 (by omega)) (by decide); omega)
      (by have := hltH (t2 2 (by omega)) (by decide); omega)
  have hrCopySeq : Runs w p ω (growIntTablesCopy copyWords) s12 .normal m7
      (c1 + (c2 + (c3 + (c4 + (c5 + (c6 + c7 + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨m1, c1, _, hrC1,
      runs_seq_iff.mpr (Or.inr ⟨m2, c2, _, hrFill,
      runs_seq_iff.mpr (Or.inr ⟨m3, c3, _, hrC3,
      runs_seq_iff.mpr (Or.inr ⟨m4, c4, _, hrC4,
      runs_seq_iff.mpr (Or.inr ⟨m5, c5, _, hrC5,
      runs_seq_iff.mpr (Or.inr ⟨m6, c6, c7, hrC6, hrC7, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  let cCopy := c1 + (c2 + (c3 + (c4 + (c5 + (c6 + c7 + 1) + 1) + 1) + 1) + 1) + 1
  have hrFull : Runs w p ω (growIntTablesFromReg7 copyWords) st .normal out
      (4 + (4 + (4 + (4 + (4 + (4 + (cCopy + 51 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s7, 4, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
      runs_seq_iff.mpr (Or.inr ⟨s11, 4, _, r11,
      runs_seq_iff.mpr (Or.inr ⟨s12, 4, _, r12,
      runs_seq_iff.mpr (Or.inr ⟨m7, cCopy, 51, hrCopySeq, hrPatch, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have herCopy (j : ℕ) (hj : j < tok.intCap) :
      out.mem (heap + 3 * newCap + j) = st.mem (tok.edgeRecords + j) := by
    rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Fr _ (Or.inl (by omega)),
      hm5Cp j hj, hlt_m4 _ (hltH (t13 j hj) (by decide))]
  obtain ⟨hrep', hphi'⟩ := solverStateRep_after_grow hlocalCore hrep0 hbelow hcapLt hnfLe
    (fun j hj => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Fr _ (Or.inl (by omega)),
        hm5Fr _ (Or.inl (by omega)), hm4Fr _ (Or.inl (by omega)), hm3Fr _ (Or.inl (by omega)),
        hm2Fr _ (Or.inl (by omega)), hm1Cp j hj])
    (fun j hj1 hj2 => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Fr _ (Or.inl (by omega)),
        hm5Fr _ (Or.inl (by omega)), hm4Fr _ (Or.inl (by omega)), hm3Fr _ (Or.inl (by omega)),
        hm2Fill j hj1 hj2])
    (fun j hj => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Fr _ (Or.inl (by omega)),
        hm5Fr _ (Or.inl (by omega)), hm4Fr _ (Or.inl (by omega)), hm3Cp j hj,
        hlt_m2 _ (hltH (t9 j hj) (by decide))])
    (fun j hj => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Fr _ (Or.inl (by omega)),
        hm5Fr _ (Or.inl (by omega)), hm4Cp j hj, hlt_m3 _ (hltH (t12 j hj) (by decide))])
    herCopy
    (fun j hj => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inl (by omega)), hm6Cp j hj,
        hlt_m5 _ (hltH (t14 j hj) (by decide))])
    (fun j hj => by
      rw [hgeHeap _ (by omega), hm7Cp j hj, hlt_m6 _ (hltH (t15 j hj) (by decide))])
    (fun j hj1 hj2 => by
      rw [hgeHeap _ (by omega), hm7Fr _ (Or.inr (by omega)), hm6Fr _ (Or.inr (by omega)),
        hm5Fr _ (Or.inr (by omega)), hm4Fr _ (Or.inr (by omega)), hm3Fr _ (Or.inr (by omega)),
        hm2Fr _ (Or.inr (by omega)), hm1Fr _ (Or.inr (by omega))]
      exact hz (heap + 5 * newCap + j) (by omega))
    ho4 ho6 ho9 ho10 ho12 ho13 ho15 hoh2
    (fun a ha h4 h6 h9 h10 h12 h13 h15 hh2 => (hoFr a h4 h6 h9 h10 h12 h13 h15 hh2).trans (hlt_m7 a ha))
  refine ⟨_, out,
    { tok with
      inverse := heap, slots := heap + newCap, edgeThresholds := heap + 2 * newCap,
      edgeRecords := heap + 3 * newCap, offReadyList := heap + 4 * newCap,
      inOffReady := heap + 5 * newCap, intCap := newCap,
      owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < heap + 6 * newCap),
      tag := fun a =>
        if heap ≤ a ∧ a < heap + newCap then 8
        else if heap + newCap ≤ a ∧ a < heap + 2 * newCap then 9
        else if heap + 2 * newCap ≤ a ∧ a < heap + 3 * newCap then 12
        else if heap + 3 * newCap ≤ a ∧ a < heap + 4 * newCap then 13
        else if heap + 4 * newCap ≤ a ∧ a < heap + 5 * newCap then 14
        else if heap + 5 * newCap ≤ a ∧ a < heap + 6 * newCap then 15
        else tok.tag a },
    hrFull,
    by rw [houtR 14 (by decide), hm7R_all 14 (by decide)]; simp [s12],
    rfl, rfl, rfl, herCopy,
    fun a ha h18 => (hoFr a
      (fun h => by have := t1 4 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 6 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 9 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 10 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 12 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 13 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t1 15 (by omega); rw [← h, h18] at this; omega)
      (fun h => by have := t2 2 (by omega); rw [← h, h18] at this; omega)).trans (hlt_m7 a ha),
    hrep',
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, fun a ht => by
      have hnz : tok.tag a ≠ 0 := by rcases ht with h | h | h | h <;> omega
      have haLt : a < heap := hltH rfl hnz
      have hne1 : tok.tag a ≠ 1 := by rcases ht with h | h | h | h <;> omega
      have hne2 : tok.tag a ≠ 2 := by rcases ht with h | h | h | h <;> omega
      refine ⟨by dsimp only; repeat rw [ite_eq_right (by omega)], ?_⟩
      exact (hoFr a
        (fun h => hne1 (h ▸ t1 4 (by omega))) (fun h => hne1 (h ▸ t1 6 (by omega)))
        (fun h => hne1 (h ▸ t1 9 (by omega))) (fun h => hne1 (h ▸ t1 10 (by omega)))
        (fun h => hne1 (h ▸ t1 12 (by omega))) (fun h => hne1 (h ▸ t1 13 (by omega)))
        (fun h => hne1 (h ▸ t1 15 (by omega))) (fun h => hne2 (h ▸ t2 2 (by omega)))).trans
          (hlt_m7 a haLt)⟩,
    hphi',
    fun a ha => by
      rw [hgeHeap a (by omega), hm7Fr a (Or.inr (by omega)), hm6Fr a (Or.inr (by omega)),
        hm5Fr a (Or.inr (by omega)), hm4Fr a (Or.inr (by omega)), hm3Fr a (Or.inr (by omega)),
        hm2Fr a (Or.inr (by omega)), hm1Fr a (Or.inr (by omega))]
      exact hz a (by omega),
    fun a ha hnf => by
      have hnotTag (v : ℕ) (hv : v ≠ 0) : tok.tag a ≠ v := fun ht => hnf (Or.inl (hOwn a (ht ▸ hv)))
      exact (hoFr a
        (fun h => hnotTag 1 (by decide) (h ▸ t1 4 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 6 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 9 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 10 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 12 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 13 (by omega)))
        (fun h => hnotTag 1 (by decide) (h ▸ t1 15 (by omega)))
        (fun h => hnotTag 2 (by decide) (h ▸ t2 2 (by omega)))).trans (hlt_m7 a ha),
    fun a ha => by
      rcases ha with (hown | htree | hcore)
      · rcases hown with h0 | hr
        · exact Or.inl (Or.inl h0)
        · exact Or.inr hr
      · exact Or.inl (Or.inr (Or.inl htree))
      · exact Or.inl (Or.inr (Or.inr hcore)),
    by dsimp only [cCopy] at hc1 hc2 hc3 hc4 hc5 hc6 hc7 ⊢; omega⟩

/-- End-to-end execution of `growIntTablesBody`: ensures `model.nextFresh + batchLen ≤ tok'.intCap`,
sets `tok'.intCap = if tok.intCap < model.nextFresh + batchLen then 2 * (model.nextFresh + batchLen)
else tok.intCap`, and preserves `solverStateRep` and all potentials. -/
theorem growIntTablesBody_runs {w L P m V psi k epsExp drainUnit copyWords root batchLen heap pos : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (hcapPos : 0 < tok.intCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (hw15 : 15 < 2 ^ w)
    (hroom : heap + 12 * (model.nextFresh + batchLen) < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ ret cost out tok',
      Runs w p ω (growIntTablesBody copyWords)
        (startState [root, batchLen, heap] mem pos) (.returned ret) out cost ∧
      model.nextFresh + batchLen ≤ tok'.intCap ∧
      Rrep.rep root model tok' out.mem ∧
      PreservesLevelMeta tok tok' mem out.mem ∧
      Rrep.phi root tok' out.mem = Rrep.phi root tok mem ∧
      tok'.intCap =
        (if tok.intCap < model.nextFresh + batchLen then 2 * (model.nextFresh + batchLen) else tok.intCap) ∧
      tok'.tree = tok.tree ∧ tok'.trees = tok.trees ∧
      (∀ j < tok.intCap, out.mem (tok'.edgeRecords + j) = mem (tok.edgeRecords + j)) ∧
      ZeroFrom out.mem ret ∧ heap ≤ ret ∧
      ret ≤ heap + 12 * (model.nextFresh + batchLen) ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost ≤ (if tok.intCap < model.nextFresh + batchLen then
        102 * tok.intCap + 34 * (model.nextFresh + batchLen) + 260 else 40) := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, _, _, hfreshTab, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, _, _, _, _, t6, _⟩ := htags
  have hltH {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hheapW : heap < 2 ^ w := by omega
  have hroot15W : root + 15 < 2 ^ w := lt_trans (hltH (t1 15 (by omega)) (by decide)) hheapW
  have hneedW : model.nextFresh + batchLen < 2 ^ w := by omega
  let s0 := startState [root, batchLen, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 3 tok.freshCounter }
  let s2 := { s1 with regs := Function.update s1.regs 4 model.nextFresh }
  let s3 := { s2 with regs := Function.update s2.regs 5 tok.intCap }
  let s4 := { s3 with regs := Function.update s3.regs 6 (model.nextFresh + batchLen) }
  have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 5)))) s0 .normal s1 5 :=
    runs_assign_iff.mpr ⟨tok.freshCounter, by
      simp [Expr.eval, BinOp.eval, s0, startState, show 5 < 2 ^ w by omega,
        show root + 5 < 2 ^ w by omega, show mem (root + 5) = tok.freshCounter by simpa using hrootDir 5 (by simp)],
      rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 4 (.load (.reg 3))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨model.nextFresh, by simp [Expr.eval, s1, s0, startState, hfreshTab.1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 15)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, hw15, hroot15W,
        show mem (root + 15) = tok.intCap by simpa using hrootDir 15 (by simp)], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.reg 1))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨model.nextFresh + batchLen, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hneedW], rfl, rfl, rfl⟩
  by_cases hgrow : tok.intCap < model.nextFresh + batchLen
  · simp only [hgrow, ↓reduceIte]
    let newCap := 2 * (model.nextFresh + batchLen)
    let s5 := { s4 with regs := Function.update s4.regs 7 newCap }
    let s6 := { s5 with regs := Function.update s5.regs 8 heap }
    have r5 : Runs w p ω (.assign 7 (.bin .mul (.const 2) (.reg 6))) s4 .normal s5 4 :=
      runs_assign_iff.mpr ⟨newCap, by
        simp [Expr.eval, BinOp.eval, s4, show 2 < 2 ^ w by omega, show newCap < 2 ^ w by dsimp only [newCap]; omega, newCap],
        rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 8 (.reg 2)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s5, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
    obtain ⟨cG, out, tok', hrG, hout14, hcapEq, htreeEq, htreesEq, hptrCopy, _, hrep', hpres', hphi', hz', hfr', hft', hcG⟩ :=
      growIntTablesFromReg7_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
        (epsExp := epsExp) (drainUnit := drainUnit) (copyWords := copyWords) (root := root)
        (heap := heap) (newCap := newCap) (st := s6) hlocalCore hCopy
        (by simp [s6, s5, s4, s3, s2, s1, s0, startState])
        (by simp [s6, s5, s4, s3]) (by simp [s6, s5]) (by simp [s6])
        hrep0 hbelow hz hcapPos (by dsimp only [newCap]; omega) hnfLe hw15
        (by dsimp only [newCap]; omega)
    have rRet : Runs w p ω (.ret (.reg 14)) out (.returned (heap + 6 * newCap)) out 2 :=
      runs_ret_iff.mpr ⟨heap + 6 * newCap, by simp [Expr.eval, hout14], rfl, rfl, rfl⟩
    let cThen := 4 + (2 + (cG + 2 + 1) + 1) + 1
    have rThen : Runs w p ω
        (.assign 7 (.bin .mul (.const 2) (.reg 6)) ;;
         .assign 8 (.reg 2) ;;
         growIntTablesFromReg7 copyWords ;;
         .ret (.reg 14)) s4 (.returned (heap + 6 * newCap)) out cThen :=
      runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
        runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
        runs_seq_iff.mpr (Or.inr ⟨out, cG, 2, hrG, rRet, rfl⟩), rfl⟩), rfl⟩)
    have rCond : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 6))
        (.assign 7 (.bin .mul (.const 2) (.reg 6)) ;;
         .assign 8 (.reg 2) ;;
         growIntTablesFromReg7 copyWords ;;
         .ret (.reg 14))
        (.ret (.reg 2))) s4 (.returned (heap + 6 * newCap)) out (cThen + 4) :=
      runs_cond_iff.mpr ⟨1, cThen, by
        simp [Expr.eval, BinOp.eval, s4, s3, hgrow, show 1 < 2 ^ w by omega],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact rThen, by simp [Expr.size]; omega⟩
    have hrFull : Runs w p ω (growIntTablesBody copyWords) s0 (.returned (heap + 6 * newCap)) out
        (5 + (3 + (5 + (4 + (cThen + 4) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, r4, rCond, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨heap + 6 * newCap, _, out, tok', hrFull, by dsimp only [newCap] at hcapEq ⊢; omega,
      hrep', hpres', hphi', hcapEq, htreeEq, htreesEq, hptrCopy, hz', by omega,
      by dsimp only [newCap]; omega, hfr', hft', ?_⟩
    dsimp only [cThen, newCap] at hcG ⊢; omega
  · simp only [hgrow, ↓reduceIte]
    have rRet : Runs w p ω (.ret (.reg 2)) s4 (.returned heap) s4 2 :=
      runs_ret_iff.mpr ⟨heap, by simp [Expr.eval, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
    have rCond : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 6))
        (.assign 7 (.bin .mul (.const 2) (.reg 6)) ;;
         .assign 8 (.reg 2) ;;
         growIntTablesFromReg7 copyWords ;;
         .ret (.reg 14))
        (.ret (.reg 2))) s4 (.returned heap) s4 6 :=
      runs_cond_iff.mpr ⟨0, 2, by
        simp [Expr.eval, BinOp.eval, s4, s3, hgrow, show 0 < 2 ^ w by omega],
        by simp only [↓reduceIte]; exact rRet, by simp [Expr.size]⟩
    have hrFull : Runs w p ω (growIntTablesBody copyWords) s0 (.returned heap) s4 27 :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, 21, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 3, 17, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, 11, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 4, 6, r4, rCond, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    exact ⟨heap, 27, s4, tok, hrFull, by omega, hrep0, PreservesLevelMeta.refl tok mem,
      rfl, rfl, rfl, rfl, fun _ _ => rfl, hz, le_rfl, by omega,
      fun _ _ _ => rfl, fun _ ha => Or.inl ha, by omega⟩

end MinCostFlow.MinRatio
