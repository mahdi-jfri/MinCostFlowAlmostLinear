module

public import MinCostFlow.HierPaths.DelProgFail
public import MinCostFlow.HierPaths.DeleteScan

/-!
# The scan of the reverse list in `Delete`

`Delete(e)` walks the terminals of the reverse list of `e` and runs the failure step for each
one whose failed bit is clear (`scan`, `HierPaths/DeleteScan.lean`). `scanStmt` is this loop. The
list is given as the words `lo, …, lo + len - 1` of section `6` of the block; the loop counter
is register `25`, and the end `lo + len` is in register `26`. The failure step writes only
registers below `25` (`failStepStmt_writesBelow`), so the counter survives it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

theorem HierConcrete.sections_getD_6_withLoss (x : HierConcrete) (L : LossState) :
    (x.withLoss L).sections.getD 6 [] = x.sections.getD 6 [] := by
  simp [HierConcrete.sections, HierConcrete.withLoss, HierConcrete.withSt, HierConcrete.m]

theorem HierConcrete.sections_getD_13 (x : HierConcrete) :
    x.sections.getD 13 [] = bitsList x.H.A.C.numTerm fun t => decide (t ∈ x.ms.st.loss.failed) := by
  simp [HierConcrete.sections]

theorem scan_take_succ (x b : ℕ) (st : LossState) {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    scan x b st (l.take (k + 1)) = scanStep x b (scan x b st (l.take k)) l[k] := by
  rw [List.take_succ_eq_append_getElem hk]
  simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The output of a scan has at most `2 ^ x` terminals: it lists, without repetition, terminals
that became globally lost (`scan_spec`), and these are below `2 ^ x`
(`globalLost_subset_range`). -/
theorem length_scan_le {x b : ℕ} {F : Finset ℕ} {st : LossState} (hinv : LossInv x b F st)
    {l : List ℕ} (hl : ∀ t ∈ l, t < 2 ^ x) : (scan x b st l).2.length ≤ 2 ^ x := by
  obtain ⟨_, hnd, hfin, _⟩ := scan_spec hinv hl
  rw [← List.toFinset_card_of_nodup hnd, hfin]
  calc (globalLost x b (F ∪ l.toFinset) \ globalLost x b F).card
      ≤ (globalLost x b (F ∪ l.toFinset)).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (Finset.range (2 ^ x)).card := Finset.card_le_card globalLost_subset_range
    _ = 2 ^ x := Finset.card_range _

/-- One entry of the scan: read the terminal, read its failed bit, and run the failure step when
the bit is clear. -/
def scanBody : Stmt :=
  .seq (.assign 10 (readSec numSec 0 6 (.reg 25)))
  (.seq (.assign 24 (readSec numSec 0 13 (.reg 10)))
    (.cond (.reg 24) .nop failStepStmt))

/-- The scan over the words from register `27` to register `26` of section `6`. -/
def scanStmt : Stmt := forRange 25 (.reg 27) (.reg 26) scanBody

theorem scanStmt_noRand : scanStmt.NoRand := by
  simp [scanStmt, scanBody, forRange, forUp, Stmt.NoRand, failStepStmt_noRand]

/-- The state of the scan before word `i`. -/
def ScanInv (x : HierConcrete) (b WB c0 lo : ℕ) (l L0 : List ℕ) (mem0 : ℕ → ℕ) (i : ℕ)
    (s : State) : Prop :=
  s.regs 25 = i ∧ s.regs 0 = b ∧ s.regs 22 = WB ∧ s.regs 26 = lo + l.length ∧
  s.regs 23 = c0 + (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).2.length ∧
  ListAt s.mem b (x.withLoss (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1).encode ∧
  ListAt s.mem WB (L0 ++ (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).2) ∧
  ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
    WB + c0 + (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).2.length ≤ a) →
    s.mem a = mem0 a

/-- Each reverse-list entry pays a fixed charge and, on its first failure, the failure cost. -/
def delScanStepCost (x : HierConcrete) (l : List ℕ) (lo i : ℕ) : ℕ :=
  let L := (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1
  let t := l.getD (i - lo) 0
  1000 + if t ∈ L.failed then 0 else delFailureCost x.H.A.x x.H.A.b t L

theorem scanBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {F : Finset ℕ}
    {b WB c0 lo : ℕ} {l L0 : List ℕ} {mem0 : ℕ → ℕ}
    (hinv : LossInv x.H.A.x x.H.A.b F x.ms.st.loss) (hl : ∀ t ∈ l, t < 2 ^ x.H.A.x)
    (hl6 : ∀ k (hk : k < l.length), (x.sections.getD 6 []).getD (lo + k) 0 = l[k])
    (hlo6 : lo + l.length ≤ (x.sections.getD 6 []).length) (hL0 : L0.length = c0)
    (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x) (hb0 : 0 < x.H.A.b)
    (hb : b + x.encode.length < 2 ^ w) (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w)
    (hd : x.depth < 2 ^ w) (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hblk : b + x.encode.length ≤ WB)
    (hW : WB + c0 + 2 * 2 ^ x.H.A.x < 2 ^ w) {i : ℕ} (hlo : lo ≤ i) (hi : i < lo + l.length) :
    Triple w p (ScanInv x b WB c0 lo l L0 mem0 i) scanBody
      (normalPost fun s₁ => ScanInv x b WB c0 lo l L0 mem0 (i + 1)
        { s₁ with regs := Function.update s₁.regs 25 (i + 1) } ∧ s₁.regs 25 = i)
      (fun _ => delScanStepCost x l lo i) := by
  intro s ω hs
  obtain ⟨h25, h0, h22, h26, h23, hbl, hwl, hfr⟩ := hs
  obtain ⟨k, rfl⟩ : ∃ k, i = lo + k := ⟨i - lo, by omega⟩
  have hk : k < l.length := by omega
  have hik : lo + k - lo = k := by omega
  have hik1 : lo + k + 1 - lo = k + 1 := by omega
  rw [hik] at h23 hbl hwl hfr
  have h25' := x.le_length_encode
  have hlt' : ∀ t ∈ l.take k, t < 2 ^ x.H.A.x := fun t ht => hl t (List.mem_of_mem_take ht)
  have hinv' := (scan_spec hinv hlt').1
  have hnext := scan_take_succ x.H.A.x x.H.A.b x.ms.st.loss hk
  have hlen1 := length_scan_le hinv (l := l.take (k + 1))
    (fun t ht => hl t (List.mem_of_mem_take ht))
  rw [hnext] at hlen1
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = scan x.H.A.x x.H.A.b x.ms.st.loss (l.take k) := ⟨_, rfl⟩
  rw [← hSc] at h23 hbl hwl hfr hinv' hnext hlen1
  obtain ⟨y, hy⟩ : ∃ y : HierConcrete, y = x.withLoss Sc.1 := ⟨_, rfl⟩
  rw [← hy] at hbl
  have hylen : y.encode.length = x.encode.length := by rw [hy]; exact x.length_encode_withLoss _
  have hb' : b + y.encode.length < 2 ^ w := by rw [hylen]; exact hb
  have hbl' : ListAt s.mem b (layoutList y.sections) := hbl
  have ht : l[k] < 2 ^ x.H.A.x := hl _ (List.getElem_mem hk)
  -- read the terminal
  obtain ⟨s1, hs1⟩ : ∃ s1 : State, s1 = { s with regs := Function.update s.regs 10 l[k] } :=
    ⟨_, rfl⟩
  have tA : Triple w p (fun s' => s' = s) (.assign 10 (readSec numSec 0 6 (.reg 25)))
      (normalPost fun s' => s' = s1) (fun _ => (readSec numSec 0 6 (.reg 25)).size + 1) :=
    Triple.assign (val := fun _ => l[k]) (fun s' hs' => by
        rw [hs']
        have := eval_readSec' (w := w) hbl' hb' h0 (i := 6)
          (by rw [y.length_sections']; norm_num) (ke := .reg 25) (k := lo + k)
          (Expr.eval_reg_of_eq h25)
          (by rw [hy, HierConcrete.sections_getD_6_withLoss]; omega)
        rw [y.length_sections', hy, HierConcrete.sections_getD_6_withLoss, hl6 k hk] at this
        exact this)
      (fun s' hs' => by rw [hs', hs1])
  -- read its failed bit
  obtain ⟨s2, hs2⟩ : ∃ s2 : State,
      s2 = { s1 with regs := Function.update s1.regs 24 (if l[k] ∈ Sc.1.failed then 1 else 0) } :=
    ⟨_, rfl⟩
  have tB : Triple w p (fun s' => s' = s1) (.assign 24 (readSec numSec 0 13 (.reg 10)))
      (normalPost fun s' => s' = s2) (fun _ => (readSec numSec 0 13 (.reg 10)).size + 1) :=
    Triple.assign (val := fun _ => if l[k] ∈ Sc.1.failed then 1 else 0) (fun s' hs' => by
        rw [hs', hs1]
        have hsec : y.sections.getD 13 [] =
            bitsList x.H.A.C.numTerm fun t => decide (t ∈ Sc.1.failed) := by
          rw [y.sections_getD_13, hy]; rfl
        have htn : l[k] < x.H.A.C.numTerm := by rw [hnt]; exact ht
        have := eval_readSec' (w := w) (st := { s with regs := Function.update s.regs 10 l[k] })
          hbl' hb' (r := 0) (by show Function.update s.regs 10 l[k] 0 = b; rw [Function.update_of_ne (by norm_num)]; exact h0) (i := 13)
          (by rw [y.length_sections']; norm_num) (ke := .reg 10) (k := l[k])
          (Expr.eval_reg_of_eq (by simp)) (by rw [hsec]; simpa using htn)
        rw [y.length_sections', hsec, List.getD_eq_getElem _ _ (by simpa using htn)] at this
        simpa [bitsList] using this)
      (fun s' hs' => by rw [hs', hs2])
  have r2 : ∀ r, r ≠ 10 → r ≠ 24 → s2.regs r = s.regs r := by
    intro r h1 h2; rw [hs2, hs1]; simp [Function.update_apply, h1, h2]
  have hm2 : s2.mem = s.mem := by rw [hs2, hs1]
  -- the two cases
  have hhead : (readSec numSec 0 6 (.reg 25)).size + 1 +
      ((readSec numSec 0 13 (.reg 10)).size + 1 + 1) + 1 ≤ 100 := by decide
  by_cases hf : l[k] ∈ Sc.1.failed
  · have hstep : scanStep x.H.A.x x.H.A.b Sc l[k] = Sc := by simp [scanStep, hf]
    have tC : Triple w p (fun s' => s' = s2) (.cond (.reg 24) .nop failStepStmt)
        (normalPost fun s₁ => ScanInv x b WB c0 lo l L0 mem0 (lo + k + 1)
          { s₁ with regs := Function.update s₁.regs 25 (lo + k + 1) } ∧ s₁.regs 25 = lo + k)
        (fun _ => 3) := by
      refine (Triple.cond (val := fun _ => 1) (T_t := fun _ => 1)
        (T_f := fun _ => 0) (fun s' hs' => Expr.eval_reg_of_eq (by rw [hs', hs2]; simp [hf]))
        (Triple.nop fun s' hs' => ?_) (fun _ _ h => absurd h.2 one_ne_zero)).mono_cost
        (fun _ _ => by simp [Expr.size])
      rw [hs'.1]
      refine ⟨⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [r2 25 (by norm_num) (by norm_num), h25]⟩
      · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num), r2 0 (by norm_num)
          (by norm_num), h0]
      · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num), r2 22 (by norm_num)
          (by norm_num), h22]
      · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num), r2 26 (by norm_num)
          (by norm_num), h26]
      · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num), r2 23 (by norm_num)
          (by norm_num), h23, hik1, hnext, hstep]
      · show ListAt s2.mem b _; rw [hik1, hnext, hstep, hm2, ← hy]; exact hbl
      · show ListAt s2.mem WB _; rw [hik1, hnext, hstep, hm2]; exact hwl
      · intro a ha ha2
        show s2.mem a = _
        rw [hik1, hnext, hstep] at ha2
        rw [hm2]; exact hfr a ha ha2
    obtain ⟨o, s', c, hr, hq, hc⟩ := (Triple.seq_normal_const tA (Triple.seq_normal_const tB tC))
      s ω rfl
    refine ⟨o, s', c, hr, hq, ?_⟩
    have hbound : c ≤ 1000 := by
      dsimp only at hc
      omega
    simpa only [delScanStepCost, hik, List.getD_eq_getElem _ _ hk, ← hSc, ite_eq_left hf,
      Nat.add_zero] using hbound
  · have hstep : scanStep x.H.A.x x.H.A.b Sc l[k] =
        ((failStep x.H.A.x x.H.A.b l[k] Sc.1).1, Sc.2 ++ (failStep x.H.A.x x.H.A.b l[k] Sc.1).2) := by
      simp [scanStep, hf]
    have hlen2 := hlen1
    rw [hstep, List.length_append] at hlen2
    have hown : Sc.1.own x.depth l[k] + 1 < 2 ^ w := by
      have h1 := hinv'.own x.depth le_rfl l[k]
      have h2 := Finset.card_le_card (lost_subset_members (x := x.H.A.x) (b := x.H.A.b)
        (F := F ∪ (l.take k).toFinset) x.depth l[k])
      have hg1 : groupSize x.H.A.x x.H.A.b x.depth = 1 := groupSize_eq_one hb0 le_rfl
      rw [card_members, hg1] at h2
      have : 0 < 2 ^ x.H.A.x := Nat.two_pow_pos _
      show Sc.1.own (leafDepth x.H.A.x x.H.A.b) l[k] + 1 < 2 ^ w
      have h1' : Sc.1.own (leafDepth x.H.A.x x.H.A.b) l[k] =
        (lost x.H.A.x x.H.A.b (F ∪ (l.take k).toFinset) (leafDepth x.H.A.x x.H.A.b) l[k]).card := h1
      have h2' : (lost x.H.A.x x.H.A.b (F ∪ (l.take k).toFinset) (leafDepth x.H.A.x x.H.A.b) l[k]).card ≤ 1 := h2
      omega
    have tF := failStep_triple (w := w) (p := p) y (F := F ∪ (l.take k).toFinset) (b := b)
      (u := l[k]) (WB := WB) (c0 := c0 + Sc.2.length) (R := s2.regs) (L0 := L0 ++ Sc.2)
      (mem0 := s2.mem)
      (by rw [r2 0 (by norm_num) (by norm_num), h0])
      (by rw [hs2, hs1]; simp)
      (by rw [r2 22 (by norm_num) (by norm_num), h22])
      (by rw [r2 23 (by norm_num) (by norm_num), h23])
      (by simp [hL0]) (by rw [hy]; exact hinv') (by rw [hy]; exact ht)
      (by rw [← hinv'.failed]; exact hf) (by rw [hy]; exact hnt) (by rw [hy]; exact hb0)
      (by rw [hy]; exact hown) hb' (by rw [hy]; exact hdb) (by rw [hy]; exact hd)
      (by rw [hy]; exact h4x) (by rw [hylen]; exact hblk)
      (by rw [hy]; show WB + (c0 + Sc.2.length) +
            (failStep x.H.A.x x.H.A.b l[k] Sc.1).2.length + 2 ^ x.H.A.x < 2 ^ w
          omega)
    have tF' := (Triple.regs_frame failStepStmt_writesBelow tF s2.regs).weaken_pre
      (P' := fun s' => s' = s2 ∧ (fun _ => 0) s' = 0)
      (fun s' hs' => ⟨⟨by rw [hs'.1], by rw [hs'.1, hm2]; exact hbl,
        by rw [hs'.1, hm2]; exact hwl, by rw [hs'.1]⟩, fun r _ => by rw [hs'.1]⟩)
    let cost := delFailureCost y.H.A.x y.H.A.b l[k] y.ms.st.loss
    have tC : Triple w p (fun s' => s' = s2) (.cond (.reg 24) .nop failStepStmt)
        (normalPost fun s₁ => ScanInv x b WB c0 lo l L0 mem0 (lo + k + 1)
          { s₁ with regs := Function.update s₁.regs 25 (lo + k + 1) } ∧ s₁.regs 25 = lo + k)
        (fun _ => cost + 2) := by
      refine (Triple.cond (val := fun _ => 0) (T_t := fun _ => 0)
        (T_f := fun _ => cost)
        (fun s' hs' => Expr.eval_reg_of_eq (by rw [hs', hs2]; simp [hf]))
        (fun _ _ h => absurd rfl h.2) (tF'.strengthen_post fun o s' h => ?_)).mono_cost
        (fun _ _ => by change 1 + cost + 1 ≤ cost + 2; omega)
      cases o with
      | returned => exact h.1.elim
      | normal =>
        obtain ⟨⟨g0, _, g22, g23, gbl, gwl, gfr⟩, gregs⟩ := h
        have g25 : s'.regs 25 = lo + k := by
          rw [gregs 25 le_rfl, r2 25 (by norm_num) (by norm_num), h25]
        have g26 : s'.regs 26 = lo + l.length := by
          rw [gregs 26 (by norm_num), r2 26 (by norm_num) (by norm_num), h26]
        refine ⟨⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, g25⟩
        · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num)]; exact g0
        · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num)]; exact g22
        · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num)]; exact g26
        · simp only [Function.update_apply]; rw [_root_.if_neg (by norm_num)]
          rw [hik1, hnext, hstep, List.length_append, ← Nat.add_assoc]
          rw [hy] at g23; exact g23
        · show ListAt s'.mem b _
          rw [hik1, hnext, hstep]; rw [hy] at gbl; exact gbl
        · show ListAt s'.mem WB _
          rw [hik1, hnext, hstep, ← List.append_assoc]; rw [hy] at gwl; exact gwl
        · intro a ha ha2
          show s'.mem a = _
          rw [hik1, hnext, hstep, List.length_append] at ha2
          have hya : a < b ∨ b + y.encode.length ≤ a := by rw [hylen]; exact ha
          rcases ha2 with h2 | h2
          · rw [gfr a hya (Or.inl (by omega)), hm2]
            exact hfr a ha (Or.inl h2)
          · rw [gfr a hya (Or.inr (by
              rw [hy]; exact Nat.le_trans (Nat.le_of_eq (by simp only [Nat.add_assoc]; rfl)) h2)), hm2]
            exact hfr a ha (Or.inr (by omega))
    obtain ⟨o, s', c, hr, hq, hc⟩ := (Triple.seq_normal_const tA (Triple.seq_normal_const tB tC))
      s ω rfl
    refine ⟨o, s', c, hr, hq, ?_⟩
    have hbound : c ≤ 1000 + cost := by
      dsimp only at hc
      omega
    have hcost : cost = delFailureCost x.H.A.x x.H.A.b l[k] Sc.1 := by
      unfold cost
      rw [hy]
      rfl
    rw [hcost] at hbound
    simpa only [delScanStepCost, hik, List.getD_eq_getElem _ _ hk, ← hSc, ite_eq_right hf] using hbound

/-- **The scan.** From the block of `x` and the work list `L0` at `WB`, `scanStmt` runs `scan`
over the list `l` stored at words `lo, …, lo + len - 1` of section `6`. At the end, `ScanInv` at
`lo + len` holds, so the block is that of `(scan … l).1` and the work list is
`L0 ++ (scan … l).2` (the prefix `l.take len` is `l`). -/
theorem scan_triple {w : ℕ} {p : Program} (x : HierConcrete) {F : Finset ℕ}
    {b WB c0 lo : ℕ} {l L0 : List ℕ} {mem0 : ℕ → ℕ} {R : ℕ → ℕ}
    (hR0 : R 0 = b) (hR22 : R 22 = WB) (hR23 : R 23 = c0) (hR26 : R 26 = lo + l.length)
    (hR27 : R 27 = lo)
    (hinv : LossInv x.H.A.x x.H.A.b F x.ms.st.loss) (hl : ∀ t ∈ l, t < 2 ^ x.H.A.x)
    (hl6 : ∀ k (hk : k < l.length), (x.sections.getD 6 []).getD (lo + k) 0 = l[k])
    (hlo6 : lo + l.length ≤ (x.sections.getD 6 []).length) (hL0 : L0.length = c0)
    (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x) (hb0 : 0 < x.H.A.b)
    (hb : b + x.encode.length < 2 ^ w) (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w)
    (hd : x.depth < 2 ^ w) (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hblk : b + x.encode.length ≤ WB)
    (hW : WB + c0 + 2 * 2 ^ x.H.A.x < 2 ^ w) (hhiw : lo + l.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) scanStmt
      (normalPost (ScanInv x b WB c0 lo l L0 mem0 (lo + l.length)))
      (fun _ => rangeCost (delScanStepCost x l lo) lo
          (lo + l.length) + (lo + l.length - lo) * ((Expr.reg 26).size + 8) +
        ((Expr.reg 27).size + (Expr.reg 26).size + 5)) := by
  have h1w : 1 < 2 ^ w := by have := Nat.two_pow_pos x.H.A.x; omega
  refine Triple.forRange_le (delScanStepCost x l lo) lo
    (lo + l.length) (by omega) h1w (fun _ => hhiw) (fun s hs => ⟨?_, ?_⟩)
    (fun i s _ _ h => h.1) (fun i s _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
    (fun i hlo hi => scanBody_triple x hinv hl hl6 hlo6 hL0 hnt hb0 hb hdb hd h4x hblk hW hlo hi)
  · exact Expr.eval_reg_of_eq (by rw [hs.1, hR27])
  · obtain ⟨hr, hbl, hwl, hm⟩ := hs
    have hnil : scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (lo - lo)) = (x.ms.st.loss, []) := by
      rw [Nat.sub_self, List.take_zero]; rfl
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply, hr, hR0]
    · simp [Function.update_apply, hr, hR22]
    · simp [Function.update_apply, hr, hR26]
    · rw [hnil]; simp [Function.update_apply, hr, hR23]
    · rw [hnil]; exact hbl
    · rw [hnil]; simpa using hwl
    · intro a _ _; rw [← hm]

/-! ### Where the reverse list of `e` is -/

/-- The first word of the reverse list of `e` in section `6`. -/
def HierConcrete.revStart (x : HierConcrete) (e : ℕ) : ℕ :=
  x.m + 1 + ((List.range e).map fun i => (x.H.A.revList i).length).sum

theorem HierConcrete.sections_getD_6 (x : HierConcrete) :
    x.sections.getD 6 [] = csrList x.m x.H.A.revList := by
  simp [HierConcrete.sections]

/-- The words of section `6` from `revStart e` on are the reverse list of `e`. -/
theorem HierConcrete.revList_words (x : HierConcrete) {e : ℕ} (he : e < x.m) :
    (∀ k (hk : k < (x.H.A.revList e).length),
      (x.sections.getD 6 []).getD (x.revStart e + k) 0 = (x.H.A.revList e)[k]) ∧
    x.revStart e + (x.H.A.revList e).length ≤ (x.sections.getD 6 []).length := by
  rw [x.sections_getD_6]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [HierConcrete.revStart, csrList_getD_data _ he hk, List.getD_eq_getElem _ _ hk]
  · rcases Nat.eq_zero_or_pos (x.H.A.revList e).length with h0 | hpos
    · rw [h0, Nat.add_zero, HierConcrete.revStart]
      have h1 : ((List.range e).map fun i => (x.H.A.revList i).length).sum ≤
          ((List.range x.m).map fun i => (x.H.A.revList i).length).sum := by
        have mono : ∀ d, ((List.range e).map fun i => (x.H.A.revList i).length).sum ≤
            ((List.range (e + d)).map fun i => (x.H.A.revList i).length).sum := by
          intro d
          induction d with
          | zero => exact le_rfl
          | succ d ih =>
            rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append]; omega
        have := mono (x.m - e)
        rwa [Nat.add_sub_cancel' he.le] at this
      have h2 : (csrList x.m x.H.A.revList).length =
          x.m + 1 + ((List.range x.m).map fun i => (x.H.A.revList i).length).sum := by
        simp [csrList, csrData, List.length_flatMap]
      omega
    · have := csrList_data_lt x.H.A.revList he (k := (x.H.A.revList e).length - 1) (by omega)
      rw [HierConcrete.revStart]; omega

/-- The word after the reverse list of `e` is the start of the reverse list of `e + 1`. -/
theorem HierConcrete.revStart_succ (x : HierConcrete) (e : ℕ) :
    x.revStart (e + 1) = x.revStart e + (x.H.A.revList e).length := by
  simp [HierConcrete.revStart, List.range_succ, Nat.add_assoc]

/-- Set registers `27` and `26` to the first word and the end of the reverse list of the edge in
register `1`. -/
def scanSetupStmt : Stmt :=
  .seq (.assign 27 (.bin .add (.bin .add (readHdr 1) (.const 1)) (readSec numSec 0 6 (.reg 1))))
    (.assign 26 (.bin .add (.bin .add (readHdr 1) (.const 1))
      (readSec numSec 0 6 (.bin .add (.reg 1) (.const 1)))))

theorem scanSetupStmt_noRand : scanSetupStmt.NoRand := by
  simp [scanSetupStmt, Stmt.NoRand]

theorem scanSetup_triple {w : ℕ} {p : Program} (x : HierConcrete) {b e : ℕ} {R : ℕ → ℕ}
    {M : (ℕ → ℕ) → Prop} (hR0 : R 0 = b) (hR1 : R 1 = e) (he : e < x.m)
    (hM : ∀ mem, M mem → ListAt mem b x.encode) (hb : b + x.encode.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) scanSetupStmt
      (normalPost fun s => s.regs = Function.update (Function.update R 27 (x.revStart e)) 26
        (x.revStart (e + 1)) ∧ M s.mem)
      (fun _ => 60) := by
  have h25 := x.le_length_encode
  obtain ⟨_, hlo6⟩ := x.revList_words he
  have hpos6 : 0 < (x.sections.getD 6 []).length := by
    rw [x.sections_getD_6]; simp [csrList]
  have hs6 : (x.sections.getD 6 []).length ≤ x.encode.length := by
    have := lt_length_of_sec (bs := x.sections) (i := 6) (by rw [x.length_sections']; norm_num)
      (k := (x.sections.getD 6 []).length - 1) (by omega)
    have h : (layoutList x.sections).length = x.encode.length := rfl
    omega
  have hsucc := x.revStart_succ e
  have hrs : x.revStart (e + 1) < 2 ^ w := by omega
  have hmrs : x.m + 1 ≤ x.revStart (e + 1) := by rw [HierConcrete.revStart]; omega
  -- the reads
  have hread : ∀ s : State, ListAt s.mem b x.encode → s.regs 0 = b → ∀ {ke : Expr} {j : ℕ},
      ke.eval w s = some j → j ≤ e + 1 →
      (Expr.bin .add (.bin .add (readHdr 1) (.const 1)) (readSec numSec 0 6 ke)).eval w s =
        some (x.m + 1 + ((List.range j).map fun i => (x.H.A.revList i).length).sum) := by
    intro s hl h0 ke j hke hj'
    have hj : j ≤ x.m := by omega
    have hl' : ListAt s.mem b (layoutList x.sections) := hl
    have h1 := x.eval_readHdr hb h0 hl (k := 1) (by norm_num)
    simp [HierConcrete.header] at h1
    have hjl : j < (x.sections.getD 6 []).length := by
      rw [x.sections_getD_6]; simp [csrList]; omega
    have h6 := eval_readSec' (w := w) hl' hb h0 (i := 6) (by rw [x.length_sections']; norm_num)
      hke hjl
    rw [x.length_sections', x.sections_getD_6, csrList_getD_offset _ hj] at h6
    have hsum : x.m + 1 + ((List.range j).map fun i => (x.H.A.revList i).length).sum ≤
        x.revStart (e + 1) := by
      have mono : ∀ d, ((List.range j).map fun i => (x.H.A.revList i).length).sum ≤
          ((List.range (j + d)).map fun i => (x.H.A.revList i).length).sum := by
        intro d
        induction d with
        | zero => exact le_rfl
        | succ d ih =>
          rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append]; omega
      have := mono (e + 1 - j)
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [HierConcrete.revStart]; omega
    refine Expr.eval_add (Expr.eval_add h1 (Expr.eval_const (by omega)) (by
      show x.ms.abs.G.m + 1 < 2 ^ w
      have : x.m + 1 ≤ x.revStart (e + 1) := by rw [HierConcrete.revStart]; omega
      have : x.m = x.ms.abs.G.m := rfl
      omega)) h6 (by omega)
  have tA : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 27 (.bin .add (.bin .add (readHdr 1) (.const 1)) (readSec numSec 0 6 (.reg 1))))
      (normalPost fun s => s.regs = Function.update R 27 (x.revStart e) ∧ M s.mem)
      (fun _ => (Expr.bin .add (.bin .add (readHdr 1) (.const 1))
        (readSec numSec 0 6 (.reg 1))).size + 1) :=
    triple_assign_exact fun s hs hm =>
      hread s (hM _ hm) (by rw [hs, hR0]) (Expr.eval_reg_of_eq (by rw [hs, hR1])) (by omega)
  have tB : Triple w p (fun s => s.regs = Function.update R 27 (x.revStart e) ∧ M s.mem)
      (.assign 26 (.bin .add (.bin .add (readHdr 1) (.const 1))
        (readSec numSec 0 6 (.bin .add (.reg 1) (.const 1)))))
      (normalPost fun s => s.regs = Function.update (Function.update R 27 (x.revStart e)) 26
        (x.revStart (e + 1)) ∧ M s.mem)
      (fun _ => (Expr.bin .add (.bin .add (readHdr 1) (.const 1))
        (readSec numSec 0 6 (.bin .add (.reg 1) (.const 1)))).size + 1) :=
    triple_assign_exact fun s hs hm =>
      hread s (hM _ hm) (by rw [hs]; simpa using hR0)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := e) (by rw [hs]; simpa using hR1))
          (Expr.eval_const (by omega)) (by omega)) (by omega)
  exact (Triple.seq_normal_const tA tB).mono_cost fun _ _ => by
    simp only [readHdr, readSec, secAddr, Expr.size]; omega

theorem HierConcrete.revStart_succ_le (x : HierConcrete) {e : ℕ} (he : e < x.m) :
    x.revStart (e + 1) ≤ x.encode.length := by
  obtain ⟨_, hlo6⟩ := x.revList_words he
  have hpos6 : 0 < (x.sections.getD 6 []).length := by
    rw [x.sections_getD_6]; simp [csrList]
  have := lt_length_of_sec (bs := x.sections) (i := 6) (by rw [x.length_sections']; norm_num)
    (k := (x.sections.getD 6 []).length - 1) (by omega)
  have h : (layoutList x.sections).length = x.encode.length := rfl
  rw [x.revStart_succ]; omega

/-- **The scan of `Delete(e)`.** With the handle in register `0` and the edge `e` in register `1`,
`scanSetupStmt` then `scanStmt` leave the block of the loss state after the scan of the reverse
list of `e`, and append the newly lost terminals to the work list at `WB`. -/
theorem deleteScan_triple {w : ℕ} {p : Program} (x : HierConcrete) {F : Finset ℕ}
    {b e WB c0 : ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ} {R : ℕ → ℕ}
    (hR0 : R 0 = b) (hR1 : R 1 = e) (hR22 : R 22 = WB) (hR23 : R 23 = c0) (he : e < x.m)
    (hinv : LossInv x.H.A.x x.H.A.b F x.ms.st.loss)
    (hl : ∀ t ∈ x.H.A.revList e, t < 2 ^ x.H.A.x) (hL0 : L0.length = c0)
    (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x) (hb0 : 0 < x.H.A.b)
    (hb : b + x.encode.length < 2 ^ w) (hdb : (x.depth - 1) * x.H.A.b < 2 ^ w)
    (hd : x.depth < 2 ^ w) (h4x : 4 * 2 ^ x.H.A.x < 2 ^ w) (hblk : b + x.encode.length ≤ WB)
    (hW : WB + c0 + 2 * 2 ^ x.H.A.x < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) (.seq scanSetupStmt scanStmt)
      (normalPost fun s => s.regs 0 = b ∧ s.regs 22 = WB ∧
        s.regs 23 = c0 + (scan x.H.A.x x.H.A.b x.ms.st.loss (x.H.A.revList e)).2.length ∧
        ListAt s.mem b
          (x.withLoss (scan x.H.A.x x.H.A.b x.ms.st.loss (x.H.A.revList e)).1).encode ∧
        ListAt s.mem WB (L0 ++ (scan x.H.A.x x.H.A.b x.ms.st.loss (x.H.A.revList e)).2) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) → (a < WB + c0 ∨
          WB + c0 + (scan x.H.A.x x.H.A.b x.ms.st.loss (x.H.A.revList e)).2.length ≤ a) →
          s.mem a = mem0 a)
      (fun _ => 60 + (rangeCost (delScanStepCost x (x.H.A.revList e) (x.revStart e))
          (x.revStart e) (x.revStart e + (x.H.A.revList e).length) +
        (x.revStart e + (x.H.A.revList e).length - x.revStart e) * ((Expr.reg 26).size + 8) +
        ((Expr.reg 27).size + (Expr.reg 26).size + 5)) + 1) := by
  obtain ⟨hw6, hlo6⟩ := x.revList_words he
  have hle := x.revStart_succ_le he
  have hsucc := x.revStart_succ e
  have tS := scanSetup_triple (w := w) (p := p) x (b := b) (e := e) (R := R)
    (M := fun mem => ListAt mem b x.encode ∧ ListAt mem WB L0 ∧ mem = mem0) hR0 hR1 he
    (fun _ h => h.1) hb
  have tL := scan_triple (w := w) (p := p) x (F := F) (b := b) (WB := WB) (c0 := c0)
    (lo := x.revStart e) (l := x.H.A.revList e) (L0 := L0) (mem0 := mem0)
    (R := Function.update (Function.update R 27 (x.revStart e)) 26 (x.revStart (e + 1)))
    (by simp [hR0]) (by simp [hR22]) (by simp [hR23]) (by simp [hsucc]) (by simp)
    hinv hl hw6 hlo6 hL0 hnt hb0 hb hdb hd h4x hblk hW (by omega)
  refine (Triple.seq_normal_const tS (tL.weaken_pre fun s hs => ⟨hs.1, hs.2⟩)).strengthen_post
    fun o s h => ?_
  cases o with
  | returned => exact h.elim
  | normal =>
    obtain ⟨_, h0, h22, _, h23, hbl, hwl, hfr⟩ := h
    rw [Nat.add_sub_cancel_left, List.take_length] at h23 hbl hwl hfr
    exact ⟨h0, h22, h23, hbl, hwl, hfr⟩

end MinCostFlow.HierPaths

end
