module

public import MinCostFlow.MinRatio.InitConcretePostTail
import Mathlib.Tactic.Ring

/-!
# End-to-end execution of `solverInitPostTailBody`

Composes `initPostTailSetup`, `initDetectThresholdsAndRecords`, `initPostTailLinkArgs`,
`initLinkChainForests`, and `initPostTailStoreRootDir` into `solverInitPostTailBody_runs`,
populating the per-edge Detect thresholds, initial `PathEdgeAt` records, Section 6 link-cut
path tree for `chain.toTreeChain.chainTree`, and the 16-word root directory `SolverRootDirAt`
at `[root, root + 16)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Precomputed pure-arithmetic region inequalities for the monotonic post-tail layout,
avoiding repeated `omega` invocations in rich proof contexts. -/
private structure PostTailArith (w root table handle levelsEnd rootGraph gradient lengths
    forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace : ℕ) : Prop where
  root16_le_rootG : root + 16 ≤ rootGraph
  rootG_lt_table : rootGraph + 4 + 7 * n + 4 * m ≤ table
  table_le_handle : table + (d + 1) = handle
  handle_lt_lvl : handle + 17 + (d + 1) + (d + 1) ≤ levelsEnd
  levelsEnd_lt_fc : levelsEnd + (4 * (d + 1) + 1) = freshCounter
  fc_lt_fwd : freshCounter + 1 = forward
  fwd_le_inv : forward + m = inverse
  inv_le_th : inverse + m = edgeThresholds
  th_le_tree : edgeThresholds + m = treeHeap
  tree_le_end : treeHeap ≤ treeEnd
  len_le_root : lengths + m * L ≤ root
  grad_le_root : gradient + m * L ≤ root
  afterThresh_lt_w :
    treeEnd + m + 2 * n + 2 * n + m + m + m + 3 * L + m * initEdgeRecordSpace L +
      (d + 1) * levelSpace < 2 ^ w
  hw17 : 17 < 2 ^ w

private theorem postTailArith_root2_lt_w {w root table handle levelsEnd rootGraph gradient lengths
    forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace : ℕ}
    (A : PostTailArith w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace) :
    rootGraph + 2 < 2 ^ w ∧ handle + 16 < 2 ^ w ∧
    treeEnd + m + 2 * n + 2 * n + m + m + m < 2 ^ w ∧ 16 < 2 ^ w ∧
    rootGraph + 4 + 7 * n + 4 * m < 2 ^ w ∧ handle + 17 + (d + 1) < 2 ^ w ∧
    root + 16 < 2 ^ w ∧ handle + 14 < 2 ^ w ∧ freshCounter < 2 ^ w ∧ treeHeap < 2 ^ w := by
  have := A.root16_le_rootG; have := A.rootG_lt_table; have := A.table_le_handle
  have := A.handle_lt_lvl; have := A.levelsEnd_lt_fc; have := A.fc_lt_fwd
  have := A.fwd_le_inv; have := A.inv_le_th; have := A.th_le_tree; have := A.tree_le_end
  have := A.afterThresh_lt_w; have := A.hw17
  omega

private theorem postTailArith_stage2 {w root table handle levelsEnd rootGraph gradient lengths
    forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace : ℕ}
    (A : PostTailArith w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace) :
    let edgeRecords := treeEnd + m + 2 * n + 2 * n
    let threshHeap := treeEnd + m + 2 * n + 2 * n + m + m + m
    lengths + m * L ≤ threshHeap ∧ gradient + m * L ≤ threshHeap ∧
    edgeThresholds + m ≤ threshHeap ∧ edgeRecords + m ≤ threshHeap ∧
    edgeThresholds + m ≤ edgeRecords ∧
    lengths + m * L ≤ edgeThresholds ∧ lengths + m * L ≤ edgeRecords ∧
    gradient + m * L ≤ edgeThresholds ∧ gradient + m * L ≤ edgeRecords ∧
    threshHeap + 3 * L + m * initEdgeRecordSpace L < 2 ^ w ∧ 2 < 2 ^ w ∧
    handle + 1 < threshHeap ∧ handle + 3 < threshHeap ∧
    handle + 1 < edgeThresholds ∧ handle + 3 < edgeThresholds ∧
    handle + 1 < edgeRecords ∧ handle + 3 < edgeRecords ∧
    root + 16 ≤ handle ∧ handle + 17 + (d + 1) + (d + 1) ≤ edgeThresholds ∧
    edgeThresholds + m ≤ treeEnd ∧ treeEnd + m + 2 * n + 2 * n ≤ threshHeap := by
  have := A.root16_le_rootG; have := A.rootG_lt_table; have := A.table_le_handle
  have := A.handle_lt_lvl; have := A.levelsEnd_lt_fc; have := A.fc_lt_fwd
  have := A.fwd_le_inv; have := A.inv_le_th; have := A.th_le_tree; have := A.tree_le_end
  have := A.len_le_root; have := A.grad_le_root; have := A.afterThresh_lt_w; have := A.hw17
  dsimp only; omega

private theorem postTailArith_stage4 {w root table handle levelsEnd rootGraph gradient lengths
    forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace : ℕ}
    (A : PostTailArith w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace) :
    let slots := treeEnd
    let names := treeEnd + m
    let slotThresholds := treeEnd + m + 2 * n
    let edgeRecords := treeEnd + m + 2 * n + 2 * n
    let threshHeap := treeEnd + m + 2 * n + 2 * n + m + m + m
    let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
    slots + m ≤ afterThresh ∧ names + 2 * n ≤ afterThresh ∧ slotThresholds + 2 * n ≤ afterThresh ∧
    slots + m ≤ names ∧ slots + m ≤ slotThresholds ∧ names + 2 * n ≤ slotThresholds ∧
    7 < 2 ^ w ∧ afterThresh + (d + 1) * levelSpace < 2 ^ w ∧
    handle + 17 + (d + 1) + (d + 1) ≤ treeHeap ∧ treeHeap ≤ slots ∧
    edgeRecords + m ≤ threshHeap ∧ threshHeap ≤ afterThresh ∧
    handle + 16 < levelsEnd ∧ levelsEnd ≤ edgeThresholds ∧
    root + 16 ≤ table ∧ table + (d + 1) ≤ handle + 17 + (d + 1) + (d + 1) ∧
    edgeThresholds + m ≤ treeEnd ∧ treeEnd ≤ edgeRecords := by
  have := A.root16_le_rootG; have := A.rootG_lt_table; have := A.table_le_handle
  have := A.handle_lt_lvl; have := A.levelsEnd_lt_fc; have := A.fc_lt_fwd
  have := A.fwd_le_inv; have := A.inv_le_th; have := A.th_le_tree; have := A.tree_le_end
  have := A.afterThresh_lt_w; have := A.hw17
  dsimp only; omega

private theorem pt_add_lt_br (h d j : ℕ) (hj : j < 17) :
    h + j < h + 17 + (d + 1) + (d + 1) := by omega

private theorem pt_add_ne_add (h a b : ℕ) (hab : a ≠ b) : h + a ≠ h + b := by omega

private theorem pt_add_add_ne (h a j b : ℕ) (hab : a + j ≠ b) : h + a + j ≠ h + b := by omega

private theorem pt_lvl_lt_br (h d i : ℕ) (hi : i ≤ d) :
    h + 17 + i < h + 17 + (d + 1) + (d + 1) ∧ h + 17 + i ≠ h + 1 ∧ h + 17 + i ≠ h + 3 := by omega

private theorem pt_br_lt_br (h d i : ℕ) (hi : i ≤ d) :
    h + 17 + (d + 1) + i < h + 17 + (d + 1) + (d + 1) ∧
    h + 17 + (d + 1) + i ≠ h + 1 ∧ h + 17 + (d + 1) + i ≠ h + 3 := by omega

private theorem pt_table_lt_handle (t d h j : ℕ) (heq : h = t + (d + 1)) (hj : j ≤ d) :
    t + j < t + (d + 1) ∧ t + j ≠ h + 1 ∧ t + j ≠ h + 3 := by omega

private theorem pt_fresh_range (lv fc fwd inv et m e d : ℕ)
    (h1 : fc = lv + (4 * (d + 1) + 1)) (h2 : fwd = fc + 1) (h3 : inv = fwd + m) (h4 : et = inv + m) :
    (lv ≤ fc ∧ fc < et) ∧ (e < m → lv ≤ fwd + e ∧ fwd + e < et) ∧
    (e < m → lv ≤ inv + e ∧ inv + e < et) ∧ (fc ≤ et) := by omega

private theorem pt_inOff_range (treeEnd m n e : ℕ) (he : e < m) :
    treeEnd + m + 2 * n + 2 * n + m ≤ treeEnd + m + 2 * n + 2 * n + m + m + e ∧
    treeEnd + m + 2 * n + 2 * n + m + m + e < treeEnd + m + 2 * n + 2 * n + m + m + m := by omega

private theorem pt_th_rec_bounds (threshHeap L e j a : ℕ) :
    threshHeap ≤ threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L ∧
    threshHeap ≤ threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L ∧
    threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L ≤
      threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + (2 + 4 * L) ∧
    (j < L → threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + j <
      threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + (2 + 4 * L)) ∧
    (a < threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + (2 + 4 * L) →
      a < threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + (2 + 4 * L)) := by
  omega

/-- Stages 1–3 of `solverInitPostTailBody`. -/
private theorem initPostTailStages123_runs
    {w shift divide negate copy root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L P epsExp d levelSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (lenInt : ℕ → ℕ) (gradInt : ℕ → ℤ)
    (A : PostTailArith w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n L d levelSpace)
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = P) (h69 : st.regs 69 = rootGraph)
    (h70 : st.regs 70 = gradient) (h71 : st.regs 71 = lengths)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (h80 : st.regs 80 = treeHeap) (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m) (h85 : st.regs 85 = freshCounter)
    (h99 : st.regs 99 = treeEnd)
    (hnCell : st.mem (rootGraph + 2) = n) (hepsCell : st.mem (handle + 16) = epsExp)
    (hlenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt st.mem (lengths + e * L) 4 L (lenInt e))
    (hgradAt : ∀ e < m, PathIntAt st.mem (gradient + e * L) 4 L (gradInt e))
    (hfits : ∀ e < m,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
      Num.Fits 4 L (-th) ∧ Num.Fits 4 L th)
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L)
    (hleEps : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hz : ZeroFrom st.mem treeEnd) :
    let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
    let slots := treeEnd
    let names := treeEnd + m
    let slotThresholds := treeEnd + m + 2 * n
    let edgeRecords := treeEnd + m + 2 * n + 2 * n
    let offReadyList := treeEnd + m + 2 * n + 2 * n + m
    let inOffReady := treeEnd + m + 2 * n + 2 * n + m + m
    let threshHeap := treeEnd + m + 2 * n + 2 * n + m + m + m
    let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
    let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
    let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
    let val := fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)
    ∃ s3 cost,
      Runs w p ω (initPostTailSetup ;; initDetectThresholdsAndRecords shift divide negate copy ;;
        initPostTailLinkArgs) st .normal s3 cost ∧
      s3.regs 0 = treeHeap ∧ s3.regs 3 = afterThresh ∧
      s3.regs 9 = dgETailSlotBase rootGraph n m ∧
      s3.regs 10 = dgEHeadSlotBase rootGraph n m ∧
      s3.regs 11 = dgIntToExtBase rootGraph n ∧
      s3.regs 19 = slots ∧ s3.regs 20 = names ∧ s3.regs 22 = edgeRecords ∧
      s3.regs 23 = edgeThresholds ∧ s3.regs 24 = slotThresholds ∧
      s3.regs 29 = handle + 17 ∧ s3.regs 30 = handle + 17 + (d + 1) ∧
      s3.regs 31 = d ∧ s3.regs 34 = rootGraph ∧
      s3.regs 69 = rootGraph ∧ s3.regs 74 = handle ∧ s3.regs 75 = d ∧
      s3.regs 81 = forward ∧ s3.regs 82 = inverse ∧ s3.regs 83 = edgeThresholds ∧
      s3.regs 84 = m ∧ s3.regs 85 = freshCounter ∧ s3.regs 86 = edgeRecords ∧
      s3.regs 87 = slots ∧ s3.regs 88 = names ∧ s3.regs 89 = slotThresholds ∧
      s3.regs 90 = offReadyList ∧ s3.regs 91 = inOffReady ∧
      s3.mem (handle + 1) = names ∧ s3.mem (handle + 3) = slotThresholds ∧
      (∀ e < m, s3.mem (edgeThresholds + e) = thPtr e ∧ s3.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt s3.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt s3.mem (recPtr e) 4 L (some (val e))) ∧
      ZeroFrom s3.mem afterThresh ∧
      (∀ a < threshHeap, (a < edgeThresholds ∨ edgeThresholds + m ≤ a) →
        (a < edgeRecords ∨ edgeRecords + m ≤ a) → a ≠ handle + 1 → a ≠ handle + 3 →
        s3.mem a = st.mem a) := by
  intro ε slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh thPtr recPtr val
  obtain ⟨hroot2W, hh16W, hthW, hw16, hdgW, hbrW, _, _, _, _⟩ := postTailArith_root2_lt_w A
  obtain ⟨hlenT, hgradT, hthT, hrecT, hthRec, hlenTh, hlenRec, hgradTh, hgradRec,
      hafterW, hw2, hh1T, hh3T, hh1Th, hh3Th, hh1Rec, hh3Rec, hrootH, _, _, _⟩ := postTailArith_stage2 A
  obtain ⟨s1, c1, hr1, hs1_92, hs1_87, hs1_88, hs1_89, hs1_86, hs1_90, hs1_91, hs1_99, hs1_73,
      hs1_regs, hs1_h1, hs1_h3, hs1_frame⟩ :=
    initPostTailSetup_runs (w := w) (p := p) (ω := ω) (st := st)
      h69 h74 h84 h99 hnCell hepsCell hroot2W hh16W hthW hw16
  have hs1_r (r : ℕ) (hr : r ≤ 85) (h73 : r ≠ 73) : s1.regs r = st.regs r :=
    hs1_regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h73
  have hltH (x : ℕ) (hx : x < root) : x ≠ handle + 1 ∧ x ≠ handle + 3 :=
    ⟨Nat.ne_of_lt (lt_of_lt_of_le hx (le_trans (Nat.le_add_right root 16) (le_trans hrootH (Nat.le_add_right handle 1)))),
     Nat.ne_of_lt (lt_of_lt_of_le hx (le_trans (Nat.le_add_right root 16) (le_trans hrootH (Nat.le_add_right handle 3))))⟩
  have hs1_lenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt s1.mem (lengths + e * L) 4 L (lenInt e) := by
    intro e he
    have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at hm
    refine ⟨(hlenAt e he).1, (hlenAt e he).2.congr (fun j hj => ?_)⟩
    have hlt : lengths + e * L + j < root := lt_of_lt_of_le (by omega) A.len_le_root
    exact hs1_frame _ (hltH _ hlt).1 (hltH _ hlt).2
  have hs1_gradAt : ∀ e < m, PathIntAt s1.mem (gradient + e * L) 4 L (gradInt e) := by
    intro e he
    have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at hm
    refine (hgradAt e he).congr (fun j hj => ?_)
    have hlt : gradient + e * L + j < root := lt_of_lt_of_le (by omega) A.grad_le_root
    exact hs1_frame _ (hltH _ hlt).1 (hltH _ hlt).2
  have hs1_z : ZeroFrom s1.mem threshHeap := fun a ha =>
    (hs1_frame a (Nat.ne_of_gt (lt_of_lt_of_le hh1T ha)) (Nat.ne_of_gt (lt_of_lt_of_le hh3T ha))).trans
      (hz a (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_right treeEnd m)
        (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _))
        (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) ha))
  obtain ⟨s2, c2, hr2, hs2_99, hs2_edges, hs2_z, hs2_frame, hs2_regs, _⟩ :=
    initDetectThresholdsAndRecords_runs (w := w) (p := p) (ω := ω) (st := s1) lenInt gradInt
      hshift hdiv hneg hcopy
      ((hs1_r 67 (by decide) (by decide)).trans h67)
      ((hs1_r 68 (by decide) (by decide)).trans h68)
      ((hs1_r 70 (by decide) (by decide)).trans h70)
      ((hs1_r 71 (by decide) (by decide)).trans h71)
      hs1_73
      ((hs1_r 83 (by decide) (by decide)).trans h83)
      ((hs1_r 84 (by decide) (by decide)).trans h84)
      hs1_86 hs1_99 hPdiv hPword hLpos hleEps hfitEps
      hlenT hgradT hthT hrecT (Or.inl hthRec)
      (Or.inl hlenTh) (Or.inl hlenRec) (Or.inl hgradTh) (Or.inl hgradRec)
      hs1_lenAt hs1_gradAt hfits hs1_z hafterW hw2
  have hs2_r85 (r : ℕ) (hlo : 8 ≤ r) (hhi : r ≤ 85) (h73 : r ≠ 73) : s2.regs r = st.regs r :=
    (hs2_regs r hlo (by omega) (by omega)).trans (hs1_r r hhi h73)
  obtain ⟨s3, c3, hr3, hs3_mem, hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20,
      hs3_22, hs3_23, hs3_24, hs3_29, hs3_30, hs3_31, hs3_34, hs3_regs⟩ :=
    initPostTailLinkArgs_runs (w := w) (p := p) (ω := ω) (st := s2)
      ((hs2_r85 80 (by decide) (by decide) (by decide)).trans h80)
      hs2_99
      ((hs2_r85 69 (by decide) (by decide) (by decide)).trans h69)
      ((hs2_regs 92 (by decide) (by decide) (by decide)).trans hs1_92)
      ((hs2_r85 84 (by decide) (by decide) (by decide)).trans h84)
      ((hs2_regs 87 (by decide) (by decide) (by decide)).trans hs1_87)
      ((hs2_regs 88 (by decide) (by decide) (by decide)).trans hs1_88)
      ((hs2_regs 86 (by decide) (by decide) (by decide)).trans hs1_86)
      ((hs2_r85 83 (by decide) (by decide) (by decide)).trans h83)
      ((hs2_regs 89 (by decide) (by decide) (by decide)).trans hs1_89)
      ((hs2_r85 74 (by decide) (by decide) (by decide)).trans h74)
      ((hs2_r85 75 (by decide) (by decide) (by decide)).trans h75)
      hdgW hbrW A.hw17
  have hs3_r85 (r : ℕ) (hlo : 36 ≤ r) (hhi : r ≤ 85) (h73 : r ≠ 73) : s3.regs r = st.regs r :=
    (hs3_regs r hlo).trans (hs2_r85 r (by omega) hhi h73)
  have hs3_rhi (r : ℕ) (hlo : 86 ≤ r) (hhi : r ≤ 91) : s3.regs r = s1.regs r :=
    (hs3_regs r (by omega)).trans (hs2_regs r (by omega) (by omega) (by omega))
  refine ⟨s3, c1 + (c2 + c3 + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2 + c3 + 1, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, c3, hr2, hr3, rfl⟩), rfl⟩),
    hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20, hs3_22, hs3_23, hs3_24,
    hs3_29, hs3_30, hs3_31, hs3_34,
    (hs3_r85 69 (by decide) (by decide) (by decide)).trans h69,
    (hs3_r85 74 (by decide) (by decide) (by decide)).trans h74,
    (hs3_r85 75 (by decide) (by decide) (by decide)).trans h75,
    (hs3_r85 81 (by decide) (by decide) (by decide)).trans h81,
    (hs3_r85 82 (by decide) (by decide) (by decide)).trans h82,
    (hs3_r85 83 (by decide) (by decide) (by decide)).trans h83,
    (hs3_r85 84 (by decide) (by decide) (by decide)).trans h84,
    (hs3_r85 85 (by decide) (by decide) (by decide)).trans h85,
    (hs3_rhi 86 (by decide) (by decide)).trans hs1_86,
    (hs3_rhi 87 (by decide) (by decide)).trans hs1_87,
    (hs3_rhi 88 (by decide) (by decide)).trans hs1_88,
    (hs3_rhi 89 (by decide) (by decide)).trans hs1_89,
    (hs3_rhi 90 (by decide) (by decide)).trans hs1_90,
    (hs3_rhi 91 (by decide) (by decide)).trans hs1_91,
    by rw [hs3_mem]; exact (hs2_frame (handle + 1) hh1T (Or.inl hh1Th) (Or.inl hh1Rec)).trans hs1_h1,
    by rw [hs3_mem]; exact (hs2_frame (handle + 3) hh3T (Or.inl hh3Th) (Or.inl hh3Rec)).trans hs1_h3,
    by rw [hs3_mem]; exact hs2_edges,
    by rw [hs3_mem]; exact hs2_z,
    fun a ha hth hrec hh1 hh3 => by rw [hs3_mem]; exact (hs2_frame a ha hth hrec).trans (hs1_frame a hh1 hh3)⟩

/-- Run the complete concrete post-tail right after `finishSolverInitBody`. -/
theorem solverInitPostTailBody_runs
    {w shift divide negate copy bind initCore initLast initTree treeConst
      root table handle levelsEnd rootGraph gradient lengths forward inverse
      edgeThresholds freshCounter treeHeap treeEnd m L P V k Ψ epsExp
      searchSpace readSpace levelSpace linkSpace lastMult stretchP vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {costs : SparseCoreMachineCosts}
    {coreAlloc : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
    {Mcap Ncap : ℕ → ℕ} {Rcore : DSRep T.State}
    {Rterm : DSRep (ℕ × (ℕ → LSF))} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} (lenInt : ℕ → ℕ) (gradInt : ℕ → ℤ) (B : ℤ)
    {xCore : ℕ → Rcore.τ} {xTerm : Rterm.τ} {sTree : PathTreeState} {xTree : Rtree.τ}
    (hfmt4 : fmt.limbBits = 4)
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreImpl : ∀ i < C.d, ∀ vc ec, Rcore.Implements w p initCore opCore
      (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (coreAlloc i)))
    (htermImpl : Rterm.Implements w p initLast opLast
      (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vcLast ecLast lastMult stretchP lastAlloc))
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hcoreInput : ∀ i < C.d,
      SparseCoreInput T.toSparseCoreTool T.restart C.k (chain.scState i) (chain.G i))
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = P) (h69 : st.regs 69 = rootGraph)
    (h70 : st.regs 70 = gradient) (h71 : st.regs 71 = lengths)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = C.d)
    (h80 : st.regs 80 = treeHeap) (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m) (h85 : st.regs 85 = freshCounter)
    (h99 : st.regs 99 = treeEnd)
    (hhandleEq : handle = table + (C.d + 1))
    (hfreshEq : freshCounter = levelsEnd + (4 * (C.d + 1) + 1))
    (hrootLe : root + 16 ≤ rootGraph)
    (hrootGEnd : rootGraph + dynGraphSize G.n G.m ≤ table)
    (hlevGe : handle + 17 + (C.d + 1) + (C.d + 1) ≤ levelsEnd)
    (hfwdEq : forward = freshCounter + 1)
    (hinvEq : inverse = forward + m)
    (hthEq : edgeThresholds = inverse + m)
    (htreeEq : treeHeap = edgeThresholds + m)
    (htreeLe : treeHeap ≤ treeEnd)
    (hlenBelow : lengths + m * L ≤ root) (hgradBelow : gradient + m * L ≤ root)
    (hG : DynGraphAt st.mem rootGraph G.n G.m G) (hGm : G.m = m)
    (hdetect0 : DetectHeaderAt st.mem handle treeHeap forward inverse edgeThresholds m L searchSpace readSpace)
    (hnum0 : MinRatioNumericHeaderAt st.mem handle L P searchSpace readSpace)
    (hchain0 : ChainInitParametersAt st.mem handle m V C.d C.k Ψ (root + 16) k epsExp)
    (hfresh0 : FreshTablesAt st.mem forward inverse freshCounter m m id id m)
    (hsched0 : ∀ a, levelsEnd ≤ a → a < freshCounter → st.mem a = 0)
    (hrepTree0 : Rtree.rep treeHeap sTree xTree st.mem)
    (hinitTreePost : (pathTreeMachineContract fmt L treeConst treeAlloc).initPost
      [G.n, L, treeHeap] st.mem sTree st.mem)
    (hfootTree0 : ∀ a, Rtree.foot treeHeap xTree a → treeHeap ≤ a ∧ a < treeEnd)
    (hcores0 : ∀ i < C.d,
      st.mem (handle + 17 + (C.d + 1) + i) = chain.bran i ∧
      Rcore.rep (st.mem (handle + 17 + i)) (chain.scState i) (xCore i) st.mem ∧
      (∀ a, Rcore.foot (st.mem (handle + 17 + i)) (xCore i) a →
        handle + 17 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
        (∀ j < C.d, j ≠ i → ¬ Rcore.foot (st.mem (handle + 17 + j)) (xCore j) a) ∧
        ¬ Rterm.foot (st.mem (handle + 17 + C.d)) xTerm a))
    (hlastBr0 : st.mem (handle + 17 + (C.d + 1) + C.d) = chain.lastBran)
    (hrepTerm0 : Rterm.rep (st.mem (handle + 17 + C.d)) (chain.lastK, chain.lastLSFs) xTerm st.mem)
    (hfootTerm0 : ∀ a, Rterm.foot (st.mem (handle + 17 + C.d)) xTerm a →
      handle + 17 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ j < C.d, ¬ Rcore.foot (st.mem (handle + 17 + j)) (xCore j) a))
    (hhandlesW : ∀ i ≤ C.d, st.mem (handle + 17 + i) < 2 ^ w ∧
      st.mem (handle + 17 + (C.d + 1) + i) < 2 ^ w)
    (hlenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt st.mem (lengths + e * L) 4 L (lenInt e))
    (hgradAt : ∀ e < m, PathIntAt st.mem (gradient + e * L) 4 L (gradInt e))
    (hfits : ∀ e < m,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
      Num.Fits 4 L (-th) ∧ Num.Fits 4 L th)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let v := initialPathEdgeValue P ε (gradInt e) (lenInt e)
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B)
    (hB : 0 ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity 4 L : ℤ))
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L)
    (hleEps : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hdW : C.d < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hz : ZeroFrom st.mem treeEnd)
    (hreadoutBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (fv fe : ℕ) (yCore : Rcore.τ),
      treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ cur →
      cur ≤ ret →
      LSFAt mem' cur fv fe fmt.limbBits L fmt.precision (chain.G i).E (T.lsfs (chain.scState i) (chain.bran i)) →
      let fBase := mem' (cur + 1)
      fBase + dynGraphSize fv fe ≤ ret ∧
      (∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        Rcore.foot (st.mem (handle + 17 + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hgraphReadBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (gv ge : ℕ) (yCore : Rcore.τ),
      treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ cur →
      cur ≤ ret →
      DynGraphAt mem' (mem' cur) gv ge (chain.G (i + 1)) →
      mem' cur + dynGraphSize gv ge ≤ ret ∧
      (∀ a, mem' cur ≤ a → a < mem' cur + dynGraphSize gv ge →
        Rcore.foot (st.mem (handle + 17 + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hlastReadBounds : ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (fv fe : ℕ) (yTerm : Rterm.τ),
      treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ cur →
      cur ≤ ret →
      LSFAt mem' cur fv fe fmt.limbBits L fmt.precision (chain.G C.d).E (chain.lastLSFs chain.lastBran) →
      let fBase := mem' (cur + 1)
      fBase + dynGraphSize fv fe ≤ ret ∧
      (∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        Rterm.foot (st.mem (handle + 17 + C.d)) yTerm a ∨ (cur ≤ a ∧ a < ret)))
    (hlevelCap : ∀ i < C.d, 5 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace ≤ levelSpace)
    (hlastCap : 4 + (chain.toTreeChain.activeLSF C.d).F.F.m * linkSpace ≤ levelSpace)
    (hlinkAlloc :
      let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
      let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
      ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
        afterThresh ≤ cur → cur ≤ afterThresh + (C.d + 1) * levelSpace →
        treeAlloc 0 G.n [treeHeap, G.tail e + 1, G.head e + 1,
          threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L, cur] ≤ linkSpace)
    (hroom :
      treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L +
        (C.d + 1) * levelSpace < 2 ^ w) :
    let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
    let slots := treeEnd
    let names := treeEnd + m
    let slotThresholds := treeEnd + m + 2 * G.n
    let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
    let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
    let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
    let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
    let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
    let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
    let val := fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)
    ∃ (out : State) (finalHeap cost : ℕ) (sFin : PathTreeState) (yTree : Rtree.τ)
      (slotFin nameFin : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (yTerm : Rterm.τ),
      Runs w p ω
        (solverInitPostTailBody shift divide negate copy (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        st .normal out cost ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      DetectHeaderAt out.mem handle treeHeap names inverse slotThresholds m L searchSpace readSpace ∧
      MinRatioNumericHeaderAt out.mem handle L P searchSpace readSpace ∧
      ChainInitParametersAt out.mem handle m V C.d C.k Ψ (root + 16) k epsExp ∧
      FreshTablesAt out.mem forward inverse freshCounter m m id id m ∧
      (∀ a, levelsEnd ≤ a → a < freshCounter → out.mem a = 0) ∧
      (∀ e < m, out.mem (inOffReady + e) = 0) ∧
      (∀ e < m,
        out.mem (edgeThresholds + e) = thPtr e ∧
        out.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt out.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt out.mem (recPtr e) 4 L (some (val e))) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap out.mem ∧
      (∀ i < C.d, Rcore.rep (st.mem (handle + 17 + i)) (chain.scState i) (yCore i) out.mem ∧
        ∀ a, Rcore.foot (st.mem (handle + 17 + i)) (yCore i) a → a < finalHeap) ∧
      Rterm.rep (st.mem (handle + 17 + C.d)) (chain.lastK, chain.lastLSFs) yTerm out.mem ∧
      (∀ a, Rterm.foot (st.mem (handle + 17 + C.d)) yTerm a → a < finalHeap) ∧
      (∀ j ≤ C.d, out.mem (table + j) = st.mem (table + j)) ∧
      (∀ i ≤ C.d, out.mem (handle + 17 + i) = st.mem (handle + 17 + i) ∧
        out.mem (handle + 17 + (C.d + 1) + i) = st.mem (handle + 17 + (C.d + 1) + i)) ∧
      (∀ a < root, out.mem a = st.mem a) ∧
      ZeroFrom out.mem finalHeap ∧ treeEnd ≤ finalHeap ∧
      DynGraphAt out.mem rootGraph G.n m G ∧
      threshHeap + 3 * L + m * initEdgeRecordSpace L ≤ finalHeap ∧
      finalHeap ≤ threshHeap + 3 * L + m * initEdgeRecordSpace L + (C.d + 1) * levelSpace ∧
      (∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootGraph (handle + 17) (handle + 17 + (C.d + 1)) edgeRecords edgeThresholds
          C.d m L G chain.toTreeChain.chainTree recPtr
          (fun a => a < handle + 17 + (C.d + 1) + (C.d + 1) ∨
            (levelsEnd ≤ a ∧ a < treeHeap) ∨
            (edgeRecords + m ≤ a ∧ a < threshHeap + 3 * L + m * initEdgeRecordSpace L)) a) ∧
      InitChainCoresAt Rcore Rterm Rtree chain treeHeap (handle + 17) (handle + 17 + (C.d + 1))
        rootGraph edgeRecords edgeThresholds slots names slotThresholds m L finalHeap G recPtr
        (fun a => a < handle + 17 + (C.d + 1) + (C.d + 1) ∨
          (levelsEnd ≤ a ∧ a < treeHeap) ∨
          (edgeRecords + m ≤ a ∧ a < threshHeap + 3 * L + m * initEdgeRecordSpace L))
        yCore yTerm yTree out.mem := by
  intro ε slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap thPtr recPtr val
  let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
  let levelTable := handle + 17
  let branchTable := levelTable + (C.d + 1)
  have hdgSz : rootGraph + 4 + 7 * G.n + 4 * m ≤ rootGraph + dynGraphSize G.n G.m := by
    rw [← hGm]; unfold dynGraphSize; omega
  have hArith : PostTailArith w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m G.n L C.d levelSpace :=
    ⟨hrootLe, le_trans hdgSz hrootGEnd, hhandleEq.symm, hlevGe, hfreshEq.symm, hfwdEq.symm,
      hinvEq.symm, hthEq.symm, htreeEq.symm, htreeLe, hlenBelow, hgradBelow, hroom, hw17⟩
  obtain ⟨_, _, _, hw16, _, _, hroot16W, hh14W, hfcW, hthW⟩ := postTailArith_root2_lt_w hArith
  obtain ⟨hslA, hnmA, hstA, hslNm, hslSt, hnmSt, hw7, hafterRoom,
      hbrLeTh, hthLeSl, herLeTh, hthLeA, hh16Lv, hlvLeEt, hrootTb, htbLeBr, hetLeEnd, hendLeEr⟩ :=
    postTailArith_stage4 hArith
  have hgnCell : st.mem (rootGraph + 2) = G.n := hG.2.2.2.2.2.1
  have hepsCell : st.mem (handle + 16) = epsExp := by simpa [Nat.add_assoc] using hchain0 7 (by simp)
  have halphaCell : st.mem (handle + 14) = root + 16 := by simpa [Nat.add_assoc] using hchain0 5 (by simp)
  -- Stages 1–3
  obtain ⟨s3, c123, hr123, hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20, hs3_22, hs3_23,
      hs3_24, hs3_29, hs3_30, hs3_31, hs3_34, hs3_69, hs3_74, hs3_75, hs3_81, hs3_82, hs3_83,
      hs3_84, hs3_85, hs3_86, hs3_87, hs3_88, hs3_89, hs3_90, hs3_91,
      hs3_h1, hs3_h3, hs3_edges, hs3_z, hs3_keep⟩ :=
    initPostTailStages123_runs lenInt gradInt hArith hshift hdiv hneg hcopy
      h67 h68 h69 h70 h71 h74 h75 h80 h81 h82 h83 h84 h85 h99
      hgnCell hepsCell hlenAt hgradAt hfits hPdiv hPword hLpos hleEps hfitEps hz
  -- Stage 4
  let extraStatic (a : ℕ) : Prop :=
    a < branchTable + (C.d + 1) ∨
    (levelsEnd ≤ a ∧ a < treeHeap) ∨
    (edgeRecords + m ≤ a ∧ a < afterThresh)
  have hSub := chain.toTreeChain.forestsAreSubgraphs_of_holds hH
  have hTSub : chain.toTreeChain.chainTree.E ⊆ G.E := by
    have hs := chain.toTreeChain.chainTree_isSubgraph hH hSub
    rw [hH.1] at hs; exact hs.2.1
  have hrecEnd (e : ℕ) (he : e < m) : recPtr e + (2 + 4 * L) ≤ afterThresh := by
    have hm : (e + 1) * initEdgeRecordSpace L ≤ m * initEdgeRecordSpace L :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at hm
    dsimp only [recPtr, afterThresh, initEdgeRecordSpace] at hm ⊢
    omega
  have hkeep_lt_et (a : ℕ) (ha : a < edgeThresholds) (hh1 : a ≠ handle + 1) (hh3 : a ≠ handle + 3) :
      s3.mem a = st.mem a :=
    hs3_keep a (lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) (le_trans hetLeEnd (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) herLeTh)))))
      (Or.inl ha) (Or.inl (lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) (le_trans hetLeEnd hendLeEr)))) hh1 hh3
  have hkeep_tree_er (a : ℕ) (h1 : treeHeap ≤ a) (h2 : a < edgeRecords) : s3.mem a = st.mem a :=
    hs3_keep a (lt_of_lt_of_le h2 (le_trans (Nat.le_add_right _ _) herLeTh))
      (Or.inr (htreeEq ▸ h1)) (Or.inl h2)
      (Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (pt_add_lt_br handle C.d 1 (by decide)) hbrLeTh) h1))
      (Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (pt_add_lt_br handle C.d 3 (by decide)) hbrLeTh) h1))
  have hbelow_lt (a : ℕ) (ha : a < treeHeap) :
      a < afterThresh ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ Rtree.foot treeHeap xTree a :=
    ⟨lt_of_lt_of_le ha (le_trans hthLeSl (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans herLeTh hthLeA)))),
     ⟨Or.inl (lt_of_lt_of_le ha hthLeSl),
      Or.inl (lt_of_lt_of_le ha (le_trans hthLeSl (Nat.le_add_right _ _))),
      Or.inl (lt_of_lt_of_le ha (le_trans hthLeSl (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))⟩,
     fun hf => Nat.not_lt_of_ge (hfootTree0 a hf).1 ha⟩
  have hbelow_ge (a : ℕ) (h1 : edgeRecords ≤ a) (h2 : a < afterThresh) :
      a < afterThresh ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ Rtree.foot treeHeap xTree a :=
    ⟨h2,
     ⟨Or.inr (le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h1),
      Or.inr (le_trans (Nat.le_add_right _ _) h1),
      Or.inr h1⟩,
     fun hf => Nat.not_lt_of_ge (le_trans hendLeEr h1) (hfootTree0 a hf).2⟩
  have hstaticBelow : ∀ a, InitChainStaticAddr rootGraph levelTable branchTable
      edgeRecords edgeThresholds C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a →
      a < afterThresh ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ Rtree.foot treeHeap xTree a := by
    intro a ha
    rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨e, he, h1, h2⟩ | hex
    · exact hbelow_lt a (lt_of_lt_of_le h2 (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans htbLeBr hbrLeTh))))
    · exact hbelow_lt a (lt_of_le_of_lt h2 (lt_of_lt_of_le (pt_lvl_lt_br handle C.d C.d le_rfl).1 hbrLeTh))
    · exact hbelow_lt a (lt_of_le_of_lt h2 (lt_of_lt_of_le (pt_br_lt_br handle C.d C.d le_rfl).1 hbrLeTh))
    · exact hbelow_ge a h1 (lt_of_lt_of_le h2 (le_trans herLeTh hthLeA))
    · exact hbelow_lt a (htreeEq.symm ▸ h2)
    · have hem : e < m := hGm ▸ hG.2.2.1 e (hTSub he)
      have hlo : edgeRecords ≤ recPtr e :=
        le_trans (Nat.le_add_right _ _) (le_trans herLeTh (pt_th_rec_bounds threshHeap L e 0 0).2.1)
      exact hbelow_ge a (le_trans hlo h1) (lt_of_lt_of_le h2 (hrecEnd e hem))
    · rcases hex with h1 | ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact hbelow_lt a (lt_of_lt_of_le h1 hbrLeTh)
      · exact hbelow_lt a h2
      · exact hbelow_ge a (le_trans (Nat.le_add_right _ _) h1) h2
  have hnotStaticOfCore (a : ℕ) (hlo : branchTable + (C.d + 1) ≤ a) (hhi : a < levelsEnd) :
      ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds C.d m L
        G chain.toTreeChain.chainTree recPtr extraStatic a := by
    rintro (⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨e, _, h1, _⟩ | (h1 | ⟨h1, _⟩ | ⟨h1, _⟩))
    · exact Nat.not_lt_of_ge hlo (lt_of_lt_of_le h2 (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) htbLeBr)))
    · exact Nat.not_lt_of_ge hlo (lt_of_le_of_lt h2 (pt_lvl_lt_br handle C.d C.d le_rfl).1)
    · exact Nat.not_lt_of_ge hlo (lt_of_le_of_lt h2 (pt_br_lt_br handle C.d C.d le_rfl).1)
    · exact Nat.not_lt_of_ge h1 (lt_of_lt_of_le hhi (le_trans hlvLeEt (le_trans (Nat.le_add_right _ _) (le_trans hetLeEnd hendLeEr))))
    · exact Nat.not_lt_of_ge h1 (lt_of_lt_of_le hhi hlvLeEt)
    · have hrecGe : levelsEnd ≤ recPtr e :=
        le_trans hlvLeEt (le_trans (Nat.le_add_right _ _) (le_trans hetLeEnd (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans herLeTh (pt_th_rec_bounds threshHeap L e 0 0).2.1)))))
      exact Nat.not_lt_of_ge (le_trans hrecGe h1) hhi
    · exact Nat.not_lt_of_ge hlo h1
    · exact Nat.not_lt_of_ge h1 hhi
    · exact Nat.not_lt_of_ge h1 (lt_of_lt_of_le hhi (le_trans hlvLeEt (le_trans (Nat.le_add_right _ _) (le_trans hetLeEnd (le_trans hendLeEr (Nat.le_add_right _ _))))))
  have hs3_treeRep : Rtree.rep treeHeap sTree xTree s3.mem :=
    (htreeImpl.1 treeHeap sTree xTree st.mem s3.mem (fun a ha =>
      (hkeep_tree_er a (hfootTree0 a ha).1 (lt_of_lt_of_le (hfootTree0 a ha).2 hendLeEr)).symm)).1 hrepTree0
  have hsTreeEq : sTree = lctInit pathPayload G.n none := hinitTreePost
  have hinv0 : InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
      slots names slotThresholds m thPtr ∅ sTree xTree (fun _ => 0) (fun _ => 0) afterThresh s3.mem := by
    rw [hsTreeEq]
    exact initPathTreeInv_empty hB (hsTreeEq ▸ hs3_treeRep)
      (fun a ha => lt_of_lt_of_le (hfootTree0 a ha).2 (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans herLeTh hthLeA))))
      (fun e he => (hkeep_tree_er (slots + e) (le_trans hthLeSl (Nat.le_add_right _ _))
        (lt_of_lt_of_le (Nat.add_lt_add_left he treeEnd) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))).trans
        (hz (slots + e) (Nat.le_add_right _ _)))
      (fun k hk => (hkeep_tree_er (names + k) (le_trans hthLeSl (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
        (lt_of_lt_of_le (Nat.add_lt_add_left hk (treeEnd + m)) (Nat.le_add_right _ _))).trans
        (hz (names + k) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
  have hs3_lvlEq (i : ℕ) (hi : i ≤ C.d) : s3.mem (levelTable + i) = st.mem (levelTable + i) :=
    hkeep_lt_et (levelTable + i) (lt_of_lt_of_le (pt_lvl_lt_br handle C.d i hi).1 (le_trans hlevGe hlvLeEt))
      (pt_lvl_lt_br handle C.d i hi).2.1 (pt_lvl_lt_br handle C.d i hi).2.2
  have hs3_brEq (i : ℕ) (hi : i ≤ C.d) : s3.mem (branchTable + i) = st.mem (branchTable + i) :=
    hkeep_lt_et (branchTable + i) (lt_of_lt_of_le (pt_br_lt_br handle C.d i hi).1 (le_trans hlevGe hlvLeEt))
      (pt_br_lt_br handle C.d i hi).2.1 (pt_br_lt_br handle C.d i hi).2.2
  have hcores3 : InitChainCoresAt Rcore Rterm Rtree chain treeHeap levelTable branchTable
      rootGraph edgeRecords edgeThresholds slots names slotThresholds m L afterThresh G recPtr extraStatic
      xCore xTerm xTree s3.mem := by
    refine ⟨fun i hi => ?_, (hs3_brEq C.d le_rfl).trans hlastBr0, ?_, ?_⟩
    · obtain ⟨hbrI, hrepI, hfootI⟩ := hcores0 i hi
      rw [hs3_lvlEq i hi.le]
      refine ⟨(hs3_brEq i hi.le).trans hbrI, ?_, fun a ha => ?_⟩
      · refine ((hcoreImpl i hi G.n G.m).1 _ _ _ st.mem s3.mem (fun a ha => ?_)).1 hrepI
        have hf := hfootI a ha
        exact (hkeep_lt_et a (lt_of_lt_of_le hf.2.1 hlvLeEt)
          (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 1 (by decide)) hf.1))
          (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 3 (by decide)) hf.1))).symm
      · have hf := hfootI a ha
        have hltT : a < treeHeap := lt_of_lt_of_le hf.2.1 (le_trans hlvLeEt (htreeEq ▸ Nat.le_add_right edgeThresholds m))
        have hb := hbelow_lt a hltT
        exact ⟨hb.1, hb.2.1, hnotStaticOfCore a hf.1 hf.2.1, hb.2.2,
          fun j hj hne => by rw [hs3_lvlEq j hj.le]; exact hf.2.2.1 j hj hne,
          by rw [hs3_lvlEq C.d le_rfl]; exact hf.2.2.2⟩
    · rw [hs3_lvlEq C.d le_rfl]
      refine (htermImpl.1 _ _ _ st.mem s3.mem (fun a ha => ?_)).1 hrepTerm0
      have hf := hfootTerm0 a ha
      exact (hkeep_lt_et a (lt_of_lt_of_le hf.2.1 hlvLeEt)
        (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 1 (by decide)) hf.1))
        (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 3 (by decide)) hf.1))).symm
    · intro a ha
      rw [hs3_lvlEq C.d le_rfl] at ha
      have hf := hfootTerm0 a ha
      have hb := hbelow_lt a (lt_of_lt_of_le hf.2.1 (le_trans hlvLeEt (htreeEq ▸ Nat.le_add_right edgeThresholds m)))
      exact ⟨hb.1, hb.2.1, hnotStaticOfCore a hf.1 hf.2.1, hb.2.2,
        fun j hj => by rw [hs3_lvlEq j hj.le]; exact hf.2.2 j hj⟩
  have hs3_G : DynGraphAt s3.mem rootGraph G.n G.m G :=
    DynGraphAt.of_agree hG (fun a hlo hhi =>
      hkeep_lt_et a (lt_of_lt_of_le hhi (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans htbLeBr (le_trans hlevGe hlvLeEt)))))
        (Nat.ne_of_lt (lt_of_lt_of_le hhi (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans hhandleEq.symm.le (Nat.le_add_right _ _))))))
        (Nat.ne_of_lt (lt_of_lt_of_le hhi (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans hhandleEq.symm.le (Nat.le_add_right _ _)))))))
  obtain ⟨s4, finalHeap, c4, sFin, yTree, slotFin, nameFin, yCore, yTerm, hr4,
      hs4_3, hinvFin, htreeNotEx, hcoresFin, htermFin, htermFootFin, hstatFin, hs4_z, hs4_ge,
      hs4_le, htreeDisj4, hcoresAt4⟩ :=
    initLinkChainForests_runs (w := w) (p := p) (ω := ω) (st := s3) (extraStatic := extraStatic)
      hH hcoreImpl htermImpl htreeImpl hbind hcoreInput hs3_G hGm hinv0 hcores3
      (fun _ _ => rfl) hvalB (by rwa [hfmt4])
      hs3_0 hs3_3 (hGm.symm ▸ hs3_9) (hGm.symm ▸ hs3_10) hs3_11
      hs3_19 hs3_20 hs3_22 hs3_23 hs3_24 hs3_29 hs3_30 hs3_31 hs3_34
      (fun e he => (hs3_edges e (hGm ▸ hG.2.2.1 e (hTSub he))).2.1)
      (fun e he => by rw [hfmt4]; exact (hs3_edges e (hGm ▸ hG.2.2.1 e (hTSub he))).2.2.2)
      (fun e he => (hs3_edges e (hGm ▸ hG.2.2.1 e (hTSub he))).1)
      (fun e he => lt_of_le_of_lt (le_trans (pt_th_rec_bounds threshHeap L e 0 0).2.2.1
        (hrecEnd e (hGm ▸ hG.2.2.1 e (hTSub he)))) (lt_of_le_of_lt (Nat.le_add_right _ _) hafterRoom))
      hstaticBelow hslA hnmA hstA (Or.inl hslNm) (Or.inl hslSt) (Or.inl hnmSt)
      (fun a ha => by
        have hlt := lt_of_lt_of_le (hfootTree0 a ha).2 le_rfl
        exact ⟨Or.inl hlt, Or.inl (lt_of_lt_of_le hlt (Nat.le_add_right _ _)),
          Or.inl (lt_of_lt_of_le hlt (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))⟩)
      (fun i hi => by rw [hs3_lvlEq i hi, hs3_brEq i hi]; exact hhandlesW i hi)
      hvw (by rwa [hfmt4]) hthW hdW hw7 hs3_z
      (fun i hi mem' cur ret fv fe yc hlo hle hlsf => by
        rw [hs3_lvlEq i hi.le]; exact hreadoutBounds i hi mem' cur ret fv fe yc hlo hle hlsf)
      (fun i hi mem' cur ret gv ge yc hlo hle hdg => by
        rw [hs3_lvlEq i hi.le]; exact hgraphReadBounds i hi mem' cur ret gv ge yc hlo hle hdg)
      (fun mem' cur ret fv fe yt hlo hle hlsf => by
        rw [hs3_lvlEq C.d le_rfl]; exact hlastReadBounds mem' cur ret fv fe yt hlo hle hlsf)
      hlevelCap hlastCap hlinkAlloc hafterRoom
  have hs4_extra (a : ℕ) (ha : extraStatic a) : s4.mem a = s3.mem a :=
    hstatFin a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))))
  -- Stage 5
  have hs4_alpha : s4.mem (handle + 14) = root + 16 :=
    (hs4_extra (handle + 14) (Or.inl (pt_add_lt_br handle C.d 14 (by decide)))).trans
      ((hkeep_lt_et (handle + 14)
        (lt_of_lt_of_le (pt_add_lt_br handle C.d 14 (by decide)) (le_trans hlevGe hlvLeEt))
        (pt_add_ne_add handle 14 1 (by decide)) (pt_add_ne_add handle 14 3 (by decide))).trans halphaCell)
  obtain ⟨out, c5, hr5, hout99, hrootDir, hframe5⟩ :=
    initPostTailStoreRootDir_runs (w := w) (p := p) (ω := ω) (st := s4)
      hs4_3
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_69)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_74)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_75)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_81)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_82)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_83)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_84)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_85)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_86)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_87)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_88)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_89)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_90)
      ((initLinkChainForests_preserves_regs (by decide) hr4).trans hs3_91)
      hhandleEq hfreshEq hs4_alpha hroot16W hh14W hfcW hw16
  have hout_ge16 (a : ℕ) (ha : root + 16 ≤ a) : out.mem a = s4.mem a := hframe5 a (Or.inr ha)
  have hroot_le_handle : root + 16 ≤ handle := le_trans hrootTb (le_trans (Nat.le_add_right _ _) hhandleEq.symm.le)
  have hroot_le_lv : root + 16 ≤ levelsEnd := le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hlevGe)))
  have hroot_le_end : root + 16 ≤ treeEnd := le_trans hroot_le_lv (le_trans hlvLeEt (le_trans (Nat.le_add_right _ _) hetLeEnd))
  have hh1_lt_lv : handle + 1 < levelsEnd := lt_of_lt_of_le (pt_add_lt_br handle C.d 1 (by decide)) hlevGe
  have hh3_lt_lv : handle + 3 < levelsEnd := lt_of_lt_of_le (pt_add_lt_br handle C.d 3 (by decide)) hlevGe
  have hout_low (a : ℕ) (h1 : root + 16 ≤ a) (h2 : a < branchTable + (C.d + 1))
      (hh1 : a ≠ handle + 1) (hh3 : a ≠ handle + 3) : out.mem a = st.mem a :=
    (hout_ge16 a h1).trans ((hs4_extra a (Or.inl h2)).trans
      (hkeep_lt_et a (lt_of_lt_of_le h2 (le_trans hlevGe hlvLeEt)) hh1 hh3))
  have hout_mid (a : ℕ) (h1 : levelsEnd ≤ a) (h2 : a < edgeThresholds) : out.mem a = st.mem a :=
    (hout_ge16 a (le_trans hroot_le_lv h1)).trans ((hs4_extra a (Or.inr (Or.inl ⟨h1, lt_of_lt_of_le h2 (htreeEq ▸ Nat.le_add_right _ _)⟩))).trans
      (hkeep_lt_et a h2 (Nat.ne_of_gt (lt_of_lt_of_le hh1_lt_lv h1)) (Nat.ne_of_gt (lt_of_lt_of_le hh3_lt_lv h1))))
  have hout_ge16_of_notEx (a : ℕ) (hne : ¬ extraStatic a) : root + 16 ≤ a := by
    by_contra hlt
    exact hne (Or.inl (lt_of_lt_of_le (Nat.lt_of_not_ge hlt) (le_trans hrootTb (le_trans (Nat.le_add_right _ _) htbLeBr))))
  have hrTotal : Runs w p ω
      (solverInitPostTailBody shift divide negate copy (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
      st .normal out (c123 + (c4 + c5 + 1) + 1) := by
    unfold solverInitPostTailBody
    rcases runs_seq_iff.mp hr123 with ⟨_, _, _, hbad, _⟩ | ⟨m1, cm1, cm23, hm1, hm23, hc1⟩; · cases hbad
    rcases runs_seq_iff.mp hm23 with ⟨_, _, _, hbad, _⟩ | ⟨m2, cm2, cm3, hm2, hm3, hc2⟩; · cases hbad
    have h45 := runs_seq_iff.mpr (Or.inr ⟨s4, c4, c5, hr4, hr5, rfl⟩)
    have h345 := runs_seq_iff.mpr (Or.inr ⟨s3, cm3, c4 + c5 + 1, hm3, h45, rfl⟩)
    have h2345 := runs_seq_iff.mpr (Or.inr ⟨m2, cm2, cm3 + (c4 + c5 + 1) + 1, hm2, h345, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨m1, cm1, cm2 + (cm3 + (c4 + c5 + 1) + 1) + 1, hm1, h2345, by rw [hc1, hc2]; ring⟩)
  refine ⟨out, finalHeap, _, sFin, yTree, slotFin, nameFin, yCore, yTerm,
    hrTotal, hout99, hrootDir, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hs4_ge, hs4_le, htreeDisj4, ?_⟩
  · intro j hj
    have hj' : j < 8 := hj
    have hge := le_trans hroot_le_handle (Nat.le_add_right handle j)
    have hlt : handle + j < branchTable + (C.d + 1) := pt_add_lt_br handle C.d j (lt_trans hj' (by decide))
    interval_cases j
    · exact (hout_low (handle + 0) hge hlt (pt_add_ne_add handle 0 1 (by decide)) (pt_add_ne_add handle 0 3 (by decide))).trans (hdetect0 0 (by simp))
    · exact (hout_ge16 (handle + 1) hge).trans ((hs4_extra (handle + 1) (Or.inl hlt)).trans hs3_h1)
    · exact (hout_low (handle + 2) hge hlt (pt_add_ne_add handle 2 1 (by decide)) (pt_add_ne_add handle 2 3 (by decide))).trans (hdetect0 2 (by simp))
    · exact (hout_ge16 (handle + 3) hge).trans ((hs4_extra (handle + 3) (Or.inl hlt)).trans hs3_h3)
    · exact (hout_low (handle + 4) hge hlt (pt_add_ne_add handle 4 1 (by decide)) (pt_add_ne_add handle 4 3 (by decide))).trans (hdetect0 4 (by simp))
    · exact (hout_low (handle + 5) hge hlt (pt_add_ne_add handle 5 1 (by decide)) (pt_add_ne_add handle 5 3 (by decide))).trans (hdetect0 5 (by simp))
    · exact (hout_low (handle + 6) hge hlt (pt_add_ne_add handle 6 1 (by decide)) (pt_add_ne_add handle 6 3 (by decide))).trans (hdetect0 6 (by simp))
    · exact (hout_low (handle + 7) hge hlt (pt_add_ne_add handle 7 1 (by decide)) (pt_add_ne_add handle 7 3 (by decide))).trans (hdetect0 7 (by simp))
  · intro j hj; have hj' : j < 4 := hj
    exact (hout_low (handle + 5 + j) (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
      (Nat.add_assoc handle 5 j ▸ pt_add_lt_br handle C.d (5 + j) (Nat.add_lt_add_left hj' 5 |>.trans (by decide)))
      (pt_add_add_ne handle 5 j 1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 5 j))))
      (pt_add_add_ne handle 5 j 3 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 5 j))))).trans (hnum0 j hj)
  · intro j hj; have hj' : j < 8 := hj
    exact (hout_low (handle + 9 + j) (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
      (Nat.add_assoc handle 9 j ▸ pt_add_lt_br handle C.d (9 + j) (Nat.add_lt_add_left hj' 9))
      (pt_add_add_ne handle 9 j 1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 9 j))))
      (pt_add_add_ne handle 9 j 3 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 9 j))))).trans (hchain0 j hj)
  · refine ⟨(hout_mid freshCounter (pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m 0 C.d hfreshEq hfwdEq hinvEq hthEq).1.1
        (pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m 0 C.d hfreshEq hfwdEq hinvEq hthEq).1.2).trans hfresh0.1,
      fun e he => (hout_mid (forward + e) ((pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m e C.d hfreshEq hfwdEq hinvEq hthEq).2.1 he).1
        ((pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m e C.d hfreshEq hfwdEq hinvEq hthEq).2.1 he).2).trans (hfresh0.2.1 e he),
      fun e he => (hout_mid (inverse + e) ((pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m e C.d hfreshEq hfwdEq hinvEq hthEq).2.2.1 he).1
        ((pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m e C.d hfreshEq hfwdEq hinvEq hthEq).2.2.1 he).2).trans (hfresh0.2.2 e he)⟩
  · intro a hlo hhi
    exact (hout_mid a hlo (lt_of_lt_of_le hhi (pt_fresh_range levelsEnd freshCounter forward inverse edgeThresholds m 0 C.d hfreshEq hfwdEq hinvEq hthEq).2.2.2)).trans (hsched0 a hlo hhi)
  · intro e he
    obtain ⟨hge1, hlt1⟩ := pt_inOff_range treeEnd m G.n e he
    exact (hout_ge16 (inOffReady + e) (le_trans hroot_le_end (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) hge1)))).trans
      ((hs4_extra (inOffReady + e) (Or.inr (Or.inr ⟨hge1, lt_of_lt_of_le hlt1 hthLeA⟩))).trans
        ((hs3_keep (inOffReady + e) hlt1 (Or.inr (le_trans hetLeEnd (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) hge1))))
          (Or.inr hge1) (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 1 (by decide)) (le_trans hbrLeTh (le_trans hthLeSl (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) hge1))))))
          (Nat.ne_of_gt (lt_of_lt_of_le (pt_add_lt_br handle C.d 3 (by decide)) (le_trans hbrLeTh (le_trans hthLeSl (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) hge1))))))).trans
          (hz (inOffReady + e) (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) hge1)))))
  · intro e he
    obtain ⟨he1, he2, he3, he4⟩ := hs3_edges e he
    have hre := hrecEnd e he
    have hloTh : edgeRecords + m ≤ thPtr e := le_trans herLeTh (pt_th_rec_bounds threshHeap L e 0 0).1
    have hloRec : edgeRecords + m ≤ recPtr e := le_trans herLeTh (pt_th_rec_bounds threshHeap L e 0 0).2.1
    refine ⟨(hout_ge16 (edgeThresholds + e) (le_trans hroot_le_lv (le_trans hlvLeEt (Nat.le_add_right _ _)))).trans
        ((hs4_extra (edgeThresholds + e) (Or.inr (Or.inl ⟨le_trans hlvLeEt (Nat.le_add_right _ _), htreeEq ▸ Nat.add_lt_add_left he _⟩))).trans he1),
      (hout_ge16 (edgeRecords + e) (le_trans hroot_le_end (le_trans hendLeEr (Nat.le_add_right _ _)))).trans
        ((hstatFin (edgeRecords + e) (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left he _⟩))))).trans he2),
      he3.congr (fun j hj => (hout_ge16 (thPtr e + j) (le_trans hroot_le_end (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans hloTh (Nat.le_add_right _ _)))))).trans
        (hs4_extra (thPtr e + j) (Or.inr (Or.inr ⟨le_trans hloTh (Nat.le_add_right _ _), lt_of_lt_of_le ((pt_th_rec_bounds threshHeap L e j 0).2.2.2.1 hj) hre⟩)))),
      he4.congr (fun a hloA hhiA => (hout_ge16 a (le_trans hroot_le_end (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans hloRec hloA))))).trans
        (hs4_extra a (Or.inr (Or.inr ⟨le_trans hloRec hloA, lt_of_lt_of_le (Nat.add_assoc (recPtr e) 2 (4 * L) ▸ hhiA) hre⟩))))⟩
  · obtain ⟨hsnF, hsubF, hrepF, hfootF, hslotF, hinvF, hstF, hoffF⟩ := hinvFin
    exact ⟨hsnF, hsubF,
      (htreeImpl.1 treeHeap sFin yTree s4.mem out.mem (fun a ha =>
        (hout_ge16 a (hout_ge16_of_notEx a (htreeNotEx a ha))).symm)).1 hrepF,
      hfootF,
      ⟨fun e he => (hout_ge16 (slots + e) (le_trans hroot_le_end (Nat.le_add_right _ _))).trans (hslotF.1 e he),
       fun k hk => (hout_ge16 (names + k) (le_trans hroot_le_end (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))).trans (hslotF.2 k hk)⟩,
      hinvF,
      fun e he => (hout_ge16 (slotThresholds + slotFin e) (le_trans hroot_le_end (le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)))).trans (hstF e he),
      hoffF⟩
  · intro i hi
    obtain ⟨hrepI, hfootI⟩ := hcoresFin i hi
    rw [hs3_lvlEq i hi.le] at hrepI hfootI
    exact ⟨((hcoreImpl i hi G.n G.m).1 _ _ _ s4.mem out.mem (fun a ha =>
      (hout_ge16 a (hout_ge16_of_notEx a (hfootI a ha).2)).symm)).1 hrepI,
      fun a ha => (hfootI a ha).1⟩
  · rw [hs3_lvlEq C.d le_rfl] at htermFin htermFootFin
    exact (htermImpl.1 _ _ _ s4.mem out.mem (fun a ha =>
      (hout_ge16 a (hout_ge16_of_notEx a (htermFootFin a ha).2)).symm)).1 htermFin
  · rw [hs3_lvlEq C.d le_rfl] at htermFootFin
    exact fun a ha => (htermFootFin a ha).1
  · intro j hj
    obtain ⟨ht1, ht2, ht3⟩ := pt_table_lt_handle table C.d handle j hhandleEq hj
    exact hout_low (table + j) (le_trans hrootTb (Nat.le_add_right _ _))
      (lt_of_lt_of_le ht1 htbLeBr) ht2 ht3
  · intro i hi
    obtain ⟨hl1, hl2, hl3⟩ := pt_lvl_lt_br handle C.d i hi
    obtain ⟨hb1, hb2, hb3⟩ := pt_br_lt_br handle C.d i hi
    exact ⟨hout_low (handle + 17 + i) (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))) hl1 hl2 hl3,
      hout_low (handle + 17 + (C.d + 1) + i) (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))) hb1 hb2 hb3⟩
  · intro a ha
    have hltBr : a < branchTable + (C.d + 1) :=
      lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) (le_trans hrootTb (le_trans (Nat.le_add_right _ _) htbLeBr)))
    exact (hframe5 a (Or.inl ha)).trans ((hs4_extra a (Or.inl hltBr)).trans
      (hkeep_lt_et a (lt_of_lt_of_le hltBr (le_trans hlevGe hlvLeEt))
        (Nat.ne_of_lt (lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) (le_trans hroot_le_handle (Nat.le_add_right _ _)))))
        (Nat.ne_of_lt (lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) (le_trans hroot_le_handle (Nat.le_add_right _ _)))))))
  · intro a ha
    exact (hout_ge16 a (le_trans hroot_le_end (le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans herLeTh (le_trans hthLeA (le_trans hs4_ge ha))))))).trans (hs4_z a ha)
  · exact le_trans hendLeEr (le_trans (Nat.le_add_right _ _) (le_trans herLeTh (le_trans hthLeA hs4_ge)))
  · exact DynGraphAt.of_agree (hGm ▸ hG) (fun a hlo hhi =>
      (hout_ge16 a (le_trans hrootLe hlo)).trans
        ((hstatFin a (Or.inl ⟨hlo, hGm.symm ▸ hhi⟩)).trans
          (hkeep_lt_et a (lt_of_lt_of_le (hGm.symm ▸ hhi) (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans htbLeBr (le_trans hlevGe hlvLeEt)))))
            (Nat.ne_of_lt (lt_of_lt_of_le (hGm.symm ▸ hhi) (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans hhandleEq.symm.le (Nat.le_add_right _ _))))))
            (Nat.ne_of_lt (lt_of_lt_of_le (hGm.symm ▸ hhi) (le_trans hrootGEnd (le_trans (Nat.le_add_right _ _) (le_trans hhandleEq.symm.le (Nat.le_add_right _ _)))))))))
  · have hlvOut (i : ℕ) (hi : i ≤ C.d) : out.mem (levelTable + i) = s4.mem (levelTable + i) :=
      hout_ge16 _ (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    have hbrOut (i : ℕ) (hi : i ≤ C.d) : out.mem (branchTable + i) = s4.mem (branchTable + i) :=
      hout_ge16 _ (le_trans hroot_le_handle (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
    refine ⟨fun i hi => ?_, (hbrOut C.d le_rfl).trans hcoresAt4.2.1, ?_, ?_⟩
    · obtain ⟨hbrI, hrepI, hfootI⟩ := hcoresAt4.1 i hi
      rw [hlvOut i hi.le, hbrOut i hi.le]
      refine ⟨hbrI, ((hcoreImpl i hi G.n G.m).1 _ _ _ s4.mem out.mem (fun a ha =>
        (hout_ge16 a (hout_ge16_of_notEx a (fun hex => (hfootI a ha).2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex))))))))).symm)).1 hrepI,
        fun a ha => ?_⟩
      have hf := hfootI a ha
      exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
        fun j hj hne => by rw [hlvOut j hj.le]; exact hf.2.2.2.2.1 j hj hne,
        by rw [hlvOut C.d le_rfl]; exact hf.2.2.2.2.2⟩
    · rw [hlvOut C.d le_rfl]
      exact (htermImpl.1 _ _ _ s4.mem out.mem (fun a ha =>
        (hout_ge16 a (hout_ge16_of_notEx a (fun hex => (hcoresAt4.2.2.2 a ha).2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex))))))))).symm)).1 hcoresAt4.2.2.1
    · intro a ha
      rw [hlvOut C.d le_rfl] at ha
      have hf := hcoresAt4.2.2.2 a ha
      exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun j hj => by rw [hlvOut j hj.le]; exact hf.2.2.2.2 j hj⟩

end MinCostFlow.MinRatio
