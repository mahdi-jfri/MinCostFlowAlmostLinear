module

public import MinCostFlow.MinRatio.WireInitLinkK
public import MinCostFlow.MinRatio.InitConcretePostTail

/-!
# Post-tail Stages 1–4 (`WireInitPostTailBaseK`)

Defines the post-tail space and fixed-cost budgets (`initPostTailSpace`, `initPostTailCost`),
precomputes pure-`Nat` layout bounds (`PostTailArithK`, `PTLayout`), and proves Stages 1–3
(`initPostTailStages123K_runs`) and Stage 4 (`initPostTailStage4K_runs`, linking the chain
forests into the Section 6 path tree).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

/-- Total heap space allocated above `treeEnd` by `solverInitPostTailBody`. -/
@[expose] def initPostTailSpace (m n L d linkSpace : ℕ) : ℕ :=
  m + 2 * n + 2 * n + m + m + m + 3 * L + m * initEdgeRecordSpace L +
    initLinkChainSpace d m linkSpace

/-- Fixed step cost bound of `solverInitPostTailBody` (excluding incoming potentials). -/
@[expose] def initPostTailCost (m n L d treeConst readout : ℕ) : ℕ :=
  m * (2700 * L ^ 2 + 2920 * L + 869) + 71 * L +
    initLinkChainCost d m treeConst L n readout + 520

private theorem initPostTailSetup_straight : IsStraightLine initPostTailSetup := by
  simp [initPostTailSetup, IsStraightLine]

private theorem initPostTailLinkArgs_straight : IsStraightLine (initPostTailLinkArgsAt 18) := by
  simp [initPostTailLinkArgsAt, initPostTailLinkArgsGen, IsStraightLine]

private theorem initPostTailSetup_cost_le : straightLineCost initPostTailSetup ≤ 80 := by decide
private theorem initPostTailLinkArgs_cost_le : straightLineCost (initPostTailLinkArgsAt 18) ≤ 110 := by decide

/-- Precomputed pure-arithmetic layout inequalities for `initPostTailStages123K_runs`. -/
structure PostTailArithK (w root table handle levelsEnd rootGraph gradient lengths
    forward inverse edgeThresholds freshCounter treeHeap treeEnd m n ec0 L d linkSpace : ℕ) : Prop where
  root16_le_rootG : root + 16 ≤ rootGraph
  rootG_lt_table : rootGraph + dynGraphSize n ec0 ≤ table
  table_le_handle : table + (4 * d + 4) = handle
  handle_lt_lvl : handle + 18 + (d + 1) + (d + 1) ≤ levelsEnd
  levelsEnd_lt_fc : levelsEnd + (4 * (d + 1) + 1) = freshCounter
  fc_lt_fwd : freshCounter + 1 = forward
  fwd_le_inv : forward + m = inverse
  inv_le_th : inverse + m = edgeThresholds
  th_le_tree : edgeThresholds + m = treeHeap
  tree_le_end : treeHeap ≤ treeEnd
  len_le_root : lengths + m * L ≤ root
  grad_le_root : gradient + m * L ≤ root
  room : treeEnd + initPostTailSpace m n L d linkSpace < 2 ^ w
  hw17 : 17 < 2 ^ w

set_option maxHeartbeats 800000 in
/-- Stages 1–3 of `solverInitPostTailBody` with explicit step cost bound. -/
theorem initPostTailStages123K_runs
    {w shift divide negate copy root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n ec0 L P epsExp d linkSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (lenInt : ℕ → ℕ) (gradInt : ℕ → ℤ)
    (A : PostTailArithK w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m n ec0 L d linkSpace)
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
    (hecCell : st.mem (rootGraph + 1) = ec0)
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
        initPostTailLinkArgsAt 18) st .normal s3 cost ∧
      s3.regs 0 = treeHeap ∧ s3.regs 3 = afterThresh ∧
      s3.regs 9 = dgETailSlotBase rootGraph n ec0 ∧
      s3.regs 10 = dgEHeadSlotBase rootGraph n ec0 ∧
      s3.regs 11 = dgIntToExtBase rootGraph n ∧
      s3.regs 19 = slots ∧ s3.regs 20 = names ∧ s3.regs 22 = edgeRecords ∧
      s3.regs 23 = edgeThresholds ∧ s3.regs 24 = slotThresholds ∧
      s3.regs 29 = handle + 18 ∧ s3.regs 30 = handle + 18 + (d + 1) ∧
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
        s3.mem a = st.mem a) ∧
      cost ≤ m * (2700 * L ^ 2 + 2920 * L + 869) + 71 * L + 290 := by
  intro ε slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh thPtr recPtr val
  have hdgSz : dynGraphSize n ec0 = 4 + 7 * n + 9 * ec0 := rfl
  have hroomAll := A.room
  dsimp only [initPostTailSpace] at hroomAll
  have ha1 := A.root16_le_rootG; have ha2 := A.rootG_lt_table; have ha3 := A.table_le_handle
  have ha4 := A.handle_lt_lvl; have ha5 := A.levelsEnd_lt_fc; have ha6 := A.fc_lt_fwd
  have ha7 := A.fwd_le_inv; have ha8 := A.inv_le_th; have ha9 := A.th_le_tree
  have ha10 := A.tree_le_end; have ha11 := A.len_le_root; have ha12 := A.grad_le_root; have ha13 := A.hw17
  obtain ⟨s1, c1, hr1, hs1_92, hs1_87, hs1_88, hs1_89, hs1_86, hs1_90, hs1_91, hs1_99, hs1_73,
      hs1_regs, hs1_h1, hs1_h3, hs1_frame⟩ :=
    initPostTailSetup_runs (w := w) (p := p) (ω := ω) (st := st)
      h69 h74 h84 h99 hnCell hepsCell (by omega) (by omega) (by omega) (by omega)
  have hc1 : c1 ≤ 80 := (straightLine_cost_eq initPostTailSetup_straight hr1).symm ▸ initPostTailSetup_cost_le
  have hs1_r (r : ℕ) (hr : r ≤ 85) (h73 : r ≠ 73) : s1.regs r = st.regs r :=
    hs1_regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h73
  have hs1_lenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt s1.mem (lengths + e * L) 4 L (lenInt e) := by
    intro e he
    have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at hm
    exact ⟨(hlenAt e he).1, (hlenAt e he).2.congr (fun j hj => hs1_frame _ (by omega) (by omega))⟩
  have hs1_gradAt : ∀ e < m, PathIntAt s1.mem (gradient + e * L) 4 L (gradInt e) := by
    intro e he
    have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    rw [Nat.succ_mul] at hm
    exact (hgradAt e he).congr (fun j hj => hs1_frame _ (by omega) (by omega))
  have hs1_z : ZeroFrom s1.mem threshHeap := fun a ha =>
    (hs1_frame a (by omega) (by omega)).trans (hz a (by omega))
  obtain ⟨s2, c2, hr2, hs2_99, hs2_edges, hs2_z, hs2_frame, hs2_regs, hc2⟩ :=
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
      (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      hs1_lenAt hs1_gradAt hfits hs1_z (by omega) (by omega)
  have hs2_r (r : ℕ) (h8 : 8 ≤ r) (h95 : r ≠ 95) (h99 : r ≠ 99) : s2.regs r = s1.regs r :=
    hs2_regs r h8 h95 h99
  have hs2_ecCell : s2.mem (rootGraph + 1) = ec0 := by
    rw [hs2_frame (rootGraph + 1) (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      hs1_frame (rootGraph + 1) (by omega) (by omega)]
    exact hecCell
  obtain ⟨s3, c3, hr3, hs3_mem, hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20, hs3_22,
      hs3_23, hs3_24, hs3_29, hs3_30, hs3_31, hs3_34, hs3_hi⟩ :=
    initPostTailLinkArgsAt_runs (w := w) (hdr := 18) (p := p) (ω := ω) (st := s2)
      ((hs2_r 80 (by decide) (by decide) (by decide)).trans ((hs1_r 80 (by decide) (by decide)).trans h80))
      hs2_99
      ((hs2_r 69 (by decide) (by decide) (by decide)).trans ((hs1_r 69 (by decide) (by decide)).trans h69))
      ((hs2_r 92 (by decide) (by decide) (by decide)).trans hs1_92)
      hs2_ecCell
      ((hs2_r 87 (by decide) (by decide) (by decide)).trans hs1_87)
      ((hs2_r 88 (by decide) (by decide) (by decide)).trans hs1_88)
      ((hs2_r 86 (by decide) (by decide) (by decide)).trans hs1_86)
      ((hs2_r 83 (by decide) (by decide) (by decide)).trans ((hs1_r 83 (by decide) (by decide)).trans h83))
      ((hs2_r 89 (by decide) (by decide) (by decide)).trans hs1_89)
      ((hs2_r 74 (by decide) (by decide) (by decide)).trans ((hs1_r 74 (by decide) (by decide)).trans h74))
      ((hs2_r 75 (by decide) (by decide) (by decide)).trans ((hs1_r 75 (by decide) (by decide)).trans h75))
      (by omega) (by omega) ha13 (by omega)
  have hc3 : c3 ≤ 110 := (straightLine_cost_eq initPostTailLinkArgs_straight hr3).symm ▸ initPostTailLinkArgs_cost_le
  have hr123 : Runs w p ω (initPostTailSetup ;; initDetectThresholdsAndRecords shift divide negate copy ;;
      initPostTailLinkArgsAt 18) st .normal s3 (c1 + (c2 + c3 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2 + c3 + 1, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, c3, hr2, hr3, rfl⟩), rfl⟩)
  refine ⟨s3, _, hr123, hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20, hs3_22, hs3_23,
    hs3_24, hs3_29, hs3_30, hs3_31, hs3_34,
    (hs3_hi 69 (by decide)).trans ((hs2_r 69 (by decide) (by decide) (by decide)).trans ((hs1_r 69 (by decide) (by decide)).trans h69)),
    (hs3_hi 74 (by decide)).trans ((hs2_r 74 (by decide) (by decide) (by decide)).trans ((hs1_r 74 (by decide) (by decide)).trans h74)),
    (hs3_hi 75 (by decide)).trans ((hs2_r 75 (by decide) (by decide) (by decide)).trans ((hs1_r 75 (by decide) (by decide)).trans h75)),
    (hs3_hi 81 (by decide)).trans ((hs2_r 81 (by decide) (by decide) (by decide)).trans ((hs1_r 81 (by decide) (by decide)).trans h81)),
    (hs3_hi 82 (by decide)).trans ((hs2_r 82 (by decide) (by decide) (by decide)).trans ((hs1_r 82 (by decide) (by decide)).trans h82)),
    (hs3_hi 83 (by decide)).trans ((hs2_r 83 (by decide) (by decide) (by decide)).trans ((hs1_r 83 (by decide) (by decide)).trans h83)),
    (hs3_hi 84 (by decide)).trans ((hs2_r 84 (by decide) (by decide) (by decide)).trans ((hs1_r 84 (by decide) (by decide)).trans h84)),
    (hs3_hi 85 (by decide)).trans ((hs2_r 85 (by decide) (by decide) (by decide)).trans ((hs1_r 85 (by decide) (by decide)).trans h85)),
    (hs3_hi 86 (by decide)).trans ((hs2_r 86 (by decide) (by decide) (by decide)).trans hs1_86),
    (hs3_hi 87 (by decide)).trans ((hs2_r 87 (by decide) (by decide) (by decide)).trans hs1_87),
    (hs3_hi 88 (by decide)).trans ((hs2_r 88 (by decide) (by decide) (by decide)).trans hs1_88),
    (hs3_hi 89 (by decide)).trans ((hs2_r 89 (by decide) (by decide) (by decide)).trans hs1_89),
    (hs3_hi 90 (by decide)).trans ((hs2_r 90 (by decide) (by decide) (by decide)).trans hs1_90),
    (hs3_hi 91 (by decide)).trans ((hs2_r 91 (by decide) (by decide) (by decide)).trans hs1_91),
    by rw [hs3_mem, hs2_frame (handle + 1) (by omega) (Or.inl (by omega)) (Or.inl (by omega))]; exact hs1_h1,
    by rw [hs3_mem, hs2_frame (handle + 3) (by omega) (Or.inl (by omega)) (Or.inl (by omega))]; exact hs1_h3,
    by rw [hs3_mem]; exact hs2_edges,
    by rw [hs3_mem]; exact hs2_z,
    fun a ha hth hrec h1 h3 => by rw [hs3_mem, hs2_frame a ha hth hrec]; exact hs1_frame a h1 h3,
    by omega⟩

/-- Pure-`Nat` precomputed layout inequalities so Stage 4 and Stage 5 never invoke `omega`
while large representation hypotheses (`OrdInitChainCoresK`, `InitPathTreeInv`) are in scope. -/
structure PTLayout (w root table handle levelsEnd rootGraph
    forward inverse edgeThresholds freshCounter treeHeap treeEnd
    slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
    m n ec0 L d linkSpace : ℕ) : Prop where
  root16_le_rootG : root + 16 ≤ rootGraph
  root16_le_handle : root + 16 ≤ handle
  rootG_end_le_handle : rootGraph + dynGraphSize n ec0 ≤ handle
  rootG_end_le_lev : rootGraph + dynGraphSize n ec0 ≤ levelsEnd
  handle16_lt_lev : handle + 16 < levelsEnd
  handle17_le_lev : handle + 18 ≤ levelsEnd
  brEnd_le_lev : handle + 18 + (d + 1) + (d + 1) ≤ levelsEnd
  lev_le_fc : levelsEnd ≤ freshCounter
  fc_lt_fwd : freshCounter < forward
  fwd_le_inv : forward ≤ inverse
  fwdEnd_le_inv : forward + m ≤ inverse
  inv_le_th : inverse ≤ edgeThresholds
  invEnd_le_th : inverse + m ≤ edgeThresholds
  th_le_tree : edgeThresholds ≤ treeHeap
  thEnd_le_tree : edgeThresholds + m ≤ treeHeap
  tree_le_end : treeHeap ≤ treeEnd
  end_le_slots : treeEnd ≤ slots
  slotsEnd_le_names : slots + m ≤ names
  namesEnd_le_st : names + 2 * n ≤ slotThresholds
  stEnd_le_rec : slotThresholds + 2 * n ≤ edgeRecords
  recEnd_le_off : edgeRecords + m ≤ offReadyList
  offEnd_le_inOff : offReadyList + m ≤ inOffReady
  inOffEnd_le_thH : inOffReady + m ≤ threshHeap
  thH_le_after : threshHeap ≤ afterThresh
  after_lt_w : afterThresh < 2 ^ w
  treeHeap_lt_w : treeHeap < 2 ^ w
  hw7 : 7 < 2 ^ w
  hw16 : 16 < 2 ^ w
  handle14_lt_w : handle + 14 < 2 ^ w
  fc_lt_w : freshCounter < 2 ^ w
  root16_lt_w : root + 16 < 2 ^ w

theorem mkPTLayout
    {w root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
      m n ec0 L d linkSpace : ℕ}
    (h1 : root + 16 ≤ rootGraph) (h2 : rootGraph + dynGraphSize n ec0 ≤ table)
    (h3 : handle = table + (4 * d + 4)) (h4 : handle + 18 + (d + 1) + (d + 1) ≤ levelsEnd)
    (h5 : freshCounter = levelsEnd + (4 * (d + 1) + 1)) (h6 : forward = freshCounter + 1)
    (h7 : inverse = forward + m) (h8 : edgeThresholds = inverse + m)
    (h9 : treeHeap = edgeThresholds + m) (h10 : treeHeap ≤ treeEnd)
    (h11 : slots = treeEnd) (h12 : names = slots + m) (h13 : slotThresholds = names + 2 * n)
    (h14 : edgeRecords = slotThresholds + 2 * n) (h15 : offReadyList = edgeRecords + m)
    (h16 : inOffReady = offReadyList + m) (h17 : threshHeap = inOffReady + m)
    (h18 : threshHeap ≤ afterThresh)
    (hroom : afterThresh + initLinkChainSpace d m linkSpace < 2 ^ w) (hw17 : 17 < 2 ^ w) :
    PTLayout w root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
      m n ec0 L d linkSpace :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
   by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
   by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
   by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Stage 4 of `solverInitPostTailBody`: prepares `InitPathTreeInv`/`OrdInitChainCoresK` at `s3`
and runs `initLinkChainForestsK_runs`. -/
theorem initPostTailStage4K_runs
    {w bind initCore initTree
      root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
      m ec0 L P depth treeConst linkSpace capExp capLimit vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool}
    {C : ChainParams} {P_sc : SparseCoreOrdParams}
    {coreAlloc : ℕ → List ℕ → ℕ}
    {lvlM : ℕ → ℕ} {treeAlloc : ℕ → ℕ → List ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st s3 : State}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {B : ℤ} {thVal : ℕ → ℤ} {val : ℕ → PathEdgeValue}
    {thPtr recPtr : ℕ → ℕ}
    {xCore : ℕ → Rcore.τ} {xTerm : ℕ} {sTree : PathTreeState} {xTree : Rtree.τ}
    {metaStatic : ℕ → Prop}
    (PL : PTLayout w root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
      m G.n ec0 L C.d linkSpace)
    (hFour : fmt.limbBits = 4) (hPeq : fmt.precision = P)
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreImpl : ∀ i < C.d,
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0
          capExp P_sc coreAlloc) ∧
      SparseCoreReadoutFootAt fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0 capExp P_sc
        coreAlloc Rcore p opCore)
    (hLastReadout : p.procs[opLast 0]? = some LastLevelProgram.readoutBody)
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hcoreInput : ∀ i < C.d,
      SparseCoreOrdInput T C.k (lvlM i) N₀ (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i))
    (hthPtrBounds : ∀ e < m, threshHeap ≤ thPtr e ∧ thPtr e + L ≤ afterThresh)
    (hrecPtrBounds : ∀ e < m, threshHeap ≤ recPtr e ∧ recPtr e + (2 + 4 * L) ≤ afterThresh)
    (hroomLink : afterThresh + initLinkChainSpace C.d m linkSpace < 2 ^ w)
    (hG : DynGraphAt st.mem rootGraph G.n ec0 G) (hELt : ∀ e ∈ G.E, e < m) (hcap0 : G.n + ec0 + 2 ≤ capLimit)
    (hz0 : ZeroFrom st.mem treeEnd)
    (hrepTree0 : Rtree.rep treeHeap sTree xTree st.mem)
    (hinitTreePost : (pathTreeMachineContract fmt L treeConst treeAlloc).initPost
      [G.n, L, treeHeap] st.mem sTree st.mem)
    (hfootTree0 : ∀ a, Rtree.foot treeHeap xTree a → treeHeap ≤ a ∧ a < treeEnd)
    (hcores0 : ∀ i < C.d,
      st.mem (handle + 18 + (C.d + 1) + i) = chain.bran i ∧
      Rcore.rep (st.mem (handle + 18 + i)) (chainLevelOrdAbs chain i) (xCore i) st.mem ∧
      (∀ a, Rcore.foot (st.mem (handle + 18 + i)) (xCore i) a →
        handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
        (∀ j < C.d, j ≠ i → ¬ Rcore.foot (st.mem (handle + 18 + j)) (xCore j) a) ∧
        ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
            (st.mem (handle + 18 + C.d)) xTerm a))
    (hlastBr0 : st.mem (handle + 18 + (C.d + 1) + C.d) = chain.lastBran)
    (hrepTerm0 : (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).rep
      (st.mem (handle + 18 + C.d)) (chain.lastK, chain.lastLSFs) xTerm st.mem)
    (hfootTerm0 : ∀ a, (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
      (st.mem (handle + 18 + C.d)) xTerm a →
      handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ j < C.d, ¬ Rcore.foot (st.mem (handle + 18 + j)) (xCore j) a))
    (hhandlesW : ∀ i ≤ C.d, st.mem (handle + 18 + i) < 2 ^ w ∧
      st.mem (handle + 18 + (C.d + 1) + i) < 2 ^ w)
    (hs3_0 : s3.regs 0 = treeHeap) (hs3_3 : s3.regs 3 = afterThresh)
    (hs3_9 : s3.regs 9 = dgETailSlotBase rootGraph G.n ec0)
    (hs3_10 : s3.regs 10 = dgEHeadSlotBase rootGraph G.n ec0)
    (hs3_11 : s3.regs 11 = dgIntToExtBase rootGraph G.n)
    (hs3_19 : s3.regs 19 = slots) (hs3_20 : s3.regs 20 = names)
    (hs3_22 : s3.regs 22 = edgeRecords) (hs3_23 : s3.regs 23 = edgeThresholds)
    (hs3_24 : s3.regs 24 = slotThresholds)
    (hs3_29 : s3.regs 29 = handle + 18) (hs3_30 : s3.regs 30 = handle + 18 + (C.d + 1))
    (hs3_31 : s3.regs 31 = C.d) (hs3_34 : s3.regs 34 = rootGraph)
    (hs3_edges : ∀ e < m, s3.mem (edgeThresholds + e) = thPtr e ∧ s3.mem (edgeRecords + e) = recPtr e ∧
      PathIntAt s3.mem (thPtr e) 4 L (thVal e) ∧ PathEdgeAt s3.mem (recPtr e) 4 L (some (val e)))
    (hs3_z : ZeroFrom s3.mem afterThresh)
    (hs3_frame : ∀ a < threshHeap, (a < edgeThresholds ∨ edgeThresholds + m ≤ a) →
      (a < edgeRecords ∨ edgeRecords + m ≤ a) → a ≠ handle + 1 → a ≠ handle + 3 →
      s3.mem a = st.mem a)
    (hvalFwd : ∀ e ∈ chain.toTreeChain.chainTree.E, (val e).forward = true)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      |(val e).gradient| ≤ B ∧ |(val e).length| ≤ B ∧ |(val e).flow| ≤ B ∧ |(val e).detector| ≤ B)
    (hB : 0 ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity 4 L : ℤ))
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hdW : C.d < 2 ^ w)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      afterThresh ≤ cur → cur ≤ afterThresh + initLinkChainSpace C.d m linkSpace →
      treeAlloc 0 G.n [treeHeap, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hmetaStatic : ∀ a, metaStatic a →
      handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ i < C.d, ¬ Rcore.foot (st.mem (handle + 18 + i)) (xCore i) a) ∧
      ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
          (st.mem (handle + 18 + C.d)) xTerm a) :
    let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
      metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
    let Rterm := lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E
    ∃ s4 finalHeap c4 sFin yTree slotFin nameFin yCore yTerm,
      Runs w p ω (initLinkChainForests (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        s3 .normal s4 c4 ∧
      s4.regs 3 = finalHeap ∧
      (∀ r, 36 ≤ r → s4.regs r = s3.regs r) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap s4.mem ∧
      (∀ a, InitChainStaticAddr rootGraph (handle + 18) (handle + 18 + (C.d + 1)) edgeRecords edgeThresholds
        C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a → s4.mem a = s3.mem a) ∧
      ZeroFrom s4.mem finalHeap ∧ afterThresh ≤ finalHeap ∧
      finalHeap ≤ afterThresh + initLinkChainSpace C.d m linkSpace ∧
      (∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootGraph (handle + 18) (handle + 18 + (C.d + 1)) edgeRecords edgeThresholds
            C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
      OrdInitChainCoresK Rcore Rterm Rtree chain treeHeap (handle + 18) (handle + 18 + (C.d + 1))
        rootGraph edgeRecords edgeThresholds slots names slotThresholds m L finalHeap G recPtr extraStatic
        yCore yTerm yTree s4.mem ∧
      c4 + Rtree.phi treeHeap yTree s4.mem +
          (∑ i : Fin C.d, Rcore.phi (s4.mem (handle + 18 + i.val)) (yCore i.val) s4.mem) ≤
        initLinkChainCost C.d m treeConst L G.n P_sc.readout +
          Rtree.phi treeHeap xTree st.mem +
          (∑ i : Fin C.d, Rcore.phi (st.mem (handle + 18 + i.val)) (xCore i.val) st.mem) := by
  subst hPeq
  intro extraStatic Rterm
  let levelTable := handle + 18
  let branchTable := handle + 18 + (C.d + 1)
  let Ttree := chain.toTreeChain.chainTree
  have hTG : Ttree.E ⊆ G.E := by
    have hs := chain.toTreeChain.chainTree_isSubgraph hH (chain.toTreeChain.forestsAreSubgraphs_of_holds hH)
    rw [hH.1] at hs; exact hs.2.1
  have hlev_le_th : levelsEnd ≤ edgeThresholds :=
    PL.lev_le_fc.trans ((Nat.le_of_lt PL.fc_lt_fwd).trans (PL.fwd_le_inv.trans PL.inv_le_th))
  have hth_le_end : edgeThresholds ≤ treeEnd := PL.th_le_tree.trans PL.tree_le_end
  have hend_le_rec : treeEnd ≤ edgeRecords :=
    PL.end_le_slots.trans ((Nat.le_add_right slots m).trans (PL.slotsEnd_le_names.trans
      ((Nat.le_add_right names (2 * G.n)).trans (PL.namesEnd_le_st.trans
        ((Nat.le_add_right slotThresholds (2 * G.n)).trans PL.stEnd_le_rec)))))
  have hrec_le_thH : edgeRecords ≤ threshHeap :=
    (Nat.le_add_right edgeRecords m).trans (PL.recEnd_le_off.trans
      ((Nat.le_add_right offReadyList m).trans (PL.offEnd_le_inOff.trans
        ((Nat.le_add_right inOffReady m).trans PL.inOffEnd_le_thH))))
  have hrecEnd_le_thH : edgeRecords + m ≤ threshHeap :=
    PL.recEnd_le_off.trans ((Nat.le_add_right offReadyList m).trans (PL.offEnd_le_inOff.trans
      ((Nat.le_add_right inOffReady m).trans PL.inOffEnd_le_thH)))
  have hlev_le_rec : levelsEnd ≤ edgeRecords := hlev_le_th.trans (hth_le_end.trans hend_le_rec)
  have hlev_le_thH : levelsEnd ≤ threshHeap := hlev_le_rec.trans hrec_le_thH
  have hend_le_thH : treeEnd ≤ threshHeap := hend_le_rec.trans hrec_le_thH
  have hend_le_after : treeEnd ≤ afterThresh := hend_le_thH.trans PL.thH_le_after
  have htree_le_after : treeHeap ≤ afterThresh := PL.tree_le_end.trans hend_le_after
  have hlev_le_tree : levelsEnd ≤ treeHeap := hlev_le_th.trans PL.th_le_tree
  have hframe3_below (a : ℕ) (ha : a < levelsEnd) (h1 : a ≠ handle + 1) (h3 : a ≠ handle + 3) :
      s3.mem a = st.mem a :=
    hs3_frame a (lt_of_lt_of_le ha hlev_le_thH) (Or.inl (lt_of_lt_of_le ha hlev_le_th))
      (Or.inl (lt_of_lt_of_le ha hlev_le_rec)) h1 h3
  have hframe3_tree (a : ℕ) (hlo : treeHeap ≤ a) (hhi : a < treeEnd) : s3.mem a = st.mem a :=
    hs3_frame a (lt_of_lt_of_le hhi hend_le_thH) (Or.inr (PL.thEnd_le_tree.trans hlo))
      (Or.inl (lt_of_lt_of_le hhi hend_le_rec))
      (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 16) handle)
        (le_of_lt PL.handle16_lt_lev)) (hlev_le_tree.trans hlo)))
      (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 3 < 16) handle)
        (le_of_lt PL.handle16_lt_lev)) (hlev_le_tree.trans hlo)))
  have hGmLeEc0 : G.m ≤ ec0 := by
    have hsub : G.E ⊆ Finset.range ec0 := fun e he => Finset.mem_range.mpr (hG.2.2.1 e he)
    simpa [MGraph.m] using Finset.card_le_card hsub
  have hdgLe : dynGraphSize G.n G.m ≤ dynGraphSize G.n ec0 := by unfold dynGraphSize; omega
  have hG3 : DynGraphAt s3.mem rootGraph G.n ec0 G :=
    dynGraphAt_of_agree hG (fun a _ hhi => by
      have hhi' : a < handle := lt_of_lt_of_le hhi PL.rootG_end_le_handle
      exact hframe3_below a (lt_of_lt_of_le hhi PL.rootG_end_le_lev)
        (ne_of_lt (lt_of_lt_of_le hhi' (Nat.le_add_right _ _)))
        (ne_of_lt (lt_of_lt_of_le hhi' (Nat.le_add_right _ _))))
  have hsTreeEq : sTree = lctInit pathPayload G.n none := hinitTreePost
  have htreeLoc3 := htreeImpl.1 treeHeap sTree xTree st.mem s3.mem (fun a ha =>
    (hframe3_tree a (hfootTree0 a ha).1 (hfootTree0 a ha).2).symm)
  have hne_of_end (a : ℕ) (hlo : treeEnd ≤ a) : a ≠ handle + 1 ∧ a ≠ handle + 3 :=
    ⟨ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 16) handle)
      (le_of_lt PL.handle16_lt_lev)) (hlev_le_tree.trans (PL.tree_le_end.trans hlo))),
     ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 3 < 16) handle)
      (le_of_lt PL.handle16_lt_lev)) (hlev_le_tree.trans (PL.tree_le_end.trans hlo)))⟩
  have hinv3 : InitPathTreeInv Rtree treeHeap G Ttree val B slots names slotThresholds m thPtr
      ∅ (lctInit pathPayload G.n none) xTree (fun _ => 0) (fun _ => 0) afterThresh s3.mem :=
    initPathTreeInv_empty hB (hsTreeEq ▸ htreeLoc3.1 hrepTree0)
      (fun a ha => lt_of_lt_of_le (hfootTree0 a ha).2 hend_le_after)
      (fun e he => by
        have hlo : treeEnd ≤ slots + e := PL.end_le_slots.trans (Nat.le_add_right _ _)
        have hhi : slots + e < edgeRecords :=
          lt_of_lt_of_le (Nat.add_lt_add_left he slots)
            (PL.slotsEnd_le_names.trans ((Nat.le_add_right _ _).trans
              (PL.namesEnd_le_st.trans ((Nat.le_add_right _ _).trans PL.stEnd_le_rec))))
        exact (hs3_frame _ (lt_of_lt_of_le hhi hrec_le_thH)
          (Or.inr (PL.thEnd_le_tree.trans (PL.tree_le_end.trans hlo))) (Or.inl hhi)
          (hne_of_end _ hlo).1 (hne_of_end _ hlo).2).trans (hz0 _ hlo))
      (fun k hk => by
        have hlo : treeEnd ≤ names + k :=
          PL.end_le_slots.trans ((Nat.le_add_right _ _).trans (PL.slotsEnd_le_names.trans (Nat.le_add_right _ _)))
        have hhi : names + k < edgeRecords :=
          lt_of_lt_of_le (Nat.add_lt_add_left hk names)
            (PL.namesEnd_le_st.trans ((Nat.le_add_right _ _).trans PL.stEnd_le_rec))
        exact (hs3_frame _ (lt_of_lt_of_le hhi hrec_le_thH)
          (Or.inr (PL.thEnd_le_tree.trans (PL.tree_le_end.trans hlo))) (Or.inl hhi)
          (hne_of_end _ hlo).1 (hne_of_end _ hlo).2).trans (hz0 _ hlo))
  have hnd (a : ℕ) (h : a < treeHeap ∨ edgeRecords ≤ a) :
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHeap xTree a := by
    rcases h with hlt | hge
    · have hltEnd : a < treeEnd := lt_of_lt_of_le hlt PL.tree_le_end
      have hltSl : a < slots := lt_of_lt_of_le hltEnd PL.end_le_slots
      have hltNm : a < names := lt_of_lt_of_le hltSl ((Nat.le_add_right _ _).trans PL.slotsEnd_le_names)
      have hltSt : a < slotThresholds := lt_of_lt_of_le hltNm ((Nat.le_add_right _ _).trans PL.namesEnd_le_st)
      exact ⟨⟨Or.inl hltSl, Or.inl hltNm, Or.inl hltSt⟩,
        fun hft => absurd (lt_of_le_of_lt (hfootTree0 a hft).1 hlt) (lt_irrefl _)⟩
    · have hgeSt : slotThresholds + 2 * G.n ≤ a := PL.stEnd_le_rec.trans hge
      have hgeNm : names + 2 * G.n ≤ a := PL.namesEnd_le_st.trans ((Nat.le_add_right _ _).trans hgeSt)
      have hgeSl : slots + m ≤ a := PL.slotsEnd_le_names.trans ((Nat.le_add_right _ _).trans hgeNm)
      exact ⟨⟨Or.inr hgeSl, Or.inr hgeNm, Or.inr hgeSt⟩,
        fun hft => absurd (lt_of_lt_of_le (hfootTree0 a hft).2 (hend_le_rec.trans hge)) (lt_irrefl _)⟩
  have hstatBelow3 : ∀ a, InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic a →
      a < afterThresh ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHeap xTree a := by
    intro a ha
    rcases ha with ⟨_, hhi⟩ | ⟨_, hhi⟩ | ⟨_, hhi⟩ | ⟨hlo, hhi⟩ | ⟨_, hhi⟩ | ⟨e, he, hlo, hhi⟩ | hex
    · have hlt : a < treeHeap :=
        lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hhi (Nat.add_le_add_left hdgLe rootGraph)) PL.rootG_end_le_lev) hlev_le_tree
      exact ⟨lt_of_lt_of_le hlt htree_le_after, hnd a (Or.inl hlt)⟩
    · have hlt : a < treeHeap := lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_of_le hhi) ((Nat.le_add_right _ _).trans PL.brEnd_le_lev)) hlev_le_tree
      exact ⟨lt_of_lt_of_le hlt htree_le_after, hnd a (Or.inl hlt)⟩
    · have hlt : a < treeHeap := lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_of_le hhi) PL.brEnd_le_lev) hlev_le_tree
      exact ⟨lt_of_lt_of_le hlt htree_le_after, hnd a (Or.inl hlt)⟩
    · exact ⟨lt_of_lt_of_le hhi (hrecEnd_le_thH.trans PL.thH_le_after), hnd a (Or.inr hlo)⟩
    · have hlt : a < treeHeap := lt_of_lt_of_le hhi PL.thEnd_le_tree
      exact ⟨lt_of_lt_of_le hlt htree_le_after, hnd a (Or.inl hlt)⟩
    · have hem : e < m := hELt e (hTG he)
      obtain ⟨hrLo, hrHi⟩ := hrecPtrBounds e hem
      exact ⟨lt_of_lt_of_le hhi hrHi, hnd a (Or.inr (hrec_le_thH.trans (hrLo.trans hlo)))⟩
    · rcases hex with hlt | hms | ⟨_, hhi⟩ | ⟨hlo, hhi⟩
      · have hlt' : a < treeHeap := lt_of_lt_of_le (lt_of_lt_of_le hlt PL.brEnd_le_lev) hlev_le_tree
        exact ⟨lt_of_lt_of_le hlt' htree_le_after, hnd a (Or.inl hlt')⟩
      · have hlt' : a < treeHeap := lt_of_lt_of_le (hmetaStatic a hms).2.1 hlev_le_tree
        exact ⟨lt_of_lt_of_le hlt' htree_le_after, hnd a (Or.inl hlt')⟩
      · exact ⟨lt_of_lt_of_le hhi htree_le_after, hnd a (Or.inl hhi)⟩
      · exact ⟨hhi, hnd a (Or.inr ((Nat.le_add_right _ _).trans hlo))⟩
  have hne_of_ge17 (a : ℕ) (hlo : handle + 18 ≤ a) : a ≠ handle + 1 ∧ a ≠ handle + 3 :=
    ⟨ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 18) handle) hlo),
     ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 3 < 18) handle) hlo)⟩
  have hCorePhi3 (i : ℕ) (hi : i < C.d) :
      s3.mem (levelTable + i) = st.mem (levelTable + i) ∧
      s3.mem (branchTable + i) = chain.bran i ∧
      Rcore.rep (s3.mem (levelTable + i)) (chainLevelOrdAbs chain i) (xCore i) s3.mem ∧
      Rcore.phi (s3.mem (levelTable + i)) (xCore i) s3.mem =
        Rcore.phi (st.mem (levelTable + i)) (xCore i) st.mem := by
    obtain ⟨hbr, hrep, hfoot⟩ := hcores0 i hi
    have hlvLt : levelTable + i < levelsEnd :=
      lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_lt hi) levelTable)
        ((Nat.le_add_right _ _).trans PL.brEnd_le_lev)
    have hbrLt : branchTable + i < levelsEnd :=
      lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_lt hi) branchTable) PL.brEnd_le_lev
    have hlv : s3.mem (levelTable + i) = st.mem (levelTable + i) :=
      hframe3_below _ hlvLt (hne_of_ge17 _ (Nat.le_add_right _ _)).1 (hne_of_ge17 _ (Nat.le_add_right _ _)).2
    have hbr' : s3.mem (branchTable + i) = chain.bran i :=
      (hframe3_below _ hbrLt
        (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).1
        (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).2).trans hbr
    have hloc := (hcoreImpl i hi).1.1 (st.mem (levelTable + i)) (chainLevelOrdAbs chain i)
      (xCore i) st.mem s3.mem (fun a ha => by
        have hlo : handle + 18 ≤ a :=
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (hfoot a ha).1
        exact (hframe3_below a (hfoot a ha).2.1 (hne_of_ge17 a hlo).1 (hne_of_ge17 a hlo).2).symm)
    exact ⟨hlv, hbr', by rw [hlv]; exact hloc.1 hrep, by rw [hlv]; exact hloc.2.symm⟩
  have hTermLoc3 := (lastLevelRepresentation_local vcLast ecLast 4 L fmt.precision (chain.G C.d).E)
    (st.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) xTerm st.mem s3.mem (fun a ha => by
      have hlo : handle + 18 ≤ a :=
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (hfootTerm0 a ha).1
      exact (hframe3_below a (hfootTerm0 a ha).2.1 (hne_of_ge17 a hlo).1 (hne_of_ge17 a hlo).2).symm)
  have hlvTermLt : levelTable + C.d < levelsEnd :=
    lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_self C.d) levelTable)
      ((Nat.le_add_right _ _).trans PL.brEnd_le_lev)
  have hbrTermLt : branchTable + C.d < levelsEnd :=
    lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_self C.d) branchTable) PL.brEnd_le_lev
  have hlvTerm3 : s3.mem (levelTable + C.d) = st.mem (levelTable + C.d) :=
    hframe3_below _ hlvTermLt (hne_of_ge17 _ (Nat.le_add_right _ _)).1 (hne_of_ge17 _ (Nat.le_add_right _ _)).2
  have hfootNotStatic (a : ℕ) (hlo : handle + 18 + (C.d + 1) + (C.d + 1) ≤ a) (hhi : a < levelsEnd)
      (hnMeta : ¬ metaStatic a) :
      a < afterThresh ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧
      ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic a ∧
      ¬ Rtree.foot treeHeap xTree a := by
    have hltTree : a < treeHeap := lt_of_lt_of_le hhi hlev_le_tree
    refine ⟨lt_of_lt_of_le hltTree htree_le_after, (hnd a (Or.inl hltTree)).1, fun hs => ?_, (hnd a (Or.inl hltTree)).2⟩
    rcases hs with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨e, he, h1, _⟩ | hex
    · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 (Nat.add_le_add_left hdgLe rootGraph)) (PL.rootG_end_le_handle.trans
        ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hlo))))) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le (Nat.lt_succ_of_le h1) ((Nat.le_add_right _ _).trans hlo)) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le (Nat.lt_succ_of_le h1) hlo) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le hhi (hlev_le_rec.trans h1)) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le hhi (hlev_le_th.trans h1)) (lt_irrefl _)
    · have hem : e < m := hELt e (hTG he)
      exact absurd (lt_of_lt_of_le hhi (hlev_le_thH.trans ((hrecPtrBounds e hem).1.trans h1))) (lt_irrefl _)
    · rcases hex with h1 | hms | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (lt_of_lt_of_le h1 hlo) (lt_irrefl _)
      · exact hnMeta hms
      · exact absurd (lt_of_lt_of_le hhi h1) (lt_irrefl _)
      · exact absurd (lt_of_lt_of_le hhi (hlev_le_rec.trans ((Nat.le_add_right _ _).trans h1))) (lt_irrefl _)
  have hcores3 : OrdInitChainCoresK Rcore Rterm Rtree chain treeHeap levelTable branchTable
      rootGraph edgeRecords edgeThresholds slots names slotThresholds m L afterThresh G recPtr
      extraStatic xCore xTerm xTree s3.mem := by
    refine ⟨fun i hi => ?_,
      (hframe3_below _ hbrTermLt
        (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).1
        (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).2).trans hlastBr0,
      by rw [hlvTerm3]; exact hTermLoc3.1 hrepTerm0, fun a ha => ?_⟩
    · obtain ⟨hlv, hbr, hrep, _⟩ := hCorePhi3 i hi
      refine ⟨hbr, hrep, fun a ha => ?_⟩
      rw [hlv] at ha
      obtain ⟨hlo, hhi, hdisjC, hdisjT⟩ := (hcores0 i hi).2.2 a ha
      obtain ⟨h1, h2, h3, h4⟩ := hfootNotStatic a hlo hhi (fun hms => (hmetaStatic a hms).2.2.1 i hi ha)
      exact ⟨h1, h2, h3, h4,
        fun j hj hne hfj => hdisjC j hj hne (by rwa [(hCorePhi3 j hj).1] at hfj),
        fun hft => hdisjT (by rwa [hlvTerm3] at hft)⟩
    · rw [hlvTerm3] at ha
      obtain ⟨hlo, hhi, hdisjC⟩ := hfootTerm0 a ha
      obtain ⟨h1, h2, h3, h4⟩ := hfootNotStatic a hlo hhi (fun hms => (hmetaStatic a hms).2.2.2 ha)
      exact ⟨h1, h2, h3, h4, fun j hj hfj => hdisjC j hj (by rwa [(hCorePhi3 j hj).1] at hfj)⟩
  obtain ⟨s4, finalHeap, c4, sFin, yTree, slotFin, nameFin, yCore, yTerm,
      hr4, hs4_3, hs4_regsHi, hinv4, hstat4, hz4, hafterLe, hfinHi, htreeOut4, hcores4, hc4⟩ :=
    initLinkChainForestsK_runs (w := w) (L := L) (treeConst := treeConst)
      (initCore := initCore) (initTree := initTree) (bind := bind)
      (treeHandle := treeHeap) (rootBase := rootGraph) (levelTable := levelTable)
      (branchTable := branchTable) (slots := slots) (names := names) (slotThresholds := slotThresholds)
      (edgeRecords := edgeRecords) (edgeThresholds := edgeThresholds) (m := m) (ec0 := ec0) (heap := afterThresh)
      (linkSpace := linkSpace) (capExp := capExp) (capLimit := capLimit)
      (vcLast := vcLast) (ecLast := ecLast)
      (fmt := fmt) (T := T) (C := C) (P := P_sc)
      (coreAlloc := coreAlloc)
      (lvlM := lvlM) (treeAlloc := treeAlloc) (N₀ := N₀)
      (Rcore := Rcore) (Rtree := Rtree) (opCore := opCore) (opLast := opLast) (opTree := opTree)
      (p := p) (ω := ω) (st := s3) (G := G) (len₀ := len₀) (chain := chain) (val := val)
      (B := B) (recPtr := recPtr) (thPtr := thPtr) (extraStatic := extraStatic)
      (xCore := xCore) (xTerm := xTerm) (s0 := lctInit pathPayload G.n none) (xTree := xTree)
      (slot0 := fun _ => 0) (name0 := fun _ => 0)
      hFour hH hcoreImpl hLastReadout htreeImpl hbind hcoreInput hG3 hELt
      (fun a _ hhi => Or.inl (lt_of_lt_of_le hhi (PL.rootG_end_le_handle.trans
        ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))))
      hcap0
      hinv3 hcores3 hvalFwd hvalB hcapB
      hs3_0 hs3_3 hs3_9 hs3_10 hs3_11 hs3_19 hs3_20 hs3_22 hs3_23 hs3_24
      hs3_29 hs3_30 hs3_31 hs3_34
      (fun e he => (hs3_edges e (hELt e (hTG he))).2.1)
      (fun e he => (hs3_edges e (hELt e (hTG he))).2.2.2)
      (fun e he => (hs3_edges e (hELt e (hTG he))).1)
      (fun e he => lt_of_le_of_lt ((Nat.le_add_right _ _).trans
        (hthPtrBounds e (hELt e (hTG he))).2) PL.after_lt_w)
      hstatBelow3
      (PL.slotsEnd_le_names.trans ((Nat.le_add_right _ _).trans (PL.namesEnd_le_st.trans
        ((Nat.le_add_right _ _).trans (PL.stEnd_le_rec.trans (hrec_le_thH.trans PL.thH_le_after))))))
      (PL.namesEnd_le_st.trans ((Nat.le_add_right _ _).trans
        (PL.stEnd_le_rec.trans (hrec_le_thH.trans PL.thH_le_after))))
      (PL.stEnd_le_rec.trans (hrec_le_thH.trans PL.thH_le_after))
      (Or.inl PL.slotsEnd_le_names)
      (Or.inl (PL.slotsEnd_le_names.trans ((Nat.le_add_right _ _).trans PL.namesEnd_le_st)))
      (Or.inl PL.namesEnd_le_st)
      (fun a ha =>
        have hltSl : a < slots := lt_of_lt_of_le (hfootTree0 a ha).2 PL.end_le_slots
        have hltNm : a < names := lt_of_lt_of_le hltSl ((Nat.le_add_right _ _).trans PL.slotsEnd_le_names)
        have hltSt : a < slotThresholds := lt_of_lt_of_le hltNm ((Nat.le_add_right _ _).trans PL.namesEnd_le_st)
        ⟨Or.inl hltSl, Or.inl hltNm, Or.inl hltSt⟩)
      (fun i hi => by
        have hlvLt : levelTable + i < levelsEnd :=
          lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hi) levelTable)
            ((Nat.le_add_right _ _).trans PL.brEnd_le_lev)
        have hbrLt : branchTable + i < levelsEnd :=
          lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hi) branchTable) PL.brEnd_le_lev
        exact ⟨by rw [hframe3_below _ hlvLt (hne_of_ge17 _ (Nat.le_add_right _ _)).1
              (hne_of_ge17 _ (Nat.le_add_right _ _)).2]; exact (hhandlesW i hi).1,
          by rw [hframe3_below _ hbrLt
              (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).1
              (hne_of_ge17 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).2]; exact (hhandlesW i hi).2⟩)
      hvw hwidth PL.treeHeap_lt_w hdW PL.hw7 hs3_z hlinkAlloc hroomLink
  have hSum3 :
      (∑ i : Fin C.d, Rcore.phi (s3.mem (levelTable + i.val)) (xCore i.val) s3.mem) =
      (∑ i : Fin C.d, Rcore.phi (st.mem (levelTable + i.val)) (xCore i.val) st.mem) :=
    Finset.sum_congr rfl fun i _ => (hCorePhi3 i.val i.isLt).2.2.2
  have hTreePhi3 : Rtree.phi treeHeap xTree s3.mem = Rtree.phi treeHeap xTree st.mem :=
    htreeLoc3.2.symm
  rw [hSum3, hTreePhi3] at hc4
  exact ⟨s4, finalHeap, c4, sFin, yTree, slotFin, nameFin, yCore, yTerm,
    hr4, hs4_3, hs4_regsHi, hinv4, hstat4, hz4, hafterLe, hfinHi, htreeOut4, hcores4, hc4⟩

end MinCostFlow.MinRatio
