module

public import MinCostFlow.LSF.Program.TreeCopiesStage

/-!
# The tree `T₀` from the copies, in one procedure

`treeLsstProc` runs the `[AN19]` program on the copy graph (`lsstFrontierProc`) and then writes
the edges of `T₀` as index arrays (`t0EdgesProc`), reading the two counts of the output from its
header. `treeLsst_meetsContract` gives a tree `T_raw` that is a low-stretch spanning tree of
`G_v`, and shows that the arrays describe `T₀ = projectTree G₀ v T_raw` (`T0IndexArrays`). The
edge IDs of `T₀` are below `eCap + ubLen`: an edge of `G₀` is below `eCap`, and a bridge is named
`eCap + z` for a free slot `z < ubLen` of the collision table. These are the facts that the rooting of `T₀` and `ValidLSFParams` ask for.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.WideWord

@[expose] public section

/-- Args: `[n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr, usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr,
tHeadPtr]`. Returns the heap pointer after the `[AN19]` call. -/
def treeLsstProc (bL bT0 : ℕ) : Stmt :=
  .call 19 bL [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11] ;;
  .assign 20 (.load (.reg 10)) ;;
  .assign 21 (.load (.bin .add (.reg 10) (.const 1))) ;;
  .call 22 bT0 [.reg 20, .reg 21, .reg 8, .reg 9, .reg 2, .reg 3, .reg 12, .reg 13, .reg 14,
    .reg 15, .reg 16, .reg 17, .reg 18] ;;
  .ret (.reg 19)

lemma treeLsstProc_noRand (bL bT0 : ℕ) : (treeLsstProc bL bT0).NoRand := by
  simp [treeLsstProc, Stmt.NoRand]

/-- The contract of `treeLsstProc`. The copy arrays, the output of the `[AN19]` call, the bridge
marks and the edge arrays of `T₀` follow each other below the heap pointer `lsstHeap`. -/
noncomputable def treeLsstContract (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ)
    (G₀ : MGraph) (v ℓ₀ : ℕ → ℝ) (P_fp : ℕ) (vList eList : List ℕ) : Contract where
  pre args mem := ∃ (n0 M copyTailPtr copyHeadPtr copyLenPtr copyWtPtr L_in L_sim outOrigPtr
      outBridgePtr outHdrPtr lsstHeap copyOrigIdxPtr usedBridgePtr ubLen eCap tOrigPtr tTailPtr
      tHeadPtr : ℕ),
    args = [n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
      outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr, usedBridgePtr, ubLen, eCap, tOrigPtr,
      tTailPtr, tHeadPtr] ∧
    1 ≤ c_AN ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L_in ∧
    G₀.IsValid ∧ G₀.V.Nonempty ∧ (∀ e ∈ G₀.E, 0 < ℓ₀ e) ∧ (∀ e ∈ G₀.E, 0 < v e) ∧
    vList.length = G₀.n ∧ vList.Nodup ∧ (∀ u, u ∈ vList ↔ u ∈ G₀.V) ∧
    eList.length = G₀.E.card ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
    (∀ e ∈ G₀.E, e < eCap) ∧
    n0 = G₀.n ∧ M = (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m ∧
    ubLen = 2 * G₀.E.card + G₀.n ∧
    lsstLSimMin c_AN G₀.n M L_in h ≤ L_sim ∧
    ListAt mem copyTailPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m =>
        (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).tail i.1) ∧
    ListAt mem copyHeadPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m =>
        (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).head i.1) ∧
    CopyArraysAt mem copyTailPtr copyHeadPtr copyOrigIdxPtr G₀ vList
      (copyList eList (treeMult G₀ v eList) G₀.E.card) ∧
    (∀ q < M, Num.Valid mem (copyLenPtr + q * L_in) h L_in ∧
      Num.fixVal mem (copyLenPtr + q * L_in) h L_in P_fp =
        ℓ₀ ((copyList eList (treeMult G₀ v eList) G₀.E.card).getD q (0, 0)).1 ∧
      0 < ℓ₀ ((copyList eList (treeMult G₀ v eList) G₀.E.card).getD q (0, 0)).1) ∧
    (∀ q < M, Num.Valid mem (copyWtPtr + q * L_in) h L_in ∧
      Num.fixVal mem (copyWtPtr + q * L_in) h L_in P_fp = (2 : ℝ)⁻¹ ^ P_fp ∧
      0 < (2 : ℝ)⁻¹ ^ P_fp) ∧
    (∀ z < ubLen,
      (mem (usedBridgePtr + z) = 1 ↔
        ∃ j < G₀.E.card, ∃ k < treeMult G₀ v eList j,
          eList.getD j 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem (usedBridgePtr + z) = 0 ∨ mem (usedBridgePtr + z) = 1)) ∧
    copyTailPtr + M ≤ copyHeadPtr ∧ copyHeadPtr + M ≤ copyLenPtr ∧
    copyLenPtr + M * L_in ≤ copyWtPtr ∧ copyWtPtr + M * L_in ≤ copyOrigIdxPtr ∧
    copyOrigIdxPtr + M ≤ outOrigPtr ∧ outOrigPtr + n0 ≤ outBridgePtr ∧
    outBridgePtr + 2 * n0 ≤ outHdrPtr ∧ outHdrPtr + 2 ≤ usedBridgePtr ∧
    usedBridgePtr + ubLen ≤ tOrigPtr ∧ tOrigPtr + n0 ≤ tTailPtr ∧ tTailPtr + n0 ≤ tHeadPtr ∧
    tHeadPtr + n0 ≤ lsstHeap ∧ eCap + ubLen < 2 ^ w ∧
    ZeroFrom mem lsstHeap ∧ lsstHeap + lsstSpace Q_AN K_AN n0 M L_sim h < 2 ^ w
  post args mem ret mem' := ∃ (n0 M copyTailPtr copyHeadPtr copyLenPtr copyWtPtr L_in L_sim
      outOrigPtr outBridgePtr outHdrPtr lsstHeap copyOrigIdxPtr usedBridgePtr ubLen eCap tOrigPtr
      tTailPtr tHeadPtr : ℕ),
    args = [n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
      outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr, usedBridgePtr, ubLen, eCap, tOrigPtr,
      tTailPtr, tHeadPtr] ∧
    lsstHeap ≤ ret ∧ ret ≤ lsstHeap + lsstSpace Q_AN K_AN n0 M L_sim h ∧ ZeroFrom mem' ret ∧
    (∃ T_raw : MGraph,
      IsLSST (if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
        (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
        (fun _ => 1)
        ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw ∧
      (projectTree G₀ v T_raw).V = G₀.V ∧
      T0IndexArrays (projectTree G₀ v T_raw) vList (G₀.n - 1) (fun i => mem' (tOrigPtr + i))
        (fun i => mem' (tTailPtr + i)) (fun i => mem' (tHeadPtr + i)) ∧
      ∀ f ∈ (projectTree G₀ v T_raw).E, f < eCap + ubLen) ∧
    (∃ nOrig ≤ G₀.n - 1, mem' outHdrPtr = nOrig ∧
      ∀ i < G₀.n - 1, (mem' (tOrigPtr + i) ∈ G₀.E ↔ i < nOrig)) ∧
    ∀ a < lsstHeap, (a < outOrigPtr ∨ outHdrPtr + 2 ≤ a) → (a < tOrigPtr ∨ tHeadPtr + n0 ≤ a) →
      mem' a = mem a
  cost args _ :=
    lsstCost Q_AN K_AN c_AN (args.getD 0 0) (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) h +
      60 * args.getD 0 0 + 80 * args.getD 14 0 + 200

theorem treeLsst_meetsContract {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {w h : ℕ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {vList eList : List ℕ} {p : Program} {b bL bT0 : ℕ}
    (hp : p.procs[b]? = some (treeLsstProc bL bT0))
    (hL : MeetsContract w p bL (lsstFrontierContract Q_AN c_AN K_AN w h
      (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)) (fun _ => (2 : ℝ)⁻¹ ^ P_fp)
      (fun q => ℓ₀ ((copyList eList (treeMult G₀ v eList) G₀.E.card).getD q (0, 0)).1) P_fp))
    (hT0 : MeetsContract w p bT0 (t0EdgesContract w)) :
    MeetsContract w p b (treeLsstContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
    outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr, usedBridgePtr, ubLen, eCap, tOrigPtr,
    tTailPtr, tHeadPtr, rfl, hc, hh1, hw3h, hL1, hGv, hVne, hℓpos, hvpos, hvLen, hvNd, hvMem,
    heLen, heNd, heMem, heCap, hn0, hM, hub, hLsim, hTl, hHd, hCA, hLen, hWt, hmark, hl1, hl2,
    hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hecw, hz, hsp⟩ := hpre
  subst hub
  set args := [n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
      outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr, usedBridgePtr, (2 * G₀.E.card + G₀.n), eCap, tOrigPtr,
      tTailPtr, tHeadPtr] with hargs
  have hR0 : ∀ i < 19, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 19, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hw16 : 16 ≤ 2 ^ w := by
    have : 5 ≤ w := by omega
    exact le_trans (by decide : 16 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) this)
  set G := copyIndexedGraph G₀ vList eList (treeMult G₀ v eList) with hGdef
  set cl := copyList eList (treeMult G₀ v eList) G₀.E.card with hcldef
  have hGn : G.n = G₀.n := rfl
  have hGm : G.m = cl.length := rfl
  have hGval : G.Valid := copyIndexedGraph_valid hGv hVne hvLen hvMem heLen heMem
  have hLsw : lsstHeap < 2 ^ w := by have := Nat.zero_le (lsstSpace Q_AN K_AN n0 M L_sim h); omega
  refine runs_start_le ?_
  unfold treeLsstProc
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  have r7 := hR0 7 (by omega)
  have r8 := hR0 8 (by omega)
  have r9 := hR0 9 (by omega)
  have r10 := hR0 10 (by omega)
  have r11 := hR0 11 (by omega)
  have r12 := hR0 12 (by omega)
  have r13 := hR0 13 (by omega)
  have r14 := hR0 14 (by omega)
  have r15 := hR0 15 (by omega)
  have r16 := hR0 16 (by omega)
  have r17 := hR0 17 (by omega)
  have r18 := hR0 18 (by omega)
  -- 1. the `[AN19]` call
  have hML : M * L_in = G.m * L_in := by rw [hM]
  refine runs_seq_call_le (vs := [n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in,
      L_sim, outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap]) hL
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _)))))))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 11 (by omega))
    ⟨n0, M, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim, outOrigPtr,
      outBridgePtr, outHdrPtr, lsstHeap, rfl, hn0, hM, hc, hGval, hh1, hw3h, hL1,
      by rw [hGn, ← hM]; exact hLsim, by omega, by omega, by omega, by omega,
      by rw [hGn]; omega, by rw [hGn]; omega, by omega,
      Or.inl (by rw [hGn]; omega), Or.inl (by rw [hGn]; omega), Or.inl (by rw [hGn]; omega),
      hTl, hHd, fun e he => hLen e (by omega), fun e he => hWt e (by omega), hz,
      by rw [hGn, ← hM, ← hn0]; exact hsp⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n0', M', copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', L_in',
    L_sim', outOrigPtr', outBridgePtr', outHdrPtr', lsstHeap', heq₁, hret1, hret2, hpost₁, hz₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  -- the frame of the call
  have hfr₁ : ∀ a < lsstHeap, (a < outOrigPtr ∨ outHdrPtr + 2 ≤ a) → mem₁ a = mem a := by
    obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, hf⟩ := hpost₁
    intro a ha hout
    exact hf a ha (by rw [hGn]; omega) (by rw [hGn]; omega) (by omega)
  have hmark₁ : ∀ z < 2 * G₀.E.card + G₀.n,
      (mem₁ (usedBridgePtr + z) = 1 ↔ ∃ j' < G₀.E.card, ∃ k < treeMult G₀ v eList j',
        eList.getD j' 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem₁ (usedBridgePtr + z) = 0 ∨ mem₁ (usedBridgePtr + z) = 1) := by
    intro z hzl
    rw [hfr₁ _ (by omega) (Or.inr (by omega))]
    exact hmark z (by omega)
  obtain ⟨origEdges, bridgePairs, hhdr0, hhdr1, hole, hble, hond, hsumn, hoLt, hoInj, hoE, hbLt,
    hbZ, hoAt, hbAt, T_raw, hTraw, hTV, hTE, hTo, hTb⟩ :=
    lsst_decode_lift (P_fp := P_fp) (lsstHeap := lsstHeap) (mult := treeMult G₀ v eList) (mem₀ := mem) hGv hVne hℓpos hvpos
      hvLen hvNd hvMem heLen heNd heMem (fun j _ => rfl) heCap hpost₁ hmark₁
  set zeros := zeroPositions mem₁ usedBridgePtr (2 * G₀.E.card + G₀.n) with hzeros
  -- 2. the two counts
  have hhw : outHdrPtr + 1 < 2 ^ w := by omega
  refine runs_seq_assign_le (v := origEdges.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := bridgePairs.length) (by eval_expr) ?_
  -- 3. the edge arrays of `T₀`
  have hoLtM : ∀ i < origEdges.length, mem₁ (outOrigPtr + i) < M := by
    intro i hi
    rw [hoAt i hi, hM, hGm]
    exact hoLt _ (List.getElem_mem hi)
  have hnBr : bridgePairs.length ≤
      (zeroPositions mem₁ usedBridgePtr (2 * G₀.E.card + G₀.n)).length := hbZ
  refine runs_seq_call_le (vs := [origEdges.length, bridgePairs.length, outOrigPtr, outBridgePtr,
      copyTailPtr, copyHeadPtr, copyOrigIdxPtr, usedBridgePtr, (2 * G₀.E.card + G₀.n), eCap, tOrigPtr, tTailPtr,
      tHeadPtr]) hT0
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have := hwa 0 (by omega); simp only [hargs, List.getD_cons_zero] at this; omega
      · have := hwa 0 (by omega); simp only [hargs, List.getD_cons_zero] at this; omega
      · exact hwa 8 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 13 (by omega)
      · exact hwa 14 (by omega)
      · exact hwa 15 (by omega)
      · exact hwa 16 (by omega)
      · exact hwa 17 (by omega)
      · exact hwa 18 (by omega))
    ⟨origEdges.length, bridgePairs.length, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr,
      copyOrigIdxPtr, usedBridgePtr, 2 * G₀.E.card + G₀.n, eCap, tOrigPtr, tTailPtr, tHeadPtr, M,
      rfl, hw16,
      hoLtM, hnBr, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨nOrig', nBr', outOrigPtr', outBridgePtr', copyTailPtr', copyHeadPtr',
    copyOrigIdxPtr', usedBridgePtr', ubLen', eCap', tOrigPtr', tTailPtr', tHeadPtr', heq₂, -,
    hto₂, htb₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hto₂ htb₂ hfr₂
  -- the copy arrays are still in place
  have hCA₁ : CopyArraysAt mem₁ copyTailPtr copyHeadPtr copyOrigIdxPtr G₀ vList cl := by
    intro q hq
    have hqM : q < M := by rw [hM, hGm]; exact hq
    rw [hfr₁ _ (by omega) (Or.inl (by omega)), hfr₁ _ (by omega) (Or.inl (by omega)),
      hfr₁ _ (by omega) (Or.inl (by omega))]
    exact hCA q hq
  have hA := t0IndexArrays_of_lift (T₀ := projectTree G₀ v T_raw) (tOrigPtr := tOrigPtr)
    (tTailPtr := tTailPtr) (tHeadPtr := tHeadPtr) (mem' := mem₂)
    (ubLen := 2 * G₀.E.card + G₀.n) (zeros := zeros)
    hzeros hvLen heCap hCA₁ hoAt hbAt hoLt hoInj (fun q hq => (hoE q hq).1) hbLt
    hbZ hTE
    (fun i hi => by
      have h := hTo i (by simpa using hi)
      simpa using h)
    (fun k hk => by
      have hkz : k < zeros.length := by omega
      have h := hTb k (by simp [List.length_take]; omega)
      simp only [List.getElem_map, List.getElem_take] at h
      rw [List.getD_eq_getElem _ _ hkz]
      exact h)
    ⟨hto₂, htb₂⟩
  rw [hsumn] at hA
  -- the edge IDs of `T₀`: those of `G₀` are below `eCap`, the bridges are `eCap + z`
  have hTEb : ∀ f ∈ (projectTree G₀ v T_raw).E, f < eCap + (2 * G₀.E.card + G₀.n) := by
    intro f hf
    rw [hTE] at hf
    simp only [List.mem_toFinset, List.mem_append, List.mem_map] at hf
    rcases hf with ⟨q, hq, rfl⟩ | ⟨z, hz, rfl⟩
    · exact lt_of_lt_of_le (heCap _ (hoE q hq).1) (Nat.le_add_right _ _)
    · have := (mem_zeroPositions_iff.mp (List.mem_of_mem_take hz)).1
      omega
  refine runs_ret_le (v := v₁) (by eval_expr) ⟨n0, M, copyTailPtr, copyHeadPtr, copyLenPtr,
    copyWtPtr, L_in, L_sim, outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap, copyOrigIdxPtr,
    usedBridgePtr, 2 * G₀.E.card + G₀.n, eCap, tOrigPtr, tTailPtr, tHeadPtr, rfl, hret1,
    by rw [hn0, hM]; exact hret2, fun a ha => ?_, ⟨T_raw, hTraw, hTV, hA, hTEb⟩,
    ⟨origEdges.length, by omega, by
      try dsimp only
      rw [hfr₂ _ (by omega)]; exact hhdr0, fun i hi => ?_⟩, fun a ha hout ht => ?_⟩ ?_
  · -- the heap stays clear
    try dsimp only [Outcome.value] at ha ⊢
    rw [hfr₂ a (Or.inr (by omega))]
    exact hz₁ a ha
  · -- the edges of `G₀` come first
    try dsimp only
    by_cases hio : i < origEdges.length
    · have hq := hoLt _ (List.getElem_mem hio)
      rw [(hto₂ i hio).1, hoAt i hio, (hCA₁ _ hq).1]
      exact ⟨fun _ => hio, fun _ => (hoE _ (List.getElem_mem hio)).1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = origEdges.length + k := ⟨i - origEdges.length, by omega⟩
      rw [(htb₂ k (by omega)).1]
      refine ⟨fun hmem => absurd (heCap _ hmem) (by omega), fun h => absurd h hio⟩
  · -- the frame
    try dsimp only
    rw [hfr₂ a (by omega)]
    exact hfr₁ a ha hout
  · -- the cost
    simp only [treeLsstContract, lsstFrontierContract, t0EdgesContract, argsSize,
      Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load, List.sum_cons, List.sum_nil,
      List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, hargs]
    have hc : lsstCost Q_AN K_AN c_AN G.n G.m L_in L_sim h = lsstCost Q_AN K_AN c_AN n0 M L_in L_sim h := by
      rw [hGn, hn0, hM]
    omega

end

end MinCostFlow.LSF.Program
