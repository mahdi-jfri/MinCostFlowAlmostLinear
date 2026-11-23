module

public import MinCostFlow.LSF.Program.TreeStageMath
public import MinCostFlow.LSF.Program.InitTreeQNat

/-!
# The copies of the edges, in one procedure

Before the `[AN19]` call, the initialization makes the graph `G_v`: edge `e` of `G₀` gets
`edgeMult G₀ v e` parallel copies of the same length and of weight `1`. `treeCopiesProc` does this
in four calls:
1. `initTreeQNatProc` computes the multiplicities (and the numbers `q_nat` that the order `π`
   uses later);
2. `memFillStmt` clears the weight blocks of the copies;
3. `initTreeCopiesProc` writes the copies;
4. `initMarkBridgesStmt` marks the bridge IDs that would collide with the IDs of the copies.

`treeCopies_meetsContract` states the result in the form that the `[AN19]` call
(`lsstFrontierContract`) and `lsst_decode_lift` ask for: the copy arrays are the graph
`copyIndexedGraph`, with the lengths of the original edges and weight `2 ^ (-P)`.
The cost is `O(m₀ K_w² + m₀ L_in + n₀)`, where `K_w` is the width of the multiplicity sums.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.WideWord MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The multiplicity of the `j`-th edge of `eList`. -/
noncomputable def treeMult (G₀ : MGraph) (v : ℕ → ℝ) (eList : List ℕ) (j : ℕ) : ℕ :=
  edgeMult G₀ v (eList.getD j 0)

/-- Args: `[g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap,
multPtr, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr,
usedBridgePtr]`. Returns the number of copies. -/
def treeCopiesProc (bQ bFill bCp bMk : ℕ) : Stmt :=
  .cond (.reg 5)
    (.call 20 bQ [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
      .call 20 bFill [.reg 16, .bin .mul (.bin .mul (.const 2) (.reg 5)) (.reg 4), .const 0] ;;
      .call 21 bCp [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5, .reg 12, .reg 9, .reg 13, .reg 14,
        .reg 15, .reg 16, .reg 17, .reg 18] ;;
      .call 20 bMk [.reg 1, .reg 12, .reg 19, .reg 5, .reg 10, .reg 11] ;;
      .ret (.reg 21))
    (.call 20 bMk [.reg 1, .reg 12, .reg 19, .reg 5, .reg 10, .reg 11] ;;
      .ret (.const 0))

lemma treeCopiesProc_noRand (bQ bFill bCp bMk : ℕ) : (treeCopiesProc bQ bFill bCp bMk).NoRand := by
  simp [treeCopiesProc, Stmt.NoRand]

/-- The contract of `treeCopiesProc`. The inputs lie below `qNatPtr`; the multiplicities, the
scratch of `initTreeQNatProc`, the copies and the bridge marks follow in this order, each copy
array with room for `2 m₀` copies. -/
def treeCopiesContract (w h : ℕ) (G₀ : MGraph) (v ℓ₀ : ℕ → ℝ) (P_fp : ℕ)
    (vList eList : List ℕ) : Contract where
  pre args mem := ∃ (g0Ptr eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap vIdxBase n0 eCap
      multPtr copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      usedBridgePtr vCap0 eCap0 : ℕ),
    args = [g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap,
      multPtr, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr,
      usedBridgePtr] ∧
    1 ≤ h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L_in ∧ 2 ≤ h * L_in ∧ h ∣ P_fp ∧
    G₀.IsValid ∧ G₀.E.card = m0 ∧ G₀.n = n0 ∧ K_w = kWidthOf m0 L_in ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧ g0Ptr + dynGraphSize vCap0 eCap0 ≤ qNatPtr ∧
    (∀ e ∈ G₀.E, e < eCap) ∧
    eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧ ListAt mem eListPtr eList ∧
    eListPtr + m0 ≤ qNatPtr ∧
    vList.length = n0 ∧ vList.Nodup ∧ (∀ u, u ∈ vList ↔ u ∈ G₀.V) ∧
    (∀ i (hi : i < vList.length), mem (vIdxBase + vList[i]) = i + 1) ∧
    vIdxBase + vCap0 ≤ qNatPtr ∧
    (∀ e ∈ G₀.E, lenArr + e * L_in + L_in ≤ qNatPtr) ∧
    (∀ e ∈ G₀.E, wtArr + e * L_in + L_in ≤ qNatPtr) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
      Num.fixVal mem (wtArr + e * L_in) h L_in P_fp = v e ∧ 0 < v e) ∧
    multPtr = qNatPtr + m0 * (K_w + 6) ∧
    multPtr + m0 + 5 * K_w + 2 * (K_w + 6) ≤ copyTailPtr ∧
    copyTailPtr + 2 * m0 ≤ copyHeadPtr ∧ copyHeadPtr + 2 * m0 ≤ copyLenPtr ∧
    copyLenPtr + 2 * m0 * L_in ≤ copyWtPtr ∧ copyWtPtr + 2 * m0 * L_in ≤ copyOrigIdxPtr ∧
    copyOrigIdxPtr + 2 * m0 ≤ copySubIdxPtr ∧ copySubIdxPtr + 2 * m0 ≤ usedBridgePtr ∧
    usedBridgePtr + (2 * m0 + n0) ≤ lsstHeap ∧
    lsstHeap + m0 * multQNatStepSpace K_w < 2 ^ w ∧
    eCap + (2 * m0 + n0) + eCap < 2 ^ w ∧
    ZeroFrom mem lsstHeap
  post args mem ret mem' := ∃ (g0Ptr eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap vIdxBase
      n0 eCap multPtr copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      usedBridgePtr : ℕ),
    args = [g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap,
      multPtr, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr,
      usedBridgePtr] ∧
    ret = (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m ∧
    (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m ≤ 2 * m0 ∧
    (∀ j < m0, mem' (multPtr + j) = treeMult G₀ v eList j ∧
      Num.Valid mem' (qNatPtr + j * (K_w + 6)) h (K_w + 6) ∧
      Num.unsignedVal mem' (qNatPtr + j * (K_w + 6)) h (K_w + 6) =
        (treeMult G₀ v eList j * 2 ^ (h * (L_in + 4))) /
          (Num.intVal mem (lenArr + eList.getD j 0 * L_in) h L_in).toNat) ∧
    ListAt mem' copyTailPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m =>
        (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).tail i.1) ∧
    ListAt mem' copyHeadPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m =>
        (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).head i.1) ∧
    CopyArraysAt mem' copyTailPtr copyHeadPtr copyOrigIdxPtr G₀ vList
      (copyList eList (treeMult G₀ v eList) G₀.E.card) ∧
    (∀ q < (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m,
      Num.Valid mem' (copyLenPtr + q * L_in) h L_in ∧
      Num.fixVal mem' (copyLenPtr + q * L_in) h L_in P_fp =
        ℓ₀ ((copyList eList (treeMult G₀ v eList) G₀.E.card).getD q (0, 0)).1 ∧
      0 < ℓ₀ ((copyList eList (treeMult G₀ v eList) G₀.E.card).getD q (0, 0)).1) ∧
    (∀ q < (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m,
      Num.Valid mem' (copyWtPtr + q * L_in) h L_in ∧
      Num.fixVal mem' (copyWtPtr + q * L_in) h L_in P_fp = (2 : ℝ)⁻¹ ^ P_fp ∧
      0 < (2 : ℝ)⁻¹ ^ P_fp) ∧
    (∀ z < 2 * m0 + n0,
      (mem' (usedBridgePtr + z) = 1 ↔
        ∃ j < m0, ∃ k < treeMult G₀ v eList j, eList.getD j 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem' (usedBridgePtr + z) = 0 ∨ mem' (usedBridgePtr + z) = 1)) ∧
    ZeroFrom mem' lsstHeap ∧
    ∀ a < qNatPtr, mem' a = mem a
  cost args _ :=
    initTreeQNatCost (args.getD 5 0) (args.getD 4 0) (args.getD 6 0) +
      100 * (args.getD 5 0) * (args.getD 4 0) + 600 * args.getD 5 0 + 20 * args.getD 10 0 + 400

/-- Two lists at the same place with the same length are equal. -/
lemma listAt_unique {mem : ℕ → ℕ} {a : ℕ} {l l' : List ℕ} (h : ListAt mem a l)
    (h' : ListAt mem a l') (hlen : l.length = l'.length) : l = l' := by
  refine List.ext_getElem hlen fun i hi hi' => ?_
  rw [← h i hi, h' i hi']

lemma range_map_congr {f g : ℕ → ℕ} {j m : ℕ} (hj : j ≤ m) (hfg : ∀ t < m, f t = g t) :
    (List.range j).map f = (List.range j).map g :=
  List.map_congr_left fun t ht => hfg t (by rw [List.mem_range] at ht; omega)

theorem treeCopies_meetsContract {w h : ℕ} {G₀ : MGraph} {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ}
    {vList eList : List ℕ} {p : Program} {b bQ bFill bCp bMk : ℕ}
    (hp : p.procs[b]? = some (treeCopiesProc bQ bFill bCp bMk))
    (hQ : MeetsContract w p bQ (initTreeQNatContract w h G₀ v))
    (hFill : MeetsContract w p bFill (memFillContract w))
    (hCp : MeetsContract w p bCp (initTreeCopiesContract w G₀ vList eList))
    (hMk : MeetsContract w p bMk (initMarkBridgesContract w G₀ eList (treeMult G₀ v eList))) :
    MeetsContract w p b (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap,
    multPtr, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr,
    usedBridgePtr, vCap0, eCap0, rfl, hh1, hw3h, hL1, hhL, hdivP, hGv, hm, hn, hKw, hdg,
    hdgb, heCap, heLen, heNd, heMem, heAt, heb, hvLen, hvNd, hvMem, hvIdx, hvIdxb, hlenb, hwtb,
    hlen, hwt, hmult, hmb, hc1, hc2, hc3, hc4, hc5, hc6, hub, hheap, heCapw, hz⟩ := hpre
  set args := [g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap,
      multPtr, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr,
      usedBridgePtr] with hargs
  have hR0 : ∀ i < 20, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 20, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hw16 : 16 ≤ 2 ^ w := by
    have : 5 ≤ w := by omega
    exact le_trans (by decide : 16 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) this)
  have hw1 : 1 < 2 ^ w := by omega
  have hlw : lsstHeap < 2 ^ w := by
    have := Nat.zero_le (m0 * multQNatStepSpace K_w); omega
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
  have r19 := hR0 19 (by omega)
  refine runs_start_le ?_
  unfold treeCopiesProc
  refine WordRAM.runs_cond_le (v := m0) (by eval_expr) ?_ ?_
  rotate_left
  · -- no edges: only the bridge marks
    intro hm0
    subst hm0
    refine runs_seq_call_le (vs := [eListPtr, multPtr, usedBridgePtr, 0, n0, eCap]) hMk
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _)))))))
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hwa 1 (by omega)
        · exact hwa 12 (by omega)
        · exact hwa 19 (by omega)
        · exact hwa 5 (by omega)
        · exact hwa 10 (by omega)
        · exact hwa 11 (by omega))
      ⟨eListPtr, multPtr, usedBridgePtr, 0, n0, eCap, rfl, hw16, hm, hn, heCap, by omega,
        by omega, heLen, heNd, heMem, heAt, by omega, Or.inl (by omega),
        fun j hj => absurd hj (Nat.not_lt_zero _), by omega, Or.inl (by omega)⟩ ?_
    rintro v₄ mem₄ pos₄ ⟨eListPtr', multPtr', usedBridgePtr', m0', n0', eCap', heq₄, -, hmk₄,
      hfr₄⟩
    simp only [List.cons.injEq, and_true] at heq₄
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
    have hcl : copyList eList (treeMult G₀ v eList) G₀.E.card = [] := by
      rw [hm]; exact copyList_zero _ _
    have hM0 : (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m = 0 := by
      simp only [copyIndexedGraph, hcl, List.length_nil]
    refine runs_ret_le (v := 0) (by eval_expr) ⟨g0Ptr, eListPtr, lenArr, wtArr, L_in, 0, K_w,
      qNatPtr, lsstHeap, vIdxBase, n0, eCap, multPtr, copyTailPtr, copyHeadPtr, copyLenPtr,
      copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, usedBridgePtr, rfl, hM0.symm, by omega,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun i hi => ?_, fun i hi => ?_,
      fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, hmk₄, fun a ha => ?_, fun a ha => ?_⟩ ?_
    · simp only [List.length_ofFn, hM0] at hi; omega
    · simp only [List.length_ofFn, hM0] at hi; omega
    · rw [hcl] at hq; simp at hq
    · omega
    · omega
    · show mem₄ a = 0
      rw [hfr₄ a (Or.inr (by omega))]; exact hz a ha
    · show mem₄ a = mem a
      exact hfr₄ a (Or.inl (by omega))
    · simp only [treeCopiesContract, initMarkBridgesContract, argsSize, Expr.size_const,
        Expr.size_reg, List.sum_cons, List.sum_nil, List.range_zero, List.map_nil,
        List.getD_cons_zero, List.getD_cons_succ, hargs]
      omega
  intro hm0ne
  have hm1 : 1 ≤ m0 := Nat.pos_of_ne_zero hm0ne
  -- the multiplicities and their sum
  set mult := treeMult G₀ v eList with hmultdef
  have hvpos : ∀ e ∈ G₀.E, 0 < v e := fun e he => (hwt e he).2.2
  have hsum : (List.map mult (List.range G₀.E.card)).sum ≤ 2 * G₀.E.card :=
    edgeMult_sum_le_two_mul hvpos (by omega) heNd heMem (fun j _ => rfl)
  rw [hm] at hsum
  set M := (List.map mult (List.range m0)).sum with hMdef
  have hMm : (copyIndexedGraph G₀ vList eList mult).m = M := by
    simp only [copyIndexedGraph, copyList_length, hm, hMdef]
  have hmultle : ∀ j < m0, mult j ≤ M := fun j hj =>
    List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have hML : M * L_in ≤ 2 * m0 * L_in := Nat.mul_le_mul_right _ hsum
  have h2mL : 2 * m0 * L_in < 2 ^ w := by omega
  -- the inputs below `qNatPtr`
  have hVlt : ∀ u ∈ G₀.V, u < vCap0 := hdg.2.1
  have hvIdxLt : ∀ i (hi : i < vList.length), vIdxBase + vList[i] < qNatPtr := fun i hi => by
    have := hVlt _ ((hvMem _).mp (List.getElem_mem hi)); omega
  have hlow : ∀ memX : ℕ → ℕ, (∀ a < qNatPtr, memX a = mem a) →
      DynGraphAt memX g0Ptr vCap0 eCap0 G₀ ∧ ListAt memX eListPtr eList ∧
      (∀ i (hi : i < vList.length), memX (vIdxBase + vList[i]) = i + 1) ∧
      (∀ e ∈ G₀.E, ∀ i < L_in, memX (lenArr + e * L_in + i) = mem (lenArr + e * L_in + i)) := by
    intro memX hX
    refine ⟨hdg.of_agree fun a _ ha => hX a (by omega), fun i hi => ?_, fun i hi => ?_,
      fun e he i hi => hX _ (by have := hlenb e he; omega)⟩
    · rw [hX _ (by omega)]; exact heAt i hi
    · rw [hX _ (hvIdxLt i hi)]; exact hvIdx i hi
  have he0 : eList[0]'(by omega) ∈ G₀.E := (heMem _).mp (List.getElem_mem _)
  have hlenw : lenArr < 2 ^ w := by have := hlenb _ he0; omega
  -- 1. the multiplicities and `q_nat`
  refine runs_seq_call_le (vs := [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap]) hQ
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega))
    ⟨ℓ₀, eList, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, P_fp, rfl, hh1, hw3h,
      hL1, hdivP, hGv, hm, hm1, by omega, hKw, heLen, heNd, heMem, heAt, heb, hlenb, hwtb,
      by omega, hheap, hlen, hwt, hz⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨eList', eListPtr', lenArr', wtArr', L_in', m0', K_w', qNatPtr', lsstHeap',
    heq₁, -, heLen', -, -, heAt', hq₁, hz₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  have hEL : eList' = eList := listAt_unique heAt' heAt (by omega)
  subst eList'
  try dsimp only at hq₁
  have hA1 := hlow mem₁ hfr₁
  have hmult₁ : ∀ j < m0, mem₁ (multPtr + j) = mult j := fun j hj => by
    rw [hmult]; exact (hq₁ j hj).1
  -- 2. clear the weight blocks of the copies
  refine runs_seq_call_le (vs := [copyWtPtr, 2 * m0 * L_in, 0]) hFill
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr <;> omega)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwa 16 (by omega)
      · exact h2mL
      · omega)
    ⟨copyWtPtr, 2 * m0 * L_in, 0, rfl, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨dst', len', val', heq₂, -, hfill₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfill₂ hfr₂
  have hA2 : ∀ a < copyWtPtr, mem₂ a = mem₁ a := fun a ha => hfr₂ a (Or.inl ha)
  have hB2 := hlow mem₂ (fun a ha => (hA2 a (by omega)).trans (hfr₁ a ha))
  have hmult₂ : ∀ j < m0, mem₂ (multPtr + j) = mult j := fun j hj => by
    rw [hA2 _ (by omega)]; exact hmult₁ j hj
  have hM₂ : ((List.range m0).map fun j => mem₂ (multPtr + j)).sum = M := by
    rw [hMdef, range_map_congr le_rfl hmult₂]
  -- 3. the copies
  refine runs_seq_call_le (vs := [g0Ptr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
      copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr]) hCp
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 13 (by omega)
      · exact hwa 14 (by omega)
      · exact hwa 15 (by omega)
      · exact hwa 16 (by omega)
      · exact hwa 17 (by omega)
      · exact hwa 18 (by omega))
    ⟨vCap0, eCap0, g0Ptr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase, copyTailPtr, copyHeadPtr,
      copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, M, rfl, hw16, hGv, hVlt, hm, hL1,
      hwa 4 (by omega), hlenw, hn ▸ hwa 10 (by omega), hwa 5 (by omega), by omega, hB2.1, by omega, heLen, heNd, heMem, hB2.2.1,
      by omega, hvNd, hvMem, hB2.2.2.1, hM₂.symm,
      fun e he => by have := hlenb e he; omega, by omega,
      fun a _ ha => Or.inl (by omega), by omega, fun a _ ha => Or.inl (by omega), by omega,
      fun a _ ha => Or.inl (by omega), fun a _ ha => Or.inl (by omega),
      by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨vCap', eCap', g0Ptr', eListPtr', lenArr', L_in', m0', multPtr', vIdxBase',
    copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', copyOrigIdxPtr', copySubIdxPtr', M',
    heq₃, hM', hv₃, hcp₃, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  rw [hM₂] at hM'
  subst hM'
  try dsimp only at hcp₃ hfr₃
  have hA3 : ∀ a < copyTailPtr, mem₃ a = mem₂ a := fun a ha => hfr₃ a (Or.inl ha)
  have hmult₃ : ∀ j < m0, mem₃ (multPtr + j) = mult j := fun j hj => by
    rw [hA3 _ (by omega)]; exact hmult₂ j hj
  have hB3 := hlow mem₃ (fun a ha => ((hA3 a (by omega)).trans (hA2 a (by omega))).trans
    (hfr₁ a ha))
  have hM₃ : ((List.range m0).map fun j => mem₃ (multPtr + j)).sum = M := by
    rw [hMdef, range_map_congr le_rfl hmult₃]
  -- 4. the bridge marks
  refine runs_seq_call_le (vs := [eListPtr, multPtr, usedBridgePtr, m0, n0, eCap]) hMk
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _)))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 1 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 19 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 11 (by omega))
    ⟨eListPtr, multPtr, usedBridgePtr, m0, n0, eCap, rfl, hw16, hm, hn, heCap, by omega,
      by omega, heLen, heNd, heMem, hB3.2.1, by omega, Or.inl (by omega),
      fun j hj => ⟨hmult₃ j hj, by have := hmultle j hj; omega⟩, by omega,
      Or.inl (by omega)⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨eListPtr', multPtr', usedBridgePtr', m0', n0', eCap', heq₄, -, hmk₄,
    hfr₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  have hA4 : ∀ a < usedBridgePtr, mem₄ a = mem₃ a := fun a ha => hfr₄ a (Or.inl ha)
  -- the copy facts in the last memory
  have hcopyW : CopiesWritten mem₄ copyTailPtr copyHeadPtr copyOrigIdxPtr G₀.E.card G₀ vList
      eList mult := by
    intro j hj k hk
    rw [hm] at hj
    have hk' : k < mem₂ (multPtr + j) := by rw [hmult₂ j hj]; exact hk
    have hc := hcp₃ j hj k hk'
    rw [range_map_congr (by omega) hmult₂] at hc
    obtain ⟨hqM, -, -, ht, hvt, hh', hvh, -, -, -, ho, -⟩ := hc
    rw [hA4 _ (by omega), hA4 _ (by omega), hA4 _ (by omega)]
    exact ⟨by omega, hvt, by omega, hvh, ho⟩
  refine runs_ret_le (v := M) (by eval_expr) ⟨g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w,
    qNatPtr, lsstHeap, vIdxBase, n0, eCap, multPtr, copyTailPtr, copyHeadPtr, copyLenPtr,
    copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, usedBridgePtr, rfl, hMm.symm, by rw [hMm]; exact hsum,
    fun j hj => ?_, copyTails_listAt hvNd hcopyW, copyHeads_listAt hvNd hcopyW,
    copyArraysAt_of_copies hcopyW, ?_, ?_, hmk₄, fun a ha => ?_, fun a ha => ?_⟩ ?_
  · -- the multiplicities and `q_nat`
    try dsimp only
    have hj' := hq₁ j hj
    have hblk : ∀ i < K_w + 6, mem₄ (qNatPtr + j * (K_w + 6) + i) =
        mem₁ (qNatPtr + j * (K_w + 6) + i) := by
      intro i hi
      have hjK : (j + 1) * (K_w + 6) ≤ m0 * (K_w + 6) := Nat.mul_le_mul_right _ hj
      have : j * (K_w + 6) + i < m0 * (K_w + 6) := by rw [Nat.add_one_mul] at hjK; omega
      rw [hA4 _ (by omega), hA3 _ (by omega), hA2 _ (by omega)]
    refine ⟨by rw [hA4 _ (by omega)]; exact hmult₃ j hj, fun i hi => ?_, ?_⟩
    · rw [hblk i hi]; exact hj'.2.1 i hi
    · rw [Num.unsignedVal_congr (fun i hi => hblk i hi)]
      exact hj'.2.2
  · -- the lengths
    try dsimp only
    refine copyLens_spec heMem (by omega) hlen fun j hj k hk i hi => ?_
    simp only [← hmultdef] at hk ⊢
    rw [hm] at hj
    have hk' : k < mem₂ (multPtr + j) := by rw [hmult₂ j hj]; exact hk
    have hc := hcp₃ j hj k hk'
    rw [range_map_congr (by omega) hmult₂] at hc
    have hqM := hc.1
    have hlt : (((List.range j).map mult).sum + k) * L_in + i < M * L_in := by
      have := Nat.mul_le_mul_right L_in (show ((List.range j).map mult).sum + k + 1 ≤ M by omega)
      rw [Nat.add_one_mul] at this; omega
    have he : eList.getD j 0 ∈ G₀.E := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact (heMem _).mp (List.getElem_mem _)
    rw [hA4 _ (by omega), hc.2.2.2.2.2.2.2.1 i hi]
    exact hB2.2.2.2 _ he i hi
  · -- the weights
    try dsimp only
    refine copyWts_spec (mem := mem₂) hh1 hhL (fun j hj k hk => ?_) (fun q hq i hi0 hi => ?_)
    · simp only [← hmultdef] at hk ⊢
      rw [hm] at hj
      have hk' : k < mem₂ (multPtr + j) := by rw [hmult₂ j hj]; exact hk
      have hc := hcp₃ j hj k hk'
      rw [range_map_congr (by omega) hmult₂] at hc
      have hqM := hc.1
      have hlt : (((List.range j).map mult).sum + k) * L_in + L_in ≤ M * L_in := by
        have := Nat.mul_le_mul_right L_in (show ((List.range j).map mult).sum + k + 1 ≤ M by omega)
        rw [Nat.add_one_mul] at this; omega
      refine ⟨?_, fun i hi0 hi => ?_⟩
      · rw [hA4 _ (by omega)]; exact hc.2.2.2.2.2.2.2.2.1
      · rw [hA4 _ (by omega)]; exact hc.2.2.2.2.2.2.2.2.2.1 i hi0 hi
    · simp only [← hmultdef] at hq
      rw [hMm] at hq
      have hlt : q * L_in + i < 2 * m0 * L_in := by
        have := Nat.mul_le_mul_right L_in (show q + 1 ≤ M by omega)
        rw [Nat.add_one_mul] at this; omega
      rw [show copyWtPtr + q * L_in + i = copyWtPtr + (q * L_in + i) by omega]
      exact hfill₂ _ hlt
  · -- the heap stays clear
    try dsimp only
    have h4 : mem₄ a = mem₃ a := hfr₄ a (Or.inr (by omega))
    rw [h4, hfr₃ a (Or.inr (by omega)), hfr₂ a (Or.inr (by omega))]
    exact hz₁ a ha
  · -- the frame
    try dsimp only
    rw [hA4 a (by omega), hA3 a (by omega), hA2 a (by omega)]
    exact hfr₁ a ha
  · -- the cost
    simp only [treeCopiesContract, initTreeQNatContract, memFillContract, initTreeCopiesContract,
      initTreeCopiesCost, initMarkBridgesContract, argsSize, Expr.size_const, Expr.size_reg,
      Expr.size_bin, List.sum_cons, List.sum_nil,
      List.getD_cons_zero, List.getD_cons_succ, hargs]
    rw [hM₂, hM₃]
    have h1 : M * (25 * L_in + 80) ≤ 2 * m0 * (25 * L_in + 80) := Nat.mul_le_mul_right _ hsum
    have e0 : 2 * m0 * (25 * L_in + 80) = 50 * (m0 * L_in) + 160 * m0 := by ring
    have e1 : 2 * m0 * L_in = 2 * (m0 * L_in) := by ring
    have e2 : 100 * m0 * L_in = 100 * (m0 * L_in) := by ring
    omega

end

end MinCostFlow.LSF.Program
