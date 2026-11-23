module

public import MinCostFlow.LSF.Program.InitParams
public import MinCostFlow.LSF.Program.InitScan
public import MinCostFlow.LSF.Program.InitTreeLSSTOpsBase

/-!
# The first stage of the initialization

`prepStageProc` does three things:
1. `initParamsProc` writes the three numbers `D`, `logCap` and `θ` at `paramOut`;
2. `initScanStmt` scans `G₀`: it writes the vertex list, the vertex indices, the flags of the
   original vertices and the component representatives into the aux block;
3. `initCopyGStmt` copies `G₀` into the graph block of the data structure, with the larger caps.

It returns the number of component representatives.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Args: `[g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut, n0, m0, eListPtr, vListPtr]`, where
`eListPtr` is the edge list of the block of `G₀` and `vListPtr = auxVListBase auxPtr vCap`. -/
def prepStageProc (bPar bScan bCopy : ℕ) : Stmt :=
  .call 11 bPar [.reg 7, .reg 3, .reg 6] ;;
  .assign 12 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .call 13 bScan [.reg 0, .reg 1, .reg 4, .reg 12] ;;
  .call 14 bCopy [.reg 0, .reg 5, .reg 9, .reg 10, .reg 1, .reg 2, .reg 7, .reg 8] ;;
  .ret (.reg 13)

lemma prepStageProc_noRand (bPar bScan bCopy : ℕ) : (prepStageProc bPar bScan bCopy).NoRand := by
  simp [prepStageProc, Stmt.NoRand]

/-- The contract of `prepStageProc`. The block of `G₀`, the graph block, the aux block and the
three numbers come in this order in memory. -/
def prepStageContract (w : ℕ) (G₀ : MGraph) : Contract where
  pre args mem := ∃ (g0Ptr vCap eCap k auxPtr dgGPtr paramOut vCap0 eCap0 : ℕ),
    args = [g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut, G₀.n, G₀.E.card,
      dgEListBase g0Ptr vCap0 eCap0, auxVListBase auxPtr vCap] ∧
    16 ≤ 2 ^ w ∧ G₀.V.Nonempty ∧ 1 ≤ k ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧ vCap0 ≤ vCap ∧ eCap0 ≤ eCap ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ dgGPtr ∧ dgGPtr + dynGraphSize vCap eCap ≤ auxPtr ∧
    auxPtr + auxSize vCap G₀.n ≤ paramOut ∧ paramOut + 3 < 2 ^ w ∧
    3 * (4 * k * (hldDepthBound G₀.n + 1)) < 2 ^ w ∧
    (∀ i < dynGraphSize vCap eCap, mem (dgGPtr + i) = 0) ∧
    (∀ v < vCap, mem (auxVIdxBase auxPtr + v) = 0) ∧
    (∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap G₀.n + v) = 0) ∧
    (∀ v < vCap, mem (auxVisABase auxPtr vCap G₀.n + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap G₀.n + v) = 0)
  post args mem ret mem' := ∃ (g0Ptr vCap eCap k auxPtr dgGPtr paramOut vCap0 eCap0 : ℕ)
      (vList repList : List ℕ),
    args = [g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut, G₀.n, G₀.E.card,
      dgEListBase g0Ptr vCap0 eCap0, auxVListBase auxPtr vCap] ∧
    mem' paramOut = hldDepthBound G₀.n ∧ mem' (paramOut + 1) = auxLogCap G₀.n ∧
    mem' (paramOut + 2) = 4 * k * (hldDepthBound G₀.n + 1) ∧
    DynGraphAt mem' dgGPtr vCap eCap G₀ ∧
    vList.length = G₀.n ∧ vList.Nodup ∧ (∀ v, v ∈ vList ↔ v ∈ G₀.V) ∧
    ListAt mem' (auxVListBase auxPtr vCap) vList ∧
    (∀ i (hi : i < vList.length), mem' (auxVIdxBase auxPtr + vList[i]) = i + 1) ∧
    (∀ v < vCap, v ∉ G₀.V → mem' (auxVIdxBase auxPtr + v) = 0) ∧
    (∀ v < vCap, mem' (auxIsOrigVertBase auxPtr vCap G₀.n + v) = if v ∈ G₀.V then 1 else 0) ∧
    (∀ w' ∈ G₀.V, w' < vCap → mem' (auxOrigVertBase auxPtr vCap G₀.n + w') = w') ∧
    (∀ v < vCap, mem' (auxVisABase auxPtr vCap G₀.n + v) = 0 ∧
      mem' (auxVisBBase auxPtr vCap G₀.n + v) = 0) ∧
    1 ≤ ret ∧ ret ≤ G₀.n ∧ repList.length = ret ∧ repList.Nodup ∧
    repList.getD 0 0 = vList.getD 0 0 ∧
    ListAt mem' (auxQBufBBase auxPtr vCap G₀.n) repList ∧
    IsCompReps G₀ (vList.getD 0 0) repList.toFinset ∧
    ∀ a, (a < dgGPtr ∨ dgGPtr + dynGraphSize vCap eCap ≤ a) →
      (a < auxPtr ∨ auxPtr + auxSize vCap G₀.n ≤ a) → (a < paramOut ∨ paramOut + 3 ≤ a) →
      mem' a = mem a
  cost args _ := 20 * Nat.log 2 (args.getD 7 0) + 20 * Nat.log 2 (args.getD 7 0 + 1) +
    640 * args.getD 7 0 + 920 * args.getD 8 0 + 600

theorem prepStage_meetsContract {w : ℕ} {G₀ : MGraph} {p : Program} {b bPar bScan bCopy : ℕ}
    (hp : p.procs[b]? = some (prepStageProc bPar bScan bCopy))
    (hPar : MeetsContract w p bPar (initParamsContract w))
    (hScan : MeetsContract w p bScan (initScanContract w G₀))
    (hCopy : ∀ (vCap0 eCap0 vCap eCap : ℕ) (eList vList : List ℕ),
      MeetsContract w p bCopy (initCopyGContract w vCap0 eCap0 vCap eCap G₀ eList vList)) :
    MeetsContract w p b (prepStageContract w G₀) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut, vCap0, eCap0, rfl, hw16, hVne, hk,
    hdg, hvc, hec, hl1, hl2, hl3, hl4, hθ, hzG, hzI, hzO, hzB⟩ := hpre
  set args := [g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut, G₀.n, G₀.E.card,
      dgEListBase g0Ptr vCap0 eCap0, auxVListBase auxPtr vCap] with hargs
  have hR0 : ∀ i < 11, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 11, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hn1 : 1 ≤ G₀.n := Finset.card_pos.mpr hVne
  have hVlt := hdg.2.1
  have hElt := hdg.2.2.1
  have hnv0 : G₀.n ≤ vCap0 := by
    have hsub : G₀.V ⊆ Finset.range vCap0 := fun v hv => Finset.mem_range.mpr (hVlt v hv)
    simpa [MGraph.n] using Finset.card_le_card hsub
  have hme0 : G₀.E.card ≤ eCap0 := by
    have hsub : G₀.E ⊆ Finset.range eCap0 := fun e he => Finset.mem_range.mpr (hElt e he)
    simpa using Finset.card_le_card hsub
  obtain ⟨eL, heLlen, heLnd, heLmem, heLat, -⟩ := hdg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hauxS : auxVListBase auxPtr vCap + G₀.n ≤ auxPtr + auxSize vCap G₀.n := by
    simp only [auxVListBase, auxVIdxBase, auxHdrSize, auxSize]; omega
  have hEL : dgEListBase g0Ptr vCap0 eCap0 + G₀.E.card ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
    simp only [dgEListBase, dynGraphSize]; omega
  refine runs_start_le ?_
  unfold prepStageProc
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
  -- 1. the three numbers
  refine runs_seq_call_le (vs := [G₀.n, k, paramOut]) hPar
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwa 7 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 6 (by omega))
    ⟨G₀.n, k, paramOut, rfl, hw16, hn1, hk, by omega, hl4, hθ⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n', k', outPtr', heq₁, -, hD₁, hL₁, hT₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hD₁ hL₁ hT₁ hfr₁
  have hlow₁ : ∀ a, a < paramOut → mem₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  -- 2. load `logCap`, then the scan
  refine runs_seq_assign_le (v := auxLogCap G₀.n)
    (by eval_expr <;> simp only [hargs, List.getD_cons_succ, List.getD_cons_zero] <;> omega) ?_
  refine runs_seq_call_le (vs := [g0Ptr, vCap, auxPtr, auxLogCap G₀.n]) hScan
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 4 (by omega)
      · have h1 : auxLogCap G₀.n ≤ G₀.n * auxLogCap G₀.n := Nat.le_mul_of_pos_left _ hn1
        have : G₀.n * auxLogCap G₀.n ≤ auxSize vCap G₀.n := by unfold auxSize; omega
        omega)
    ⟨g0Ptr, vCap, auxPtr, auxLogCap G₀.n, vCap0, eCap0, rfl, hw16, hn1, hVne, hvc, rfl, by omega,
      by omega, hdg.of_agree fun a ha1 ha2 => by
        dsimp only; exact hlow₁ a (by omega),
      fun v hv => by dsimp only; rw [hlow₁ _ (by simp only [auxVIdxBase, auxHdrSize, auxSize] at *; omega)]; exact hzI v hv,
      fun v hv => by
        dsimp only
        rw [hlow₁ _ (by simp only [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
          auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
          auxVListBase, auxVIdxBase, auxHdrSize, auxSize] at *; omega)]
        exact hzO v hv,
      fun v hv => by
        dsimp only
        have hB : auxVisBBase auxPtr vCap G₀.n + v < paramOut := by
          simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
          auxHdrSize, auxSize] at *; omega
        have hA : auxVisABase auxPtr vCap G₀.n + v < paramOut := by
          simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
          auxHdrSize, auxSize] at *; omega
        rw [hlow₁ _ hA, hlow₁ _ hB]
        exact hzB v hv⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨g0Ptr', vCap', auxPtr', logCap', vCap0', eCap0', vList, repList, heq₂, -,
    hvlen, hvnd, hvmem, hvLA, hvI, hvI0, hiso, horig, hvisB, hc1, hc2, hrl, hrnd, hr0, hrLA,
    hcomp, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hvLA hvI hvI0 hiso horig hvisB hrLA hfr₂
  have hout₂ : ∀ a, a < auxPtr → mem₂ a = mem a := fun a ha => by
    rw [hfr₂ a (Or.inl ha)]
    exact hlow₁ a (by omega)
  -- 3. copy `G₀`
  refine runs_seq_call_le (vs := [g0Ptr, dgGPtr, dgEListBase g0Ptr vCap0 eCap0,
      auxVListBase auxPtr vCap, vCap, eCap, G₀.n, G₀.E.card]) (hCopy vCap0 eCap0 vCap eCap eL vList)
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega))
    ⟨g0Ptr, dgGPtr, dgEListBase g0Ptr vCap0 eCap0, auxVListBase auxPtr vCap, G₀.n, G₀.E.card,
      rfl, hw16, hdg.1, rfl, rfl, fun v hv => by have := hVlt v hv; omega,
      fun e he => by have := hElt e he; omega,
      hdg.of_agree fun a ha1 ha2 => by dsimp only; exact hout₂ a (by omega),
      by omega, Or.inl hl1, heLlen, heLnd, heLmem,
      heLat.congr fun j hj1 hj2 => by
        dsimp only; rw [hout₂ j (by simp only [heLlen, MGraph.m] at hj2; omega)],
      by omega, Or.inl (by omega), hvlen, hvnd, fun v => hvmem v, hvLA, by omega,
      Or.inr (by simp only [auxVListBase, auxVIdxBase]; omega), by omega,
      fun i hi => by dsimp only; rw [hout₂ _ (by omega)]; exact hzG i hi⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨g0Ptr', dgGPtr', eListPtr', vListPtr', n0', m0', heq₃, -, hdgG, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, rfl, rfl⟩ := heq₃
  try dsimp only at hdgG hfr₃
  have hE3 : ∀ a, dgGPtr + dynGraphSize vCap eCap ≤ a → mem₃ a = mem₂ a := fun a ha =>
    hfr₃ a (Or.inr ha)
  have hauxT : ∀ a, auxPtr ≤ a → mem₃ a = mem₂ a := fun a ha => hE3 a (by omega)
  refine runs_ret_le (v := v₂) (by eval_expr) ⟨g0Ptr, vCap, eCap, k, auxPtr, dgGPtr, paramOut,
    vCap0, eCap0, vList, repList, rfl, ?_, ?_, ?_, hdgG, hvlen, hvnd, hvmem, ?_, fun i hi => ?_,
    fun v hv hv' => ?_, fun v hv => ?_, fun w' hw' hw'' => ?_, fun v hv => ?_, hc1, hc2, hrl,
    hrnd, hr0, ?_, hcomp, fun a ha1 ha2 ha3 => ?_⟩ ?_
  · dsimp only; rw [hauxT _ (by omega), hfr₂ _ (Or.inr (by omega))]; exact hD₁
  · dsimp only; rw [hauxT _ (by omega), hfr₂ _ (Or.inr (by omega))]; exact hL₁
  · dsimp only; rw [hauxT _ (by omega), hfr₂ _ (Or.inr (by omega))]; exact hT₁
  · exact hvLA.congr fun j hj1 hj2 => by
      dsimp only; exact hauxT j (by simp only [auxVListBase, auxVIdxBase] at hj1; omega)
  · dsimp only; rw [hauxT _ (by simp only [auxVIdxBase]; omega)]; exact hvI i hi
  · dsimp only; rw [hauxT _ (by simp only [auxVIdxBase]; omega)]; exact hvI0 v hv hv'
  · dsimp only
    rw [hauxT _ (by simp only [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase]; omega)]
    exact hiso v hv
  · dsimp only
    rw [hauxT _ (by simp only [auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase]; omega)]
    exact horig w' hw' hw''
  · dsimp only
    have hB : auxPtr ≤ auxVisBBase auxPtr vCap G₀.n + v := by
      simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase]; omega
    have hA : auxPtr ≤ auxVisABase auxPtr vCap G₀.n + v := by
      simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase]; omega
    rw [hauxT _ hA, hauxT _ hB]
    exact hvisB v hv
  · exact hrLA.congr fun j hj1 hj2 => by
      dsimp only
      exact hauxT j (by simp only [auxQBufBBase, auxQBufABase,
        auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
        auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase] at hj1; omega)
  · dsimp only
    rw [hfr₃ a ha1, hfr₂ a ha2, hfr₁ a ha3]; rfl
  · have hn₁ : mem₁ (g0Ptr + dgNOff) = G₀.n := by
      rw [hlow₁ _ (by simp only [dgNOff, dynGraphSize] at *; omega)]; exact hdg.2.2.2.2.2.1
    have hm₁ : mem₁ (g0Ptr + dgMOff) = G₀.E.card := by
      rw [hlow₁ _ (by simp only [dgMOff, dynGraphSize] at *; omega)]; exact hdg.2.2.2.2.2.2.1
    simp only [prepStageContract, initParamsContract, initScanContract, initCopyGContract,
      argsSize, Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load, List.getD_cons_zero,
      List.getD_cons_succ, hargs, hn₁, hm₁]
    omega

end

end MinCostFlow.LSF.Program
