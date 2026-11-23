module

public import MinCostFlow.LSF.Program.TBlockAssemble
public import MinCostFlow.LSF.Program.T0Index
public import MinCostFlow.LSF.Program.TreeStageMath

/-!
# The `T` block, in one procedure

`tStageProc` writes the `T` block of the start state, where `G = G₀` and `T_cur = T₀`:
1. `memCopyStmt` copies the edge IDs of `T₀` from the scratch arrays of `t0EdgesProc` into the
   block (the arrays lie above the block, and `t0EdgesProc` asks its output to lie above its
   input, so it cannot write into the block itself);
2. `tBlockFillProc` writes the header, the frozen ends and the table `idxOfEdge`;
3. `tTrackProc` writes the tracker graph.

The order `π` is already in the block: `congOrderProc` writes its ranks there. The post of
`tStage_meetsContract` is `TBlockAt`, with `π` read from the block (`tStagePi`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

@[expose] public section

/-- The edge IDs of `T₀`, read from the scratch array at `src`. -/
def tStageList (mem : ℕ → ℕ) (src tM : ℕ) : List ℕ := (List.range tM).map fun i => mem (src + i)

/-- The order `π` read from the block: edge `f` gets the rank stored at its index. -/
def tStagePi (mem : ℕ → ℕ) (tPtr vCap tM : ℕ) (L : List ℕ) (f : ℕ) : ℕ :=
  mem (tPiBase tPtr vCap tM + L.idxOf f)

/-- Args: `[tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr, tHeadPtr, n0, nOrig, tOrigDst,
dgTPtr]`, where `tOrigDst = tOrigIdBase tPtr vCap tM` and `dgTPtr = tDgTPtr tPtr`. -/
def tStageProc (bCopy bFill bTrack : ℕ) : Stmt :=
  .call 12 bCopy [.reg 10, .reg 5, .reg 3] ;;
  .call 12 bFill [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7] ;;
  .call 12 bTrack [.reg 11, .reg 1, .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1), .reg 8,
    .reg 4, .reg 9, .reg 6, .reg 7] ;;
  .ret (.const 0)

lemma tStageProc_noRand (bCopy bFill bTrack : ℕ) : (tStageProc bCopy bFill bTrack).NoRand := by
  simp [tStageProc, Stmt.NoRand]

/-- The contract of `tStageProc`. The vertex list lies above the block, and the scratch arrays
of `t0EdgesProc` above the vertex list. -/
def tStageContract (w : ℕ) (G₀ T₀ : MGraph) (vList : List ℕ) : Contract where
  pre args mem := ∃ (tPtr vCap eCap tM vListPtr tOrigSrc tTailPtr tHeadPtr n0 nOrig : ℕ),
    args = [tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr, tHeadPtr, n0, nOrig,
      tOrigIdBase tPtr vCap tM, tDgTPtr tPtr] ∧
    16 ≤ 2 ^ w ∧
    T0IndexArrays T₀ vList tM (fun i => mem (tOrigSrc + i)) (fun i => mem (tTailPtr + i))
      (fun i => mem (tHeadPtr + i)) ∧
    vList.length = n0 ∧ ListAt mem vListPtr vList ∧ (∀ u ∈ vList, u < vCap) ∧
    (∀ u, u ∈ G₀.V ↔ u ∈ vList) ∧
    nOrig ≤ tM ∧ (∀ i < tM, (mem (tOrigSrc + i) ∈ G₀.E ↔ i < nOrig)) ∧
    (∀ e ∈ T₀.E, e ∈ G₀.E → T₀.tail e = G₀.tail e ∧ T₀.head e = G₀.head e) ∧
    (∀ i < dynGraphSize vCap (2 * tM + 1), mem (tDgTPtr tPtr + i) = 0) ∧
    (∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0) ∧
    tPtr + tBlockSize vCap eCap tM ≤ vListPtr ∧ vListPtr + n0 ≤ tOrigSrc ∧
    tOrigSrc + tM ≤ tTailPtr ∧ tTailPtr + tM ≤ tHeadPtr ∧ tHeadPtr + tM < 2 ^ w
  post args mem ret mem' := ∃ (tPtr vCap eCap tM vListPtr tOrigSrc tTailPtr tHeadPtr n0
      nOrig : ℕ),
    args = [tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr, tHeadPtr, n0, nOrig,
      tOrigIdBase tPtr vCap tM, tDgTPtr tPtr] ∧ ret = 0 ∧
    TBlockAt mem' tPtr vCap eCap tM G₀ T₀ T₀
      (tStagePi mem' tPtr vCap tM (tStageList mem tOrigSrc tM)) (tStageList mem tOrigSrc tM) ∧
    (∀ i < tM, mem' (tPiBase tPtr vCap tM + i) = mem (tPiBase tPtr vCap tM + i)) ∧
    ∀ a, a < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ a → mem' a = mem a
  cost args _ := 100 * args.getD 3 0 + 150 * args.getD 8 0 +
    1000 * args.getD 9 0 + 400

theorem tStage_meetsContract {w : ℕ} {G₀ T₀ : MGraph} {vList : List ℕ} {p : Program}
    {b bCopy bFill bTrack : ℕ}
    (hp : p.procs[b]? = some (tStageProc bCopy bFill bTrack))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (tBlockFillContract w))
    (hTrack : MeetsContract w p bTrack (tTrackContract w)) :
    MeetsContract w p b (tStageContract w G₀ T₀ vList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr, tHeadPtr, n0, nOrig, rfl, hw16, hA,
    hvLen, hvAt, hvCap, hV, hnO, hG, hTG, hz, hzIdx, hl1, hl2, hl3, hl4, hl5⟩ := hpre
  set args := [tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr, tHeadPtr, n0, nOrig,
      tOrigIdBase tPtr vCap tM, tDgTPtr tPtr] with hargs
  have hR0 : ∀ i < 12, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 12, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  -- the places in the block
  have hb1 : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) = tOrigIdBase tPtr vCap tM := rfl
  have hb2 : tOrigIdBase tPtr vCap tM + tM = tPiBase tPtr vCap tM := rfl
  have hb3 : tPiBase tPtr vCap tM + tM = tFrozenTailBase tPtr vCap tM := rfl
  have hb4 : tFrozenTailBase tPtr vCap tM + tM = tFrozenHeadBase tPtr vCap tM := rfl
  have hb5 : tFrozenHeadBase tPtr vCap tM + tM = tIdxOfEdgeBase tPtr vCap tM := rfl
  have hb6 : tIdxOfEdgeBase tPtr vCap tM + eCap = tSplitScratchBase tPtr vCap eCap tM := rfl
  have hb7 : tSplitScratchBase tPtr vCap eCap tM + (4 + 2 * tM) = tPtr + tBlockSize vCap eCap tM := by
    simp only [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase,
      tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hb0 : tPtr + tHdrSize = tDgTPtr tPtr := rfl
  have hh8 : tHdrSize = 8 := rfl
  set L := tStageList mem tOrigSrc tM with hLdef
  have hLlen : L.length = tM := by simp [hLdef, tStageList]
  have hLget : ∀ i (hi : i < L.length), L[i] = mem (tOrigSrc + i) := fun i hi => by
    simp [hLdef, tStageList]
  have hLnd : L.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [List.get_eq_getElem, hLget] at hij
    exact Fin.ext (hA.fid_inj i (by omega) j (by omega) hij)
  refine runs_start_le ?_
  unfold tStageProc
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
  -- 1. the edge IDs
  refine runs_seq_call_le (vs := [tOrigIdBase tPtr vCap tM, tOrigSrc, tM]) hCopy
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwa 10 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 3 (by omega))
    ⟨tOrigIdBase tPtr vCap tM, tOrigSrc, tM, rfl, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨dst', src', len', heq₁, -, hcp₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hcp₁ hfr₁
  have hlow₁ : ∀ a, (a < tOrigIdBase tPtr vCap tM ∨ tPiBase tPtr vCap tM ≤ a) → mem₁ a = mem a :=
    fun a ha => hfr₁ a (by omega)
  have hO₁ : ∀ i < tM, mem₁ (tOrigIdBase tPtr vCap tM + i) = mem (tOrigSrc + i) := hcp₁
  -- 2. header, frozen ends, `idxOfEdge`
  refine runs_seq_call_le (vs := [tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr]) hFill
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 7 (by omega))
    ⟨tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr, n0, rfl, hw16, hl1, by omega, by omega,
      by omega, by omega, by omega,
      fun i hi => by
        dsimp only
        rw [hlow₁ _ (by omega), hlow₁ _ (by omega)]
        exact ⟨by rw [← hvLen]; exact hA.tl_lt i hi, by rw [← hvLen]; exact hA.hd_lt i hi⟩,
      fun i hi j hj hij => by
        dsimp only at hij
        rw [hO₁ i hi, hO₁ j hj] at hij
        exact hA.fid_inj i hi j hj hij,
      fun e he => by
        dsimp only
        rw [hlow₁ _ (by omega)]
        exact hzIdx e he⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨tPtr', vCap', eCap', tM', vListPtr', tTailPtr', tHeadPtr', heq₂, -, hH₂,
    hFr₂, hI1₂, hI0₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hFr₂ hI1₂ hI0₂ hfr₂
  have hmid₂ : ∀ a, tDgTPtr tPtr ≤ a → a < tFrozenTailBase tPtr vCap tM → mem₂ a = mem₁ a :=
    fun a ha1 ha2 => hfr₂ a (Or.inr (Or.inl ⟨by omega, ha2⟩))
  have hout₂ : ∀ a, a < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ a → mem₂ a = mem₁ a :=
    fun a ha => hfr₂ a (by omega)
  have hz₂ : ∀ i < dynGraphSize vCap (2 * tM + 1), mem₂ (tDgTPtr tPtr + i) = 0 := fun i hi => by
    rw [hmid₂ _ (by omega) (by omega), hlow₁ _ (by omega)]; exact hz i hi
  have hvAt₂ : ∀ i < n0, mem₂ (vListPtr + i) = mem (vListPtr + i) := fun i hi => by
    rw [hout₂ _ (by omega), hlow₁ _ (by omega)]
  have htt₂ : ∀ i < tM, mem₂ (tTailPtr + i) = mem (tTailPtr + i) ∧
      mem₂ (tHeadPtr + i) = mem (tHeadPtr + i) := fun i hi =>
    ⟨by rw [hout₂ _ (by omega), hlow₁ _ (by omega)], by rw [hout₂ _ (by omega), hlow₁ _ (by omega)]⟩
  -- 3. the tracker graph
  have h2t : 2 * tM + 1 < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [tDgTPtr tPtr, vCap, 2 * tM + 1, n0, vListPtr, nOrig, tTailPtr,
      tHeadPtr]) hTrack
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 11 (by omega)
      · exact hwa 1 (by omega)
      · exact h2t
      · exact hwa 8 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 7 (by omega))
    ⟨tDgTPtr tPtr, vCap, 2 * tM + 1, n0, vListPtr, nOrig, tTailPtr, tHeadPtr, rfl, hw16,
      by omega, by omega, hz₂, Or.inr (by omega), by omega, Or.inr (by omega), by omega,
      Or.inr (by omega), by omega,
      fun i hi => by dsimp only; rw [hvAt₂ i hi, hvAt i (by omega)]; exact hvCap _ (List.getElem_mem _),
      fun i hi => by
        dsimp only
        rw [(htt₂ i (by omega)).1, (htt₂ i (by omega)).2]
        exact ⟨by rw [← hvLen]; exact hA.tl_lt i (by omega),
          by rw [← hvLen]; exact hA.hd_lt i (by omega)⟩⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨dgTPtr', vCap', eCapT', n0', vListPtr', nOrig', tTailPtr', tHeadPtr', heq₃,
    -, hdg₃, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hdg₃ hfr₃
  have hE3 : ∀ a, (a < tDgTPtr tPtr ∨ tOrigIdBase tPtr vCap tM ≤ a) → mem₃ a = mem₂ a :=
    fun a ha => hfr₃ a (by omega)
  -- the facts in the last memory
  have hO₃ : ∀ i < tM, mem₃ (tOrigIdBase tPtr vCap tM + i) = mem (tOrigSrc + i) := fun i hi => by
    rw [hE3 _ (by omega), hmid₂ _ (by omega) (by omega), hO₁ i hi]
  have hvs : ∀ x < n0, mem (vListPtr + x) = vList.getD x 0 := fun x hx => by
    rw [hvAt x (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hVeq : (memSlice mem₂ vListPtr n0).toFinset = G₀.V := by
    ext u
    rw [List.mem_toFinset, hV]
    simp only [memSlice, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hvAt₂ i hi, hvAt i (by omega)]; exact List.getElem_mem _
    · intro hu
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      exact ⟨i, by omega, by rw [hvAt₂ i (by omega), hvAt i hi]⟩
  rw [hVeq] at hdg₃
  have hTB : TBlockAt mem₃ tPtr vCap eCap tM G₀ T₀ T₀
      (tStagePi mem₃ tPtr vCap tM L) L := by
    refine tBlockAt_init (nOrig := nOrig) ?_ hLlen hLnd ?_ ?_ ?_ ?_ ?_ hdg₃ ?_ ?_ hnO ?_ hTG
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hH₂
      have hk : ∀ k < 8, mem₃ (tPtr + k) = mem₂ (tPtr + k) := fun k hk => hE3 _ (by omega)
      exact ⟨by rw [hk _ (by decide)]; exact h0, by rw [hk _ (by decide)]; exact h1,
        by rw [hk _ (by decide)]; exact h2, by rw [hk _ (by decide)]; exact h3,
        by rw [hk _ (by decide)]; exact h4, by rw [hk _ (by decide)]; exact h5,
        by rw [hk _ (by decide)]; exact h6, by rw [hk _ (by decide)]; exact h7⟩
    · intro f
      constructor
      · intro hf
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
        rw [hLget]; exact hA.fid_mem i (by omega)
      · intro hf
        obtain ⟨i, hi, rfl⟩ := hA.fid_cover f hf
        rw [← hLget i (by omega)]; exact List.getElem_mem _
    · intro i hi
      rw [hO₃ i (by omega), hLget]
    · intro i hi
      simp only [List.getElem_map, tStagePi]
      rw [List.length_map] at hi
      rw [idxOf_getElem_of_nodup hLnd hi]
    · intro i hi hlt
      rw [hO₃ i hi] at hlt ⊢
      rw [hE3 _ (by omega)]
      have := hI1₂ i hi (by rw [hO₁ i hi]; exact hlt)
      rwa [hO₁ i hi] at this
    · intro e he hne
      rw [hE3 _ (by omega)]
      exact hI0₂ e he fun i hi heq => hne i hi (by
        rw [hO₃ i hi]; rwa [hO₁ i hi] at heq)
    · intro i hi hi'
      have hiL : i < tM := by omega
      simp only [trackEnd, show (2 * i) % 2 = 0 by omega, show (2 * i + 1) % 2 = 1 by omega,
        ite_true, show ¬ (1 = 0) from by omega, ite_false, show 2 * i / 2 = i by omega,
        show (2 * i + 1) / 2 = i by omega]
      rw [(htt₂ i hiL).1, (htt₂ i hiL).2, hvAt₂ _ (by rw [← hvLen]; exact hA.tl_lt i hiL),
        hvAt₂ _ (by rw [← hvLen]; exact hA.hd_lt i hiL),
        hvs _ (by rw [← hvLen]; exact hA.tl_lt i hiL), hvs _ (by rw [← hvLen]; exact hA.hd_lt i hiL),
        hLget, ← hA.tail_eq i hiL, ← hA.head_eq i hiL]
      exact ⟨rfl, rfl⟩
    · intro i hi
      have hiL : i < tM := by omega
      rw [hE3 _ (by omega), hE3 _ (by omega), (hFr₂ i hiL).1, (hFr₂ i hiL).2,
        hlow₁ _ (by omega), hlow₁ _ (by omega), hlow₁ _ (by omega), hlow₁ _ (by omega),
        hvs _ (by rw [← hvLen]; exact hA.tl_lt i hiL), hvs _ (by rw [← hvLen]; exact hA.hd_lt i hiL),
        hLget, ← hA.tail_eq i hiL, ← hA.head_eq i hiL]
      exact ⟨rfl, rfl⟩
    · intro i hi
      rw [hLget]; exact hG i (by omega)
  refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, vCap, eCap, tM, vListPtr, tOrigSrc, tTailPtr,
    tHeadPtr, n0, nOrig, rfl, rfl, hTB, fun i hi => ?_, fun a ha => ?_⟩ ?_
  · try dsimp only
    rw [hE3 _ (by omega), hmid₂ _ (by omega) (by omega), hlow₁ _ (by omega)]
  · try dsimp only
    rw [hE3 _ (by omega), hout₂ a ha, hlow₁ _ (by omega)]
  · simp only [tStageContract, memCopyContract, tBlockFillContract, tTrackContract, argsSize,
      Expr.size_const, Expr.size_reg, Expr.size_bin, List.sum_cons, List.sum_nil, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ, hargs]
    omega

end

end MinCostFlow.LSF.Program
