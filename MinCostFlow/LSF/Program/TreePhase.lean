module

public import MinCostFlow.LSF.Program.TreeLsstStage
public import MinCostFlow.LSF.Program.LSimProc

/-!
# The tree phase of the initialization

`treePhaseProc` makes the copies of the edges of `G₀` (`treeCopiesProc`), computes the limb count
`L_sim` of the `[AN19]` simulation (`lsimProc`), and runs the `[AN19]` program on the copies
(`treeLsstProc`). It returns the heap pointer after the call.

The contract keeps the two inner contracts as they are. Its post names the memory `mem₁` after
the copies and says that the post of `treeCopiesContract` holds from `mem` to `mem₁` and the post
of `treeLsstContract` holds from `mem₁` to the end. Its pre asks for the pre of
`treeCopiesContract`, the pre of `lsimContract`, and the pre of `treeLsstContract` in every memory
that the post of `treeCopiesContract` allows. The caller proves the last part from the layout.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.WideWord

@[expose] public section

/-- The arguments of `treeCopiesProc` among the arguments of the phase. -/
def treePhaseCopyArgs (a : List ℕ) : List ℕ := a.take 20

/-- The arguments of `treeLsstProc`, for the number `M` of copies and the limb count `L_sim`. -/
def treePhaseLsstArgs (a : List ℕ) (M L_sim : ℕ) : List ℕ :=
  [a.getD 10 0, M, a.getD 13 0, a.getD 14 0, a.getD 15 0, a.getD 16 0, a.getD 4 0, L_sim,
    a.getD 20 0, a.getD 21 0, a.getD 22 0, a.getD 8 0, a.getD 17 0, a.getD 19 0,
    2 * a.getD 5 0 + a.getD 10 0, a.getD 11 0, a.getD 23 0, a.getD 24 0, a.getD 25 0]

/-- Args (`26`): the `20` arguments of `treeCopiesProc`
`[g0Ptr, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, vIdxBase, n0, eCap, multPtr,
copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, usedBridgePtr]`,
then `[outOrigPtr, outBridgePtr, outHdrPtr, tOrigPtr, tTailPtr, tHeadPtr]`. -/
def treePhaseProc (bCopies bLsim bLsst : ℕ) : Stmt :=
  .call 26 bCopies ((List.range 20).map Expr.reg) ;;
  .call 27 bLsim [.bin .mul (.const 2) (.reg 5), .reg 4] ;;
  .call 28 bLsst [.reg 10, .reg 26, .reg 13, .reg 14, .reg 15, .reg 16, .reg 4, .reg 27, .reg 20,
    .reg 21, .reg 22, .reg 8, .reg 17, .reg 19,
    .bin .add (.bin .mul (.const 2) (.reg 5)) (.reg 10), .reg 11, .reg 23, .reg 24, .reg 25] ;;
  .ret (.reg 28)

lemma treePhaseProc_noRand (bCopies bLsim bLsst : ℕ) :
    (treePhaseProc bCopies bLsim bLsst).NoRand := by
  simp [treePhaseProc, Stmt.NoRand]

/-- The number of copies. -/
noncomputable def treePhaseM (G₀ : MGraph) (v : ℕ → ℝ) (vList eList : List ℕ) : ℕ :=
  (copyIndexedGraph G₀ vList eList (treeMult G₀ v eList)).m

/-- The contract of `treePhaseProc`. -/
noncomputable def treePhaseContract (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ)
    (G₀ : MGraph) (v ℓ₀ : ℕ → ℝ) (P_fp : ℕ) (vList eList : List ℕ) : Contract where
  pre args mem := args.length = 26 ∧
    (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList).pre (treePhaseCopyArgs args) mem ∧
    (lsimContract w c_AN h).pre [2 * args.getD 5 0, args.getD 4 0] mem ∧
    2 * args.getD 5 0 + args.getD 10 0 < 2 ^ w ∧
    ∀ mem₁, (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList).post (treePhaseCopyArgs args) mem
      (treePhaseM G₀ v vList eList) mem₁ →
      (treeLsstContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).pre
        (treePhaseLsstArgs args (treePhaseM G₀ v vList eList)
          (lsstLSimMin c_AN 0 (2 * args.getD 5 0) (args.getD 4 0) h)) mem₁
  post args mem ret mem' := ∃ mem₁,
    (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList).post (treePhaseCopyArgs args) mem
      (treePhaseM G₀ v vList eList) mem₁ ∧
    (treeLsstContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
      (treePhaseLsstArgs args (treePhaseM G₀ v vList eList)
        (lsstLSimMin c_AN 0 (2 * args.getD 5 0) (args.getD 4 0) h)) mem₁ ret mem'
  cost args mem :=
    (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList).cost (treePhaseCopyArgs args) mem +
    (lsimContract w c_AN h).cost [2 * args.getD 5 0, args.getD 4 0] mem +
    (treeLsstContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).cost
      (treePhaseLsstArgs args (treePhaseM G₀ v vList eList)
        (lsstLSimMin c_AN 0 (2 * args.getD 5 0) (args.getD 4 0) h)) mem + 100

/-- The registers hold the values of a list of register expressions. -/
lemma evalArgs_map_reg' {w : ℕ} {st : State} (l : List ℕ) :
    evalArgs w st (l.map Expr.reg) = some (l.map st.regs) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [evalArgs, Expr.eval, ih]

lemma argsSize_map_reg' (l : List ℕ) : argsSize (l.map Expr.reg) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [argsSize, Expr.size, ih]; omega

theorem treePhase_meetsContract {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {w h : ℕ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {vList eList : List ℕ} {p : Program} {b bCopies bLsim bLsst : ℕ}
    (hp : p.procs[b]? = some (treePhaseProc bCopies bLsim bLsst))
    (hCopies : MeetsContract w p bCopies (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList))
    (hLsim : MeetsContract w p bLsim (lsimContract w c_AN h))
    (hLsst : MeetsContract w p bLsst
      (treeLsstContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList)) :
    MeetsContract w p b (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨hlen, hpC, hpL, hub, hpS⟩ := hpre
  have hR0 : ∀ i < 26, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    simp only [startState]
  have hwa : ∀ i < 26, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hmap : ∀ (f : ℕ → ℕ), (∀ i < 20, f i = args.getD i 0) →
      (List.range 20).map f = treePhaseCopyArgs args := by
    intro f hf
    apply List.ext_getElem
    · simp [treePhaseCopyArgs, hlen]
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, treePhaseCopyArgs, List.getElem_take]
    rw [hf i h1, List.getD_eq_getElem _ _ (by omega)]
  refine runs_start_le ?_
  unfold treePhaseProc
  -- 1. the copies
  refine runs_seq_call_le (vs := treePhaseCopyArgs args) hCopies
    (by rw [evalArgs_map_reg', hmap _ (fun i hi => hR0 i (by omega))])
    (fun x hx => by
      simp only [treePhaseCopyArgs] at hx
      exact hwords x (List.mem_of_mem_take hx))
    hpC ?_
  intro v₁ mem₁ pos₁ hpost₁
  have hM : v₁ = treePhaseM G₀ v vList eList := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hret, -⟩ := hpost₁
    exact hret
  subst hM
  -- 2. the limb count
  have hst : ∀ i < 26, Function.update (startState args mem pos).regs 26
      (treePhaseM G₀ v vList eList) i = args.getD i 0 := fun i hi => by
    rw [Function.update_of_ne (by omega)]; exact hR0 i hi
  refine runs_seq_call_le (vs := [2 * args.getD 5 0, args.getD 4 0]) hLsim
    (evalArgs_cons (by
      have h2w : 2 < 2 ^ w := by
        obtain ⟨m, L, -, -, hw16, -⟩ := hpL
        omega
      have h5w : 2 * args.getD 5 0 < 2 ^ w := by omega
      simp only [Expr.eval, BinOp.eval, hst 5 (by omega), h2w, h5w, if_true])
      (evalArgs_cons (by simp only [Expr.eval, hst 4 (by omega)]) (evalArgs_nil _ _)))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega
      · exact hwa 4 (by omega))
    (by
      obtain ⟨m, L, hml, rest⟩ := hpL
      exact ⟨m, L, hml, rest⟩) ?_
  rintro v₂ mem₂ pos₂ ⟨m', L', heq₂, hmem₂, hv₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl⟩ := heq₂
  try dsimp only at hmem₂
  subst mem₂
  have hv₂' := hv₂ 0
  subst hv₂'
  -- 3. the `[AN19]` call
  have hst2 : ∀ i < 26, Function.update (Function.update (startState args mem pos).regs 26
      (treePhaseM G₀ v vList eList)) 27 (lsstLSimMin c_AN 0 (2 * args.getD 5 0) (args.getD 4 0) h)
      i = args.getD i 0 := fun i hi => by
    rw [Function.update_of_ne (by omega)]; exact hst i hi
  have hpS' := hpS mem₁ hpost₁
  set M := treePhaseM G₀ v vList eList with hMdef
  set L_sim := lsstLSimMin c_AN 0 (2 * args.getD 5 0) (args.getD 4 0) h with hLdef
  have hMle : M ≤ 2 * args.getD 5 0 := by
    obtain ⟨g0Ptr', eListPtr', lenArr', wtArr', L_in', m0', K_w', qNatPtr', lsstHeap', vIdxBase',
      n0', eCap', multPtr', copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', copyOrigIdxPtr',
      copySubIdxPtr', usedBridgePtr', heqA, -, hle, -⟩ := hpost₁
    have h5 := congrArg (fun l : List ℕ => l.getD 5 0) heqA
    simp only [treePhaseCopyArgs, List.getD_cons_succ, List.getD_cons_zero] at h5
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
      ← List.getD_eq_getElem?_getD] at h5
    rw [h5]; exact hle
  have hLsimW : L_sim < 2 ^ w := by
    obtain ⟨m, L, hml, -, -, -, -, hK, -, hW⟩ := hpL
    simp only [List.cons.injEq, and_true] at hml
    obtain ⟨rfl, rfl⟩ := hml
    simp only [hLdef, lsstLSimMin]
    exact max_lt hK hW
  have h2w : 2 < 2 ^ w := by
    obtain ⟨m, L, -, -, hw16, -⟩ := hpL
    omega
  have h5w : 2 * args.getD 5 0 < 2 ^ w := by omega
  have hLw : ∀ x ∈ treePhaseLsstArgs args M L_sim, x < 2 ^ w := by
    intro x hx
    simp only [treePhaseLsstArgs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwa 10 (by omega)
    · omega
    · exact hwa 13 (by omega)
    · exact hwa 14 (by omega)
    · exact hwa 15 (by omega)
    · exact hwa 16 (by omega)
    · exact hwa 4 (by omega)
    · exact hLsimW
    · exact hwa 20 (by omega)
    · exact hwa 21 (by omega)
    · exact hwa 22 (by omega)
    · exact hwa 8 (by omega)
    · exact hwa 17 (by omega)
    · exact hwa 19 (by omega)
    · exact hub
    · exact hwa 11 (by omega)
    · exact hwa 23 (by omega)
    · exact hwa 24 (by omega)
    · exact hwa 25 (by omega)
  have e26 : Function.update (Function.update (startState args mem pos).regs 26 M) 27 L_sim 26 =
      M := by rw [Function.update_of_ne (by omega), Function.update_self]
  have e27 : Function.update (Function.update (startState args mem pos).regs 26 M) 27 L_sim 27 =
      L_sim := Function.update_self _ _ _
  refine runs_seq_call_le (vs := treePhaseLsstArgs args M L_sim) hLsst ?_ hLw hpS' ?_
  · simp only [evalArgs, Expr.eval, BinOp.eval, e26, e27, hst2 10 (by omega),
      hst2 13 (by omega), hst2 14 (by omega), hst2 15 (by omega), hst2 16 (by omega),
      hst2 4 (by omega), hst2 20 (by omega), hst2 21 (by omega), hst2 22 (by omega),
      hst2 8 (by omega), hst2 17 (by omega), hst2 19 (by omega), hst2 5 (by omega),
      hst2 11 (by omega), hst2 23 (by omega), hst2 24 (by omega), hst2 25 (by omega),
      h2w, h5w, hub, if_true, treePhaseLsstArgs]
  · intro v₃ mem₃ pos₃ hpost₃
    refine runs_ret_le (by eval_expr) ⟨mem₁, hpost₁, ?_⟩ ?_
    · exact hpost₃
    · simp only [treePhaseContract, treeLsstContract, lsimContract, argsSize_map_reg', argsSize,
        Expr.size, List.length_range, startState, e26, e27, treePhaseLsstArgs,
        List.getD_cons_succ, List.getD_cons_zero]
      simp only [← hMdef, ← hLdef]
      omega

end

end MinCostFlow.LSF.Program
