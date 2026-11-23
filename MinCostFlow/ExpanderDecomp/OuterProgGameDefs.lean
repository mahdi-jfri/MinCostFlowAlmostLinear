module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterGame
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.OuterProgParams
public import MinCostFlow.ExpanderDecomp.OuterProgMatching
public import MinCostFlow.ExpanderDecomp.OuterProgGameBase
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-Node Outer Cut-Matching Game Word-RAM Procedure (`OuterProgGame`)

Implements and verifies the deterministic (`NoRand`) Word-RAM procedure `outerGameProc idx` for
the outer cut-matching game, parameterized on the existential
`outerCoreContract` and `outerRouterContract`:

- `gameRoundBodyStmt idx`: one round of the outer cut-matching game — invokes `bCore`, branches on
  `.expander S` (`bInj`) vs `.cut U` (`bPad`), invokes `bRoute` on the port graph `Hhat` at
  `Δ = 10`, returns immediately on a router cut, otherwise invokes `bFake`, appends `M ++ F_k` to
  `W` and `F_k` to `F`, returns on an expander-injection round, or decrements fuel and continues.
- `outerGameProc idx`: loads parameters, computes `q = coreLevel M r (2 * e)`, allocates and
  initializes the witness/fake/scratch buffers on the zero-heap, and executes the bounded loop.
- `outerGameContract`, `outerGameProc_spec`: proves the existential outcome specification
  `OuterGameOutcomeSpec ParamConfig.default M r e Hhat res`, zero-heap space bound
  `outerGameSpace`, frame outside `[outResAddr, outResAddr + 4)` below `h`, and step count
  `≤ outerGameStepBound C_core C_rt r e (outerGameMaxCost ParamConfig.default M r routeC e)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Loop Body, Procedure, and Contract -/

/-- Write the cut result descriptor `[0, kU, routeOutAddr + 2]` at `outResAddr` and return `hCur`. -/
def gameWriteCutRetStmt : Stmt :=
  .assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
  .store (.reg 3) (.const 0) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 29) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 20) (.const 2)) ;;
  .ret (.reg 26)

/-- Write the witness result descriptor `[1, wAddr, fLen, fAddr]` at `outResAddr` and return `hCur`. -/
def gameWriteWitRetStmt : Stmt :=
  .store (.reg 3) (.const 1) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 16) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 25) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 17) ;;
  .ret (.reg 26)

/-- One round of `outerGameProc`: core call, bisection/injection pair build, router call, and
either cut return, fake-edge completion + witness return, or fuel decrement. -/
def gameRoundBodyStmt (idx : OuterGameIndices) : Stmt :=
  .call 26 idx.bCore [.reg 14, .reg 16, .reg 5, .reg 6, .reg 18, .reg 26] ;;
  (.assign 35 (.load (.reg 18)) ;;
   .assign 29 (.load (.bin .add (.reg 18) (.const 1))) ;;
   .assign 30 (.bin .add (.reg 18) (.const 2))) ;;
  .cond (.reg 35)
    (.call 26 idx.bInj [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26])
    (.call 26 idx.bPad [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26]) ;;
  .call 26 idx.bRoute [.reg 1, .reg 15, .reg 19, .const 10, .reg 7, .reg 9, .reg 13, .reg 20, .reg 26] ;;
  .assign 28 (.load (.reg 20)) ;;
  .cond (.reg 28)
    gameWriteCutRetStmt
    ((.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
      .assign 30 (.bin .add (.reg 20) (.const 2))) ;;
     .call 26 idx.bFake [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26] ;;
     gameAppendMatchedStmt ;;
     .cond (.reg 35)
       gameWriteWitRetStmt
       (.assign 27 (.bin .sub (.reg 27) (.const 1))))

/-- Outer cut-matching game procedure.
Args: `[e, pgAddr, paramAddr, outResAddr, h]`. -/
def outerGameProc (idx : OuterGameIndices) : Stmt :=
  gameLoadParamsStmt ;;
  .call 14 idx.bCoreLevel [.reg 8, .reg 12] ;;
  gameAllocBufsStmt ;;
  gameInitBufsStmt ;;
  .loop (.bin .lt (.const 0) (.reg 27)) (gameRoundBodyStmt idx) ;;
  (.store (.reg 3) (.const 0) ;;
   .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
   .store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 20) (.const 2)) ;;
   .ret (.reg 26))

/-- Bundled `MeetsContract` hypotheses for the six subprocedures called by `outerGameProc`. -/
structure OuterGameSubprocs (M r w : ℕ) (p : Program)
    (idx : OuterGameIndices)
    (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (C_core C_rt C_sp_core C_sp_rt C_sp routeC : ℕ) : Prop where
  hcoreCost : CoreCostBounded ParamConfig.default M r coreCost
  hroute : IsMatchingPlayer route routeCost
  hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
    X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
    1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
    ValidTerminalPairs X' pairs →
    routeCost G' X' pairs Δ L b z' ≤
      routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L + 1)
  hsp_core : C_sp_core ≤ C_sp
  hsp_rt : C_sp_rt ≤ C_sp
  hCoreLevel : MeetsContract w p idx.bCoreLevel (coreLevelContract w)
  hCoreProg : MeetsContract w p idx.bCore (coreAdapterContract M r coreCost C_core C_sp_core w)
  hRouteProg : MeetsContract w p idx.bRoute (outerRouterContract route routeCost C_rt C_sp_rt w)
  hPad : MeetsContract w p idx.bPad (padToBisectionContract w)
  hInj : MeetsContract w p idx.bInj (buildInjPairContract w)
  hFake : MeetsContract w p idx.bFake (fakeCompletionContract w)

/-- Contract for `outerGameProc`: runs the outer cut-matching game on `Hhat` at `ParamConfig.default`,
writes some `res` satisfying `OuterGameOutcomeSpec ParamConfig.default M r e Hhat res` at
`outResAddr` (`OuterGameOutAt`), returns the updated zero-heap cursor
`h' ≤ h + outerGameSpace C_sp M r e (outerGameMaxCost ParamConfig.default M r routeC e)`,
preserves memory `< h` outside `[outResAddr, outResAddr + 4)`, and runs in at most
`outerGameStepBound C_core C_rt r e (outerGameMaxCost ParamConfig.default M r routeC e)` steps. -/
noncomputable def outerGameContract (M r : ℕ)
    (C_core C_rt C_sp routeC w : ℕ) : Contract where
  pre args mem :=
    ∃ (n e pgAddr paramAddr outResAddr h : ℕ) (Hhat : Graph),
      args = [e, pgAddr, paramAddr, outResAddr, h] ∧
      GraphAt mem pgAddr Hhat ∧
      Hhat.n = 2 * e ∧
      Hhat.m ≤ 10 * e ∧
      Hhat.IsValid ∧
      Hhat.IsLoopless ∧
      (∀ v, Hhat.deg v ≤ 10) ∧
      OuterParamBlockAt mem paramAddr ParamConfig.default n M r ∧
      1 ≤ e ∧
      1 ≤ r ∧ r ≤ ell M ∧
      2 ≤ NOf M r ∧
      2 * e ≤ (NOf M r) ^ r ∧
      2 * e < 2 ^ LParam M ∧
      0 < DOut ParamConfig.default M r ∧
      ZeroFrom mem h ∧
      pgAddr + 2 + 2 * Hhat.m ≤ h ∧
      paramAddr + 12 ≤ h ∧
      outResAddr + 4 ≤ h ∧
      DisjointRange outResAddr 4 pgAddr (2 + 2 * Hhat.m) ∧
      DisjointRange outResAddr 4 paramAddr 12 ∧
      let loopCost := outerGameMaxCost ParamConfig.default M r routeC e
      h + outerGameSpace C_sp M r e loopCost < 2 ^ w ∧
      NOf M r * (2 * e) + 16 < 2 ^ w ∧
      bOut ParamConfig.default M < 2 ^ w ∧
      M < 2 ^ w ∧
      r < 2 ^ w ∧
      16 < 2 ^ w
  post args mem v mem' :=
    let e := args.getD 0 0
    let pgAddr := args.getD 1 0
    let outResAddr := args.getD 3 0
    let h := args.getD 4 0
    let Hhat := readGraph mem pgAddr
    let loopCost := outerGameMaxCost ParamConfig.default M r routeC e
    (∃ res : OuterGameResult,
      OuterGameOutAt mem' outResAddr h v e res ∧
      OuterGameOutcomeSpec ParamConfig.default M r e Hhat res) ∧
    h ≤ v ∧
    v ≤ h + outerGameSpace C_sp M r e loopCost ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outResAddr ∨ outResAddr + 4 ≤ a) → mem' a = mem a)
  cost args _ :=
    let e := args.getD 0 0
    let loopCost := outerGameMaxCost ParamConfig.default M r routeC e
    outerGameStepBound C_core C_rt r e loopCost

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma outerGameProc_noRand (idx : OuterGameIndices) : (outerGameProc idx).NoRand := by
  simp [outerGameProc, gameLoadParamsStmt_noRand, gameAllocBufsStmt_noRand,
    gameInitBufsStmt_noRand, gameRoundBodyStmt, gameWriteCutRetStmt, gameWriteWitRetStmt,
    gameAppendMatchedStmt_noRand, Stmt.NoRand]

/-! ## 2. Pure Model Helpers -/

lemma two_le_bOut' (cfg : ParamConfig) (M : ℕ) : 2 ≤ bOut cfg M := by
  unfold bOut
  have hk := cfg.kappa_pos
  have hL := four_le_LParam M
  have hE := cfg.hE
  have h1 : 16 * 4 * 5 * 1 ≤ 16 * cfg.kappa * (LParam M + 1) * cfg.E :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hk) (by omega)) hE
  omega

lemma validTerminalPairs_singleton' {X A B : Finset ℕ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hdisj : Disjoint A B) (hcard : A.card ≤ B.card) :
    ValidTerminalPairs X [(A, B)] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp
    exact ⟨hA, hB, hcard⟩
  · simp [hdisj]

private lemma matchings_flatten_eq_getD {matchings : List (List (ℕ × ℕ))}
    (hlen : matchings.length = 1) :
    matchings.flatten = matchings.getD 0 [] := by
  cases matchings with
  | nil => simp at hlen
  | cons E rest =>
    cases rest with
    | nil => simp
    | cons _ _ => simp at hlen

lemma singlePair_matched_props {Hhat : Graph} {A B : Finset ℕ} {cfg : ParamConfig} {M z : ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut cfg M) z matchings emb) :
    let E := matchings.getD 0 []
    matchings.flatten = E ∧ IsPartialMatching A B E ∧ E.length ≤ A.card := by
  obtain ⟨hlen, hpair, _, _, _, _⟩ := h
  have hflat : matchings.flatten = matchings.getD 0 [] := matchings_flatten_eq_getD hlen
  have h0 := hpair 0 (by simp)
  simp only [List.getElem_cons_zero] at h0
  have hpm : IsPartialMatching A B (matchings.getD 0 []) := h0
  have hlen_le : (matchings.getD 0 []).length ≤ A.card := by
    have hnd := hpm.2.1
    have hsub : ((matchings.getD 0 []).map Prod.fst).toFinset ⊆ A := by
      intro x hx
      rcases List.mem_map.mp (List.mem_toFinset.mp hx) with ⟨ed, hed, rfl⟩
      exact (hpm.1 ed hed).1
    calc (matchings.getD 0 []).length
        = ((matchings.getD 0 []).map Prod.fst).length := by simp
      _ = ((matchings.getD 0 []).map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ A.card := Finset.card_le_card hsub
  exact ⟨hflat, hpm, hlen_le⟩

lemma witness_step_invariants {e k : ℕ} {A B : Finset ℕ}
    {W_edges F_edges M_k : List (ℕ × ℕ)}
    (hW_val : (Graph.mk (2 * e) W_edges).IsValid)
    (hW_loop : (Graph.mk (2 * e) W_edges).IsLoopless)
    (hW_deg : ∀ v < 2 * e, (Graph.mk (2 * e) W_edges).deg v ≤ k)
    (hW_len : W_edges.length ≤ k * e)
    (hF_len : F_edges.length ≤ k * e)
    (hA_sub : A ⊆ Finset.range (2 * e)) (hB_sub : B ⊆ Finset.range (2 * e))
    (hdisj : Disjoint A B) (hA_le : A.card ≤ e) (hAB_card : A.card ≤ B.card)
    (hpm : IsPartialMatching A B M_k) :
    let F_k := fakeCompletion A B M_k
    M_k.length + F_k.length ≤ e ∧
    F_k.length ≤ e ∧
    (W_edges ++ (M_k ++ F_k)).length ≤ (k + 1) * e ∧
    (F_edges ++ F_k).length ≤ (k + 1) * e ∧
    (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).IsValid ∧
    (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).IsLoopless ∧
    (∀ v < 2 * e, (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).deg v ≤ k + 1) := by
  intro F_k
  have hfc := fakeCompletion_spec hdisj hAB_card hpm
  rcases hfc with ⟨hF_len_eq, _, _, hpm_tot, hnd_tot, _⟩
  change F_k.length = A.card - M_k.length at hF_len_eq
  have hM_le_A : M_k.length ≤ A.card := by
    have hsub : (M_k.map Prod.fst).toFinset ⊆ A := by
      intro x hx
      rcases List.mem_map.mp (List.mem_toFinset.mp hx) with ⟨ed, hed, rfl⟩
      exact (hpm.1 ed hed).1
    calc M_k.length = (M_k.map Prod.fst).length := by simp
      _ = (M_k.map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup hpm.2.1).symm
      _ ≤ A.card := Finset.card_le_card hsub
  have hMF_le : M_k.length + F_k.length ≤ e := by omega
  have hFk_le : F_k.length ≤ e := by omega
  have hW_len' : (W_edges ++ (M_k ++ F_k)).length ≤ (k + 1) * e := by
    simp only [List.length_append]
    have hmul : (k + 1) * e = k * e + e := by ring
    omega
  have hF_len' : (F_edges ++ F_k).length ≤ (k + 1) * e := by
    simp only [List.length_append]
    have hmul : (k + 1) * e = k * e + e := by ring
    omega
  have hval' : (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).IsValid := by
    intro ed hed
    rcases List.mem_append.mp hed with h1 | h2
    · exact hW_val ed h1
    · have ⟨h1, h2⟩ := hpm_tot.1 ed h2
      exact ⟨Finset.mem_range.mp (hA_sub h1), Finset.mem_range.mp (hB_sub h2)⟩
  have hloop' : (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).IsLoopless := by
    intro ed hed
    rcases List.mem_append.mp hed with h1 | h2
    · exact hW_loop ed h1
    · have ⟨h1, h2⟩ := hpm_tot.1 ed h2
      intro heq
      exact Finset.disjoint_left.mp hdisj h1 (heq ▸ h2)
  have hdeg' : ∀ v < 2 * e, (Graph.mk (2 * e) (W_edges ++ (M_k ++ F_k))).deg v ≤ k + 1 := by
    intro v hv
    rw [deg_append]
    have h1 := hW_deg v hv
    have h2 : (Graph.mk (2 * e) (M_k ++ F_k)).deg v ≤ 1 := deg_le_one_of_nodup_flatMap hnd_tot v
    omega
  exact ⟨hMF_le, hFk_le, hW_len', hF_len', hval', hloop', hdeg'⟩

/-! ## 3. Small Return-Block Triples -/

lemma gameWriteCutRet_triple {w outResAddr routeOutAddr hCur kU : ℕ}
    (pProg : Program) (st₀ : State)
    (h3 : st₀.regs 3 = outResAddr) (h20 : st₀.regs 20 = routeOutAddr) (h26 : st₀.regs 26 = hCur)
    (hkU : st₀.mem (routeOutAddr + 1) = kU)
    (hwR : routeOutAddr + 2 < 2 ^ w) (hwO : outResAddr + 4 < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) gameWriteCutRetStmt
      (retPost fun v s' =>
        v = hCur ∧
        s'.mem outResAddr = 0 ∧
        s'.mem (outResAddr + 1) = kU ∧
        s'.mem (outResAddr + 2) = routeOutAddr + 2 ∧
        (∀ a, a < outResAddr ∨ outResAddr + 3 ≤ a → s'.mem a = st₀.mem a))
      (fun _ => 35) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [gameWriteCutRetStmt]
  refine runs_seq_assign_le (v := kU)
    (by simp [Expr.eval, BinOp.eval, h20, hw1, (by omega : routeOutAddr + 1 < 2 ^ w), hkU]) ?_
  refine runs_seq_store_le (x := outResAddr) (v := 0)
    (by simp [Expr.eval, h3]) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_seq_store_le (x := outResAddr + 1) (v := kU)
    (by simp [Expr.eval, BinOp.eval, h3, hw1, (by omega : outResAddr + 1 < 2 ^ w)])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := outResAddr + 2) (v := routeOutAddr + 2)
    (by simp [Expr.eval, BinOp.eval, h3, hw2, (by omega : outResAddr + 2 < 2 ^ w)])
    (by simp [Expr.eval, BinOp.eval, h20, hw2, (by omega : routeOutAddr + 2 < 2 ^ w)]) ?_
  refine runs_ret_le (v := hCur) (by simp [Expr.eval, h26]) ?_ (by simp [Expr.size])
  refine ⟨rfl,
    by simp (disch := omega) only [Function.update_of_ne, Function.update_self],
    by simp (disch := omega) only [Function.update_of_ne, Function.update_self],
    by simp,
    fun a ha => by simp (disch := omega) only [Function.update_of_ne]⟩

lemma gameWriteWitRet_triple {w outResAddr wAddr fLen fAddr hCur : ℕ}
    (pProg : Program) (st₀ : State)
    (h3 : st₀.regs 3 = outResAddr) (h16 : st₀.regs 16 = wAddr) (h17 : st₀.regs 17 = fAddr)
    (h25 : st₀.regs 25 = fLen) (h26 : st₀.regs 26 = hCur)
    (hwO : outResAddr + 4 < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) gameWriteWitRetStmt
      (retPost fun v s' =>
        v = hCur ∧
        s'.mem outResAddr = 1 ∧
        s'.mem (outResAddr + 1) = wAddr ∧
        s'.mem (outResAddr + 2) = fLen ∧
        s'.mem (outResAddr + 3) = fAddr ∧
        (∀ a, a < outResAddr ∨ outResAddr + 4 ≤ a → s'.mem a = st₀.mem a))
      (fun _ => 35) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [gameWriteWitRetStmt]
  refine runs_seq_store_le (x := outResAddr) (v := 1)
    (by simp [Expr.eval, h3]) (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_store_le (x := outResAddr + 1) (v := wAddr)
    (by simp [Expr.eval, BinOp.eval, h3, hw1, (by omega : outResAddr + 1 < 2 ^ w)])
    (by simp [Expr.eval, h16]) ?_
  refine runs_seq_store_le (x := outResAddr + 2) (v := fLen)
    (by simp [Expr.eval, BinOp.eval, h3, hw2, (by omega : outResAddr + 2 < 2 ^ w)])
    (by simp [Expr.eval, h25]) ?_
  refine runs_seq_store_le (x := outResAddr + 3) (v := fAddr)
    (by simp [Expr.eval, BinOp.eval, h3, hw3, (by omega : outResAddr + 3 < 2 ^ w)])
    (by simp [Expr.eval, h17]) ?_
  refine runs_ret_le (v := hCur) (by simp [Expr.eval, h26]) ?_ (by simp [Expr.size])
  refine ⟨rfl,
    by simp (disch := omega) only [Function.update_of_ne, Function.update_self],
    by simp (disch := omega) only [Function.update_of_ne, Function.update_self],
    by simp (disch := omega) only [Function.update_of_ne, Function.update_self],
    by simp,
    fun a ha => by simp (disch := omega) only [Function.update_of_ne]⟩


end MinCostFlow.ExpanderDecomp

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 4. Loop Invariant and Inductive Verification -/

/-- Fixed layout geometry of `outerGameProc` for a given call. -/
structure GameGeom (cfg : ParamConfig) (M r e pgAddr outResAddr h : ℕ) where
  Hhat : Graph
  hHhat_n : Hhat.n = 2 * e
  hHhat_m : Hhat.m ≤ 10 * e
  hHhat_val : Hhat.IsValid
  hHhat_loop : Hhat.IsLoopless
  hHhat_deg : ∀ v, Hhat.deg v ≤ 10
  he_pos : 1 ≤ e
  hr_pos : 1 ≤ r
  hN2 : 2 ≤ NOf M r
  h2e_pow : 2 * e ≤ (NOf M r) ^ r
  h2e_L : 2 * e < 2 ^ LParam M
  hpgH : pgAddr + 2 + 2 * Hhat.m ≤ h
  houtH : outResAddr + 4 ≤ h
  hdOG : DisjointRange outResAddr 4 pgAddr (2 + 2 * Hhat.m)

def GameGeom.F {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (_g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := 49 * LParam M + 1
def GameGeom.xPortAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (_g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := h
def GameGeom.wAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (_g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := h + 1 + 2 * e
def GameGeom.wEdgesAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.wAddr + 2
def GameGeom.fAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.wEdgesAddr + 2 * g.F * e
def GameGeom.coreOutAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.fAddr + 2 * g.F * e
def GameGeom.pairsAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.coreOutAddr + 2 + 2 * e
def GameGeom.routeOutAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.pairsAddr + 3 + 2 * e
def GameGeom.fRoundAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.routeOutAddr + 2 + 4 * e
def GameGeom.fLenAddr {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.fRoundAddr + 2 * e
def GameGeom.hInit {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) : ℕ := g.fLenAddr + 1

lemma GameGeom.hInit_eq {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) :
    g.hInit = h + outerGameBufSpace M e := by
  simp only [GameGeom.hInit, GameGeom.fLenAddr, GameGeom.fRoundAddr, GameGeom.routeOutAddr,
    GameGeom.pairsAddr, GameGeom.coreOutAddr, GameGeom.fAddr, GameGeom.wEdgesAddr, GameGeom.wAddr,
    GameGeom.F, outerGameBufSpace]
  ring

/-- State invariant before iteration `k` (with `fuel` remaining rounds, `k + fuel = 49 * L + 1`). -/
structure GameLoopInv {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h)
    (mem₀ : ℕ → ℕ) (fuel k : ℕ) (W_edges F_edges : List (ℕ × ℕ)) (st : State) : Prop where
  hk_fuel : k + fuel = g.F
  hW_len : W_edges.length ≤ k * e
  hF_len : F_edges.length ≤ k * e
  hW_val : (Graph.mk (2 * e) W_edges).IsValid
  hW_loop : (Graph.mk (2 * e) W_edges).IsLoopless
  hW_deg : ∀ v < 2 * e, (Graph.mk (2 * e) W_edges).deg v ≤ k
  hr0 : st.regs 0 = e
  hr1 : st.regs 1 = pgAddr
  hr3 : st.regs 3 = outResAddr
  hr5 : st.regs 5 = M
  hr6 : st.regs 6 = r
  hr7 : st.regs 7 = LParam M
  hr9 : st.regs 9 = bOut cfg M
  hr11 : st.regs 11 = g.F
  hr12 : st.regs 12 = 2 * e
  hr13 : st.regs 13 = e / DOut cfg M r
  hr14 : st.regs 14 = coreLevel M r (2 * e)
  hr15 : st.regs 15 = g.xPortAddr
  hr16 : st.regs 16 = g.wAddr
  hr17 : st.regs 17 = g.fAddr
  hr18 : st.regs 18 = g.coreOutAddr
  hr19 : st.regs 19 = g.pairsAddr
  hr20 : st.regs 20 = g.routeOutAddr
  hr21 : st.regs 21 = g.fRoundAddr
  hr22 : st.regs 22 = g.fLenAddr
  hr23 : st.regs 23 = g.wEdgesAddr
  hr24 : st.regs 24 = W_edges.length
  hr25 : st.regs 25 = F_edges.length
  hr27 : st.regs 27 = fuel
  hhInit : g.hInit ≤ st.regs 26
  hZero : ZeroFrom st.mem (st.regs 26)
  hPg : GraphAt st.mem pgAddr g.Hhat
  hXPort : LenListAt st.mem g.xPortAddr (List.range (2 * e))
  hW_g : GraphAt st.mem g.wAddr (Graph.mk (2 * e) W_edges)
  hF_e : EdgesAt st.mem g.fAddr F_edges
  hFrame : ∀ a < h, st.mem a = mem₀ a



end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma GameGeom.bufOrder {cfg : ParamConfig} {M r e pgAddr outResAddr h : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h) :
    h ≤ g.xPortAddr ∧
    g.xPortAddr + 1 + 2 * e = g.wAddr ∧
    g.wAddr + 2 = g.wEdgesAddr ∧
    g.wEdgesAddr + 2 * g.F * e = g.fAddr ∧
    g.fAddr + 2 * g.F * e = g.coreOutAddr ∧
    g.coreOutAddr + 2 + 2 * e = g.pairsAddr ∧
    g.pairsAddr + 3 + 2 * e = g.routeOutAddr ∧
    g.routeOutAddr + 2 + 4 * e = g.fRoundAddr ∧
    g.fRoundAddr + 2 * e = g.fLenAddr ∧
    g.fLenAddr + 1 = g.hInit := by
  simp [GameGeom.xPortAddr, GameGeom.wAddr, GameGeom.wEdgesAddr, GameGeom.fAddr,
    GameGeom.coreOutAddr, GameGeom.pairsAddr, GameGeom.routeOutAddr, GameGeom.fRoundAddr,
    GameGeom.fLenAddr, GameGeom.hInit]

private lemma one_le_coreSpaceBase (M r : ℕ) : 1 ≤ coreSpaceBase M r := by
  unfold coreSpaceBase
  have : 1 ≤ 2048 * LParam M * (NOf M r) ^ r + 3 := by omega
  exact Nat.one_le_pow 5 _ this

lemma gamePostPair_space_aux {M r e fuel lc cCore cRoute C_sp_core C_sp_rt C_sp st26 st3_26 : ℕ}
    (hsp_c : C_sp_core ≤ C_sp) (hsp_r : C_sp_rt ≤ C_sp)
    (hh3_le : st3_26 ≤ st26 + coreAdapterSpace C_sp_core M r (2 * e) cCore + 2 * e)
    (hcc_le : cCore + cRoute ≤ lc) :
    st3_26 + outerRouterSpace C_sp_rt (2 * e) cRoute + 8 * e ≤
      st26 + C_sp * coreSpaceBase M r * (cCore + cRoute + 1) +
        (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) ∧
    st26 + C_sp * coreSpaceBase M r * (cCore + cRoute + 1) +
        (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) ≤
      st26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc := by
  have hB1 : 1 ≤ coreSpaceBase M r := one_le_coreSpaceBase M r
  unfold coreAdapterSpace at hh3_le
  unfold outerRouterSpace outerGameLoopSpace
  set SB := coreSpaceBase M r
  have hpow45 : (2 * e + 3) ^ 4 ≤ (2 * e + 3) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hcore_le : C_sp_core * (SB * (cCore + 1) + (2 * e + 3) ^ 5 + 1) ≤
      C_sp * SB * (cCore + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) := by
    have h0 := Nat.mul_le_mul_right (SB * (cCore + 1) + (2 * e + 3) ^ 5 + 1) hsp_c
    have h1 : C_sp * (SB * (cCore + 1) + (2 * e + 3) ^ 5 + 1) =
        C_sp * SB * (cCore + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) := by ring
    omega
  have hrt_le : C_sp_rt * (cRoute + (2 * e + 3) ^ 4 + 1) ≤
      C_sp * SB * cRoute + C_sp * ((2 * e + 3) ^ 5 + 1) := by
    have h0 : C_sp_rt * (cRoute + (2 * e + 3) ^ 4 + 1) ≤
        C_sp * (cRoute + (2 * e + 3) ^ 5 + 1) :=
      Nat.mul_le_mul hsp_r (by omega)
    have h1 : C_sp * cRoute ≤ C_sp * SB * cRoute := by
      have : C_sp * cRoute = C_sp * 1 * cRoute := by ring
      rw [this]; exact Nat.mul_le_mul_right cRoute (Nat.mul_le_mul_left C_sp hB1)
    have h2 : C_sp * (cRoute + (2 * e + 3) ^ 5 + 1) =
        C_sp * cRoute + C_sp * ((2 * e + 3) ^ 5 + 1) := by ring
    linarith
  have h1 : C_sp * SB * (cCore + cRoute + 1) ≤ C_sp * SB * (lc + (fuel + 1)) :=
    Nat.mul_le_mul_left (C_sp * SB) (by omega)
  have h2 : 2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e ≤
      (fuel + 1) * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos fuel)
  have h3 : C_sp * SB * (cCore + 1) + C_sp * SB * cRoute =
      C_sp * SB * (cCore + cRoute + 1) := by ring
  have h4 : C_sp * ((2 * e + 3) ^ 5 + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) =
      2 * C_sp * ((2 * e + 3) ^ 5 + 1) := by ring
  exact ⟨by linarith, by linarith⟩

end MinCostFlow.ExpanderDecomp
