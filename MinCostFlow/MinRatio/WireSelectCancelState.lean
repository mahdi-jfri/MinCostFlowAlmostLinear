module

public import MinCostFlow.MinRatio.WireSelectPathSum
public import MinCostFlow.MinRatio.PathCompareExchange
public import MinCostFlow.MinRatio.PathSwapHistory
public import MinCostFlow.MinRatio.PathCancellationAccounting
import WordRAM.Tactic

/-!
# State invariant and helper lemmas for path-cancellation post-processing

Defines the swap-history and loop-state invariants (`ValidSwapSeq`, `CancelState`) used to
verify `cancelPairInnerBody`, `cancelPairOuterBody`, and `cancelRoutePathsBody`
(`WireSelectQuery.lean`, Algorithm 2, page 29), together with:
1. `validSwapSeq_zero`, `validSwapSeq_extend`: maintains the premise of `pathSwap_index_history`
   as well as the same-component invariant across every improving swap.
2. `scaled_lt_iff` and `fits_sum_two_paths`: exact correspondence between `2^P`-scaled integer
   sums and real `walkLength` sums, plus limb-capacity overflow safety for two-path sums.
3. `cancelPairGuard_runs`: verifies the 4-statement guarded `opTree 3` (`PathSummary`) block
   `rS := r7 ;; r7 := opTree 3 (r0, rU + 1, rV + 1, r7) ;; r18 := rS + 2 * r1 ;; if r7 < r18 then r7 := r18`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LinkCut.PathProg

/-- A valid length-`steps` sequence of strictly improving destination swaps on forest `F` with
positive edge lengths `length` (exact premise of `pathSwap_index_history`). -/
@[expose] def ValidSwapSeq (F : MGraph) (length : ℕ → ℝ) (route : ℕ → List (ℕ × ℕ)) (steps : ℕ) : Prop :=
  ∀ t < steps, ∃ i j : ℕ, ∃ hij : i < j, ∃ hj : j < (route t).length,
    let hi := hij.trans hj
    let a := (route t)[i].1
    let b := (route t)[i].2
    let c := (route t)[j].1
    let d := (route t)[j].2
    F.Connected a c ∧
    walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) <
      walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) ∧
    route (t + 1) = ((route t).set i (a, d)).set j (c, b)

theorem validSwapSeq_zero (F : MGraph) (length : ℕ → ℝ) (route : ℕ → List (ℕ × ℕ)) :
    ValidSwapSeq F length route 0 := fun _ h => (Nat.not_lt_zero _ h).elim

theorem validSwapSeq_extend {F : MGraph} {length : ℕ → ℝ} {route : ℕ → List (ℕ × ℕ)}
    {steps i j n : ℕ} {paths : List (ℕ × ℕ)}
    (hH : ValidSwapSeq F length route steps)
    (hRt : route steps = paths)
    (hij : i < j) (hj : j < paths.length)
    (hPtOk : ∀ p ∈ paths, p.1 < n ∧ p.2 < n ∧ F.Connected p.1 p.2)
    (hSame : ∀ p ∈ paths, ∀ q ∈ paths, F.Connected p.1 q.1)
    (hlt : walkLength length (F.forestPath (paths[i]'(hij.trans hj)).1 (paths[j]'hj).2) +
        walkLength length (F.forestPath (paths[j]'hj).1 (paths[i]'(hij.trans hj)).2) <
      walkLength length (F.forestPath (paths[i]'(hij.trans hj)).1 (paths[i]'(hij.trans hj)).2) +
        walkLength length (F.forestPath (paths[j]'hj).1 (paths[j]'hj).2)) :
    let hi := hij.trans hj
    let paths' := (paths.set i (paths[i].1, paths[j].2)).set j (paths[j].1, paths[i].2)
    let route' := Function.update route (steps + 1) paths'
    ValidSwapSeq F length route' (steps + 1) ∧
    route' 0 = route 0 ∧
    route' (steps + 1) = paths' ∧
    paths'.length = paths.length ∧
    (∀ p ∈ paths', p.1 < n ∧ p.2 < n ∧ F.Connected p.1 p.2) ∧
    (∀ p ∈ paths', ∀ q ∈ paths', F.Connected p.1 q.1) := by
  dsimp only
  set hi := hij.trans hj
  set paths' := (paths.set i (paths[i].1, paths[j].2)).set j (paths[j].1, paths[i].2)
  set route' := Function.update route (steps + 1) paths'
  have hpi := hPtOk paths[i] (List.getElem_mem hi)
  have hpj := hPtOk paths[j] (List.getElem_mem hj)
  have hac : F.Connected paths[i].1 paths[j].1 :=
    hSame _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  have had : F.Connected paths[i].1 paths[j].2 := MGraph.connected_trans hac hpj.2.2
  have hcb : F.Connected paths[j].1 paths[i].2 :=
    MGraph.connected_trans (MGraph.connected_symm hac) hpi.2.2
  have hValid' : ValidSwapSeq F length route' (steps + 1) := by
    intro t ht
    by_cases hts : t = steps
    · subst hts
      have hrEq : route' t = paths := by
        dsimp only [route']; rw [Function.update_of_ne (by omega), hRt]
      refine ⟨i, j, hij, hrEq.symm ▸ hj, ?_, ?_, ?_⟩
      · simpa only [hrEq] using hac
      · simpa only [hrEq] using hlt
      · exact (show route' (t + 1) = paths' from Function.update_self ..).trans (by simp only [hrEq, paths'])
    · have htLt : t < steps := by omega
      have h1 : route' t = route t := Function.update_of_ne (by omega) _ _
      have h2 : route' (t + 1) = route (t + 1) := Function.update_of_ne (by omega) _ _
      obtain ⟨i', j', hij', hj', hac', hlt', hstep'⟩ := hH t htLt
      refine ⟨i', j', hij', h1.symm ▸ hj', ?_, ?_, ?_⟩
      · simpa only [h1] using hac'
      · simpa only [h1] using hlt'
      · rw [h2]; simpa only [h1] using hstep'
  have hMemSet : ∀ {xs : List (ℕ × ℕ)} {k : ℕ} {v x : ℕ × ℕ}, x ∈ xs.set k v → x ∈ xs ∨ x = v := by
    intro xs k v x hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    by_cases hmk : m = k
    · subst hmk; exact Or.inr (List.getElem_set_self ..)
    · rw [List.getElem_set_ne (Ne.symm hmk)]
      exact Or.inl (List.getElem_mem (by simpa using hm))
  have hMem : ∀ p ∈ paths', p ∈ paths ∨ p = (paths[i].1, paths[j].2) ∨ p = (paths[j].1, paths[i].2) := by
    intro p hp
    rcases hMemSet hp with hp1 | rfl
    · rcases hMemSet hp1 with hp0 | rfl
      · exact Or.inl hp0
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hOk' : ∀ p ∈ paths', p.1 < n ∧ p.2 < n ∧ F.Connected p.1 p.2 := by
    intro p hp
    rcases hMem p hp with h0 | rfl | rfl
    · exact hPtOk p h0
    · exact ⟨hpi.1, hpj.2.1, had⟩
    · exact ⟨hpj.1, hpi.2.1, hcb⟩
  have hSame' : ∀ p ∈ paths', ∀ q ∈ paths', F.Connected p.1 q.1 := by
    have hFst : ∀ p ∈ paths', ∃ r ∈ paths, p.1 = r.1 := fun p hp => by
      rcases hMem p hp with h0 | rfl | rfl
      · exact ⟨p, h0, rfl⟩
      · exact ⟨paths[i], List.getElem_mem hi, rfl⟩
      · exact ⟨paths[j], List.getElem_mem hj, rfl⟩
    intro p hp q hq
    obtain ⟨rp, hrp, hp1⟩ := hFst p hp
    obtain ⟨rq, hrq, hq1⟩ := hFst q hq
    rw [hp1, hq1]; exact hSame rp hrp rq hrq
  refine ⟨hValid', Function.update_of_ne (by omega) _ _, Function.update_self ..,
    by simp [paths'], hOk', hSame'⟩

/-- Invariant state threaded through `cancelPairInnerBody`, `cancelPairOuterBody`, and
`cancelRoutePathsBody`. -/
structure CancelState {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P m V psi k epsExp drainUnit : ℕ)
    (loc : SelectHeapLoc) (root descBase pathsBase K flagPtr size : ℕ)
    (model : Alg2State cfg) (B R : ℤ) (pathsInit : List (ℕ × ℕ))
    (levelsEnd0 intCap0 handle0 treeHeap0 : ℕ)
    (mem : ℕ → ℕ) (tok : SolverToken cfg L Rcore) (paths : List (ℕ × ℕ))
    (route : ℕ → List (ℕ × ℕ)) (steps work : ℕ) : Prop where
  hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem
  hMatch : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size
  hnum : PathTreeNumericInv tok.tree tok.trees B R
  hoff : OffTreeRecInv model L mem tok.edgeRecords B
  hBd : OffTreeRecBound model L mem tok.edgeRecords B
  hPtAt : PathEndpointsAt mem pathsBase paths
  hlen : paths.length = K
  hPtOk : ∀ p ∈ paths, p.1 < model.extG.n ∧ p.2 < model.extG.n ∧
    model.chain.toTreeChain.chainTree.Connected p.1 p.2
  hSameComp : ∀ p ∈ paths, ∀ q ∈ paths, model.chain.toTreeChain.chainTree.Connected p.1 q.1
  hHist : ValidSwapSeq model.chain.toTreeChain.chainTree
    (fun ei => model.extℓ (model.intToExt ei)) route steps
  hR0 : route 0 = pathsInit
  hRt : route steps = paths
  hlev : tok.levelsEnd = levelsEnd0
  hcap : tok.intCap = intCap0
  hhdl : tok.handle = handle0
  htreeH : tok.treeHeap = treeHeap0
  hnfPt : ∀ x < 2 * K, ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (pathsBase + x)
  hlocDisj : ∀ a, loc.hb ≤ a → a < loc.endAddr →
    ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a
  htag18 : ∀ a, tok.tag a = 18 → a < descBase
  hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < work
  hz : ZeroFrom mem work
  hFlagDisj : ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok flagPtr
  hFlagLt : flagPtr < work
  hPtLt : pathsBase + 2 * K ≤ flagPtr
  hDescLtPt : descBase ≤ pathsBase

theorem scaled_lt_iff {P : ℕ} {x y : ℤ} {rx ry : ℝ}
    (hx : (x : ℝ) / (2 : ℝ) ^ P = rx) (hy : (y : ℝ) / (2 : ℝ) ^ P = ry) :
    x < y ↔ rx < ry := by
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
  rw [← hx, ← hy, div_lt_div_iff_of_pos_right hP]
  exact Int.cast_lt.symm

theorem fits_sum_two_paths {L n maxEdges maxPaths : ℕ} {B x y : ℤ}
    (hB : 0 ≤ B) (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hx : |x| ≤ (n : ℤ) * B) (hy : |y| ≤ (n : ℤ) * B) :
    Num.Fits 4 L (x + y) := by
  unfold Num.Fits
  have h2le : 2 ≤ maxPaths := by omega
  have h1 : 2 * (n : ℤ) ≤ (maxEdges + maxPaths * n : ℕ) := by
    push_cast
    have hmn : 2 * (n : ℤ) ≤ (maxPaths : ℤ) * (n : ℤ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h2le) (Int.natCast_nonneg n)
    linarith
  have h2 : |x + y| ≤ 2 * ((n : ℤ) * B) := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ (n : ℤ) * B + (n : ℤ) * B := add_le_add hx hy
      _ = 2 * ((n : ℤ) * B) := by ring
  have h3 : 2 * ((n : ℤ) * B) ≤ ((maxEdges + maxPaths * n : ℕ) : ℤ) * B := by
    have := mul_le_mul_of_nonneg_right h1 hB
    linarith
  have h4 : |x + y| * 2 < (Num.capacity 4 L : ℤ) := by linarith
  have h5 : |2 * (x + y)| < (Num.capacity 4 L : ℤ) := by
    rw [abs_mul, show |(2 : ℤ)| = 2 by decide]; linarith
  exact ⟨by linarith [(abs_lt.mp h5).1], (abs_lt.mp h5).2⟩

/-- Runs the 4-statement guarded `opTree 3` (`PathSummary`) block used four times in
`cancelPairInnerBody`, ensuring the returned scratch pointer is at least `s0 + 2 * L`. -/
theorem cancelPairGuard_runs {w opTree3 treeHeap0 L rS rU rV uV vV s0 oV : ℕ}
    {p : Program} {ω : ℕ → Bool} {mA mB : ℕ → ℕ} {rgA : ℕ → ℕ} {posA posB cT : ℕ} {bT : Stmt}
    (hw16 : 16 < 2 ^ w)
    (h0 : rgA 0 = treeHeap0) (h1 : rgA 1 = L) (h7 : rgA 7 = s0)
    (hrU : rgA rU = uV) (hrV : rgA rV = vV)
    (hrS0 : rS ≠ 0) (hrS1 : rS ≠ 1) (hrS7 : rS ≠ 7) (hrS18 : rS ≠ 18)
    (hrUS : rU ≠ rS) (hrVS : rV ≠ rS)
    (huW : uV + 1 < 2 ^ w) (hvW : vV + 1 < 2 ^ w) (h2LW : s0 + 2 * L < 2 ^ w)
    (hbT : p.procs[opTree3]? = some bT)
    {oT : Outcome} {stT : State} (hoEq : oT.value = oV) (hmEq : stT.mem = mB) (hpEq : stT.pos = posB)
    (hrT : Runs w p ω bT (startState [treeHeap0, uV + 1, vV + 1, s0] mA posA) oT stT cT) :
    ∃ (rgB : ℕ → ℕ) (cG : ℕ),
      Runs w p ω
        (.assign rS (.reg 7) ;;
         .call 7 opTree3 [.reg 0, .bin .add (.reg rU) (.const 1), .bin .add (.reg rV) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg rS) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop)
        ⟨mA, rgA, posA⟩ .normal ⟨mB, rgB, posB⟩ cG ∧
      (∀ r, r ≠ rS → r ≠ 7 → r ≠ 18 → rgB r = rgA r) ∧
      rgB rS = s0 ∧ rgB 7 = max oV (s0 + 2 * L) ∧ cG ≤ cT + 30 := by
  let rg1 := Function.update rgA rS s0
  let rg2 := Function.update rg1 7 oV
  let rg3 := Function.update rg2 18 (s0 + 2 * L)
  have hs1 : Runs w p ω (.assign rS (.reg 7)) ⟨mA, rgA, posA⟩ .normal ⟨mA, rg1, posA⟩ 2 :=
    runs_assign_iff.mpr ⟨s0, by simp [Expr.eval, h7], rfl, rfl, rfl⟩
  have hrg1_0 : rg1 0 = treeHeap0 := by simp [rg1, hrS0.symm, h0]
  have hrg1_1 : rg1 1 = L := by simp [rg1, hrS1.symm, h1]
  have hrg1_7 : rg1 7 = s0 := by simp [rg1, hrS7.symm, h7]
  have hrg1_U : rg1 rU = uV := by simp [rg1, hrUS, hrU]
  have hrg1_V : rg1 rV = vV := by simp [rg1, hrVS, hrV]
  have hs2 : Runs w p ω
      (.call 7 opTree3 [.reg 0, .bin .add (.reg rU) (.const 1), .bin .add (.reg rV) (.const 1), .reg 7])
      ⟨mA, rg1, posA⟩ .normal ⟨mB, rg2, posB⟩ (cT + 9) := by
    refine runs_call_iff.mpr ⟨[treeHeap0, uV + 1, vV + 1, s0], bT, oT, stT, cT, ?_, hbT, hrT, rfl, ?_, ?_⟩
    · simp [evalArgs, Expr.eval, BinOp.eval, hrg1_0, hrg1_U, hrg1_V, hrg1_7,
        show 1 < 2 ^ w by omega, huW, hvW]
    · simp [rg2, hoEq, hmEq, hpEq]
    · simp [argsSize, Expr.size]; omega
  have hrg2_S : rg2 rS = s0 := by simp [rg2, rg1, hrS7]
  have hrg2_1 : rg2 1 = L := by simp [rg2, hrg1_1]
  have hs3 : Runs w p ω (.assign 18 (.bin .add (.reg rS) (.bin .mul (.const 2) (.reg 1))))
      ⟨mB, rg2, posB⟩ .normal ⟨mB, rg3, posB⟩ 6 :=
    runs_assign_iff.mpr ⟨s0 + 2 * L, by
      simp [Expr.eval, BinOp.eval, hrg2_S, hrg2_1, show 2 < 2 ^ w by omega,
        show 2 * L < 2 ^ w by omega, h2LW], rfl, rfl, rfl⟩
  have hrg3_7 : rg3 7 = oV := by simp [rg3, rg2]
  have hrg3_18 : rg3 18 = s0 + 2 * L := Function.update_self ..
  have hrg3_S : rg3 rS = s0 := by simp [rg3, hrS18, hrg2_S]
  by_cases hltG : oV < s0 + 2 * L
  · let rg4 := Function.update rg3 7 (s0 + 2 * L)
    have hs4 : Runs w p ω (.cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop)
        ⟨mB, rg3, posB⟩ .normal ⟨mB, rg4, posB⟩ 6 :=
      runs_cond_iff.mpr ⟨1, 2,
        by simp [Expr.eval, BinOp.eval, hrg3_7, hrg3_18, hltG, show 1 < 2 ^ w by omega],
        by simp [runs_assign_iff, Expr.eval, hrg3_18, rg4], by simp [Expr.size]⟩
    refine ⟨rg4, _,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs3, hs4, rfl⟩), rfl⟩), rfl⟩),
      ?_, ?_, ?_, by omega⟩
    · intro r hr1 hr2 hr3
      simp [rg4, rg3, rg2, rg1, hr1, hr2, hr3]
    · simp [rg4, hrS7, hrg3_S]
    · simp [rg4, Nat.max_eq_right (le_of_lt hltG)]
  · have hs4 : Runs w p ω (.cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop)
        ⟨mB, rg3, posB⟩ .normal ⟨mB, rg3, posB⟩ 5 :=
      runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, hrg3_7, hrg3_18, hltG],
        by simp [runs_nop_iff], by simp [Expr.size]⟩
    refine ⟨rg3, _,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs3, hs4, rfl⟩), rfl⟩), rfl⟩),
      ?_, ?_, ?_, by omega⟩
    · intro r hr1 hr2 hr3
      simp [rg3, rg2, rg1, hr1, hr2, hr3]
    · exact hrg3_S
    · rw [hrg3_7, Nat.max_eq_left (not_lt.mp hltG)]

/-- Appends a continuation `t` to the right spine of a `;`-separated statement `s`. -/
@[expose] def appendStmt : Stmt → Stmt → Stmt
  | .seq a b, t => .seq a (appendStmt b t)
  | s, t => .seq s t

/-- Composes a normal run of `s` with a run of `t` into a run of `appendStmt s t`. -/
theorem runs_appendStmt {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st0 st1 st2 : State} {o : Outcome} {c1 c2 : ℕ}
    (h1 : Runs w p ω s st0 .normal st1 c1)
    (h2 : Runs w p ω t st1 o st2 c2) :
    Runs w p ω (appendStmt s t) st0 o st2 (c1 + c2 + 1) := by
  induction s generalizing st0 c1 with
  | seq a b _ ihb =>
    rcases runs_seq_iff.mp h1 with ⟨_, _, _, hne, _⟩ | ⟨stM, ca, cb, ha, hb, rfl⟩
    · cases hne
    · have hbt := ihb hb
      have hab := runs_seq_iff.mpr (Or.inr ⟨stM, ca, cb + c2 + 1, ha, hbt, rfl⟩)
      rwa [show ca + (cb + c2 + 1) + 1 = ca + cb + 1 + c2 + 1 by omega] at hab
  | _ => exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩)

end MinCostFlow.MinRatio
