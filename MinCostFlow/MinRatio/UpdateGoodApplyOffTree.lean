module

public import MinCostFlow.MinRatio.ExplicitEdgeRouteUpdate
public import MinCostFlow.MinRatio.UpdateOffTreePush
import WordRAM.Tactic

/-!
# Off-tree explicit-edge flow update and `offReadyList` push for `Update`

When `Chain.Ordered.algorithm2_loopWith` finds a good cycle with explicit off-tree edge list
`edges : List (ℕ × Bool)` (encoded at `edgesBase` in internal edge IDs),
`updateGoodApplyOffTreeBody`:
1. calls `explicitEdgeRouteUpdateBody` on `[edgesBase, edgesLen, edgeRecords, heap, multPtr, L]`
   to apply the grouped signed flow increment and its absolute detector increment in-place
   at `edgeRecords[ei]` for every `ei ∈ edges.map Prod.fst`, and
2. loops over `j = 0 .. edgesLen - 1`, invoking `offTreePushBody` on `[root, ei, edgeRecords[ei], L]`
   to push every newly ready (`0 ≤ detector`) off-tree edge onto `offReadyList` while maintaining
   `OffReadyInv`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Space reserved by `explicitEdgeRouteUpdateBody` for `edgesLen` explicit edge occurrences. -/
@[expose] def explicitRouteSpace (L edgesLen : ℕ) : ℕ :=
  edgesLen + edgesLen * (17 * L + 3)

/-- Fixed deterministic procedure taking `[root, edgesBase, edgesLen, multPtr, L, heap]`.
Applies all grouped explicit off-tree increments via `explicitRouteUpdate` and pushes every
newly ready off-tree edge onto `offReadyList` via `offTreePush`, returning the updated heap. -/
@[expose] def updateGoodApplyOffTreeBody (explicitRouteUpdate offTreePush : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .call 7 explicitRouteUpdate [.reg 1, .reg 2, .reg 6, .reg 5, .reg 3, .reg 4] ;;
  forRange 8 (.const 0) (.reg 2)
    (.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
     .call 11 offTreePush [.reg 0, .reg 9, .reg 10, .reg 4]) ;;
  .ret (.reg 7)

theorem updateGoodApplyOffTreeBody_noRand (explicitRouteUpdate offTreePush : ℕ) :
    (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush).NoRand := by
  simp [updateGoodApplyOffTreeBody, forRange, forUp, Stmt.NoRand]

/-- Updated `PathEdgeValue` after applying `explicitEdgeRouteUpdateBody` with multiplier `mult`
to explicit edge list `edges`. -/
@[expose] def updatedOffTreeVal (edges : List (ℕ × Bool)) (old : ℕ → PathEdgeValue)
    (mult : ℤ) (ei : ℕ) : PathEdgeValue :=
  let net : ℤ := (edges.count (ei, true) : ℤ) - (edges.count (ei, false) : ℤ)
  (old ei).shift (PathTag.ofFlow (mult * net))

/-- Inductive proof of the `offTreePush` scan over `j = 0 .. edges.length - 1`. -/
private theorem offTreePushLoop_runs
    {w offTreePush isNeg root edgesBase L edgeRecords offReadyList inOffReady intCap heapRet : ℕ}
    {p : Program} {ω : ℕ → Bool} {edges : List (ℕ × Bool)}
    {address : ℕ → ℕ} {newVal : ℕ → PathEdgeValue}
    (tag : ℕ → ℕ)
    (hPush : p.procs[offTreePush]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hw13 : 13 < 2 ^ w) (hroot13W : root + 13 < 2 ^ w)
    (hcapW : intCap < 2 ^ w) (hLW : L < 2 ^ w)
    (holW : ∀ k < intCap, offReadyList + k < 2 ^ w)
    (hedgesLenW : edges.length < 2 ^ w)
    (hedgesEndW : edgesBase + 2 * edges.length ≤ 2 ^ w)
    (ht1 : ∀ j < 14, tag (root + j) = 1)
    (ht13 : ∀ k < intCap, tag (edgeRecords + k) = 13)
    (ht14 : ∀ k < intCap, tag (offReadyList + k) = 14)
    (ht15 : ∀ k < intCap, tag (inOffReady + k) = 15)
    (ht18 : ∀ ei ∈ edges.map Prod.fst, ∀ x < 2 + 4 * L, tag (address ei + x) = 18)
    (htEdges : ∀ x < 2 * edges.length, tag (edgesBase + x) = 0)
    (heiBound : ∀ ei ∈ edges.map Prod.fst, ei < intCap ∧ edgeRecords + ei < 2 ^ w ∧
      inOffReady + ei < 2 ^ w ∧ address ei + (2 + 4 * L) < 2 ^ w) :
    ∀ (rem : ℕ) (st : State) (cnt : ℕ),
      let j := edges.length - rem
      rem ≤ edges.length →
      st.regs 0 = root → st.regs 1 = edgesBase → st.regs 2 = edges.length →
      st.regs 4 = L → st.regs 6 = edgeRecords → st.regs 7 = heapRet → st.regs 8 = j →
      st.mem (root + 10) = edgeRecords → st.mem (root + 11) = cnt →
      st.mem (root + 12) = offReadyList → st.mem (root + 13) = inOffReady →
      OffReadyInv st.mem cnt offReadyList inOffReady intCap →
      ExplicitEdgesAt st.mem edgesBase edges →
      (∀ ei ∈ edges.map Prod.fst, st.mem (edgeRecords + ei) = address ei ∧
        PathEdgeAt st.mem (address ei) 4 L (some (newVal ei))) →
      (∀ k (hk : k < edges.length), k < j →
        0 ≤ (newVal (edges[k]'hk).1).detector → st.mem (inOffReady + (edges[k]'hk).1) = 1) →
      ∃ out cost cnt',
        Runs w p ω
          (.loop (.bin .lt (.reg 8) (.reg 2))
            ((.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))) ;;
              .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
              .call 11 offTreePush [.reg 0, .reg 9, .reg 10, .reg 4]) ;;
             .assign 8 (.bin .add (.reg 8) (.const 1))))
          st .normal out cost ∧
        cost ≤ rem * 130 + 4 ∧
        out.regs 7 = heapRet ∧
        cnt ≤ cnt' ∧ cnt' ≤ cnt + rem ∧
        out.mem (root + 11) = cnt' ∧
        OffReadyInv out.mem cnt' offReadyList inOffReady intCap ∧
        (∀ ei ∈ edges.map Prod.fst, 0 ≤ (newVal ei).detector → out.mem (inOffReady + ei) = 1) ∧
        (∀ a, a ≠ root + 11 → tag a ≠ 14 → tag a ≠ 15 → out.mem a = st.mem a) ∧
        (∀ k < intCap, st.mem (inOffReady + k) = 1 → out.mem (inOffReady + k) = 1) ∧
        (∀ k < intCap, k ∉ edges.map Prod.fst → out.mem (inOffReady + k) = st.mem (inOffReady + k)) := by
  intro rem
  induction rem with
  | zero =>
    intro st cnt j hrem hr0 hr1 hr2 hr4 hr6 hr7 hr8 hm10 hm11 hm12 hm13 hoff hedges hrec hprev
    have hjEq : j = edges.length := by dsimp only [j]; omega
    have hcond0 : (Expr.bin .lt (.reg 8) (.reg 2)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hr8, hr2, hjEq, show 0 < 2 ^ w by omega]
    refine ⟨st, 4, cnt,
      runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
      by omega, hr7, le_rfl, le_rfl, hm11, hoff, ?_,
      fun _ _ _ _ => rfl, fun _ _ h => h, fun _ _ _ => rfl⟩
    intro ei hei hdet
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hei
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hrow
    rw [← hget] at hdet ⊢
    exact hprev k hk (by omega) hdet
  | succ rem ih =>
    intro st cnt j hrem hr0 hr1 hr2 hr4 hr6 hr7 hr8 hm10 hm11 hm12 hm13 hoff hedges hrec hprev
    have hjLt : j < edges.length := by dsimp only [j]; omega
    have hremNext : edges.length - rem = j + 1 := by dsimp only [j]; omega
    let ei := (edges[j]'hjLt).1
    have heiMem : ei ∈ edges.map Prod.fst := List.mem_map.mpr ⟨edges[j]'hjLt, List.getElem_mem hjLt, rfl⟩
    obtain ⟨heiCap, herW, hioW, hrecEndW⟩ := heiBound ei heiMem
    obtain ⟨hmemRec, hvalAt⟩ := hrec ei heiMem
    have hmemEi : st.mem (edgesBase + 2 * j) = ei := (hedges.read hjLt).1
    let recPtr := address ei
    let s1 : State := { st with regs := Function.update st.regs 9 ei }
    let s2 : State := { s1 with regs := Function.update s1.regs 10 recPtr }
    have r1 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))))
        st .normal s1 7 :=
      runs_assign_iff.mpr ⟨ei, by
        simp [Expr.eval, BinOp.eval, hr1, hr8, show 2 < 2 ^ w by omega, show 2 * j < 2 ^ w by omega,
          show edgesBase + 2 * j < 2 ^ w by omega, hmemEi], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.reg 9)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨recPtr, by
        simp [Expr.eval, BinOp.eval, s1, hr6, herW, hmemRec, recPtr], rfl, rfl, rfl⟩
    have holEnd : offReadyList + intCap ≤ 2 ^ w := by
      have := holW (intCap - 1) (by omega); omega
    obtain ⟨cPush, stP, cnt1, hrPush, hcPush, hcnt1Cases, hm11_1, hmER_1, hoff1, hdet1, hioMono1, hfrP⟩ :=
      offTreePushBody_runs (w := w) (ω := ω) (pos := s2.pos) (val := newVal ei) tag
        hIsNeg hoff heiCap hm10 hm11 hm12 hm13 hvalAt ht1 (ht13 ei heiCap) ht14 ht15
        (ht18 ei heiMem) hw13 hroot13W herW hioW holEnd hcapW hrecEndW hLW
    let s3 : State := { regs := Function.update s2.regs 11 0, mem := stP.mem, pos := stP.pos }
    have r3 : Runs w p ω (.call 11 offTreePush [.reg 0, .reg 9, .reg 10, .reg 4]) s2 .normal s3 (cPush + 5) :=
      runs_call_iff.mpr ⟨[root, ei, recPtr, L], offTreePushBody isNeg, .returned 0, stP, cPush,
        by simp [evalArgs, Expr.eval, s2, s1, hr0, hr4], hPush, hrPush, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    let s4 : State := { s3 with regs := Function.update s3.regs 8 (j + 1) }
    have rInc : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) s3 .normal s4 4 :=
      runs_assign_iff.mpr ⟨j + 1, by
        simp [Expr.eval, BinOp.eval, s3, s2, s1, hr8, show 1 < 2 ^ w by omega,
          show j + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hstepRun : Runs w p ω
        ((.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))) ;;
          .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
          .call 11 offTreePush [.reg 0, .reg 9, .reg 10, .reg 4]) ;;
         .assign 8 (.bin .add (.reg 8) (.const 1))) st .normal s4 ((7 + (5 + (cPush + 5) + 1) + 1) + 4 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s3, 7 + (5 + (cPush + 5) + 1) + 1, 4,
        runs_seq_iff.mpr (Or.inr ⟨s1, 7, 5 + (cPush + 5) + 1, r1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 5, cPush + 5, r2, r3, rfl⟩), rfl⟩), rInc, rfl⟩)
    -- Frame facts for `s4.mem = stP.mem`
    have hcnt1Bounds : cnt ≤ cnt1 ∧ cnt1 ≤ cnt + 1 := by rcases hcnt1Cases with rfl | rfl <;> omega
    have hfrAll (a : ℕ) (h11 : a ≠ root + 11) (h14 : tag a ≠ 14) (h15 : tag a ≠ 15) :
        s4.mem a = st.mem a := by
      by_cases haEr : a = edgeRecords + ei
      · subst haEr; exact hmER_1.trans hmemRec.symm
      · exact hfrP a haEr (fun h => h15 (h ▸ ht15 ei heiCap))
          (fun hinc h => h14 (h ▸ ht14 cnt (by have := hoff1.1; omega))) h11
    have hfrRoot (x : ℕ) (hx : x < 14) (hne11 : x ≠ 11) : s4.mem (root + x) = st.mem (root + x) :=
      hfrAll (root + x) (by omega) (by rw [ht1 x hx]; decide) (by rw [ht1 x hx]; decide)
    have hedges1 : ExplicitEdgesAt s4.mem edgesBase edges := hedges.congr fun x hx1 hx2 => by
      have htx : tag x = 0 := by rw [show x = edgesBase + (x - edgesBase) by omega]; exact htEdges _ (by omega)
      exact hfrAll x (fun h => by rw [h, ht1 11 (by omega)] at htx; omega)
        (by rw [htx]; decide) (by rw [htx]; decide)
    have hrec1 : ∀ e' ∈ edges.map Prod.fst, s4.mem (edgeRecords + e') = address e' ∧
        PathEdgeAt s4.mem (address e') 4 L (some (newVal e')) := fun e' he' => by
      have h13e := ht13 e' (heiBound e' he').1
      refine ⟨(hfrAll _ (fun h => by rw [h, ht1 11 (by omega)] at h13e; omega)
          (by rw [h13e]; decide) (by rw [h13e]; decide)).trans (hrec e' he').1,
        (hrec e' he').2.congr (fun a ha1 ha2 => by
          have haIdx : a = address e' + (a - address e') := by omega
          have ht18a : tag a = 18 := by rw [haIdx]; exact ht18 e' he' (a - address e') (by omega)
          exact hfrAll a (fun h => by rw [h, ht1 11 (by omega)] at ht18a; omega)
            (by rw [ht18a]; decide) (by rw [ht18a]; decide))⟩
    have hprev1 : ∀ k (hk : k < edges.length), k < j + 1 →
        0 ≤ (newVal (edges[k]'hk).1).detector → s4.mem (inOffReady + (edges[k]'hk).1) = 1 := by
      intro k hk hkj hdet
      by_cases hkeq : k = j
      · subst hkeq; exact hdet1 hdet
      · have hkeMem : (edges[k]'hk).1 ∈ edges.map Prod.fst :=
          List.mem_map.mpr ⟨edges[k]'hk, List.getElem_mem hk, rfl⟩
        exact hioMono1 _ (heiBound _ hkeMem).1 (hprev k hk (by omega) hdet)
    -- Recurse on `rem`
    obtain ⟨out, cRest, cnt', hrRest, hcRest, hret7, hcntLe2, hcntHi2, hm11_2, hoff2, hdetAll,
        hfrAll2, hioMono2, hioPres2⟩ :=
      ih s4 cnt1 (by omega)
        (by simp [s4, s3, s2, s1, hr0]) (by simp [s4, s3, s2, s1, hr1])
        (by simp [s4, s3, s2, s1, hr2]) (by simp [s4, s3, s2, s1, hr4])
        (by simp [s4, s3, s2, s1, hr6]) (by simp [s4, s3, s2, s1, hr7])
        (by simp [s4, hremNext])
        ((hfrRoot 10 (by omega) (by decide)).trans hm10) hm11_1
        ((hfrRoot 12 (by omega) (by decide)).trans hm12)
        ((hfrRoot 13 (by omega) (by decide)).trans hm13)
        hoff1 hedges1 hrec1 (by simp only [hremNext]; exact hprev1)
    have hcond1 : (Expr.bin .lt (.reg 8) (.reg 2)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hr8, hr2, hjLt, show 1 < 2 ^ w by omega]
    have hrLoop : Runs w p ω
        (.loop (.bin .lt (.reg 8) (.reg 2))
          ((.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))) ;;
            .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
            .call 11 offTreePush [.reg 0, .reg 9, .reg 10, .reg 4]) ;;
           .assign 8 (.bin .add (.reg 8) (.const 1))))
        st .normal out (3 + ((7 + (5 + (cPush + 5) + 1) + 1) + 4 + 1) + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s4, _, cRest, hcond1, by decide, hstepRun, hrRest,
        by simp [Expr.size]⟩))
    refine ⟨out, _, cnt', hrLoop, by rw [Nat.add_mul, one_mul]; omega, hret7,
      by omega, by omega, hm11_2, hoff2, hdetAll,
      fun a h11 h14 h15 => (hfrAll2 a h11 h14 h15).trans (hfrAll a h11 h14 h15),
      fun k hk h1 => hioMono2 k hk (hioMono1 k hk h1),
      fun k hk hnot => (hioPres2 k hk hnot).trans (hfrP (inOffReady + k)
        (fun h => by have h1 := ht13 ei heiCap; have h2 := ht15 k hk; rw [h] at h2; omega)
        (fun h => hnot ((show k = ei by omega) ▸ heiMem))
        (fun _ h => by have h1 := ht14 cnt (by have := hoff1.1; omega); have h2 := ht15 k hk; rw [h] at h2; omega)
        (fun h => by have h1 := ht1 11 (by omega); have h2 := ht15 k hk; rw [h] at h2; omega))⟩

/-- End-to-end execution of `updateGoodApplyOffTreeBody`: updates all explicit off-tree edge
records in-place and pushes every newly ready off-tree edge onto `offReadyList`, maintaining
`OffReadyInv` and leaving all other tagged regions intact. -/
theorem updateGoodApplyOffTreeBody_runs
    {w L drainUnit explicitRouteUpdate offTreePush isNeg root edgesBase multPtr heap pos : ℕ}
    {handle table levelsEnd forward inverse freshCounter slots names slotThresholds
      edgeThresholds edgeRecords offReadyCount offReadyList inOffReady rootGraph intCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {edges : List (ℕ × Bool)} {address : ℕ → ℕ} {old : ℕ → PathEdgeValue} {mult : ℤ}
    (tag : ℕ → ℕ)
    (hRoute : MeetsContract w p explicitRouteUpdate
      (explicitEdgeRouteUpdateContract w 4 L edgesBase edgeRecords heap multPtr edges address old mult))
    (hPush : p.procs[offTreePush]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hrootDir : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter
      slots names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList
      inOffReady rootGraph intCap)
    (hoffReady : OffReadyInv mem offReadyCount offReadyList inOffReady intCap)
    (hltH : ∀ {a v : ℕ}, tag a = v → v ≠ 0 → a < heap)
    (t1 : ∀ j < 16, tag (root + j) = 1)
    (t13 : ∀ k < intCap, tag (edgeRecords + k) = 13)
    (t14 : ∀ k < intCap, tag (offReadyList + k) = 14)
    (t15 : ∀ k < intCap, tag (inOffReady + k) = 15)
    (hedgesEnd : edgesBase + 2 * edges.length ≤ heap)
    (hmultEnd : multPtr + L ≤ heap)
    (htEdges : ∀ x < 2 * edges.length, tag (edgesBase + x) = 0)
    (hedgesAt : ExplicitEdgesAt mem edgesBase edges)
    (hmultAt : PathIntAt mem multPtr 4 L mult)
    (haddr : ∀ ei ∈ edges.map Prod.fst, ei < intCap ∧
      mem (edgeRecords + ei) = address ei ∧
      PathEdgeAt mem (address ei) 4 L (some (old ei)) ∧
      (∀ x < 2 + 4 * L, tag (address ei + x) = 18))
    (hz : ZeroFrom mem heap)
    (hcapPos : 0 < intCap)
    (hw13 : 13 < 2 ^ w) (hLW : L < 2 ^ w)
    (hroom : heap + explicitRouteSpace L edges.length + 2 < 2 ^ w) :
    ∃ ret cost out cnt',
      Runs w p ω (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush)
        (startState [root, edgesBase, edges.length, multPtr, L, heap] mem pos)
        (.returned ret) out cost ∧
      heap + edges.length ≤ ret ∧ ret ≤ heap + explicitRouteSpace L edges.length ∧
      offReadyCount ≤ cnt' ∧ cnt' ≤ offReadyCount + edges.length ∧
      out.mem (root + 11) = cnt' ∧
      OffReadyInv out.mem cnt' offReadyList inOffReady intCap ∧
      (∀ ei ∈ edges.map Prod.fst,
        PathEdgeAt out.mem (address ei) 4 L (some (updatedOffTreeVal edges old mult ei)) ∧
        (0 ≤ (updatedOffTreeVal edges old mult ei).detector → out.mem (inOffReady + ei) = 1)) ∧
      ZeroFrom out.mem ret ∧
      (∀ a < heap, tag a ≠ 1 → tag a ≠ 14 → tag a ≠ 15 → tag a ≠ 18 →
        out.mem a = mem a) ∧
      (∀ a < heap, (∀ ei ∈ edges.map Prod.fst, a < address ei + 2 + 2 * L ∨ address ei + 2 + 4 * L ≤ a) →
        tag a ≠ 1 → tag a ≠ 14 → tag a ≠ 15 → out.mem a = mem a) ∧
      (∀ j < 16, j ≠ 11 → out.mem (root + j) = mem (root + j)) ∧
      (∀ j < intCap, mem (inOffReady + j) = 1 → out.mem (inOffReady + j) = 1) ∧
      (∀ j < intCap, j ∉ edges.map Prod.fst → out.mem (inOffReady + j) = mem (inOffReady + j)) ∧
      cost + cnt' * drainUnit ≤
        edges.length * (136 * edges.length + 152 * L ^ 2 + 561 * L + drainUnit + 960) + 80 +
        offReadyCount * drainUnit := by
  have hheapW : heap < 2 ^ w := by dsimp only [explicitRouteSpace] at hroom; omega
  have hroot13W : root + 13 < 2 ^ w := lt_trans (hltH (t1 13 (by omega)) (by decide)) hheapW
  have hcapW : intCap < 2 ^ w := by
    have := hltH (t14 (intCap - 1) (by omega)) (by decide); omega
  have holW : ∀ k < intCap, offReadyList + k < 2 ^ w :=
    fun k hk => lt_trans (hltH (t14 k hk) (by decide)) hheapW
  have hm10 : mem (root + 10) = edgeRecords := by simpa using hrootDir 10 (by simp)
  have hm11 : mem (root + 11) = offReadyCount := by simpa using hrootDir 11 (by simp)
  have hm12 : mem (root + 12) = offReadyList := by simpa using hrootDir 12 (by simp)
  have hm13 : mem (root + 13) = inOffReady := by simpa using hrootDir 13 (by simp)
  have herBaseW : edgeRecords < 2 ^ w := by
    have := hltH (t13 0 (by omega)) (by decide); omega
  let s0 := startState [root, edgesBase, edges.length, multPtr, L, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 6 edgeRecords }
  have r1 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 10)))) s0 .normal s1 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by
      simp [Expr.eval, BinOp.eval, s0, startState, show 10 < 2 ^ w by omega,
        show root + 10 < 2 ^ w by omega, hm10], rfl, rfl, rfl⟩
  -- Step 1: call `explicitRouteUpdate [edgesBase, edges.length, edgeRecords, heap, multPtr, L]`
  have hroutePre : (explicitEdgeRouteUpdateContract w 4 L edgesBase edgeRecords heap multPtr edges address old mult).pre
      [edgesBase, edges.length, edgeRecords, heap, multPtr, L] s1.mem := by
    refine ⟨rfl, ⟨edgesBase, edgeRecords, heap, rfl, hedgesAt, hedgesEnd,
        fun ei hei => ⟨hltH (t13 ei (haddr ei hei).1) (by decide), (haddr ei hei).2.1⟩,
        by dsimp only [explicitRouteSpace] at hroom; omega⟩,
      hmultAt, hz, fun ei hei => (haddr ei hei).2.2.1,
      by dsimp only [explicitRouteSpace] at hroom; omega⟩
  obtain ⟨bR, hbR, oR, stR, cR, hrR, ⟨hretLo, hzR, hprefR, hretHi, hfrR⟩, hcR⟩ :=
    hRoute [edgesBase, edges.length, edgeRecords, heap, multPtr, L] s1.mem s1.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hroutePre
  change cR ≤ edges.length * (136 * edges.length + 152 * L ^ 2 + 561 * L + 825) + 40 at hcR
  let ret := oR.value
  let s2 : State := { regs := Function.update s1.regs 7 ret, mem := stR.mem, pos := stR.pos }
  have r2 : Runs w p ω (.call 7 explicitRouteUpdate [.reg 1, .reg 2, .reg 6, .reg 5, .reg 3, .reg 4])
      s1 .normal s2 (cR + 7) :=
    runs_call_iff.mpr ⟨[edgesBase, edges.length, edgeRecords, heap, multPtr, L], bR, oR, stR, cR,
      by simp [evalArgs, Expr.eval, s1, s0, startState], hbR, hrR, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  let s3 : State := { s2 with regs := Function.update s2.regs 8 0 }
  have r3 : Runs w p ω (.assign 8 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Transfer memory facts across `explicitRouteUpdate` (which only modifies tag-18 flow/detector slices below `heap`)
  have hfrNot18 (a : ℕ) (ha : a < heap) (hnt18 : tag a ≠ 18) : s3.mem a = mem a :=
    hfrR a ha fun ei hei => by
      by_contra h
      push Not at h
      have ht18a := (haddr ei hei).2.2.2 (a - address ei) (by omega)
      rw [show address ei + (a - address ei) = a by omega] at ht18a
      exact hnt18 ht18a
  have hfrTag (a v : ℕ) (ht : tag a = v) (hv0 : v ≠ 0) (hv18 : v ≠ 18) : s3.mem a = mem a :=
    hfrNot18 a (hltH ht hv0) (fun h => hv18 (ht.symm.trans h))
  have hoff3 : OffReadyInv s3.mem offReadyCount offReadyList inOffReady intCap := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hoffReady
    have hol (j : ℕ) (hj : j < intCap) : s3.mem (offReadyList + j) = mem (offReadyList + j) :=
      hfrTag _ 14 (t14 j hj) (by decide) (by decide)
    have hio (j : ℕ) (hj : j < intCap) : s3.mem (inOffReady + j) = mem (inOffReady + j) :=
      hfrTag _ 15 (t15 j hj) (by decide) (by decide)
    refine ⟨h1, fun j hj => by rw [hol j (lt_of_lt_of_le hj h1), hio _ (h2 j hj).1]; exact h2 j hj,
      fun j₁ hj₁ j₂ hj₂ hne => by
        rw [hol j₁ (lt_of_lt_of_le hj₁ h1), hol j₂ (lt_of_lt_of_le hj₂ h1)]; exact h3 j₁ hj₁ j₂ hj₂ hne,
      fun k hk => by rw [hio k hk]; exact h4 k hk,
      fun k hk h1' => by
        rw [hio k hk] at h1'
        obtain ⟨j, hj, hje⟩ := h5 k hk h1'
        exact ⟨j, hj, (hol j (lt_of_lt_of_le hj h1)).trans hje⟩⟩
  have hedges3 : ExplicitEdgesAt s3.mem edgesBase edges := hedgesAt.congr fun x hx1 hx2 =>
    hfrNot18 x (by omega) (by rw [show x = edgesBase + (x - edgesBase) by omega, htEdges _ (by omega)]; decide)
  have hrec3 : ∀ ei ∈ edges.map Prod.fst, s3.mem (edgeRecords + ei) = address ei ∧
      PathEdgeAt s3.mem (address ei) 4 L (some (updatedOffTreeVal edges old mult ei)) := fun ei hei =>
    ⟨(hfrTag _ 13 (t13 ei (haddr ei hei).1) (by decide) (by decide)).trans (haddr ei hei).2.1,
     explicitEdgePrefixAt_done hprefR ei hei⟩
  -- Step 2: run `offTreePushLoop_runs`
  obtain ⟨out, cLoop, cnt', hrLoop, hcLoop, hret7, hcntLo, hcntHi, hm11', hoff', hdetAll,
      hfrLoop, hioMono, hioPres⟩ :=
    offTreePushLoop_runs (w := w) (ω := ω) (heapRet := ret) (address := address)
      (newVal := updatedOffTreeVal edges old mult)
      tag hPush hIsNeg hw13 hroot13W hcapW hLW holW (by dsimp only [explicitRouteSpace] at hroom; omega)
      (by omega) (fun j hj => t1 j (by omega)) t13 t14 t15
      (fun ei hei => (haddr ei hei).2.2.2) htEdges
      (fun ei hei => ⟨(haddr ei hei).1, lt_trans (hltH (t13 ei (haddr ei hei).1) (by decide)) hheapW,
        lt_trans (hltH (t15 ei (haddr ei hei).1) (by decide)) hheapW,
        by have hlast := hltH ((haddr ei hei).2.2.2 (2 + 4 * L - 1) (by omega)) (by decide); omega⟩)
      edges.length s3 offReadyCount le_rfl
      (by simp [s3, s2, s1, s0, startState]) (by simp [s3, s2, s1, s0, startState])
      (by simp [s3, s2, s1, s0, startState]) (by simp [s3, s2, s1, s0, startState])
      (by simp [s3, s2, s1]) (by simp [s3, s2]) (by simp [s3])
      ((hfrTag _ 1 (t1 10 (by omega)) (by decide) (by decide)).trans hm10)
      ((hfrTag _ 1 (t1 11 (by omega)) (by decide) (by decide)).trans hm11)
      ((hfrTag _ 1 (t1 12 (by omega)) (by decide) (by decide)).trans hm12)
      ((hfrTag _ 1 (t1 13 (by omega)) (by decide) (by decide)).trans hm13)
      hoff3 hedges3 hrec3 (fun _ _ h0 _ => by omega)
  have rRet : Runs w p ω (.ret (.reg 7)) out (.returned ret) out 2 :=
    runs_ret_iff.mpr ⟨ret, by simp [Expr.eval, hret7], rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush) s0
      (.returned ret) out (5 + ((cR + 7) + ((2 + cLoop + 1) + 2 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cR + 7, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨out, 2 + cLoop + 1, 2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, cLoop, r3, hrLoop, rfl⟩), rRet, rfl⟩), rfl⟩), rfl⟩)
  have hgeRetTag0 (a : ℕ) (ha : ret ≤ a) : tag a = 0 := by
    by_contra hnz
    have := hltH rfl hnz
    omega
  refine ⟨ret, _, out, cnt', hrFull, hretLo, by dsimp only [explicitRouteSpace]; omega, hcntLo, hcntHi, hm11', hoff', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ei hei
    refine ⟨(hrec3 ei hei).2.congr (fun a ha1 ha2 => by
        have haIdx : a = address ei + (a - address ei) := by omega
        have ht18a : tag a = 18 := by rw [haIdx]; exact (haddr ei hei).2.2.2 (a - address ei) (by omega)
        exact hfrLoop a (fun h => by rw [h, t1 11 (by omega)] at ht18a; omega)
          (by rw [ht18a]; decide) (by rw [ht18a]; decide)),
      hdetAll ei hei⟩
  · intro a ha
    have ht0 := hgeRetTag0 a ha
    exact (hfrLoop a (fun h => by rw [h, t1 11 (by omega)] at ht0; omega)
      (by rw [ht0]; decide) (by rw [ht0]; decide)).trans (hzR a ha)
  · intro a ha h1 h14 h15 h18
    exact (hfrLoop a (fun h => h1 (h ▸ t1 11 (by omega))) h14 h15).trans (hfrNot18 a ha h18)
  · intro a ha hout h1 h14 h15
    exact (hfrLoop a (fun h => h1 (h ▸ t1 11 (by omega))) h14 h15).trans (hfrR a ha hout)
  · intro j hj hne11
    exact (hfrLoop (root + j) (by omega) (by rw [t1 j hj]; decide) (by rw [t1 j hj]; decide)).trans
      (hfrTag _ 1 (t1 j hj) (by decide) (by decide))
  · intro j hj h1
    exact hioMono j hj ((hfrTag _ 15 (t15 j hj) (by decide) (by decide)).trans h1)
  · intro j hj hnot
    exact (hioPres j hj hnot).trans (hfrTag _ 15 (t15 j hj) (by decide) (by decide))
  · have hmul : cnt' * drainUnit ≤ (offReadyCount + edges.length) * drainUnit :=
      Nat.mul_le_mul_right drainUnit hcntHi
    rw [Nat.add_mul] at hmul
    simp only [Nat.mul_add] at hcR ⊢
    omega

end MinCostFlow.MinRatio
