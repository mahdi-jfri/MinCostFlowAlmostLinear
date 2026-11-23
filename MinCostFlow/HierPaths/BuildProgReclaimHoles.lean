module

public import MinCostFlow.HierPaths.BuildProgSec01
public import MinCostFlow.HierPaths.BuildProgZero
import MinCostFlow.HierPaths.InitLayout

/-!
# Collecting zero-filled position-array holes and reclaiming scratch memory

Pass C of the non-singleton level builder compacts `sec0 ++ sec1` from `[outStart, end1)` down to
`[h + 4, h + 4 + (end1 - outStart))` using `buildCopyProc` (`buildCopyDownContract`) and then
zeroes `[h + 4 + (end1 - outStart), end1 + numHoles)` while skipping the `≤ limit + 1` disjoint
`G.n`-word zero holes left by the routed rounds and final injection. Because every skipped hole is
already zero in memory, the final memory satisfies `ZeroFrom after (h + 4 + (end1 - outStart))`
and the total running time is independent of `G.n`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Sorted, pairwise-disjoint zero holes of length `gn` inside `[lo, hi)`. -/
def HolesValid (gn lo hi : ℕ) (holes : List ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ i (hi' : i < holes.length),
    lo ≤ holes[i]'hi' ∧ holes[i]'hi' + gn ≤ hi ∧ ∀ a < gn, mem (holes[i]'hi' + a) = 0) ∧
  (∀ i (hi' : i + 1 < holes.length), holes[i]'(by omega) + gn ≤ holes[i + 1]'hi')

/-- Cursor after processing the first `i` holes in `buildReclaimHolesProc`. -/
def reclaimCur (holes : List ℕ) (gn start0 : ℕ) : ℕ → ℕ
  | 0 => start0
  | i + 1 => max (reclaimCur holes gn start0 i) (holes.getD i 0 + gn)

/-- Number of words zeroed before hole `i` in `buildReclaimHolesProc`. -/
def reclaimGap (holes : List ℕ) (gn start0 : ℕ) (i : ℕ) : ℕ :=
  holes.getD i 0 - reclaimCur holes gn start0 i

/-- Scan the round directory and final injection reply to list all position-array hole starts at
`dst`, returning `numHoles ≤ limit + 1`.
Args: `[directory, limit, s, k, d, heap1, dst]`. -/
def buildCollectHolesProc : Stmt :=
  .assign 7 (.const 0) ;;
  forRange 8 (.const 0) (.reg 1)
    (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
     .cond (.reg 9)
       (.assign 10 (.load (.reg 9)) ;;
        .assign 11 (.load (.bin .add (.reg 9) (.const 1))) ;;
        .assign 12 (.load (.reg 10)) ;;
        .cond (.reg 12)
          (.assign 13 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 11)) ;;
           .assign 14 (.bin .add (.bin .add (.bin .add (.reg 13) (.bin .add (.reg 12) (.reg 12))) (.const 1))
                         (.bin .mul (.reg 12) (.reg 2))) ;;
           .assign 15 (.bin .add (.bin .add (.reg 14) (.const 4)) (.load (.bin .add (.reg 14) (.const 1)))) ;;
           .assign 16 (.load (.reg 13)) ;;
           .assign 17 (.bin .div (.load (.bin .add (.reg 15) (.reg 12))) (.const 2)) ;;
           .assign 18 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 16) (.const 4)) (.reg 17)) (.reg 4)) (.const 1)) ;;
           .store (.bin .add (.reg 6) (.reg 7)) (.reg 18) ;;
           .assign 7 (.bin .add (.reg 7) (.const 1)))
          .nop)
       .nop) ;;
  .assign 14 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 5) (.reg 2))
                (.bin .add (.reg 3) (.reg 3))) (.const 1)) (.bin .mul (.reg 3) (.reg 2))) ;;
  .assign 15 (.bin .add (.bin .add (.reg 14) (.const 4)) (.load (.bin .add (.reg 14) (.const 1)))) ;;
  .assign 16 (.load (.reg 5)) ;;
  .assign 17 (.bin .div (.load (.bin .add (.reg 15) (.reg 3))) (.const 2)) ;;
  .assign 18 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 16) (.const 4)) (.reg 17)) (.reg 4)) (.const 1)) ;;
  .store (.bin .add (.reg 6) (.reg 7)) (.reg 18) ;;
  .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
  .ret (.reg 7)

theorem buildCollectHolesProc_noRand : buildCollectHolesProc.NoRand := by
  simp [buildCollectHolesProc, forRange, forUp, Stmt.NoRand]

/-- Contract for collecting the sorted zero-hole list above `end1`. -/
def buildCollectHolesContract (w : ℕ) (D : ChoiceLoopData) (slot slotWords heap₁ injEnd : ℕ)
    (sts : ℕ → ChildState) (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : Contract where
  pre args mem := ∃ dst mem₀,
    args = [D.directory, D.limit, D.base.childSize, D.count, D.base.pathBound, heap₁, dst] ∧
    D.directory + D.limit ≤ injEnd ∧ injEnd ≤ dst ∧
    (∀ a < injEnd, mem a = mem₀ a) ∧
    TraceRoundsMem D D.limit heap₁ sts mem₀ ∧
    InjArchive D.base.host D.base.childSize D.count D.base.pathBound (roundRouteCap D) slot slotWords
      heap₁ injEnd F (fun c => (sts c).rounds.flatten.map Prod.snd) mem₀ ∧
    ZeroFrom mem dst ∧ dst + D.limit + 1 < 2 ^ w ∧ 4 < 2 ^ w
  post args mem v after := ∃ dst holes,
    args = [D.directory, D.limit, D.base.childSize, D.count, D.base.pathBound, heap₁, dst] ∧
    v = holes.length ∧ 1 ≤ v ∧ v ≤ D.limit + 1 ∧
    ListAt after dst holes ∧
    HolesValid D.base.host.n D.addrs.heap injEnd holes after ∧
    injEnd ≤ D.addrs.heap + (D.limit + 1) * roundNonHoleCap D.base.childSize D.count D.base.pathBound +
      D.limit * (roundCoreCap D + roundRouteCap D) + roundRouteCap D + v * D.base.host.n ∧
    (∀ a < dst, after a = mem a) ∧ ZeroFrom after (dst + v)
  cost _ _ := 120 * D.limit + 160

/-- Copy `[outStart, end1)` down to `[h + 4, h + 4 + (end1 - outStart))` and zero the rest up to
`holesAddr + numHoles` skipping the sorted zero holes at `holesAddr`. Returns `h + 4 + (end1 - outStart)`.
Args: `[h, outStart, end1, holesAddr, numHoles, gn]`. -/
def buildReclaimHolesProc (fCopy fZero : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 7 (.bin .sub (.reg 2) (.reg 1)) ;;
  .call 8 fCopy [.reg 1, .reg 7, .reg 6] ;;
  .assign 9 (.bin .add (.reg 6) (.reg 7)) ;;
  forRange 10 (.const 0) (.reg 4)
    (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
     .cond (.bin .lt (.reg 9) (.reg 11))
       (.call 8 fZero [.reg 9, .bin .sub (.reg 11) (.reg 9)] ;;
        .assign 9 (.reg 11))
       .nop ;;
     .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
     .cond (.bin .lt (.reg 9) (.reg 12))
       (.assign 9 (.reg 12))
       .nop) ;;
  .cond (.bin .lt (.reg 9) (.reg 2))
    (.call 8 fZero [.reg 9, .bin .sub (.reg 2) (.reg 9)])
    .nop ;;
  .call 8 fZero [.reg 3, .reg 4] ;;
  .ret (.bin .add (.reg 6) (.reg 7))

theorem buildReclaimHolesProc_noRand (fCopy fZero : ℕ) :
    (buildReclaimHolesProc fCopy fZero).NoRand := by
  simp [buildReclaimHolesProc, forRange, forUp, Stmt.NoRand]

/-- Contract for compacting `sec0 ++ sec1` down to `h + 4` and reclaiming scratch in time
independent of `gn`. -/
def buildReclaimHolesContract (w gn : ℕ) (payload : List ℕ) (holes : List ℕ) : Contract where
  pre args mem := ∃ h outStart end1,
    args = [h, outStart, end1, end1, holes.length, gn] ∧
    h + 4 ≤ outStart ∧ end1 = outStart + payload.length ∧
    ListAt mem outStart payload ∧
    ListAt mem end1 holes ∧
    HolesValid gn h outStart holes mem ∧
    ZeroFrom mem (end1 + holes.length) ∧
    end1 + holes.length < 2 ^ w ∧ 4 < 2 ^ w
  post args mem v after := ∃ h outStart end1,
    args = [h, outStart, end1, end1, holes.length, gn] ∧
    v = h + 4 + payload.length ∧
    ListAt after (h + 4) payload ∧
    (∀ a < h, after a = mem a) ∧ ZeroFrom after v
  cost args _ :=
    let h := args.getD 0 0
    let outStart := args.getD 1 0
    let end1 := args.getD 2 0
    let m := args.getD 4 0
    17 * (end1 - outStart) + 15 * (end1 - h - m * gn) + 125 * m + 200

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem routeMatched_flatten_offset {mem : ℕ → ℕ} {rep : ℕ} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (hAt : ListAt mem rep (routeResultWords (.matched Ms emb))) :
    mem (rep + 1) = 1 ∧
    mem (rep + 5 + Ms.length) = 2 * Ms.flatten.length ∧
    Ms.length + 6 + 2 * Ms.flatten.length ≤ (routeResultWords (.matched Ms emb)).length := by
  let bs : List (List ℕ) :=
    [[0], csrList Ms.length (matchingRowWords Ms), csrList Ms.flatten.length emb]
  have hAt' : ListAt mem rep (layoutList bs) := hAt
  have hOff1 : mem (rep + 1) = 1 := by
    have h1 := csrList_offset hAt' (show 1 ≤ 3 by omega)
    simpa [bs, List.range_succ, List.getD_cons_zero] using h1
  have hMtAt : ListAt mem (rep + 5) (csrList Ms.length (matchingRowWords Ms)) := by
    have h1 := listAt_csrList_get hAt' (show 1 < bs.length by simp [bs])
    simpa [bs, List.range_succ, List.getD_cons_zero, List.getD_cons_succ] using h1
  have hSum : ((List.range Ms.length).map fun i => (matchingRowWords Ms i).length).sum =
      2 * Ms.flatten.length := by
    have hgen : ∀ n ≤ Ms.length,
        ((List.range n).map fun i => (matchingRowWords Ms i).length).sum =
          2 * (Ms.take n).flatten.length := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, ih (Nat.le_of_succ_le hn), length_matchingRowWords,
          List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
          List.flatten_singleton, List.getD_eq_getElem _ _ hn]
        omega
    simpa using hgen Ms.length le_rfl
  have hMtEnd : mem (rep + 5 + Ms.length) = 2 * Ms.flatten.length := by
    rw [csrList_offset hMtAt le_rfl, hSum]
  have hLen : Ms.length + 6 + 2 * Ms.flatten.length ≤ (routeResultWords (.matched Ms emb)).length := by
    change Ms.length + 6 + 2 * Ms.flatten.length ≤ (layoutList bs).length
    rw [length_layoutList]
    simp only [bs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have h1 : (csrList Ms.length (matchingRowWords Ms)).length =
        Ms.length + 1 + 2 * Ms.flatten.length := by
      rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq, hSum]
    omega
  exact ⟨hOff1, hMtEnd, hLen⟩

private theorem holesValid_append {gn lo hi1 hi2 p : ℕ} {holes : List ℕ} {mem : ℕ → ℕ}
    (hV : HolesValid gn lo hi1 holes mem) (hlo : lo ≤ hi1) (hp1 : hi1 ≤ p) (hp2 : p + gn ≤ hi2)
    (hZ : ∀ a < gn, mem (p + a) = 0) :
    HolesValid gn lo hi2 (holes ++ [p]) mem := by
  constructor
  · intro i hi'
    rw [List.length_append, List.length_singleton] at hi'
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | heq
    · rw [List.getElem_append_left hlt]
      obtain ⟨h1, h2, h3⟩ := hV.1 i hlt
      exact ⟨h1, by omega, h3⟩
    · subst heq
      rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      exact ⟨hlo.trans hp1, hp2, hZ⟩
  · intro i hi'
    rw [List.length_append, List.length_singleton] at hi'
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | heq
    · have hi1' : i < holes.length := by omega
      rw [List.getElem_append_left hi1', List.getElem_append_left hlt]
      exact hV.2 i hlt
    · have hiL : i + 1 = holes.length := heq
      have hi1' : i < holes.length := by omega
      rw [List.getElem_append_left hi1', List.getElem_append_right (by omega)]
      simp only [show i + 1 - holes.length = 0 by omega, List.getElem_singleton]
      exact (hV.1 i hi1').2.1.trans hp1

private theorem holesValid_congr {gn lo hi : ℕ} {holes : List ℕ} {mem after : ℕ → ℕ}
    (hV : HolesValid gn lo hi holes mem) (hEq : ∀ a < hi, after a = mem a) :
    HolesValid gn lo hi holes after :=
  ⟨fun i hi' =>
    ⟨(hV.1 i hi').1, (hV.1 i hi').2.1, fun a ha =>
      (hEq _ (by have := (hV.1 i hi').2.1; omega)).trans ((hV.1 i hi').2.2 a ha)⟩,
   hV.2⟩


/-- `buildCollectHolesProc` meets `buildCollectHolesContract`. -/
theorem buildCollectHolesProc_meetsContract {w f : ℕ} {p : Program}
    {D : ChoiceLoopData} {slot slotWords heap₁ injEnd : ℕ}
    {sts : ℕ → ChildState} {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hf : p.procs[f]? = some buildCollectHolesProc) :
    MeetsContract w p f (buildCollectHolesContract w D slot slotWords heap₁ injEnd sts F) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨dst, mem₀, rfl, hDirLe, hInjDst, hMemEq, hTrace, hInj, hZF, htop, hw4⟩ := hPre
  obtain ⟨_, bounds, walks, holesOpt, hb0, hbt, hbMono, hArch₀, _⟩ := hTrace
  obtain ⟨Ms, emb, routedEnd, hMlen, _, hloRep, hMemHeap₀, hRepEndLe, hEndInj, hRepAt₀,
    hHeapLeP, hPInj, hZeroP₀, _, _, _, hInjSize, _⟩ := hInj
  have hBoundsGe (r : ℕ) (hr : r ≤ D.limit) : D.addrs.heap ≤ bounds r := by
    induction r with
    | zero => rw [hb0]
    | succ r ih => exact (ih (Nat.le_of_succ_le hr)).trans (hbMono r hr)
  have hBoundsLe (r : ℕ) (hr : r ≤ D.limit) : bounds r ≤ heap₁ := by
    have hgen : ∀ d, r + d ≤ D.limit → bounds r ≤ bounds (r + d) := by
      intro d; induction d with
      | zero => intro _; simp
      | succ d ih => intro hle; exact (ih (by omega)).trans (hbMono (r + d) (by omega))
    have h1 := hgen (D.limit - r) (by omega)
    rw [Nat.add_sub_of_le hr, hbt] at h1; exact h1
  have hHeapLeInj : heap₁ ≤ injEnd := by omega
  have hArch : ∀ r < D.limit, RoundArchive D.base.host D.first D.base.childSize D.count
      D.base.pathBound (roundCoreCap D + roundRouteCap D) mem (bounds r) (bounds (r + 1)) (mem (D.directory + r))
      (walks r) (holesOpt r) := fun r hr => by
    rw [hMemEq (D.directory + r) (by omega)]
    exact (hArch₀ r hr).frame fun a _ ha => hMemEq a (ha.trans_le ((hBoundsLe (r + 1) hr).trans hHeapLeInj))
  have hRepAt : ListAt mem (injectReplyBase heap₁ D.count D.base.childSize)
      (routeResultWords (.matched Ms emb)) :=
    WordRAM.ListAt.congr hRepAt₀ fun a _ ha => hMemEq a (by omega)
  have hMemHeap : mem heap₁ = routedEnd :=
    (hMemEq heap₁ (by have : heap₁ < injectReplyBase heap₁ D.count D.base.childSize := by unfold injectReplyBase buildBatchEnd; omega
                      omega)).trans hMemHeap₀
  have hZeroP : ∀ a < D.base.host.n,
      mem (routedEnd + 4 + Ms.flatten.length + D.base.pathBound + 1 + a) = 0 := fun a ha =>
    (hMemEq _ (by omega)).trans (hZeroP₀ a ha)
  let prefHoles : ℕ → List ℕ := fun r => (List.range r).filterMap holesOpt
  have hPrefLenLe : ∀ r, (prefHoles r).length ≤ r := fun r => by
    dsimp [prefHoles]
    exact (List.length_filterMap_le holesOpt (List.range r)).trans (by simp)
  have hPrefValid : ∀ r ≤ D.limit, HolesValid D.base.host.n D.addrs.heap (bounds r) (prefHoles r) mem := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun _ hi => by simp [prefHoles] at hi, fun _ hi => by simp [prefHoles] at hi⟩
    | succ r ih =>
      intro hr
      have hPrev := ih (Nat.le_of_succ_le hr)
      have hArchR := hArch r hr
      have hStep : prefHoles (r + 1) = prefHoles r ++ (match holesOpt r with | some p => [p] | none => []) := by
        simp only [prefHoles, List.range_succ, List.filterMap_append]
        cases hopt : holesOpt r <;> simp [hopt]
      rw [hStep]
      unfold RoundArchive at hArchR
      split_ifs at hArchR with h0
      · rw [hArchR.2.1]; simpa [hArchR.2.2] using hPrev
      · obtain ⟨_, _, _, numCuts, _, _, _, hhiEq, _, _, _, _, _, _, _, _, _, _, hRest⟩ := hArchR
        split_ifs at hRest with hnc
        · rw [hRest.2.1]
          simpa using (holesValid_congr (hi := bounds (r + 1))
            ⟨fun i hi => ⟨(hPrev.1 i hi).1, (hPrev.1 i hi).2.1.trans (hbMono r hr), (hPrev.1 i hi).2.2⟩,
             hPrev.2⟩ (fun _ _ => rfl))
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, hhole, hloP, hPRec, hZeroPR, _⟩ := hRest
          rw [hhole]
          exact holesValid_append hPrev (hBoundsGe r (Nat.le_of_succ_le hr)) hloP (by omega) hZeroPR
  refine runs_start_le ?_
  unfold buildCollectHolesProc
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
      .cond (.reg 9)
        (.assign 10 (.load (.reg 9)) ;;
         .assign 11 (.load (.bin .add (.reg 9) (.const 1))) ;;
         .assign 12 (.load (.reg 10)) ;;
         .cond (.reg 12)
           (.assign 13 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 11)) ;;
            .assign 14 (.bin .add (.bin .add (.bin .add (.reg 13) (.bin .add (.reg 12) (.reg 12))) (.const 1))
                          (.bin .mul (.reg 12) (.reg 2))) ;;
            .assign 15 (.bin .add (.bin .add (.reg 14) (.const 4)) (.load (.bin .add (.reg 14) (.const 1)))) ;;
            .assign 16 (.load (.reg 13)) ;;
            .assign 17 (.bin .div (.load (.bin .add (.reg 15) (.reg 12))) (.const 2)) ;;
            .assign 18 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 16) (.const 4)) (.reg 17)) (.reg 4)) (.const 1)) ;;
            .store (.bin .add (.reg 6) (.reg 7)) (.reg 18) ;;
            .assign 7 (.bin .add (.reg 7) (.const 1)))
           .nop)
        .nop)
    (P := fun st =>
      st.regs 0 = D.directory ∧ st.regs 1 = D.limit ∧ st.regs 2 = D.base.childSize ∧
      st.regs 3 = D.count ∧ st.regs 4 = D.base.pathBound ∧ st.regs 5 = heap₁ ∧
      st.regs 6 = dst ∧ st.regs 7 = 0 ∧ st.mem = mem)
    (Inv := fun r st =>
      st.regs 0 = D.directory ∧ st.regs 1 = D.limit ∧ st.regs 2 = D.base.childSize ∧
      st.regs 3 = D.count ∧ st.regs 4 = D.base.pathBound ∧ st.regs 5 = heap₁ ∧
      st.regs 6 = dst ∧ st.regs 7 = (prefHoles r).length ∧ st.regs 8 = r ∧
      ListAt st.mem dst (prefHoles r) ∧
      (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dst + (prefHoles r).length))
    110 0 D.limit (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simpa [prefHoles] using h7,
        by simp, fun i hi => by simp [prefHoles] at hi, fun _ _ => hm ▸ rfl,
        fun a ha => hm ▸ hZF a (by simp [prefHoles] at ha; omega)⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.1])
    (fun r _ hr => by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hAtR, hPresR, hZFR⟩
      set rec := mem (D.directory + r)
      have hMrec : st.mem (D.directory + r) = rec := hPresR _ (by omega)
      have hStepH : prefHoles (r + 1) = prefHoles r ++ (match holesOpt r with | some p => [p] | none => []) := by
        simp only [prefHoles, List.range_succ, List.filterMap_append]
        cases hopt : holesOpt r <;> simp [hopt]
      have hBndLe : bounds (r + 1) ≤ injEnd := (hBoundsLe (r + 1) hr).trans hHeapLeInj
      have hLenRLe : (prefHoles r).length ≤ r := hPrefLenLe r
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := rec)
        (by rw [← hMrec]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h0)
              (Expr.eval_reg_of_eq h8) (by omega))) ?_
      refine runs_cond_le (v := rec) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
      · intro hrec0
        have hArchR := hArch r hr
        unfold RoundArchive at hArchR
        rw [ite_eq_right hrec0] at hArchR
        obtain ⟨prep, oldCount, act, numCuts, cutIdx, hlp, hpr, hhiEq, ho1, hok, hmp, hmo, hact,
          hactInj, hmnum, hnumLe, hcut, hcutInj, hRest⟩ := hArchR
        have hMprep : st.mem rec = prep := (hPresR _ (by omega)).trans hmp
        have hMold : st.mem (rec + 1) = oldCount := (hPresR _ (by omega)).trans hmo
        have hMnum : st.mem prep = numCuts := (hPresR _ (by omega)).trans hmnum
        refine runs_seq_assign_le (v := prep)
          (by rw [← hMprep]; exact Expr.eval_load (Expr.eval_reg_of_eq (v := rec) (by simp))) ?_
        refine runs_seq_assign_le (v := oldCount)
          (by rw [← hMold]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := rec) (by simp))
                (Expr.eval_const (by omega)) (by omega))) ?_
        refine runs_seq_assign_le (v := numCuts)
          (by rw [← hMnum]; exact Expr.eval_load (Expr.eval_reg_of_eq (v := prep) (by simp))) ?_
        refine runs_cond_le (v := numCuts) (Expr.eval_reg_of_eq (v := numCuts) (by simp)) ?_ ?_
        · intro hnc
          rw [ite_eq_right hnc] at hRest
          obtain ⟨Ms', emb', routedEnd', hMlen', _, hloRep', hMemBatch', hRepEndLe', hEndRec',
            hRepAt', hHoleEq, hloP', hPRec', _, _, _, _, _⟩ := hRest
          let batch := prep + 1 + oldCount
          let rep := buildBatchEnd batch numCuts D.base.childSize
          let P := routedEnd' + 4 + Ms'.flatten.length + D.base.pathBound + 1
          have hRepEndLe'' : rep + (routeResultWords (.matched Ms' emb')).length ≤ routedEnd' := hRepEndLe'
          obtain ⟨hRep1', hMtEnd', hLenRep'⟩ := routeMatched_flatten_offset hRepAt'
          have hPW : P < 2 ^ w := by dsimp [P]; omega
          have hRoW : routedEnd' < 2 ^ w := by dsimp [P] at hPW; omega
          have hRepW : rep < 2 ^ w := by omega
          have hBatchW : batch < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
          have hMrep1 : st.mem (rep + 1) = 1 :=
            (hPresR _ (by omega)).trans hRep1'
          have hMbatch : st.mem batch = routedEnd' :=
            (hPresR _ (by dsimp [batch, rep, buildBatchEnd] at hRepEndLe' hEndRec' ⊢; omega)).trans hMemBatch'
          have hMmtEnd : st.mem (rep + 5 + numCuts) = 2 * Ms'.flatten.length := by
            rw [hPresR _ (by omega), ← hMlen']; exact hMtEnd'
          refine runs_seq_assign_le (v := batch)
            (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := prep) (by simp))
              (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_reg_of_eq (v := oldCount) (by simp)) hBatchW) ?_
          refine runs_seq_assign_le (v := rep)
            (by have h1' : numCuts + numCuts < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
                have h2' : batch + (numCuts + numCuts) < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
                have h3' : batch + (numCuts + numCuts) + 1 < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
                have h4' : numCuts * D.base.childSize < 2 ^ w := by dsimp [rep, buildBatchEnd] at hRepW; omega
                have h5' : batch + (numCuts + numCuts) + 1 + numCuts * D.base.childSize = rep := by
                  dsimp [rep, buildBatchEnd]; omega
                rw [← h5']
                exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := batch) (by simp))
                  (Expr.eval_add (Expr.eval_reg_of_eq (v := numCuts) (by simp))
                    (Expr.eval_reg_of_eq (v := numCuts) (by simp)) h1') h2')
                  (Expr.eval_const (by omega)) h3')
                  (Expr.eval_mul (Expr.eval_reg_of_eq (v := numCuts) (by simp))
                    (Expr.eval_reg_of_eq (v := D.base.childSize) (by simpa using h2)) h4')
                  (by rw [h5']; exact hRepW)) ?_
          refine runs_seq_assign_le (v := rep + 5)
            (by have h1' : rep + 4 + st.mem (rep + 1) = rep + 5 := by rw [hMrep1]
                rw [← h1']
                exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := rep) (by simp))
                  (Expr.eval_const (by omega)) (by omega))
                  (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := rep) (by simp))
                    (Expr.eval_const (by omega)) (by omega)))
                  (by rw [h1']; omega)) ?_
          refine runs_seq_assign_le (v := routedEnd')
            (by rw [← hMbatch]; exact Expr.eval_load (Expr.eval_reg_of_eq (v := batch) (by simp))) ?_
          refine runs_seq_assign_le (v := Ms'.flatten.length)
            (by have hdiv : 2 * Ms'.flatten.length / 2 = Ms'.flatten.length :=
                  Nat.mul_div_right _ (by omega : 0 < 2)
                conv_rhs => rw [← hdiv]
                exact Expr.eval_div
                  (by rw [← hMmtEnd]; exact Expr.eval_load (Expr.eval_add
                        (Expr.eval_reg_of_eq (v := rep + 5) (by simp))
                        (Expr.eval_reg_of_eq (v := numCuts) (by simp))
                        (by omega)))
                  (Expr.eval_const (by omega)) (by omega)) ?_
          refine runs_seq_assign_le (v := P)
            (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (v := routedEnd') (by simp)) (Expr.eval_const (by omega))
              (by dsimp [P] at hPW; omega))
              (Expr.eval_reg_of_eq (v := Ms'.flatten.length) (by simp)) (by dsimp [P] at hPW; omega))
              (Expr.eval_reg_of_eq (v := D.base.pathBound) (by simpa using h4)) (by dsimp [P] at hPW; omega))
              (Expr.eval_const (by omega)) hPW) ?_
          refine runs_seq_store_le (x := dst + (prefHoles r).length) (v := P)
            (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h6))
              (Expr.eval_reg_of_eq (by simpa using h7)) (by omega))
            (Expr.eval_reg_of_eq (v := P) (by simp)) ?_
          refine runs_assign_le (v := (prefHoles r).length + 1)
            (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7))
              (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
          have hStepP : prefHoles (r + 1) = prefHoles r ++ [P] := by
            rw [hStepH, hHoleEq]
          refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
            by simpa using h4, by simpa using h5, by simpa using h6,
            by simp [hStepP], by simp, ?_, ?_, ?_⟩, by simp [h8]⟩
          · rw [hStepP]
            refine listAt_append.mpr ⟨WordRAM.ListAt.congr hAtR fun a _ hb =>
              Function.update_of_ne (by omega) _ _, fun i hi => ?_⟩
            simp only [List.length_singleton, Nat.lt_one_iff] at hi
            subst hi; simp
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hPresR a ha
          · intro a ha
            dsimp only
            rw [hStepP, List.length_append, List.length_singleton] at ha
            rw [Function.update_of_ne (by omega)]
            exact hZFR a (by omega)
        · intro hnc
          rw [ite_eq_left hnc] at hRest
          have hStepNone : prefHoles (r + 1) = prefHoles r := by rw [hStepH, hRest.2.1]; simp
          refine runs_nop_le ?_ (by simp [Expr.size])
          exact ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
            by simpa using h4, by simpa using h5, by simpa using h6,
            by simpa [hStepNone] using h7, by simp,
            hStepNone.symm ▸ hAtR, hPresR, hStepNone.symm ▸ hZFR⟩, by simp [h8]⟩
      · intro hrec0
        have hArchR := hArch r hr
        unfold RoundArchive at hArchR
        rw [ite_eq_left hrec0] at hArchR
        have hStepNone : prefHoles (r + 1) = prefHoles r := by rw [hStepH, hArchR.2.1]; simp
        refine runs_nop_le ?_ (by simp [Expr.size])
        exact ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6,
          by simpa [hStepNone] using h7, by simp,
          hStepNone.symm ▸ hAtR, hPresR, hStepNone.symm ▸ hZFR⟩, by simp [h8]⟩)
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st1 ⟨_, _, h2, h3, h4, h5, h6, h7, _, hAt1, hPres1, hZF1⟩
  -- Final injection hole P_inj
  let rep := injectReplyBase heap₁ D.count D.base.childSize
  let P_inj := routedEnd + 4 + Ms.flatten.length + D.base.pathBound + 1
  obtain ⟨hRep1, hMtEnd, hLenRep⟩ := routeMatched_flatten_offset hRepAt
  have hPW : P_inj < 2 ^ w := by dsimp [P_inj]; omega
  have hRoW : routedEnd < 2 ^ w := by dsimp [P_inj] at hPW; omega
  have hRepW : rep < 2 ^ w := by omega
  have hMrep1 : st1.mem (rep + 1) = 1 :=
    (hPres1 _ (by dsimp [rep]; omega)).trans hRep1
  have hMheap1 : st1.mem heap₁ = routedEnd :=
    (hPres1 _ (by dsimp [rep, injectReplyBase, buildBatchEnd] at hRepEndLe hEndInj; omega)).trans hMemHeap
  have hMmtEnd : st1.mem (rep + 5 + D.count) = 2 * Ms.flatten.length := by
    rw [hPres1 _ (by dsimp [rep]; omega), ← hMlen]; exact hMtEnd
  have hLenLim : (prefHoles D.limit).length ≤ D.limit := hPrefLenLe D.limit
  refine runs_seq_assign_le (v := rep)
    (by have h1' : heap₁ + D.base.childSize < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h2' : D.count + D.count < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h3' : heap₁ + D.base.childSize + (D.count + D.count) < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h4' : heap₁ + D.base.childSize + (D.count + D.count) + 1 < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h5' : D.count * D.base.childSize < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h6' : heap₁ + D.base.childSize + (D.count + D.count) + 1 +
            D.count * D.base.childSize = rep := by
          dsimp [rep, injectReplyBase, buildBatchEnd]; omega
        rw [← h6']
        exact Expr.eval_add (Expr.eval_add (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h2) h1')
          (Expr.eval_add (Expr.eval_reg_of_eq h3) (Expr.eval_reg_of_eq h3) h2') h3')
          (Expr.eval_const (by omega)) h4')
          (Expr.eval_mul (Expr.eval_reg_of_eq h3) (Expr.eval_reg_of_eq h2) h5')
          (by rw [h6']; exact hRepW)) ?_
  refine runs_seq_assign_le (v := rep + 5)
    (by have h1' : rep + 4 + st1.mem (rep + 1) = rep + 5 := by rw [hMrep1]
        rw [← h1']
        exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := rep) (by simp))
          (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := rep) (by simp))
            (Expr.eval_const (by omega)) (by omega)))
          (by rw [h1']; omega)) ?_
  refine runs_seq_assign_le (v := routedEnd)
    (by rw [← hMheap1]; exact Expr.eval_load (Expr.eval_reg_of_eq (by simpa using h5))) ?_
  refine runs_seq_assign_le (v := Ms.flatten.length)
    (by have hdiv : 2 * Ms.flatten.length / 2 = Ms.flatten.length :=
          Nat.mul_div_right _ (by omega : 0 < 2)
        conv_rhs => rw [← hdiv]
        exact Expr.eval_div
          (by rw [← hMmtEnd]; exact Expr.eval_load (Expr.eval_add
                (Expr.eval_reg_of_eq (v := rep + 5) (by simp))
                (Expr.eval_reg_of_eq (v := D.count) (by simpa using h3))
                (by omega)))
          (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := P_inj)
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (v := routedEnd) (by simp)) (Expr.eval_const (by omega))
      (by dsimp [P_inj] at hPW; omega))
      (Expr.eval_reg_of_eq (v := Ms.flatten.length) (by simp)) (by dsimp [P_inj] at hPW; omega))
      (Expr.eval_reg_of_eq (v := D.base.pathBound) (by simpa using h4)) (by dsimp [P_inj] at hPW; omega))
      (Expr.eval_const (by omega)) hPW) ?_
  refine runs_seq_store_le (x := dst + (prefHoles D.limit).length) (v := P_inj)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h6))
      (Expr.eval_reg_of_eq (by simpa using h7)) (by omega))
    (Expr.eval_reg_of_eq (v := P_inj) (by simp)) ?_
  refine runs_seq_assign_le (v := (prefHoles D.limit).length + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_ret_le (v := (prefHoles D.limit).length + 1)
    (Expr.eval_reg_of_eq (v := (prefHoles D.limit).length + 1) (by simp)) ?_ ?_
  · let allHoles := prefHoles D.limit ++ [P_inj]
    have hAllLen : allHoles.length = (prefHoles D.limit).length + 1 := by simp [allHoles]
    have hPresAll : ∀ a < dst, Function.update st1.mem (dst + (prefHoles D.limit).length) P_inj a = mem a :=
      fun a ha => (Function.update_of_ne (by omega) _ _).trans (hPres1 a ha)
    have hNonHole : injEnd ≤ D.addrs.heap +
        (D.limit + 1) * roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        D.limit * (roundCoreCap D + roundRouteCap D) + roundRouteCap D +
        allHoles.length * D.base.host.n := by
      have h1 := trace_nonHole_le hb0 hbt hArch
      have hFiltEq : ((List.range D.limit).filter fun r => (holesOpt r).isSome).length =
          (prefHoles D.limit).length := by
        dsimp [prefHoles]
        clear h1
        induction (List.range D.limit) with
        | nil => simp
        | cons x xs ih =>
          cases hopt : holesOpt x <;> simp [hopt, ih]
      rw [hFiltEq, Nat.mul_add] at h1
      rw [hAllLen, Nat.succ_mul, Nat.succ_mul]
      omega
    refine ⟨dst, allHoles, rfl, by dsimp [Outcome.value]; exact hAllLen.symm,
      by dsimp [Outcome.value]; omega, by dsimp [Outcome.value]; omega, ?_, ?_,
      by dsimp [Outcome.value]; exact hAllLen ▸ hNonHole, hPresAll, ?_⟩
    · refine listAt_append.mpr ⟨WordRAM.ListAt.congr hAt1 fun a _ hb =>
        Function.update_of_ne (by omega) _ _, fun i hi => ?_⟩
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi; simp
    · refine holesValid_congr (holesValid_append (hbt ▸ hPrefValid D.limit le_rfl)
        (hbt ▸ hBoundsGe D.limit le_rfl) hHeapLeP hPInj hZeroP)
        (fun a ha => hPresAll a (ha.trans_le hInjDst))
    · intro a ha
      dsimp only [Outcome.value] at ha ⊢
      rw [Function.update_of_ne (by omega)]
      exact hZF1 a (by omega)
  · simp only [buildCollectHolesContract, Expr.size, Nat.sub_zero]
    have hnorm : 110 + 1 + 8 = 119 := by omega
    rw [hnorm]
    have hle : D.limit * 119 ≤ 120 * D.limit := by omega
    omega


end MinCostFlow.HierPaths
