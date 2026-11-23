module

public import MinCostFlow.HierPaths.BuildProgLevelDefs
import MinCostFlow.HierPaths.InitLayout

/-!
# Back half of the non-singleton one-parent level builder

Proves `nonSingleton_back_runs`: collects archived walks, writes sections 0, 1, and 2
consecutively above `outStart`, copies the concatenated sections down to `h + 4`, writes the
four top-level offsets at `h..h+3`, and returns the bump heap end `end2`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Back half of the non-singleton pipeline (Passes A–D + header) -/

theorem layoutList3_eq (a b c : List ℕ) :
    layoutList [a, b, c] = [0, a.length, a.length + b.length, a.length + b.length + c.length] ++
      (a ++ b ++ c) := by
  simp [layoutList, csrList, csrOffsets, csrData, List.range_succ, List.append_assoc, Nat.add_assoc]

set_option maxHeartbeats 800000 in
theorem nonSingleton_back_runs {w K C router core : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h heap₁ injEnd : ℕ} {β : ℝ}
    {p : Program} {prior later : List Stmt} {initMem : ℕ → ℕ}
    {sts : ℕ → ChildState} {st : State} {ω : ℕ → Bool}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w K route routeCost sR p router)
    (hPlayer : IsMatchingPlayer route routeCost) (hC : RouteCostLe routeCost C)
    (hGE : g + G.encode.length ≤ h)
    (hXE : x + (finsetWords (buildLevelVerts start s k)).length ≤ h)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0)
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w)
    (hArgW : ∀ a ∈ buildLevelArgs g x start s k M r Δ L L' bh h, a < 2 ^ w)
    (hGraphAt : GraphAt st.mem g G)
    (hVertsAt : ListAt st.mem x (finsetWords (buildLevelVerts start s k)))
    (hPrefix : ∀ a < h, st.mem a = initMem a)
    (hRoundsMem : TraceRoundsMem
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h)
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).limit
      heap₁ sts st.mem)
    (hInjArch : InjArchive G s k (routePathLen Δ bh L)
      (roundRouteCap (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h))
      (h + (49 * L' + 1) + k + k + k) (2 + buildLevelDegree L' * s) heap₁ injEnd
      (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k (fun c => start + c * s) sts)
      (fun c => (sts c).rounds.flatten.map Prod.snd) st.mem)
    (hInjBound : injEnd ≤ h + (buildLevelDegree L' + 4 * k + 1 + k * (2 + buildLevelDegree L' * s)) +
      buildLevelDegree L' * (roundNonHoleCap s k (routePathLen Δ bh L) +
        k * (maxCoreSpace (sC M r) (2 + buildLevelDegree L' * s) + 3 * s) +
        (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
          (Δ + L + max 2 (s * k)) + G.n))
    (hFlen : ∀ c < k, (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
      (fun c => start + c * s) sts c).length ≤ buildLevelDegree L' * (s / 2))
    (hFends : ∀ c < k, ∀ e ∈ (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
      (fun c => start + c * s) sts c).map Prod.fst, e.1 < s ∧ e.2 < s)
    (hFwalk : ∀ c < k, ∀ e < (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
      (fun c => start + c * s) sts c).length,
      ((finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
        (fun c => start + c * s) sts c).getD e ((0, 0), [])).2.length ≤ routePathLen Δ bh L)
    (hr0 : st.regs 0 = g) (hr1 : st.regs 1 = x) (hr2 : st.regs 2 = start)
    (hr3 : st.regs 3 = s) (hr4 : st.regs 4 = k) (hr7 : st.regs 7 = Δ) (hr8 : st.regs 8 = L)
    (hr11 : st.regs 11 = h) (hr12 : st.regs 12 = routePathLen Δ bh L)
    (hr13 : st.regs 13 = 49 * L' + 1) (hr15 : st.regs 15 = 2 + buildLevelDegree L' * s)
    (hr16 : st.regs 16 = buildLevelDegree L' * (s / 2))
    (hr20 : st.regs 20 = h + (49 * L' + 1) + k + k + k)
    (hr25 : st.regs 25 = heap₁) (hr26 : st.regs 26 = injEnd) :
    let D_level := levelDataOfFamily route G start s k Δ L
      (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
        (fun c => start + c * s) sts)
    let T := buildLevelDegree L'
    let limit := 49 * L' + 1
    let d := routePathLen Δ bh L
    let maxM := T * (s / 2)
    let s0 := (sec0Words G.n start s k
      (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
        (fun c => start + c * s) sts)).length
    let s1 := (sec1Words k
      (finishedChildFamily route G (buildLevelVerts start s k) Δ L s k
        (fun c => start + c * s) sts)).length
    let s2 := (csrList (k * k) (levelConnRow route G start s k Δ L)).length
    ∃ v st' c,
      Runs w p ω
        (buildLevelNonSingletonBack (prior.length + 44) (prior.length + 45)
          (prior.length + 46) (prior.length + 57) (prior.length + 14))
        st (.returned v) st' c ∧
      h + (D_level.encode k).length ≤ v ∧
      v ≤ h + buildLevelSpace sR sC G s k M r Δ L L' bh ∧
      ListAt st'.mem h (D_level.encode k) ∧
      (∀ a < h, st'.mem a = initMem a) ∧
      ZeroFrom st'.mem v ∧
      c ≤ ((limit + 1) * (32 * (s * k) + 170 * k + 260) + 120) +
        (k * (50 * maxM + 105) + 60) +
        (k * (maxM * (17 * d + 85) + 115) + 60) +
        connAllCostBound K C G s k Δ L bh +
        (17 * (s0 + s1 + s2) + 12) + 220 := by
  let b := prior.length
  let gIdx := b + 1
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  let F := finishedChildFamily route G (buildLevelVerts start s k) Δ L s k (fun c => start + c * s) sts
  let D_level := levelDataOfFamily route G start s k Δ L F
  set T := buildLevelDegree L'
  set limit := 49 * L' + 1
  set d := routePathLen Δ bh L
  set slotWords := 2 + T * s
  set maxM := T * (s / 2)
  set slots := h + limit + k + k + k
  set walkPtrs := injEnd + k
  set outStart := walkPtrs + k * maxM
  set s0Words := sec0Words G.n start s k F
  set s1Words := sec1Words k F
  set s2Words := csrList (k * k) (levelConnRow route G start s k Δ L)
  set end0 := outStart + s0Words.length
  set end1 := end0 + s1Words.length
  set end2 := end1 + s2Words.length
  set coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
  set routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
    (Δ + L + max 2 (s * k))
  -- Word and space bounds
  have hNonSingLe : (T + 4 * k + 1 + k * slotWords) + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
      (k + k * (T * s)) + (k + 1 + k * slotWords) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
      (maxCoreSpace (sC M r) slotWords + routeCap +
        6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
      connAllSpace sR G s k Δ L d +
      NOf M r + d + G.n + 100 ≤ buildLevelSpace sR sC G s k M r Δ L L' bh :=
    le_max_right _ _
  have hNonSing : h + ((T + 4 * k + 1 + k * slotWords) + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
      (k + k * (T * s)) + (k + 1 + k * slotWords) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
      (maxCoreSpace (sC M r) slotWords + routeCap +
        6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
      connAllSpace sR G s k Δ L d +
      NOf M r + d + G.n + 100) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left hNonSingLe h) hSpace
  have h2Half : 2 * (s / 2) = s := by omega
  have h2MaxM : 2 * maxM = T * s := by
    dsimp [maxM]; calc 2 * (T * (s / 2)) = T * (2 * (s / 2)) := by ring
      _ = T * s := by rw [h2Half]
  have hMaxMLe : maxM ≤ T * s := by omega
  have hKMaxM : k * maxM ≤ k * (T * s) := Nat.mul_le_mul_left k hMaxMLe
  have hS0Len : s0Words.length ≤ k + 1 + k * slotWords := by
    have h1 := sec0Words_length_le (gn := G.n) (start := start) (s := s) (k := k) (maxM := maxM) hFlen
    have h2 : 3 * k + 1 + 2 * (k * maxM) = k + 1 + k * (2 + 2 * maxM) := by ring
    rw [h2, h2MaxM] at h1; exact h1
  have hS1Len : s1Words.length ≤ k + 1 + k * (T * s + 1 + T * s * d) := by
    have h1 : s1Words.length ≤ 2 * k + 1 + k * (maxM * (d + 1)) :=
      sec1Words_length_le (k := k) (d := d) (maxM := maxM) hFlen hFwalk
    have h2 : maxM * (d + 1) ≤ T * s * (d + 1) := Nat.mul_le_mul_right (d + 1) hMaxMLe
    have h3 : k * (maxM * (d + 1)) ≤ k * (T * s * (d + 1)) := Nat.mul_le_mul_left k h2
    have h4 : 2 * k + 1 + k * (T * s * (d + 1)) = k + 1 + k * (T * s + 1 + T * s * d) := by ring
    omega
  have hS2Len : s2Words.length ≤ k * k + 1 + k * k * (8 + 3 * s + s * d) :=
    levelConnSec_length_le hPlayer hPos hExp hHost (by omega) (by omega) hBh
  have hStartLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
  have hCardW : (buildLevelVerts start s k).card < 2 ^ w := by
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; omega
  -- Order between heap0, heap1, injEnd, outStart
  have hHeap0LeHeap1 : D.addrs.heap ≤ heap₁ := by
    obtain ⟨_, bounds, _, _, hb0, hbt, hbMono, _, _⟩ := hRoundsMem
    have hgen : ∀ n ≤ D.limit, bounds 0 ≤ bounds n := by
      intro n; induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (Nat.le_of_succ_le hn)).trans (hbMono n hn)
    rw [← hb0, ← hbt]; exact hgen D.limit le_rfl
  have hHeap1LeInj : heap₁ ≤ injEnd := by
    obtain ⟨_, _, _, _, _, h1, _, h2, h3, _⟩ := hInjArch; omega
  have hDirLeHeap0 : h + limit ≤ D.addrs.heap := by
    change h + limit ≤ h + limit + k + k + k + k * (2 + (limit + 1) * s) + k + 1; omega
  have hSlotsLeHeap0 : slots + k * slotWords ≤ D.addrs.heap := by
    have hLim1 : limit + 1 = T := rfl
    change h + limit + k + k + k + k * (2 + T * s) ≤
      h + limit + k + k + k + k * (2 + (limit + 1) * s) + k + 1
    rw [hLim1]; omega
  have hH4LeOut : h + 4 ≤ outStart := by
    have h4 : h + 4 ≤ D.addrs.heap := by
      change h + 4 ≤ h + limit + k + k + k + k * (2 + (limit + 1) * s) + k + 1; omega
    dsimp [outStart, walkPtrs]; omega
  have hGnMem : st.mem g = G.n := by
    have h0 := hGraphAt 0 (by rw [buildGraph_encode_length]; omega)
    simpa [Graph.encode] using h0
  -- Word bounds for all registers
  have hGW : g < 2 ^ w := hArgW g (by simp [buildLevelArgs])
  have hXW : x < 2 ^ w := hArgW x (by simp [buildLevelArgs])
  have hStartW : start < 2 ^ w := hArgW start (by simp [buildLevelArgs])
  have hSW : s < 2 ^ w := hArgW s (by simp [buildLevelArgs])
  have hKW : k < 2 ^ w := hArgW k (by simp [buildLevelArgs])
  have hΔW : Δ < 2 ^ w := hArgW Δ (by simp [buildLevelArgs])
  have hLW : L < 2 ^ w := hArgW L (by simp [buildLevelArgs])
  have hHW : h < 2 ^ w := hArgW h (by simp [buildLevelArgs])
  have hEnd1ConnW : end1 + connAllSpace sR G s k Δ L d < 2 ^ w := by
    dsimp [end1, end0, outStart, walkPtrs]; omega
  have hEnd1ConnLeSpace : end1 + connAllSpace sR G s k Δ L d ≤ h + buildLevelSpace sR sC G s k M r Δ L L' bh := by
    have h1 : end1 + connAllSpace sR G s k Δ L d ≤ h + ((T + 4 * k + 1 + k * slotWords) +
        T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
        (k + k * (T * s)) + (k + 1 + k * slotWords) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
        (maxCoreSpace (sC M r) slotWords + routeCap +
          6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
        connAllSpace sR G s k Δ L d +
        NOf M r + d + G.n + 100) := by
      dsimp [end1, end0, outStart, walkPtrs]; omega
    exact h1.trans (Nat.add_le_add_left hNonSingLe h)
  have hS2LeConn : s2Words.length ≤ connAllSpace sR G s k Δ L d := by
    unfold connAllSpace; omega
  have hEnd2W : end2 < 2 ^ w := by dsimp [end2]; omega
  have hEnd1W : end1 < 2 ^ w := by dsimp [end2] at hEnd2W; omega
  have hEnd0W : end0 < 2 ^ w := by dsimp [end1] at hEnd1W; omega
  have hOutStartW : outStart < 2 ^ w := by dsimp [end0] at hEnd0W; omega
  have hWalkPtrsW : walkPtrs < 2 ^ w := by dsimp [outStart] at hOutStartW; omega
  have hInjW : injEnd < 2 ^ w := by dsimp [walkPtrs] at hWalkPtrsW; omega
  have hHeap1W : heap₁ < 2 ^ w := by omega
  have hKMaxMW : k * maxM < 2 ^ w := by omega
  have hDW : d < 2 ^ w := by omega
  have hLimW : limit < 2 ^ w := by dsimp [T, buildLevelDegree, limit] at hNonSing ⊢; omega
  have hSlotW : slotWords < 2 ^ w := by
    have : 1 * slotWords ≤ k * slotWords := Nat.mul_le_mul_right slotWords (by omega)
    omega
  have hMaxMW : maxM < 2 ^ w := by
    have : 1 * maxM ≤ k * maxM := Nat.mul_le_mul_right maxM (by omega); omega
  have hSlotsW : slots < 2 ^ w := by omega
  have hGnW : G.n < 2 ^ w := by omega
  have h4W : 4 < 2 ^ w := by omega
  -- Lookup tail/game procs
  have hg13 := buildLevelProcs_lookup_game hp 13 (by decide)
  have ht8 := buildLevelProcs_lookup_tail hp 8 (by decide)
  have ht9 := buildLevelProcs_lookup_tail hp 9 (by decide)
  have ht10 := buildLevelProcs_lookup_tail hp 10 (by decide)
  have ht11 := buildLevelProcs_lookup_tail hp 11 (by decide)
  have ht12 := buildLevelProcs_lookup_tail hp 12 (by decide)
  simp only [buildGameProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at hg13
  simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht8 ht9 ht10 ht11 ht12
  have hSpecWalks := buildCollectWalksProc_meetsContract (w := w) (D := D)
    (slot := slots) (slotWords := slotWords) (heap₁ := heap₁) (injEnd := injEnd) (sts := sts) (F := F)
    (by simpa [b] using ht10) (by simpa [b] using ht9) (by simpa [b] using ht8)
  have hSpecSec0 := buildSec0Proc_meetsContract (w := w) (gn := G.n) (start := start)
    (s := s) (k := k) (maxM := maxM) (F := F) (by simpa [b] using ht11)
  have hSpecSec1 := buildSec1Proc_meetsContract (w := w) (k := k) (d := d)
    (maxM := maxM) (F := F) (by simpa [b] using ht12) (by simpa [b, gIdx] using hg13)
  have hSpecConn := buildLevelProcs_connAll_meetsContract (w := w) (K := K) (C := C)
    (sR := sR) (G := G) (start := start) (s := s) (k := k) (Δ := Δ) (L := L) (bh := bh)
    hp hRouter hPlayer hC hValid hPos hExp hBh hCardW
  have hSpecCopy := buildCopyProc_meetsDownContract (w := w) (by simpa [b, gIdx] using hg13)
  -- Part 1: collect walks, write sections 0, 1, and 2 consecutively starting at outStart
  have hBack1 : ∃ o st7 c1,
      Runs w p ω
        (buildLevelNonSingletonBack1 (b + 44) (b + 45) (b + 46) (b + 57))
        st o st7 c1 ∧
      (∃ vFinal,
        o = .normal ∧
        st7.regs 4 = k ∧ st7.regs 11 = h ∧ st7.regs 28 = outStart ∧ st7.regs 29 = end0 ∧
        st7.regs 30 = end1 ∧ st7.regs 31 = vFinal ∧
        end2 ≤ vFinal ∧ vFinal ≤ end1 + connAllSpace sR G s k Δ L d ∧
        ListAt st7.mem outStart ((s0Words ++ s1Words) ++ s2Words) ∧
        ListAt st7.mem end1 s2Words ∧
        ZeroFrom st7.mem vFinal ∧
        (∀ a < h, st7.mem a = initMem a)) ∧
      c1 ≤ ((limit + 1) * (32 * (s * k) + 170 * k + 260) + 120) +
           (k * (50 * maxM + 105) + 60) +
           (k * (maxM * (17 * d + 85) + 115) + 60) +
           connAllCostBound K C G s k Δ L bh + 80 := by
    refine runs_start_le ?_
    unfold buildLevelNonSingletonBack1
    -- Step 1: assign 27 := injEnd + k
    refine runs_seq_assign_le (v := walkPtrs)
      (Expr.eval_add (Expr.eval_reg_of_eq hr26) (Expr.eval_reg_of_eq hr4) hWalkPtrsW) ?_
    -- Step 2: assign 28 := walkPtrs + k * maxM
    refine runs_seq_assign_le (v := outStart)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_reg_of_eq (by simpa using hr4))
          (Expr.eval_reg_of_eq (by simpa using hr16)) hKMaxMW) hOutStartW) ?_
    -- Step 3: call 24 fCollectWalks
    have hWalksPre : (buildCollectWalksContract w D slots slotWords heap₁ injEnd sts F).pre
        [h, limit, start, s, k, heap₁, injEnd, walkPtrs, maxM] st.mem :=
      ⟨maxM, rfl, by change 1 ≤ s; omega, by change h + limit ≤ injEnd; omega,
       hRoundsMem, hInjArch, hFlen,
       by change injEnd + k + k * maxM < 2 ^ w; dsimp [outStart, walkPtrs] at hOutStartW; omega,
       by change start + k * s < 2 ^ w; omega, h4W⟩
    refine runs_seq_call_le hSpecWalks
      (vs := [h, limit, start, s, k, heap₁, injEnd, walkPtrs, maxM])
      (by simp [evalArgs, Expr.eval, hr2, hr3, hr4, hr11, hr13, hr16, hr25, hr26])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hWalksPre ?_
    intro _ m4 _ hPost4
    obtain ⟨cap4, heq4, hWT4, hFr4, hZ4⟩ := hPost4
    have hCap4 : cap4 = maxM := by
      simpa using congrArg (fun l => l.getD 8 0) heq4.symm
    subst hCap4
    have hFr4Inj : ∀ a < injEnd, m4 a = st.mem a := hFr4
    have hZ4Out : ZeroFrom m4 outStart := by
      intro a ha; exact hZ4 a (by change injEnd + k + k * maxM ≤ a; dsimp [outStart, walkPtrs] at ha; omega)
    -- Step 4: call 29 fSec0
    have hSec0Pre : (buildSec0Contract w G.n start s k maxM F).pre
        [g, start, s, k, slots, slotWords, outStart] m4 := by
      refine ⟨g, slots, slotWords, outStart, rfl,
        (hFr4Inj g (by omega)).trans hGnMem, by omega, by omega, by omega, ?_,
        hZ4Out, by omega, by omega, hGnW, by omega⟩
      intro c hc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hSlotAt, _⟩ := hInjArch
      have hSlotLen : (Graph.mk s ((F c).map Prod.fst)).encode.length ≤ slotWords := by
        have hfl : (F c).length ≤ maxM := hFlen c hc
        dsimp [slotWords]; rw [buildGraph_encode_length]; simp only [Graph.m, List.length_map]
        omega
      have hMul : (c + 1) * slotWords ≤ k * slotWords := Nat.mul_le_mul_right _ hc
      rw [Nat.succ_mul] at hMul
      exact ⟨WordRAM.ListAt.congr (hSlotAt c hc) fun a _ hb => hFr4Inj a (by omega),
        hFlen c hc, hFends c hc⟩
    refine runs_seq_call_le hSpecSec0
      (vs := [g, start, s, k, slots, slotWords, outStart])
      (by simp [evalArgs, Expr.eval, hr0, hr2, hr3, hr4, hr15, hr20])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hSec0Pre ?_
    intro v5 m5 _ hPost5
    obtain ⟨_, _, _, _, heq5, hv5, hSec0At5, hFr5, hZ5⟩ := hPost5
    simp only [List.cons.injEq, and_true, true_and] at heq5
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq5
    change v5 = end0 at hv5; subst hv5
    -- Step 5: call 30 fSec1
    have hSec1Pre : (buildSec1Contract w k d maxM F).pre
        [k, injEnd, walkPtrs, maxM, end0] m5 := by
      refine ⟨injEnd, walkPtrs, maxM, end0, rfl, ?_, by dsimp [end0, outStart]; omega,
        fun c hc => ⟨hFlen c hc, hFwalk c hc⟩, hZ5, by dsimp [end1] at hEnd1W; omega, by omega⟩
      have hEqOut : ∀ a < outStart, m5 a = m4 a := hFr5
      refine ⟨hWT4.1, fun c hc => ?_⟩
      obtain ⟨hLenC, hCntC, hEntC⟩ := hWT4.2 c hc
      refine ⟨hLenC, (hEqOut _ (by dsimp [outStart, walkPtrs]; omega)).trans hCntC, fun e he => ?_⟩
      obtain ⟨hAddrLe, hSeq⟩ := hEntC e he
      have hMul : c * maxM + e < k * maxM := by
        have h1 : (c + 1) * maxM ≤ k * maxM := Nat.mul_le_mul_right _ hc
        rw [Nat.succ_mul] at h1
        have hfl : (F c).length ≤ maxM := hFlen c hc
        have : e < maxM := by simp only [List.length_map] at he; omega
        omega
      have hPtrEq : m5 (walkPtrs + c * maxM + e) = m4 (walkPtrs + c * maxM + e) :=
        hEqOut _ (by dsimp [outStart, walkPtrs]; omega)
      have hWalkIdxEq : injEnd + D.count + c * maxM + e = walkPtrs + c * maxM + e := rfl
      rw [hWalkIdxEq] at hAddrLe hSeq
      have hPtrOut : m4 (walkPtrs + c * maxM + e) < outStart := by
        dsimp [outStart, walkPtrs] at hAddrLe ⊢; omega
      refine ⟨by rw [hPtrEq]; exact hAddrLe, ?_⟩
      rw [hPtrEq]
      exact ⟨(hEqOut _ hPtrOut).trans hSeq.1,
        WordRAM.ListAt.congr hSeq.2 fun a _ hb => hEqOut a (by dsimp [outStart, walkPtrs] at hAddrLe hb ⊢; omega)⟩
    refine runs_seq_call_le hSpecSec1
      (vs := [k, injEnd, walkPtrs, maxM, end0])
      (by simp [evalArgs, Expr.eval, hr4, hr16, hr26])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption)
      hSec1Pre ?_
    intro v6 m6 _ hPost6
    obtain ⟨_, _, _, _, heq6, hv6, hSec1At6, hFr6, hZ6⟩ := hPost6
    simp only [List.cons.injEq, and_true, true_and] at heq6
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq6
    change v6 = end1 at hv6; subst hv6
    have hFr6Inj : ∀ a < injEnd, m6 a = st.mem a := fun a ha =>
      (hFr6 a (by dsimp [end0, outStart, walkPtrs]; omega)).trans
        ((hFr5 a (by dsimp [outStart, walkPtrs]; omega)).trans (hFr4Inj a ha))
    -- Step 6: call 31 fConnAll [g, x, start, s, k, Δ, L, d, end1]
    have hConnPre : (buildConnAllContract w K C route sR G start s k Δ L bh).pre
        [g, x, start, s, k, Δ, L, d, end1] m6 := by
      refine ⟨g, x, end1, rfl,
        WordRAM.ListAt.congr hGraphAt (fun a _ hb => hFr6Inj a (by omega)),
        WordRAM.ListAt.congr hVertsAt (fun a _ hb => hFr6Inj a (by omega)),
        hGE.trans (by dsimp [end1, end0, outStart, walkPtrs]; omega),
        hXE.trans (by dsimp [end1, end0, outStart, walkPtrs]; omega),
        hZ6, hValid, hHost, by omega, by omega, by omega, h4W, hGnW, hEnd1ConnW,
        β, hPos, hExp, hBh⟩
    refine runs_call_le hSpecConn
      (vs := [g, x, start, s, k, Δ, L, d, end1])
      (by simp [evalArgs, Expr.eval, hr0, hr1, hr2, hr3, hr4, hr7, hr8, hr12])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hConnPre ?_
    intro v7 m7 _ hPost7
    obtain ⟨_, _, _, heq7, hv7Lo, hv7Hi, hSec2At7, hFr7, hZ7⟩ := hPost7
    simp only [d, List.cons.injEq, and_true, true_and] at heq7
    obtain ⟨rfl, rfl, rfl⟩ := heq7
    have hPayAt7 : ListAt m7 outStart ((s0Words ++ s1Words) ++ s2Words) := by
      apply listAt_append.mpr
      refine ⟨listAt_append.mpr ⟨WordRAM.ListAt.congr hSec0At5 (fun a _ hb =>
        (hFr7 a (by dsimp [end1, end0]; omega)).trans (hFr6 a hb)),
        WordRAM.ListAt.congr hSec1At6 (fun a _ hb => hFr7 a hb)⟩, ?_⟩
      simpa only [List.length_append, ← Nat.add_assoc] using hSec2At7
    have hFr7H : ∀ a < h, m7 a = initMem a := fun a ha =>
      (hFr7 a (by dsimp [end1, end0, outStart, walkPtrs]; omega)).trans
        ((hFr6Inj a (by omega)).trans (hPrefix a ha))
    refine ⟨⟨v7, rfl, by simpa using hr4, by simpa using hr11, by simp, by simp, by simp, by simp,
      by dsimp [end2]; exact hv7Lo, hv7Hi, hPayAt7, hSec2At7, hZ7, hFr7H⟩, ?_⟩
    simp only [buildCollectWalksContract, buildSec0Contract, buildSec1Contract,
      buildConnAllContract, Expr.size, argsSize]
    have hDlim : D.limit = limit := rfl
    have hDcs : D.base.childSize = s := rfl
    have hDcnt : D.count = k := rfl
    rw [hDlim, hDcs, hDcnt]
    clear * -
    omega
  obtain ⟨_, st7, c1, hRun1, ⟨vFinal, rfl, h7r4, h7r11, h7r28, h7r29, h7r30, h7r31,
    hEnd2LeV, hVLeConn, hPayAt7, hSec2At7, hZ7, hFr7H⟩, hC1⟩ := hBack1
  -- Part 2: read end2 from sec2 CSR header, copy [outStart, end2) down to h + 4, store header, return vFinal
  have hEncEq : D_level.encode k = layoutList [s0Words, s1Words, s2Words] := by
    unfold BuildLevelData.encode
    congr 1
    simp only [List.cons.injEq, and_true]
    exact ⟨(sec0Words_eq_levelHost route G start s k Δ L F).symm,
      (sec1Words_eq_levelEmb route G start s k Δ L F).symm, rfl⟩
  have hEncLen : (D_level.encode k).length = 4 + s0Words.length + s1Words.length + s2Words.length := by
    rw [hEncEq, layoutList3_eq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hSec2LenEq : s2Words.length = k * k + 1 + st7.mem (end1 + k * k) := by
    have hOff := csrList_offset hSec2At7 (le_refl (k * k))
    have hL : s2Words.length = k * k + 1 + ((List.range (k * k)).map fun j =>
        (levelConnRow route G start s k Δ L j).length).sum := by
      rw [show s2Words = csrList (k * k) (levelConnRow route G start s k Δ L) from rfl,
        csrList, List.length_append, length_csrOffsets, length_csrData_eq]
    omega
  have hBack2 : ∃ o st' c2,
      Runs w p ω
        (buildLevelNonSingletonBack2 (b + 14))
        st7 o st' c2 ∧
      (o = .returned vFinal ∧
        ListAt st'.mem h (D_level.encode k) ∧
        (∀ a < h, st'.mem a = initMem a) ∧
        ZeroFrom st'.mem vFinal) ∧
      c2 ≤ (17 * (s0Words.length + s1Words.length + s2Words.length) + 12) + 120 := by
    refine runs_start_le ?_
    unfold buildLevelNonSingletonBack2
    have hH1W : h + 1 < 2 ^ w := by omega
    have hH2W : h + 2 < 2 ^ w := by omega
    have hH3W : h + 3 < 2 ^ w := by omega
    have hH4W : h + 4 < 2 ^ w := by omega
    have hkkW : k * k < 2 ^ w := by dsimp [end2] at hEnd2W; omega
    have hEnd1kkW : end1 + k * k < 2 ^ w := by dsimp [end2] at hEnd2W; omega
    have hEnd1kk1W : end1 + k * k + 1 < 2 ^ w := by dsimp [end2] at hEnd2W; omega
    have hLen0Eq : end0 - outStart = s0Words.length := by dsimp [end0]; omega
    have hLen01Eq : end1 - outStart = s0Words.length + s1Words.length := by dsimp [end1, end0]; omega
    have hLen012Eq : end2 - outStart = s0Words.length + s1Words.length + s2Words.length := by
      dsimp [end2, end1, end0]; omega
    have hTotLenW : s0Words.length + s1Words.length + s2Words.length < 2 ^ w := by omega
    -- Step 7a: compute end2 = end1 + k * k + 1 + mem[end1 + k * k] in reg 32
    refine runs_seq_assign_le (v := k * k)
      (Expr.eval_mul (Expr.eval_reg_of_eq h7r4) (Expr.eval_reg_of_eq h7r4) hkkW) ?_
    refine runs_seq_assign_le (v := end2)
      (by have h1 : end1 + k * k + 1 + st7.mem (end1 + k * k) = end2 := by dsimp [end2]; omega
          rw [← h1]
          exact Expr.eval_add
            (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7r30))
              (Expr.eval_reg_of_eq (by simp)) hEnd1kkW) (Expr.eval_const (by omega)) hEnd1kk1W)
            (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7r30))
              (Expr.eval_reg_of_eq (by simp)) hEnd1kkW))
            (by rw [h1]; exact hEnd2W)) ?_
    -- Step 7b: call 33 fCopy [outStart, end2 - outStart, h + 4]
    have hCopyPre : (buildCopyDownContract w).pre
        [outStart, s0Words.length + s1Words.length + s2Words.length, h + 4] st7.mem :=
      ⟨outStart, s0Words.length + s1Words.length + s2Words.length, h + 4, rfl, hH4LeOut,
       by dsimp [end2, end1, end0] at hEnd2W; omega, by omega⟩
    refine runs_seq_call_le hSpecCopy
      (vs := [outStart, s0Words.length + s1Words.length + s2Words.length, h + 4])
      (by simp [evalArgs, Expr.eval, BinOp.eval, h7r11, h7r28, h4W, hH4W, hTotLenW, hLen012Eq])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> assumption)
      hCopyPre ?_
    intro _ m8 _ hPost8
    obtain ⟨_, _, _, heq8, hCopied8, hFr8⟩ := hPost8
    simp only [List.cons.injEq, and_true] at heq8
    obtain ⟨rfl, rfl, rfl⟩ := heq8
    have hPayAt8 : ListAt m8 (h + 4) ((s0Words ++ s1Words) ++ s2Words) := by
      intro i hi
      have hi' : i < s0Words.length + s1Words.length + s2Words.length := by
        simpa only [List.length_append] using hi
      exact (hCopied8 i hi').trans (hPayAt7 i hi)
    have hFr8H : ∀ a < h, m8 a = initMem a := fun a ha =>
      (hFr8 a (Or.inl (by omega))).trans (hFr7H a ha)
    have hZ8 : ZeroFrom m8 vFinal := fun a ha =>
      (hFr8 a (Or.inr (by dsimp [end2, end1, end0] at hEnd2LeV ⊢; omega))).trans (hZ7 a ha)
    -- Step 8: store the 4 top-level layoutList header words
    refine runs_seq_store_le (x := h) (v := 0)
      (Expr.eval_reg_of_eq (by simpa using h7r11)) (Expr.eval_const (Nat.two_pow_pos _)) ?_
    refine runs_seq_store_le (x := h + 1) (v := s0Words.length)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7r11)) (Expr.eval_const (by omega)) hH1W)
      (by rw [← hLen0Eq]; exact Expr.eval_sub (Expr.eval_reg_of_eq (by simpa using h7r29))
            (Expr.eval_reg_of_eq (by simpa using h7r28)) hEnd0W) ?_
    refine runs_seq_store_le (x := h + 2) (v := s0Words.length + s1Words.length)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7r11)) (Expr.eval_const (by omega)) hH2W)
      (by rw [← hLen01Eq]; exact Expr.eval_sub (Expr.eval_reg_of_eq (by simpa using h7r30))
            (Expr.eval_reg_of_eq (by simpa using h7r28)) hEnd1W) ?_
    refine runs_seq_store_le (x := h + 3) (v := s0Words.length + s1Words.length + s2Words.length)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h7r11)) (Expr.eval_const (by omega)) hH3W)
      (by rw [← hLen012Eq]; exact Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_reg_of_eq (by simpa using h7r28)) hEnd2W) ?_
    -- Step 9: return vFinal
    refine runs_ret_le (v := vFinal) (Expr.eval_reg_of_eq (by simpa using h7r31)) ?_ ?_
    · let mFinal := Function.update (Function.update (Function.update (Function.update m8 h 0)
          (h + 1) s0Words.length) (h + 2) (s0Words.length + s1Words.length))
          (h + 3) (s0Words.length + s1Words.length + s2Words.length)
      have hMFinalAbove : ∀ a, h + 4 ≤ a → mFinal a = m8 a := fun a ha => by
        dsimp [mFinal]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hMFinalBelow : ∀ a < h, mFinal a = initMem a := fun a ha => by
        dsimp [mFinal]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hFr8H a ha
      have hListAt : ListAt mFinal h (D_level.encode k) := by
        have hL3 : D_level.encode k =
            [0, s0Words.length, s0Words.length + s1Words.length,
              s0Words.length + s1Words.length + s2Words.length] ++
              ((s0Words ++ s1Words) ++ s2Words) := by
          rw [hEncEq, layoutList3_eq]
        rw [hL3]
        apply listAt_append.mpr
        constructor
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          interval_cases i <;> simp [mFinal, Function.update]
        · simp only [List.length_cons, List.length_nil]
          exact WordRAM.ListAt.congr hPayAt8 fun a ha _ => hMFinalAbove a ha
      have hZFinal : ZeroFrom mFinal vFinal := fun a ha =>
        (hMFinalAbove a (by dsimp [end2, end1, end0] at hEnd2LeV ⊢; omega)).trans (hZ8 a ha)
      exact ⟨rfl, hListAt, hMFinalBelow, hZFinal⟩
    · simp only [buildCopyDownContract, buildCopyContract,
        List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
      omega
  obtain ⟨_, st', c2, hRun2, ⟨rfl, hListAt, hMFinalBelow, hZFinal⟩, hC2⟩ := hBack2
  have hEncLeV : h + (D_level.encode k).length ≤ vFinal := by
    rw [hEncLen]; dsimp [end2, end1, end0] at hEnd2LeV ⊢; omega
  exact ⟨vFinal, st', c1 + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨st7, c1, c2, hRun1, hRun2, rfl⟩),
    hEncLeV, hVLeConn.trans hEnd1ConnLeSpace, hListAt, hMFinalBelow, hZFinal,
    by dsimp only [s0Words, s1Words, s2Words, maxM, T, limit, d] at hC1 hC2 ⊢; omega⟩

end MinCostFlow.HierPaths
