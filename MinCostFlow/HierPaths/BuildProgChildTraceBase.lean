module

public import MinCostFlow.HierPaths.BuildProgInjectEnd
public import MinCostFlow.HierPaths.BuildProgLevelTrace
import MinCostFlow.HierPaths.BuildProgGameStepMemory
import MinCostFlow.HierPaths.BuildProgChoiceSaved
import MinCostFlow.HierPaths.InitBlockLen
import MinCostFlow.HierPaths.InitLayout

/-!
# Definitions and cursor bounds for the finished child-game archive

Defines the archive invariants (`RoundArchive`, `TraceRoundsMem`, `InjArchive`), the per-round
non-hole budget `roundNonHoleCap`, and the arithmetic and cursor lemmas shared by the loop trace
and final injection archive proofs.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Uniform upper bound on the non-hole words allocated by one executed round or the final
injection (excluding core scan bump gaps). -/
def roundNonHoleCap (s k d : ℕ) : ℕ :=
  12 * (s * k) + 3 * (s * k * d) + s + 12 * k + 2 * d + 40

/-- Uniform upper bound on the heap advance of the core scan across one round of `D`. -/
def roundCoreCap (D : ChoiceLoopData) : ℕ :=
  D.count * ((Finset.range (D.geometry.slotWords + 1)).sup D.base.coreSpace + 3 * D.base.childSize)

/-- Uniform upper bound on the router bump gap for one full-routing call of `D`. -/
def roundRouteCap (D : ChoiceLoopData) : ℕ :=
  (D.base.verts.card + 1) *
    (Finset.range (2 * D.count + 1 + D.count * D.base.childSize + 1)).sup
      (fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
        pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card))

/-- The memory archive of one round slot `[lo, hi)`. -/
def RoundArchive (G : Graph) (start s k d bumpCap : ℕ) (mem : ℕ → ℕ) (lo hi rec : ℕ)
    (walks : ℕ → List (List ℕ)) (hole : Option ℕ) : Prop :=
  if rec = 0 then
    (∀ c, walks c = []) ∧ hole = none ∧ hi = lo
  else
    ∃ (prep oldCount : ℕ) (act : ℕ → ℕ) (numCuts : ℕ) (cutIdx : ℕ → ℕ),
      lo ≤ prep ∧ prep ≤ rec ∧ rec + 2 + oldCount = hi ∧ 1 ≤ oldCount ∧ oldCount ≤ k ∧
      mem rec = prep ∧ mem (rec + 1) = oldCount ∧
      (∀ i < oldCount, act i < k ∧ mem (rec + 2 + i) = start + act i * s) ∧
      (∀ i < oldCount, ∀ j < oldCount, act i = act j → i = j) ∧
      mem prep = numCuts ∧ numCuts ≤ oldCount ∧
      (∀ j < numCuts, cutIdx j < oldCount ∧ mem (prep + 1 + j) = cutIdx j) ∧
      (∀ j₁ < numCuts, ∀ j₂ < numCuts, cutIdx j₁ = cutIdx j₂ → j₁ = j₂) ∧
      if numCuts = 0 then
        (∀ c, walks c = []) ∧ hole = none ∧ hi - lo ≤ roundNonHoleCap s k d + bumpCap
      else
        ∃ (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) (routedEnd : ℕ),
          Ms.length = numCuts ∧ (∀ j < numCuts, (Ms.getD j []).length ≤ s) ∧
          let batch := prep + 1 + oldCount
          let rep := buildBatchEnd batch numCuts s
          let walkDir := routedEnd + 4
          let P := walkDir + Ms.flatten.length + d + 1
          lo ≤ rep ∧ mem batch = routedEnd ∧
          rep + (routeResultWords (.matched Ms emb)).length ≤ routedEnd ∧ routedEnd ≤ rec ∧
          ListAt mem rep (routeResultWords (.matched Ms emb)) ∧
          hole = some P ∧ lo ≤ P ∧ P + G.n ≤ rec ∧
          (∀ a < G.n, mem (P + a) = 0) ∧
          (∀ j < numCuts, ∀ e < (Ms.getD j []).length,
            let row := matchingWalkRow Ms emb j
            let w := erase G.edges (row.u e) (row.raw e)
            let addr := mem (walkDir + flatIndex Ms j 0 + e)
            lo ≤ addr ∧ addr + 1 + w.length ≤ rec ∧ SeqAt mem addr w) ∧
          (∀ j < numCuts, walks (act (cutIdx j)) =
            (List.range (Ms.getD j []).length).map fun e =>
              let row := matchingWalkRow Ms emb j
              erase G.edges (row.u e) (row.raw e)) ∧
          (∀ c < k, (∀ j < numCuts, act (cutIdx j) ≠ c) → walks c = []) ∧
          hi - lo - G.n ≤ roundNonHoleCap s k d + bumpCap

/-- The round archive across the first `t` iterations of `ChoiceLoopTrace`. -/
def TraceRoundsMem (D : ChoiceLoopData) (t heap : ℕ) (sts : ℕ → ChildState)
    (mem : ℕ → ℕ) : Prop :=
  (∀ r, t ≤ r → r < D.limit → mem (D.directory + r) = 0) ∧
  ∃ (bounds : ℕ → ℕ) (walks : ℕ → ℕ → List (List ℕ)) (holes : ℕ → Option ℕ),
    bounds 0 = D.addrs.heap ∧ bounds t = heap ∧
    (∀ r < t, bounds r ≤ bounds (r + 1)) ∧
    (∀ r < t, RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
      (roundCoreCap D + roundRouteCap D) mem (bounds r) (bounds (r + 1))
      (mem (D.directory + r)) (walks r) (holes r)) ∧
    (∀ c < D.count, (sts c).rounds.flatten.map Prod.snd =
      (List.range t).flatMap fun r => walks r c)

/-- The archive left by the final injection at `[heap₁, injEnd)` and in the child graph slots. -/
def InjArchive (G : Graph) (s k d routeCap slot slotWords heap₁ injEnd : ℕ)
    (F : ℕ → List ((ℕ × ℕ) × List ℕ)) (preWalks : ℕ → List (List ℕ)) (mem : ℕ → ℕ) : Prop :=
  ∃ (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) (routedEnd : ℕ),
    Ms.length = k ∧ (∀ c < k, (Ms.getD c []).length ≤ s) ∧
    let rep := injectReplyBase heap₁ k s
    let walkDir := routedEnd + 4
    let P := walkDir + Ms.flatten.length + d + 1
    heap₁ ≤ rep ∧ mem heap₁ = routedEnd ∧
    rep + (routeResultWords (.matched Ms emb)).length ≤ routedEnd ∧ routedEnd ≤ injEnd ∧
    ListAt mem rep (routeResultWords (.matched Ms emb)) ∧
    heap₁ ≤ P ∧ P + G.n ≤ injEnd ∧
    (∀ a < G.n, mem (P + a) = 0) ∧
    (∀ c < k, GraphAt mem (slot + c * slotWords) ⟨s, (F c).map Prod.fst⟩) ∧
    (∀ c < k, ∀ e < (Ms.getD c []).length,
      let row := matchingWalkRow Ms emb c
      let w := erase G.edges (row.u e) (row.raw e)
      let addr := mem (walkDir + flatIndex Ms c 0 + e)
      heap₁ ≤ addr ∧ addr + 1 + w.length ≤ injEnd ∧ SeqAt mem addr w) ∧
    (∀ c < k, (F c).map Prod.snd = preWalks c ++
      (List.range (Ms.getD c []).length).map fun e =>
        let row := matchingWalkRow Ms emb c
        erase G.edges (row.u e) (row.raw e)) ∧
    injEnd - heap₁ - G.n ≤ roundNonHoleCap s k d + routeCap ∧
    ZeroFrom mem injEnd

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

theorem flatIndex_zero_add {α : Type*} (Ms : List (List α)) (j e : ℕ) :
    flatIndex Ms j 0 + e = flatIndex Ms j e := by
  simp [flatIndex]

theorem flatIndex_lt_flatten {Ms : List (List (ℕ × ℕ))} {j e : ℕ}
    (hj : j < Ms.length) (he : e < (Ms.getD j []).length) :
    flatIndex Ms j 0 + e < Ms.flatten.length := by
  rw [flatIndex_zero_add]
  exact (getD_flatten_flatIndex Ms (0, 0) hj he).1

/-- The third offset word of `routeResultWords (.matched Ms emb)` gives its exact length minus 4. -/
theorem routeMatched_end_offset {mem : ℕ → ℕ} {rep : ℕ} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (hAt : ListAt mem rep (routeResultWords (.matched Ms emb))) :
    mem (rep + 3) + 4 = (routeResultWords (.matched Ms emb)).length := by
  let bs : List (List ℕ) :=
    [[0], csrList Ms.length (matchingRowWords Ms), csrList Ms.flatten.length emb]
  have hAt' : ListAt mem rep (layoutList bs) := hAt
  have hOff := csrList_offset hAt' (le_refl 3)
  have hLen : (routeResultWords (.matched Ms emb)).length = (layoutList bs).length := rfl
  rw [length_layoutList] at hLen
  simp only [bs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.range_succ, List.map_append,
    List.sum_append, List.getD_cons_zero, List.getD_cons_succ, List.range_zero] at hLen hOff
  change mem (rep + 3) = _ at hOff
  omega

/-- Framing `[lo, hi)` preserves `RoundArchive`. -/
theorem RoundArchive.frame {G : Graph} {start s k d coreCap lo hi rec : ℕ}
    {walks : ℕ → List (List ℕ)} {hole : Option ℕ} {mem after : ℕ → ℕ}
    (h : RoundArchive G start s k d coreCap mem lo hi rec walks hole)
    (hEq : ∀ a, lo ≤ a → a < hi → after a = mem a) :
    RoundArchive G start s k d coreCap after lo hi rec walks hole := by
  unfold RoundArchive at h ⊢
  split_ifs at h ⊢ with h0
  · exact h
  · obtain ⟨prep, oldCount, act, numCuts, cutIdx, hlp, hpr, hhi, ho1, hok, hmp, hmo, hact,
      hactInj, hmnum, hnumLe, hcut, hcutInj, hRest⟩ := h
    refine ⟨prep, oldCount, act, numCuts, cutIdx, hlp, hpr, hhi, ho1, hok,
      (hEq _ (hlp.trans hpr) (by omega)).trans hmp,
      (hEq _ (by omega) (by omega)).trans hmo,
      fun i hi' => ⟨(hact i hi').1, (hEq _ (by omega) (by omega)).trans (hact i hi').2⟩,
      hactInj,
      (hEq _ hlp (by omega)).trans hmnum, hnumLe,
      fun j hj => ⟨(hcut j hj).1, (hEq _ (by omega) (by omega)).trans (hcut j hj).2⟩,
      hcutInj, ?_⟩
    split_ifs at hRest ⊢ with hnc
    · exact hRest
    · obtain ⟨Ms, emb, routedEnd, hMlen, hRowLe, hloRep, hMemBatch, hRepEndLe, hEndRec, hRepAt,
        hHole, hloP, hPRec, hZeroP, hWalks, hWmatch, hWother, hSize⟩ := hRest
      let batch := prep + 1 + oldCount
      let rep := buildBatchEnd batch numCuts s
      have hBatchLtRep : batch < rep := by dsimp [rep, buildBatchEnd]; omega
      refine ⟨Ms, emb, routedEnd, hMlen, hRowLe, hloRep,
        (hEq _ (by omega) (by dsimp [rep, batch] at hBatchLtRep; omega)).trans hMemBatch,
        hRepEndLe, hEndRec,
        WordRAM.ListAt.congr hRepAt (fun a ha hb => hEq a (hloRep.trans ha) (by omega)),
        hHole, hloP, hPRec,
        fun a ha => (hEq _ (by omega) (by omega)).trans (hZeroP a ha),
        fun j hj e he => ?_, hWmatch, hWother, hSize⟩
      obtain ⟨hloA, hARec, hSeq⟩ := hWalks j hj e he
      have hfl : flatIndex Ms j 0 + e < Ms.flatten.length :=
        flatIndex_lt_flatten (hMlen.symm ▸ hj) he
      have hDirLt : routedEnd + 4 + flatIndex Ms j 0 + e < rec := by omega
      have hDirGe : lo ≤ routedEnd + 4 + flatIndex Ms j 0 + e := by omega
      have hAddrEq := hEq _ hDirGe (by omega)
      refine ⟨hAddrEq.symm ▸ hloA, hAddrEq.symm ▸ hARec, ?_⟩
      rw [hAddrEq]
      exact seqAt_frame hSeq (fun a ha hb => hEq a (hloA.trans ha) (by omega))

private theorem sum_map_range_le {n B : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j ≤ B) :
    ((List.range n).map f).sum ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Nat.succ_mul]
    have h1 := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    have h2 := h n (Nat.lt_succ_self n)
    omega

private theorem sum_matchingRowWords_eq (Ms : List (List (ℕ × ℕ))) :
    ((List.range Ms.length).map fun j => (matchingRowWords Ms j).length).sum =
      2 * Ms.flatten.length := by
  have hgen : ∀ n ≤ Ms.length,
      ((List.range n).map fun j => (matchingRowWords Ms j).length).sum =
        2 * (Ms.take n).flatten.length := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ih (Nat.le_of_succ_le hn), length_matchingRowWords,
        List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
        List.flatten_singleton, List.getD_eq_getElem _ _ hn]
      omega
  simpa using hgen Ms.length le_rfl

private theorem buildWalkRow_cursor_le (R : BuildWalkRow) (out d : ℕ)
    (hlen : ∀ j < R.count, (R.raw j).length ≤ d) :
    R.cursor out R.count ≤ out + R.count * (d + 1) := by
  have hgen : ∀ n ≤ R.count, R.cursor out n ≤ out + n * (d + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [BuildWalkRow.cursor]
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := hlen n hn
      simp only [BuildWalkRow.cursor, Nat.succ_mul]
      omega
  exact hgen R.count le_rfl

/-- Total arena advance of `ApplyBatchData.cursor` is at most `Ms.flatten.length * (d + 1)`. -/
theorem applyBatch_cursor_le (A : ApplyBatchData) (out d : ℕ)
    (hlen : ∀ j < A.matchings.flatten.length, (A.emb j).length ≤ d) :
    A.cursor out A.matchings.length ≤ out + A.matchings.flatten.length * (d + 1) := by
  have hgen : ∀ n ≤ A.matchings.length,
      A.cursor out n ≤ out + ((A.matchings.take n).flatten).length * (d + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [ApplyBatchData.cursor]
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.le_of_succ_le hn)
      have hrow : (A.row n).cursor (A.cursor out n) (A.row n).count ≤
          A.cursor out n + (A.row n).count * (d + 1) := by
        apply buildWalkRow_cursor_le
        intro j hj
        apply hlen
        exact flatIndex_lt_flatten hn hj
      have htake : (A.matchings.take (n + 1)).flatten.length =
          (A.matchings.take n).flatten.length + (A.matchings.getD n []).length := by
        rw [List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
          List.flatten_singleton, List.getD_eq_getElem _ _ hn]
      simp only [ApplyBatchData.cursor]
      rw [htake, Nat.add_mul]
      have hcnt : (A.row n).count = (A.matchings.getD n []).length := rfl
      exact hrow.trans (by rw [hcnt]; omega)
  simpa using hgen A.matchings.length le_rfl

/-- Length bound on `routeResultWords (.matched Ms emb)`. -/
theorem routeMatched_length_le {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {d : ℕ}
    (hlen : ∀ j < Ms.flatten.length, (emb j).length ≤ d) :
    (routeResultWords (.matched Ms emb)).length ≤
      7 + Ms.length + 3 * Ms.flatten.length + Ms.flatten.length * d := by
  change (layoutList [[0], csrList Ms.length (matchingRowWords Ms),
    csrList Ms.flatten.length emb]).length ≤ _
  rw [length_layoutList]
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  have h1 : (csrList Ms.length (matchingRowWords Ms)).length =
      Ms.length + 1 + 2 * Ms.flatten.length := by
    rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq, sum_matchingRowWords_eq]
  have h2 : (csrList Ms.flatten.length emb).length ≤
      Ms.flatten.length + 1 + Ms.flatten.length * d := by
    rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
    have hsum := sum_map_range_le hlen
    omega
  omega

theorem flatten_length_le_mul {Ms : List (List (ℕ × ℕ))} {s : ℕ}
    (h : ∀ i < Ms.length, (Ms.getD i []).length ≤ s) :
    Ms.flatten.length ≤ Ms.length * s := by
  have hgen : ∀ n ≤ Ms.length, (Ms.take n).flatten.length ≤ n * s := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
        List.flatten_singleton, Nat.succ_mul]
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := h n hn
      rw [List.getD_eq_getElem _ _ hn] at h2
      omega
  simpa using hgen Ms.length le_rfl

theorem prepPrefix_le_validBump {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult} {bump : ℕ → ℕ}
    (hBump : (D.round sts).ValidBump answer bump)
    (hSlot : ∀ i < (D.round sts).jobs.count,
      ((D.round sts).jobs.graph i).encode.length ≤ D.geometry.slotWords)
    (heap : ℕ) :
    let B := (D.round sts).withReplies answer bump
    B.prepared (D.atHeap heap) ≤ heap + roundCoreCap D := by
  let B := (D.round sts).withReplies answer bump
  set coreMax := (Finset.range (D.geometry.slotWords + 1)).sup D.base.coreSpace
  have hgen : ∀ i ≤ B.jobs.count,
      B.jobs.prepPrefix B.core B.q heap i ≤ heap + i * (coreMax + 3 * B.childSize) := by
    intro i
    induction i with
    | zero => intro _; simp [BuildGameJobs.prepPrefix]
    | succ i ih =>
      intro hi
      have hj : i < B.jobs.count := Nat.lt_of_succ_le hi
      have hPrev := ih hj.le
      have hAns : B.jobs.answer B.core B.q i = answer i := rfl
      have hn : (B.jobs.graph i).n = B.childSize := rfl
      have hStep : preparedChildEnd 0 B.childSize (answer i) + bump i ≤
          D.base.coreSpace (B.jobs.graph i).encode.length + 3 * B.childSize := hBump i hj
      have hSup : D.base.coreSpace (B.jobs.graph i).encode.length ≤ coreMax :=
        Finset.le_sup (f := D.base.coreSpace) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hSlot i hj)))
      have hPrep : preparedChildEnd (B.jobs.prepPrefix B.core B.q heap i) B.childSize (answer i) =
          B.jobs.prepPrefix B.core B.q heap i + preparedChildEnd 0 B.childSize (answer i) := by
        cases answer i <;> simp only [preparedChildEnd] <;> omega
      change B.jobs.prepPrefix B.core B.q heap (i + 1) ≤ heap + (i + 1) * (coreMax + 3 * B.childSize)
      simp only [BuildGameJobs.prepPrefix, BuildGameJobs.bumpSize, hAns, hn, Nat.add_mul, Nat.one_mul]
      change preparedChildEnd (B.jobs.prepPrefix B.core B.q heap i) B.childSize (answer i) + bump i ≤ _
      rw [hPrep]
      omega
  have h1 := hgen B.jobs.count le_rfl
  have hcnt : B.jobs.count ≤ D.count := D.active_le sts
  have h2 := Nat.mul_le_mul_right (coreMax + 3 * B.childSize) hcnt
  exact h1.trans (Nat.add_le_add_left h2 heap)

theorem round_nonhole_arith {s k d oldCount numCuts flatLen repLen : ℕ}
    (ho : oldCount ≤ k) (hn : numCuts ≤ oldCount) (hfl : flatLen ≤ k * s)
    (hrep : repLen ≤ 7 + numCuts + 3 * flatLen + flatLen * d) :
    s + oldCount * (4 + 4 * s) + (1 + oldCount) + (2 * numCuts + 1 + numCuts * s) +
      repLen + 4 + flatLen + d + 1 + flatLen * (d + 1) + 2 + oldCount ≤
      roundNonHoleCap s k d := by
  have h1 : oldCount * (4 + 4 * s) ≤ k * (4 + 4 * s) := Nat.mul_le_mul_right _ ho
  have h2 : numCuts * s ≤ k * s := Nat.mul_le_mul_right _ (hn.trans ho)
  have h3 : flatLen * d ≤ (s * k) * d := by
    rw [Nat.mul_comm s k]; exact Nat.mul_le_mul_right d hfl
  have h4 : flatLen * (d + 1) = flatLen * d + flatLen := by ring
  have h5 : k * (4 + 4 * s) = 4 * k + 4 * (s * k) := by ring
  have h6 : k * s = s * k := Nat.mul_comm k s
  unfold roundNonHoleCap
  omega

theorem round_nonhole_bump_arith {s k d coreCap oldCount numCuts flatLen repLen : ℕ}
    (ho : oldCount ≤ k) (hn : numCuts ≤ oldCount) (hfl : flatLen ≤ k * s)
    (hrep : repLen ≤ 7 + numCuts + 3 * flatLen + flatLen * d) :
    coreCap + (1 + oldCount) + (2 * numCuts + 1 + numCuts * s) +
      repLen + 4 + flatLen + d + 1 + flatLen * (d + 1) + 2 + oldCount ≤
      roundNonHoleCap s k d + coreCap := by
  have hBase := round_nonhole_arith (s := s) (k := k) (d := d) ho hn hfl hrep
  omega

/-- Each archived round advances the heap by at most `roundNonHoleCap s k d + coreCap + G.n`. -/
theorem RoundArchive.step_le {G : Graph} {start s k d coreCap lo hi rec : ℕ}
    {walks : ℕ → List (List ℕ)} {hole : Option ℕ} {mem : ℕ → ℕ}
    (h : RoundArchive G start s k d coreCap mem lo hi rec walks hole) :
    hi ≤ lo + roundNonHoleCap s k d + coreCap + (if hole.isSome then G.n else 0) := by
  unfold RoundArchive at h
  split_ifs at h with h0
  · rcases h with ⟨_, hhole, hhi⟩
    rw [hhole]; simp; omega
  · obtain ⟨prep, oldCount, act, numCuts, cutIdx, hlp, hpr, hhi, ho1, hok, _, _, _, _, _, _, _, _, hRest⟩ := h
    split_ifs at hRest with hnc
    · rcases hRest with ⟨_, hhole, hsz⟩
      rw [hhole]; simp; omega
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, hhole, _, _, _, _, _, _, hsz⟩ := hRest
      rw [hhole]; simp; omega

/-- Length bound on `pairsWords` when every pair has total cardinality at most `s`. -/
theorem pairsWords_length_le_card {s : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (h : ∀ p ∈ pairs, p.1.card + p.2.card ≤ s) :
    (pairsWords pairs).length ≤ 2 * pairs.length + 1 + pairs.length * s := by
  induction pairs with
  | nil => simp [pairsWords, length_layoutList]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [pairsWords, length_layoutList, List.flatMap_cons, List.cons_append,
      List.nil_append, List.length_cons, List.map_cons, List.sum_cons, finsetWords,
      Finset.length_sort, Nat.succ_mul] at ht ⊢
    omega

/-- After `t` rounds, the heap cursor is bounded by
`D.addrs.heap + t * (roundNonHoleCap s k d + roundCoreCap D + roundRouteCap D + G.n)`. -/
theorem trace_heap_le {D : ChoiceLoopData} {t heap : ℕ} {sts : ℕ → ChildState} {mem : ℕ → ℕ}
    (h : TraceRoundsMem D t heap sts mem) :
    heap ≤ D.addrs.heap +
      t * (roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        (roundCoreCap D + roundRouteCap D) + D.base.host.n) := by
  obtain ⟨_, bounds, walks, holes, hb0, hbt, _, hArch, _⟩ := h
  have hgen : ∀ r ≤ t, bounds r ≤ D.addrs.heap +
      r * (roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        (roundCoreCap D + roundRouteCap D) + D.base.host.n) := by
    intro r
    induction r with
    | zero => intro _; simp [hb0]
    | succ r ih =>
      intro hr
      have h1 := ih (Nat.le_of_succ_le hr)
      have h2 := (hArch r hr).step_le
      have h3 : (if (holes r).isSome then D.base.host.n else 0) ≤ D.base.host.n := by
        split_ifs <;> omega
      rw [Nat.succ_mul]
      omega
  rw [← hbt]
  exact hgen t le_rfl

/-- Total non-hole words across all `t` rounds of `TraceRoundsMem`. -/
theorem trace_nonHole_le {D : ChoiceLoopData} {t heap : ℕ} {mem : ℕ → ℕ}
    {bounds : ℕ → ℕ} {walks : ℕ → ℕ → List (List ℕ)} {holes : ℕ → Option ℕ}
    (hb0 : bounds 0 = D.addrs.heap) (hbt : bounds t = heap)
    (hArch : ∀ r < t, RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
      (roundCoreCap D + roundRouteCap D) mem (bounds r) (bounds (r + 1)) (mem (D.directory + r)) (walks r) (holes r)) :
    heap ≤ D.addrs.heap +
      t * (roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        (roundCoreCap D + roundRouteCap D)) +
      ((List.range t).filter fun r => (holes r).isSome).length * D.base.host.n := by
  have hgen : ∀ n ≤ t, bounds n ≤ D.addrs.heap +
      n * (roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        (roundCoreCap D + roundRouteCap D)) +
      ((List.range n).filter fun r => (holes r).isSome).length * D.base.host.n := by
    intro n
    induction n with
    | zero => intro _; simp [hb0]
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := (hArch n hn).step_le
      rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton, Nat.succ_mul]
      cases h : (holes n).isSome <;> simp [h, Nat.succ_mul] at h2 ⊢ <;> omega
  rw [← hbt]
  exact hgen t le_rfl

end MinCostFlow.HierPaths
