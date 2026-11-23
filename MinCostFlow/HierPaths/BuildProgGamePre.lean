module

public import MinCostFlow.HierPaths.BuildProgGameSlots

/-!
# The memory precondition of a scheduled round

At each round the active arrays and the child graphs have the model's
current values. Fixed reservations separate the child writes from the
inputs. The caller only needs to allocate enough space for the arena.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The input and child graph blocks at a prefix of the scheduled loop. -/
structure GameMemory (S : BuildGameSchedule) (t : ℕ) (mem : ℕ → ℕ) : Prop where
  host : GraphAt mem S.addrs.host S.base.host
  verts : ListAt mem S.addrs.verts (finsetWords S.base.verts)
  graphs : ListAt mem S.addrs.graphs (tabList (S.round t).jobs.count (S.round t).jobs.addr)
  offsets : ListAt mem S.addrs.offsets (tabList (S.round t).jobs.count (S.round t).jobs.offset)
  children : ∀ c < S.count, GraphAt mem (S.childAddr c) (gameGraph S.base.childSize (S.states t c))
  zero : ZeroFrom mem (S.heap t)

/-- Word bounds for the arena, including each player's temporary space. -/
structure GameArenaWords (w : ℕ) (S : BuildGameSchedule) : Prop where
  heap : ∀ t ≤ S.data.limit, S.heap t < 2^w
  core : ∀ t < S.data.limit, ∀ i < (S.round t).jobs.count,
    let B := S.round t
    B.jobs.prepPrefix B.core B.q (S.heap t) i + B.coreSpace (B.jobs.graph i).encode.length +
      3 * (B.jobs.graph i).n < 2^w
  route : ∀ t < S.data.limit,
    let B := S.round t
    B.routeReply (S.data.addrs t) +
      (B.verts.card + 1) * routerSpaceUpTo B.routeSpace B.host.n B.host.encode.length
        (pairsWords B.pairs).length (B.Δ + B.L + max 2 B.verts.card) < 2^w

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Addresses of child graphs are fixed as the arena grows. -/
theorem BuildGamePlayerBounds.heap_mono_of_players {S : BuildGameSchedule} {cfg : ParamConfig}
    {β : ℝ} {bh : ℕ} (hP : BuildGamePlayerBounds S cfg β bh) {t : ℕ}
    (ht : t ≤ S.data.limit) : S.addrs.heap ≤ S.heap t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    let B := S.round t
    let A := S.data.addrs t
    have hPrev := ih (by omega)
    have hGe : S.heap t ≤ B.prepared A :=
      B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
    by_cases hn : B.jobs.count = 0
    · change S.addrs.heap ≤ if B.jobs.count = 0 then S.heap t else B.record A + 2 + B.jobs.count
      rw [ite_eq_left hn]
      exact hPrev
    · have hb : B.prepared A ≤ B.record A := by
        unfold BuildRoundData.record
        by_cases he : B.indices.isEmpty = true
        · simp [he]; omega
        · have hne : B.indices.isEmpty = false := Bool.eq_false_iff.mpr he
          obtain ⟨Ms,emb,hRes,_,_,_⟩ := hP.matched (show t < S.data.limit by omega) hne
          change B.result.1 = _ at hRes
          simp only [hne, Bool.false_eq_true, ite_false, hRes]
          have hR : B.prepared A ≤ B.routedEnd A := by
            simp only [BuildRoundData.routedEnd,BuildRoundData.routeReply,buildBatchEnd]
            omega
          have hC := (B.applyData Ms emb).cursor_mono
            (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n) (Nat.zero_le Ms.length)
          change B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n ≤ _ at hC
          exact hR.trans (Nat.le_trans (by omega) hC)
      change S.addrs.heap ≤ if B.jobs.count = 0 then S.heap t else B.record A + 2 + B.jobs.count
      rw [ite_eq_right hn]
      omega

private theorem localEndpoints {S : BuildGameSchedule} {cfg : ParamConfig}
    {β : ℝ} {bh w t : ℕ} (hP : BuildGamePlayerBounds S cfg β bh) (hL : GameFixedLayout w S)
    (ht : t < S.data.limit) {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hRes : (S.round t).result.1 = .matched Ms emb) (hne : (S.round t).indices.isEmpty = false) :
    let D := (S.round t).applyData Ms emb
    ∀ i < Ms.length, ∀ e ∈ Ms.getD i [],
      D.offset i ≤ e.1 ∧ D.offset i ≤ e.2 ∧ e.1 < 2^w ∧ e.2 < 2^w := by
  let B := S.round t
  let D := B.applyData Ms emb
  change ∀ i < Ms.length, ∀ e ∈ Ms.getD i [],
    D.offset i ≤ e.1 ∧ D.offset i ≤ e.2 ∧ e.1 < 2^w ∧ e.2 < 2^w
  obtain ⟨xs,f,he,hs,_,_⟩ := hP.matched ht hne
  rw [hRes] at he
  cases he
  intro i hi e he
  have hi' : i < B.pairs.length := hs.1 ▸ hi
  have hi'' : i < B.indices.length := (length_batchJobPairs .. : B.pairs.length = B.indices.length) ▸ hi'
  have hChosen : D.child i ∈ B.indices := by
    change B.indices.getD i 0 ∈ B.indices
    rw [List.getD_eq_getElem _ _ hi'']
    exact List.getElem_mem hi''
  obtain ⟨hChild,U,hCut⟩ := mem_batchJobIndices.mp hChosen
  let f := batchJobPair B.jobs B.core B.q B.childSize
  have hw : i < (B.indices.map f).length := by simpa using hi''
  have hEq : B.pairs[i] = f (D.child i) :=
    (List.getElem_map f (h := hw)).trans (congrArg f (List.getD_eq_getElem _ _ hi'').symm)
  have hSides := (hs.2.1 i hi').1 e he
  change e.1 ∈ B.pairs[i].1 ∧ e.2 ∈ B.pairs[i].2 at hSides
  rw [hEq] at hSides
  change e.1 ∈ (batchJobPair B.jobs B.core B.q B.childSize (D.child i)).1 ∧
    e.2 ∈ (batchJobPair B.jobs B.core B.q B.childSize (D.child i)).2 at hSides
  rw [batchJobPair,hCut] at hSides
  have hOut := hP.coreOutcome ht hChild
  change CoreOutcomeSpec cfg B.M B.r (B.jobs.graph (D.child i)) (B.jobs.answer B.core B.q (D.child i))
    at hOut
  rw [hCut] at hOut
  have hU : U ⊆ Finset.range B.childSize := hOut.1
  have hA := mem_shiftSet_iff.mp (shiftSet_subset (bisectOf_spec hU).1 hSides.1)
  have hB := mem_shiftSet_iff.mp (shiftSet_subset Finset.sdiff_subset hSides.2)
  have hWord : D.offset i + B.childSize < 2^w := hL.offsetWords _ (S.child_active hChild).1
  change B.jobs.offset (D.child i) + B.childSize < 2^w at hWord
  have h₁ := hA.1
  have h₂ := hB.1
  refine ⟨h₁,h₂,?_,?_⟩
  · have hh := Finset.mem_range.mp hA.2
    omega
  · have hh := Finset.mem_range.mp hB.2
    omega

/-- The core and router preconditions follow from the child-game invariant
and the word reservations. -/
theorem gameRoundFit_of_memory {w : ℕ} {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ}
    {bh t : ℕ} {mem : ℕ → ℕ}
    (hL : GameFixedLayout w S) (hP : BuildGamePlayerBounds S cfg β bh)
    (hSpace : GameArenaWords w S) (hV : S.base.host.IsValid)
    (hCap : routePathLen S.base.Δ bh S.base.L ≤ S.base.pathBound)
    (ht : t < S.data.limit) (hM : GameMemory S t mem) :
    BuildRoundFit w (S.round t) (S.data.addrs t) mem := by
  let B := S.round t
  let A := S.data.addrs t
  have hn : B.jobs.count ≤ S.count := S.count_le t
  have hOffsets := hL.offsets
  have hGraphs := hL.graphs
  have hHeap := hP.heap_mono_of_players ht.le
  have hRO : A.replies + B.jobs.count + 1 ≤ A.heap := by
    have hr := hL.replies
    change A.replies + S.count + 1 ≤ S.addrs.heap at hr
    change S.addrs.heap ≤ A.heap at hHeap
    omega
  have hHost : A.host + B.host.encode.length ≤ A.replies := by
    have hh := hL.host
    have hd := hL.directory
    have hv := hL.saved
    change S.addrs.host + S.base.host.encode.length ≤ S.addrs.replies
    omega
  have hVerts : A.verts + (finsetWords B.verts).length ≤ A.replies := by
    have hh := hL.verts
    have hd := hL.directory
    have hv := hL.saved
    change S.addrs.verts + (finsetWords S.base.verts).length ≤ S.addrs.replies
    omega
  have hA : 1 < 2^w := by have := hL.bits; omega
  refine ⟨?_,hM.host,hV,hM.verts,hHost,hVerts,hP.routerPre ht,hL.bits,hSpace.route t ht,?_,
    fun _ _ => rfl,?_,?_,?_,?_⟩
  · refine ⟨A.graphs,A.offsets,A.heap,A.replies,rfl,?_,?_,hRO,hA,hSpace.heap t ht.le,
      coreLevel_le hP.coreSize,hM.zero,hM.graphs,hM.offsets,?_⟩
    · change S.addrs.graphs + B.jobs.count ≤ S.addrs.replies
      omega
    · change S.addrs.offsets + B.jobs.count ≤ S.addrs.replies
      omega
    · intro i hi
      let G := B.jobs.graph i
      let c := S.child t i
      have hc : c < S.count := (S.child_active hi).1
      obtain ⟨hValid,hLoop,hLength,hDeg⟩ := hP.gameGraph_bounds ht.le hc
      have he : G.encode.length ≤ S.slotWords := by
        refine hLength.trans ?_
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      have hd : t ≤ deltaParam B.M := by
        have hD := hP.coreDegree
        change t < 49*S.L'+1 at ht
        change t ≤ deltaParam S.base.M
        omega
      refine ⟨⟨hM.children c hc,(Nat.add_le_add_left he _).trans (hL.slots c hc).2,
        hValid,hLoop,le_pow_coreLevel _ _ _,fun v hv => (hDeg v hv).trans hd,
        hL.size,hL.offsetWords c hc⟩,hSpace.core t ht i hi⟩
  · have := hP.even
    change 2 * (S.base.childSize / 2) = S.base.childSize
    omega
  · intro i hi U he
    have ho := hP.coreOutcome ht hi
    change CoreOutcomeSpec cfg B.M B.r (B.jobs.graph i) (B.jobs.answer B.core B.q i) at ho
    rw [he] at ho
    exact ho.1
  · intro i hi
    have ho := (hL.slots _ (S.child_active hi).1).1
    change S.addrs.graphs + B.jobs.count ≤ S.childAddr (S.child t i) ∧
      S.addrs.offsets + B.jobs.count ≤ S.childAddr (S.child t i)
    omega
  · intro hne
    obtain ⟨Ms,emb,he,_,_,hb⟩ := hP.matched ht hne
    have hb' : B.result.2 ≤ bh := by exact_mod_cast hb
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb')).trans hCap
  · intro Ms emb hne he
    let D := B.applyData Ms emb
    have hcnt := hP.rows ht (fun h => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr h)) he
    have hRow (i : ℕ) (hi : i < Ms.length) : D.child i < B.jobs.count := by
      have hl : i < B.indices.length := hcnt ▸ hi
      have hm : D.child i ∈ B.indices := by
        change B.indices.getD i 0 ∈ B.indices
        rw [List.getD_eq_getElem _ _ hl]
        exact List.getElem_mem hl
      exact (mem_batchJobIndices.mp hm).1
    have hChild (i : ℕ) (hi : i < Ms.length) : S.child t (D.child i) < S.count :=
      (S.child_active (hRow i hi)).1
    have hFit (i : ℕ) (hi : i < Ms.length) : D.cap i ≤ D.addr i + S.slotWords :=
      hP.matchedCap ht he hne hi
    refine ⟨⟨?_,?_,?_,?_⟩,localEndpoints hP hL ht he hne,?_⟩
    · intro i hi
      have hHd := hL.host
      have hDir := hL.directory
      have hSaved := hL.saved
      have hSlot := (hL.slots _ (hChild i hi)).1
      have he := buildGraph_encode_length S.base.host
      change S.addrs.host + 2 + 2 * S.base.host.m ≤ S.childAddr (S.child t (D.child i))
      omega
    · intro i hi
      exact (hFit i hi).trans (hL.slots _ (hChild i hi)).2
    · intro i hi j hj hij
      have hn' : S.child t (D.child i) ≠ S.child t (D.child j) := by
        intro he'
        have hh := S.child_injective t (hRow i hi) (hRow j hj) he'
        have hnd : B.indices.Nodup := List.nodup_range.filter _
        have hi' : i < B.indices.length := hcnt ▸ hi
        have hj' : j < B.indices.length := hcnt ▸ hj
        change B.indices.getD i 0 = B.indices.getD j 0 at hh
        rw [List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hj'] at hh
        exact hij ((hnd.getElem_inj_iff).mp hh)
      obtain ha | ha := hL.slotsApart _ (hChild i hi) _ (hChild j hj) hn'
      · exact Or.inl ((hFit i hi).trans ha)
      · exact Or.inr ((hFit j hj).trans ha)
    · intro i hi
      exact (Nat.le_add_right _ _).trans_lt (hL.offsetWords _ (hChild i hi))
    · have hNext := hSpace.heap (t+1) (Nat.succ_le_of_lt ht)
      change S.heap (t+1) < 2^w at hNext
      have hNot : B.jobs.count ≠ 0 := fun hh => (Bool.eq_false_iff.mp hne)
        (List.isEmpty_iff.mpr (S.indices_empty hh))
      have hEnd : S.heap (t+1) = B.record A + 2 + B.jobs.count := by
        simp only [BuildGameSchedule.heap, show (S.round t).jobs.count ≠ 0 from hNot, ite_false]
        rfl
      rw [hEnd] at hNext
      have hRecord : B.record A = D.cursor
          (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n) Ms.length := by
        change B.indices.isEmpty = false at hne
        change B.result.1 = .matched Ms emb at he
        simp only [BuildRoundData.record,hne,Bool.false_eq_true,ite_false,he]
        rfl
      rw [hRecord] at hNext
      change D.cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n)
        Ms.length < 2 ^ w
      omega

end MinCostFlow.HierPaths
