module

public import MinCostFlow.MinRatio.ShiftForestQueue

/-!
# Preparing the forest potential traversal

The traversal for Definition 5.6 (page 18) considers active names in
increasing order so the first vertex of each component is its canonical
root. The sorted names and empty traversal arrays occupy separate ranges.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- Prepare the compact candidate array and initialize the traversal state. -/
@[expose] def setupForestTraversal (copy sort : ℕ) : Stmt :=
  prepareOrderedForestNames copy sort ;; (reserveForestTraversal ;; .assign 44 (.const 0))

/-- Sorting and initializing the traversal yields an empty worklist and
potential invariant without charging for gaps in the vertex names. -/
theorem setupForestTraversal_runs {w copy sort a vc ec heap h limbs precision : ℕ}
    {F : MGraph} {p : Program} {st : State} {ω : ℕ → Bool} (g : ℕ → ℝ)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hgraph : DynGraphAt st.mem a vc ec F) (ha : st.regs 45 = a) (hc : st.regs 21 = vc)
    (hh : st.regs 4 = heap) (hl : st.regs 3 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + F.n ≤ heap)
    (hsortRoom : heap + F.n + 2 < 2 ^ w) (hcount : 2 * F.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : F.IsForest)
    (hroom : heap + F.n + vc * limbs + limbs + vc + vc < 2 ^ w) :
    ∃ out names cost, Runs w p ω (setupForestTraversal copy sort) st .normal out cost ∧
      names.Nodup ∧ names.Pairwise (· ≤ ·) ∧ names.toFinset = F.V ∧
      out.regs 44 = 0 ∧ out.regs 46 = names.length ∧ out.regs 48 = heap ∧
      ListAt out.mem heap names ∧
      out.regs 20 = heap + F.n ∧ out.regs 22 = heap + F.n + vc * limbs ∧
      out.regs 36 = heap + F.n + vc * limbs + limbs ∧
      out.regs 39 = heap + F.n + vc * limbs + limbs + vc ∧
      out.regs 40 = 0 ∧ out.regs 41 = 0 ∧
      out.regs 4 = heap + F.n + vc * limbs + limbs + vc + vc ∧
      ForestVisitedAt out.mem (out.regs 36) vc ∅ ∧
      ForestPotentialsAt out.mem (heap + F.n) h limbs precision F g ∅ ∧
      PathIntAt out.mem (out.regs 22) h limbs 0 ∧ ZeroFrom out.mem (heap + F.n) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 46 → r ≠ 47 → r ≠ 48 → r ≠ 49 → r ≠ 44 → r ≠ 20 →
        r ≠ 22 → r ≠ 36 → r ≠ 39 → r ≠ 40 → r ≠ 41 → r ≠ 4 →
        out.regs r = st.regs r) ∧
      cost ≤ 280 * (F.n * (2 * Nat.log 2 (F.n + 2) + 1) + 1) + 17 * F.n + 79 := by
  obtain ⟨mid, names, c, hprep, hnd, hordered, hnames, _, hlist, hbase, hn, hheap,
      hzero, hmem, hregs, hcost⟩ :=
    prepareOrderedForestNames_runs (ω := ω) hcopy hsort hgraph ha hc hh hz
      hgraphEnd hsortRoom hcount hlistEnd hw
  obtain ⟨out, hinit, hi, hlen, hsorted, hoList, hp, hzptr, hf, hq, hr, hwrite,
      hfinal, hflags, hpots, hzval, htail, hkeep, hm⟩ :=
    reserveForestTraversal_initial_scan_runs (p := p) (ω := ω) g hheap
      ((hregs 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
      ((hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl)
      hbase hn hlist hzero hforest hroom
  exact ⟨out, names, c + 40, runs_seq_iff.mpr (Or.inr ⟨mid, c, 39, hprep, hinit, by omega⟩),
    hnd, hordered, hnames, hi, hlen, hsorted, hoList, hp, hzptr, hf, hq, hr, hwrite, hfinal,
    hflags, hpots, hzval, htail, fun a h => (congrFun hm a).trans (hmem a h),
    fun r h46 h47 h48 h49 h44 h20 h22 h36 h39 h40 h41 h4 =>
      (hkeep r h44 h20 h22 h36 h39 h40 h41 h4).trans (hregs r h46 h47 h48 h49 h4),
    by omega⟩

/-- At a root-scan boundary the queue is exhausted, its entries are the
visited vertices, and every earlier candidate belongs to one of the
completed components. Unvisited potential slots are still zero. -/
@[expose] def ForestRootScanAt (st : State) (F : MGraph) (g : ℕ → ℝ)
    (sortedBase potential flags queue vc h limbs precision i : ℕ) (names : List ℕ) : Prop :=
  st.regs 44 = i ∧ st.regs 46 = names.length ∧ st.regs 48 = sortedBase ∧
  ListAt st.mem sortedBase names ∧ st.regs 20 = potential ∧
  st.regs 36 = flags ∧ st.regs 39 = queue ∧
  ∃ seen : List ℕ, seen.Nodup ∧ seen.toFinset ⊆ F.V ∧
    st.regs 40 = seen.length ∧ st.regs 41 = seen.length ∧
    ListAt st.mem queue seen ∧ ForestVisitedAt st.mem flags vc seen.toFinset ∧
    ForestPotentialsAt st.mem potential h limbs precision F g seen.toFinset ∧
    (∀ j (hj : j < names.length), j < i → names[j] ∈ seen.toFinset) ∧
    (∀ u ∈ seen.toFinset, ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) → v ∈ seen.toFinset) ∧
    ∀ v ∈ F.V, v ∉ seen.toFinset → ∀ j < limbs, st.mem (potential + v * limbs + j) = 0

/-- The empty arrays and zero cursor produced by setup establish the
ordered scan invariant before any candidate is processed. -/
theorem ForestRootScanAt.initial {st : State} {F : MGraph} {g : ℕ → ℝ} {names : List ℕ}
    {sortedBase potential flags queue vc h limbs precision : ℕ}
    (hi : st.regs 44 = 0) (hn : st.regs 46 = names.length) (hs : st.regs 48 = sortedBase)
    (hlist : ListAt st.mem sortedBase names) (hp : st.regs 20 = potential)
    (hf : st.regs 36 = flags) (hq : st.regs 39 = queue)
    (hr : st.regs 40 = 0) (hw : st.regs 41 = 0)
    (hflags : ForestVisitedAt st.mem flags vc ∅)
    (hpots : ForestPotentialsAt st.mem potential h limbs precision F g ∅)
    (hzero : ZeroFrom st.mem potential) :
    ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision 0 names := by
  refine ⟨hi, hn, hs, hlist, hp, hf, hq, [], List.nodup_nil, by simp, hr, hw,
    by intro j hj; simp at hj, by simpa using hflags, by simpa using hpots, ?_, ?_, ?_⟩
  · intro j _ hj
    exact (Nat.not_lt_zero j hj).elim
  · simp
  · intro v _ _ j _
    exact hzero _ (by omega)

/-- An already visited candidate extends the processed prefix without
changing the queue, flags, or potentials. -/
theorem ForestRootScanAt.skip {st out : State} {F : MGraph} {g : ℕ → ℝ} {names : List ℕ}
    {sortedBase potential flags queue vc h limbs precision i : ℕ}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hvisited : st.mem (flags + names[i]) = 1) (hcap : names[i] < vc)
    (hindex : out.regs 44 = i + 1) (hmem : out.mem = st.mem)
    (hregs : ∀ r, r ≠ 26 → r ≠ 37 → r ≠ 44 → out.regs r = st.regs r) :
    ForestRootScanAt out F g sortedBase potential flags queue vc h limbs precision (i + 1) names := by
  obtain ⟨_, hn, hs, hl, hp, hf, hq, seen, hd, hv, hr, hw, hlist, hflags, hpots,
    hprefix, hclosed, hz⟩ := hin
  have hseen : names[i] ∈ seen.toFinset := by
    by_contra hm
    rw [hflags _ hcap, ite_eq_right hm] at hvisited
    contradiction
  have keep (r : ℕ) (h26 : r ≠ 26) (h37 : r ≠ 37) (h44 : r ≠ 44) (n : ℕ)
      (he : st.regs r = n) : out.regs r = n := (hregs r h26 h37 h44).trans he
  refine ⟨hindex, keep 46 (by decide) (by decide) (by decide) _ hn,
    keep 48 (by decide) (by decide) (by decide) _ hs, hmem.symm ▸ hl,
    keep 20 (by decide) (by decide) (by decide) _ hp,
    keep 36 (by decide) (by decide) (by decide) _ hf,
    keep 39 (by decide) (by decide) (by decide) _ hq, seen, hd, hv,
    keep 40 (by decide) (by decide) (by decide) _ hr,
    keep 41 (by decide) (by decide) (by decide) _ hw, hmem.symm ▸ hlist,
    hmem.symm ▸ hflags, hmem.symm ▸ hpots, ?_, hclosed, hmem.symm ▸ hz⟩
  intro j hj hji
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt | rfl
  · exact hprefix j hj hlt
  · exact hseen

/-- A visited mark makes the concrete ordered scan skip component startup.
The step advances the prefix in twenty machine steps. -/
theorem ForestRootScanAt.skip_runs
    {w entry sortedBase potential flags queue vc h limbs precision i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {names : List ℕ} {st : State}
    {p : Program} {ω : ℕ → Bool}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hvisited : st.mem (flags + names[i]) = 1) (hcap : names[i] < vc)
    (hsRoom : sortedBase + names.length < 2 ^ w) (hfRoom : flags + vc ≤ 2 ^ w) :
    ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) st .normal out cost ∧
      ForestRootScanAt out F g sortedBase potential flags queue vc h limbs precision (i + 1) names ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 26 → r ≠ 37 → r ≠ 44 → out.regs r = st.regs r) ∧
      cost ≤ 20 := by
  have hinitial := hin
  obtain ⟨hidx, _, hs, hlist, _, hf, _, seen, _, _, _, _, _, hflags, _⟩ := hin
  have hseen : names[i] ∈ seen.toFinset := by
    by_contra hn
    rw [hflags _ hcap, ite_eq_right hn] at hvisited
    contradiction
  let Post (s : State) := s.mem = st.mem ∧
    ∀ r, r ≠ 26 → r ≠ 37 → s.regs r = st.regs r
  obtain ⟨out, cost, hrun, houtIdx, ⟨mid, ⟨hm, hr⟩, hmem, hregs⟩, hcost⟩ :=
    propagateOrderedForestVertex_runs (p := p) (ω := ω) (entry := entry)
      hlist hi hs hidx hsRoom Post (budget := 9) (by
        intro pre hname hpRegs hpMem
        obtain ⟨skip, hm, _, hr, _, hskip, _⟩ :=
          visitFreshForestChild_runs (w := w) (p := p) (ω := ω)
            (action := propagateForestComponent entry) (hpMem.symm ▸ hflags)
            ((hpRegs 36 (by decide)).trans hf) hname hcap hfRoom
        exact ⟨skip, 9, hskip hseen, (hr 44 (by decide)).trans ((hpRegs 44 (by decide)).trans hidx),
          ⟨hm.trans hpMem, fun r h26 h37 => (hr r h37).trans (hpRegs r h26)⟩, le_rfl⟩)
  have hkeep (r : ℕ) (h26 : r ≠ 26) (h37 : r ≠ 37) (h44 : r ≠ 44) :
      out.regs r = st.regs r := (hregs r h44).trans (hr r h26 h37)
  exact ⟨out, cost, hrun, hinitial.skip hi hvisited hcap houtIdx (hmem.trans hm) hkeep,
    hmem.trans hm, hkeep, hcost⟩

/-- A zero visited mark in the ordered scan identifies a canonical root
with an untouched potential slot. The existing queue has room for it. -/
theorem ForestRootScanAt.fresh_root
    {st : State} {F : MGraph} {g : ℕ → ℝ} {names : List ℕ}
    {sortedBase potential flags queue vc h limbs precision i : ℕ}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hvalid : F.IsValid) (hnames : names.toFinset = F.V)
    (horder : names.Pairwise (· ≤ ·)) (hcap : ∀ v ∈ F.V, v < vc)
    (hfresh : st.mem (flags + names[i]) = 0) :
    Chain.compRoot F names[i] = names[i] ∧
      (∀ j < limbs, st.mem (potential + names[i] * limbs + j) = 0) ∧
      st.regs 41 < vc := by
  obtain ⟨_, _, _, _, _, _, _, seen, hnd, hsub, _, hw, _, hflags, _, hprefix, hclosed, hz⟩ := hin
  have hactive : names[i] ∈ F.V := hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
  have hnot : names[i] ∉ seen.toFinset := by
    intro hm
    rw [hflags _ (hcap _ hactive), ite_eq_left hm] at hfresh
    contradiction
  refine ⟨forestRoot_of_ordered_prefix hi hvalid hnames horder hnot hprefix hclosed,
    hz _ hactive hnot, ?_⟩
  have hs : seen.toFinset ⊂ Finset.range vc := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun v hv => Finset.mem_range.mpr (hcap v (hsub hv)), ?_⟩
    intro he
    exact hnot (he ▸ Finset.mem_range.mpr (hcap _ hactive))
  have hcard := Finset.card_lt_card hs
  simpa only [hw, List.toFinset_card_of_nodup hnd, Finset.card_range] using hcard

/-- Seed the fresh ordered candidate and preserve the already-scanned
prefix of the queue. Its new entry carries the canonical root potential. -/
theorem ForestRootScanAt.seed_runs
    {w sortedBase potential flags queue vc h limbs precision i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {names : List ℕ} {st : State} {p : Program} {ω : ℕ → Bool}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hforest : F.IsForest) (hnames : names.toFinset = F.V)
    (horder : names.Pairwise (· ≤ ·)) (hcap : ∀ v ∈ F.V, v < vc)
    (hfresh : st.mem (flags + names[i]) = 0) (hr : st.regs 26 = names[i])
    (hqRoom : queue + vc < 2 ^ w)
    (hsortedEnd : sortedBase + names.length ≤ potential)
    (hpotEnd : potential + vc * limbs ≤ flags) (hflagsEnd : flags + vc ≤ queue) :
    ∃ out old, Runs w p ω enqueueForestRoot st .normal out 16 ∧
      old.Nodup ∧ old.toFinset ⊆ F.V ∧ names[i] ∉ old.toFinset ∧
      out.regs 40 = old.length ∧ out.regs 41 = (old ++ [names[i]]).length ∧
      ListAt out.mem queue (old ++ [names[i]]) ∧
      ForestVisitedAt out.mem flags vc (old ++ [names[i]]).toFinset ∧
      ForestPotentialsAt out.mem potential h limbs precision F g (old ++ [names[i]]).toFinset ∧
      ListAt out.mem sortedBase names ∧
      (∀ u ∈ old.toFinset, ∀ v, (∃ e ∈ F.E,
        (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) →
        v ∈ (old ++ [names[i]]).toFinset) ∧
      (∀ v ∈ F.V, v ∉ (old ++ [names[i]]).toFinset →
        ∀ j < limbs, out.mem (potential + v * limbs + j) = 0) ∧
      (∀ a, a ≠ flags + names[i] → a ≠ queue + old.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = st.regs r) := by
  obtain ⟨hroot, hzero, hspace⟩ := hin.fresh_root hi hforest.1 hnames horder hcap hfresh
  obtain ⟨_, _, _, hsorted, _, hf, hq, old, hnd, hsub, hread, hwrite, hlist, hflags, hpots, _, hclosed, hz⟩ := hin
  have hactive : names[i] ∈ F.V := hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
  have hrootCap := hcap _ hactive
  have hnot : names[i] ∉ old.toFinset := by
    intro hm
    rw [hflags _ hrootCap, ite_eq_left hm] at hfresh
    contradiction
  have hframe : ∀ v ∈ (old ++ [names[i]]).toFinset, ∀ j < limbs,
      potential + v * limbs + j ≠ flags + names[i] ∧
      potential + v * limbs + j ≠ queue + old.length := by
    intro v hv j hj
    have hvActive : v ∈ F.V := by
      simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hsub (List.mem_toFinset.mpr hv)
      · exact hactive
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hcap _ hvActive))
    simp only [Nat.succ_mul] at hmul
    exact ⟨by omega, by omega⟩
  obtain ⟨out, hrun, hlen, hout, hoFlags, hoPots, hoMem, hoRegs, _⟩ :=
    enqueueForestRoot_potentials_runs (w := w) (p := p) (ω := ω) hflags hlist hf hq hwrite hr
      hrootCap (hwrite ▸ hspace) (by omega) hqRoom (Or.inl hflagsEnd)
      hforest hroot hzero hpots hframe
  refine ⟨out, old, hrun, hnd, hsub, hnot, (hoRegs 40 (by decide)).trans hread,
    hlen, hout, hoFlags, hoPots, ?_, ?_, ?_, hoMem, hoRegs⟩
  · intro j hj
    rw [hoMem _ (by omega) (by omega)]
    exact hsorted j hj
  · intro u hu v hv
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (hclosed u hu v hv)))
  · intro v hv hfresh j hj
    have hvOld : v ∉ old.toFinset := fun hm =>
      hfresh (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hm)))
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hcap _ hv))
    simp only [Nat.succ_mul] at hmul
    rw [hoMem _ (by omega) (by omega)]
    exact hz v hv hvOld j hj

/-- After scanning every queued parent, its scanned-prefix closure is
closure of the whole visited set. The root scan can then advance. -/
theorem ForestRootScanAt.of_exhausted_component
    {st out : State} {F : MGraph} {g : ℕ → ℝ} {names seen : List ℕ}
    {sortedBase potential flags queue vc h limbs precision i : ℕ}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hroot : names[i] ∈ seen.toFinset)
    (hkeep : ∀ v < vc, st.mem (flags + v) = 1 → v ∈ seen.toFinset)
    (hcap : ∀ v ∈ F.V, v < vc)
    (hindex : out.regs 44 = i + 1) (hn : out.regs 46 = names.length)
    (hs : out.regs 48 = sortedBase) (hordered : ListAt out.mem sortedBase names)
    (hp : out.regs 20 = potential) (hf : out.regs 36 = flags) (hq : out.regs 39 = queue)
    (hnd : seen.Nodup) (hsub : seen.toFinset ⊆ F.V)
    (hread : out.regs 40 = seen.length) (hwrite : out.regs 41 = seen.length)
    (hlist : ListAt out.mem queue seen) (hflags : ForestVisitedAt out.mem flags vc seen.toFinset)
    (hpots : ForestPotentialsAt out.mem potential h limbs precision F g seen.toFinset)
    (hscanned : ∀ u ∈ seen.take (out.regs 40), ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) → v ∈ seen.toFinset)
    (hzero : ∀ v ∈ F.V, v ∉ seen.toFinset → ∀ j < limbs, out.mem (potential + v * limbs + j) = 0) :
    ForestRootScanAt out F g sortedBase potential flags queue vc h limbs precision (i + 1) names := by
  obtain ⟨_, _, _, _, _, _, _, old, _, hold, _, _, _, holdFlags, _, holdPrefix, _, _⟩ := hin
  refine ⟨hindex, hn, hs, hordered, hp, hf, hq, seen, hnd, hsub, hread, hwrite, hlist,
    hflags, hpots, ?_, ?_, hzero⟩
  · intro j hj hji
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt | rfl
    · have hjOld := holdPrefix j hj hlt
      have hjCap := hcap _ (hold hjOld)
      exact hkeep _ hjCap (by rw [holdFlags _ hjCap, ite_eq_left hjOld])
    · exact hroot
  · intro u hu v hv
    apply hscanned u _ v hv
    rw [hread, List.take_length]
    exact List.mem_toFinset.mp hu

/-- Every neighbor of a processed queue entry has already been discovered. -/
@[expose] def ForestQueueScanned (F : MGraph) (seen : List ℕ) (read : ℕ) : Prop :=
  ∀ u ∈ seen.take read, ∀ v, (∃ e ∈ F.E,
    (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) → v ∈ seen.toFinset

/-- Appending discoveries leaves the processed segment of the queue unchanged. -/
theorem ForestQueueScanned.append {F : MGraph} {seen fresh : List ℕ} {read : ℕ}
    (hs : ForestQueueScanned F seen read) (hr : read ≤ seen.length) :
    ForestQueueScanned F (seen ++ fresh) read := by
  intro u hu v hv
  rw [List.take_append_of_le_length hr] at hu
  exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (hs u hu v hv)))

/-- Scanning all incidences of the next parent adds that parent to the
processed prefix. A successor appended during the scan is already in `seen`. -/
theorem ForestQueueScanned.advance {F : MGraph} {seen : List ℕ} {read : ℕ}
    (hs : ForestQueueScanned F seen read) (hr : read < seen.length)
    (hneighbors : ∀ v, (∃ e ∈ F.E,
      (F.tail e = seen[read] ∧ F.head e = v) ∨
        (F.head e = seen[read] ∧ F.tail e = v)) → v ∈ seen.toFinset) :
    ForestQueueScanned F seen (read + 1) := by
  intro u hu v hv
  rw [List.take_succ_eq_append_getElem hr, List.mem_append, List.mem_singleton] at hu
  rcases hu with hu | rfl
  · exact hs u hu v hv
  · exact hneighbors v hv

/-- The completed incidence scan extends the processed queue prefix by
one parent, even when it appended new children to the worklist. -/
theorem ForestQueueScanned.advance_of_incidence
    {F : MGraph} {seen fresh incidents : List ℕ} {read ec : ℕ}
    (hs : ForestQueueScanned F seen read) (hr : read < seen.length)
    (hcap : ∀ e ∈ F.E, e < ec)
    (hmembers : ∀ j, j ∈ incidents ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = seen[read])
    (hcovered : (incidents.map (forestIncidenceChild F)).toFinset ⊆
      (seen ++ fresh).toFinset) :
    ForestQueueScanned F (seen ++ fresh) (read + 1) := by
  have hlt : read < (seen ++ fresh).length := by
    simp only [List.length_append]
    omega
  apply (hs.append hr.le).advance hlt
  intro v hv
  rw [List.getElem_append_left hr] at hv
  exact hcovered ((mem_forestIncidenceChildren_iff hcap hmembers).mpr hv)

/-- A newly discovered active vertex has room in the queue. Appending it
preserves distinctness and keeps all queued names in the forest. -/
theorem forestQueue_append_fresh {F : MGraph} {seen : List ℕ} {child vc : ℕ}
    (hnd : seen.Nodup) (hsub : seen.toFinset ⊆ F.V)
    (hc : child ∈ F.V) (hfresh : child ∉ seen.toFinset)
    (hcap : ∀ v ∈ F.V, v < vc) :
    seen.length < vc ∧ (seen ++ [child]).Nodup ∧ (seen ++ [child]).toFinset ⊆ F.V := by
  have hstrict : seen.toFinset ⊂ Finset.range vc := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨fun v hv => Finset.mem_range.mpr (hcap v (hsub hv)), ?_⟩
    intro heq
    exact hfresh (heq ▸ Finset.mem_range.mpr (hcap child hc))
  have hroom := Finset.card_lt_card hstrict
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hroom
  refine ⟨hroom, List.nodup_append.mpr ⟨hnd, List.nodup_singleton child, ?_⟩, ?_⟩
  · intro x hx y hy heq
    rw [List.mem_singleton.mp hy] at heq
    exact hfresh (List.mem_toFinset.mpr (heq ▸ hx))
  · intro v hv
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hsub (List.mem_toFinset.mpr hv)
    · exact hc

/-- While a component is being scanned, the queue contains precisely the
discovered vertices, including parents whose incidences are still pending. -/
@[expose] def ForestWorklistAt (st : State) (F : MGraph) (g : ℕ → ℝ)
    (potential flags queue vc h limbs precision read : ℕ) (seen : List ℕ) : Prop :=
  st.regs 20 = potential ∧ st.regs 36 = flags ∧ st.regs 39 = queue ∧
  st.regs 40 = read ∧ st.regs 41 = seen.length ∧ read ≤ seen.length ∧
  seen.Nodup ∧ seen.toFinset ⊆ F.V ∧ ListAt st.mem queue seen ∧
  ForestVisitedAt st.mem flags vc seen.toFinset ∧
  ForestPotentialsAt st.mem potential h limbs precision F g seen.toFinset ∧
  ForestQueueScanned F seen read ∧
  ∀ v ∈ F.V, v ∉ seen.toFinset → ∀ j < limbs, st.mem (potential + v * limbs + j) = 0

/-- The read and write indices of a represented worklist fit within the
vertex capacity because its entries are distinct active names. -/
theorem ForestWorklistAt.indices {st : State} {F : MGraph} {g : ℕ → ℝ}
    {potential flags queue vc h limbs precision read : ℕ} {seen : List ℕ}
    (hin : ForestWorklistAt st F g potential flags queue vc h limbs precision read seen)
    (hcap : ∀ v ∈ F.V, v < vc) :
    st.regs 40 = read ∧ read ≤ st.regs 41 ∧ st.regs 41 ≤ vc := by
  obtain ⟨_, _, _, hr, hw, hle, hnd, hsub, _⟩ := hin
  refine ⟨hr, hw.symm ▸ hle, ?_⟩
  have hcard := Finset.card_le_card
    (show seen.toFinset ⊆ Finset.range vc from fun v hv => Finset.mem_range.mpr (hcap v (hsub hv)))
  simpa only [hw, List.toFinset_card_of_nodup hnd, Finset.card_range] using hcard

/-- A fresh root enters the worklist immediately after its processed prefix. -/
theorem ForestRootScanAt.seed_worklist_runs
    {w sortedBase potential flags queue vc h limbs precision i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {names : List ℕ} {st : State} {p : Program} {ω : ℕ → Bool}
    (hin : ForestRootScanAt st F g sortedBase potential flags queue vc h limbs precision i names)
    (hi : i < names.length) (hforest : F.IsForest) (hnames : names.toFinset = F.V)
    (horder : names.Pairwise (· ≤ ·)) (hcap : ∀ v ∈ F.V, v < vc)
    (hfresh : st.mem (flags + names[i]) = 0) (hr : st.regs 26 = names[i])
    (hqRoom : queue + vc < 2 ^ w)
    (hsortedEnd : sortedBase + names.length ≤ potential)
    (hpotEnd : potential + vc * limbs ≤ flags) (hflagsEnd : flags + vc ≤ queue) :
    ∃ out old, Runs w p ω enqueueForestRoot st .normal out 16 ∧
      st.regs 40 = old.length ∧
      ForestWorklistAt out F g potential flags queue vc h limbs precision old.length
        (old ++ [names[i]]) ∧ ListAt out.mem sortedBase names ∧
      (∀ a, a ≠ flags + names[i] → a ≠ queue + old.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = st.regs r) := by
  obtain ⟨out, old, hrun, hnd, hsub, hfresh', hread, hwrite, hlist, hflags, hpots, hsorted,
    hclosed, hzero, hmem, hregs⟩ :=
    hin.seed_runs (p := p) (ω := ω) hi hforest hnames horder hcap hfresh hr hqRoom
      hsortedEnd hpotEnd hflagsEnd
  have hv : names[i] ∈ F.V := hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
  obtain ⟨_, hnodup, hvertices⟩ := forestQueue_append_fresh hnd hsub hv hfresh' hcap
  have hscanned : ForestQueueScanned F (old ++ [names[i]]) old.length := by
    intro u hu v hv
    rw [List.take_append_of_le_length le_rfl, List.take_length] at hu
    exact hclosed u (List.mem_toFinset.mpr hu) v hv
  obtain ⟨_, _, _, _, hp, hf, hq, _⟩ := hin
  exact ⟨out, old, hrun, (hregs 40 (by decide)).symm.trans hread,
    ⟨(hregs 20 (by decide)).trans hp, (hregs 36 (by decide)).trans hf,
      (hregs 39 (by decide)).trans hq, hread, hwrite, by simp, hnodup, hvertices,
      hlist, hflags, hpots, hscanned, hzero⟩, hsorted, hmem, hregs⟩

/-- A fresh child can be appended while the current parent is being scanned.
The queue's read index stays fixed until all incidences of that parent are processed. -/
theorem ForestWorklistAt.append_child
    {st out : State} {F : MGraph} {g : ℕ → ℝ} {seen : List ℕ}
    {potential flags queue vc h limbs precision read child heap : ℕ}
    (hin : ForestWorklistAt st F g potential flags queue vc h limbs precision read seen)
    (hc : child ∈ F.V) (hfresh : child ∉ seen.toFinset)
    (hcap : ∀ v ∈ F.V, v < vc)
    (hpotEnd : potential + vc * limbs ≤ flags) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ heap)
    (hwrite : out.regs 41 = (seen ++ [child]).length)
    (hlist : ListAt out.mem queue (seen ++ [child]))
    (hflags : ForestVisitedAt out.mem flags vc (seen ++ [child]).toFinset)
    (hpots : ForestPotentialsAt out.mem potential h limbs precision F g (seen ++ [child]).toFinset)
    (hframe : ∀ a < heap, a ≠ queue + seen.length → a ≠ flags + child →
      a < potential + child * limbs ∨ potential + child * limbs + limbs ≤ a →
      out.mem a = st.mem a)
    (hregs : ∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → r ≠ 41 → out.regs r = st.regs r) :
    ForestWorklistAt out F g potential flags queue vc h limbs precision read (seen ++ [child]) := by
  obtain ⟨hp, hf, hq, hr, _, hle, hnd, hsub, _, _, _, hscanned, hzero⟩ := hin
  obtain ⟨_, hnodup, hvertices⟩ := forestQueue_append_fresh hnd hsub hc hfresh hcap
  refine ⟨(hregs 20 (by decide) (by decide) (by decide)).trans hp,
    (hregs 36 (by decide) (by decide) (by decide)).trans hf,
    (hregs 39 (by decide) (by decide) (by decide)).trans hq,
    (hregs 40 (by decide) (by decide) (by decide)).trans hr, hwrite,
    by simp only [List.length_append, List.length_singleton]; omega,
    hnodup, hvertices, hlist, hflags, hpots, hscanned.append hle, ?_⟩
  intro v hv hnew j hj
  have hold : v ∉ seen.toFinset := fun hm =>
    hnew (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hm)))
  have hne : v ≠ child := fun he => hnew (by simp [he, List.toFinset_append])
  have hlt := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hcap v hv))
  simp only [Nat.succ_mul] at hlt
  have hsep : potential + v * limbs + j < potential + child * limbs ∨
      potential + child * limbs + limbs ≤ potential + v * limbs + j := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt h)
      simp only [Nat.succ_mul] at hmul
      exact Or.inl (by omega)
    · have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt h)
      simp only [Nat.succ_mul] at hmul
      exact Or.inr (by omega)
  rw [hframe _ (by omega) (by omega) (by omega) hsep]
  exact hzero v hv hold j hj

/-- The supplied machine operands and the live tables suffice to run the
fresh-child action while preserving the worklist invariant. -/
theorem ForestWorklistAt.child_runs
    {w h limbs precision base gradients zeroPtr heap entry flags capacity queue : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {read : ℕ}
    (hin : ForestWorklistAt st F g base flags queue capacity h limbs precision read names)
    (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge])
    (hpVisited : parent ∈ names.toFinset) (hcFresh : child ∉ names.toFinset)
    (hcActive : child ∈ F.V) (hcap : ∀ v ∈ F.V, v < capacity)
    (hpotEnd : base + capacity * limbs ≤ flags)
    {edges : Finset ℕ} (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g)
    (he : edge.1 ∈ edges) (hgradientReg : st.regs 38 = gradients) (heReg : st.regs 32 = edge.1)
    (himpl : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (heRoom : gradients + edge.1 * limbs + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue))))
    (hqEnd : queue + capacity ≤ heap)
    (hflagsEnd : flags + capacity ≤ queue) :
    ∃ out cost, Runs w p ω (propagateAndEnqueueForestChild entry) st .normal out cost ∧
      out.regs 4 = heap + 3 * limbs ∧ ZeroFrom out.mem (out.regs 4) ∧
      ForestWorklistAt out F g base flags queue capacity h limbs precision read (names ++ [child]) ∧
      (∀ a < heap, a ≠ queue + names.length → a ≠ flags + child →
        a < base + child * limbs ∨ base + child * limbs + limbs ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → r ≠ 41 → out.regs r = st.regs r) ∧ cost ≤ 129 * limbs + 163 := by
  have hinitial := hin
  obtain ⟨hb, hf, hq, _, hi, _, hnd, hsub, hlist, hflags, hpots, _, _⟩ := hin
  obtain ⟨hspace, _, _⟩ := forestQueue_append_fresh hnd hsub hcActive hcFresh hcap
  have hslot (v : ℕ) (hv : v ∈ insert child names.toFinset) :
      base + v * limbs + limbs ≤ flags := by
    have hv' : v ∈ F.V := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hcActive
      · exact hsub hv
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hcap v hv'))
    simp only [Nat.succ_mul] at hmul
    omega
  obtain ⟨out, cost, hrun, hh, hzout, hw', hl', hp', hf', hm, hregs, hcost⟩ :=
    propagateAndEnqueueForestChild_of_tables_runs (ω := ω) hb hp hc hforest hpath g hpots
      hpVisited hcFresh hflags hf (hcap _ hcActive) (by omega) (fun v hv => Or.inl (hslot v hv))
      (fun v hv => by have := hslot v (Finset.mem_insert_of_mem hv); omega)
      hvalues he hgradientReg heReg himpl hr₃ hr₄ hr₂₂ hr₂₃ hz heRoom hzRoom
      (by have := hslot child (Finset.mem_insert_self ..); omega)
      hzero hroom hw hfit hlist hq hi hspace hqEnd (by omega) hflagsEnd
      (fun v hv => (hslot v hv).trans (by omega))
  exact ⟨out, cost, hrun, hh, hzout,
    hinitial.append_child hcActive hcFresh hcap hpotEnd hflagsEnd hqEnd hw' hl' hf' hp' hm hregs,
    hm, hregs, hcost⟩

/-- Decoding an incidence and reading its flag leave all live worklist
data intact before either branch runs. -/
theorem ForestWorklistAt.frame_incidence
    {st out : State} {F : MGraph} {g : ℕ → ℝ} {seen : List ℕ}
    {potential flags queue vc h limbs precision read : ℕ}
    (hin : ForestWorklistAt st F g potential flags queue vc h limbs precision read seen)
    (hm : out.mem = st.mem)
    (hr : ∀ r, r ≠ 37 → r ≠ 29 → r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 →
      out.regs r = st.regs r) :
    ForestWorklistAt out F g potential flags queue vc h limbs precision read seen := by
  obtain ⟨hp, hf, hq, hread, hwrite, hle, hnd, hsub, hl, hflags, hpots, hscan, hz⟩ := hin
  have keep (r : ℕ) (hlo : 38 ≤ r) : out.regs r = st.regs r :=
    hr r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨(hr 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp,
    (hr 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf,
    (keep 39 (by decide)).trans hq, (keep 40 (by decide)).trans hread,
    (keep 41 (by decide)).trans hwrite, hle, hnd, hsub, hm.symm ▸ hl,
    hm.symm ▸ hflags, hm.symm ▸ hpots, hscan, hm.symm ▸ hz⟩

/-- A live incidence either skips a queued child or appends a fresh one.
It advances the adjacency cursor while leaving the queue read index fixed. -/
theorem ForestWorklistAt.incidence_runs
    {w a vc ec parent i prev next head flags entry limbs : ℕ}
    {base gradients zeroPtr heap queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {L names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hlist : IsDoublyLinkedList st.mem prev next head (2 * ec) L)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (hnext : st.regs 27 = next) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hnextRoom : next + L[i] < 2 ^ w) (hgraphRoom : a + dynGraphSize vc ec ≤ 2 ^ w)
    (hp : st.regs 25 = parent) (hpVisited : parent ∈ names.toFinset)
    (hgrad : st.regs 38 = gradients) (hr₃ : st.regs 3 = limbs)
    (hheap : st.regs 4 = heap) (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem heap)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (heRoom : gradients + (L[i] / 2) * limbs + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ flags) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ heap)
    (hfit : let value := Num.intVal st.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal st.mem (base + parent * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    let child := forestIncidenceChild F L[i]
    let seen := if child ∈ names.toFinset then names else names ++ [child]
    ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision read seen ∧
      out.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      heap ≤ out.regs 4 ∧ out.regs 4 ≤ heap + 3 * limbs ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ x < heap, x ≠ queue + names.length → x ≠ flags + child →
        x < base + child * limbs ∨ base + child * limbs + limbs ≤ x → out.mem x = st.mem x) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 207 := by
  have hf := hin.2.1
  have hflags := hin.2.2.2.2.2.2.2.2.2.1
  obtain ⟨pre, hm, _, hchild, heReg, hd, hcur, hregs, hpath, hskip, hvisit⟩ :=
    scanForestIncidence_runs (p := p) (ω := ω) (action := propagateAndEnqueueForestChild entry)
      hgraph hforest hmembers hlist hnext hi hcursor ht hc hn hnextRoom hflags hf (by omega) hgraphRoom
  let child := forestIncidenceChild F L[i]
  have hpre := hin.frame_incidence hm hregs
  by_cases hs : child ∈ names.toFinset
  · have hh := (hregs 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hheap
    refine ⟨pre, 45, hskip hs, ?_, hcur, by rw [hh], by rw [hh]; omega, ?_,
      fun x _ _ _ _ => congrFun hm x, ?_, by omega⟩
    · simpa only [child, hs, ↓reduceIte] using hpre
    · rw [hh, hm]
      exact hzero
    · intro r _ h23 _ h26 h28 h29 h32 h37 _
      exact hregs r h37 h29 h26 h28 h23 h32
  · obtain ⟨_, he, hparent⟩ := (hmembers L[i]).mp (List.getElem_mem hi)
    have hv := (forestHalfEdge_childPath hforest he hparent).1
    obtain ⟨out, cost, hrun, hheapOut, hzout, hout, hframe, hkeep, hcost⟩ :=
      hpre.child_runs
        ((hregs 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
        hchild hforest hpath hpVisited hs hv hgraph.2.1 hpotEnd (hm.symm ▸ hvalues)
        (hsub he)
        ((hregs 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgrad)
        heReg (himpl _ _ _)
        ((hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr₃)
        ((hregs 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hheap)
        ((hregs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzPtr)
        hd (hm.symm ▸ hz) heRoom hzRoom (hm.symm ▸ hzero) hroom hw
        (by simpa [hm] using hfit) hqEnd hflagsEnd
    refine ⟨out, cost + 44, hvisit hs hrun,
      by rw [ite_eq_right hs]; exact hout,
      (hkeep 29 (by decide) (by decide) (by decide)).trans hcur, by omega, by omega, hzout, ?_, ?_, by omega⟩
    · intro x hx hq hf hs
      exact (hframe x hx hq hf hs).trans (congrFun hm x)
    · intro r hlo h23 h24 h26 h28 h29 h32 h37 h41
      exact (hkeep r hlo h24 h41).trans (hregs r h37 h29 h26 h28 h23 h32)

/-- An incidence writes only to its child slot, flag, and queue cell.
The graph and input gradients lie below those arrays, while the shared
zero block is between the potential table and flags. -/
theorem forestIncidence_frame_inputs
    {mem out : ℕ → ℕ} {F : MGraph} {edges : Finset ℕ} {g : ℕ → ℝ}
    {a vc ec gradients h limbs precision base zeroPtr flags queue tail child heap : ℕ}
    (hg : DynGraphAt mem a vc ec F)
    (hgrad : EdgeValuesAt mem gradients h limbs precision edges g)
    (hz : PathIntAt mem zeroPtr h limbs 0)
    (hgEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hchildEnd : base + child * limbs + limbs ≤ zeroPtr)
    (hzEnd : zeroPtr + limbs ≤ flags) (hfEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ heap)
    (hframe : ∀ x < heap, x ≠ queue + tail → x ≠ flags + child →
      x < base + child * limbs ∨ base + child * limbs + limbs ≤ x → out x = mem x) :
    DynGraphAt out a vc ec F ∧ EdgeValuesAt out gradients h limbs precision edges g ∧
      PathIntAt out zeroPtr h limbs 0 := by
  have hprefix (x : ℕ) (hx : x < base) : out x = mem x :=
    hframe x (by omega) (by omega) (by omega) (Or.inl (by omega))
  exact ⟨hg.of_agree (fun x _ hx => hprefix x (by omega)),
    hgrad.congr (fun e he j hj => hprefix _ (by have := hgradEnd e he; omega)),
    hz.congr (fun j hj => hframe _ (by omega) (by omega) (by omega) (Or.inr (by omega)))⟩

/-- A frame on the forest block preserves the same incidence list, so
the successor cursor still indexes that list after a child write. -/
theorem forestIncidenceList_of_graph_frame
    {mem out : ℕ → ℕ} {a vc ec slot : ℕ} {L : List ℕ}
    (hslot : slot < vc)
    (hlist : IsDoublyLinkedList mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L)
    (hframe : ∀ x, a ≤ x → x < a + dynGraphSize vc ec → out x = mem x) :
    IsDoublyLinkedList out (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L := by
  apply hlist.of_agree
  · apply hframe <;> simp only [dgIncHeadBase, dynGraphSize] <;> omega
  · intro j hj
    have hcap := hlist.2.1 j hj
    apply hframe <;> simp only [dgHePrevBase, dynGraphSize] <;> omega
  · intro j hj
    have hcap := hlist.2.1 j hj
    apply hframe <;> simp only [dgHeNextBase, dynGraphSize] <;> omega

/-- Process a live incidence and retain the immutable inputs at their
original addresses, so the successor can use the same adjacency list. -/
theorem ForestWorklistAt.incidence_with_inputs_runs
    {w a vc ec parent i slot flags entry limbs : ℕ}
    {base gradients zeroPtr heap queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {L names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hslot : slot < vc)
    (hlist : IsDoublyLinkedList st.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hp : st.regs 25 = parent) (hpVisited : parent ∈ names.toFinset)
    (hgrad : st.regs 38 = gradients) (hr₃ : st.regs 3 = limbs)
    (hheap : st.regs 4 = heap) (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem heap)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgraphEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hzEnd : zeroPtr + limbs ≤ flags) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ heap)
    (hfit : let value := Num.intVal st.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal st.mem (base + parent * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    let child := forestIncidenceChild F L[i]
    let seen := if child ∈ names.toFinset then names else names ++ [child]
    ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision read seen ∧
      out.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      heap ≤ out.regs 4 ∧ out.regs 4 ≤ heap + 3 * limbs ∧
      ZeroFrom out.mem (out.regs 4) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧
      IsDoublyLinkedList out.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
        (dgIncHeadBase a vc + slot) (2 * ec) L ∧
      (∀ x < heap, x ≠ queue + names.length → x ≠ flags + child →
        x < base + child * limbs ∨ base + child * limbs + limbs ≤ x → out.mem x = st.mem x) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 207 := by
  obtain ⟨hj, he, hparent⟩ := (hmembers L[i]).mp (List.getElem_mem hi)
  have hnextRoom : dgHeNextBase a vc ec + L[i] < 2 ^ w := by
    simp only [dgHeNextBase, dynGraphSize] at *
    omega
  obtain ⟨out, cost, hrun, hwork, hcur, hlo, hhi, htail, hframe, hregs, hcost⟩ :=
    hin.incidence_runs (ω := ω) hgraph hforest hmembers hlist hi hcursor hnext ht hc hn
      hnextRoom (by omega) hp hpVisited hgrad hr₃ hheap hzPtr hz hzero hvalues hsub himpl
      ((hgradEnd _ (hsub he)).trans (by omega)) (by omega) hroom hw (by omega) hflagsEnd hqEnd hfit
  have hv := (forestHalfEdge_childPath hforest he hparent).1
  have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hgraph.2.1 _ hv))
  simp only [Nat.succ_mul] at hmul
  have hchildEnd : base + forestIncidenceChild F L[i] * limbs + limbs ≤ zeroPtr := by
    change base + F.src (L[i] / 2, decide (L[i] % 2 ≠ 0)) * limbs + limbs ≤ zeroPtr
    omega
  obtain ⟨hg, hgradient, hzeroBlock⟩ :=
    forestIncidence_frame_inputs hgraph hvalues hz hgraphEnd hgradEnd hchildEnd hzEnd hflagsEnd hqEnd hframe
  have hadj := forestIncidenceList_of_graph_frame hslot hlist fun x _ hx =>
    hframe x (by omega) (by omega) (by omega) (Or.inl (by omega))
  exact ⟨out, cost, hrun, hwork, hcur, hlo, hhi, htail, hg, hgradient, hzeroBlock, hadj,
    hframe, hregs, hcost⟩

/-- At a live index the loop cursor names that entry. Advancing past the
last entry gives zero, and all other advances name the next half-edge. -/
theorem forestIncidenceCursor_step {L : List ℕ} {i : ℕ} (hi : i < L.length) :
    (if i < L.length then L.getD i 0 + 1 else 0) = L[i] + 1 ∧
    (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) =
      (if i + 1 < L.length then L.getD (i + 1) 0 + 1 else 0) := by
  constructor
  · simp [hi, List.getD]
  · by_cases hend : i + 1 = L.length
    · simp [hend]
    · have hnext : i + 1 < L.length := by omega
      simp [hend, hnext]

/-- Charging one scratch reservation per remaining incidence leaves room
for the next write and the rest of the loop. -/
theorem forestIncidenceHeap_step {w heap next limbs i count : ℕ}
    (hi : i < count) (hnext : next ≤ heap + 3 * limbs)
    (hroom : heap + 3 * limbs * (count - i) < 2 ^ w) :
    heap + 3 * limbs < 2 ^ w ∧ next + 3 * limbs * (count - (i + 1)) < 2 ^ w := by
  have heq : count - i = (count - (i + 1)) + 1 := by omega
  rw [heq, Nat.mul_add, Nat.mul_one] at hroom
  omega

/-- One incidence run advances the loop cursor and pays for any heap
growth from the allowance reserved for remaining incidences. -/
theorem ForestWorklistAt.incidence_loop_step
    {w a vc ec parent i slot flags entry limbs : ℕ}
    {base gradients zeroPtr heap queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {L names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hslot : slot < vc)
    (hlist : IsDoublyLinkedList st.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L)
    (hi : i < L.length) (hcursor : st.regs 29 = if i < L.length then L.getD i 0 + 1 else 0)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hp : st.regs 25 = parent) (hpVisited : parent ∈ names.toFinset)
    (hgrad : st.regs 38 = gradients) (hr₃ : st.regs 3 = limbs)
    (hheap : st.regs 4 = heap) (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem heap)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgraphEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hzEnd : zeroPtr + limbs ≤ flags) (hroom : heap + 3 * limbs * (L.length - i) < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ heap)
    (hfit : let value := Num.intVal st.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal st.mem (base + parent * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    let child := forestIncidenceChild F L[i]
    let seen := if child ∈ names.toFinset then names else names ++ [child]
    ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision read seen ∧
      out.regs 29 = (if i + 1 < L.length then L.getD (i + 1) 0 + 1 else 0) ∧
      heap ≤ out.regs 4 ∧ out.regs 4 ≤ heap + 3 * limbs ∧
      out.regs 4 + 3 * limbs * (L.length - (i + 1)) < 2 ^ w ∧
      ZeroFrom out.mem (out.regs 4) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧
      IsDoublyLinkedList out.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
        (dgIncHeadBase a vc + slot) (2 * ec) L ∧
      (∀ x < heap, x ≠ queue + names.length → x ≠ flags + child →
        x < base + child * limbs ∨ base + child * limbs + limbs ≤ x → out.mem x = st.mem x) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 207 := by
  obtain ⟨hcurrent, hnextCursor⟩ := forestIncidenceCursor_step hi
  have hroomNow := (forestIncidenceHeap_step hi (Nat.le_add_right heap _) hroom).1
  obtain ⟨out, cost, hrun, hwork, hcur, hlo, hhi, htail, hg, hgradient, hzeroBlock,
    hadj, hframe, hregs, hcost⟩ :=
    hin.incidence_with_inputs_runs (ω := ω) hgraph hforest hmembers hslot hlist hi
      (hcursor.trans hcurrent) hnext ht hc hn hp hpVisited hgrad hr₃ hheap hzPtr hz hzero
      hvalues hsub himpl hgraphEnd hgradEnd hzEnd hroomNow hw hpotEnd hflagsEnd hqEnd hfit
  exact ⟨out, cost, hrun, hwork, hcur.trans hnextCursor, hlo, hhi,
    (forestIncidenceHeap_step hi hhi hroom).2, htail, hg, hgradient, hzeroBlock,
    hadj, hframe, hregs, hcost⟩

/-- The concrete adjacency scan preserves its read-only inputs and discovers
all children in the scanned suffix. The arithmetic fit premise concerns
each signed addition at the actual parent slot. -/
theorem ForestWorklistAt.adjacency_runs
    {w a vc ec parent slot flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {L names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hslot : slot < vc)
    (hlist : IsDoublyLinkedList st.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L)
    (hcursor : st.regs 29 = if 0 < L.length then L.getD 0 0 + 1 else 0)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hp : st.regs 25 = parent) (hpVisited : parent ∈ names.toFinset)
    (hgrad : st.regs 38 = gradients) (hlimbs : st.regs 3 = limbs)
    (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem (st.regs 4))
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgraphEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hzEnd : zeroPtr + limbs ≤ flags)
    (hroom : st.regs 4 + 3 * limbs * L.length < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ s seen i (hi : i < L.length),
      ForestWorklistAt s F g base flags queue vc h limbs precision read seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    ∃ out cost fresh, Runs w p ω (propagateForestAdjacency entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision read (names ++ fresh) ∧
      (L.map (forestIncidenceChild F)).toFinset ⊆ (names ++ fresh).toFinset ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 3 * limbs * L.length ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ L.length * (129 * limbs + 209) + 2 := by
  let Inv (visited : Finset ℕ) (i : ℕ) (s : State) : Prop :=
    (∃ fresh, visited = (names ++ fresh).toFinset ∧
      ForestWorklistAt s F g base flags queue vc h limbs precision read (names ++ fresh)) ∧
    s.regs 29 = (if i < L.length then L.getD i 0 + 1 else 0) ∧
    DynGraphAt s.mem a vc ec F ∧ EdgeValuesAt s.mem gradients h limbs precision edges g ∧
    PathIntAt s.mem zeroPtr h limbs 0 ∧
    IsDoublyLinkedList s.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
      (dgIncHeadBase a vc + slot) (2 * ec) L ∧
    ZeroFrom s.mem (s.regs 4) ∧ queue + vc ≤ s.regs 4 ∧
    s.regs 4 + 3 * limbs * (L.length - i) < 2 ^ w ∧
    s.regs 27 = dgHeNextBase a vc ec ∧ s.regs 33 = dgETailSlotBase a vc ec ∧
    s.regs 34 = ec ∧ s.regs 35 = dgIntToExtBase a vc ∧ s.regs 25 = parent ∧
    s.regs 38 = gradients ∧ s.regs 3 = limbs ∧ s.regs 22 = zeroPtr ∧
    st.regs 4 ≤ s.regs 4 ∧ s.regs 4 ≤ st.regs 4 + 3 * limbs * i ∧
    (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
      r ≠ 32 → r ≠ 37 → r ≠ 41 → s.regs r = st.regs r) ∧ (∀ x < base, s.mem x = st.mem x)
  have hinit : Inv names.toFinset 0 st :=
    ⟨⟨[], by simp, by simpa using hin⟩, hcursor, hgraph, hvalues, hz, hlist, hzero,
      hqEnd, by simpa using hroom, hnext, ht, hc, hn, hp, hgrad, hlimbs, hzPtr, le_rfl, by simp, fun _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hstep (visited : Finset ℕ) (i : ℕ) (s : State) (hi : i < L.length)
      (hs : Inv visited i s) :
      ∃ out cost, Runs w p ω (propagateForestIncidence entry) s .normal out cost ∧
        Inv (insert (forestIncidenceChild F L[i]) visited) (i + 1) out ∧
        cost ≤ 129 * limbs + 207 := by
    obtain ⟨⟨fresh, rfl, hwork⟩, hcur, hg, hv, hz', hl, htail, hqe, hr,
      hnxt, htt, hcc, hnn, hpp, hgr, hli, hzp, hheapLo, hheapHi, hpreserve, hprefix⟩ := hs
    have hparent : parent ∈ (names ++ fresh).toFinset :=
      List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hpVisited))
    obtain ⟨out, cost, hrun, hwork', hcur', hlo, hhi, hr', htail', hg', hv', hz'', hl', hframe, hregs, hcost⟩ :=
      hwork.incidence_loop_step (ω := ω) hg hforest hmembers hslot hl hi hcur hnxt htt hcc hnn
        hpp hparent hgr hli rfl hzp hz' htail hv hsub himpl hgraphEnd hgradEnd hzEnd hr hw
        hpotEnd hflagsEnd hqe (hfit s _ i hi hwork hv)
    refine ⟨out, cost, hrun, ⟨?_, hcur', hg', hv', hz'', hl', htail', hqe.trans hlo, hr',
      (hregs 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnxt,
      (hregs 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans htt,
      (hregs 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcc,
      (hregs 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnn,
      (hregs 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpp,
      (hregs 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgr,
      (hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hli,
      (hregs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzp,
      hheapLo.trans hlo, ?_, ?_, ?_⟩, hcost⟩
    swap
    · rw [Nat.mul_succ]
      omega
    swap
    · intro r hr h23 h24 h26 h28 h29 h32 h37 h41
      exact (hregs r hr h23 h24 h26 h28 h29 h32 h37 h41).trans
        (hpreserve r hr h23 h24 h26 h28 h29 h32 h37 h41)
    swap
    · intro x hx
      exact (hframe x (by omega) (by omega) (by omega) (Or.inl (by omega))).trans (hprefix x hx)
    let child := forestIncidenceChild F L[i]
    by_cases hm : child ∈ (names ++ fresh).toFinset
    all_goals dsimp only [child] at hm
    · exact ⟨fresh, Finset.insert_eq_of_mem hm, by simpa only [ite_eq_left hm] using hwork'⟩
    · refine ⟨fresh ++ [child], ?_, ?_⟩
      · rw [← List.append_assoc]
        ext v
        simp [List.toFinset_append, Finset.mem_insert, child]
      · simpa only [ite_eq_right hm, List.append_assoc] using hwork'
  obtain ⟨out, cost, hrun, ⟨⟨fresh, hset, hwork⟩, _, hg, hv, hz, _, htail, _, _, _, _, _, _, _, _, _, _, hlo, hhi, hregs, hprefix⟩, hcost⟩ :=
    propagateForestAdjacency_visited_runs Inv (fun _ _ _ hs => hs.2.1) hstep hinit
  exact ⟨out, cost, fresh, hrun, hwork, hset ▸ Finset.subset_union_right, hg, hv, hz, htail, hlo, hhi, hregs, hprefix, hcost⟩

end MinCostFlow.MinRatio
