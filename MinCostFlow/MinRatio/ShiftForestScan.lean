module

public import MinCostFlow.MinRatio.ShiftForestParent
public import MinCostFlow.MinRatio.RebuildGuard

/-!
# The ordered forest scan

The outer loop considers each active name once. Component scans charge
their work against the volume and count of parents they actually visit.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- The ordered loop completes the potential traversal with a telescoping
incidence charge and a constant overhead per candidate. -/
theorem ForestRootScanAt.scan_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision sortedBase i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i ≤ names.length) (hnames : names.toFinset = F.V) (horder : names.Pairwise (· ≤ ·))
    (hsortedRoom : sortedBase + names.length < 2 ^ w)
    (hsortedEnd : sortedBase + names.length ≤ base)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hext : st.regs 30 = dgExtToIntBase a vc)
    (hhead : st.regs 31 = dgIncHeadBase a vc)
    (hgraphRoom : a + dynGraphSize vc ec ≤ 2 ^ w)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hgrad : st.regs 38 = gradients) (hlimbs : st.regs 3 = limbs)
    (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem (st.regs 4))
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgraphEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hzEnd : zeroPtr + limbs ≤ flags)
    (hroom : st.regs 4 + 3 * limbs * F.vol (F.V \ (Finset.filter (fun v => st.mem (flags + v) = 1) F.V)) < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ parent ∈ F.V, ∀ e ∈ F.E, ∀ direction : Bool, ∀ s seen r,
      ForestWorklistAt s F g base flags queue vc h limbs precision r seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + e * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
        ((if direction then value else 0) - (if direction then 0 else value)))) :
    ∃ out cost, Runs w p ω (propagateForestVertices entry) st .normal out cost ∧
      ForestRootScanAt out F g sortedBase base flags queue vc h limbs precision names.length names ∧
      st.regs 40 ≤ out.regs 40 ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      queue + vc ≤ out.regs 4 ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ (F.V.filter fun v => out.mem (flags + v) = 1)) < 2 ^ w ∧
      (∀ k, k = 3 ∨ 6 ≤ k → k ≠ 25 → k ≠ 40 → k ≠ 23 → k ≠ 24 →
        k ≠ 26 → k ≠ 28 → k ≠ 29 → k ≠ 32 → k ≠ 37 → k ≠ 41 → k ≠ 44 →
        out.regs k = st.regs k) ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ (F.V.filter fun v => out.mem (flags + v) = 1)) ≤
        st.regs 4 + 3 * limbs * F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost + F.vol (F.V \ (F.V.filter fun v => out.mem (flags + v) = 1)) * (129 * limbs + 209) ≤
        F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) *
          (129 * limbs + 209) + 26 * (out.regs 40 - st.regs 40) + 44 * (names.length - i) + 4 := by
  have hidx := hin.1
  have hcandidates := hin.2.1
  by_cases hlive : i < names.length
  · obtain ⟨mid, c, hstep, hmid, hlo, hg, hgv, hz', htail, hqe, hspace, keep, hscratch, hframe, hcost⟩ :=
      hin.step_runs (ω := ω) hlive hnames horder hsortedRoom hsortedEnd hgraph hforest
        hext hhead hgraphRoom hnext ht hc hn hgrad hlimbs hzPtr hz hzero hvalues hsub
        himpl hgraphEnd hgradEnd hzEnd hroom hw hpotEnd hflagsEnd hqEnd hfit
    obtain ⟨out, d, hloop, hout, hread, hg', hgv', hz'', ht', hqe', hspace', hkeep, hscratch', hprefix, hd⟩ :=
      hmid.scan_runs (ω := ω) (by omega) hnames horder hsortedRoom hsortedEnd hg hforest
        ((keep 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hext)
        ((keep 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hhead) hgraphRoom
        ((keep 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnext)
        ((keep 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht)
        ((keep 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
        ((keep 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
        ((keep 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgrad)
        ((keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlimbs)
        ((keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzPtr)
        hz' htail hgv hsub himpl hgraphEnd hgradEnd hzEnd hspace hw hpotEnd hflagsEnd hqe hfit
    have htest : Expr.eval w st (.bin .lt (.reg 44) (.reg 46)) = some 1 := by
      simp [Expr.eval, BinOp.eval, hidx, hcandidates, hlive, show 1 < 2 ^ w by omega]
    refine ⟨out, c + 4 + d, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨1, mid, c, d, htest, by decide, hstep, hloop, by simp [Expr.size]; omega⟩)),
      hout, hlo.trans hread, hg', hgv', hz'', ht', hqe', hspace', ?_, hscratch'.trans hscratch, fun x hx => (hprefix x hx).trans (hframe x hx), ?_⟩
    · intro k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41 h44
      exact (hkeep k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41 h44).trans
        (keep k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41 h44)
    · have hdelta : out.regs 40 - st.regs 40 =
          (out.regs 40 - mid.regs 40) + (mid.regs 40 - st.regs 40) := by omega
      have hcount : names.length - i = (names.length - (i + 1)) + 1 := by omega
      rw [hdelta, hcount]
      simp only [Nat.mul_add, Nat.mul_one] at hcost hd ⊢
      omega
  · have he : i = names.length := by omega
    clear hidx
    subst i
    have hidx := hin.1
    have htest : Expr.eval w st (.bin .lt (.reg 44) (.reg 46)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hidx, hcandidates]
    exact ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨htest, rfl, rfl, rfl⟩),
      hin, le_rfl, hgraph, hvalues, hz, hzero, hqEnd, hroom,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, le_rfl, fun _ _ => rfl, by simp [Nat.add_comm]⟩
termination_by names.length - i
decreasing_by omega

/-- The completed ordered scan returns all active potentials. Distinct
queued vertices bound the parent count by the number of active names. -/
theorem ForestRootScanAt.scan_potentials_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision sortedBase i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i ≤ names.length) (hnames : names.toFinset = F.V) (horder : names.Pairwise (· ≤ ·)) (hndNames : names.Nodup)
    (hsortedRoom : sortedBase + names.length < 2 ^ w)
    (hsortedEnd : sortedBase + names.length ≤ base)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hext : st.regs 30 = dgExtToIntBase a vc)
    (hhead : st.regs 31 = dgIncHeadBase a vc)
    (hgraphRoom : a + dynGraphSize vc ec ≤ 2 ^ w)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc)
    (hgrad : st.regs 38 = gradients) (hlimbs : st.regs 3 = limbs)
    (hzPtr : st.regs 22 = zeroPtr)
    (hz : PathIntAt st.mem zeroPtr h limbs 0) (hzero : ZeroFrom st.mem (st.regs 4))
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgraphEnd : a + dynGraphSize vc ec ≤ base)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ base)
    (hzEnd : zeroPtr + limbs ≤ flags)
    (hroom : st.regs 4 + 3 * limbs * F.vol (F.V \ (Finset.filter (fun v => st.mem (flags + v) = 1) F.V)) < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ parent ∈ F.V, ∀ e ∈ F.E, ∀ direction : Bool, ∀ s seen r,
      ForestWorklistAt s F g base flags queue vc h limbs precision r seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + e * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
        ((if direction then value else 0) - (if direction then 0 else value)))) :
    ∃ out cost, Runs w p ω (propagateForestVertices entry) st .normal out cost ∧
      ForestPotentialsAt out.mem base h limbs precision F g F.V ∧
      out.regs 40 = F.n ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      queue + vc ≤ out.regs 4 ∧
      out.regs 4 < 2 ^ w ∧
      out.regs 4 ≤ st.regs 4 + 3 * limbs * F.vol F.V ∧
      (∀ k, k = 3 ∨ 6 ≤ k → k ≠ 25 → k ≠ 40 → k ≠ 23 → k ≠ 24 →
        k ≠ 26 → k ≠ 28 → k ≠ 29 → k ≠ 32 → k ≠ 37 → k ≠ 41 → k ≠ 44 →
        out.regs k = st.regs k) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ F.vol F.V * (129 * limbs + 209) + 70 * F.n + 4 := by
  obtain ⟨out, cost, hr, hout, _, hg, hv, hz', ht', hqe, hspace, hregs, hscratch, hframe, hcost⟩ :=
    hin.scan_runs (ω := ω) hi hnames horder hsortedRoom hsortedEnd hgraph hforest
      hext hhead hgraphRoom hnext ht hc hn hgrad hlimbs hzPtr hz hzero hvalues hsub
      himpl hgraphEnd hgradEnd hzEnd hroom hw hpotEnd hflagsEnd hqEnd hfit
  obtain ⟨_, _, _, _, _, _, _, seen, hnd, hsub', hread, _, _, _, hpots, hprefix, _, _⟩ := hout
  have hcover : F.V ⊆ seen.toFinset := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hnames.symm ▸ hv))
    exact hprefix j hj hj
  have hseen : seen.toFinset = F.V := Finset.Subset.antisymm hsub' hcover
  have hcount : out.regs 40 = F.n := by
    rw [hread, MGraph.n, ← hseen, List.toFinset_card_of_nodup hnd]
  have hlen : names.length = F.n := by
    rw [MGraph.n, ← hnames, List.toFinset_card_of_nodup hndNames]
  have hvol : F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) ≤ F.vol F.V :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _)
  have hmul := Nat.mul_le_mul_right (129 * limbs + 209) hvol
  have hbound := Nat.mul_le_mul_left (3 * limbs) hvol
  exact ⟨out, cost, hr, hseen ▸ hpots, hcount, hg, hv, hz', ht', hqe, by omega, by omega, hregs, hframe, by omega⟩

/-- Prepare the traversal storage and compute every active root potential. -/
@[expose] def computeForestPotentials (copy sort entry : ℕ) : Stmt :=
  setupForestTraversal copy sort ;; propagateForestVertices entry

/-- This traversal pays for sorting and scanning only active names and
incidences. The word-space bound also reserves the arrays indexed by names. -/
theorem computeForestPotentials_runs
    {w copy sort entry a vc ec heap h limbs precision gradients : ℕ} {F : MGraph}
    {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool} {edges : Finset ℕ}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hgraph : DynGraphAt st.mem a vc ec F) (ha : st.regs 45 = a) (hvc : st.regs 21 = vc)
    (hh : st.regs 4 = heap) (hl : st.regs 3 = limbs) (hz : ZeroFrom st.mem heap)
    (hext : st.regs 30 = dgExtToIntBase a vc) (hhead : st.regs 31 = dgIncHeadBase a vc)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc) (hgrad : st.regs 38 = gradients)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + F.n ≤ heap)
    (hsortRoom : heap + F.n + 2 < 2 ^ w) (hcount : 2 * F.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : F.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g) (hsub : F.E ⊆ edges)
    (hgradEnd : ∀ e ∈ edges, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hspace : heap + F.n + vc * limbs + limbs + vc + vc + 3 * limbs * F.vol F.V < 2 ^ w)
    (hfit : let base := heap + F.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ F.V, ∀ e ∈ F.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s F g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision edges g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value)))) :
    ∃ out cost, Runs w p ω (computeForestPotentials copy sort entry) st .normal out cost ∧
      out.regs 20 = heap + F.n ∧ ForestPotentialsAt out.mem (out.regs 20) h limbs precision F g F.V ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      ZeroFrom out.mem (out.regs 4) ∧ out.regs 4 < 2 ^ w ∧
      (∀ r, r ∈ ([6, 7, 13, 14, 15, 16, 17, 50] : List ℕ) → out.regs r = st.regs r) ∧
      heap + F.n + vc * limbs + limbs + vc + vc ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + F.n + vc * limbs + limbs + vc + vc + 3 * limbs * F.vol F.V ∧
      out.regs 3 = limbs ∧ (∀ x < heap, out.mem x = st.mem x) ∧
      cost ≤ 280 * (F.n * (2 * Nat.log 2 (F.n + 2) + 1) + 1) +
        F.vol F.V * (129 * limbs + 209) + 87 * F.n + 84 := by
  obtain ⟨mid, names, c, hsetup, hnd, ho, hnames, hi, hlen, hs, hlist, hb, hzptr, hf, hq,
    hr, hwrite, hheap, hflags, hpots, hzval, htail, hframe, hregs, hcost⟩ :=
    setupForestTraversal_runs (ω := ω) g hcopy hsort hgraph ha hvc hh hl hz hgraphEnd
      hlistEnd hsortRoom hcount hw hforest (by omega)
  have hlength : names.length = F.n := by
    rw [MGraph.n, ← hnames, List.toFinset_card_of_nodup hnd]
  have hin := ForestRootScanAt.initial hi hlen hs hlist hb hf hq hr hwrite
    (by rw [← hf]; exact hflags) hpots htail
  have hg := hgraph.of_agree (fun x _ hx => hframe x (by omega))
  have hgr := hvalues.congr (fun e he j hj => hframe _ (by have := hgradEnd e he; omega))
  have htail' : ZeroFrom mid.mem (mid.regs 4) := fun x hx => htail x (by omega)
  have hroom : mid.regs 4 + 3 * limbs * F.vol
      (F.V \ (F.V.filter fun v => mid.mem (heap + F.n + vc * limbs + limbs + v) = 1)) < 2 ^ w := by
    have hvol : F.vol (F.V \ (F.V.filter fun v => mid.mem (heap + F.n + vc * limbs + limbs + v) = 1))
        ≤ F.vol F.V :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _)
    have hm := Nat.mul_le_mul_left (3 * limbs) hvol
    omega
  have keep (r : ℕ) (hne : r ≠ 4) (hr : r = 3 ∨ 21 ≤ r ∧ r ≤ 38 ∧ r ≠ 22 ∧ r ≠ 36) :
      mid.regs r = st.regs r :=
    hregs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hne
  obtain ⟨out, d, hrun, hp, _, hg', hgv, _, ht', hheapEnd, hword, hupper, hkeep, hprefix, hd⟩ :=
    hin.scan_potentials_runs (ω := ω) (Nat.zero_le _) hnames ho hnd (by omega) (by omega)
      hg hforest ((keep 30 (by decide) (by decide)).trans hext)
      ((keep 31 (by decide) (by decide)).trans hhead) (by omega)
      ((keep 27 (by decide) (by decide)).trans hnext) ((keep 33 (by decide) (by decide)).trans ht)
      ((keep 34 (by decide) (by decide)).trans hc) ((keep 35 (by decide) (by decide)).trans hn)
      ((keep 38 (by decide) (by decide)).trans hgrad) ((keep 3 (by decide) (by decide)).trans hl)
      hzptr (hzptr ▸ hzval) htail' hgr hsub himpl (by omega)
      (fun e he => (hgradEnd e he).trans (Nat.le_add_right _ _)) (by omega) hroom
      (by omega) (by omega) (by omega) (by omega) hfit
  have hb' := (hkeep 20 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hsetup, hrun, rfl⟩),
    hb', hb'.symm ▸ hp, hg', hgv, ht', hword, ?_, hheapEnd, by omega, ?_, fun x hx => (hprefix x (by omega)).trans (hframe x hx), by omega⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hlo : 6 ≤ r := by omega
    exact (hkeep r (Or.inr hlo) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hregs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact (hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((keep 3 (by decide) (by decide)).trans hl)

/-- Reserve the deeper gradient table after the potential traversal.
Register 50 supplies the edge-name capacity of the input graph. -/
@[expose] def reserveDeeperGradients : Stmt :=
  .assign 14 (.reg 4) ;;
  .assign 4 (.bin .add (.reg 4) (.bin .mul (.reg 50) (.reg 3)))

/-- The output table starts at the traversal's final heap. Reserving it
preserves the potentials below the heap and leaves the new tail zeroed. -/
theorem reserveDeeperGradients_runs {w heap capacity limbs : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hc : st.regs 50 = capacity) (hl : st.regs 3 = limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + capacity * limbs < 2 ^ w) :
    ∃ out, Runs w p ω reserveDeeperGradients st .normal out 9 ∧
      out.regs 14 = heap ∧ out.regs 4 = heap + capacity * limbs ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, r ≠ 14 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem := by
  let mid := { st with regs := Function.update st.regs 14 heap }
  let out := { mid with regs := Function.update mid.regs 4 (heap + capacity * limbs) }
  have hm : capacity * limbs < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 14 (.reg 4)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hlast : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.bin .mul (.reg 50) (.reg 3))))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hh, hc, hl, hm, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 6, hfirst, hlast, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, ?_, rfl⟩
  · intro a ha
    exact hz a (by change heap + capacity * limbs ≤ a at ha; omega)
  · intro r h14 h4
    simp [out, mid, Function.update_of_ne, h14, h4]

/-- Allocate the output gradient table and then populate its active cells. -/
@[expose] def reserveAndPrepareDeeperGradients (entry : ℕ) : Stmt :=
  reserveDeeperGradients ;; prepareShiftGradientInputs entry

/-- Reserving the table adds ten steps to the deeper gradient scan. -/
theorem reserveAndPrepareDeeperGradients_runs
    {w h base vc ec nextBase nextVC nextEC src dst potential limbs precision entry : ℕ}
    {G H : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (nextLengths : ℕ → ℝ) (hsub : H.E ⊆ G.E)
    (hn : st.regs 6 = nextBase) (hnGraph : DynGraphAt st.mem nextBase nextVC nextEC H)
    (hgraph : DynGraphAt st.mem base vc ec G) (hvertices : G.V ⊆ forest.T.V)
    (hgrad : EdgeValuesAt st.mem src h limbs precision G.E g)
    (hforest : forest.T.IsForest)
    (hpots : ForestPotentialsAt st.mem potential h limbs precision forest.T g forest.T.V)
    (hsrc : st.regs 13 = src) (hcap : st.regs 50 = ec)
    (htail : st.regs 15 = dgETailSlotBase base vc ec)
    (hhead : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hnames : st.regs 17 = dgIntToExtBase base vc)
    (hbase : st.regs 20 = potential) (hlimbs : st.regs 3 = limbs)
    (hheap : st.regs 4 = dst) (hzero : ZeroFrom st.mem dst)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgEnd : base + dynGraphSize vc ec ≤ dst)
    (hsEnd : ∀ e ∈ G.E, src + e * limbs + limbs ≤ dst)
    (hpEnd : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hnEnd : nextBase + dynGraphSize nextVC nextEC ≤ dst)
    (hlenTable : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ dst)
    (hfit : ∀ e ∈ G.E, Num.Fits h limbs
      (Num.intVal st.mem (src + e * limbs) h limbs +
        (Num.intVal st.mem (potential + G.head e * limbs) h limbs -
          Num.intVal st.mem (potential + G.tail e * limbs) h limbs)))
    (hspace : dst + ec * limbs + 3 * limbs * H.m < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out cost, Runs w p ω (reserveAndPrepareDeeperGradients entry) st .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧ out.regs 8 = dst ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      out.regs 4 = dst + ec * limbs + 3 * limbs * H.m ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < dst, out.mem addr = st.mem addr) ∧
      cost ≤ (129 * limbs + 172) * H.m + 41 := by
  obtain ⟨mid, ha, hdst, hh, hz, hregs, hm⟩ :=
    reserveDeeperGradients_runs (w := w) (p := p) (ω := ω) hheap hcap hlimbs hzero (by omega)
  have hs (r : ℕ) (hr : r ≠ 14) (hr' : r ≠ 4) : mid.regs r = st.regs r := hregs r hr hr'
  have h7 := hs 7 (by decide) (by decide)
  have hslot (e : ℕ) (he : e ∈ G.E) : dst + e * limbs + limbs ≤ dst + ec * limbs := by
    have hn := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hgraph.2.2.1 e he))
    simpa only [Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add_left hn dst
  obtain ⟨out, cost, hr, ho6, ho7, ho8, hg, hv, hp, hf, hz', hfKeep, hc⟩ :=
    prepareShiftGradientInputs_of_forestPotentials_runs (ω := ω) nextLengths hsub
      ((hs 6 (by decide) (by decide)).trans hn) (hm.symm ▸ hnGraph) (hm.symm ▸ hgraph)
      hvertices (hm.symm ▸ hgrad) hforest (hm.symm ▸ hpots)
      ((hs 13 (by decide) (by decide)).trans hsrc) hdst
      ((hs 15 (by decide) (by decide)).trans htail) ((hs 16 (by decide) (by decide)).trans hhead)
      ((hs 17 (by decide) (by decide)).trans hnames) ((hs 20 (by decide) (by decide)).trans hbase)
      ((hs 3 (by decide) (by decide)).trans hlimbs) hh (hh ▸ hz)
      himpl hgEnd hsEnd hpEnd hnEnd (by simpa only [hm, h7] using hlenTable)
      (by simpa only [h7] using hlenEnd) hslot (Nat.le_add_right _ _)
      (hm.symm ▸ hfit) hspace hw
  exact ⟨out, 9 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 9, cost, ha, hr, rfl⟩),
    ho6, ho7.trans h7, ho8, hg, hv, hp, hf, hz', (fun a ha => (hfKeep a ha).trans (congrFun hm a)), by omega⟩

/-- Compute the shifted forest potentials and the gradient table for the
first deeper graph in Algorithm 1 (page 20). -/
@[expose] def computeDeeperGradients (copy sort entry : ℕ) : Stmt :=
  computeForestPotentials copy sort entry ;; reserveAndPrepareDeeperGradients entry

/-- The traversal and the scan share a heap. Their combined allowance places
the gradient output after the potential table and leaves a zeroed tail. -/
theorem computeDeeperGradients_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hgraph : DynGraphAt st.mem a vc ec forest.T) (ha : st.regs 45 = a) (hvc : st.regs 21 = vc)
    (hh : st.regs 4 = heap) (hl : st.regs 3 = limbs) (hz : ZeroFrom st.mem heap)
    (hext : st.regs 30 = dgExtToIntBase a vc) (hhead : st.regs 31 = dgIncHeadBase a vc)
    (hnext : st.regs 27 = dgHeNextBase a vc ec) (ht : st.regs 33 = dgETailSlotBase a vc ec)
    (hc : st.regs 34 = ec) (hn : st.regs 35 = dgIntToExtBase a vc) (hgrad : st.regs 38 = gradients)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h13 : st.regs 13 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ heap)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients h limbs precision G.E g →
      ∀ e ∈ G.E, Num.Fits h limbs
        (Num.intVal mem (gradients + e * limbs) h limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) h limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) h limbs))) :
    ∃ out cost, Runs w p ω (computeDeeperGradients copy sort entry) st .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧
      heap ≤ out.regs 8 ∧ out.regs 8 + ecG * limbs ≤ out.regs 4 ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 126 := by
  obtain ⟨mid, c, htRun, hb, hp, _, hValues, hZero, _, hregs, hlow, hhigh, hlimbs, hframe, hcost⟩ :=
    computeForestPotentials_runs (ω := ω) hcopy hsort hgraph ha hvc hh hl hz hext hhead
      hnext ht hc hn hgrad hgraphEnd hlistEnd hsortRoom hcount hw hforest hvalues hsub
      hgradEnd himpl (by omega) hfit
  have hG' := hG.of_agree (fun x _ hx => hframe x (by omega))
  have hH' := hH.of_agree (fun x _ hx => hframe x (by omega))
  have h7 := hregs 7 (by decide)
  have hlen' := hlen.congr (fun e he j hj => hframe _ (by have := hlenEnd e he; omega))
  have hpotEnd (v : ℕ) (hv : v ∈ G.V) : heap + forest.T.n + v * limbs + limbs ≤ mid.regs 4 := by
    have hm := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hgraph.2.1 v (hvertices hv)))
    simp only [Nat.succ_mul] at hm
    omega
  obtain ⟨out, d, hr, ho6, ho7, ho8, hg, hlengths, hgradients, hheapOut, htail, hkeep, hd⟩ :=
    reserveAndPrepareDeeperGradients_runs (ω := ω) nextLengths hHE
      ((hregs 6 (by decide)).trans h6) hH' hG' hvertices hValues hforest (hb ▸ hp)
      ((hregs 13 (by decide)).trans h13) ((hregs 50 (by decide)).trans h50)
      ((hregs 15 (by decide)).trans h15) ((hregs 16 (by decide)).trans h16)
      ((hregs 17 (by decide)).trans h17) hb hlimbs rfl hZero himpl (by omega)
      (fun e he => (hgradEnd e he).trans (by omega)) hpotEnd (by omega)
      (h7.symm ▸ hlen') (fun e he => by rw [h7]; have := hlenEnd e he; omega)
      (hfitScan mid.mem (hb ▸ hp) hValues) (by omega) hwScan
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, htRun, hr, rfl⟩),
    ho6, ho7.trans h7, by omega, by omega, hg, hlengths, hgradients, htail, by omega, by omega,
    (fun a ha => (hkeep a (by omega)).trans (hframe a ha)), by omega⟩

/-- Read the spanning tree pointer from the selected LSF header in
register 9. The potential calculation reads the tree in register 45. -/
@[expose] def loadShiftPotentialTree : Stmt :=
  .assign 45 (.load (.reg 9))

/-- The Shift readout already represents the exact traversal graph. Reading
its pointer leaves the length table, heap and caller registers intact. -/
theorem loadShiftPotentialTree_runs {w vc ec h limbs precision : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {edges : Finset ℕ} {forest : LSF}
    (hforest : LSFAt st.mem (st.regs 9) vc ec h limbs precision edges forest) :
    ∃ out, Runs w p ω loadShiftPotentialTree st .normal out 3 ∧
      out.regs 45 = st.mem (st.regs 9) ∧
      DynGraphAt out.mem (out.regs 45) vc ec forest.T ∧
      (∀ r, r ≠ 45 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let tree := st.mem (st.regs 9)
  let out := { st with regs := Function.update st.regs 45 tree }
  have hrun : Runs w p ω loadShiftPotentialTree st .normal out 3 :=
    runs_assign_iff.mpr ⟨tree, rfl, rfl, rfl, rfl⟩
  exact ⟨out, hrun, by simp [out, tree], by simpa [out, tree] using hforest.1,
    fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩

/-- Read the selected tree and its vertex and edge capacities. -/
@[expose] def loadShiftPotentialTreeHeader : Stmt :=
  loadShiftPotentialTree ;;
  .assign 21 (.load (.reg 45)) ;;
  .assign 34 (.load (.bin .add (.reg 45) (.const 1)))

/-- The headers give the traversal's address and capacities directly from
the LSF readout, leaving the deeper graph and length inputs intact. -/
theorem loadShiftPotentialTreeHeader_runs {w vc ec h limbs precision : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {edges : Finset ℕ} {forest : LSF}
    (hforest : LSFAt st.mem (st.regs 9) vc ec h limbs precision edges forest)
    (hroom : st.mem (st.regs 9) + dynGraphSize vc ec ≤ 2 ^ w) :
    ∃ out, Runs w p ω loadShiftPotentialTreeHeader st .normal out 13 ∧
      out.regs 45 = st.mem (st.regs 9) ∧ out.regs 21 = vc ∧ out.regs 34 = ec ∧
      DynGraphAt out.mem (out.regs 45) vc ec forest.T ∧
      (∀ r, r ≠ 45 → r ≠ 21 → r ≠ 34 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨pre, hload, hbase, hg, hregs, hm, hp⟩ :=
    loadShiftPotentialTree_runs (w := w) (p := p) (ω := ω) hforest
  let mid := { pre with regs := Function.update pre.regs 21 vc }
  let out := { mid with regs := Function.update mid.regs 34 ec }
  have ⟨_, _, _, hvc, hec, _⟩ := hg
  have hv : pre.mem (pre.regs 45) = vc := by simpa only [dgVCapOff, Nat.add_zero] using hvc
  have he : pre.mem (pre.regs 45 + 1) = ec := by simpa only [dgECapOff] using hec
  have haddr : pre.regs 45 + 1 < 2 ^ w := by
    simp only [dynGraphSize] at hroom
    omega
  have hone : 1 < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 21 (.load (.reg 45))) pre .normal mid 3 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hv], rfl, rfl, rfl⟩
  have hlast : Runs w p ω (.assign 34 (.load (.bin .add (.reg 45) (.const 1))))
      mid .normal out 5 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, haddr, hone, he],
      rfl, rfl, rfl⟩
  have hb : out.regs 45 = pre.regs 45 := by simp [out, mid, Function.update_of_ne]
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨pre, 3, 9, hload,
      runs_seq_iff.mpr (Or.inr ⟨mid, 3, 5, hfirst, hlast, rfl⟩), rfl⟩),
    hb.trans hbase, by simp [out, mid, Function.update_of_ne], by simp [out],
    hb.symm ▸ hg, ?_, hm, hp⟩
  intro r h45 h21 h34
  simpa only [out, mid, Function.update_of_ne h34, Function.update_of_ne h21] using hregs r h45

/-- Compute the named tree's adjacency array base addresses. -/
@[expose] def prepareShiftTreeAdjacency : Stmt :=
  .assign 30 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 3) (.reg 21))) ;;
  .assign 31 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 6) (.reg 21))) ;;
  .assign 35 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 4) (.reg 21))) ;;
  .assign 33 (.bin .add (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 7) (.reg 21))) (.bin .mul (.const 3) (.reg 34))) ;;
  .assign 27 (.bin .add (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 7) (.reg 21))) (.bin .mul (.const 7) (.reg 34)))

/-- The prepared registers address the exact arrays in the dynamic graph layout. -/
theorem prepareShiftTreeAdjacency_runs {w a vc ec : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (ha : st.regs 45 = a) (hv : st.regs 21 = vc) (he : st.regs 34 = ec)
    (hroom : a + dynGraphSize vc ec < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out, Runs w p ω prepareShiftTreeAdjacency st .normal out 52 ∧
      out.regs 30 = dgExtToIntBase a vc ∧
      out.regs 31 = dgIncHeadBase a vc ∧
      out.regs 35 = dgIntToExtBase a vc ∧
      out.regs 33 = dgETailSlotBase a vc ec ∧
      out.regs 27 = dgHeNextBase a vc ec ∧
      (∀ r, r ≠ 30 → r ≠ 31 → r ≠ 35 → r ≠ 33 → r ≠ 27 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  simp only [dynGraphSize] at hroom
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hheader : a + 4 < 2 ^ w := by omega
  have hv3 : 3 * vc < 2 ^ w := by omega
  have hb3 : a + 4 + 3 * vc < 2 ^ w := by omega
  have hv4 : 4 * vc < 2 ^ w := by omega
  have hb4 : a + 4 + 4 * vc < 2 ^ w := by omega
  have hv6 : 6 * vc < 2 ^ w := by omega
  have hb6 : a + 4 + 6 * vc < 2 ^ w := by omega
  have hv7 : 7 * vc < 2 ^ w := by omega
  have hb7 : a + 4 + 7 * vc < 2 ^ w := by omega
  have he3 : 3 * ec < 2 ^ w := by omega
  have hd3 : a + 4 + 7 * vc + 3 * ec < 2 ^ w := by omega
  have he7 : 7 * ec < 2 ^ w := by omega
  have hd7 : a + 4 + 7 * vc + 7 * ec < 2 ^ w := by omega
  let s1 := { st with regs := Function.update st.regs 30 (dgExtToIntBase a vc) }
  let s2 := { s1 with regs := Function.update s1.regs 31 (dgIncHeadBase a vc) }
  let s3 := { s2 with regs := Function.update s2.regs 35 (dgIntToExtBase a vc) }
  let s4 := { s3 with regs := Function.update s3.regs 33 (dgETailSlotBase a vc ec) }
  let s5 := { s4 with regs := Function.update s4.regs 27 (dgHeNextBase a vc ec) }
  have h1 : Runs w p ω (.assign 30 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 3) (.reg 21)))) st .normal s1 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hv, dgExtToIntBase,
      hheader, hw3, hw4, hv3, hb3],
      rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 31 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 6) (.reg 21)))) s1 .normal s2 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hv, dgIncHeadBase,
      hheader, hw4, hw6, hv6, hb6, Function.update_of_ne, s1],
      rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 35 (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 4) (.reg 21)))) s2 .normal s3 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hv, dgIntToExtBase,
      hheader, hw4, hv4, hb4, Function.update_of_ne, s1, s2],
      rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 33 (.bin .add (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 7) (.reg 21))) (.bin .mul (.const 3) (.reg 34)))) s3 .normal s4 12 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hv, he, dgETailSlotBase,
      hheader, hw3, hw4, hw7, hv7, hb7, he3, hd3, Function.update_of_ne, s1, s2, s3],
      rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 27 (.bin .add (.bin .add (.bin .add (.reg 45) (.const 4)) (.bin .mul (.const 7) (.reg 21))) (.bin .mul (.const 7) (.reg 34)))) s4 .normal s5 12 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hv, he, dgHeNextBase,
      hheader, hw4, hw7, hv7, hb7, he7, hd7, Function.update_of_ne, s1, s2, s3, s4],
      rfl, rfl, rfl⟩
  refine ⟨s5, runs_seq_iff.mpr (Or.inr ⟨s1, 8, 43, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 8, 34, h2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 8, 25, h3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 12, 12, h4,
      h5, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [Function.update_of_ne, s1, s2, s3, s4, s5],
    by simp [Function.update_of_ne, s2, s3, s4, s5],
    by simp [Function.update_of_ne, s3, s4, s5],
    by simp [Function.update_of_ne, s4, s5],
    by simp [s5],
    ?_, rfl, rfl⟩
  intro r h30 h31 h35 h33 h27
  simp [s5, s4, s3, s2, s1, Function.update_of_ne, h30, h31, h35, h33, h27]

/-- Load all traversal graph registers from the forest readout. -/
@[expose] def loadShiftTreeTraversal : Stmt :=
  loadShiftPotentialTreeHeader ;; prepareShiftTreeAdjacency

/-- The selected forest header provides the capacities and incidence arrays
in a fixed number of steps before the traversal. -/
theorem loadShiftTreeTraversal_runs {w vc ec h limbs precision : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {edges : Finset ℕ} {forest : LSF}
    (hforest : LSFAt st.mem (st.regs 9) vc ec h limbs precision edges forest)
    (hroom : st.mem (st.regs 9) + dynGraphSize vc ec < 2 ^ w) (hw : 7 < 2 ^ w) :
    let a := st.mem (st.regs 9)
    ∃ out, Runs w p ω loadShiftTreeTraversal st .normal out 66 ∧
      DynGraphAt out.mem a vc ec forest.T ∧
      out.regs 45 = a ∧ out.regs 21 = vc ∧ out.regs 34 = ec ∧
      out.regs 30 = dgExtToIntBase a vc ∧ out.regs 31 = dgIncHeadBase a vc ∧
      out.regs 35 = dgIntToExtBase a vc ∧ out.regs 33 = dgETailSlotBase a vc ec ∧
      out.regs 27 = dgHeNextBase a vc ec ∧
      (∀ r, r ≠ 45 → r ≠ 21 → r ≠ 34 → r ≠ 30 → r ≠ 31 → r ≠ 35 →
        r ≠ 33 → r ≠ 27 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hload, a, hv, he, hg, hkeep, hm, hp⟩ :=
    loadShiftPotentialTreeHeader_runs (p := p) (ω := ω) hforest hroom.le
  obtain ⟨out, hprep, hext, hhead, hnames, htail, hnext, hregs, hm', hp'⟩ :=
    prepareShiftTreeAdjacency_runs (p := p) (ω := ω) a hv he hroom hw
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 13, 52, hload, hprep, rfl⟩),
    hm'.symm ▸ (a ▸ hg), ?_, ?_, ?_, hext, hhead, hnames, htail, hnext, ?_,
    hm'.trans hm, hp'.trans hp⟩
  · exact (hregs 45 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a
  · exact (hregs 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hv
  · exact (hregs 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans he
  · intro r h45 h21 h34 h30 h31 h35 h33 h27
    exact (hregs r h30 h31 h35 h33 h27).trans (hkeep r h45 h21 h34)

/-- Pass the Shift readout's free heap and the input gradient pointer to
the forest traversal. The deeper scan also reads the gradient from register 13. -/
@[expose] def passShiftTraversalInputs : Stmt :=
  .assign 4 (.reg 5) ;; .assign 38 (.reg 13)

/-- The handoff retains the selected forest header, the copied graph,
and the prepared lengths. -/
theorem passShiftTraversalInputs_runs {w : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} :
    ∃ out, Runs w p ω passShiftTraversalInputs st .normal out 5 ∧
      out.regs 4 = st.regs 5 ∧ out.regs 38 = st.regs 13 ∧
      (∀ r, r ≠ 4 → r ≠ 38 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 4 (st.regs 5) }
  let out := { mid with regs := Function.update mid.regs 38 (st.regs 13) }
  have hheap : Runs w p ω (.assign 4 (.reg 5)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hgrad : Runs w p ω (.assign 38 (.reg 13)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hheap, hgrad, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r h4 h38
  simp [out, mid, Function.update_of_ne, h4, h38]

/-- After the tool calls, register 3 is reused for the fixed-point width. -/
@[expose] def setShiftGradientWidth : Stmt :=
  .assign 3 (.reg 67)

/-- Setting the width costs two steps and preserves the forest readout
and all the graph, length, gradient, and heap pointers. -/
theorem setShiftGradientWidth_runs {w limbs : ℕ} {p : Program} {st : State}
    {ω : ℕ → Bool} (hlimbs : st.regs 67 = limbs) :
    ∃ out, Runs w p ω setShiftGradientWidth st .normal out 2 ∧
      out.regs 3 = limbs ∧ (∀ r, r ≠ 3 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 3 limbs }
  have hstep : Runs w p ω setShiftGradientWidth st .normal out 2 :=
    runs_assign_iff.mpr ⟨limbs, by simp [Expr.eval, hlimbs], rfl, rfl, rfl⟩
  exact ⟨out, hstep, by simp [out], fun r hr => by simp [out, Function.update_of_ne hr], rfl, rfl⟩

/-- Prepare deeper gradients directly from the selected Shift readout. -/
@[expose] def prepareShiftReadoutGradients (copy sort entry : ℕ) : Stmt :=
  setShiftGradientWidth ;; loadShiftTreeTraversal ;; passShiftTraversalInputs ;; computeDeeperGradients copy sort entry

/-- The selected forest readout, copied graph, and prepared lengths suffice
to start the deeper gradient program after fixed register setup. -/
theorem prepareShiftReadoutGradients_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h13 : st.regs 13 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ heap)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients h limbs precision G.E g →
      ∀ e ∈ G.E, Num.Fits h limbs
        (Num.intVal mem (gradients + e * limbs) h limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) h limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) h limbs))) :
    ∃ out cost, Runs w p ω (prepareShiftReadoutGradients copy sort entry) st .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧
      heap ≤ out.regs 8 ∧ out.regs 8 + ecG * limbs ≤ out.regs 4 ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 202 := by
  obtain ⟨width, hwidth, hl, hwidthRegs, hwidthMem, _⟩ :=
    setShiftGradientWidth_runs (p := p) (ω := ω) (st := st) hlimbs
  obtain ⟨pre, htree, hg, hp, hv, he, hext, hhead, hnames, htail, hnext, hkeep, hm, _⟩ :=
    loadShiftTreeTraversal_runs (p := p) (ω := ω) (st := width)
      (by simpa only [hwidthRegs 9 (by decide), hwidthMem] using hreadout)
      (by rw [hwidthRegs 9 (by decide), hwidthMem, ha]; omega) hwScan
  have hreadoutAddr : width.mem (width.regs 9) = a := by
    simpa only [hwidthRegs 9 (by decide), hwidthMem] using ha
  obtain ⟨mid, hpass, hpHeap, hpGrad, hregs, hm', _⟩ :=
    passShiftTraversalInputs_runs (w := w) (p := p) (ω := ω) (st := pre)
  have hmem := (hm'.trans hm).trans hwidthMem
  have keep (r : ℕ) (hlo : r ≤ 17 ∨ r = 50) (hne : r ≠ 4) : mid.regs r = width.regs r :=
    (hregs r hne (by omega)).trans
      (hkeep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  have keepInput (r : ℕ) (hlo : r ≤ 17 ∨ r = 50) (hne : r ≠ 4) (h3 : r ≠ 3) :
      mid.regs r = st.regs r :=
    (keep r hlo hne).trans (hwidthRegs r h3)
  have h7 := keepInput 7 (by decide) (by decide) (by decide)
  obtain ⟨out, c, hrun, ho6, ho7, ho8Lo, ho8, hgo, hlo, hgr, hz', hheapLo, hheapHi, hkeep, hcost⟩ :=
    computeDeeperGradients_runs (ω := ω) hcopy hsort (hreadoutAddr ▸ (hm'.symm ▸ hg))
      ((hregs 45 (by decide) (by decide)).trans (hp.trans hreadoutAddr))
      ((hregs 21 (by decide) (by decide)).trans hv)
      (hpHeap.trans ((hkeep 5 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans ((hwidthRegs 5 (by decide)).trans hh)))
      ((keep 3 (by decide) (by decide)).trans hl) (hmem.symm ▸ hz)
      ((hregs 30 (by decide) (by decide)).trans (hreadoutAddr ▸ hext))
      ((hregs 31 (by decide) (by decide)).trans (hreadoutAddr ▸ hhead))
      ((hregs 27 (by decide) (by decide)).trans (hreadoutAddr ▸ hnext))
      ((hregs 33 (by decide) (by decide)).trans (hreadoutAddr ▸ htail))
      ((hregs 34 (by decide) (by decide)).trans he)
      ((hregs 35 (by decide) (by decide)).trans (hreadoutAddr ▸ hnames))
      (hpGrad.trans ((hkeep 13 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans ((hwidthRegs 13 (by decide)).trans h13)))
      hgraphEnd hlistEnd hsortRoom hcount hw hforest (hmem.symm ▸ hvalues) hsub hgradEnd
      himpl (hmem.symm ▸ hG) hGEnd hvertices (hmem.symm ▸ hH) hHEnd hHE
      ((keepInput 6 (by decide) (by decide) (by decide)).trans h6) ((keepInput 13 (by decide) (by decide) (by decide)).trans h13)
      ((keepInput 50 (by decide) (by decide) (by decide)).trans h50) ((keepInput 15 (by decide) (by decide) (by decide)).trans h15)
      ((keepInput 16 (by decide) (by decide) (by decide)).trans h16) ((keepInput 17 (by decide) (by decide) (by decide)).trans h17)
      nextLengths (by simpa only [hmem, h7] using hlen) (by simpa only [h7] using hlenEnd)
      hwScan hspace hfit hfitScan
  exact ⟨out, c + 76,
    runs_seq_iff.mpr (Or.inr ⟨width, 2, c + 73, hwidth,
      runs_seq_iff.mpr (Or.inr ⟨pre, 66, 5 + c + 1, htree,
      runs_seq_iff.mpr (Or.inr ⟨mid, 5, c, hpass, hrun, rfl⟩), by omega⟩), by omega⟩),
    ho6, ho7.trans h7, ho8Lo, ho8, hgo, hlo, hgr, hz', hheapLo, hheapHi, (fun a ha => (hkeep a ha).trans (congrFun hmem a)), by omega⟩


/-- Shift in Algorithm 1 (page 20) restarts the new branch and prepares the
graph, lengths, and gradients for the first deeper initialization. -/
@[expose] def shiftRestartPrepareGradients (restart read forestOp copy sort entry : ℕ) : Stmt :=
  shiftRestartGraphAndLengths restart read forestOp ;;
    prepareShiftReadoutGradients copy sort entry

/-- The prepared readouts are consumed directly by the traversal. Its bound
adds the traversal and one sequencing step to the restart prefix cost. -/
theorem shiftRestartPrepareGradients_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {restart read forestOp prefixCost : ℕ} {p : Program} {initial st : State} {ω : ℕ → Bool}
    (hprefix : Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h13 : st.regs 13 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients h limbs precision G.E g →
      ∀ e ∈ G.E, Num.Fits h limbs
        (Num.intVal mem (gradients + e * limbs) h limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) h limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) h limbs))) :
    ∃ out cost, Runs w p ω (shiftRestartPrepareGradients restart read forestOp copy sort entry)
        initial .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧
      out.regs 8 + ecG * limbs ≤ out.regs 4 ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      out.regs 6 + dynGraphSize nextVC nextEC ≤ out.regs 4 ∧
      out.regs 7 + nextEC * limbs ≤ out.regs 4 ∧
      out.regs 8 + nextEC * limbs ≤ out.regs 4 ∧
      ZeroFrom out.mem (out.regs 4) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 203 + prefixCost := by
  have hlenLive : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ heap := by
    intro e he
    have hcap : e < nextEC := hH.2.2.1 e he
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt hcap)
    rw [Nat.succ_mul] at hmul
    omega
  obtain ⟨out, c, hrun, ho6, ho7, _, ho8, hg, hl, hgrad, hzero, hlo, hhi, hkeep, hc⟩ :=
    prepareShiftReadoutGradients_runs (ω := ω) hcopy hsort hreadout ha hh hlimbs hz
      hgraphEnd hlistEnd hsortRoom hcount hw hforest hvalues hsub hgradEnd
      himpl hG hGEnd hvertices hH hHEnd hHE h6 h13 h50 h15 h16 h17
      nextLengths hlen hlenLive hwScan hspace hfit hfitScan
  refine ⟨out, prefixCost + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨st, prefixCost, c, hprefix, hrun, rfl⟩),
    ho6, ho7, ho8, hg, hl, hgrad, ho6.symm ▸ hHEnd.trans hlo, ho7.symm ▸ hlenEnd.trans hlo, ?_, hzero, hlo, hhi, hkeep, by omega⟩
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right limbs hcapacity) _).trans ho8

@[expose] def writesBelow (bound : ℕ) : Stmt → Bool
  | .assign r _ | .rand r | .call r _ _ => decide (r < bound)
  | .seq s t | .cond _ s t => writesBelow bound s && writesBelow bound t
  | .loop _ body => writesBelow bound body
  | _ => true

theorem runs_preserves_above {w bound r : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st out : State} {o : Outcome} {c : ℕ}
    (hr : bound ≤ r) (hb : writesBelow bound s = true)
    (h : Runs w p ω s st o out c) : out.regs r = st.regs r := by
  induction c using Nat.strong_induction_on generalizing s st out o with
  | h c ih =>
    cases s with
    | nop => exact congrArg (fun s : State => s.regs r) (runs_nop_iff.mp h).2.1
    | ret e =>
      obtain ⟨_, _, _, rfl, _⟩ := runs_ret_iff.mp h
      rfl
    | store a e =>
      obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h
      rfl
    | assign dest e =>
      obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp h
      have hd : dest < bound := of_decide_eq_true hb
      exact Function.update_of_ne (by omega) _ _
    | rand dest =>
      obtain ⟨_, rfl, _⟩ := runs_rand_iff.mp h
      have hd : dest < bound := of_decide_eq_true hb
      exact Function.update_of_ne (by omega) _ _
    | call dest f args =>
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp h
      have hd : dest < bound := of_decide_eq_true hb
      exact Function.update_of_ne (by omega) _ _
    | seq s t =>
      have hboth : writesBelow bound s = true ∧ writesBelow bound t = true :=
        Bool.and_eq_true_iff.mp hb
      rcases runs_seq_iff.mp h with ⟨_, _, hs, _, hc⟩ | ⟨mid, _, _, hs, ht, hc⟩
      · exact ih _ (by omega) hboth.1 hs
      · exact (ih _ (by omega) hboth.2 ht).trans (ih _ (by omega) hboth.1 hs)
    | cond e s t =>
      have hboth : writesBelow bound s = true ∧ writesBelow bound t = true :=
        Bool.and_eq_true_iff.mp hb
      obtain ⟨v, d, _, ht, hc⟩ := runs_cond_iff.mp h
      apply ih d (by omega) _ ht
      split <;> tauto
    | loop e body =>
      have hbody : writesBelow bound body = true := hb
      rcases runs_loop_iff.mp h with ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, ht, _, hc⟩ |
        ⟨mid, _, _, _, _, _, hs, ht, hc⟩
      · rfl
      · exact ih _ (by omega) hbody ht
      · exact (ih _ (by omega) hb ht).trans (ih _ (by omega) hbody hs)

/-- The Shift readout and traversal leave the descriptor addresses and
suffix index intact. These caller registers start at register 51. -/
theorem shiftRestartPrepareGradients_preserves_regs
    {w restart read forestOp copy sort entry r cost : ℕ}
    {p : Program} {st out : State} {ω : ℕ → Bool} (hr : 51 ≤ r)
    (h : Runs w p ω (shiftRestartPrepareGradients restart read forestOp copy sort entry)
      st .normal out cost) : out.regs r = st.regs r := by
  apply runs_preserves_above hr _ h
  rfl

/-- The Shift prefix leaves the caller's descriptor registers intact
even when no gradient traversal follows. -/
theorem shiftRestartGraphAndLengths_preserves_regs
    {w restart read forestOp r cost : ℕ} {p : Program} {st out : State} {ω : ℕ → Bool}
    (hr : 51 ≤ r)
    (h : Runs w p ω (shiftRestartGraphAndLengths restart read forestOp) st .normal out cost) :
    out.regs r = st.regs r := by
  apply runs_preserves_above hr _ h
  rfl

/-- The counter writes preserve the saved free-heap register. -/
theorem shiftLevelCounters_preserves_heap_slot
    {w cost : ℕ} {p : Program} {st out : State} {ω : ℕ → Bool}
    (h : Runs w p ω shiftLevelCounters st .normal out cost) :
    out.regs 59 = st.regs 59 := by
  apply runs_preserves_above (by decide : 59 ≤ 59) _ h
  rfl

end MinCostFlow.MinRatio
