module

public import MinCostFlow.MinRatio.ShiftForestSetup

/-!
# Scanning a queued parent

Reading the parent's adjacency head selects its incidence list. The
verified scan then discovers all neighbors and preserves the input tables.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- Open the parent adjacency list and run the concrete worklist scan. -/
theorem ForestWorklistAt.parent_runs
    {w a vc ec parent flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hparent : parent ∈ F.V)
    (hext : st.regs 30 = dgExtToIntBase a vc)
    (hhead : st.regs 31 = dgIncHeadBase a vc)
    (hgraphRoom : a + dynGraphSize vc ec ≤ 2 ^ w)
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
    (hroom : ∀ L : List ℕ, L.Nodup →
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) →
      st.regs 4 + 3 * limbs * L.length < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ (L : List ℕ),
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) →
      ∀ s seen i (hi : i < L.length),
      ForestWorklistAt s F g base flags queue vc h limbs precision read seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    ∃ out cost fresh, ∃ L : List ℕ, Runs w p ω (propagateForestParent entry) st .normal out cost ∧
      L.Nodup ∧ (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision read (names ++ fresh) ∧
      (∀ v, (∃ e ∈ F.E, (F.tail e = parent ∧ F.head e = v) ∨
        (F.head e = parent ∧ F.tail e = v)) → v ∈ (names ++ fresh).toFinset) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 3 * limbs * L.length ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ L.length * (129 * limbs + 209) + 11 := by
  obtain ⟨mid, L, hload, hl, hmembers, hcursor, hregs, hm, _⟩ :=
    loadForestIncidenceHead_runs (p := p) (ω := ω) hgraph hparent hp hext hhead hgraphRoom
  have hslot : st.mem (dgExtToIntBase a vc + parent) < vc := by
    obtain ⟨_, hcap, _, _, _, _, _, _, _, hmap, _⟩ := hgraph
    exact hcap _ (hmap parent hparent).1
  have hcursor' : mid.regs 29 = if 0 < L.length then L.getD 0 0 + 1 else 0 := by
    cases L <;> simpa using hcursor
  have hheap := hregs 4 (by decide)
  have hmid := hin.frame_incidence hm (fun r _ h29 _ _ _ _ => hregs r h29)
  obtain ⟨out, cost, fresh, hrun, hwork, hcovered, hg, hvalues', hz', htail, hlo, hhi,
    hkeep, hframe, hcost⟩ :=
    hmid.adjacency_runs (ω := ω) (hm.symm ▸ hgraph) hforest hmembers hslot (hm.symm ▸ hl) hcursor'
      ((hregs 27 (by decide)).trans hnext) ((hregs 33 (by decide)).trans ht)
      ((hregs 34 (by decide)).trans hc) ((hregs 35 (by decide)).trans hn)
      ((hregs 25 (by decide)).trans hp) hpVisited ((hregs 38 (by decide)).trans hgrad)
      ((hregs 3 (by decide)).trans hlimbs) ((hregs 22 (by decide)).trans hzPtr)
      (hm.symm ▸ hz) (by simpa only [hm, hheap] using hzero) (hm.symm ▸ hvalues)
      hsub himpl hgraphEnd hgradEnd hzEnd (by simpa only [hheap] using hroom L hl.1 hmembers)
      hw hpotEnd hflagsEnd (by simpa only [hheap] using hqEnd) (hfit L hmembers)
  refine ⟨out, 8 + cost + 1, fresh, L,
    runs_seq_iff.mpr (Or.inr ⟨mid, 8, cost, hload, hrun, rfl⟩),
    hl.1, hmembers, hwork, ?_, hg, hvalues', hz', htail, by omega, by omega, ?_,
    fun x hx => (hframe x hx).trans (congrFun hm x), by omega⟩
  · intro v hv
    exact hcovered ((mem_forestIncidenceChildren_iff hgraph.2.2.1 hmembers).mpr hv)
  · intro r hr h23 h24 h26 h28 h29 h32 h37 h41
    exact (hkeep r hr h23 h24 h26 h28 h29 h32 h37 h41).trans (hregs r h29)

/-- Finishing the current parent's adjacency scan allows the worklist to
advance its read index. The supplied transition only changes that index. -/
theorem ForestWorklistAt.finish_parent
    {st out : State} {F : MGraph} {g : ℕ → ℝ} {names fresh : List ℕ}
    {potential flags queue vc h limbs precision read : ℕ}
    (hin : ForestWorklistAt st F g potential flags queue vc h limbs precision read (names ++ fresh))
    (hr : read < names.length)
    (hneighbors : ∀ v, (∃ e ∈ F.E,
      (F.tail e = names[read] ∧ F.head e = v) ∨
        (F.head e = names[read] ∧ F.tail e = v)) → v ∈ (names ++ fresh).toFinset)
    (hidx : out.regs 40 = read + 1) (hm : out.mem = st.mem)
    (hregs : ∀ r, r ≠ 40 → out.regs r = st.regs r) :
    ForestWorklistAt out F g potential flags queue vc h limbs precision (read + 1) (names ++ fresh) := by
  obtain ⟨hp, hf, hq, _, hw, _, hnd, hsub, hlist, hflags, hpots, hscan, hz⟩ := hin
  have hr' : read < (names ++ fresh).length := by simp only [List.length_append]; omega
  have hscan' : ForestQueueScanned F (names ++ fresh) (read + 1) :=
    hscan.advance hr' (by simpa only [List.getElem_append_left hr] using hneighbors)
  exact ⟨(hregs 20 (by decide)).trans hp, (hregs 36 (by decide)).trans hf,
    (hregs 39 (by decide)).trans hq, hidx, (hregs 41 (by decide)).trans hw,
    Nat.succ_le_of_lt hr', hnd, hsub, hm.symm ▸ hlist, hm.symm ▸ hflags,
    hm.symm ▸ hpots, hscan', hm.symm ▸ hz⟩

/-- The read index advances only after the parent's neighbors are present. -/
theorem ForestWorklistAt.finish_parent_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {F : MGraph} {g : ℕ → ℝ}
    {names fresh : List ℕ} {potential flags queue vc h limbs precision read : ℕ}
    (hin : ForestWorklistAt st F g potential flags queue vc h limbs precision read (names ++ fresh))
    (hr : read < names.length) (hroom : names.length < 2 ^ w)
    (hneighbors : ∀ v, (∃ e ∈ F.E,
      (F.tail e = names[read] ∧ F.head e = v) ∨
        (F.head e = names[read] ∧ F.tail e = v)) → v ∈ (names ++ fresh).toFinset) :
    ∃ out, Runs w p ω advanceForestRead st .normal out 4 ∧
      ForestWorklistAt out F g potential flags queue vc h limbs precision (read + 1) (names ++ fresh) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 40 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 40 (read + 1) }
  have hidx : st.regs 40 = read := hin.2.2.2.1
  have hnext : read + 1 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt hr) hroom
  have hword : 1 < 2 ^ w := by omega
  have hrun : Runs w p ω advanceForestRead st .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hidx, hword, hnext], rfl, rfl, rfl⟩
  have hregs (r : ℕ) (hr : r ≠ 40) : out.regs r = st.regs r := Function.update_of_ne hr _ _
  exact ⟨out, hrun, hin.finish_parent hr hneighbors (by simp [out]) rfl hregs, rfl, hregs, rfl⟩

/-- A complete worklist step discovers the parent's neighbors and advances
the processed prefix, preserving the inputs for the next parent. -/
theorem ForestWorklistAt.scan_queue_parent_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hi : read < names.length)
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
    (hroom : ∀ L : List ℕ, L.Nodup →
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) →
      st.regs 4 + 3 * limbs * L.length < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ (L : List ℕ),
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) →
      ∀ s seen i (hi : i < L.length),
      ForestWorklistAt s F g base flags queue vc h limbs precision read seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + names[read] * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    ∃ out cost fresh, ∃ L : List ℕ, Runs w p ω (scanForestQueueParent entry) st .normal out cost ∧
      L.Nodup ∧ (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision (read + 1) (names ++ fresh) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 3 * limbs * L.length ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 25 → r ≠ 40 → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ L.length * (129 * limbs + 209) + 22 := by
  have hq := hin.2.2.1
  have hr := hin.2.2.2.1
  have hnames := hin.2.2.2.2.2.2.2.1
  have hlist := hin.2.2.2.2.2.2.2.2.1
  have hmem : names[read] ∈ names.toFinset := List.mem_toFinset.mpr (List.getElem_mem hi)
  have hv := hnames hmem
  have hvc := (hin.indices hgraph.2.1).2.2
  have hlen : names.length ≤ vc := hin.2.2.2.2.1 ▸ hvc
  obtain ⟨initialList, initialLayout, initialMembers⟩ := dynGraphAt_incident hgraph hv
  have heapRoom := hroom initialList initialLayout.1 initialMembers
  have hword : queue + read < 2 ^ w := by omega
  let pre := { st with regs := Function.update st.regs 25 names[read] }
  have hload : Runs w p ω (.assign 25 (.load (.bin .add (.reg 39) (.reg 40))))
      st .normal pre 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hq, hr, hword, hlist read hi],
      rfl, rfl, rfl⟩
  have hregs (r : ℕ) (hne : r ≠ 25) : pre.regs r = st.regs r := Function.update_of_ne hne _ _
  have hpre : ForestWorklistAt pre F g base flags queue vc h limbs precision read names := by
    simpa [ForestWorklistAt, pre, Function.update_of_ne] using hin
  obtain ⟨mid, c, fresh, L, hscan, hnd, hmembers, hwork, hneighbors, hg, hgv, hz', ht',
    hlo, hhi, hkeep, hframe, hcost⟩ :=
    hpre.parent_runs (ω := ω) hgraph hforest hv (by simpa [pre] using hext)
      (by simpa [pre] using hhead) hgraphRoom (by simpa [pre] using hnext)
      (by simpa [pre] using ht) (by simpa [pre] using hc) (by simpa [pre] using hn)
      (by simp [pre]) hmem (by simpa [pre] using hgrad) (by simpa [pre] using hlimbs)
      (by simpa [pre] using hzPtr) hz (by simpa [pre] using hzero) hvalues hsub himpl
      hgraphEnd hgradEnd hzEnd (by simpa [pre] using hroom) hw hpotEnd hflagsEnd
      (by simpa [pre] using hqEnd) hfit
  obtain ⟨out, hinc, hout, hm, houtRegs, _⟩ :=
    hwork.finish_parent_runs (w := w) (p := p) (ω := ω) hi (by omega) hneighbors
  refine ⟨out, 5 + (c + 4 + 1) + 1, fresh, L,
    runs_seq_iff.mpr (Or.inr ⟨pre, 5, c + 4 + 1, hload,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hscan, hinc, rfl⟩), rfl⟩),
    hnd, hmembers, hout, hm.symm ▸ hg, hm.symm ▸ hgv, hm.symm ▸ hz', ?_, ?_, ?_, ?_, fun x hx => (congrFun hm x).trans (hframe x hx), by omega⟩
  · rwa [hm, houtRegs 4 (by decide)]
  · simpa only [houtRegs 4 (by decide), hregs 4 (by decide)] using hlo
  · simpa only [houtRegs 4 (by decide), hregs 4 (by decide)] using hhi
  · intro r hr h25 h40 h23 h24 h26 h28 h29 h32 h37 h41
    exact (houtRegs r h40).trans ((hkeep r hr h23 h24 h26 h28 h29 h32 h37 h41).trans (hregs r h25))

/-- Each tail contributes an even incidence and each head an odd one.
The duplicate-free list therefore has length equal to the parent's degree. -/
theorem forestIncidence_length_eq_degree {F : MGraph} {ec parent : ℕ}
    {L : List ℕ} (hcap : ∀ e ∈ F.E, e < ec) (hnd : L.Nodup)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) :
    L.length = F.deg parent := by
  let tails := F.E.filter fun e => F.tail e = parent
  let heads := F.E.filter fun e => F.head e = parent
  have heq : L.toFinset = tails.image (fun e => 2 * e) ∪ heads.image (fun e => 2 * e + 1) := by
    ext j
    simp only [List.mem_toFinset, hmembers, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, tails, heads]
    constructor
    · rintro ⟨_, he, hp⟩
      by_cases hj : j % 2 = 0
      · exact Or.inl ⟨j / 2, ⟨he, by simpa only [hj, ↓reduceIte] using hp⟩, by omega⟩
      · exact Or.inr ⟨j / 2, ⟨he, by simpa only [hj, ↓reduceIte] using hp⟩, by omega⟩
    · rintro (⟨e, ⟨he, hp⟩, rfl⟩ | ⟨e, ⟨he, hp⟩, rfl⟩)
      · have hlt := hcap e he
        refine ⟨by omega, by simpa using he, ?_⟩
        simpa only [show 2 * e / 2 = e by omega, show 2 * e % 2 = 0 by omega, ↓reduceIte] using hp
      · have hlt := hcap e he
        have hdiv : (2 * e + 1) / 2 = e := by omega
        refine ⟨by omega, by simpa only [hdiv] using he, ?_⟩
        simpa only [hdiv, show (2 * e + 1) % 2 ≠ 0 by omega, ↓reduceIte] using hp
  rw [← List.toFinset_card_of_nodup hnd, heq, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun x y hxy => by omega),
        Finset.card_image_of_injective _ (fun x y hxy => by omega)]
    rfl
  · rw [Finset.disjoint_left]
    intro j ht hh
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e', _, h⟩ := Finset.mem_image.mp hh
    omega

/-- Charge a complete worklist step by the degree of its queued parent. -/
theorem ForestWorklistAt.scan_queue_parent_degree_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hi : read < names.length)
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
    (hroom : st.regs 4 + 3 * limbs * F.deg names[read] < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ (L : List ℕ),
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) →
      ∀ s seen i (hi : i < L.length),
      ForestWorklistAt s F g base flags queue vc h limbs precision read seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + names[read] * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    ∃ out cost fresh, Runs w p ω (scanForestQueueParent entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision (read + 1) (names ++ fresh) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 3 * limbs * F.deg names[read] ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 25 → r ≠ 40 → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ F.deg names[read] * (129 * limbs + 209) + 22 := by
  have hroom' (L : List ℕ) (hl : L.Nodup)
      (hm : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) :
      st.regs 4 + 3 * limbs * L.length < 2 ^ w := by
    rw [forestIncidence_length_eq_degree hgraph.2.2.1 hl hm]
    exact hroom
  obtain ⟨out, cost, fresh, L, hrun, hnd, hmem, hwork, hg, hgr, hz', ht', hlo, hhi, hregs, hframe, hcost⟩ :=
    hin.scan_queue_parent_runs (ω := ω) hgraph hforest hi hext hhead hgraphRoom hnext ht hc hn
      hgrad hlimbs hzPtr hz hzero hvalues hsub himpl hgraphEnd hgradEnd hzEnd hroom'
      hw hpotEnd hflagsEnd hqEnd hfit
  have hlen := forestIncidence_length_eq_degree hgraph.2.2.1 hnd hmem
  exact ⟨out, cost, fresh, hrun, hwork, hg, hgr, hz', ht', hlo,
    hlen ▸ hhi, hregs, hframe, hlen ▸ hcost⟩

/-- Scanning the next distinct parent removes its degree from the remaining
volume, including when the queue grows by appending new discoveries. -/
theorem forestWorklist_remaining_volume_step {F : MGraph} {names fresh : List ℕ}
    {read : ℕ} (hr : read < names.length) (hnd : names.Nodup)
    (hsub : names.toFinset ⊆ F.V) :
    F.vol (F.V \ (names.take read).toFinset) =
      F.deg names[read] + F.vol (F.V \ ((names ++ fresh).take (read + 1)).toFinset) := by
  classical
  have hmem : names[read] ∈ F.V := hsub (List.mem_toFinset.mpr (List.getElem_mem hr))
  have hnot : names[read] ∉ (names.take read).toFinset := by
    intro hm
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem (List.mem_toFinset.mp hm)
    have hj' : j < read := by simp [List.length_take] at hj; omega
    have hjl : j < names.length := by omega
    have hne := List.pairwise_iff_getElem.mp hnd j read hjl hr hj'
    exact hne (by simpa using he)
  let remaining := F.V \ (names.take read).toFinset
  have hparent : names[read] ∈ remaining := Finset.mem_sdiff.mpr ⟨hmem, hnot⟩
  have hrest : F.V \ ((names ++ fresh).take (read + 1)).toFinset =
      remaining.erase names[read] := by
    rw [List.take_append_of_le_length (Nat.succ_le_of_lt hr),
      List.take_succ_eq_append_getElem hr]
    ext v
    simp only [remaining, Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset,
      List.mem_append, List.mem_singleton]
    tauto
  rw [hrest]
  exact (Finset.add_sum_erase _ _ hparent).symm

/-- Reserving scratch by remaining incidence volume suffices for one
parent and leaves the corresponding allowance for the rest of the queue. -/
theorem ForestWorklistAt.scan_queue_parent_volume_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hi : read < names.length)
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
    (hroom : st.regs 4 + 3 * limbs * F.vol (F.V \ (names.take read).toFinset) < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ (L : List ℕ),
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = names[read]) →
      ∀ s seen i (hi : i < L.length),
      ForestWorklistAt s F g base flags queue vc h limbs precision read seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + (L[i] / 2) * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + names[read] * limbs) h limbs +
        ((if L[i] % 2 ≠ 0 then value else 0) - (if L[i] % 2 ≠ 0 then 0 else value)))) :
    ∃ out cost fresh, Runs w p ω (scanForestQueueParent entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision (read + 1) (names ++ fresh) ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 3 * limbs * F.deg names[read] ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ ((names ++ fresh).take (read + 1)).toFinset) < 2 ^ w ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 25 → r ≠ 40 → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 28 → r ≠ 29 →
        r ≠ 32 → r ≠ 37 → r ≠ 41 → out.regs r = st.regs r) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost ≤ F.deg names[read] * (129 * limbs + 209) + 22 := by
  have hnd := hin.2.2.2.2.2.2.1
  have hsubVertices := hin.2.2.2.2.2.2.2.1
  have hvolume := forestWorklist_remaining_volume_step (F := F) (fresh := []) hi hnd hsubVertices
  have hroom' : st.regs 4 + 3 * limbs * F.deg names[read] < 2 ^ w := by
    rw [hvolume, Nat.mul_add] at hroom
    omega
  obtain ⟨out, cost, fresh, hr, hwork, hg, hgr, hz', htail, hlo, hhi, hregs, hframe, hcost⟩ :=
    hin.scan_queue_parent_degree_runs (ω := ω) hgraph hforest hi hext hhead hgraphRoom
      hnext ht hc hn hgrad hlimbs hzPtr hz hzero hvalues hsub himpl hgraphEnd hgradEnd hzEnd
      hroom' hw hpotEnd hflagsEnd hqEnd hfit
  refine ⟨out, cost, fresh, hr, hwork, hg, hgr, hz', htail, hlo, hhi, ?_, hregs, hframe, hcost⟩
  rw [forestWorklist_remaining_volume_step (fresh := fresh) hi hnd hsubVertices, Nat.mul_add] at hroom
  omega

/-- Drain a concrete worklist, charging incidence volume and the number of
parents actually processed. Arithmetic fit is required for signed additions. -/
theorem ForestWorklistAt.queue_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision read : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestWorklistAt st F g base flags queue vc h limbs precision read names)
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
    (hroom : st.regs 4 + 3 * limbs * F.vol (F.V \ (names.take read).toFinset) < 2 ^ w) (hw : 2 < 2 ^ w)
    (hpotEnd : base + vc * limbs ≤ zeroPtr) (hflagsEnd : flags + vc ≤ queue)
    (hqEnd : queue + vc ≤ st.regs 4)
    (hfit : ∀ parent ∈ F.V, ∀ e ∈ F.E, ∀ direction : Bool, ∀ s seen r,
      ForestWorklistAt s F g base flags queue vc h limbs precision r seen →
      EdgeValuesAt s.mem gradients h limbs precision edges g →
      let value := Num.intVal s.mem (gradients + e * limbs) h limbs
      Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
        ((if direction then value else 0) - (if direction then 0 else value)))) :
    ∃ out cost fresh r, Runs w p ω (propagateForestQueue entry) st .normal out cost ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision r (names ++ fresh) ∧
      r = (names ++ fresh).length ∧ read ≤ r ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      queue + vc ≤ out.regs 4 ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ ((names ++ fresh).take r).toFinset) < 2 ^ w ∧
      (∀ k, k = 3 ∨ 6 ≤ k → k ≠ 25 → k ≠ 40 → k ≠ 23 → k ≠ 24 →
        k ≠ 26 → k ≠ 28 → k ≠ 29 → k ≠ 32 → k ≠ 37 → k ≠ 41 → out.regs k = st.regs k) ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ ((names ++ fresh).take r).toFinset) ≤
        st.regs 4 + 3 * limbs * F.vol (F.V \ (names.take read).toFinset) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost + F.vol (F.V \ ((names ++ fresh).take r).toFinset) * (129 * limbs + 209) ≤
        F.vol (F.V \ (names.take read).toFinset) * (129 * limbs + 209) + 26 * (r - read) + 4 := by
  obtain ⟨hr, hle, hcap⟩ := hin.indices hgraph.2.1
  have hwrite := hin.2.2.2.2.1
  by_cases hi : read < names.length
  · have hv : names[read] ∈ F.V :=
      hin.2.2.2.2.2.2.2.1 (List.mem_toFinset.mpr (List.getElem_mem hi))
    obtain ⟨mid, c, added, hrun, hmid, hg, hgv, hz', htail, hlo, hhi, hroom', hregs, hframe, hcost⟩ :=
      hin.scan_queue_parent_volume_runs (ω := ω) hgraph hforest hi hext hhead hgraphRoom
        hnext ht hc hn hgrad hlimbs hzPtr hz hzero hvalues hsub himpl hgraphEnd hgradEnd hzEnd
        hroom hw hpotEnd hflagsEnd hqEnd (by
          intro L hm s seen i hi' ht hv'
          have he := ((hm L[i]).mp (List.getElem_mem hi')).2.1
          simpa using hfit names[read] hv (L[i] / 2) he (decide (L[i] % 2 ≠ 0)) s seen read ht hv')
    obtain ⟨out, d, rest, r, hloop, hout, hend, hread, hg', hgv', hz'', ht', hqe,
      hroom'', hkeep, hscratch, hprefix, hd⟩ :=
      hmid.queue_runs (ω := ω) hg hforest
        ((hregs 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hext)
        ((hregs 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hhead)
        hgraphRoom
        ((hregs 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnext)
        ((hregs 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht)
        ((hregs 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
        ((hregs 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
        ((hregs 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgrad)
        ((hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlimbs)
        ((hregs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzPtr)
        hz' htail hgv hsub himpl hgraphEnd hgradEnd hzEnd hroom' hw hpotEnd hflagsEnd
        (hqEnd.trans hlo) hfit
    have htest : Expr.eval w st (.bin .lt (.reg 40) (.reg 41)) = some 1 := by
      simp [Expr.eval, BinOp.eval, hr, hwrite, hi, show 1 < 2 ^ w by omega]
    refine ⟨out, c + 4 + d, added ++ rest, r, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨1, mid, c, d, htest, by decide, hrun, hloop, by simp [Expr.size]; omega⟩)),
      by simpa only [List.append_assoc] using hout, by simpa only [List.append_assoc] using hend,
      by omega, hg', hgv', hz'', ht', hqe, by simpa only [List.append_assoc] using hroom'', ?_, ?_, fun x hx => (hprefix x hx).trans (hframe x hx), ?_⟩
    · intro k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41
      exact (hkeep k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41).trans
        (hregs k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41)
    · simp only [← List.append_assoc]
      rw [forestWorklist_remaining_volume_step (fresh := added) hi hin.2.2.2.2.2.2.1
        hin.2.2.2.2.2.2.2.1, Nat.mul_add]
      omega
    · simp only [← List.append_assoc]
      rw [forestWorklist_remaining_volume_step (fresh := added) hi hin.2.2.2.2.2.2.1
        hin.2.2.2.2.2.2.2.1, Nat.add_mul]
      have hs : r - read = (r - (read + 1)) + 1 := by omega
      rw [hs]
      simp only [Nat.mul_add, Nat.mul_one] at hcost hd ⊢
      omega
  · have he : read = names.length := by omega
    have htest : Expr.eval w st (.bin .lt (.reg 40) (.reg 41)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hr, hwrite, he]
    exact ⟨st, 4, [], read, runs_loop_iff.mpr (Or.inl ⟨htest, rfl, rfl, rfl⟩),
      by simpa using hin, by simpa using he, le_rfl, hgraph, hvalues, hz, hzero, hqEnd,
      by simpa using hroom, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, by simp, fun _ _ => rfl, by simp [Nat.add_comm]⟩
termination_by vc - read
decreasing_by omega

/-- Seed the fresh canonical root and drain its concrete worklist.
The previously visited set determines the available incidence volume. -/
theorem ForestRootScanAt.component_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision sortedBase i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i < names.length) (hnames : names.toFinset = F.V) (horder : names.Pairwise (· ≤ ·))
    (hfresh : st.mem (flags + names[i]) = 0) (hv : st.regs 26 = names[i])
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
    ∃ out cost old fresh r, Runs w p ω (propagateForestComponent entry) st .normal out cost ∧
      st.regs 40 = old.length ∧
      ForestWorklistAt out F g base flags queue vc h limbs precision r (old ++ [names[i]] ++ fresh) ∧
      r = (old ++ [names[i]] ++ fresh).length ∧ old.length ≤ r ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      queue + vc ≤ out.regs 4 ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ (old ++ [names[i]] ++ fresh).toFinset) < 2 ^ w ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ (old ++ [names[i]] ++ fresh).toFinset) ≤
        st.regs 4 + 3 * limbs * F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      (∀ k, k = 3 ∨ 6 ≤ k → k ≠ 25 → k ≠ 40 → k ≠ 23 → k ≠ 24 →
        k ≠ 26 → k ≠ 28 → k ≠ 29 → k ≠ 32 → k ≠ 37 → k ≠ 41 → out.regs k = st.regs k) ∧
      (∀ v ∈ F.V, st.mem (flags + v) = 1 → v ∈ (old ++ [names[i]] ++ fresh).toFinset) ∧
      cost + F.vol (F.V \ (old ++ [names[i]] ++ fresh).toFinset) * (129 * limbs + 209) ≤
        F.vol (F.V \ (Finset.filter (fun v => st.mem (flags + v) = 1) F.V)) *
          (129 * limbs + 209) + 26 * (r - old.length) + 21 := by
  have hword : queue + vc < 2 ^ w := by omega
  obtain ⟨mid, old, hseed, hread, hwork, _, hmem, hregs⟩ :=
    hin.seed_worklist_runs (p := p) (ω := ω) hi hforest hnames horder hgraph.2.1 hfresh hv
      hword hsortedEnd (by omega) hflagsEnd
  have hvCap := hgraph.2.1 names[i] (hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi))
  have hprior : (F.V.filter fun v => st.mem (flags + v) = 1) = old.toFinset := by
    obtain ⟨_, _, _, _, _, _, _, seen, hnd, hsub, hr, _, hlist, hflags, _⟩ := hin
    have hseedList := hwork.2.2.2.2.2.2.2.2.1
    have heq : seen = old := by
      apply List.ext_getElem
      · omega
      · intro j hj hj'
        have hcap := (hwork.indices hgraph.2.1).2.2
        have hw' := hwork.2.2.2.2.1
        have hlen : (old ++ [names[i]]).length ≤ vc := hw'.symm ▸ hcap
        have hj'' : j < (old ++ [names[i]]).length := by simp; omega
        calc
          seen[j] = st.mem (queue + j) := (hlist j hj).symm
          _ = mid.mem (queue + j) := (hmem _ (by omega) (by omega)).symm
          _ = (old ++ [names[i]])[j] := hseedList j hj''
          _ = old[j] := List.getElem_append_left hj'
    subst seen
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvmark⟩
      by_contra hn'
      rw [hflags v (hgraph.2.1 v hv), ite_eq_right hn'] at hvmark
      contradiction
    · intro hv
      exact ⟨hsub hv, by rw [hflags v (hgraph.2.1 v (hsub hv)), ite_eq_left hv]⟩
  have hmemBase (x : ℕ) (hx : x < base) : mid.mem x = st.mem x :=
    hmem x (by omega) (by omega)
  have hg := hgraph.of_agree (fun x _ hx => hmemBase x (by omega))
  have hgrad' := hvalues.congr (fun e he j hj =>
    hmemBase _ (by have := hgradEnd e he; omega))
  have hz' := hz.congr (fun j hj => hmem _ (by omega) (by omega))
  have hheap := hregs 4 (by decide)
  have htail : ZeroFrom mid.mem (mid.regs 4) := by
    intro x hx
    have hcap := (hwork.indices hgraph.2.1).2.2
    have hw' := hwork.2.2.2.2.1
    have hlen : (old ++ [names[i]]).length ≤ vc := hw'.symm ▸ hcap
    simp only [List.length_append, List.length_singleton] at hlen
    exact (hmem x (by omega) (by omega)).trans (hzero x (by omega))
  have hpref : ((old ++ [names[i]]).take old.length).toFinset =
      (F.V.filter fun v => st.mem (flags + v) = 1) := by
    rw [List.take_append_of_le_length le_rfl, List.take_length, hprior]
  obtain ⟨out, c, fresh, r, hrun, hout, hend, hlo, hgraph', hvalues', hzero', htail', hqe,
    hspace, hkeep, hscratch, hprefix, hcost⟩ :=
    hwork.queue_runs (ω := ω) hg hforest ((hregs 30 (by decide)).trans hext)
      ((hregs 31 (by decide)).trans hhead) hgraphRoom ((hregs 27 (by decide)).trans hnext)
      ((hregs 33 (by decide)).trans ht) ((hregs 34 (by decide)).trans hc)
      ((hregs 35 (by decide)).trans hn) ((hregs 38 (by decide)).trans hgrad)
      ((hregs 3 (by decide)).trans hlimbs) ((hregs 22 (by decide)).trans hzPtr)
      hz' htail hgrad' hsub himpl hgraphEnd hgradEnd hzEnd
      (by simpa only [hheap, hpref] using hroom) hw hpotEnd hflagsEnd
      (by simpa only [hheap] using hqEnd) hfit
  rw [hpref, hend, List.take_length] at hcost
  refine ⟨out, c + 17, old, fresh, r, runs_seq_iff.mpr (Or.inr ⟨mid, 16, c, hseed, hrun, by omega⟩),
    hread, hout, hend, hlo, hgraph', hvalues', hzero', htail', hqe,
    by simpa only [hend, List.take_length] using hspace, by simpa only [hend, List.take_length, hpref, hheap] using hscratch, fun x hx => (hprefix x hx).trans (hmemBase x hx), ?_, ?_, by omega⟩
  · intro k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41
    exact (hkeep k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41).trans (hregs k h41)
  · intro v hv hm
    have hold : v ∈ old.toFinset := hprior ▸ Finset.mem_filter.mpr ⟨hv, hm⟩
    exact List.mem_toFinset.mpr (List.mem_append_left _
      (List.mem_append_left _ (List.mem_toFinset.mp hold)))

/-- The drained component establishes the next ordered-root invariant.
The caller advances only the candidate index after the component returns. -/
theorem ForestRootScanAt.finish_component
    {st mid out : State} {F : MGraph} {g : ℕ → ℝ} {names old fresh : List ℕ}
    {sortedBase base flags queue vc h limbs precision i r : ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i < names.length) (hcap : ∀ v ∈ F.V, v < vc)
    (hwork : ForestWorklistAt mid F g base flags queue vc h limbs precision r
      (old ++ [names[i]] ++ fresh))
    (hend : r = (old ++ [names[i]] ++ fresh).length)
    (hvisited : ∀ v ∈ F.V, st.mem (flags + v) = 1 → v ∈ (old ++ [names[i]] ++ fresh).toFinset)
    (hsortedEnd : sortedBase + names.length ≤ base)
    (hprefix : ∀ x < base, mid.mem x = st.mem x)
    (hcount : mid.regs 46 = st.regs 46) (harray : mid.regs 48 = st.regs 48)
    (hindex : out.regs 44 = i + 1) (hm : out.mem = mid.mem)
    (hregs : ∀ k, k ≠ 44 → out.regs k = mid.regs k) :
    ForestRootScanAt out F g sortedBase base flags queue vc h limbs precision (i + 1) names := by
  have hinitial := hin
  obtain ⟨_, hn, hs, hl, _, _, _, seen, _, hsub, _, _, _, hflags, _⟩ := hin
  obtain ⟨hp, hf, hq, hr, hw, _, hnd, hs', hlist, hflags', hpots, hscan, hzero⟩ := hwork
  have hmarked (v : ℕ) (hv : v < vc) (hm : st.mem (flags + v) = 1) :
      v ∈ (old ++ [names[i]] ++ fresh).toFinset := by
    have hseen : v ∈ seen.toFinset := by
      by_contra hnot
      rw [hflags v hv, ite_eq_right hnot] at hm
      contradiction
    exact hvisited v (hsub hseen) hm
  have hsorted : ListAt out.mem sortedBase names := by
    intro j hj
    rw [hm, hprefix _ (by omega)]
    exact hl j hj
  refine hinitial.of_exhausted_component hi (by simp [List.toFinset_append]) hmarked hcap hindex
    ((hregs 46 (by decide)).trans (hcount.trans hn))
    ((hregs 48 (by decide)).trans (harray.trans hs)) hsorted
    ((hregs 20 (by decide)).trans hp) ((hregs 36 (by decide)).trans hf)
    ((hregs 39 (by decide)).trans hq) hnd hs'
    ((hregs 40 (by decide)).trans (hr.trans hend)) ((hregs 41 (by decide)).trans hw)
    (hm.symm ▸ hlist) (hm.symm ▸ hflags') (hm.symm ▸ hpots) ?_ (hm.symm ▸ hzero)
  simpa only [ForestQueueScanned, hregs 40 (by decide), hr] using hscan

/-- A fresh candidate starts its component and then advances the compact
scan. The cost carries forward the component's unused incidence volume. -/
theorem ForestRootScanAt.fresh_step_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision sortedBase i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i < names.length) (hnames : names.toFinset = F.V) (horder : names.Pairwise (· ≤ ·))
    (hfresh : st.mem (flags + names[i]) = 0)
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
    ∃ out cost, ∃ seen : List ℕ, ∃ r, Runs w p ω (propagateOrderedForestVertex entry) st .normal out cost ∧
      ForestRootScanAt out F g sortedBase base flags queue vc h limbs precision (i + 1) names ∧
      r = seen.length ∧ st.regs 40 ≤ r ∧ out.regs 40 = r ∧
      DynGraphAt out.mem a vc ec F ∧ EdgeValuesAt out.mem gradients h limbs precision edges g ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem (out.regs 4) ∧
      queue + vc ≤ out.regs 4 ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ seen.toFinset) < 2 ^ w ∧
      (F.V.filter fun v => out.mem (flags + v) = 1) = seen.toFinset ∧
      (∀ k, k = 3 ∨ 6 ≤ k → k ≠ 25 → k ≠ 40 → k ≠ 23 → k ≠ 24 →
        k ≠ 26 → k ≠ 28 → k ≠ 29 → k ≠ 32 → k ≠ 37 → k ≠ 41 → k ≠ 44 →
        out.regs k = st.regs k) ∧
      out.regs 4 + 3 * limbs * F.vol (F.V \ seen.toFinset) ≤
        st.regs 4 + 3 * limbs * F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧
      cost + F.vol (F.V \ seen.toFinset) * (129 * limbs + 209) ≤
        F.vol (F.V \ (F.V.filter fun v => st.mem (flags + v) = 1)) *
          (129 * limbs + 209) + 26 * (r - st.regs 40) + 40 := by
  have hiReg := hin.1
  have hs := hin.2.2.1
  have hl := hin.2.2.2.1
  obtain ⟨pre, hload, hname, hloadRegs, hloadMem, _⟩ :=
    loadOrderedForestVertex_runs (p := p) (ω := ω) hl hi hs hiReg hsortedRoom.le
  have hactive : names[i] ∈ F.V := hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
  have hvc := hgraph.2.1 _ hactive
  have hflagsRoom : flags + vc ≤ 2 ^ w := by omega
  have ⟨_, _, _, _, _, hf, _, visited, _, _, _, _, _, hflags, _⟩ := hin
  have hfresh' : names[i] ∉ visited.toFinset := by
    intro hm
    rw [hflags _ hvc, ite_eq_left hm] at hfresh
    contradiction
  obtain ⟨input, hmem, _, htestRegs, _, _, hdispatch⟩ :=
    visitFreshForestChild_runs (p := p) (ω := ω) (action := propagateForestComponent entry)
      (hloadMem.symm ▸ hflags) ((hloadRegs 36 (by decide)).trans hf) hname hvc hflagsRoom
  have hm := hmem.trans hloadMem
  have keep (k : ℕ) (h26 : k ≠ 26) (h37 : k ≠ 37) : input.regs k = st.regs k :=
    (htestRegs k h37).trans (hloadRegs k h26)
  have hin' : ForestRootScanAt input F g sortedBase base flags queue vc h limbs precision i names := by
    obtain ⟨hidx, hcount, hs, hl, hb, hf, hq, old, hnd, hsub', hr, hw', hlist, hflags', hpot,
      hpref, hclosed, hz'⟩ := hin
    exact ⟨(keep 44 (by decide) (by decide)).trans hidx,
      (keep 46 (by decide) (by decide)).trans hcount, (keep 48 (by decide) (by decide)).trans hs,
      hm.symm ▸ hl, (keep 20 (by decide) (by decide)).trans hb,
      (keep 36 (by decide) (by decide)).trans hf, (keep 39 (by decide) (by decide)).trans hq,
      old, hnd, hsub', (keep 40 (by decide) (by decide)).trans hr,
      (keep 41 (by decide) (by decide)).trans hw', hm.symm ▸ hlist, hm.symm ▸ hflags',
      hm.symm ▸ hpot, hpref, hclosed, hm.symm ▸ hz'⟩
  have hheap := keep 4 (by decide) (by decide)
  obtain ⟨mid, c, old, fresh, r, hrun, hread, hwork, hend, hlo, hg, hgv, hz', htail, hqe,
    hspace, hscratch, hprefix, hregs, hvisited, hcost⟩ :=
    hin'.component_runs (ω := ω) hi hnames horder (by rw [hm]; exact hfresh)
      ((htestRegs 26 (by decide)).trans hname) hsortedEnd (hm.symm ▸ hgraph) hforest
      ((keep 30 (by decide) (by decide)).trans hext) ((keep 31 (by decide) (by decide)).trans hhead)
      hgraphRoom ((keep 27 (by decide) (by decide)).trans hnext)
      ((keep 33 (by decide) (by decide)).trans ht) ((keep 34 (by decide) (by decide)).trans hc)
      ((keep 35 (by decide) (by decide)).trans hn) ((keep 38 (by decide) (by decide)).trans hgrad)
      ((keep 3 (by decide) (by decide)).trans hlimbs) ((keep 22 (by decide) (by decide)).trans hzPtr)
      (hm.symm ▸ hz) (by rw [hm, hheap]; exact hzero) (hm.symm ▸ hvalues) hsub himpl hgraphEnd
      hgradEnd hzEnd (by simpa only [hm, hheap] using hroom) hw hpotEnd hflagsEnd (hheap.symm ▸ hqEnd) hfit
  have preserve (k : ℕ) (hk : k = 3 ∨ 6 ≤ k) (h25 : k ≠ 25) (h40 : k ≠ 40)
      (h23 : k ≠ 23) (h24 : k ≠ 24) (h26 : k ≠ 26) (h28 : k ≠ 28) (h29 : k ≠ 29)
      (h32 : k ≠ 32) (h37 : k ≠ 37) (h41 : k ≠ 41) : mid.regs k = st.regs k :=
    (hregs k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41).trans (keep k h26 h37)
  have hidx := (preserve 44 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hiReg
  let out := { mid with regs := Function.update mid.regs 44 (i + 1) }
  have hlast : Runs w p ω (.assign 44 (.bin .add (.reg 44) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hidx, show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have houtRegs (k : ℕ) (hk : k ≠ 44) : out.regs k = mid.regs k := Function.update_of_ne hk _ _
  have hout := hin.finish_component hi hgraph.2.1 hwork hend
    (by simpa only [hm] using hvisited) hsortedEnd (fun x hx => (hprefix x hx).trans (congrFun hm x))
    (preserve 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
    (preserve 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
    (show out.regs 44 = i + 1 by simp [out]) rfl houtRegs
  have hseen := hwork.2.2.2.2.2.2.2.1
  have hmark := hwork.2.2.2.2.2.2.2.2.2.1
  refine ⟨out, c + 19, old ++ [names[i]] ++ fresh, r,
    runs_seq_iff.mpr (Or.inr ⟨pre, 5, c + 8 + 4 + 1, hload,
      runs_seq_iff.mpr (Or.inr ⟨mid, c + 8, 4, hdispatch hfresh' hrun, hlast, rfl⟩), by omega⟩),
    hout, hend, by rw [← keep 40 (by decide) (by decide), hread]; exact hlo,
    by rw [houtRegs 40 (by decide)]; exact hwork.2.2.2.1,
    hg, hgv, hz', by simpa only [houtRegs 4 (by decide)] using htail,
    by simpa only [houtRegs 4 (by decide)] using hqe,
    by simpa only [houtRegs 4 (by decide)] using hspace, ?_,
    fun k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41 h44 =>
      (houtRegs k h44).trans (preserve k hk h25 h40 h23 h24 h26 h28 h29 h32 h37 h41),
    by simpa only [houtRegs 4 (by decide), hm, hheap] using hscratch,
    fun x hx => (hprefix x hx).trans (congrFun hm x), ?_⟩
  · ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvmark⟩
      by_contra hnot
      rw [show out.mem = mid.mem from rfl, hmark v (hgraph.2.1 v hv), ite_eq_right hnot] at hvmark
      contradiction
    · intro hv
      exact ⟨hseen hv, by rw [show out.mem = mid.mem from rfl,
        hmark v (hgraph.2.1 v (hseen hv)), ite_eq_left hv]⟩
  · rw [keep 40 (by decide) (by decide)] at hread
    rw [hm, ← hread] at hcost
    omega

/-- Advance the ordered scan regardless of the candidate's visited mark.
A skip spends no incidence volume and does not move the worklist indices. -/
theorem ForestRootScanAt.step_runs
    {w a vc ec flags entry limbs base gradients zeroPtr queue h precision sortedBase i : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    {names : List ℕ} {edges : Finset ℕ}
    (hin : ForestRootScanAt st F g sortedBase base flags queue vc h limbs precision i names)
    (hi : i < names.length) (hnames : names.toFinset = F.V) (horder : names.Pairwise (· ≤ ·))
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
    ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) st .normal out cost ∧
      ForestRootScanAt out F g sortedBase base flags queue vc h limbs precision (i + 1) names ∧
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
          (129 * limbs + 209) + 26 * (out.regs 40 - st.regs 40) + 40 := by
  have hv : names[i] ∈ F.V := hnames ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
  have hvc := hgraph.2.1 _ hv
  have hflags := hin.2.2.2.2.2.2.2
  have hmark : st.mem (flags + names[i]) = 0 ∨ st.mem (flags + names[i]) = 1 := by
    obtain ⟨seen, _, _, _, _, _, hf, _⟩ := hflags
    rw [hf _ hvc]
    split <;> simp
  rcases hmark with hzeroMark | hone
  · obtain ⟨out, cost, seen, r, hr, hout, _, hlo, hread, hg, hgv, hz', htail, hqe,
      hspace, hseen, hregs, hscratch, hframe, hcost⟩ :=
      hin.fresh_step_runs (ω := ω) hi hnames horder hzeroMark hsortedRoom hsortedEnd hgraph
        hforest hext hhead hgraphRoom hnext ht hc hn hgrad hlimbs hzPtr hz hzero hvalues hsub
        himpl hgraphEnd hgradEnd hzEnd hroom hw hpotEnd hflagsEnd hqEnd hfit
    exact ⟨out, cost, hr, hout, hread.symm ▸ hlo, hg, hgv, hz', htail, hqe,
      hseen.symm ▸ hspace, hregs, hseen.symm ▸ hscratch, hframe, by simpa only [hseen, hread] using hcost⟩
  · obtain ⟨out, cost, hrun, hout, hm, hregs, hcost⟩ :=
      hin.skip_runs (p := p) (ω := ω) hi hone hvc hsortedRoom (by omega)
    have hh := hregs 4 (by decide) (by decide) (by decide)
    refine ⟨out, cost, hrun, hout, by rw [hregs 40 (by decide) (by decide) (by decide)],
      hm.symm ▸ hgraph, hm.symm ▸ hvalues, hm.symm ▸ hz, ?_, ?_, ?_, ?_, by rw [hm, hh], fun x _ => congrFun hm x, ?_⟩
    · rwa [hm, hh]
    · rwa [hh]
    · rwa [hm, hh]
    · intro k _ _ _ _ _ h26 _ _ _ h37 _ h44
      exact hregs k h26 h37 h44
    · rw [hm, hregs 40 (by decide) (by decide) (by decide)]
      omega

end MinCostFlow.MinRatio
