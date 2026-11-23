module

public import MinCostFlow.MinRatio.ShiftForestEndpoint
public import MinCostFlow.Expander.HeapSortProg
import MinCostFlow.LSF.Walks
import MinCostFlow.MinRatio.PathSummaryWalk

/-!
# Scanning the forest worklist during Shift

Each iteration reads one parent and propagates the Definition 5.6 potentials
(page 18) along its incidence list. Newly discovered vertices join the queue.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- Record that the current parent has been scanned. -/
@[expose] def advanceForestRead : Stmt :=
  .assign 40 (.bin .add (.reg 40) (.const 1))

/-- Read and scan the current queue entry, then advance the read index. -/
@[expose] def scanForestQueueParent (entry : ℕ) : Stmt :=
  .assign 25 (.load (.bin .add (.reg 39) (.reg 40))) ;;
    propagateForestParent entry ;; advanceForestRead

/-- Scan each queued parent, including those appended during the scan. -/
@[expose] def propagateForestQueue (entry : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 40) (.reg 41))
    (scanForestQueueParent entry)

/-- The worklist loop terminates when the read index reaches the write index.
A per-parent budget pays for each iteration and its queue test. -/
theorem propagateForestQueue_runs {w entry capacity : ℕ} {p : Program} {ω : ℕ → Bool}
    (Inv : ℕ → State → Prop) (budget : ℕ → ℕ)
    (hindices : ∀ i st, Inv i st → st.regs 40 = i ∧ i ≤ st.regs 41 ∧ st.regs 41 ≤ capacity)
    (hstep : ∀ i st, Inv i st → i < st.regs 41 →
      ∃ out cost, Runs w p ω (scanForestQueueParent entry) st .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ budget i)
    (hw : 1 < 2 ^ w) {i : ℕ} {st : State} (hin : Inv i st) :
    ∃ out cost j, Runs w p ω (propagateForestQueue entry) st .normal out cost ∧
      Inv j out ∧ i ≤ j ∧ out.regs 40 = out.regs 41 ∧
      cost ≤ ((List.range' i (j - i)).map (fun k => budget k + 4)).sum + 4 := by
  suffices h : ∀ n i st, i + n = capacity → Inv i st →
      ∃ out cost j, Runs w p ω (propagateForestQueue entry) st .normal out cost ∧
        Inv j out ∧ i ≤ j ∧ out.regs 40 = out.regs 41 ∧
        cost ≤ ((List.range' i (j - i)).map (fun k => budget k + 4)).sum + 4 by
    exact h (capacity - i) i st (by have := (hindices i st hin).2; omega) hin
  intro n
  induction n with
  | zero =>
    intro i st heq hin
    obtain ⟨hr, hlo, hhi⟩ := hindices i st hin
    have he : st.regs 41 = i := by omega
    have ht : Expr.eval w st (.bin .lt (.reg 40) (.reg 41)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hr, he]
    exact ⟨st, 4, i, runs_loop_iff.mpr (Or.inl ⟨ht, rfl, rfl, rfl⟩),
      hin, le_rfl, hr.trans he.symm, by simp⟩
  | succ n ih =>
    intro i st heq hin
    obtain ⟨hr, hlo, _⟩ := hindices i st hin
    by_cases ht : i < st.regs 41
    · have htest : Expr.eval w st (.bin .lt (.reg 40) (.reg 41)) = some 1 := by
        simp [Expr.eval, BinOp.eval, hr, ht, hw]
      obtain ⟨mid, c, hrun, hmid, hc⟩ := hstep i st hin ht
      obtain ⟨out, d, j, hrest, hout, hj, he, hd⟩ := ih (i + 1) mid (by omega) hmid
      refine ⟨out, c + 4 + d, j, runs_loop_iff.mpr (Or.inr (Or.inr
        ⟨1, mid, c, d, htest, by decide, hrun, hrest, by simp [Expr.size]; omega⟩)),
        hout, by omega, he, ?_⟩
      have hlen : j - i = (j - (i + 1)) + 1 := by omega
      rw [hlen]
      simp only [List.range'_succ, List.map_cons, List.sum_cons]
      omega
    · have htest : Expr.eval w st (.bin .lt (.reg 40) (.reg 41)) = some 0 := by
        simp [Expr.eval, BinOp.eval, hr, ht]
      exact ⟨st, 4, i, runs_loop_iff.mpr (Or.inl ⟨htest, rfl, rfl, rfl⟩), hin, le_rfl, by omega, by simp⟩

/-- When the queue is exhausted, every visited parent has been scanned.
If the component roots were seeded, the potential table then covers every
active vertex of the forest. -/
theorem forestQueue_exhausted_potentials {F : MGraph} {names : List ℕ}
    {st : State} {base h limbs precision : ℕ} {g : ℕ → ℝ}
    (hpots : ForestPotentialsAt st.mem base h limbs precision F g names.toFinset)
    (hroots : ∀ v ∈ F.V, Chain.compRoot F v ∈ names.toFinset)
    (hscanned : ∀ u ∈ (names.take (st.regs 40)), ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) →
      v ∈ names.toFinset)
    (hwrite : st.regs 41 = names.length) (hfinished : st.regs 40 = st.regs 41) :
    ForestPotentialsAt st.mem base h limbs precision F g F.V := by
  have hclosed : ∀ u ∈ names.toFinset, ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) →
      v ∈ names.toFinset := by
    intro u hu v hv
    apply hscanned u _ v hv
    rw [hfinished, hwrite, List.take_length]
    exact List.mem_toFinset.mp hu
  have hcover := forestVisited_covers_vertices hroots hclosed
  intro v hv
  exact hpots v (hcover hv)

/-- Schedule a canonical root whose potential is already zero. -/
@[expose] def enqueueForestRoot : Stmt :=
  markForestChildVisited ;; enqueueForestChild

/-- Root seeding changes exactly the root's visited word and its new queue
slot. The two arrays may share a heap as long as their ranges are disjoint. -/
theorem enqueueForestRoot_runs {w flags queue capacity root : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hflags : ForestVisitedAt st.mem flags capacity names.toFinset)
    (hlist : ListAt st.mem queue names)
    (hf : st.regs 36 = flags) (hq : st.regs 39 = queue)
    (hi : st.regs 41 = names.length) (hr : st.regs 26 = root)
    (hroot : root < capacity) (hspace : names.length < capacity)
    (hfRoom : flags + capacity ≤ 2 ^ w) (hqRoom : queue + capacity < 2 ^ w)
    (hdisjoint : flags + capacity ≤ queue ∨ queue + capacity ≤ flags) :
    ∃ out, Runs w p ω enqueueForestRoot st .normal out 16 ∧
      out.regs 41 = (names ++ [root]).length ∧ ListAt out.mem queue (names ++ [root]) ∧
      ForestVisitedAt out.mem flags capacity (names ++ [root]).toFinset ∧
      (∀ a, a ≠ flags + root → a ≠ queue + names.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  obtain ⟨mid, hmark, hmFlags, hmMem, hmRegs, hmPos⟩ :=
    markForestChildVisited_runs (p := p) (ω := ω) hflags hf hr hroot hfRoom (by omega)
  have hmList : ListAt mid.mem queue names := by
    intro i hin
    rw [hmMem _ (by rcases hdisjoint with h | h <;> omega)]
    exact hlist i hin
  obtain ⟨out, hrun, hlen, hoList, hoMem, hoRegs, hoPos⟩ :=
    enqueueForestChild_runs (p := p) (ω := ω) hmList
      (by rw [hmRegs, hq]) (by rw [hmRegs, hi]) (by rw [hmRegs, hr]) hspace hqRoom
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 10, hmark, hrun, rfl⟩),
    hlen, hoList, ?_, fun a ha hb => (hoMem a hb).trans (hmMem a ha),
    fun r hn => (hoRegs r hn).trans (congrFun hmRegs r), hoPos.trans hmPos⟩
  intro v hv
  rw [hoMem _ (by rcases hdisjoint with h | h <;> omega), hmFlags v hv]
  simp [List.toFinset_append, Finset.mem_insert]

/-- When vertices are considered by increasing name, any unvisited
vertex is its component's canonical root provided its smaller component
vertices have already been reached. -/
theorem forestRoot_of_unvisited_in_order {F : MGraph} {visited : Finset ℕ} {v : ℕ}
    (hfresh : v ∉ visited)
    (hsmaller : ∀ u < v, F.Connected v u → v ∈ visited) :
    Chain.compRoot F v = v := by
  have hroot : F.Connected v (Chain.compRoot F v) := Chain.connected_compRoot F v
  have hle : Chain.compRoot F v ≤ v := by
    classical
    unfold Chain.compRoot
    exact Nat.find_min' _ ⟨[], MGraph.IsWalk.nil v⟩
  exact le_antisymm hle (Nat.le_of_not_gt fun h => hfresh (hsmaller _ h hroot))

/-- Once the processed names and all their neighbors have been scanned,
a fresh vertex in the increasing-name scan has no smaller component vertex. -/
theorem forestRoot_of_closed_prefix {F : MGraph} {visited : Finset ℕ} {v : ℕ}
    (hvalid : F.IsValid) (hfresh : v ∉ visited)
    (hprefix : ∀ u ∈ F.V, u < v → u ∈ visited)
    (hclosed : ∀ u ∈ visited, ∀ x, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = x) ∨ (F.head e = u ∧ F.tail e = x)) → x ∈ visited) :
    Chain.compRoot F v = v := by
  apply forestRoot_of_unvisited_in_order hfresh
  intro u hu hconn
  obtain ⟨P, hp⟩ := LSF.connected_symm hconn
  have hne : P ≠ [] := by
    intro heq
    subst P
    cases hp
    exact (Nat.lt_irrefl _) hu
  exact forestVisited_of_walk hclosed hp (hprefix u (LSF.IsWalk_nonempty_mem hvalid hp hne).1 hu)

/-- The untouched slot of a fresh canonical root contains its exact
potential. Earlier components need only preserve this slot's zero words. -/
theorem forestRootPotential_of_zero_slot {F : MGraph} {mem : ℕ → ℕ}
    {base h limbs precision root : ℕ} {g : ℕ → ℝ}
    (hforest : F.IsForest) (hroot : Chain.compRoot F root = root)
    (hz : ∀ j < limbs, mem (base + root * limbs + j) = 0) :
    Num.Valid mem (base + root * limbs) h limbs ∧
      Num.fixVal mem (base + root * limbs) h limbs precision = Chain.treeRootPot F g root := by
  have hzero : ZeroFrom (fun _ => 0) 0 := fun _ _ => rfl
  have hvalid : Num.Valid mem (base + root * limbs) h limbs := by
    intro j hj
    rw [hz j hj]
    exact Nat.two_pow_pos h
  refine ⟨hvalid, ?_⟩
  have hagree : ∀ j < limbs, mem (base + root * limbs + j) = (fun _ : ℕ => 0) (0 + j) := hz
  have hpot : Chain.treeRootPot F g root = 0 := by
    simpa only [hroot] using treeRootPot_componentRoot F hforest g root
  rw [hpot, Num.fixVal, Num.intVal_congr (mem' := fun _ => 0) (a' := 0) hagree, Num.intVal_zeroFrom hzero (Nat.le_refl 0)]
  simp

/-- Seeding a canonical root establishes its potential and preserves the
potentials of the vertices already in the queue. -/
theorem enqueueForestRoot_potentials_runs
    {w flags queue capacity root base h limbs precision : ℕ} {names : List ℕ}
    {F : MGraph} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hflags : ForestVisitedAt st.mem flags capacity names.toFinset)
    (hlist : ListAt st.mem queue names)
    (hf : st.regs 36 = flags) (hq : st.regs 39 = queue)
    (hi : st.regs 41 = names.length) (hr : st.regs 26 = root)
    (hroot : root < capacity) (hspace : names.length < capacity)
    (hfRoom : flags + capacity ≤ 2 ^ w) (hqRoom : queue + capacity < 2 ^ w)
    (hdisjoint : flags + capacity ≤ queue ∨ queue + capacity ≤ flags)
    (hforest : F.IsForest) (hcanonical : Chain.compRoot F root = root)
    (hzero : ∀ j < limbs, st.mem (base + root * limbs + j) = 0)
    (hpots : ForestPotentialsAt st.mem base h limbs precision F g names.toFinset)
    (hpotFrame : ∀ v ∈ (names ++ [root]).toFinset, ∀ j < limbs,
      base + v * limbs + j ≠ flags + root ∧ base + v * limbs + j ≠ queue + names.length) :
    ∃ out, Runs w p ω enqueueForestRoot st .normal out 16 ∧
      out.regs 41 = (names ++ [root]).length ∧ ListAt out.mem queue (names ++ [root]) ∧
      ForestVisitedAt out.mem flags capacity (names ++ [root]).toFinset ∧
      ForestPotentialsAt out.mem base h limbs precision F g (names ++ [root]).toFinset ∧
      (∀ a, a ≠ flags + root → a ≠ queue + names.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  obtain ⟨out, hrun, hlen, houtList, houtFlags, hmem, hregs, hpos⟩ :=
    enqueueForestRoot_runs (p := p) (ω := ω) hflags hlist hf hq hi hr hroot hspace
      hfRoom hqRoom hdisjoint
  refine ⟨out, hrun, hlen, houtList, houtFlags, ?_, hmem, hregs, hpos⟩
  intro v hv
  have hagree (j : ℕ) (hj : j < limbs) :=
    hmem _ (hpotFrame v hv j hj).1 (hpotFrame v hv j hj).2
  rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · obtain ⟨hvalid, hvalue⟩ := hpots v (List.mem_toFinset.mpr hv)
    exact ⟨fun j hj => (hagree j hj) ▸ hvalid j hj,
      by rw [Num.fixVal, Num.intVal_congr hagree]; exact hvalue⟩
  · exact forestRootPotential_of_zero_slot hforest hcanonical
      (fun j hj => (hagree j hj).trans (hzero j hj))

/-- Seed a fresh component root and scan its worklist to exhaustion. -/
@[expose] def propagateForestComponent (entry : ℕ) : Stmt :=
  enqueueForestRoot ;; propagateForestQueue entry

/-- Starting a component adds seventeen steps to the worklist cost.
The worklist invariant starts at the previous queue length because its
earlier entries have already been scanned. -/
theorem propagateForestComponent_runs {w entry flags queue capacity root : ℕ}
    {names : List ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hflags : ForestVisitedAt st.mem flags capacity names.toFinset)
    (hlist : ListAt st.mem queue names)
    (hf : st.regs 36 = flags) (hq : st.regs 39 = queue)
    (hi : st.regs 41 = names.length) (hr : st.regs 26 = root)
    (hroot : root < capacity) (hspace : names.length < capacity)
    (hfRoom : flags + capacity ≤ 2 ^ w) (hqRoom : queue + capacity < 2 ^ w)
    (hdisjoint : flags + capacity ≤ queue ∨ queue + capacity ≤ flags)
    (Inv : ℕ → State → Prop) (budget : ℕ → ℕ)
    (hstart : ∀ mid, mid.regs 41 = (names ++ [root]).length →
      ListAt mid.mem queue (names ++ [root]) →
      ForestVisitedAt mid.mem flags capacity (names ++ [root]).toFinset →
      (∀ a, a ≠ flags + root → a ≠ queue + names.length → mid.mem a = st.mem a) →
      (∀ r, r ≠ 41 → mid.regs r = st.regs r) → Inv names.length mid)
    (hindices : ∀ i s, Inv i s → s.regs 40 = i ∧ i ≤ s.regs 41 ∧ s.regs 41 ≤ capacity)
    (hstep : ∀ i s, Inv i s → i < s.regs 41 →
      ∃ out cost, Runs w p ω (scanForestQueueParent entry) s .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ budget i) :
    ∃ out cost j, Runs w p ω (propagateForestComponent entry) st .normal out cost ∧
      Inv j out ∧ names.length ≤ j ∧ out.regs 40 = out.regs 41 ∧
      cost ≤ ((List.range' names.length (j - names.length)).map (fun k => budget k + 4)).sum + 21 := by
  obtain ⟨mid, hseed, hlen, hmList, hmFlags, hmMem, hmRegs, _⟩ :=
    enqueueForestRoot_runs (p := p) (ω := ω) hflags hlist hf hq hi hr hroot hspace
      hfRoom hqRoom hdisjoint
  obtain ⟨out, cost, j, hrun, hout, hj, he, hcost⟩ :=
    propagateForestQueue_runs Inv budget hindices hstep (by omega)
      (hstart mid hlen hmList hmFlags hmMem hmRegs)
  exact ⟨out, 16 + cost + 1, j, runs_seq_iff.mpr (Or.inr ⟨mid, 16, cost, hseed, hrun, rfl⟩),
    hout, hj, he, by omega⟩

/-- Start the component only if the candidate vertex has no visited mark. -/
@[expose] def propagateForestRootCandidate (entry : ℕ) : Stmt :=
  visitFreshForestChild (propagateForestComponent entry)

/-- The root test preserves the closed prefix for a visited vertex.
For a fresh root it adds eight steps to the component traversal. -/
theorem propagateForestRootCandidate_runs {w flags capacity v entry : ℕ}
    {visited : Finset ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hflags : ForestVisitedAt st.mem flags capacity visited)
    (hf : st.regs 36 = flags) (hv : st.regs 26 = v)
    (hcap : v < capacity) (hroom : flags + capacity ≤ 2 ^ w)
    (Post : State → Prop) (budget : ℕ)
    (hvisited : ∀ mid, v ∈ visited → mid.mem = st.mem →
      (∀ r, r ≠ 37 → mid.regs r = st.regs r) → Post mid)
    (hfresh : ∀ mid, v ∉ visited → mid.mem = st.mem →
      (∀ r, r ≠ 37 → mid.regs r = st.regs r) →
      ∃ out cost, Runs w p ω (propagateForestComponent entry) mid .normal out cost ∧
        Post out ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω (propagateForestRootCandidate entry) st .normal out cost ∧
      Post out ∧ cost ≤ budget + 9 := by
  obtain ⟨mid, hm, _, hregs, _, hskip, hrun⟩ :=
    visitFreshForestChild_runs (p := p) (ω := ω) (action := propagateForestComponent entry)
      hflags hf hv hcap hroom
  by_cases h : v ∈ visited
  · exact ⟨mid, 9, hskip h, hvisited mid h hm hregs, by omega⟩
  · obtain ⟨out, cost, hc, hout, hcost⟩ := hfresh mid h hm hregs
    exact ⟨out, cost + 8, hrun h hc, hout, by omega⟩

/-- Read the active-name list length and base from the forest layout.
Register 45 holds the graph base. Registers 46 and 47 receive the count
and list base, respectively. -/
@[expose] def loadForestActiveNames : Stmt :=
  .assign 46 (.load (.bin .add (.reg 45) (.const 2))) ;;
  .assign 47 (.bin .add (.bin .add (.reg 45) (.const 4)) (.reg 21))

/-- The active-name array enumerates every forest vertex once. Its compact
length, rather than the name capacity, is the number of entries to copy. -/
theorem loadForestActiveNames_runs {w a vc ec : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hgraph : DynGraphAt st.mem a vc ec F)
    (ha : st.regs 45 = a) (hc : st.regs 21 = vc)
    (hroom : a + dynGraphSize vc ec < 2 ^ w) :
    ∃ out names, Runs w p ω loadForestActiveNames st .normal out 12 ∧
      out.regs 46 = names.length ∧ out.regs 47 = dgVListBase a vc ∧
      names.Nodup ∧ names.toFinset = F.V ∧ ListAt out.mem (out.regs 47) names ∧
      (∀ r, r ≠ 46 → r ≠ 47 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  rcases hgraph with ⟨_, _, _, _, _, hn, _, _, ⟨names, hlen, hnd, hmem, hlist, _⟩, _⟩
  have htwo : 2 < 2 ^ w := by simp only [dynGraphSize] at hroom; omega
  have hfour : 4 < 2 ^ w := by simp only [dynGraphSize] at hroom; omega
  have hcount : a + 2 < 2 ^ w := by simp only [dynGraphSize] at hroom; omega
  have hheader : a + 4 < 2 ^ w := by simp only [dynGraphSize] at hroom; omega
  have hbase : dgVListBase a vc < 2 ^ w := by
    simp only [dgVListBase, dynGraphSize] at *
    omega
  let mid := { st with regs := Function.update st.regs 46 names.length }
  let out := { mid with regs := Function.update mid.regs 47 (dgVListBase a vc) }
  have h1 : Runs w p ω (.assign 46 (.load (.bin .add (.reg 45) (.const 2)))) st .normal mid 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, htwo, hcount]; exact hn.trans hlen.symm,
      rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 47 (.bin .add (.bin .add (.reg 45) (.const 4)) (.reg 21)))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, ha, hc, hfour, hheader,
        dgVListBase, show a + 4 + vc < 2 ^ w from hbase],
      rfl, rfl, rfl⟩
  refine ⟨out, names, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 6, h1, h2, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], hnd, ?_, ?_, ?_, rfl, rfl⟩
  · ext v
    exact List.mem_toFinset.trans (hmem v)
  · simpa [out, mid] using hlist
  · intro r h46 h47
    simp [out, mid, Function.update_of_ne, h46, h47]

/-- Copy the compact active-name array before sorting it. Register 48
holds the scratch destination. -/
@[expose] def copyForestActiveNames (entry : ℕ) : Stmt :=
  .call 49 entry [.reg 47, .reg 48, .reg 46]

/-- Copy the active names without touching the source or other live memory. -/
theorem copyForestActiveNames_runs {w entry src dst : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hcopy : MeetsContract w p entry (copyWordsContract w))
    (hlist : ListAt st.mem src names)
    (hs : st.regs 47 = src) (hd : st.regs 48 = dst) (hn : st.regs 46 = names.length)
    (hsrc : src + names.length < 2 ^ w) (hdst : dst + names.length < 2 ^ w)
    (hw : 1 < 2 ^ w)
    (hdisjoint : dst + names.length ≤ src ∨ src + names.length ≤ dst) :
    ∃ out cost, Runs w p ω (copyForestActiveNames entry) st .normal out cost ∧
      ListAt out.mem dst names ∧
      (∀ a, a < dst ∨ dst + names.length ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 49 → out.regs r = st.regs r) ∧ cost ≤ 17 * names.length + 14 := by
  have hpre : (copyWordsContract w).pre [src, dst, names.length] st.mem :=
    ⟨src, dst, names.length, rfl, hw, hsrc.le, hdst.le, hdisjoint⟩
  have hwords : ∀ a ∈ [src, dst, names.length], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hr, hpost, hcost⟩ :=
    hcopy [src, dst, names.length] st.mem st.pos ω hwords hpre
  obtain ⟨x, y, n, hargs, _, hcells, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  let out := { after with regs := Function.update st.regs 49 o.value }
  have hargs : evalArgs w st [.reg 47, .reg 48, .reg 46] = some [src, dst, names.length] := by
    simp [evalArgs, Expr.eval, hs, hd, hn]
  refine ⟨out, 3 + c + 1, runs_call_iff.mpr ⟨_, body, o, after, c, hargs,
    hbody, hr, rfl, rfl, rfl⟩, copyWords_listAt hlist rfl hcells, hframe,
    fun r hne => Function.update_of_ne hne _ _, ?_⟩
  change c ≤ 17 * names.length + 10 at hcost
  omega

/-- Sort the copied active names in place. -/
@[expose] def sortForestActiveNames (entry : ℕ) : Stmt :=
  .call 49 entry [.reg 48, .reg 46]

/-- Sorting orders the active names without changing their multiplicity
or touching graph storage outside the copied array. -/
theorem sortForestActiveNames_runs {w entry dst : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsort : MeetsContract w p entry (Expander.heapSortContract w))
    (hlist : ListAt st.mem dst names) (hd : st.regs 48 = dst) (hn : st.regs 46 = names.length)
    (hroom : dst + names.length + 2 < 2 ^ w) (hcount : 2 * names.length + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hname : ∀ v ∈ names, v < 2 ^ w) :
    ∃ out sorted cost, Runs w p ω (sortForestActiveNames entry) st .normal out cost ∧
      sorted.Perm names ∧ sorted.Pairwise (· ≤ ·) ∧ ListAt out.mem dst sorted ∧
      (∀ a, a < dst ∨ dst + names.length ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 49 → out.regs r = st.regs r) ∧
      cost ≤ 280 * (names.length * (2 * Nat.log 2 (names.length + 2) + 1) + 1) + 3 := by
  have hpre : (Expander.heapSortContract w).pre [dst, names.length] st.mem :=
    ⟨dst, names.length, rfl, hroom, hcount, hw, fun i hi => by
      rw [hlist i hi]
      exact hname _ (List.getElem_mem hi)⟩
  have hwords : ∀ a ∈ [dst, names.length], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hr, hpost, hcost⟩ :=
    hsort [dst, names.length] st.mem st.pos ω hwords hpre
  obtain ⟨_, hperm, hsorted, _, hframe⟩ := hpost
  let sorted := tab names.length fun i => after.mem (dst + i)
  have htab : (tab names.length fun i => st.mem (dst + i)) = names := by
    apply List.ext_getElem
    · simp [tab]
    · intro i hi hi'
      simpa [tab] using hlist i hi'
  let out := { after with regs := Function.update st.regs 49 o.value }
  have hargs : evalArgs w st [.reg 48, .reg 46] = some [dst, names.length] := by
    simp [evalArgs, Expr.eval, hd, hn]
  refine ⟨out, sorted, 2 + c + 1, runs_call_iff.mpr ⟨_, body, o, after, c, hargs,
    hbody, hr, rfl, rfl, rfl⟩, ?_, hsorted, ?_, hframe,
    fun r hne => Function.update_of_ne hne _ _, ?_⟩
  · change sorted.Perm (tab names.length fun i => st.mem (dst + i)) at hperm
    exact htab ▸ hperm
  · intro i hi
    simp [sorted, tab, out]
  · change c ≤ 280 * (names.length * (2 * Nat.log 2 (names.length + 2) + 1) + 1) at hcost
    omega

/-- Prepare a sorted copy of the active-name array. -/
@[expose] def orderForestActiveNames (copy sort : ℕ) : Stmt :=
  copyForestActiveNames copy ;; sortForestActiveNames sort

/-- Both calls change only the destination array and their return register.
The result lists the same vertex names in increasing order. -/
theorem orderForestActiveNames_runs {w copy sort src dst : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hlist : ListAt st.mem src names)
    (hs : st.regs 47 = src) (hd : st.regs 48 = dst) (hn : st.regs 46 = names.length)
    (hsrc : src + names.length < 2 ^ w) (hdst : dst + names.length + 2 < 2 ^ w)
    (hcount : 2 * names.length + 2 < 2 ^ w) (hw : 4 ≤ 2 ^ w)
    (hdisjoint : dst + names.length ≤ src ∨ src + names.length ≤ dst)
    (hname : ∀ v ∈ names, v < 2 ^ w) :
    ∃ out sorted cost, Runs w p ω (orderForestActiveNames copy sort) st .normal out cost ∧
      sorted.Perm names ∧ sorted.Pairwise (· ≤ ·) ∧ ListAt out.mem dst sorted ∧
      (∀ a, a < dst ∨ dst + names.length ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 49 → out.regs r = st.regs r) ∧
      cost ≤ 280 * (names.length * (2 * Nat.log 2 (names.length + 2) + 1) + 1) +
        17 * names.length + 18 := by
  obtain ⟨mid, c, hrc, hmid, hm, hregs, hc⟩ :=
    copyForestActiveNames_runs (ω := ω) hcopy hlist hs hd hn hsrc (by omega) (by omega) hdisjoint
  obtain ⟨out, sorted, d, hrs, hperm, hsorted, hout, hframe, horegs, hcost⟩ :=
    sortForestActiveNames_runs (ω := ω) hsort hmid
      ((hregs 48 (by decide)).trans hd) ((hregs 46 (by decide)).trans hn)
      hdst hcount hw hname
  exact ⟨out, sorted, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hrc, hrs, rfl⟩),
    hperm, hsorted, hout, fun a ha => (hframe a ha).trans (hm a ha),
    fun r hr => (horegs r hr).trans (hregs r hr), by omega⟩

/-- Load the next root candidate from the sorted active-name array. -/
@[expose] def loadOrderedForestVertex : Stmt :=
  .assign 26 (.load (.bin .add (.reg 48) (.reg 44)))

/-- The compact scan reads exactly one active name and keeps its index. -/
theorem loadOrderedForestVertex_runs {w base i : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hlist : ListAt st.mem base names) (hi : i < names.length)
    (hb : st.regs 48 = base) (hr : st.regs 44 = i)
    (hroom : base + names.length ≤ 2 ^ w) :
    ∃ out, Runs w p ω loadOrderedForestVertex st .normal out 5 ∧
      out.regs 26 = names[i] ∧
      (∀ r, r ≠ 26 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 26 names[i] }
  have ha : base + i < 2 ^ w := by omega
  have hrun : Runs w p ω loadOrderedForestVertex st .normal out 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hb, hr, ha, hlist i hi],
      rfl, rfl, rfl⟩
  exact ⟨out, hrun, by simp [out], fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩

/-- Process a candidate from the sorted active array and advance its index. -/
@[expose] def propagateOrderedForestVertex (entry : ℕ) : Stmt :=
  loadOrderedForestVertex ;; propagateForestRootCandidate entry ;;
    .assign 44 (.bin .add (.reg 44) (.const 1))

/-- The compact step adds eleven steps to root dispatch and keeps its next
index independent of the vertex names used by the worklist. -/
theorem propagateOrderedForestVertex_runs {w entry base i budget : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hlist : ListAt st.mem base names) (hi : i < names.length)
    (hb : st.regs 48 = base) (hr : st.regs 44 = i)
    (hroom : base + names.length < 2 ^ w) (Post : State → Prop)
    (hstep : ∀ pre, pre.regs 26 = names[i] →
      (∀ r, r ≠ 26 → pre.regs r = st.regs r) → pre.mem = st.mem →
      ∃ mid cost, Runs w p ω (propagateForestRootCandidate entry) pre .normal mid cost ∧
        mid.regs 44 = i ∧ Post mid ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) st .normal out cost ∧
      out.regs 44 = i + 1 ∧
      (∃ mid, Post mid ∧ out.mem = mid.mem ∧
        ∀ r, r ≠ 44 → out.regs r = mid.regs r) ∧ cost ≤ budget + 11 := by
  obtain ⟨pre, hload, hname, hregs, hmem, _⟩ :=
    loadOrderedForestVertex_runs (p := p) (ω := ω) hlist hi hb hr hroom.le
  obtain ⟨mid, c, hrun, hidx, hpost, hc⟩ := hstep pre hname hregs hmem
  let out := { mid with regs := Function.update mid.regs 44 (i + 1) }
  have hone : 1 < 2 ^ w := by omega
  have hnext : i + 1 < 2 ^ w := by omega
  have hlast : Runs w p ω (.assign 44 (.bin .add (.reg 44) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hidx, hone, hnext], rfl, rfl, rfl⟩
  exact ⟨out, 5 + (c + 4 + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨pre, 5, c + 4 + 1, hload,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hrun, hlast, rfl⟩), rfl⟩),
    by simp [out], ⟨mid, hpost, rfl, fun r hne => Function.update_of_ne hne _ _⟩, by omega⟩

/-- Consider the remaining active vertex names in increasing order. -/
@[expose] def propagateForestVertices (entry : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 44) (.reg 46)) (propagateOrderedForestVertex entry)

/-- The name scan starts from its current index and stops exactly at the
vertex count. Each index pays for its step and one comparison. -/
theorem propagateForestVertices_runs {w entry count : ℕ}
    {p : Program} {ω : ℕ → Bool} (Inv : ℕ → State → Prop) (budget : ℕ → ℕ)
    (hindex : ∀ i s, Inv i s → s.regs 44 = i ∧ s.regs 46 = count)
    (hstep : ∀ i s, i < count → Inv i s →
      ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) s .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ budget i)
    (hw : 1 < 2 ^ w) {i : ℕ} {st : State} (hi : i ≤ count) (hin : Inv i st) :
    ∃ out cost, Runs w p ω (propagateForestVertices entry) st .normal out cost ∧
      Inv count out ∧
      cost ≤ ((List.range' i (count - i)).map (fun k => budget k + 4)).sum + 4 := by
  suffices h : ∀ n i s, i + n = count → Inv i s →
      ∃ out cost, Runs w p ω (propagateForestVertices entry) s .normal out cost ∧
        Inv count out ∧ cost ≤ ((List.range' i n).map (fun k => budget k + 4)).sum + 4 by
    exact h (count - i) i st (by omega) hin
  intro n
  induction n with
  | zero =>
    intro i s heq hs
    have hi : i = count := by omega
    subst i
    obtain ⟨hr, hc⟩ := hindex _ _ hs
    have ht : Expr.eval w s (.bin .lt (.reg 44) (.reg 46)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hr, hc]
    exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨ht, rfl, rfl, rfl⟩), hs, by simp⟩
  | succ n ih =>
    intro i s heq hs
    have hi : i < count := by omega
    obtain ⟨hr, hc⟩ := hindex i s hs
    have ht : Expr.eval w s (.bin .lt (.reg 44) (.reg 46)) = some 1 := by
      simp [Expr.eval, BinOp.eval, hr, hc, hi, hw]
    obtain ⟨mid, c, hrun, hmid, hcost⟩ := hstep i s hi hs
    obtain ⟨out, d, hrest, hout, hd⟩ := ih (i + 1) mid (by omega) hmid
    refine ⟨out, c + 4 + d, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨1, mid, c, d, ht, by decide, hrun, hrest, by simp [Expr.size]; omega⟩)), hout, ?_⟩
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega

/-- A fresh candidate in the sorted active list is a canonical root once
the previous candidates belong to completed components. -/
theorem forestRoot_of_ordered_prefix {F : MGraph} {visited : Finset ℕ}
    {names : List ℕ} {i : ℕ} (hi : i < names.length)
    (hvalid : F.IsValid) (hnames : names.toFinset = F.V)
    (horder : names.Pairwise (· ≤ ·)) (hfresh : names[i] ∉ visited)
    (hprefix : ∀ j (hj : j < names.length), j < i → names[j] ∈ visited)
    (hclosed : ∀ u ∈ visited, ∀ x, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = x) ∨ (F.head e = u ∧ F.tail e = x)) → x ∈ visited) :
    Chain.compRoot F names[i] = names[i] := by
  apply forestRoot_of_closed_prefix hvalid hfresh _ hclosed
  intro u hu hlt
  have hmem : u ∈ names := List.mem_toFinset.mp (hnames.symm ▸ hu)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  apply hprefix j hj
  by_contra! hji
  rcases lt_or_eq_of_le hji with h | rfl
  · exact (Nat.not_lt_of_ge (List.pairwise_iff_getElem.mp horder i j hi hj h)) hlt
  · exact (Nat.lt_irrefl _) hlt

/-- Once the sorted scan has processed every index, its visited potential
invariant gives a potential for every active graph vertex. -/
theorem orderedForestScan_potentials {F : MGraph} {names : List ℕ}
    {visited : Finset ℕ} {mem : ℕ → ℕ} {base h limbs precision : ℕ} {g : ℕ → ℝ}
    (hnames : names.toFinset = F.V)
    (hprefix : ∀ i (hi : i < names.length), names[i] ∈ visited)
    (hpots : ForestPotentialsAt mem base h limbs precision F g visited) :
    ForestPotentialsAt mem base h limbs precision F g F.V := by
  intro v hv
  have hmem : v ∈ names := List.mem_toFinset.mp (hnames.symm ▸ hv)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  exact hpots _ (hprefix i hi)

/-- Recover the integer numerator map needed by the core gradient scan.
Outside the active set no walk can have a first edge, so the model
potential there is zero. -/
theorem ForestPotentialsAt.numerators {F : MGraph} {mem : ℕ → ℕ}
    {base h limbs precision : ℕ} {g : ℕ → ℝ}
    (hforest : F.IsForest) (hpots : ForestPotentialsAt mem base h limbs precision F g F.V) :
    ∃ pot : ℕ → ℤ, (∀ v ∈ F.V, PathIntAt mem (base + v * limbs) h limbs (pot v)) ∧
      ∀ v, Chain.treeRootPot F g v = (pot v : ℝ) / (2 : ℝ) ^ precision := by
  classical
  let pot (v : ℕ) := if v ∈ F.V then Num.intVal mem (base + v * limbs) h limbs else 0
  refine ⟨pot, ?_, ?_⟩
  · intro v hv
    simpa only [pot, hv, ↓reduceIte] using
      (show PathIntAt mem (base + v * limbs) h limbs
        (Num.intVal mem (base + v * limbs) h limbs) from ⟨(hpots v hv).1, rfl⟩)
  · intro v
    by_cases hv : v ∈ F.V
    · simpa only [pot, hv, ↓reduceIte, Num.fixVal] using (hpots v hv).2.symm
    · have hpath := LSF.forestPath_isPath hforest (Chain.connected_compRoot F v)
      have hnil : F.forestPath v (Chain.compRoot F v) = [] := by
        by_contra hne
        exact hv (LSF.IsWalk_nonempty_mem hforest.1 hpath.1 hne).1
      rw [Chain.treeRootPot, hnil]
      simp [pot, hv, walkInner, walkEdges]

/-- The original graph and gradient table, together with the traversed
forest potentials, supply the inputs to the core gradient scan. -/
theorem gradientScanInputsAt_of_forestPotentials
    {G F : MGraph} {mem : ℕ → ℕ} {graph vc ec src base h limbs precision : ℕ} {g : ℕ → ℝ}
    (hgraph : DynGraphAt mem graph vc ec G) (hvertices : G.V ⊆ F.V)
    (hgrad : EdgeValuesAt mem src h limbs precision G.E g)
    (hforest : F.IsForest) (hpots : ForestPotentialsAt mem base h limbs precision F g F.V) :
    ∃ ng pot : ℕ → ℤ,
      gradientScanInputsAt mem G graph vc ec src base h limbs ng pot ∧
      (∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ precision) ∧
      ∀ v, Chain.treeRootPot F g v = (pot v : ℝ) / (2 : ℝ) ^ precision := by
  obtain ⟨pot, hp, hpot⟩ := hpots.numerators hforest
  let ng (e : ℕ) := Num.intVal mem (src + e * limbs) h limbs
  exact ⟨ng, pot, ⟨hgraph, fun e he => ⟨(hgrad e he).1, rfl⟩,
      fun v hv => hp v (hvertices hv)⟩,
    fun e he => (hgrad e he).2.symm, hpot⟩

/-- Start the deeper gradient scan with the decoded potentials and an
empty output prefix. The scan frames the memory present at this boundary. -/
theorem gradientScanReady_of_forestPotentials
    {G F : MGraph} {st : State} {graph vc ec src base dst h limbs precision scratch : ℕ}
    {g : ℕ → ℝ}
    (hgraph : DynGraphAt st.mem graph vc ec G) (hvertices : G.V ⊆ F.V)
    (hgrad : EdgeValuesAt st.mem src h limbs precision G.E g)
    (hforest : F.IsForest) (hpots : ForestPotentialsAt st.mem base h limbs precision F g F.V)
    (hsrc : st.regs 13 = src) (hdst : st.regs 14 = dst)
    (htail : st.regs 15 = dgETailSlotBase graph vc ec)
    (hhead : st.regs 16 = dgEHeadSlotBase graph vc ec)
    (hnames : st.regs 17 = dgIntToExtBase graph vc)
    (hbase : st.regs 20 = base) (hlimbs : st.regs 3 = limbs)
    (hheap : st.regs 4 = scratch) (hzero : ZeroFrom st.mem scratch) :
    ∃ ng pot : ℕ → ℤ,
      gradientScanReady G graph vc ec src base dst h limbs scratch ng pot st.mem
        (st.regs 6) (st.regs 7) 0 st ∧
      (∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ precision) ∧
      ∀ v, Chain.treeRootPot F g v = (pot v : ℝ) / (2 : ℝ) ^ precision := by
  obtain ⟨ng, pot, hinputs, hg, hp⟩ :=
    gradientScanInputsAt_of_forestPotentials hgraph hvertices hgrad hforest hpots
  exact ⟨ng, pot, ⟨hinputs, hsrc, hdst, htail, hhead, hnames, hbase, hlimbs,
    by simpa using hheap, hheap.symm ▸ hzero, rfl, rfl, fun _ _ => rfl⟩, hg, hp⟩

/-- Run the deeper gradient calculation using the forest traversal's
potential table and the original gradient table. -/
theorem prepareShiftGradientInputs_of_forestPotentials_runs
    {w h base vc ec nextBase nextVC nextEC src dst potential limbs scratch precision entry : ℕ}
    {G H : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (nextLengths : ℕ → ℝ) (hsub : H.E ⊆ G.E)
    (hn : st.regs 6 = nextBase) (hnGraph : DynGraphAt st.mem nextBase nextVC nextEC H)
    (hgraph : DynGraphAt st.mem base vc ec G) (hvertices : G.V ⊆ forest.T.V)
    (hgrad : EdgeValuesAt st.mem src h limbs precision G.E g)
    (hforest : forest.T.IsForest)
    (hpots : ForestPotentialsAt st.mem potential h limbs precision forest.T g forest.T.V)
    (hsrc : st.regs 13 = src) (hdst : st.regs 14 = dst)
    (htail : st.regs 15 = dgETailSlotBase base vc ec)
    (hhead : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hnames : st.regs 17 = dgIntToExtBase base vc)
    (hbase : st.regs 20 = potential) (hlimbs : st.regs 3 = limbs)
    (hheap : st.regs 4 = scratch) (hzero : ZeroFrom st.mem scratch)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hgEnd : base + dynGraphSize vc ec ≤ dst)
    (hsEnd : ∀ e ∈ G.E, src + e * limbs + limbs ≤ dst)
    (hpEnd : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hnEnd : nextBase + dynGraphSize nextVC nextEC ≤ dst)
    (hlenTable : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ dst)
    (hdEnd : ∀ e ∈ G.E, dst + e * limbs + limbs ≤ scratch)
    (hdScratch : dst ≤ scratch)
    (hfit : ∀ e ∈ G.E, Num.Fits h limbs
      (Num.intVal st.mem (src + e * limbs) h limbs +
        (Num.intVal st.mem (potential + G.head e * limbs) h limbs -
          Num.intVal st.mem (potential + G.tail e * limbs) h limbs)))
    (hspace : scratch + 3 * limbs * H.m < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareShiftGradientInputs entry) st .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧ out.regs 8 = dst ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      out.regs 4 = scratch + 3 * limbs * H.m ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < dst, out.mem addr = st.mem addr) ∧
      cost ≤ (129 * limbs + 172) * H.m + 31 := by
  obtain ⟨ng, pot, hready, hg, hpot⟩ := gradientScanReady_of_forestPotentials hgraph
    hvertices hgrad hforest hpots hsrc hdst htail hhead hnames hbase hlimbs hheap hzero
  rw [hn] at hready
  refine prepareShiftGradientInputs_runs ng pot nextLengths hsub hn hnGraph hready hg hpot
    (fun _ _ => himpl _ _ _) hgEnd hsEnd hpEnd hnEnd hlenTable hlenEnd hdEnd hdScratch ?_ hspace hw
  intro e he
  have hinput := hready.1
  obtain ⟨ht, hh⟩ := hgraph.1 e he
  rw [← (hinput.2.1 e he).2, ← (hinput.2.2 _ hh).2, ← (hinput.2.2 _ ht).2]
  exact hfit e he

/-- Start the compact root scan at the beginning of the sorted array. -/
@[expose] def startForestVertices (entry : ℕ) : Stmt :=
  .assign 44 (.const 0) ;; propagateForestVertices entry

/-- Initializing the compact cursor costs three steps including sequencing. -/
theorem startForestVertices_runs {w entry count : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (Inv : ℕ → State → Prop) (budget : ℕ → ℕ)
    (hindex : ∀ i s, Inv i s → s.regs 44 = i ∧ s.regs 46 = count)
    (hstep : ∀ i s, i < count → Inv i s →
      ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) s .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ budget i)
    (hw : 1 < 2 ^ w)
    (hstart : Inv 0 { st with regs := Function.update st.regs 44 0 }) :
    ∃ out cost, Runs w p ω (startForestVertices entry) st .normal out cost ∧
      Inv count out ∧
      cost ≤ ((List.range' 0 count).map (fun k => budget k + 4)).sum + 7 := by
  let mid := { st with regs := Function.update st.regs 44 0 }
  have hinit : Runs w p ω (.assign 44 (.const 0)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  obtain ⟨out, cost, hr, hout, hc⟩ :=
    propagateForestVertices_runs Inv budget hindex hstep hw (Nat.zero_le count) hstart
  exact ⟨out, 2 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 2, cost, hinit, hr, rfl⟩),
    hout, by simp only [Nat.sub_zero] at hc; omega⟩

/-- The compact scan returns the entire potential table once the loop
invariant covers the processed prefix. -/
theorem startForestVertices_potentials_runs {w entry base h limbs precision : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {names : List ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hnames : names.toFinset = F.V)
    (Inv : ℕ → State → Prop) (budget : ℕ → ℕ)
    (hindex : ∀ i s, Inv i s → s.regs 44 = i ∧ s.regs 46 = names.length)
    (hstep : ∀ i s, i < names.length → Inv i s →
      ∃ out cost, Runs w p ω (propagateOrderedForestVertex entry) s .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ budget i)
    (hprefix : ∀ i s, Inv i s → ∃ visited,
      (∀ j (hj : j < names.length), j < i → names[j] ∈ visited) ∧
      ForestPotentialsAt s.mem base h limbs precision F g visited)
    (hw : 1 < 2 ^ w)
    (hstart : Inv 0 { st with regs := Function.update st.regs 44 0 }) :
    ∃ out cost, Runs w p ω (startForestVertices entry) st .normal out cost ∧
      Inv names.length out ∧ ForestPotentialsAt out.mem base h limbs precision F g F.V ∧
      cost ≤ ((List.range' 0 names.length).map (fun k => budget k + 4)).sum + 7 := by
  obtain ⟨out, cost, hrun, hout, hcost⟩ :=
    startForestVertices_runs Inv budget hindex hstep hw hstart
  obtain ⟨visited, hcovered, hpots⟩ := hprefix names.length out hout
  exact ⟨out, cost, hrun, hout,
    orderedForestScan_potentials hnames (fun j hj => hcovered j hj hj) hpots, hcost⟩

/-- Allocate the potential table, shared zero operand, visited markers,
and queue in that order. Their arrays occupy consecutive disjoint ranges. -/
@[expose] def reserveForestTraversal : Stmt :=
  reserveForestPotentials ;; reserveForestVisited ;; reserveForestQueue

/-- The traversal starts with no visited vertices or queued parents, and the
root potential slots and unused heap are zero. -/
theorem reserveForestTraversal_runs {w heap vc h limbs precision : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool} (g : ℕ → ℝ)
    (hh : st.regs 4 = heap) (hv : st.regs 21 = vc) (hl : st.regs 3 = limbs)
    (hz : ZeroFrom st.mem heap) (hforest : F.IsForest)
    (hroom : heap + vc * limbs + limbs + vc + vc < 2 ^ w) :
    let zeroPtr := heap + vc * limbs
    let flags := zeroPtr + limbs
    let queue := flags + vc
    ∃ out, Runs w p ω reserveForestTraversal st .normal out 36 ∧
      out.regs 20 = heap ∧ out.regs 22 = zeroPtr ∧ out.regs 36 = flags ∧
      out.regs 39 = queue ∧ out.regs 40 = 0 ∧ out.regs 41 = 0 ∧
      out.regs 4 = queue + vc ∧ ForestVisitedAt out.mem flags vc ∅ ∧
      ForestPotentialsAt out.mem heap h limbs precision F g ∅ ∧
      PathIntAt out.mem zeroPtr h limbs 0 ∧ ZeroFrom out.mem heap ∧
      (∀ r, r ≠ 20 → r ≠ 22 → r ≠ 36 → r ≠ 39 → r ≠ 40 → r ≠ 41 → r ≠ 4 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨s1, hpot, hbase, hzptr, hheap, hzval, _, htail, hr1, hm1, hp1⟩ :=
    reserveForestPotentials_runs (w := w) (p := p) (ω := ω) hh hv hl hz (by omega) hforest g h precision
  obtain ⟨s2, hmark, hf, hq, hflags, hzq, hr2, hm2, hp2⟩ :=
    reserveForestVisited_runs (w := w) (p := p) (ω := ω) hheap
      ((hr1 21 (by decide) (by decide) (by decide)).trans hv)
      (by simpa only [hheap] using htail) (by omega)
  obtain ⟨out, hqueue, hqptr, hread, hwrite, houtHeap, _, hr3, hm3, hp3⟩ :=
    reserveForestQueue_runs (p := p) (ω := ω) hq
      ((hr2 21 (by decide) (by decide)).trans
        ((hr1 21 (by decide) (by decide) (by decide)).trans hv)) hzq hroom
  have keep (r : ℕ) (ha : r ≠ 39) (hb : r ≠ 40) (hc : r ≠ 41)
      (hd : r ≠ 36) (he : r ≠ 4) : out.regs r = s1.regs r :=
    (hr3 r ha hb hc he).trans (hr2 r hd he)
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 14, 21, hpot,
      runs_seq_iff.mpr (Or.inr ⟨s2, 7, 13, hmark, hqueue, rfl⟩), rfl⟩),
    (keep 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbase,
    (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzptr,
    (hr3 36 (by decide) (by decide) (by decide) (by decide)).trans hf,
    hqptr, hread, hwrite, houtHeap, hm3.symm ▸ hflags, ?_,
    by simpa only [hm3, hm2, hzptr] using hzval,
    by simpa only [hm3, hm2, hm1] using hz, ?_, hm3.trans (hm2.trans hm1), hp3.trans (hp2.trans hp1)⟩
  · simp [ForestPotentialsAt]
  · intro r h20 h22 h36 h39 h40 h41 h4
    exact (keep r h39 h40 h41 h36 h4).trans (hr1 r h20 h22 h4)

/-- The empty initialized scan has a compact array cursor, an exhausted
empty queue, and zero marker and potential storage. -/
theorem reserveForestTraversal_initial_scan_runs
    {w heap vc h limbs precision sortedBase : ℕ} {F : MGraph}
    {names : List ℕ} {p : Program} {st : State} {ω : ℕ → Bool} (g : ℕ → ℝ)
    (hh : st.regs 4 = heap) (hv : st.regs 21 = vc) (hl : st.regs 3 = limbs)
    (hs : st.regs 48 = sortedBase) (hc : st.regs 46 = names.length)
    (hnames : ListAt st.mem sortedBase names)
    (hz : ZeroFrom st.mem heap) (hforest : F.IsForest)
    (hroom : heap + vc * limbs + limbs + vc + vc < 2 ^ w) :
    ∃ out, Runs w p ω (reserveForestTraversal ;; .assign 44 (.const 0)) st .normal out 39 ∧
      out.regs 44 = 0 ∧ out.regs 46 = names.length ∧ out.regs 48 = sortedBase ∧
      ListAt out.mem sortedBase names ∧
      out.regs 20 = heap ∧ out.regs 22 = heap + vc * limbs ∧
      out.regs 36 = heap + vc * limbs + limbs ∧
      out.regs 39 = heap + vc * limbs + limbs + vc ∧
      out.regs 40 = 0 ∧ out.regs 41 = 0 ∧
      out.regs 4 = heap + vc * limbs + limbs + vc + vc ∧
      ForestVisitedAt out.mem (out.regs 36) vc ∅ ∧
      ForestPotentialsAt out.mem heap h limbs precision F g ∅ ∧
      PathIntAt out.mem (out.regs 22) h limbs 0 ∧ ZeroFrom out.mem heap ∧
      (∀ r, r ≠ 44 → r ≠ 20 → r ≠ 22 → r ≠ 36 → r ≠ 39 → r ≠ 40 → r ≠ 41 →
        r ≠ 4 → out.regs r = st.regs r) ∧ out.mem = st.mem := by
  obtain ⟨mid, hrun, hb, hzptr, hf, hq, hr, hw, hheap, hflags, hpots, hzval, hzero, hregs, hm, _⟩ :=
    reserveForestTraversal_runs (p := p) (ω := ω) g hh hv hl hz hforest hroom
  let out := { mid with regs := Function.update mid.regs 44 0 }
  have hinit : Runs w p ω (.assign 44 (.const 0)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  have h46 := (hregs 46 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hc
  have h48 := (hregs 48 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 36, 2, hrun, hinit, rfl⟩), by simp [out],
    by simpa [out] using h46, by simpa [out] using h48, hm.symm ▸ hnames,
    by simpa [out] using hb, by simpa [out] using hzptr, by simpa [out] using hf,
    by simpa [out] using hq, by simpa [out] using hr, by simpa [out] using hw,
    by simpa [out] using hheap, by simpa [out, hf, Function.update_of_ne] using hflags, hpots,
    by simpa [out, hzptr, Function.update_of_ne] using hzval, hzero, ?_, hm⟩
  intro r h44 h20 h22 h36 h39 h40 h41 h4
  exact (Function.update_of_ne h44 _ _).trans (hregs r h20 h22 h36 h39 h40 h41 h4)

/-- Reserve exactly one scratch word per active vertex for the sorted names. -/
@[expose] def reserveForestActiveNames : Stmt :=
  .assign 48 (.reg 4) ;; .assign 4 (.bin .add (.reg 4) (.reg 46))

/-- The scratch array begins at the old heap and the new heap remains zeroed. -/
theorem reserveForestActiveNames_runs {w heap count : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hc : st.regs 46 = count)
    (hz : ZeroFrom st.mem heap) (hroom : heap + count < 2 ^ w) :
    ∃ out, Runs w p ω reserveForestActiveNames st .normal out 7 ∧
      out.regs 48 = heap ∧ out.regs 4 = heap + count ∧
      ZeroFrom out.mem (heap + count) ∧
      (∀ r, r ≠ 48 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 48 heap }
  let out := { mid with regs := Function.update mid.regs 4 (heap + count) }
  have hfirst : Runs w p ω (.assign 48 (.reg 4)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.reg 46))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hh, hc, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], fun a ha => hz a (by omega),
    ?_, rfl, rfl⟩
  intro r h48 h4
  simp [out, mid, Function.update_of_ne, h48, h4]

/-- Read, allocate, and order the active-name array. -/
@[expose] def prepareOrderedForestNames (copy sort : ℕ) : Stmt :=
  loadForestActiveNames ;; reserveForestActiveNames ;; orderForestActiveNames copy sort

/-- Prepare the sorted array above the graph and advance the heap by
exactly the number of active vertices. -/
theorem prepareOrderedForestNames_runs {w copy sort a vc ec heap : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hgraph : DynGraphAt st.mem a vc ec F) (ha : st.regs 45 = a) (hc : st.regs 21 = vc)
    (hh : st.regs 4 = heap) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap)
    (hroom : heap + F.n + 2 < 2 ^ w) (hcount : 2 * F.n + 2 < 2 ^ w)
    (hlistEnd : dgVListBase a vc + F.n ≤ heap) (hw : 4 ≤ 2 ^ w) :
    ∃ out names cost, Runs w p ω (prepareOrderedForestNames copy sort) st .normal out cost ∧
      names.Nodup ∧ names.Pairwise (· ≤ ·) ∧ names.toFinset = F.V ∧ names.length = F.n ∧
      ListAt out.mem heap names ∧ out.regs 48 = heap ∧ out.regs 46 = names.length ∧
      out.regs 4 = heap + F.n ∧ ZeroFrom out.mem (heap + F.n) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 46 → r ≠ 47 → r ≠ 48 → r ≠ 49 → r ≠ 4 →
        out.regs r = st.regs r) ∧
      cost ≤ 280 * (F.n * (2 * Nat.log 2 (F.n + 2) + 1) + 1) + 17 * F.n + 39 := by
  obtain ⟨s1, names, hload, hn, hbase, hnodup, hnames, hlist, hr1, hm1, _⟩ :=
    loadForestActiveNames_runs (w := w) (p := p) (ω := ω) hgraph ha hc (by omega)
  have hlen : names.length = F.n := by rw [MGraph.n, ← hnames, List.toFinset_card_of_nodup hnodup]
  obtain ⟨s2, hreserve, hd, hheap, hzero, hr2, hm2, _⟩ :=
    reserveForestActiveNames_runs (w := w) (p := p) (ω := ω)
      ((hr1 4 (by decide) (by decide)).trans hh) hn (hm1.symm ▸ hz) (by omega)
  have hword (v : ℕ) (hv : v ∈ names) : v < 2 ^ w := by
    have hvCap := hgraph.2.1 v (hnames ▸ List.mem_toFinset.mpr hv)
    simp only [dynGraphSize] at hgraphEnd
    omega
  obtain ⟨out, sorted, c, horder, hperm, hsorted, hresult, hframe, hregs, hcost⟩ :=
    orderForestActiveNames_runs (ω := ω) hcopy hsort (hm2.symm ▸ (hbase ▸ hlist))
      ((hr2 47 (by decide) (by decide)).trans hbase) hd
      ((hr2 46 (by decide) (by decide)).trans hn)
      (by omega) (by omega) (by omega) hw (Or.inr (by omega)) hword
  have hsortedLen := hperm.length_eq.trans hlen
  refine ⟨out, sorted, 12 + (7 + c + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 12, 7 + c + 1, hload,
      runs_seq_iff.mpr (Or.inr ⟨s2, 7, c, hreserve, horder, rfl⟩), rfl⟩),
    hperm.nodup_iff.mpr hnodup, hsorted, ?_, hsortedLen, hresult,
    (hregs 48 (by decide)).trans hd,
    (hregs 46 (by decide)).trans ((hr2 46 (by decide) (by decide)).trans (hn.trans hperm.length_eq.symm)),
    (hregs 4 (by decide)).trans (by simpa only [hlen] using hheap), ?_, ?_, ?_, ?_⟩
  · ext v
    simp only [List.mem_toFinset, hperm.mem_iff, ← hnames]
  · intro x hx
    rw [hframe x (Or.inr (by omega))]
    exact hzero x (by omega)
  · intro x hx
    rw [hframe x (Or.inl hx), hm2, hm1]
  · intro r h46 h47 h48 h49 h4
    exact (hregs r h49).trans ((hr2 r h48 h4).trans (hr1 r h46 h47))
  · rw [hlen] at hcost
    omega

end MinCostFlow.MinRatio
