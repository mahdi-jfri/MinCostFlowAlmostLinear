module

public import MinCostFlow.LSF.Program.UpMinMath
public import MinCostFlow.LSF.Program.UpClosureMath
public import MinCostFlow.LSF.Program.BlockRep

/-!
# The aux block at the start

`auxAt_init` collects the facts that the passes of the initialization give into `AuxAt`: the vertex
list and its index table (from the component scan), the parent, parent-edge and depth arrays of the
rooted tree `T₀` (from the search), the ancestor table and the jump-minimum table (from `upVProc`
and `upMinProc`), the parent of each vertex in `T_H` (from `thProc`), and the header words.

`liftMin_congr` lets the driver use the table of `upMinProc`, which reads the ancestor table from
memory, in place of `liftMin` on `liftF par`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- `liftMin` at level `j` only reads the ancestor table below level `j`. -/
lemma liftMin_congr {U U' : ℕ → ℕ → ℕ} {pe piv : ℕ → ℕ} {r n L : ℕ}
    (hUU : ∀ i < n, ∀ j < L, U i j = U' i j) (hU : ∀ i < n, ∀ j < L, U i j < n) :
    ∀ j < L, ∀ i < n, liftMin U pe piv r i j = liftMin U' pe piv r i j := by
  intro j
  induction j with
  | zero => intro _ i _; rfl
  | succ j ih =>
    intro hj i hi
    simp only [liftMin]
    rw [← hUU i hi j (by omega), ih (by omega) i hi, ih (by omega) _ (hU i hi j (by omega))]

/-- One step up in `T_H`: the depth drops by one, and the vertex itself is the edge to its
parent (`treeOfParent`). -/
lemma th_step {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) (hur : u ≠ r) :
    ((hldAuxTree T r).forestPath u r).length =
      ((hldAuxTree T r).forestPath (thParent T r u) r).length + 1 ∧
    ∃ e ∈ (hldAuxTree T r).E,
      ((hldAuxTree T r).tail e = u ∧ (hldAuxTree T r).head e = thParent T r u) ∨
      ((hldAuxTree T r).tail e = thParent T r u ∧ (hldAuxTree T r).head e = u) := by
  refine ⟨(hldAuxTree_parent hT hu hur).2.2, u, ?_, Or.inl ⟨rfl, rfl⟩⟩
  simp only [hldAuxTree, treeOfParent, Finset.mem_erase]
  exact ⟨hur, hu⟩

/-- The header words of the aux block. -/
def AuxHeader (mem : ℕ → ℕ) (auxPtr vCap n0 : ℕ) : Prop :=
  mem (auxPtr + auxOffVIdxPtr) = auxVIdxBase auxPtr ∧
  mem (auxPtr + auxOffVListPtr) = auxVListBase auxPtr vCap ∧
  mem (auxPtr + auxOffT0ParentPtr) = auxT0ParentBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffT0ParentTreeIdxPtr) = auxT0ParentTreeIdxBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffT0DepthPtr) = auxT0DepthBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffLogCap) = auxLogCap n0 ∧
  mem (auxPtr + auxOffUpVPtr) = auxUpVBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffUpMinIdxPtr) = auxUpMinIdxBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffThParentPtr) = auxThParentBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffOrigVertPtr) = auxOrigVertBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffIsOrigVertPtr) = auxIsOrigVertBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffQBufAPtr) = auxQBufABase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffQBufBPtr) = auxQBufBBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffVisAPtr) = auxVisABase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffVisBPtr) = auxVisBBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffThStackPtr) = auxThStackBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffFSplitScratchPtr) = auxFSplitScratchBase auxPtr vCap n0

lemma getElem!_eq_getD' (l : List ℕ) (i : ℕ) : l[i]! = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, getElem!_def]
  cases l[i]? <;> rfl

/-- The aux block at the start of the data structure. The arrays of the rooted tree are read from
their places in the block. -/
theorem auxAt_init {mem : ℕ → ℕ} {auxPtr vCap tM r : ℕ} {S : LSFState}
    {tOrigList vList : List ℕ} {fid tl hd : ℕ → ℕ}
    (hH : AuxHeader mem auxPtr vCap vList.length)
    (hr0 : mem (auxPtr + auxOffR0Idx) = r) (hS0 : S.r₀ = vList.getD r 0)
    (hTI : TreeIdx S.T₀ vList tM r fid tl hd
      (fun x => mem (auxT0ParentBase auxPtr vCap vList.length + x))
      (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap vList.length + x))
      (fun x => mem (auxT0DepthBase auxPtr vCap vList.length + x)))
    (hlenT : tOrigList.length = tM) (hfid : ∀ t < tM, fid t = tOrigList.getD t 0)
    (hper : 0 < tM → mem (auxT0ParentTreeIdxBase auxPtr vCap vList.length + r) < tM)
    (hvLA : ListAt mem (auxVListBase auxPtr vCap) vList)
    (hvIdx : ∀ i (hi : i < vList.length), mem (auxVIdxBase auxPtr + vList[i]) = i + 1)
    (hvIdx0 : ∀ v < vCap, v ∉ S.T₀.V → mem (auxVIdxBase auxPtr + v) = 0)
    (hup : ∀ i < vList.length, ∀ j < auxLogCap vList.length,
      mem (auxUpVBase auxPtr vCap vList.length + (i * auxLogCap vList.length + j)) =
        liftF (fun x => mem (auxT0ParentBase auxPtr vCap vList.length + x)) i j)
    (hmin : ∀ i < vList.length, ∀ j < auxLogCap vList.length,
      mem (auxUpMinIdxBase auxPtr vCap vList.length + (i * auxLogCap vList.length + j)) =
        liftMin (fun i j => liftF (fun x => mem (auxT0ParentBase auxPtr vCap vList.length + x)) i j)
          (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap vList.length + x))
          (fun t => S.π (fid t)) r i j)
    (hth : ∀ x < vList.length, x ≠ r →
      mem (auxThParentBase auxPtr vCap vList.length + x) < vList.length ∧
      vList.getD (mem (auxThParentBase auxPtr vCap vList.length + x)) 0 =
        thParent S.T₀ (vList.getD r 0) (vList.getD x 0))
    (hthr : mem (auxThParentBase auxPtr vCap vList.length + r) = r)
    (hIso : ∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap vList.length + v) =
      if v ∈ S.T₀.V then 1 else 0)
    (hOrig : ∀ w ∈ S.G.V, w < vCap →
      mem (auxOrigVertBase auxPtr vCap vList.length + w) = S.origVert w)
    (hVis : ∀ v < vCap, mem (auxVisABase auxPtr vCap vList.length + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap vList.length + v) = 0) :
    AuxAt mem auxPtr vCap vList.length tM S tOrigList vList
      (fun x => mem (auxT0ParentBase auxPtr vCap vList.length + x))
      (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap vList.length + x))
      (fun x => mem (auxT0DepthBase auxPtr vCap vList.length + x))
      (fun x => mem (auxThParentBase auxPtr vCap vList.length + x))
      (fun i j => mem (auxUpVBase auxPtr vCap vList.length + (i * auxLogCap vList.length + j)))
      (fun i j => mem (auxUpMinIdxBase auxPtr vCap vList.length + (i * auxLogCap vList.length + j))) := by
  classical
  set n := vList.length with hn
  set par := fun x => mem (auxT0ParentBase auxPtr vCap n + x) with hpar
  set pe := fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap n + x) with hpe
  set dep := fun x => mem (auxT0DepthBase auxPtr vCap n + x) with hdep
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hH
  have hR := hTI.hR
  have hr := hTI.hr
  have hT := hTI.hT
  have hparlt : ∀ x < n, par x < n := hR.par_lt
  have hpelt : ∀ x < n, 0 < tM → pe x < tM := by
    intro x hx htM
    by_cases hxr : x = r
    · rw [hxr]; exact hper htM
    · exact (hR.step x hx hxr).1
  have hlift_lt : ∀ i < n, ∀ j, liftF par i j < n := fun i hi j => liftF_lt hparlt j i hi
  have hmemV : ∀ x < n, vList.getD x 0 ∈ S.T₀.V := fun x hx => hTI.getD_mem hx
  have hpiv : ∀ t < tM, (fun t => S.π (fid t)) t = S.π (fid t) := fun _ _ => rfl
  dsimp only [AuxAt]
  rw [hr0]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, rfl,
    hTI.hnd, fun v => (hTI.hV v).symm, hlenT, hvLA, hvIdx, hvIdx0, hr, ?_,
    fun i hi => ⟨rfl, hparlt i hi⟩, fun i hi => ⟨rfl, hpelt i hi⟩, fun i hi => rfl,
    fun i hi j hj => ?_, fun i hi => ?_, ?_, hR.dep_r, fun i hi hir => ?_, fun i hi j hj => ?_,
    fun i hi hir => ?_, hIso, hOrig, hVis⟩
  · rw [List.getElem?_eq_getElem hr, hS0, List.getD_eq_getElem _ _ hr]
  · -- the two tables
    refine ⟨rfl, by rw [hup i hi j hj]; exact hlift_lt i hi j, rfl, fun htM => ?_⟩
    rw [hmin i hi j hj]
    obtain ⟨k, hk, hkeq⟩ := liftMin_mem (pe := pe) (piv := fun t => S.π (fid t)) (r := r)
      (L := auxLogCap n) (fun i hi j _ => hlift_lt i hi j) j hj i hi
    rw [hkeq]
    exact hpelt k hk htM
  · -- the parents in `T_H`
    refine ⟨rfl, ?_⟩
    by_cases hir : i = r
    · show mem _ < n
      rw [hir, hthr]; exact hr
    · exact (hth i hi hir).1
  · exact hthr
  · -- the parent edge of a non-root vertex
    obtain ⟨hpe_lt, hjoin, hdep_eq⟩ := hR.step i hi hir
    refine ⟨hdep_eq, by rw [hlenT]; exact hpe_lt, ?_⟩
    have hf : tOrigList[pe i]! = fid (pe i) := by
      rw [getElem!_eq_getD', hfid _ hpe_lt]
    show tOrigList[pe i]! ∈ S.T₀.E ∧ _
    rw [hf]
    refine ⟨hTI.hA.fid_mem _ hpe_lt, ?_⟩
    rw [hTI.hA.tail_eq _ hpe_lt, hTI.hA.head_eq _ hpe_lt, getElem!_eq_getD',
      ← List.getD_eq_getElem _ 0 hi]
    rcases hjoin with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact Or.inl ⟨by rw [ht], by rw [hh]⟩
    · exact Or.inr ⟨by rw [ht], by rw [hh]⟩
  · -- the properties of the two tables
    refine ⟨fun hj0 => ?_, fun hj1 => ?_, fun hne => ?_⟩
    · subst hj0
      refine ⟨by rw [hup i hi 0 hj]; rfl, by rw [hmin i hi 0 hj]; rfl⟩
    · show mem _ = mem _
      rw [hup i hi (j + 1) hj1, hup _ (by rw [hup i hi j hj]; exact hlift_lt i hi j) j hj,
        hup i hi j hj]
      rfl
    · -- a jump that moves
      have hu' : liftF par i j < n := hlift_lt i hi j
      rw [getElem!_eq_getD', getElem!_eq_getD'] at hne
      try simp only at hne
      rw [hup i hi j hj] at hne
      have hne' : liftF par i j ≠ i := fun h => hne (by rw [h])
      obtain ⟨hm1, hm2, hm3⟩ := liftMin_spec (π := S.π) hR (fid := fid) hpiv j i hi hne'
      have hwalk := walkEdges_up_eq hT hTI.hA hTI.hnd hTI.hV hR hr (2 ^ j) i hi
      rw [← liftF_eq_iterate] at hwalk
      have hfm : tOrigList[liftMin (fun i j => liftF par i j) pe (fun t => S.π (fid t)) r i j]! =
          fid (liftMin (fun i j => liftF par i j) pe (fun t => S.π (fid t)) r i j) := by
        rw [getElem!_eq_getD', hfid _ hm1]
      show mem _ < tOrigList.length ∧ tOrigList[mem _]! ∈ _ ∧ _
      rw [hmin i hi j hj, hlenT, hfm, getElem!_eq_getD', getElem!_eq_getD', hup i hi j hj,
        hwalk]
      exact ⟨hm1, hm2, hm3⟩
  · -- the step up in `T_H`
    obtain ⟨hlt, hval⟩ := hth i hi hir
    have hiV := hmemV i hi
    have hne : vList.getD i 0 ≠ S.r₀ := by
      rw [hS0]
      intro h
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hr] at h
      exact hir ((hTI.hnd.getElem_inj_iff).mp h)
    have hstep := th_step hT hiV (by rw [← hS0]; exact hne)
    rw [← hS0] at hstep hval
    rw [getElem!_eq_getD', ← List.getD_eq_getElem _ 0 hi]
    simp only [LSFState.TH]
    rw [hval]
    exact hstep

end

end MinCostFlow.LSF.Program
