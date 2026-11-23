module

public import MinCostFlow.LSF.Program.DecompFrame
public import MinCostFlow.LSF.Program.FlagMergeMath
public import MinCostFlow.LSF.Program.FForestMath

/-!
# The roots pass of the decomposition phase

The forest phase reads the root flags, the owners and the roots of the decomposition phase. The
bridges `fGraph_bridge`, `fAnc_bridge` and `wBlock_bridge` ask that these arrays form the roots
pass (`RootPassIdx`) of a root set. Here we show that they do, for the upward closure of
`C_reps ∪ B ∪ ends of the edges with P`, where the representatives, the boundary flags and the
high flags are the inputs of the flag merge (`decompPhase_rootPass`).

The roots stage reads the tree arrays from the memory after the flag merge and writes its
output above `inR`. `RootPassIdx.congr` moves the facts to the memory at the start of the phase
for the tree arrays (they lie below `dBase`, which the first five calls keep) and to the memory
at the end of the phase for the output (the two last copies write only the stretch arrays).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- `RootPassIdx` depends on its arrays only through their values on indices that exist. -/
lemma RootPassIdx.congr {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {R : Finset ℕ} {π inR piv mp own rt : ℕ → ℕ}
    {par' pe' inR' piv' mp' own' rt' : ℕ → ℕ}
    (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt)
    (hmpl : ∀ x < vList.length, x ≠ r → mp x < tM)
    (e1 : ∀ y < vList.length, inR' y = inR y) (e2 : ∀ y < vList.length, par' y = par y)
    (e3 : ∀ y < vList.length, pe' y = pe y) (e4 : ∀ i < tM, piv' i = piv i)
    (e5 : ∀ y < vList.length, mp' y = mp y) (e6 : ∀ i < tM, own' i = own i)
    (e7 : ∀ y < vList.length, rt' y = rt y) :
    RootPassIdx T₀ vList tM r fid par' pe' R π inR' piv' mp' own' rt' := by
  have hr := hI.hr
  have hinRr : inR r = 1 := (h.hS.hinR r hr).mpr h.hS.hrR
  refine ⟨⟨h.hS.hR, h.hS.hrR, fun x hx => by rw [e1 x hx]; exact h.hS.hinR x hx, h.hS.hπ,
    fun i hi => by rw [e4 i hi]; exact h.hS.hpiv i hi⟩, fun x hx hxr => ?_,
    ownState_congr3 e1 e5 e6 h.hown, by rw [e7 r hr]; exact h.hrt_r, fun x hx hxr => ?_⟩
  · have hp := hI.hR.par_lt x hx
    have hpe := (hI.hR.step x hx hxr).1
    refine mpRule_congrM (by rw [e2 x hx, e1 _ hp]) (e2 x hx) (e3 x hx) (e4 _ hpe) (e5 x hx)
      (e5 _ hp) (fun hne => e4 _ (hmpl _ hp fun he => hne (by rw [he]; exact hinRr)))
      (h.hmp x hx hxr)
  · have hp := hI.hR.par_lt x hx
    have hpe := (hI.hR.step x hx hxr).1
    exact rtRule_congrM (e1 x hx) (e2 x hx) (e3 x hx) (e6 _ hpe) (e7 x hx) (e7 _ hp)
      (h.hrule x hx hxr)

open Classical in
/-- After the decomposition phase, the root flags, the owners and the roots above `inR` form the
roots pass for the upward closure in `T_H` of the representatives, the boundary `B` and the
ends of the edges with `P`. The tree arrays are read from the memory at the start of the phase.
The boundary flags are those of the first call, the high flags those copied to `hiCopy`. -/
theorem decompPhase_rootPass {w h C : ℕ} {T₀ G₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem m₁ m₃ m₄ m₅ m₆ m₇ mem₈ : ℕ → ℕ} {v₁ v₄ v₅ v₆ : ℕ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (h₁ : (decompWTContract w).post [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] mem
        v₁ m₁)
    (h₃ : (wstrStageContract w h C).post [X.n, X.tM, X.m0, X.k, wstrLB X.n X.D X.Lw, X.Lw, X.Lin,
        X.nOrig, 0, X.logCap, X.lenArr, tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar,
        X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev,
        X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS,
        X.denS, X.idPtr] m₁ (wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18) m₃)
    (h₄ : (memCopyContract w).post [X.hiCopy, wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18,
        X.m0] m₃ v₄ m₄)
    (h₅ : (flagMergeContract w).post [X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx,
        X.hiCopy, X.eu, X.ev, X.inR] m₄ v₅ m₅)
    (h₆ : (rootsStageContract w).post [X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n,
        tPiBase X.tPtr X.vCap X.tM, X.thDst, X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n,
        X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM] m₅ v₆ m₆)
    (h₇ : wstrCopyEdgesPost X.numSt X.numS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₆ m₇)
    (h₈ : wstrCopyEdgesPost X.denSt X.denS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₇ mem₈)
    {B : Finset ℕ} {P : ℕ → Prop} {π : ℕ → ℕ}
    (hbnd : ∀ x < vList.length, m₁ (X.dBase + 11 * X.n + x) = 1 ↔ vList.getD x 0 ∈ B)
    (hBV : ∀ v ∈ B, v ∈ vList)
    (hrepV : ∀ j < X.cnt, mem (X.repPtr + j) ∈ vList)
    (hvC : ∀ v ∈ vList, v < X.vCap)
    (hvIdx : ∀ i (hi : i < vList.length), mem (X.vIdx + vList[i]) = i + 1)
    (heMem : ∀ e, e ∈ G₀.E ↔ ∃ t < X.m0, mem (dgEListBase X.gPtr X.vCap X.eCap + t) = e)
    (hhigh : ∀ t < X.m0, mem₈ (X.hiCopy + t) = 1 ↔
      P (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (heu : ∀ t < X.m0, mem (X.eu + t) < vList.length ∧
      vList.getD (mem (X.eu + t)) 0 = G₀.tail (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (hev : ∀ t < X.m0, mem (X.ev + t) < vList.length ∧
      vList.getD (mem (X.ev + t)) 0 = G₀.head (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (hπ : IsEdgeOrder T₀ π)
    (hpiv : ∀ i < X.tM, π (mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) =
      mem (tPiBase X.tPtr X.vCap X.tM + i)) :
    RootPassIdx T₀ vList X.tM 0 (fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i))
      (fun x => mem (X.auxPar + x)) (fun x => mem (X.auxPar + X.n + x))
      (upClosure (hldAuxTree T₀ (vList.getD 0 0)) (vList.getD 0 0)
        (((List.range X.cnt).map fun j => mem (X.repPtr + j)).toFinset ∪ B ∪
          (G₀.E.filter P).biUnion fun e => {G₀.tail e, G₀.head e}))
      π (fun y => mem₈ (X.inR + y)) (fun i => mem (tPiBase X.tPtr X.vCap X.tM + i))
      (fun y => mem₈ (X.inR + X.n + y)) (fun i => mem₈ (X.inR + X.n + X.n + i))
      (fun y => mem₈ (X.inR + X.n + X.n + X.tM + y)) := by
  have hn := I.hn; have hvl := I.hvlen
  have L3 := I.L3; have L5 := I.L5; have L7 := I.L7; have L8 := I.L8; have L9 := I.L9
  have L10 := I.L10; have L11 := I.L11; have L12 := I.L12; have L15 := I.L15
  have L16 := I.L16; have L17 := I.L17
  obtain ⟨-, -, -, F4, F5, F6⟩ := decompPhase_frame I h₁ h₃ h₄ h₅ h₆ h₇ h₈
  -- the tree arrays, at the start and after the flag merge
  obtain ⟨Q, tl, hd, dep, -, -, hRA, -, hTA⟩ := I.htree
  have hpar5 : ∀ x < X.n, mem (X.auxPar + x) = m₅ (X.auxPar + x) :=
    fun x hx => (F5 _ (by omega)).symm
  have hpe5 : ∀ x < X.n, mem (X.auxPar + X.n + x) = m₅ (X.auxPar + X.n + x) :=
    fun x hx => (F5 _ (by omega)).symm
  have hI : TreeIdx T₀ vList X.tM 0 (fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) tl hd
      (fun x => mem (X.auxPar + x)) (fun x => mem (X.auxPar + X.n + x)) dep :=
    ⟨I.hT, hTA, I.hnd, I.hV, by rw [hvl]; exact hRA, by rw [hvl]; exact hn⟩
  have hI5 : TreeIdx T₀ vList X.tM 0 (fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) tl hd
      (fun x => m₅ (X.auxPar + x)) (fun x => m₅ (X.auxPar + X.n + x)) dep :=
    ⟨I.hT, hTA, I.hnd, I.hV, by rw [hvl]; exact hRA.congr hn hpar5 hpe5 (fun _ _ => rfl),
      by rw [hvl]; exact hn⟩
  -- the memory before the flag merge
  obtain ⟨_, _, _, heq₄, -, -, hfr₄⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₅, -, hfr₅, hfl₅⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  have h45 : ∀ a, (a < X.inR ∨ X.inR + X.n ≤ a) → m₄ a = m₅ a := fun a ha => (hfr₅ a ha).symm
  have hm4 : ∀ a < X.dBase, m₄ a = mem a := fun a ha => by
    rw [h45 a (Or.inl (by omega)), F5 a ha]
  have L13 := I.L13; have L14 := I.L14
  have hm48 : ∀ t < X.m0, m₄ (X.hiCopy + t) = mem₈ (X.hiCopy + t) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, hfr₆, -⟩ := id h₆
    simp only [List.cons.injEq, and_true] at heq₆
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
    obtain ⟨-, hfr₇⟩ := h₇
    obtain ⟨-, hfr₈⟩ := h₈
    intro t ht
    rw [hfr₈ _ (Or.inr (by omega)), hfr₇ _ (Or.inr (by omega)),
      hfr₆ _ (Or.inl (by omega)) (Or.inl (by omega)), h45 _ (Or.inl (by omega))]
  set repList := (List.range X.cnt).map fun j => mem (X.repPtr + j) with hrl
  have hMF := mergedFlag_iff (mem := m₄) (cnt := X.cnt) (m0 := X.m0)
    (bndPtr := X.dBase + 11 * X.n) (repPtr := X.repPtr) (vIdxPtr := X.vIdx) (highPtr := X.hiCopy)
    (euPtr := X.eu) (evPtr := X.ev) (repList := repList) (G₀ := G₀) (B := B) (P := P)
    (eL := fun t => mem (dgEListBase X.gPtr X.vCap X.eCap + t)) I.hnd
    (fun x hx => by
      rw [h45 _ (Or.inl (by omega)), F6 _ (by omega) (by omega)]; exact hbnd x hx)
    (fun i hi => by
      simp only [hrl, List.length_map, List.length_range] at hi
      simp only [hrl, List.getElem_map, List.getElem_range]
      exact hm4 _ (by omega))
    (by simp [hrl])
    (fun v hv => by
      simp only [hrl, List.mem_map, List.mem_range] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      exact hrepV j hj)
    (fun i hi => by
      have := hvC _ (List.getElem_mem hi)
      rw [hm4 _ (by omega)]; exact hvIdx i hi)
    heMem
    (fun t ht => by rw [hm48 t ht]; exact hhigh t ht)
    (fun t ht => by rw [hm4 _ (by omega)]; exact heu t ht)
    (fun t ht => by rw [hm4 _ (by omega)]; exact hev t ht)
  set R0 := repList.toFinset ∪ B ∪ (G₀.E.filter P).biUnion fun e => {G₀.tail e, G₀.head e}
    with hR0
  have hf : ∀ u < vList.length, m₅ (X.inR + u) = 1 ↔ vList.getD u 0 ∈ R0 := by
    intro u hu
    rw [hfl₅ u (by omega), ← hMF u hu]
    split_ifs with hc <;> simp [hc]
  have hRV : ∀ v ∈ R0, v ∈ vList := by
    intro v hv
    simp only [hR0, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      List.mem_toFinset] at hv
    rcases hv with (hv | hv) | ⟨e, ⟨he, -⟩, hv⟩
    · simp only [hrl, List.mem_map, List.mem_range] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      exact hrepV j hj
    · exact hBV v hv
    · obtain ⟨t, ht, rfl⟩ := (heMem e).mp he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [← (heu t ht).2]; rw [List.getD_eq_getElem _ _ (heu t ht).1]
        exact List.getElem_mem _
      · rw [← (hev t ht).2]; rw [List.getD_eq_getElem _ _ (hev t ht).1]
        exact List.getElem_mem _
  -- the roots stage
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, -, hin₆, -, hmp₆, hown₆, hrt₆,
    hrule₆⟩ := h₆
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  have hTH : THIdx T₀ vList 0 (fun x => m₅ (X.thBase + 7 * X.n + x)) (fun x => m₅ (X.thDst + x)) :=
    fun x hx => ⟨by dsimp only; rw [F5 _ (by omega)]; exact I.hthDep x (by omega), fun hx0 => by
      dsimp only; rw [F5 _ (by omega), hvl]; exact I.hthPar x (by omega) hx0⟩
  have hrR : vList.getD 0 0 ∈ R0 := by
    obtain ⟨j, hj, hj0⟩ := I.hroot
    have hm : mem (X.repPtr + j) ∈ vList := hrepV j hj
    have hidx : vList.idxOf (mem (X.repPtr + j)) = 0 := by
      have hi := List.idxOf_lt_length_of_mem hm
      have h1 := hvIdx _ hi
      simp only [List.getElem_idxOf] at h1
      unfold repIdx at hj0
      omega
    have : vList.getD 0 0 = mem (X.repPtr + j) := by
      rw [← hidx, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hm), List.getElem_idxOf]
    rw [this, hR0]
    simp only [Finset.mem_union, List.mem_toFinset, hrl, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
  have hP5 := rootsStage_rootPassIdx (R := R0) (π := π) hI5 hTH hRV hf hrR hπ
    (fun i hi => by rw [F5 _ (by omega)]; exact hpiv i hi)
    (fun y hy => by rw [hin₆ y (by omega), hvl])
    (fun x hx hx0 => (hmp₆ x (by omega) hx0).2) (by rw [hvl]; exact hown₆) hrt₆
    (fun x hx hx0 => hrule₆ x (by omega) hx0)
  refine RootPassIdx.congr hI5 hP5 (fun x hx hx0 => (hmp₆ x (by omega) hx0).1)
    (fun y hy => F4 _ (by omega) (by omega)) (fun y hy => (F5 _ (by omega)).symm)
    (fun y hy => (F5 _ (by omega)).symm) (fun i hi => (F5 _ (by omega)).symm)
    (fun y hy => F4 _ (by omega) (by omega)) (fun i hi => F4 _ (by omega) (by omega))
    (fun y hy => F4 _ (by omega) (by omega))

end

end MinCostFlow.LSF.Program
