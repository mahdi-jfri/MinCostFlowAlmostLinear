module

public import MinCostFlow.LSF.Program.OrderPhase

/-!
# What the order phase needs

`OrderPhaseIn` lists what the memory holds at the start of the order phase: the edge arrays of
`T₀`, the graph block of `G₀`, the vertex list and the indices in the aux block, the numbers
`q_nat`, the zero scratch areas, and the layout. `orderPhase_rootPre` gives the pre of the first
call from it.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The memory at the start of the order phase. -/
structure OrderPhaseIn (w h : ℕ) (G₀ T₀ : MGraph) (vList eList : List ℕ) (X : OrderLayout)
    (mem : ℕ → ℕ) : Prop where
  hw16 : 16 ≤ 2 ^ w
  hh : 0 < h
  hhw : 2 * h + 2 ≤ w
  hn2 : 2 ≤ X.n
  hvlen : vList.length = X.n
  hnd : vList.Nodup
  hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList
  hGV : ∀ u, u ∈ G₀.V ↔ u ∈ vList
  htM : X.tM = X.n - 1
  hT : IsRootedTree T₀ (vList.getD 0 0)
  hST : ∀ u ∈ T₀.V, ∀ v ∈ T₀.V, T₀.Connected u v
  hA : T0IndexArrays T₀ vList X.tM (fun i => mem (X.tOrigSrc + i)) (fun i => mem (X.tTail + i))
    (fun i => mem (X.tHead + i))
  hnO : X.nOrig ≤ X.tM
  hO : ∀ i < X.tM, (mem (X.tOrigSrc + i) ∈ G₀.E ↔ i < X.nOrig)
  hTG : ∀ e ∈ T₀.E, e ∈ G₀.E → T₀.tail e = G₀.tail e ∧ T₀.head e = G₀.head e
  hdg : DynGraphAt mem X.gPtr X.vCap X.eCap G₀
  heL : ListAt mem (dgEListBase X.gPtr X.vCap X.eCap) eList
  heLen : eList.length = X.m0
  heE : ∀ e ∈ eList, e ∈ G₀.E
  hvI : ∀ i (hi : i < vList.length), mem (X.vIdx + vList[i]) = i + 1
  hvLA : ListAt mem X.vListPtr vList
  hvCap : ∀ u ∈ vList, u < X.vCap
  hK : 1 ≤ X.K
  hKq : X.Kq ≤ X.K
  hme : X.m0 ≤ X.eCap
  hq : ∀ t < X.m0, Valid mem (X.qPtr + t * X.Kq) h X.Kq
  hqs : ∑ t ∈ Finset.range X.m0, unsignedVal mem (X.qPtr + t * X.Kq) h X.Kq < capacity h X.K
  hzS1 : ∀ i < X.n, mem (X.sPtr + i) = 0
  hzS2 : ∀ i < X.n, mem (X.sPtr + X.n + 2 * X.tM + i) = 0
  hzT : ∀ i < dynGraphSize X.vCap (2 * X.tM + 1), mem (tDgTPtr X.tPtr + i) = 0
  hzIdx : ∀ e < X.eCap, mem (tIdxOfEdgeBase X.tPtr X.vCap X.tM + e) = 0
  hzTH : ∀ a, X.thBase ≤ a → a < X.thBase + 8 * X.n → mem a = 0
  hlog : X.logCap = auxLogCap X.n
  hmin : X.minPtr = X.auxPar + 3 * X.n + X.n * X.logCap
  -- the layout, from the bottom up
  l1 : X.gPtr + dynGraphSize X.vCap X.eCap ≤ X.tPtr
  l2 : X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ X.vIdx
  l3 : X.vIdx + X.vCap ≤ X.vListPtr
  l4 : X.vListPtr + X.n ≤ X.auxPar
  l5 : X.minPtr + X.n * X.logCap ≤ X.thDst
  l6 : X.thDst + X.n ≤ X.qPtr
  l7 : X.qPtr + X.m0 * X.Kq ≤ X.tOrigSrc
  l8 : X.tOrigSrc + X.tM ≤ X.tTail
  l9 : X.tTail + X.tM ≤ X.tHead
  l10 : X.tHead + X.tM ≤ X.rtOut
  l11 : X.rtOut + 3 * X.n ≤ X.sPtr
  l12 : X.sPtr + 4 * X.n + 2 * X.tM ≤ X.eu
  l13 : X.eu + X.m0 ≤ X.ev
  l14 : X.ev + X.m0 ≤ X.dPtr
  l15 : X.dPtr + X.n * X.K ≤ X.tmpPtr
  l16 : X.tmpPtr + X.K ≤ X.arrPtr
  l17 : X.arrPtr + X.n ≤ X.scratchPtr
  l18 : X.scratchPtr + X.n ≤ X.thBase
  l19 : X.thBase + 8 * X.n < 2 ^ w
  l20 : thBound X.n + 2 * X.n + 8 < 2 ^ w

/-- The ends of the tree edges, as functions. -/
def OrderLayout.tl (X : OrderLayout) (mem : ℕ → ℕ) : ℕ → ℕ := fun f => mem (X.tTail + f)
def OrderLayout.hd (X : OrderLayout) (mem : ℕ → ℕ) : ℕ → ℕ := fun f => mem (X.tHead + f)

/-- The pre of the first call. -/
lemma orderPhase_rootPre {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem) :
    (rootStageContract w).pre [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap]
      mem := by
  have hA := I.hA
  have hn := I.hn2
  refine ⟨X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap, X.tl mem,
    X.hd mem, rfl, ⟨I.hw16, by omega, fun f hf => ⟨rfl, ?_⟩, fun f hf => ⟨rfl, ?_⟩,
      by have := I.l10; have := I.l9; omega, I.l10, I.l11, ?_⟩, I.hzS1, I.hzS2, ?_, ?_, ?_, ?_⟩
  · rw [← I.hvlen]; exact hA.tl_lt f hf
  · rw [← I.hvlen]; exact hA.hd_lt f hf
  · have := I.l12; have := I.l13; have := I.l14; have := I.l15; have := I.l16; have := I.l17
    have := I.l18; have := I.l19; omega
  · intro x hx
    have h := rtReach_of_spanning hA I.hnd I.hST (fun u => (I.hV u).symm) (a := 0)
      (by rw [I.hvlen]; omega) x (by rw [I.hvlen]; exact hx)
    exact h
  · rw [I.hlog]; unfold auxLogCap; omega
  · have := I.hmin; have := I.l5; have := I.l6; have := I.l7; have := I.l8; omega
  · have := I.hmin; have := I.l5; have := I.l6; have := I.l7; have := I.l8; have := I.l9; omega


/-- The memory after the rooting call and the store: it agrees with the start memory outside the
aux arrays of the tree and the scratch areas of the rooting. -/
lemma orderPhase_frame₂ {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₁ : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hfr : ∀ a, (a < X.auxPar ∨ X.auxPar + 3 * X.n + X.n * X.logCap ≤ a) →
      (a < X.rtOut ∨ (X.rtOut + 3 * X.n ≤ a ∧ a < X.sPtr) ∨ X.sPtr + 4 * X.n + 2 * X.tM ≤ a) →
      mem₁ a = mem a) :
    ∀ a, (a < X.auxPar ∨ (X.minPtr ≤ a ∧ a < X.rtOut) ∨ X.sPtr + 4 * X.n + 2 * X.tM ≤ a) →
      Function.update mem₁ (X.auxPar + X.n) 0 a = mem a := by
  intro a ha
  have hm := I.hmin; have h11 := I.l11; have h5 := I.l5; have h6 := I.l6; have h7 := I.l7
  have h8 := I.l8; have h9 := I.l9; have h10 := I.l10; have hn := I.hn2
  rcases ha with ha | ⟨ha1, ha2⟩ | ha
  · rw [Function.update_of_ne (by omega)]; exact hfr a (Or.inl ha) (Or.inl (by omega))
  · rw [Function.update_of_ne (by omega)]; exact hfr a (Or.inr (by omega)) (Or.inl ha2)
  · rw [Function.update_of_ne (by omega)]; exact hfr a (Or.inr (by omega)) (Or.inr (Or.inr ha))

/-- The pre of the order call, after the rooting call and the store. -/
lemma orderPhase_orderPre {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₁ : ℕ → ℕ} {v₁ : ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hpost : (rootStageContract w).post
      [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁) :
    (orderStageContract w h G₀ vList eList).pre
      [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
        dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
        X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n, X.auxPar + X.n + X.n,
        X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr, tPiBase X.tPtr X.vCap X.tM,
        X.minPtr]
      (Function.update mem₁ (X.auxPar + X.n) 0) := by
  obtain ⟨n', m', tailArr', headArr', r', outPtr', sPtr', auxPar', logCap', tl, hd, heq, -, hends,
    hR, ⟨Q, hQ, hQat⟩, hup, hfr⟩ := hpost
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  set mem₂ := Function.update mem₁ (X.auxPar + X.n) 0 with hmem₂
  have hfr₂ : ∀ a, (a < X.auxPar ∨ (X.minPtr ≤ a ∧ a < X.rtOut) ∨
      X.sPtr + 4 * X.n + 2 * X.tM ≤ a) → mem₂ a = mem a := orderPhase_frame₂ I hfr
  have hqo : X.qOrd = X.sPtr + X.n + 2 * X.tM + X.n := rfl
  have hn := I.hn2
  have hmin := I.hmin
  have hl := (show 1 ≤ X.logCap by rw [I.hlog]; unfold auxLogCap; omega)
  -- the arrays of the tree in `mem₂`
  have hA3 : ∀ x, x < 3 * X.n → x ≠ X.n → mem₂ (X.auxPar + x) = mem₁ (X.auxPar + x) :=
    fun x _ hx => Function.update_of_ne (by omega) _ _
  have hR₂ : RootedArrays X.n X.tM 0 tl hd (fun x => mem₂ (X.auxPar + x))
      (fun x => mem₂ (X.auxPar + X.n + x)) (fun x => mem₂ (X.auxPar + X.n + X.n + x)) := by
    have h1 := hR.congr (par' := fun x => mem₂ (X.auxPar + x))
      (pe' := fun x => mem₁ (X.auxPar + X.n + x)) (dep' := fun x => mem₂ (X.auxPar + X.n + X.n + x))
      (by omega) (fun x hx => (hA3 x (by omega) (by omega)).symm) (fun _ _ => rfl)
      (fun x hx => by
        show mem₁ _ = mem₂ _
        rw [show X.auxPar + X.n + X.n + x = X.auxPar + (X.n + X.n + x) by omega,
          hA3 _ (by omega) (by omega)])
    refine RootedArrays.congr_pe_root h1 fun x hx hx0 => ?_
    show mem₁ _ = mem₂ _
    rw [show X.auxPar + X.n + x = X.auxPar + (X.n + x) by omega, hA3 _ (by omega) (by omega)]
  have hdep : ∀ x < X.n, mem₂ (X.auxPar + X.n + X.n + x) < X.n := fun x hx => hR₂.dep_lt hx
  have hupT : ∀ i < X.n, ∀ j < X.logCap, mem₂ (X.auxPar + 3 * X.n + (i * X.logCap + j)) =
      liftF (fun x => mem₂ (X.auxPar + x)) i j := by
    intro i hi j hj
    have hij : i * X.logCap + j < X.n * X.logCap := by
      calc i * X.logCap + j < i * X.logCap + X.logCap := by omega
        _ = (i + 1) * X.logCap := by ring
        _ ≤ X.n * X.logCap := Nat.mul_le_mul_right _ hi
    rw [hmem₂, Function.update_of_ne (by omega), hup i hi j hj]
    exact liftF_congr (fun x hx => hR.par_lt x hx) (fun x hx => (hA3 x (by omega) (by omega)).symm)
      j i hi
  have hnL : X.n < 2 ^ X.logCap := by
    rw [I.hlog]; unfold auxLogCap
    have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (X.n + 1)
    omega
  have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15; have l16 := I.l16
  have l17 := I.l17; have l18 := I.l18; have l19 := I.l19; have l5 := I.l5; have l6 := I.l6
  have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10; have l11 := I.l11
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4
  have htb : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.tPtr + tBlockSize X.vCap X.eCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hgE : dgEListBase X.gPtr X.vCap X.eCap + X.m0 ≤ X.gPtr + dynGraphSize X.vCap X.eCap := by
    have := I.hme
    simp only [dgEListBase, dynGraphSize]; omega
  have htP : X.gPtr + dynGraphSize X.vCap X.eCap ≤ tPiBase X.tPtr X.vCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr]; omega
  refine ⟨X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, X.vIdx, X.eu, X.ev, X.qPtr, X.Kq, X.dPtr,
    X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, X.auxPar, X.qOrd,
    X.auxPar + X.n, X.arrPtr, X.scratchPtr, tPiBase X.tPtr X.vCap X.tM, X.minPtr, X.tM, X.gPtr,
    X.vCap, X.eCap, tl, hd, Q, rfl, ?_, ?_, I.heLen, I.heE, ?_, fun u hu => (I.hGV u).mp hu,
    I.hvlen.symm, I.hh, I.hhw, I.hw16, I.hK, I.hKq, by omega, by omega, hR₂, ?_, ?_, ?_, ?_, ?_, ?_,
    htP, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
    Or.inl (by omega), by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    Or.inl (by omega), Or.inl (by omega), by omega⟩
  · exact I.hdg.of_agree fun a ha1 ha2 => hfr₂ a (Or.inl (by omega))
  · exact I.heL.congr fun k hk1 hk2 => hfr₂ k (Or.inl (by rw [I.heLen] at hk2; omega))
  · intro i hi
    have hv := I.hvCap _ (List.getElem_mem hi)
    rw [hfr₂ _ (Or.inl (by omega))]
    exact I.hvI i hi
  · show mem₂ (X.auxPar + X.n + 0) < X.tM
    rw [hmem₂, add_zero, Function.update_self, I.htM]; omega
  · exact hQ.congr fun x hx => (hA3 x (by omega) (by omega)).symm
  · exact hQat.congr fun k hk1 hk2 => by
      rw [hQ.len] at hk2
      show mem₂ k = mem₁ k
      rw [hmem₂, Function.update_of_ne (by omega)]
  · exact ⟨hl, fun x hx => lt_trans (hdep x hx) hnL, hupT, fun i hi => rfl, fun i hi => rfl,
      by omega, by omega, by omega⟩
  · intro t ht
    have := I.hq t ht
    intro i hi
    rw [hfr₂ _ (Or.inr (Or.inl ⟨by
      have : t * X.Kq + i < X.m0 * X.Kq := by
        calc t * X.Kq + i < t * X.Kq + X.Kq := by omega
          _ = (t + 1) * X.Kq := by ring
          _ ≤ X.m0 * X.Kq := Nat.mul_le_mul_right _ ht
      omega, by
      have : t * X.Kq + i < X.m0 * X.Kq := by
        calc t * X.Kq + i < t * X.Kq + X.Kq := by omega
          _ = (t + 1) * X.Kq := by ring
          _ ≤ X.m0 * X.Kq := Nat.mul_le_mul_right _ ht
      omega⟩))]
    exact this i hi
  · have hsum : ∀ t ∈ Finset.range X.m0, unsignedVal mem₂ (X.qPtr + t * X.Kq) h X.Kq =
        unsignedVal mem (X.qPtr + t * X.Kq) h X.Kq := by
      intro t ht
      have ht' := Finset.mem_range.mp ht
      refine unsignedVal_congr fun i hi => ?_
      have : t * X.Kq + i < X.m0 * X.Kq := by
        calc t * X.Kq + i < t * X.Kq + X.Kq := by omega
          _ = (t + 1) * X.Kq := by ring
          _ ≤ X.m0 * X.Kq := Nat.mul_le_mul_right _ ht'
      exact hfr₂ _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    rw [Finset.sum_congr rfl hsum]
    exact I.hqs

end

end MinCostFlow.LSF.Program
