module

public import MinCostFlow.LSF.Program.DecompPhase

/-!
# What the decomposition phase needs

`DecompPhaseIn` lists what the memory holds at the start of the decomposition phase: the rooted
arrays of `T₀` and the ancestor tables in the aux block, the top-down order, the parents and
depths of `T_H`, the endpoint arrays, the lengths, the component representatives, a zero scratch
area, and the layout. All inputs lie below `dBase`; the scratch areas follow in the order
`dBase` (`12 n` words), `hiCopy`, `inR` (with `mp`, `own`, `rt`), `numS`, `denS`, `idPtr`.

`decompPhase_wstrPre` gives the pre of the stretch pass on any memory that agrees with the start
memory below `dBase`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The memory at the start of the decomposition phase. -/
structure DecompPhaseIn (w h C : ℕ) (T₀ : MGraph) (vList : List ℕ) (X : DecompLayout)
    (mem : ℕ → ℕ) : Prop where
  hw16 : 16 ≤ 2 ^ w
  hh : 1 ≤ h
  hn : 0 < X.n
  hvlen : vList.length = X.n
  hnd : vList.Nodup
  hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList
  hT : IsRootedTree T₀ (vList.getD 0 0)
  hLin1 : 1 ≤ X.Lin
  hLinw : X.Lin ≤ X.Lw
  hnO : X.nOrig ≤ X.tM
  hC : C < 2 ^ (h * X.Lw)
  hD : X.D = hldDepthBound X.n
  hDw : 2 * (X.D + 1) < 2 ^ w
  htree : ∃ (Q : List ℕ) (tl hd dep : ℕ → ℕ),
    TopDownOrder X.n 0 (fun x => mem (X.auxPar + x)) Q ∧ ListAt mem X.qOrd Q ∧
    RootedArrays X.n X.tM 0 tl hd (fun x => mem (X.auxPar + x)) (fun x => mem (X.auxPar + X.n + x))
      dep ∧
    LcaTables w X.n X.logCap (X.auxPar + 3 * X.n) (X.auxPar + X.n + X.n) X.auxPar
      (fun x => mem (X.auxPar + x)) dep mem ∧
    T0IndexArrays T₀ vList X.tM (fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) tl hd
  hthPar : ∀ x < X.n, x ≠ 0 → mem (X.thDst + x) < X.n ∧
    vList.getD (mem (X.thDst + x)) 0 = thParent T₀ (vList.getD 0 0) (vList.getD x 0)
  hthDep : ∀ x < X.n, mem (X.thBase + 7 * X.n + x) =
    depth (hldAuxTree T₀ (vList.getD 0 0)) (vList.getD 0 0) (vList.getD x 0)
  hlenT : ∀ i < X.nOrig, Valid mem (X.lenArr + mem (tOrigIdBase X.tPtr X.vCap X.tM + i) * X.Lin)
    h X.Lin ∧
    X.lenArr + mem (tOrigIdBase X.tPtr X.vCap X.tM + i) * X.Lin + wstrLB X.n X.D X.Lw ≤ X.dBase
  hlenE : ∀ t < X.m0,
    Valid mem (X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin) h X.Lin ∧
    X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin + wstrLB X.n X.D X.Lw ≤ X.dBase
  heLt : ∀ t < X.m0, mem (dgEListBase X.gPtr X.vCap X.eCap + t) < X.eCap
  heInj : ∀ t < X.m0, ∀ t' < X.m0, mem (dgEListBase X.gPtr X.vCap X.eCap + t) =
    mem (dgEListBase X.gPtr X.vCap X.eCap + t') → t = t'
  heuv : ∀ t < X.m0, mem (X.eu + t) < X.n ∧ mem (X.ev + t) < X.n
  hzD : ∀ a, X.dBase ≤ a → a < X.dBase + 12 * X.n → mem a = 0
  hθ : 0 < X.θ
  hθw : 3 * X.θ < 2 ^ w
  hm0w : 2 * X.m0 < 2 ^ w
  hrep : ∀ j < X.cnt, mem (X.repPtr + j) < X.vCap ∧ repIdx mem X.repPtr X.vIdx j < X.n
  hroot : ∃ j < X.cnt, repIdx mem X.repPtr X.vIdx j = 0
  hLB : wstrLB X.n X.D X.Lw < 2 ^ w
  hk : X.k < 2 ^ w
  -- the inputs lie below `dBase`
  L1 : X.lenArr + wstrLB X.n X.D X.Lw ≤ X.dBase
  L2 : tOrigIdBase X.tPtr X.vCap X.tM + X.tM ≤ X.dBase
  L3 : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.dBase
  L4 : dgEListBase X.gPtr X.vCap X.eCap + X.m0 ≤ X.dBase
  L4s : dgEListBase X.gPtr X.vCap X.eCap + X.m0 ≤ X.numSt
  L5 : X.auxPar + 3 * X.n + X.n * X.logCap ≤ X.dBase
  L6 : X.qOrd + X.n ≤ X.dBase
  L7 : X.eu + X.m0 ≤ X.dBase
  L8 : X.ev + X.m0 ≤ X.dBase
  L9 : X.thDst + X.n ≤ X.dBase
  L10 : X.thBase + 8 * X.n ≤ X.dBase
  L11 : X.repPtr + X.cnt ≤ X.dBase
  L12 : X.vIdx + X.vCap ≤ X.dBase
  L13 : X.numSt + X.eCap * X.Lw ≤ X.denSt
  L14 : X.denSt + X.eCap * X.Lw ≤ X.dBase
  -- the scratch areas
  L15 : X.dBase + 12 * X.n ≤ X.hiCopy
  L16 : X.hiCopy + X.m0 ≤ X.inR
  L17 : X.inR + 3 * X.n + X.tM ≤ X.numS
  L18 : X.numS + 2 * (X.eCap * X.Lw) ≤ X.idPtr
  L19 : wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 + X.m0 < 2 ^ w

lemma capacity_ge_of_le {h L L' : ℕ} (hL : L ≤ L') : 2 ^ (h * L) ≤ capacity h L' := by
  rw [capacity, base, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hL)

lemma lw_le_wstrLB (n D Lw : ℕ) : Lw ≤ wstrLB n D Lw := by unfold wstrLB; omega

/-- The pre of the stretch pass, on a memory that agrees with the start memory below `dBase`. -/
lemma decompPhase_wstrPre {w h C : ℕ} {T₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem mem₁ : ℕ → ℕ} (I : DecompPhaseIn w h C T₀ vList X mem)
    (hfr : ∀ a < X.dBase, mem₁ a = mem a) :
    (wstrStageContract w h C).pre
      [X.n, X.tM, X.m0, X.k, wstrLB X.n X.D X.Lw, X.Lw, X.Lin, X.nOrig, 0, X.logCap, X.lenArr,
        tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar, X.auxPar + X.n,
        tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev, X.auxPar + 3 * X.n,
        X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS, X.denS, X.idPtr] mem₁ := by
  have hn := I.hn
  have L1 := I.L1; have L2 := I.L2; have L3 := I.L3; have L4 := I.L4; have L5 := I.L5
  have L6 := I.L6; have L7 := I.L7; have L8 := I.L8; have L9 := I.L9; have L10 := I.L10
  have L15 := I.L15; have L16 := I.L16; have L17 := I.L17; have L18 := I.L18; have L19 := I.L19
  have hden : X.denS = X.numS + X.eCap * X.Lw := rfl
  set LB := wstrLB X.n X.D X.Lw with hLBdef
  have hLwB : X.Lw ≤ LB := lw_le_wstrLB _ _ _
  have hpt : ∀ j ≤ 18, wsPt X.idPtr X.n X.tM X.m0 LB j ≤ wsPt X.idPtr X.n X.tM X.m0 LB 18 :=
    fun j hj => wsPt_mono _ _ _ _ _ hj
  have hpt0 : wsPt X.idPtr X.n X.tM X.m0 LB 1 = X.idPtr + X.n := rfl
  have hp1 := hpt 1 (by omega)
  obtain ⟨Q, tl, hd, dep, hQ, hQat, hRA, hLT, -⟩ := I.htree
  obtain ⟨hQ₁, hQat₁, hRA₁, hLT₁⟩ := treeIn_transfer (B := X.dBase) (mem' := mem₁) (by omega) hQ hQat
    hRA hLT hfr (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨-, -, hth0⟩ := thArrays_parDep (dep := fun x => mem (X.thBase + 7 * X.n + x))
    (par := fun x => mem (X.thDst + x)) I.hT I.hnd I.hV I.hvlen hn I.hthPar I.hthDep
  have hfid : ∀ i < X.nOrig, mem₁ (tOrigIdBase X.tPtr X.vCap X.tM + i) =
      mem (tOrigIdBase X.tPtr X.vCap X.tM + i) := fun i hi => hfr _ (by have := I.hnO; omega)
  have heL : ∀ t < X.m0, mem₁ (dgEListBase X.gPtr X.vCap X.eCap + t) =
      mem (dgEListBase X.gPtr X.vCap X.eCap + t) := fun t ht => hfr _ (by omega)
  have hLinB : X.Lin ≤ LB := le_trans I.hLinw hLwB
  have hValid : ∀ a, a + LB ≤ X.dBase → Valid mem a h X.Lin → Valid mem₁ a h X.Lin :=
    fun a ha hv i hi => by rw [hfr _ (by omega)]; exact hv i hi
  refine ⟨by simp [wstrStageArgs], by simpa using (show wsPt X.idPtr X.n X.tM X.m0 LB 18 < 2 ^ w
    by omega), ?_⟩
  refine ⟨X.n, X.tM, X.m0, X.k, LB, X.Lw, X.Lin, X.nOrig, 0, X.logCap, X.lenArr,
    tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar, X.auxPar + X.n,
    tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev, X.auxPar + 3 * X.n,
    X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS, X.denS, X.idPtr,
    wsPt X.idPtr X.n X.tM X.m0 LB 1, wsPt X.idPtr X.n X.tM X.m0 LB 2,
    wsPt X.idPtr X.n X.tM X.m0 LB 3, wsPt X.idPtr X.n X.tM X.m0 LB 4,
    wsPt X.idPtr X.n X.tM X.m0 LB 5, wsPt X.idPtr X.n X.tM X.m0 LB 6,
    wsPt X.idPtr X.n X.tM X.m0 LB 7, wsPt X.idPtr X.n X.tM X.m0 LB 8,
    wsPt X.idPtr X.n X.tM X.m0 LB 9, wsPt X.idPtr X.n X.tM X.m0 LB 10,
    wsPt X.idPtr X.n X.tM X.m0 LB 11, wsPt X.idPtr X.n X.tM X.m0 LB 12,
    wsPt X.idPtr X.n X.tM X.m0 LB 13, wsPt X.idPtr X.n X.tM X.m0 LB 14,
    wsPt X.idPtr X.n X.tM X.m0 LB 15, wsPt X.idPtr X.n X.tM X.m0 LB 16,
    wsPt X.idPtr X.n X.tM X.m0 LB 17, wsPt X.idPtr X.n X.tM X.m0 LB 18, rfl, ?_⟩
  refine ⟨I.hw16, hn, I.hLin1, I.hLinw, hLwB, I.hnO, hn, ?_, ?_, by omega,
    ⟨Q, tl, hd, dep, hQ₁, hQat₁, hRA₁, hLT₁⟩, ?_, ?_, ?_, by omega, ?_,
    ⟨X.eCap, fun t ht => (heL t ht).symm ▸ I.heLt t ht,
      fun t ht t' ht' h => I.heInj t ht t' ht' (by rw [← heL t ht, ← heL t' ht']; exact h),
      by omega, by omega⟩,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, ?_⟩
  · exact lt_of_lt_of_le I.hC (capacity_ge_of_le hLwB)
  · rw [← I.hD]; exact I.hDw
  · rw [hfr _ (by omega)]; exact hth0
  · intro i hi
    rw [hfid i hi]
    obtain ⟨hv, hlt⟩ := I.hlenT i hi
    exact ⟨hValid _ hlt hv, by omega⟩
  · intro t ht
    rw [heL t ht]
    obtain ⟨hv, hlt⟩ := I.hlenE t ht
    exact ⟨hValid _ hlt hv, by omega⟩
  · intro t ht
    rw [hfr _ (by omega), hfr _ (by omega)]
    exact I.heuv t ht
  · simp only [wsPt, wsStep] at hpt L19 ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩

end

end MinCostFlow.LSF.Program
