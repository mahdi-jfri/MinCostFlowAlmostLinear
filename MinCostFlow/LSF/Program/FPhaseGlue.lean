module

public import MinCostFlow.LSF.Program.DecompFrame
public import MinCostFlow.LSF.Program.FPhase

/-!
# From the decomposition phase to the forest phase

`fIn_of_decomp` gives the pre `FPhaseIn` of the forest phase on the memory after the
decomposition phase. The forest phase reads three kinds of arrays.

* Arrays that the decomposition phase does not touch: the vertex list, the `T` arrays, the
  parents and parent edges of the rooting, and three zero areas (the static `F` and `FAnc`
  blocks and a part of the work area). Their facts hold in the start memory (`FExtra`) and move
  over by `decompPhase_frame`.
* The labels of `decompWTProc`. They are below `n` (the last part of `DecompWTOut`).
* The owner and root arrays of `rootsStageProc`. The roots are below `n` by
  `rt_lt_of_rooted`: a root is the vertex itself, the owner of the parent edge, or the root of
  the parent, and induction on the depth shows that all three are indices.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The roots of `RtRule` are indices. -/
lemma rt_lt_of_rooted {n tM r : ℕ} {tl hd par pe dep inR mp own rt : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (hr : r < n)
    (hown : OwnState r tM inR mp own n) (hrt : rt r = r)
    (hrule : ∀ x < n, x ≠ r → RtRule inR par pe own rt x) :
    ∀ x < n, rt x < n := by
  suffices H : ∀ d, ∀ x < n, dep x = d → rt x < n from fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd
  by_cases hxr : x = r
  · rw [hxr, hrt]; exact hr
  obtain ⟨hpe, -, hdep⟩ := hR.step x hx hxr
  rw [hrule x hx hxr]
  split_ifs with h1 h2
  · exact hx
  · exact ((hown _ hpe).1 h2).1
  · exact ih _ (by omega) _ (hR.par_lt x hx) rfl

/-- The places of the forest phase, from those of the decomposition phase. The `F` graph has the
edge capacity `fECap X.eCap X.n`, which bounds the IDs of the bridges of `T₀`. -/
def FLayout.ofDecomp (X : DecompLayout) (dgF vListPtr tTail tHead fAnc wBase wPtr : ℕ) :
    FLayout where
  dgF := dgF
  vCap := X.vCap
  eCap := fECap X.eCap X.n
  n := X.n
  vListPtr := vListPtr
  tM := X.tM
  tTail := tTail
  tHead := tHead
  fid := tOrigIdBase X.tPtr X.vCap X.tM
  own := X.inR + X.n + X.n
  fAnc := fAnc
  inR := X.inR
  rt := X.inR + X.n + X.n + X.tM
  auxPar := X.auxPar
  dBase := X.dBase
  logCap := X.logCap
  wBase := wBase
  wPtr := wPtr

/-- The facts of the start memory that the forest phase reads, and the places of its arrays. -/
structure FExtra (w : ℕ) (X : DecompLayout) (dgF vListPtr tTail tHead fAnc wBase wPtr : ℕ)
    (mem : ℕ → ℕ) : Prop where
  hnv : X.n ≤ X.vCap
  hnL : X.n < 2 ^ X.logCap
  hzG : ∀ i < dynGraphSize X.vCap (fECap X.eCap X.n), mem (dgF + i) = 0
  hzA : ∀ i < fAncSize X.vCap, mem (fAnc + i) = 0
  hzW : ∀ y < X.n, mem (wBase + X.n * (3 * X.logCap) + 2 * X.n + y) = 0
  hvL : ∀ x < X.n, mem (vListPtr + x) < X.vCap
  hvInj : ∀ x < X.n, ∀ y < X.n, mem (vListPtr + x) = mem (vListPtr + y) → x = y
  hT : ∀ i < X.tM, mem (tTail + i) < X.n ∧ mem (tHead + i) < X.n ∧
    mem (tOrigIdBase X.tPtr X.vCap X.tM + i) < fECap X.eCap X.n
  -- the static blocks lie below the stretch arrays, the read arrays away from them and below
  -- `dBase`
  m1 : tOrigIdBase X.tPtr X.vCap X.tM + X.tM ≤ dgF
  m2 : dgF + dynGraphSize X.vCap (fECap X.eCap X.n) ≤ fAnc
  m3 : fAnc + fAncSize X.vCap ≤ wPtr
  m4 : wPtr + wBlockSize X.n ≤ X.numSt
  m5 : vListPtr + X.n ≤ X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ vListPtr
  m6 : tTail + X.tM ≤ X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ tTail
  m7 : tHead + X.tM ≤ X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ tHead
  m8 : X.auxPar + 2 * X.n ≤ X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ X.auxPar
  m9 : vListPtr + X.n ≤ X.dBase
  m10 : tTail + X.tM ≤ X.dBase
  m11 : tHead + X.tM ≤ X.dBase
  -- the work area lies above the scratch of the stretch pass
  m12 : wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 + X.m0 ≤ wBase
  m13 : wBase + wWorkSize X.n X.logCap < 2 ^ w
  -- the read arrays lie above the `W` block
  m14 : wPtr + wBlockSize X.n ≤ vListPtr
  m15 : wPtr + wBlockSize X.n ≤ tTail
  m16 : wPtr + wBlockSize X.n ≤ tHead
  m17 : wPtr + wBlockSize X.n ≤ X.auxPar

/-- The pre of the forest phase on the memory after the decomposition phase. -/
theorem fIn_of_decomp {w h C : ℕ} {T₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {dgF vListPtr tTail tHead fAnc wBase wPtr : ℕ}
    {mem m₁ m₃ m₄ m₅ m₆ m₇ mem₈ : ℕ → ℕ} {v₁ v₄ v₅ v₆ : ℕ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (E : FExtra w X dgF vListPtr tTail tHead fAnc wBase wPtr mem)
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
        (X.eCap * X.Lw) m₇ mem₈) :
    FPhaseIn w h (FLayout.ofDecomp X dgF vListPtr tTail tHead fAnc wBase wPtr) mem₈ := by
  obtain ⟨F1, F2, F3, F4, F5, -⟩ := decompPhase_frame I h₁ h₃ h₄ h₅ h₆ h₇ h₈
  have hn := I.hn
  have L5 := I.L5; have L13 := I.L13; have L14 := I.L14; have L15 := I.L15; have L16 := I.L16
  have L17 := I.L17; have L18 := I.L18
  have m1 := E.m1; have m2 := E.m2; have m3 := E.m3; have m4 := E.m4; have m5 := E.m5
  have m6 := E.m6; have m7 := E.m7; have m8 := E.m8; have m9 := E.m9; have m10 := E.m10
  have m11 := E.m11; have m12 := E.m12; have m14 := E.m14; have m15 := E.m15
  have m16 := E.m16; have m17 := E.m17
  have hid : X.idPtr ≤ wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 :=
    wsPt_mono X.idPtr X.n X.tM X.m0 _ (Nat.zero_le 18)
  obtain ⟨Q, tl, hd, dep, hQ, hQat, hR, hLca, -⟩ := I.htree
  -- the labels
  obtain ⟨_, _, _, _, _, _, _, _, _, heq₁, -, -, hO⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  obtain ⟨-, -, -, -, -, -, hlab⟩ := hO
  -- the roots
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, -, -, -, -, hown, hrt0, hrule⟩ := h₆
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  have hR₅ : RootedArrays X.n X.tM 0 tl hd (fun x => m₅ (X.auxPar + x))
      (fun x => m₅ (X.auxPar + X.n + x)) dep :=
    hR.congr hn (fun x hx => (F5 _ (by omega)).symm) (fun x hx => (F5 _ (by omega)).symm)
      fun _ _ => rfl
  have hrt := rt_lt_of_rooted hR₅ hn hown hrt0 hrule
  have hb1 : X.dBase + 12 * X.n ≤ wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 := by
    omega
  refine ⟨I.hw16, I.hh, hn, E.hnv, hLca.hL, E.hnL, fun i hi => ?_, fun i hi => ?_, fun y hy => ?_,
    fun x hx => ?_, fun x hx y hy hxy => ?_, fun i hi => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx hx0 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, E.m13⟩
  all_goals try dsimp only [FLayout.ofDecomp] at *
  · rw [F1 _ (by omega) (Or.inl (by omega))]; exact E.hzG i hi
  · rw [F1 _ (by omega) (Or.inl (by omega))]; exact E.hzA i hi
  · rw [F2 _ (by omega)]; exact E.hzW y hy
  · rw [F1 _ (by omega) (by omega)]; exact E.hvL x hx
  · rw [F1 _ (by omega) (by omega), F1 _ (by omega) (by omega)] at hxy
    exact E.hvInj x hx y hy hxy
  · rw [F1 _ (by omega) (by omega), F1 _ (by omega) (by omega),
      F1 _ (by omega) (Or.inl (by omega))]
    exact E.hT i hi
  · rw [F4 _ (by omega) (by omega)]; exact hrt x hx
  · rw [F3 _ (by omega) (by omega), F3 _ (by omega) (by omega)]; exact hlab x hx
  · rw [F1 _ (by omega) (by omega)]; exact hR.par_lt x hx
  · rw [F1 _ (by omega) (by omega)]; exact (hR.step x hx hx0).1
  all_goals omega

end

end MinCostFlow.LSF.Program
