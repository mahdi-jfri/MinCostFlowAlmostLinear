module

public import MinCostFlow.LSF.Program.OrderPhaseFrame
public import MinCostFlow.LSF.Program.DecompPhaseIn

/-!
# From the order phase to the decomposition phase

`decompIn_of_order` shows that the memory after the order phase satisfies `DecompPhaseIn`, for the
layout `DecompLayout.ofOrder` that keeps the places of the order phase. The facts come from three
sources: the posts of the calls of the order phase (the rooted arrays, the order `Q`, the ancestor
table, the endpoint arrays, the `T` block and the arrays of `T_H`), `OrderPhaseIn`, and the facts
`DecompExtra` about the lengths, the edge list, the representatives and the numbers of the phase.
`orderPhase_frame` moves each of them to the final memory.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The layout of the decomposition phase that keeps the places of the order phase. -/
def DecompLayout.ofOrder (X : OrderLayout) (θ dBase D Lw k Lin lenArr numS idPtr hiCopy cnt repPtr
    inR numSt denSt : ℕ) : DecompLayout where
  n := X.n
  m0 := X.m0
  eu := X.eu
  ev := X.ev
  qOrd := X.qOrd
  auxPar := X.auxPar
  θ := θ
  dBase := dBase
  D := D
  Lw := Lw
  tM := X.tM
  k := k
  Lin := Lin
  nOrig := X.nOrig
  logCap := X.logCap
  lenArr := lenArr
  tPtr := X.tPtr
  vCap := X.vCap
  eCap := X.eCap
  gPtr := X.gPtr
  thBase := X.thBase
  thDst := X.thDst
  numS := numS
  idPtr := idPtr
  hiCopy := hiCopy
  cnt := cnt
  repPtr := repPtr
  vIdx := X.vIdx
  inR := inR
  numSt := numSt
  denSt := denSt

/-- The facts that the decomposition phase needs beyond the order phase, on the memory at the
start of the order phase. -/
structure DecompExtra (w h C : ℕ) (G₀ : MGraph) (vList eList repList : List ℕ) (X : OrderLayout)
    (Y : DecompLayout) (mem : ℕ → ℕ) : Prop where
  hLin1 : 1 ≤ Y.Lin
  hLinw : Y.Lin ≤ Y.Lw
  hC : C < 2 ^ (h * Y.Lw)
  hD : Y.D = hldDepthBound X.n
  hDw : 2 * (Y.D + 1) < 2 ^ w
  hθ : 0 < Y.θ
  hθw : 3 * Y.θ < 2 ^ w
  hm0w : 2 * X.m0 < 2 ^ w
  hLB : wstrLB X.n Y.D Y.Lw < 2 ^ w
  hk : Y.k < 2 ^ w
  hlenG : ∀ e ∈ G₀.E, Valid mem (Y.lenArr + e * Y.Lin) h Y.Lin ∧ e < X.eCap ∧
    Y.lenArr + e * Y.Lin + Y.Lin ≤ X.tPtr ∧ Y.lenArr + e * Y.Lin + wstrLB X.n Y.D Y.Lw ≤ Y.dBase
  heNd : eList.Nodup
  hrepAt : ListAt mem Y.repPtr repList
  hrepLen : repList.length = Y.cnt
  hrepV : ∀ v ∈ repList, v ∈ vList
  hrep0 : repList.getD 0 0 = vList.getD 0 0
  hcnt : 1 ≤ Y.cnt
  hrepLay : X.thDst + X.n ≤ Y.repPtr ∧ Y.repPtr + Y.cnt ≤ X.rtOut
  hzD : ∀ a, Y.dBase ≤ a → a < Y.dBase + 12 * X.n → mem a = 0
  L1 : Y.lenArr + wstrLB X.n Y.D Y.Lw ≤ Y.dBase
  L10 : X.thBase + 8 * X.n ≤ Y.dBase
  L12s : X.tPtr ≤ Y.numSt
  L13 : Y.numSt + X.eCap * Y.Lw ≤ Y.denSt
  L14 : Y.denSt + X.eCap * Y.Lw ≤ Y.dBase
  L15 : Y.dBase + 12 * X.n ≤ Y.hiCopy
  L16 : Y.hiCopy + X.m0 ≤ Y.inR
  L17 : Y.inR + 3 * X.n + X.tM ≤ Y.numS
  L18 : Y.numS + 2 * (X.eCap * Y.Lw) ≤ Y.idPtr
  L19 : wsPt Y.idPtr X.n X.tM X.m0 (wstrLB X.n Y.D Y.Lw) 18 + X.m0 < 2 ^ w

/-- An entry of a list below its length is in the list. -/
lemma getD_mem_of_lt {l : List ℕ} {t : ℕ} (h : t < l.length) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- The memory after the order phase satisfies `DecompPhaseIn`. -/
theorem decompIn_of_order {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {θ dBase D Lw k Lin lenArr numS idPtr hiCopy cnt repPtr inR numSt denSt : ℕ}
    {mem mem₁ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₁ v₃ v₄ v₅ : ℕ} {repList : List ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (E : DecompExtra w h C G₀ vList eList repList X (DecompLayout.ofOrder X θ dBase D Lw k Lin lenArr numS
      idPtr hiCopy cnt repPtr inR numSt denSt) mem)
    (h₁ : (rootStageContract w).post
        [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁)
    (h₃ : (orderStageContract w h G₀ vList eList).post
        [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
          dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
          X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n,
          X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr,
          tPiBase X.tPtr X.vCap X.tM, X.minPtr]
        (Function.update mem₁ (X.auxPar + X.n) 0) v₃ mem₃)
    (h₄ : (tStageContract w G₀ T₀ vList).post [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr,
        X.tOrigSrc, X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM,
        tDgTPtr X.tPtr] mem₃ v₄ mem₄)
    (h₅ : (thStageContract w T₀ vList).post
        [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] mem₄ v₅ mem₅) :
    DecompPhaseIn w h C T₀ vList (DecompLayout.ofOrder X θ dBase D Lw k Lin lenArr numS idPtr
      hiCopy cnt repPtr inR numSt denSt) mem₅ := by
  obtain ⟨hFr, hAux, hS, h53, hTB, -⟩ := orderPhase_frame I h₁ h₃ h₄ h₅
  have hn := I.hn2; have hmin := I.hmin
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have l19 := I.l19
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  have ht0 : tOrigIdBase X.tPtr X.vCap X.tM + X.tM = tPiBase X.tPtr X.vCap X.tM := rfl
  have ht3 : X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ X.vIdx := l2
  have htt : X.tPtr ≤ tOrigIdBase X.tPtr X.vCap X.tM := by
    simp only [tOrigIdBase, tDgTPtr]; omega
  have htb : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.tPtr + tBlockSize X.vCap X.eCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hgE : dgEListBase X.gPtr X.vCap X.eCap + X.m0 ≤ X.tPtr := by
    have := I.hme
    simp only [dgEListBase, dynGraphSize] at l1 ⊢; omega
  have hl := (show 1 ≤ X.logCap by rw [I.hlog]; unfold auxLogCap; omega)
  have hnL : X.n < 2 ^ X.logCap := by
    rw [I.hlog]; unfold auxLogCap
    have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (X.n + 1)
    omega
  have hnnL : X.n ≤ X.n * X.logCap := Nat.le_mul_of_pos_right _ hl
  have EL1 := E.L1; have EL10 := E.L10; have EL12s := E.L12s; have EL13 := E.L13; have EL14 := E.L14
  have EL15 := E.L15; have EL16 := E.L16; have EL17 := E.L17; have EL18 := E.L18
  have EL19 := E.L19; have Erep := E.hrepLay; have Ecnt := E.hcnt
  dsimp only [DecompLayout.ofOrder] at EL1 EL10 EL12s EL13 EL14 EL15 EL16 EL17 EL18 EL19 Erep Ecnt
  have ErepLen := E.hrepLen; have ErepAt := E.hrepAt; have ElenG := E.hlenG; have EzD := E.hzD
  dsimp only [DecompLayout.ofOrder] at ErepLen ErepAt ElenG EzD
  -- the posts
  obtain ⟨_, _, _, _, _, _, _, _, _, tl, hd, heq, -, hends, hR, ⟨Q, hQ, hQat⟩, hup, -⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, heu,
    hev, -, -, -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, hTBA, -, -⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hIdAt, -⟩ := hTBA
  obtain ⟨_, _, _, _, _, _, _, heq₅, -, hthP, -, hthD, -⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  have hqo : X.qOrd = X.sPtr + X.n + 2 * X.tM + X.n := rfl
  -- the arrays of the rooting in the final memory
  have hpar : ∀ x < X.n, mem₁ (X.auxPar + x) = mem₅ (X.auxPar + x) := fun x hx =>
    (hAux _ (by omega) (by omega) (by omega)).symm
  have hdep : ∀ x < X.n, mem₁ (X.auxPar + X.n + X.n + x) = mem₅ (X.auxPar + X.n + X.n + x) :=
    fun x hx => (hAux _ (by omega) (by omega) (by omega)).symm
  have hR₅ : RootedArrays X.n X.tM 0 tl hd (fun x => mem₅ (X.auxPar + x))
      (fun x => mem₅ (X.auxPar + X.n + x)) (fun x => mem₅ (X.auxPar + X.n + X.n + x)) :=
    RootedArrays.congr_pe_root (hR.congr (by omega) hpar (fun _ _ => rfl) hdep)
      fun x hx hx0 => (hAux _ (by omega) (by omega) (by omega)).symm
  -- the vertex index table and the edge ids
  have hvI₅ : ∀ i (hi : i < vList.length), mem₅ (X.vIdx + vList[i]) = i + 1 := fun i hi => by
    have := I.hvCap _ (List.getElem_mem hi)
    rw [hFr _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact I.hvI i hi
  have hfid : ∀ i < X.tM, mem₅ (tOrigIdBase X.tPtr X.vCap X.tM + i) = mem (X.tOrigSrc + i) := by
    intro i hi
    have h1 := hIdAt i (by simp [tStageList]; omega)
    simp only [tStageList, List.getElem_map, List.getElem_range] at h1
    rw [hTB _ (by omega) (by omega), h1, ← h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      hFr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]
  have heL₅ : ∀ t < X.m0, mem₅ (dgEListBase X.gPtr X.vCap X.eCap + t) = eList.getD t 0 :=
    fun t ht => by
      rw [hFr _ (Or.inl (by omega)), List.getD_eq_getElem _ _ (by rw [I.heLen]; omega)]
      exact I.heL t (by rw [I.heLen]; omega)
  have hValid : ∀ a, a + Lin ≤ X.tPtr → Valid mem a h Lin → Valid mem₅ a h Lin :=
    fun a ha hv i hi => by rw [hFr _ (Or.inl (by omega))]; exact hv i hi
  have hrep₅ : ∀ j < cnt, mem₅ (repPtr + j) = repList.getD j 0 :=
    fun j hj => by
      rw [hFr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))),
        List.getD_eq_getElem _ _ (by rw [ErepLen]; omega)]
      exact ErepAt j (by rw [ErepLen]; omega)
  have hrepIdx : ∀ j < cnt, ∃ i < X.n, repIdx mem₅ repPtr X.vIdx j = i ∧
      repList.getD j 0 = vList.getD i 0 := by
    intro j hj
    have hjl : j < repList.length := by rw [ErepLen]; omega
    obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem (E.hrepV _ (List.getElem_mem hjl))
    refine ⟨i, by rw [← I.hvlen]; exact hi, ?_, by
      rw [List.getD_eq_getElem _ _ hi, hvi, List.getD_eq_getElem _ _ hjl]⟩
    unfold repIdx
    rw [hrep₅ j hj, List.getD_eq_getElem _ _ hjl, ← hvi, hvI₅ i hi]
    omega
  refine ⟨I.hw16, I.hh, by (try dsimp only [DecompLayout.ofOrder] at *); omega, I.hvlen, I.hnd, I.hV, I.hT, E.hLin1, E.hLinw, I.hnO, E.hC, E.hD,
    E.hDw, ⟨Q, tl, hd, fun x => mem₅ (X.auxPar + X.n + X.n + x),
      hQ.congr hpar, hQat.congr fun k hk1 hk2 => hS k (by (try dsimp only [DecompLayout.ofOrder] at *); omega) (by rw [hQ.len] at hk2; omega),
      hR₅, ⟨hl, fun x hx => lt_trans (hR₅.dep_lt hx) hnL, fun i hi j hj => ?_, fun _ _ => rfl,
        fun _ _ => rfl, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega⟩,
      I.hA.congr (fun i hi => (hfid i hi).symm) (fun f hf => (hends f hf).1)
        (fun f hf => (hends f hf).2)⟩,
    hthP, hthD, ?_, ?_, ?_, ?_, ?_, ?_, E.hθ, E.hθw, E.hm0w, ?_, ?_, E.hLB, E.hk, EL1, ?_, ?_, ?_,
    by (try dsimp only [DecompLayout.ofOrder] at *); omega,
    by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, EL10, by (try dsimp only [DecompLayout.ofOrder] at *); omega, by (try dsimp only [DecompLayout.ofOrder] at *); omega, EL13, EL14, EL15,
    EL16, EL17, EL18, EL19⟩
  all_goals try dsimp only [DecompLayout.ofOrder] at *
  · -- the ancestor table
    have hij : i * X.logCap + j < X.n * X.logCap := by
      calc i * X.logCap + j < i * X.logCap + X.logCap := by omega
        _ = (i + 1) * X.logCap := by ring
        _ ≤ X.n * X.logCap := Nat.mul_le_mul_right _ hi
    rw [hAux _ (by omega) (by omega) (by omega), hup i hi j hj]
    exact liftF_congr (fun x hx => hR.par_lt x hx) hpar j i hi
  · intro i hi
    rw [hfid i (by have := I.hnO; omega)]
    obtain ⟨hv, -, hb1, hb2⟩ := ElenG _ ((I.hO i (by have := I.hnO; omega)).mpr hi)
    exact ⟨hValid _ hb1 hv, hb2⟩
  · intro t ht
    rw [heL₅ t ht]
    have he := I.heE _ (getD_mem_of_lt (show t < eList.length by rw [I.heLen]; omega))
    obtain ⟨hv, -, hb1, hb2⟩ := ElenG _ he
    exact ⟨hValid _ hb1 hv, hb2⟩
  · intro t ht
    rw [heL₅ t ht]
    exact (ElenG _ (I.heE _ (getD_mem_of_lt (show t < eList.length by rw [I.heLen]; omega)))).2.1
  · intro t ht t' ht' h'
    rw [heL₅ t ht, heL₅ t' ht', List.getD_eq_getElem _ _ (by rw [I.heLen]; omega),
      List.getD_eq_getElem _ _ (by rw [I.heLen]; omega)] at h'
    exact (E.heNd.getElem_inj_iff).mp h'
  · intro t ht
    have h1 := (heu t (by rw [I.heLen]; omega)).1
    have h2 := (hev t (by rw [I.heLen]; omega)).1
    rw [h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    rw [I.hvlen] at h1 h2
    exact ⟨h1, h2⟩
  · intro a ha1 ha2
    rw [hFr a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))))]
    exact EzD a ha1 ha2
  · intro j hj
    obtain ⟨i, hi, hidx, hv⟩ := hrepIdx j hj
    refine ⟨?_, by rw [hidx]; exact hi⟩
    rw [hrep₅ j hj, hv]
    exact I.hvCap _ (getD_mem_of_lt (by rw [I.hvlen]; omega))
  · obtain ⟨i, hi, hidx, hv⟩ := hrepIdx 0 (by omega)
    refine ⟨0, by omega, ?_⟩
    rw [hidx]
    rw [E.hrep0] at hv
    have hlen : 0 < vList.length := by rw [I.hvlen]; omega
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ (by rw [I.hvlen]; omega)] at hv
    exact ((I.hnd.getElem_inj_iff).mp hv).symm
  · simp only [tOrigIdBase, tDgTPtr] at ht0 ⊢; omega
  · omega
  · omega

end

end MinCostFlow.LSF.Program
