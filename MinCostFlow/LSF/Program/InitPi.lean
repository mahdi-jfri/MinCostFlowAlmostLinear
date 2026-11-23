module

public import MinCostFlow.LSF.Program.OrderPhasePre
public import MinCostFlow.LSF.Program.CongOrderModel

/-!
# The edge order written by the order phase

The order phase ranks the tree edges and leaves the ranks in the `π` array of the `T` block.
`orderPi X mem mem'` reads the order as a function of the edge: edge `f` gets the rank at its
index in the list of tree edge IDs. `orderPhase_pi` shows that this order meets
`IsApproxCongOrder` with factor `5/4`, when the weight blocks at `qPtr` hold
`edgeMult · 2^S_div / ℓ_int` (`congOrder_isApproxCongOrder`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The position of `f i` in the list `f 0, …, f (n - 1)` is `i`, when `f` is injective on
`[0, n)`. -/
lemma idxOf_range_map {f : ℕ → ℕ} {n i : ℕ} (hi : i < n)
    (hinj : ∀ a < n, ∀ b < n, f a = f b → a = b) :
    ((List.range n).map f).idxOf (f i) = i := by
  have hnd : ((List.range n).map f).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro a ha b hb hab
    exact hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) hab
  have hl : i < ((List.range n).map f).length := by simp [hi]
  simpa using hnd.idxOf_getElem i hl

/-- `congKey` reads the weights only below `m0`. -/
lemma congKey_congr_q {par dep eu ev q q' : ℕ → ℕ} {m0 : ℕ} (hq : ∀ t < m0, q t = q' t)
    (y : ℕ) : congKey par dep eu ev q m0 y = congKey par dep eu ev q' m0 y := by
  unfold congKey
  exact Finset.sum_congr rfl fun t ht => by rw [hq t (Finset.mem_range.mp ht)]

/-- The edge order of the order phase: the rank stored at the index of the edge. Here `mem` is
the memory at the start of the phase (it holds the edge IDs) and `mem'` the memory after it. -/
def orderPi (X : OrderLayout) (mem mem' : ℕ → ℕ) : ℕ → ℕ :=
  tStagePi mem' X.tPtr X.vCap X.tM (tStageList mem X.tOrigSrc X.tM)

set_option maxHeartbeats 1600000 in
/-- The order of the order phase is a `5/4`-approximate congestion order of `T₀`. -/
theorem orderPhase_pi {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {bRoot bStore bOrder bT bTH : ℕ} {mem mem₅ : ℕ → ℕ} {ret : ℕ}
    {v ℓ₀ : ℕ → ℝ} {ℓ_int : ℕ → ℕ} {P_fp S_div : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hpost : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args
      mem ret mem₅)
    (hv : ∀ e ∈ G₀.E, 0 < v e) (hℓ_pos : ∀ e ∈ G₀.E, 0 < ℓ_int e)
    (hℓ_lt : ∀ e ∈ G₀.E, 16 * ℓ_int e ≤ 2 ^ S_div)
    (hℓ_eq : ∀ e ∈ G₀.E, ℓ₀ e = (ℓ_int e : ℝ) / (2 : ℝ) ^ P_fp)
    (hend : eList.Nodup) (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (hq : ∀ t < X.m0, unsignedVal mem (X.qPtr + t * X.Kq) h X.Kq =
      edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div / ℓ_int (eList.getD t 0)) :
    IsApproxCongOrder (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀) T₀
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1) (5 / 4)
      (orderPi X mem mem₅) := by
  obtain ⟨v₁, mem₁, v₃, mem₃, v₄, mem₄, v₅, h₁, h₃, h₄, h₅⟩ := orderPhase_post hpost
  have hn := I.hn2
  have hmin := I.hmin
  have hlen := I.heLen
  have l5 := I.l5; have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9
  have l10 := I.l10; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l18 := I.l18
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17
  obtain ⟨tp1, tp2⟩ := I.tPi_le
  -- the rooting call
  obtain ⟨n', m', tailArr', headArr', r', outPtr', sPtr', auxPar', logCap', tl, hd, heq, -, hends,
    hR, -, -, hfr⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  set mem₂ := Function.update mem₁ (X.auxPar + X.n) 0 with hmem₂
  have hfr₂ := orderPhase_frame₂ I hfr
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
  -- the tree arrays, with the ends that the rooting call read
  have hA : T0IndexArrays T₀ vList X.tM (fun i => mem (X.tOrigSrc + i)) tl hd :=
    I.hA.congr (fun _ _ => rfl) (fun f hf => (hends f hf).1) (fun f hf => (hends f hf).2)
  -- the order call
  obtain ⟨n₃, r₃, m₃, eL₃, vI₃, eu₃, ev₃, qP₃, Kq₃, dP₃, K₃, tmp₃, L₃, up₃, dep₃, par₃, qO₃, pe₃,
    arr₃, scr₃, pi₃, min₃, g₃, vc₃, ec₃, heq₃, -, heu, hev, ⟨S, hSnd, -, hSmem, hSsort, hrank⟩, -,
    -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  -- the `T` stage keeps the ranks
  obtain ⟨tP₄, vc₄, ec₄, tM₄, vL₄, tO₄, tT₄, tH₄, n₄, nO₄, heq₄, -, -, hpi₄, -⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  -- the `T_H` stage keeps them too
  obtain ⟨n₅, q₅, p₅, d₅, b₅, r₅, t₅, heq₅, -, -, -, -, hfr₅⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  -- the weights in the memory of the order call
  have hq₂ : ∀ t < eList.length, unsignedVal mem₂ (X.qPtr + t * X.Kq) h X.Kq =
      edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div / ℓ_int (eList.getD t 0) := by
    intro t ht
    rw [hlen] at ht
    rw [← hq t ht]
    refine unsignedVal_congr fun i hi => ?_
    have : t * X.Kq + X.Kq ≤ X.m0 * X.Kq := by
      calc t * X.Kq + X.Kq = (t + 1) * X.Kq := by ring
        _ ≤ X.m0 * X.Kq := Nat.mul_le_mul_right _ ht
    exact hfr₂ _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hvl := I.hvlen
  refine congOrder_isApproxCongOrder (r := 0) (par := fun x => mem₂ (X.auxPar + x))
    (pe := fun x => mem₂ (X.auxPar + X.n + x)) (dep := fun x => mem₂ (X.auxPar + X.n + X.n + x))
    (eu := fun t => mem₃ (X.eu + t)) (ev := fun t => mem₃ (X.ev + t))
    (piv := fun i => mem₃ (tPiBase X.tPtr X.vCap X.tM + i)) (S := S) (ℓ_int := ℓ_int)
    (P_fp := P_fp) (S_div := S_div)
    hv hℓ_pos hℓ_lt hℓ_eq I.hT hA I.hnd (by rw [hvl]; exact hR₂) (by omega)
    (fun i hi => (I.hV _).mpr (List.getD_eq_getElem _ _ hi ▸ List.getElem_mem hi))
    (fun u hu => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((I.hV u).mp hu)
      exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩)
    hend hEl heu hev hSnd (fun y => by rw [hSmem y, hvl]) ?_ hrank ?_
  · have hq₂' : ∀ t < X.m0, unsignedVal mem₂ (X.qPtr + t * X.Kq) h X.Kq =
        edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div / ℓ_int (eList.getD t 0) :=
      fun t ht => hq₂ t (by omega)
    refine List.Pairwise.imp (fun hab => ?_) hSsort
    rw [hlen]
    rwa [congKey_congr_q hq₂', congKey_congr_q hq₂'] at hab
  · intro i hi
    have hinj : ∀ a < X.tM, ∀ b < X.tM, mem (X.tOrigSrc + a) = mem (X.tOrigSrc + b) → a = b :=
      hA.fid_inj
    show mem₅ (tPiBase X.tPtr X.vCap X.tM +
      ((List.range X.tM).map fun i => mem (X.tOrigSrc + i)).idxOf (mem (X.tOrigSrc + i))) = _
    rw [idxOf_range_map (f := fun i => mem (X.tOrigSrc + i)) hi hinj,
      hfr₅ _ (Or.inl (by omega)) (Or.inl (by omega)), hpi₄ i hi]

end

end MinCostFlow.LSF.Program
