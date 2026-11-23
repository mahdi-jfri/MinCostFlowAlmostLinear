module

public import MinCostFlow.LSF.Program.InitPi
public import MinCostFlow.LSF.Program.InitGlue

/-!
# What the stretch pass reads after the order phase

`decompPhase_wstrAt` reads the order `π` on tree indices, the edge list of the graph block and
the endpoint arrays `eu`, `ev`. This file reads them off the posts of the order phase.
`order_pi_idx`: the rank stored at tree index `j` is the rank that `orderPi` gives to the edge
with that index. `order_ends`: the edge list holds `eList`, and `eu`, `ev` hold the indices of the
ends of its edges.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- After the order phase, `orderPi` gives the edge at tree index `j` the rank at index `j`. -/
theorem order_pi_idx {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {bRoot bStore bOrder bT bTH : ℕ} {mem mem₅ : ℕ → ℕ} {ret : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hpost : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args
      mem ret mem₅) :
    ∀ j < X.tM, orderPi X mem mem₅ (mem₅ (tOrigIdBase X.tPtr X.vCap X.tM + j)) =
      mem₅ (tPiBase X.tPtr X.vCap X.tM + j) := by
  obtain ⟨v₁, mem₁, v₃, mem₃, v₄, mem₄, v₅, h₁, h₃, h₄, h₅⟩ := orderPhase_post hpost
  intro j hj
  rw [order_tOrigId I h₁ h₃ h₄ h₅ j hj]
  unfold orderPi tStagePi tStageList
  rw [idxOf_range_map (f := fun i => mem (X.tOrigSrc + i)) hj I.hA.fid_inj]

/-- After the order phase, the edge list of the graph block holds `eList`, and `eu`, `ev` hold
the indices of the tails and heads of its edges. -/
theorem order_ends {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {bRoot bStore bOrder bT bTH : ℕ} {mem mem₅ : ℕ → ℕ} {ret : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hpost : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args
      mem ret mem₅) :
    (∀ t < X.m0, mem₅ (dgEListBase X.gPtr X.vCap X.eCap + t) = eList.getD t 0) ∧
    (∀ t < X.m0, vList.getD (mem₅ (X.eu + t)) 0 = G₀.tail (eList.getD t 0) ∧
      vList.getD (mem₅ (X.ev + t)) 0 = G₀.head (eList.getD t 0)) := by
  obtain ⟨v₁, mem₁, v₃, mem₃, v₄, mem₄, v₅, h₁, h₃, h₄, h₅⟩ := orderPhase_post hpost
  obtain ⟨hFr, -, -, h53, -, -⟩ := orderPhase_frame I h₁ h₃ h₄ h₅
  have hn := I.hn2; have hmin := I.hmin
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7
  have l8 := I.l8; have l9 := I.l9; have l10 := I.l10; have l11 := I.l11; have l12 := I.l12
  have l13 := I.l13; have l14 := I.l14; have l15 := I.l15; have l16 := I.l16; have l17 := I.l17
  have l18 := I.l18
  have hgE : dgEListBase X.gPtr X.vCap X.eCap + X.m0 ≤ X.tPtr := by
    have := I.hme
    simp only [dgEListBase, dynGraphSize] at l1 ⊢; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, heu,
    hev, -, -, -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [hFr _ (Or.inl (by omega)), List.getD_eq_getElem _ _ (by rw [I.heLen]; omega)]
    exact I.heL t (by rw [I.heLen]; omega)
  · rw [h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact ⟨(heu t (by rw [I.heLen]; omega)).2, (hev t (by rw [I.heLen]; omega)).2⟩

end

end MinCostFlow.LSF.Program
