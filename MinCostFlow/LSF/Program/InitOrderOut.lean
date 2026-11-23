module

public import MinCostFlow.LSF.Program.InitMain
public import MinCostFlow.LSF.Program.InitPi
public import MinCostFlow.LSF.Program.InitQ

/-!
# What the order phase gives the initial state

`order_pi_of_posts` restates `orderPhase_pi` with the places and posts of `main_wp`: the edge order
that the order phase writes is a `5/4`-approximate congestion order of `T₀` for the weighted copy
graph. The weights come from `order_q`, and the length facts from `lenInt_facts`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The edge order of the order phase, in the terms of `main_wp`. -/
theorem order_pi_of_posts {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ T₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH ret : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ : ℕ → ℕ} {vList eList : List ℕ} (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hm : G₀.E.card = V.m0)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (IO : OrderPhaseIn w h G₀ T₀ vList eList
      (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post
      (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)).args mem₃ ret mem₄) :
    IsApproxCongOrder (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀) T₀
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1) (5 / 4)
      (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) := by
  have hq := order_q (V.withH H) (S.withH H) hn rfl h₁ h₂ heLen heE h₃
  refine orderPhase_pi (ℓ_int := fun e => lenInt mem lenArr V.L_in h e) (P_fp := P_fp)
    IO h₄ (fun e he => (S.hwv e he).2.2) (fun e he => ?_) (fun e he => ?_) (fun e he => ?_)
    heNd heE hq
  · exact (lenInt_facts S.hh (S.hlv e he).1 (S.hlv e he).2.1 (S.hlv e he).2.2).1
  · exact (lenInt_facts S.hh (S.hlv e he).1 (S.hlv e he).2.1 (S.hlv e he).2.2).2.1
  · exact (lenInt_facts S.hh (S.hlv e he).1 (S.hlv e he).2.1 (S.hlv e he).2.2).2.2

/-- The representatives of `prepStage`: a list at `repPtr` that names one vertex of every
component, starting with the root `vList[0]`. -/
theorem prep_reps {w : ℕ} {G₀ : MGraph} {V : InitVals} {g0Ptr vCap0 eCap0 kk cnt : ℕ}
    {mem mem₁ mem₂ : ℕ → ℕ} {vList : List ℕ}
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂) (hn : G₀.n = V.n0)
    (hvLen : vList.length = V.n0) (hvL : ListAt mem₂ V.vListPtr vList) :
    ∃ repList : List ℕ, repList.length = cnt ∧ repList.Nodup ∧
      repList.getD 0 0 = vList.getD 0 0 ∧ ListAt mem₁ V.repPtr repList ∧
      IsCompReps G₀ (vList.getD 0 0) repList.toFinset := by
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vList', repList, heq, -, -, -,
    -, hvLen', -, -, hvL', -, -, -, -, -, -, -, hrl, hrnd, hr0, hrL, hC, -⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  have hvEq : vList' = vList := by
    refine listAt_unique (fun i hi => ?_) hvL (by rw [hvLen', hvLen, hn])
    rw [hfr₂ _ (Or.inl (by rw [hvLen', hn] at hi; omega))]
    exact hvL' i hi
  subst vList'
  refine ⟨repList, hrl, hrnd, hr0, ?_, hC⟩
  rw [hn] at hrL
  exact hrL

end

end MinCostFlow.LSF.Program
