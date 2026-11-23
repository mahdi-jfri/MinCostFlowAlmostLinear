module

public import MinCostFlow.LSF.Program.InitRoots
public import MinCostFlow.LSF.Program.InitDecompOut
public import MinCostFlow.LSF.Program.WBridge

/-!
# What the forest phase reads, from the posts of the decomposition phase

The bridges of the forest phase ask for a tree decomposition `W` with its labels (`WLabels`) and
for the roots pass of the root set. `decompPhase_forestIn` gives both from the post of the
decomposition phase. The decomposition and its labels come from `decompWT_W`; the root set is the
upward closure of the representatives, the boundary of `W` and the ends of the edges with `P`,
where `P` is what the high flags at `hiCopy` mark (`decompPhase_rootPass`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

open Classical in
/-- After the decomposition phase: a decomposition `W` of `T₀` with the six properties, the
labels at `dBase + 6 n` and `dBase + 7 n` name its pieces, and the arrays above `inR` are the
roots pass of the first root set. -/
theorem decompPhase_forestIn {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ}
    {X : DecompLayout} {bWT bLB bW bCopy bFlag bRoots : ℕ} {K : List ℕ → (ℕ → ℕ) → ℕ}
    {mem mem₈ : ℕ → ℕ} {ret : ℕ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (hpost : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots K).post X.args mem ret
      mem₈)
    (hG₀ : G₀.IsValid) (hTV : T₀.V = G₀.V) (hk : 0 < X.k)
    (hθ : X.θ = decompThetaNat G₀ X.k) (hn2 : 2 ≤ X.n)
    (heNd : eList.Nodup) (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E) (heLen : eList.length = X.m0)
    (heL : ∀ t < X.m0, mem (dgEListBase X.gPtr X.vCap X.eCap + t) = eList.getD t 0)
    (heu : ∀ t < eList.length, mem (X.eu + t) < vList.length ∧
      vList.getD (mem (X.eu + t)) 0 = G₀.tail (eList.getD t 0))
    (hev : ∀ t < eList.length, mem (X.ev + t) < vList.length ∧
      vList.getD (mem (X.ev + t)) 0 = G₀.head (eList.getD t 0))
    (hrepV : ∀ j < X.cnt, mem (X.repPtr + j) ∈ vList)
    (hvC : ∀ v ∈ vList, v < X.vCap)
    (hvIdx : ∀ i (hi : i < vList.length), mem (X.vIdx + vList[i]) = i + 1)
    {P : ℕ → Prop} (hhigh : ∀ t < X.m0, mem₈ (X.hiCopy + t) = 1 ↔ P (eList.getD t 0))
    {π : ℕ → ℕ} (hπ : IsEdgeOrder T₀ π)
    (hpiv : ∀ i < X.tM, π (mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) =
      mem (tPiBase X.tPtr X.vCap X.tM + i)) :
    ∃ W : Finset (Finset ℕ), IsTreeDecompSpec G₀ T₀ X.k W ∧
      WLabels T₀ vList 0 W
        (fun x => (mem₈ (X.dBase + 6 * X.n + x), mem₈ (X.dBase + 7 * X.n + x))) ∧
      RootPassIdx T₀ vList X.tM 0 (fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i))
        (fun x => mem (X.auxPar + x)) (fun x => mem (X.auxPar + X.n + x))
        (upClosure (hldAuxTree T₀ (vList.getD 0 0)) (vList.getD 0 0)
          (((List.range X.cnt).map fun j => mem (X.repPtr + j)).toFinset ∪ boundary W ∪
            (G₀.E.filter P).biUnion fun e => {G₀.tail e, G₀.head e}))
        π (fun y => mem₈ (X.inR + y)) (fun i => mem (tPiBase X.tPtr X.vCap X.tM + i))
        (fun y => mem₈ (X.inR + X.n + y)) (fun i => mem₈ (X.inR + X.n + X.n + i))
        (fun y => mem₈ (X.inR + X.n + X.n + X.tM + y)) := by
  have hvl := I.hvlen
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, q₁, q₃, q₄, q₅, q₆, q₇, q₈⟩ := decompPhase_post hpost
  have F3 := (decompPhase_frame I q₁ q₃ q₄ q₅ q₆ q₇ q₈).2.2.1
  obtain ⟨W, hspec, hbndV, hlab⟩ := decompWT_W I q₁ hG₀ hTV hk hθ heNd hEl heLen heu hev hn2
  have hBV : ∀ v ∈ boundary W, v ∈ vList := by
    intro v hv
    obtain ⟨W₁, hW₁, -, -, -, hv1, -⟩ := mem_boundary_iff.mp hv
    exact (I.hV v).mp ((hspec.1 W₁ hW₁).2.1 hv1)
  refine ⟨W, hspec, wLabels_of_spec hspec fun x hx hx0 x' hx' hx0' => ?_, ?_⟩
  · rw [F3 _ (by omega) (by omega), F3 _ (by omega) (by omega), F3 _ (by omega) (by omega),
      F3 _ (by omega) (by omega)]
    exact hlab x hx hx0 x' hx' hx0'
  refine decompPhase_rootPass (G₀ := G₀) (P := P) I q₁ q₃ q₄ q₅ q₆ q₇ q₈ (fun x hx => ?_) hBV
    hrepV hvC hvIdx (fun e => ?_) (fun t ht => by rw [heL t ht]; exact hhigh t ht)
    (fun t ht => by rw [heL t ht]; exact heu t (by omega))
    (fun t ht => by rw [heL t ht]; exact hev t (by omega)) hπ hpiv
  · have hv : vList.getD x 0 ∈ T₀.V := by
      rw [I.hV, List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _
    have := hbndV _ hv
    unfold vtxFun at this
    rw [idxOf_getD I.hnd hx] at this
    exact this
  · rw [← hEl]
    constructor
    · intro he
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp he
      exact ⟨t, by omega, by rw [heL t (by omega), List.getD_eq_getElem _ _ ht]⟩
    · rintro ⟨t, ht, rfl⟩
      rw [heL t ht, List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _

end

end MinCostFlow.LSF.Program
