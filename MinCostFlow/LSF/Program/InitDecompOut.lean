module

public import MinCostFlow.LSF.Program.DecompPhaseIn
public import MinCostFlow.LSF.Program.DecompWTEmpty

/-!
# The decomposition that the decomposition phase computes

The first call of the decomposition phase, `decompWTProc`, writes degree, greedy, label, mark and
closure arrays in its scratch area at `dBase`. `decompWT_W` reads them as a decomposition `W` of
`T₀` that meets `IsTreeDecompSpec` (`wT_spec`), and gives what the later calls need: the closure
flags at `dBase + 11 n` mark the boundary of `W`, and two non-root vertices have the same labels
at `dBase + 6 n`, `dBase + 7 n` exactly when their parent edges lie in the same part.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

set_option maxHeartbeats 1600000 in
/-- The decomposition of `decompWTProc`. -/
theorem decompWT_W {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : DecompLayout}
    {mem m₁ : ℕ → ℕ} {v₁ : ℕ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (h₁ : (decompWTContract w).post [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] mem
      v₁ m₁)
    (hG₀ : G₀.IsValid) (hTV : T₀.V = G₀.V) (hk : 0 < X.k)
    (hθ : X.θ = decompThetaNat G₀ X.k)
    (heNd : eList.Nodup) (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E) (heLen : eList.length = X.m0)
    (heu : ∀ t < eList.length, mem (X.eu + t) < vList.length ∧
      vList.getD (mem (X.eu + t)) 0 = G₀.tail (eList.getD t 0))
    (hev : ∀ t < eList.length, mem (X.ev + t) < vList.length ∧
      vList.getD (mem (X.ev + t)) 0 = G₀.head (eList.getD t 0)) (hn2 : 2 ≤ X.n) :
    ∃ W : Finset (Finset ℕ), IsTreeDecompSpec G₀ T₀ X.k W ∧
      (∀ v ∈ T₀.V, vtxFun vList (fun x => m₁ (X.dBase + 11 * X.n + x)) v = 1 ↔ v ∈ boundary W) ∧
      (∀ x < vList.length, x ≠ 0 → ∀ x' < vList.length, x' ≠ 0 →
        ((m₁ (X.dBase + 6 * X.n + x) = m₁ (X.dBase + 6 * X.n + x') ∧
          m₁ (X.dBase + 7 * X.n + x) = m₁ (X.dBase + 7 * X.n + x')) ↔ ∃ P ∈ W,
          parentEdge T₀ (vList.getD 0 0) (vList.getD x 0) ∈ inducedEdges T₀ P ∧
          parentEdge T₀ (vList.getD 0 0) (vList.getD x' 0) ∈ inducedEdges T₀ P)) := by
  classical
  obtain ⟨n', m0', eu', ev', q', par', r', θ', base', heq, -, -, hO⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  obtain ⟨hdeg, hGC, hlab, hmark, hmr, hcr, -⟩ := hO
  obtain ⟨Q, tl, hd, dep, hQ, hQat, hRA, -, hTA⟩ := I.htree
  obtain ⟨hG, hC⟩ := hGC Q hQ hQat
  have hvl := I.hvlen
  have hV2 : 2 ≤ G₀.V.card := by
    have hcard : G₀.V.card = vList.length := by
      rw [← hTV, ← List.toFinset_card_of_nodup I.hnd]
      congr 1
      ext u
      simp [I.hV u]
    omega
  have hm : eList.length = X.m0 := heLen
  have hdegR : ∀ x < vList.length, ((m₁ (X.dBase + x) : ℕ) : ℝ) =
      vWeight G₀ (fun _ => 1) (vList.getD x 0) := fun x hx => by
    rw [(hdeg x (by omega)).1, ← hm]
    exact degCount_eq_vWeight heNd hEl I.hnd heu hev hx
  by_cases hE : G₀.E.Nonempty
  · have hWT := wT_spec (G₀ := G₀) (T₀ := T₀) (vList := vList) (tM := X.tM) (r := 0) (k := X.k)
        (fid := fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) (tl := tl) (hd := hd)
        (par := fun x => mem (X.auxPar + x)) (pe := fun x => mem (X.auxPar + X.n + x)) (dep := dep)
        (Q := Q) (deg := fun x => m₁ (X.dBase + x)) (ν := fun x => m₁ (X.dBase + 1 * X.n + x))
        (cur := fun x => m₁ (X.dBase + 2 * X.n + x)) (nb := fun x => m₁ (X.dBase + 3 * X.n + x))
        (bidx := fun x => m₁ (X.dBase + 4 * X.n + x)) (s := fun x => m₁ (X.dBase + 5 * X.n + x))
        (labY := fun x => m₁ (X.dBase + 6 * X.n + x)) (labB := fun x => m₁ (X.dBase + 7 * X.n + x))
        (S := fun x => m₁ (X.dBase + 8 * X.n + x)) (cnt := fun x => m₁ (X.dBase + 9 * X.n + x))
        (has := fun x => m₁ (X.dBase + 10 * X.n + x)) (inR := fun x => m₁ (X.dBase + 11 * X.n + x))
          hG₀ hTV hV2 hE hk I.hT hTA I.hnd I.hV (by rw [hvl]; exact hRA) (by omega)
        (by rw [hvl]; exact hQ)
        hdegR
        (fun x hx => by
          show m₁ (X.dBase + 1 * X.n + x) = _
          rw [(hdeg x (by omega)).2, hθ, (hdeg x (by omega)).1])
        (by rw [hvl, ← hθ]; exact hG)
        (fun x hx hx0 => hlab x (by omega) hx0)
        (fun x hx hx0 => by rw [← hθ]; exact hmark x (by omega) hx0)
        (by rw [← hθ, hvl]; exact hmr)
        (by rw [hvl]; exact hC) hcr
    exact ⟨_, hWT⟩
  · have hE0 : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    exact wT_spec_empty (G₀ := G₀) (T₀ := T₀) (vList := vList) (tM := X.tM) (r := 0) (k := X.k)
        (fid := fun i => mem (tOrigIdBase X.tPtr X.vCap X.tM + i)) (tl := tl) (hd := hd)
        (par := fun x => mem (X.auxPar + x)) (pe := fun x => mem (X.auxPar + X.n + x)) (dep := dep)
        (Q := Q) (deg := fun x => m₁ (X.dBase + x)) (ν := fun x => m₁ (X.dBase + 1 * X.n + x))
        (cur := fun x => m₁ (X.dBase + 2 * X.n + x)) (nb := fun x => m₁ (X.dBase + 3 * X.n + x))
        (bidx := fun x => m₁ (X.dBase + 4 * X.n + x)) (s := fun x => m₁ (X.dBase + 5 * X.n + x))
        (labY := fun x => m₁ (X.dBase + 6 * X.n + x)) (labB := fun x => m₁ (X.dBase + 7 * X.n + x))
        (S := fun x => m₁ (X.dBase + 8 * X.n + x)) (cnt := fun x => m₁ (X.dBase + 9 * X.n + x))
        (has := fun x => m₁ (X.dBase + 10 * X.n + x)) (inR := fun x => m₁ (X.dBase + 11 * X.n + x))
          hE0 hk I.hT hTA I.hnd I.hV (by rw [hvl]; exact hRA) (by omega)
        (by rw [hvl]; exact hQ)
        hdegR
        (fun x hx => by
          show m₁ (X.dBase + 1 * X.n + x) = _
          rw [(hdeg x (by omega)).2, hθ, (hdeg x (by omega)).1])
        (by rw [hvl, ← hθ]; exact hG)
        (fun x hx hx0 => hlab x (by omega) hx0)
        (fun x hx hx0 => by rw [← hθ]; exact hmark x (by omega) hx0)
        (by rw [← hθ, hvl]; exact hmr)
        (by rw [hvl]; exact hC) hcr

end

end MinCostFlow.LSF.Program
