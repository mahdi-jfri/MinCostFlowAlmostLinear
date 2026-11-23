module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

/-!
# The number of candidates of a step for `0 < j`

The step for `0 < j` finds the affected edges among candidates: the edges whose walk at a level
`i < j` passes through a vertex of `S_{j-1}` (Algorithm 6, line 71). The program reads them from
the reverse lists of the vertices of `S_{j-1}`, whose contents are the model sets
`modelRevSet m i v` (`RevHistoryInv`). Its cost is linear in `modelCandRevSum m`, the total size
of these sets, and the paper bounds the work of this line by the vertex congestion of the
embeddings (the proof of Lemma 5.9, [chen2022maximum] Section 5.1).

Here we prove this bound. The set `modelRevSet m i v` was fixed when level `i` was last rebuilt,
at step `r = lastRebuild q L i k`. Its edges are edges of `G^{(r)}` whose walk `Π_{≤ i}` in
`H_{≤ i}^{(r)}` visits `v`, so their number is at most the vertex congestion of `Π_{≤ i}` at `v`,
which `SnapInv` at `r` bounds by `vcongBound i` (Claim 5.7). Summing over the levels `i < j` and
the vertices of `S_{j-1}` bounds `modelCandRevSum`, and every candidate is counted there at least
once.

* `card_modelRevSet_le`: `|modelRevSet m i v| ≤ vcongBound i`.
* `modelCandRevSum_le`: `modelCandRevSum m ≤ |S_{j-1}| · Σ_{i < j} vcongBound i`.
* `card_modelCandSet_le`: `|modelCandSet m| ≤ modelCandRevSum m`.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

public section

/-- **The reverse set of a vertex is bounded by the vertex congestion** (Claim 5.7 at the last
rebuild of level `i`): `|modelRevSet m i v| ≤ vcongBound i`. The hypotheses are `SnapInv` and
the validity of the graph at the last rebuild `r` of level `i`. -/
theorem card_modelRevSet_le {mMax : ℕ} {P : SparsifyParams} (m : StepPosModel) (hq : 1 ≤ m.q)
    (i : Fin (m.L + 1))
    (hS : SnapInv m.G₀ m.L m.q mMax P (canonicalSparsify m.impl) m.us
      (lastRebuild m.q m.L i.1 m.k))
    (hVr : (m.G₀.applyBatch (m.us.take (lastRebuild m.q m.L i.1 m.k))).IsValid) (v : ℕ) :
    ((modelRevSet m i v).card : ℝ) ≤ vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i.1 := by
  set r := lastRebuild m.q m.L i.1 m.k with hr
  set st := runState (L := m.L) m.G₀ m.q (canonicalSparsify m.impl) m.us r with hst
  set Gr := m.G₀.applyBatch (m.us.take r) with hGr
  set Hu := unionGraphLt Gr st.H_level (i.1 + 1) with hHu
  have hch : chooseLevel m.L m.q r ≤ i.1 := lastRebuild_chooseLevel_le hq (Nat.le_of_lt_succ i.2)
  have hemb := hS.emb_at i hch
  have hvc := hS.vcong_at i hch
  have hGeq : st.G = Gr := hS.G_eq
  -- Every edge of the reverse set is an edge of `G^{(r)}` whose walk `Π_{≤ i}` in `H_{≤ i}` visits
  -- `v`.
  have hkey : ∀ e ∈ modelRevSet m i v,
      e ∈ Gr.E ∧ v ∈ Hu.walkVertices (Gr.tail e) (piLe st i.1 e) := by
    intro e he
    simp only [modelRevSet, Finset.mem_filter] at he
    obtain ⟨hdom, hwv⟩ := he
    have heG : e ∈ Gr.E := hS.inDom_sub i hdom
    have hpi : piLe st i.1 e = st.Pi_level i e := by
      have h0 : e ∈ st.inDom ⟨0, Nat.zero_lt_succ m.L⟩ := by rw [hS.inDom0]; exact heG
      obtain ⟨i₁, hi₁j, _, hi₁none, heq₁⟩ :=
        piLtFrom_eq st.Pi_level st.inDom (j := i.1 + 1) (Nat.succ_pos _) h0
      have hi₁ : i₁ = i := by
        by_contra hne
        have hlt : i₁.1 < i.1 := by
          have : i₁.1 ≠ i.1 := fun h => hne (Fin.ext h)
          omega
        exact hi₁none i hlt (Nat.lt_succ_self _) hdom
      subst hi₁
      exact heq₁
    have hwalk := hemb.2 e heG
    rw [hpi] at hwalk ⊢
    refine ⟨heG, ?_⟩
    rw [hGeq] at hwv
    have hcong : st.H.walkVertices (Gr.tail e) (st.Pi_level i e) =
        Hu.walkVertices (Gr.tail e) (st.Pi_level i e) := by
      apply walkVertices_congr
      rintro ⟨a, d⟩ hx
      have hxE : a ∈ Hu.E := IsWalk.mem_edge hwalk _ hx
      have hxH : a ∈ st.H.E := by
        rw [hS.H_E]; exact unionEdgesLt_mono _ (by omega) hxE
      obtain ⟨ht, hh⟩ := hS.H_sub.2.2 a hxH
      cases d <;> simp only [MGraph.dst, Hu, unionGraphLt, Bool.false_eq_true, ↓reduceIte] <;>
        first | exact ht | exact hh
    rw [← hcong]
    exact hwv
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hbnd_nn : 0 ≤ vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i.1 := by
    unfold vcongBound; positivity
  by_cases hv : v ∈ Hu.V
  · have hsub : modelRevSet m i v ⊆
        Gr.E.filter fun e => v ∈ Hu.walkVertices (Gr.tail e) (piLe st i.1 e) := fun e he => by
      rw [Finset.mem_filter]; exact hkey e he
    have hcard : ((modelRevSet m i v).card : ℝ) ≤
        Embedding.vcongAt (piLe st i.1) Gr Hu (fun _ => 1) v := by
      unfold Embedding.vcongAt
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_le_card hsub
    have hsup : Embedding.vcongAt (piLe st i.1) Gr Hu (fun _ => 1) v ≤
        Embedding.vcong (piLe st i.1) Gr Hu (fun _ => 1) := by
      unfold Embedding.vcong
      rw [dif_pos ⟨v, hv⟩]
      exact Finset.le_sup' (Embedding.vcongAt (piLe st i.1) Gr Hu (fun _ => 1)) hv
    exact le_trans hcard (le_trans hsup hvc)
  · -- A vertex outside `H_{≤ i}` is on no walk, so the reverse set is empty.
    have hHuV : Hu.IsValid := by
      intro e' he'
      have he'H : e' ∈ st.H.E := by
        rw [hS.H_E]; exact unionEdgesLt_mono _ (by omega) he'
      have he'G : e' ∈ Gr.E := hS.H_sub.2.1 he'H
      exact hVr e' he'G
    have hempty : modelRevSet m i v = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => hv ?_
      obtain ⟨heG, hwv⟩ := hkey e he
      exact IsWalk.walkVertices_mem_V hHuV (hemb.2 e heG) ((hVr e heG).1) v hwv
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact hbnd_nn

/-- Every candidate lies in some reverse set that `modelCandRevSum` counts. -/
theorem card_modelCandSet_le (m : StepPosModel) : (modelCandSet m).card ≤ modelCandRevSum m := by
  classical
  have hsub : modelCandSet m ⊆ (Finset.range m.j).biUnion fun i =>
      m.S_prev.biUnion fun v => if hi : i < m.L + 1 then modelRevSet m ⟨i, hi⟩ v else ∅ := by
    intro e he
    simp only [modelCandSet, Finset.mem_filter] at he
    obtain ⟨_, i, v, hv, hij, he⟩ := he
    simp only [Finset.mem_biUnion, Finset.mem_range]
    exact ⟨i.1, hij, v, hv, by simpa [i.2] using he⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  unfold modelCandRevSum
  refine Finset.sum_le_sum fun i _ => le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs <;> simp

/-- **The candidates are bounded by the vertex congestion** (the bound of line 71 of Algorithm 6
in the proof of Lemma 5.9): `modelCandRevSum m ≤ |S_{j-1}| · Σ_{i < j} vcongBound i`, given
`SnapInv` and valid graphs at the last rebuilds of the levels below `j`. -/
theorem modelCandRevSum_le {mMax : ℕ} {P : SparsifyParams} (m : StepPosModel) (hq : 1 ≤ m.q)
    (hS : ∀ i : Fin (m.L + 1), i.1 < m.j →
      SnapInv m.G₀ m.L m.q mMax P (canonicalSparsify m.impl) m.us (lastRebuild m.q m.L i.1 m.k))
    (hVr : ∀ i : Fin (m.L + 1), i.1 < m.j →
      (m.G₀.applyBatch (m.us.take (lastRebuild m.q m.L i.1 m.k))).IsValid) :
    (modelCandRevSum m : ℝ) ≤
      (m.S_prev.card : ℝ) * ∑ i ∈ Finset.range m.j, vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i := by
  have hjL : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
  unfold modelCandRevSum
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i < m.j := Finset.mem_range.mp hi
  have hiL : i < m.L + 1 := by omega
  simp only [hiL, ↓reduceDIte]
  calc (∑ v ∈ m.S_prev, ((modelRevSet m ⟨i, hiL⟩ v).card : ℝ))
      ≤ ∑ _v ∈ m.S_prev, vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i :=
        Finset.sum_le_sum fun v _ =>
          card_modelRevSet_le m hq ⟨i, hiL⟩ (hS ⟨i, hiL⟩ hij) (hVr ⟨i, hiL⟩ hij) v
    _ = (m.S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i := by
        rw [Finset.sum_const, nsmul_eq_mul]

end

end MinCostFlow.DynSpanner.Program
