module

public import MinCostFlow.Spanner.ProgSparsifyWord

@[expose] public section

/-!
# One Witness Graph for Tasks 2 and 3

Tasks 2 and 3 each name a witness input in their posts, under their own existentials. So a
priori the graph `W` that Task 2 embeds into `J` and the graph `W` that `J` is embedded into by
Task 3 could differ. They do not: both posts say that their witness input starts at the address
stored in slot `h + 5` of the Task 1 output, and that the witness graph is stored at the address
in the slot `13` after that start (`WitnessCoreInput.OutputAt`). The memory below the Task 1 heap
end does not change between the two tasks, so both read the same graph.

The main results are `sparsifyCoreOut_commonW`: after the three tasks there is one graph `W`
with an embedding of `W` into `J` and an embedding of `J` into `W`, and `W` is stored in the final
memory; and `sparsifyCoreOut_commonWD`: the witness data of Tasks 2 and 3 also have the same
weights on the edges of `W`, the same real parameters (`φ_dec`, `M_W`, `φ_ds`, `γ_ExpPath`,
`γ_del`, `τ₁`, `τ₂`), and the same `J0` edges. The weights and the parameters are read from
stored cells; the `J0` edges come from the decomposition stored at the address in slot `h + 3`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- The Task 1 header slots lie below the Task 1 heap end. -/
lemma task1OutAt_slots_lt {impl : SpannerToolImpl} {jAddr h : ℕ} {H' J : Graph}
    {embJH : ℕ → Walk} {mem mem' : ℕ → ℕ} {v w : ℕ}
    (hT : Task1OutAt impl jAddr h H' J embJH mem mem' v w) : h + 9 ≤ v := by
  obtain ⟨wInp, WSubs, -, -, -, -, -, hj0, -, -, -, -, -, hv20, -, -, -, -, -, -, -, -, -, -,
    -, -, hsv, -, -, -, -, -, hhend⟩ := hT
  have h15 := hsv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpe : wInp.prep.h ≤ wInp.prep.hEnd := by
    unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
  omega

/-- `OutputAt` stores the witness graph at the address in slot `13`, below the heap end `v`. -/
lemma outputAt_W_at {wInp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ mem : ℕ → ℕ} {v : ℕ} {wd : WitnessData}
    (hO : wInp.OutputAt ce pds mem₀ mem v wd) :
    wInp.h + 13 < v ∧ GraphAt mem (mem (wInp.h + 13)) wd.W ∧
      mem (wInp.h + 13) + wd.W.encode.length ≤ v := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h20, h21, h22, h23, h24, h25,
    -, hG, -⟩ := hO
  rw [graph_encode_length]
  exact ⟨by omega, hG, by omega⟩

/-- `OutputAt` stores the weight numerators of `W` right after `W`, over the denominator in
slot `18`, below the heap end `v`. -/
lemma outputAt_wW_at {wInp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ mem : ℕ → ℕ} {v : ℕ} {wd : WitnessData}
    (hO : wInp.OutputAt ce pds mem₀ mem v wd) :
    wInp.h + 18 < v ∧ mem (wInp.h + 18) = wInp.prep.phiDen_dec ∧
      mem (wInp.h + 13) + (2 + 2 * wd.W.m) + wd.W.m ≤ v ∧
      ∀ eW < wd.W.m, ((mem (mem (wInp.h + 13) + (2 + 2 * wd.W.m) + eW) : ℝ) /
        (wInp.prep.phiDen_dec : ℝ)) = wd.wW eW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -, h20, h21, h22, h23, h24, h25,
    -, -, hw, -⟩ := hO
  refine ⟨by omega, h18, by omega, fun eW heW => ?_⟩
  rw [← h22]
  exact (hw eW heW).1

/-- `OutputAt` stores the decomposition parameters `phiNum_dec`, `phiDen_dec` and the edge count
of `J0_strip` in slots `17`, `18` and `19`, below the heap end `v`. -/
lemma outputAt_prep_cells {wInp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ mem : ℕ → ℕ} {v : ℕ} {wd : WitnessData}
    (hO : wInp.OutputAt ce pds mem₀ mem v wd) :
    wInp.h + 19 < v ∧ mem (wInp.h + 17) = wInp.prep.phiNum_dec ∧
      mem (wInp.h + 18) = wInp.prep.phiDen_dec ∧ mem (wInp.h + 19) = wInp.prep.J0_strip.m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, h18, h19, h20, h21, h22, h23, h24,
    h25, -⟩ := hO
  exact ⟨by omega, h17, h18, h19⟩

/-- The vertex congestion only sees the embedding on the edges of `G`. -/
lemma vcong_congr_emb {G H : Graph} {wG : ℕ → ℝ} {emb₁ emb₂ : ℕ → Walk}
    (h : ∀ j < G.m, emb₁ j = emb₂ j) : vcong G H wG emb₁ = vcong G H wG emb₂ := by
  unfold vcong vcongAt
  refine Finset.fold_congr fun v _ => ?_
  rw [Finset.filter_congr fun j hj => by rw [h j (Finset.mem_range.mp hj)]]

/-- The real parameters of the witness data depend only on `phiNum_dec`, `phiDen_dec`, the edge
count of `J0_strip`, `J`, `H'`, and the embedding of `J` into `H'` on the edges of `J`. -/
lemma mkWitnessData_params_congr {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {w₁ w₂ : WitnessCoreInput} {S₁ S₂ : List Graph}
    (hn : w₁.prep.phiNum_dec = w₂.prep.phiNum_dec) (hd : w₁.prep.phiDen_dec = w₂.prep.phiDen_dec)
    (hm : w₁.prep.J0_strip.m = w₂.prep.J0_strip.m) (hJ : w₁.prep.J = w₂.prep.J)
    (hH : w₁.H' = w₂.H') (he : ∀ e < w₁.prep.J.m, w₁.embJH e = w₂.embJH e) :
    (w₁.mkWitnessData ce pds S₁).φ_dec = (w₂.mkWitnessData ce pds S₂).φ_dec ∧
    (w₁.mkWitnessData ce pds S₁).M_W = (w₂.mkWitnessData ce pds S₂).M_W ∧
    (w₁.mkWitnessData ce pds S₁).φ_ds = (w₂.mkWitnessData ce pds S₂).φ_ds ∧
    (w₁.mkWitnessData ce pds S₁).γ_ExpPath = (w₂.mkWitnessData ce pds S₂).γ_ExpPath ∧
    (w₁.mkWitnessData ce pds S₁).γ_del = (w₂.mkWitnessData ce pds S₂).γ_del ∧
    (w₁.mkWitnessData ce pds S₁).τ₁ = (w₂.mkWitnessData ce pds S₂).τ₁ ∧
    (w₁.mkWitnessData ce pds S₁).τ₂ = (w₂.mkWitnessData ce pds S₂).τ₂ := by
  have hmw : w₁.mwInt ce = w₂.mwInt ce := by unfold WitnessCoreInput.mwInt; rw [hn, hd, hm]
  have hl : length w₁.prep.J w₁.embJH = length w₂.prep.J w₂.embJH := by
    rw [length_congr_emb he, hJ]
  have hv : vcong w₁.prep.J w₁.H' (fun _ => 1) w₁.embJH =
      vcong w₂.prep.J w₂.H' (fun _ => 1) w₂.embJH := by
    rw [vcong_congr_emb he, hJ, hH]
  have hmd : maxDeg w₁.prep.J = maxDeg w₂.prep.J := by rw [hJ]
  simp only [WitnessCoreInput.mkWitnessData, hn, hd, hm, hmw, hl, hv, hmd]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The weights stored by `OutputAt` are positive when the denominator is. -/
lemma outputAt_wW_pos {wInp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ mem : ℕ → ℕ} {v : ℕ} {wd : WitnessData}
    (hO : wInp.OutputAt ce pds mem₀ mem v wd) (hpd : 0 < wInp.prep.phiDen_dec) :
    ∀ eW < wd.W.m, 0 < wd.wW eW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hw, -⟩ := hO
  intro eW heW
  obtain ⟨he, h1⟩ := hw eW heW
  rw [← he]
  have h1' : (1 : ℝ) ≤ (mem (mem (wInp.h + 14) + eW) : ℝ) := by exact_mod_cast h1
  exact div_pos (by linarith) (by exact_mod_cast hpd)

/-- `τ₂` is positive when `1 ≤ phiNum_dec ≤ phiDen_dec`. -/
lemma mkWitnessData_τ₂_pos {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {wInp : WitnessCoreInput} {S : List Graph}
    (h1 : 1 ≤ wInp.prep.phiNum_dec) (h2 : wInp.prep.phiNum_dec ≤ wInp.prep.phiDen_dec) :
    0 < (wInp.mkWitnessData ce pds S).τ₂ := by
  have hφd : 0 < (wInp.prep.phiNum_dec : ℝ) / (wInp.prep.phiDen_dec : ℝ) :=
    div_pos (by exact_mod_cast h1) (by exact_mod_cast (lt_of_lt_of_le h1 h2))
  have r1 := roundPhi_pos hφd
  have r2 := roundPhi_pos ce.hφ_Const_pos
  dsimp only [WitnessCoreInput.mkWitnessData]
  refine div_pos (mul_pos ?_ ?_) (lt_min (pds.hφ_out_pos _ _ r1) (pds.hφ_out_pos _ _ r2))
  · exact lt_of_lt_of_le one_pos (le_trans (pds.one_le_γ_ExpPath _ _ r1) (le_max_left _ _))
  · exact lt_of_lt_of_le one_pos (le_trans (pds.hγ_del_ge _ _ r1) (le_max_left _ _))

/-- After the three tasks, one graph `W` is embedded into `J` (by Task 2) and has `J` embedded
into it (by Task 3), and the final memory stores it at the address read from the Task 1
header. -/
theorem sparsifyCoreOut_commonW {impl : SpannerToolImpl} {inp : Task1Input}
    {mem mem3 : ℕ → ℕ} {v3 w : ℕ} (hS : SparsifyCoreOut impl inp mem mem3 v3 w) :
    ∃ (W : Graph) (embWJ embJW : ℕ → Walk),
      IsEmbedding W inp.J embWJ ∧ IsEmbedding inp.J W embJW ∧
      GraphAt mem3 (mem3 (mem3 (inp.h + 5) + 13)) W := by
  obtain ⟨mem1, v1, mem2, v2, hT1, hT2, hT3⟩ := hS
  have hs1 := task1OutAt_slots_lt hT1
  -- Task 2: its witness graph is stored in `mem1`, below `v1`.
  obtain ⟨wInp2, WSubs2, _, embWJ, _, _, _, _, _, _, -, -, -, -, -, -, -, hagr2, -, hv12, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hEmb2, -, -, -, -, -, -, -, -, -, hs5_2,
    hO2, -, -⟩ := hT2
  -- Task 3: its witness graph is stored in `memT1`, which agrees with `mem2` below `v1'`.
  obtain ⟨hagr3, -, -, -, wInp3, WSubs3, embJW, _, _, _, _, -, -, -, -,
    ⟨memPre, memT1, v1', hagrT, -, hT1', hs5_3, -, -, -, hO3⟩, -, -, -, -, -, -, -, -, -, -, -, hEmb3,
    -⟩ := hT3
  have hs1' : inp.h + 9 ≤ v1' := task1OutAt_slots_lt hT1'
  have hagr2' : ∀ x < v1, mem2 x = mem1 x := hagr2
  have hv12' : v1 + 32 ≤ v2 := hv12
  have hs5_2' : mem1 (inp.h + 5) = wInp2.h := hs5_2
  have hs5_3' : memT1 (inp.h + 5) = wInp3.h := hs5_3
  have hagr3' : ∀ x < v2, mem3 x = mem2 x := hagr3
  -- The two witness inputs start at the same address.
  have hH : wInp2.h = wInp3.h := by
    rw [← hs5_2', ← hs5_3', ← hagr2' _ (by omega), hagrT _ (by omega)]
  obtain ⟨hb2, hG2, hr2⟩ := outputAt_W_at hO2
  obtain ⟨hb3, hG3, hr3⟩ := outputAt_W_at hO3
  rw [← hH] at hb3 hG3 hr3
  -- They read the graph address from the same cell.
  have hA : memT1 (wInp2.h + 13) = mem1 (wInp2.h + 13) := by
    rw [← hagrT _ hb3, hagr2' _ hb2]
  rw [hA] at hG3 hr3
  have hG2' : GraphAt mem2 (mem1 (wInp2.h + 13)) _ := GraphAt.of_agree_below hG2 hr2 hagr2'
  have hG3' : GraphAt mem2 (mem1 (wInp2.h + 13)) _ := GraphAt.of_agree_below hG3 hr3 hagrT
  have hW := graphAt_inj hG2' hG3'
  refine ⟨_, embWJ, embJW, hEmb2, hW ▸ hEmb3, ?_⟩
  have hc5 : mem3 (inp.h + 5) = wInp2.h := by
    rw [hagr3' _ (by omega), hagr2' _ (by omega), hs5_2']
  have hc13 : mem3 (wInp2.h + 13) = mem1 (wInp2.h + 13) := by
    rw [hagr3' _ (by omega), hagr2' _ hb2]
  rw [hc5, hc13]
  exact GraphAt.of_agree_below hG2' (by omega) hagr3'

/-- After the three tasks, the witness data named by Tasks 2 and 3 have the same graph `W` and
the same weights on its edges. Task 2 embeds `W` into `J` and Task 3 embeds `J` into `W`. -/
theorem sparsifyCoreOut_commonWD {impl : SpannerToolImpl} {inp : Task1Input}
    {mem mem3 : ℕ → ℕ} {v3 w : ℕ} (hS : SparsifyCoreOut impl inp mem mem3 v3 w) :
    ∃ (wd₂ wd₃ : WitnessData) (embWJ embJW : ℕ → Walk),
      wd₂.W = wd₃.W ∧ (∀ eW < wd₂.W.m, wd₂.wW eW = wd₃.wW eW) ∧
      IsEmbedding wd₂.W inp.J embWJ ∧ IsEmbedding inp.J wd₃.W embJW ∧
      wd₂.φ_dec = wd₃.φ_dec ∧ wd₂.M_W = wd₃.M_W ∧ wd₂.φ_ds = wd₃.φ_ds ∧
      wd₂.γ_ExpPath = wd₃.γ_ExpPath ∧ wd₂.γ_del = wd₃.γ_del ∧ wd₂.τ₁ = wd₃.τ₁ ∧
      wd₂.τ₂ = wd₃.τ₂ ∧ wd₂.j0Edges = wd₃.j0Edges ∧
      ∃ η₁ η₂ : ℕ, 1 ≤ η₁ ∧ η₁ ≤ eta1Bound wd₂ inp.J ∧ η₂ ≤ eta2Bound inp.J ∧
        vcong wd₂.W inp.H' wd₂.wW (compose inp.J inp.embJH embWJ) ≤ (η₁ + 1 / 2) * wd₂.τ₁ ∧
        (length wd₂.W embWJ : ℝ) ≤ wd₂.γ_ExpPath ∧
        (∀ eW < wd₃.W.m, econgAt inp.J (fun _ => 1) wd₃.wW embJW eW ≤ (η₂ + 1 / 2) * wd₃.τ₂) ∧
        (length inp.J embJW : ℝ) ≤ wd₃.γ_ExpPath ∧
        (∀ eW < wd₂.W.m, 0 < wd₂.wW eW) ∧ wd₂.W.n = inp.J.n ∧ 0 < wd₂.τ₂ := by
  obtain ⟨mem1, v1, mem2, v2, hT1, hT2, hT3⟩ := hS
  have hs1 := task1OutAt_slots_lt hT1
  obtain ⟨wInp2, WSubs2, η₁, embWJ, _, _, _, _, _, _, hH2, hE2, hJ2, -, hSV2, -, -, hagr2, -, hv12, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hη1lo, hη1, hEmb2, hvc2, -, hlen2, -, -, -, -, -, -,
    hs5_2,
    hO2, hdec2, hhe2⟩ := hT2
  obtain ⟨-, -, -, -, wInp3, WSubs3, embJW, η₂, _, _, _, hH3, hE3, hJ3, -,
    ⟨memPre, memT1, v1', hagrT, -, hT1', hs5_3, hdec3, hSV3, hhe3, hO3⟩, -, -, -, -, -, -, -, -, -, -, -, hEmb3,
    hη2, hec3, -, -, hlen3, -⟩ := hT3
  have hs1' : inp.h + 9 ≤ v1' := task1OutAt_slots_lt hT1'
  have hagr2' : ∀ x < v1, mem2 x = mem1 x := hagr2
  have hs5_2' : mem1 (inp.h + 5) = wInp2.h := hs5_2
  have hs5_3' : memT1 (inp.h + 5) = wInp3.h := hs5_3
  have hH : wInp2.h = wInp3.h := by
    rw [← hs5_2', ← hs5_3', ← hagr2' _ (by omega), hagrT _ (by omega)]
  -- Cells below both heap ends agree.
  have hcell : ∀ x, x < v1 → x < v1' → memT1 x = mem1 x := fun x h1 h2 => by
    rw [← hagrT _ h2, hagr2' _ h1]
  obtain ⟨hb2, hG2, hr2⟩ := outputAt_W_at hO2
  obtain ⟨hb3, hG3, hr3⟩ := outputAt_W_at hO3
  obtain ⟨hd2, hden2, hn2, hw2⟩ := outputAt_wW_at hO2
  obtain ⟨hd3, hden3, hn3, hw3⟩ := outputAt_wW_at hO3
  rw [← hH] at hb3 hG3 hr3 hd3 hden3 hn3 hw3
  have hA := hcell _ hb2 hb3
  rw [hA] at hG3 hr3 hn3 hw3
  have hG2' := GraphAt.of_agree_below hG2 hr2 hagr2'
  have hG3' := GraphAt.of_agree_below hG3 hr3 hagrT
  have hW := graphAt_inj hG2' hG3'
  obtain ⟨hp2, hpn2, hpd2, hpm2⟩ := outputAt_prep_cells hO2
  obtain ⟨hp3, hpn3, hpd3, hpm3⟩ := outputAt_prep_cells hO3
  rw [← hH] at hp3 hpn3 hpd3 hpm3
  have hp2' : wInp2.h + 19 < v1 := hp2
  have hp3' : wInp2.h + 19 < v1' := hp3
  have hJ23 : wInp2.prep.J = wInp3.prep.J := hJ2.trans hJ3.symm
  have hpar := mkWitnessData_params_congr (ce := impl.constructExpander)
    (pds := impl.pathDS.params) (S₁ := WSubs2) (S₂ := WSubs3)
    (by rw [← hpn2, ← hpn3, hcell (wInp2.h + 17) (by omega) (by omega)])
    (by rw [← hpd2, ← hpd3, hcell (wInp2.h + 18) (by omega) (by omega)])
    (by rw [← hpm2, ← hpm3, hcell (wInp2.h + 19) (by omega) (by omega)])
    hJ23 (hH2.trans hH3.symm)
    (fun e he => by
      have he' : e < inp.J.m := by
        have h' : wInp2.prep.J = inp.J := hJ2
        rw [← h']; exact he
      exact (hE2 e he').trans (hE3 e he').symm)
  -- The decompositions are read from the same address, so the `J0` edges agree.
  have hj0 : (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).j0Edges =
      (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).j0Edges := by
    have hdec2' : mem1 (inp.h + 3) = wInp2.prep.decAddr := hdec2
    have hdec3' : memT1 (inp.h + 3) = wInp3.prep.decAddr := hdec3
    have hdA : wInp3.prep.decAddr = wInp2.prep.decAddr := by
      rw [← hdec2', ← hdec3', hcell (inp.h + 3) (by omega) (by omega)]
    have hpe3 : wInp3.prep.h ≤ wInp3.prep.hEnd := by
      unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
    have hhe3' : wInp3.prep.hEnd ≤ wInp3.h := hhe3
    have hreg3 := hSV3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have D3 := ListAt.of_agree_below hSV3.2.2.2.2.2.2.1 (h₀ := v1') (by omega)
      (fun k hk => hagrT k hk)
    have D2 := hSV2.2.2.2.2.2.2.1
    rw [hdA] at D3
    have hll : wInp2.prep.level.length = wInp3.prep.level.length := by
      rw [hSV2.2.2.2.2.2.2.2.1, hSV3.2.2.2.2.2.2.2.1, hSV2.2.2.1, hSV3.2.2.1, hJ23]
    obtain ⟨hℓ, -, -, hlvl, hcs⟩ := decomposeOutAt_inj D2 D3 hll
    show wInp2.prep.j0Edges = wInp3.prep.j0Edges
    unfold PrepInput.j0Edges PrepInput.decomp
    rw [hℓ, hlvl, hcs, hSV2.2.2.1, hSV3.2.2.1, hSV2.2.2.2.2.1, hSV3.2.2.2.2.1, hJ23]
  refine ⟨_, _, embWJ, embJW, hW, fun eW heW => ?_, hEmb2, hEmb3, hpar.1, hpar.2.1, hpar.2.2.1,
    hpar.2.2.2.1, hpar.2.2.2.2.1, hpar.2.2.2.2.2.1, hpar.2.2.2.2.2.2, hj0, η₁, η₂, hη1lo, hη1, hη2,
    hvc2, hlen2, hec3, hlen3,
    outputAt_wW_pos hO2 (by
      have := hSV2.2.2.2.2.2.2.2.2.1; have := hSV2.2.2.2.2.2.2.2.2.2.1; omega),
    by show wInp2.prep.J.n = inp.J.n; rw [show wInp2.prep.J = inp.J from hJ2],
    mkWitnessData_τ₂_pos hSV2.2.2.2.2.2.2.2.2.1 hSV2.2.2.2.2.2.2.2.2.2.1⟩
  have heW3 : eW < (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).W.m := by
    rw [← hW]; exact heW
  have e2 := hw2 eW heW
  have e3 := hw3 eW heW3
  rw [← hW] at e3
  have hden : (wInp2.prep.phiDen_dec : ℝ) = (wInp3.prep.phiDen_dec : ℝ) := by
    rw [← hden2, ← hden3, hcell _ hd2 hd3]
  have hm : (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m =
      (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).W.m := by rw [hW]
  have hn2' : mem1 (wInp2.h + 13) +
      (2 + 2 * (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m) +
      (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m ≤ v1 := hn2
  have hn3' : mem1 (wInp2.h + 13) +
      (2 + 2 * (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m) +
      (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m ≤ v1' := by
    rw [hm]; exact hn3
  have hx := hcell (mem1 (wInp2.h + 13) +
      (2 + 2 * (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W.m) + eW)
    (by clear hn3 hn2 hm; omega) (by clear hn3 hn2 hm; omega)
  rw [← e2, ← e3, hden, hx]

end MinCostFlow.Spanner
