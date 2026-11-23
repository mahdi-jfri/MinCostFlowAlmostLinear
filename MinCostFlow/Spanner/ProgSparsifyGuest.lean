module

public import MinCostFlow.Spanner.ProgSparsifyGuestBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Guest `[0, heap]` Contract, `SparsifyImpl` Instance, and `MGraph` Translation for `Sparsify`

Proves the end-to-end guest contract, constructs the deterministic `DynSpanner.Program.SparsifyImpl`
instance from the fixed Word-RAM program `sparsifyGuestProgram impl`, and lifts the execution
directly to `MGraph` / `MinCostFlow.Embedding`:

1. `sparsifyGuest_meetsContract`: `sparsifyGuestProgram impl` meets
   `DynSpanner.Program.sparsifyGuestContractWithTime` at every edge cap `mMax` and word width `w`
   on all valid inputs (including empty graphs).
2. `sparsifyImplOfTools`: constructs a `DynSpanner.Program.SparsifyImpl` from `impl : SpannerToolImpl`,
   `invB : impl.decompose.InvPhiBound`, and the `NoRand` determinism hypotheses of the three tool
   procedure lists, with all constants independent of the input.
3. `sparsifyGuest_mGraph_correct`: lifts the Word-RAM execution directly to `MGraph` /
   `MinCostFlow.Embedding` via `DynSpanner.Program.mGraph_props_of_citedSparsifyProp`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited MinCostFlow.DynSpanner.Program

/-! ### Main guest contract theorem -/

/-- `sparsifyGuestProgram impl` meets `DynSpanner.Program.sparsifyGuestContractWithTime` at every
edge cap `mMax` and word width `w` on all valid inputs. -/
theorem sparsifyGuest_meetsContract (impl : SpannerToolImpl)
    (invB : impl.decompose.InvPhiBound) :
    ∃ (C_sp c_sp cw : ℕ),
      6 ≤ C_sp ∧ 2 ≤ cw ∧
      (∀ heap mVal s, 3 ≤ heap → s ≤ 3 * (heap + mVal) →
        heap + C_sp * (s + 2) ^ c_sp < (heap + mVal + 2) ^ cw) ∧
      (∀ mMax w : ℕ,
        MeetsContract w (sparsifyGuestProgram impl) 0
          (sparsifyGuestContractWithTime mMax
            (sparsifyGuestGammaC impl mMax) (sparsifyGuestGammaL impl mMax)
            (sparsifyGuestKs impl) 1
            (sparsifyGuestKt impl) (sparsifyGuestGammaT impl mMax) 1
            cw (fun s => C_sp * (s + 2) ^ c_sp) w)) := by
  obtain ⟨C_sp, c_sp, cw, hCsp6, hcw2, hcw_space, hpoly⟩ :=
    sparsify_poly_space_and_wordWidth impl invB
  refine ⟨C_sp, c_sp, cw, hCsp6, hcw2, hcw_space, fun mMax w => ?_⟩
  have hproc0 : (sparsifyGuestProgram impl).procs[0]? = some (sparsifyGuestBody 1) := by
    simp [sparsifyGuestProgram, sparsifyGuestModule]
  have hsp1 : MeetsContract w (sparsifyGuestProgram impl) 1 (sparsifyContract impl w) :=
    sparsifyModule_meetsContract fun i hi => by
      simp [sparsifyGuestProgram, sparsifyGuestModule, Nat.add_comm 1 i, hi]
  refine meetsContract_of_runs hproc0 fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨⟨heap, H', J, embJH, rfl, hw16, hheap3, hHle, hJle, hEmble,
    hH, hJ, hEmb, hBnd, hHval, hJval, hIsEmb, hJm, hLen_imp, hcw_w⟩, hzf, hsp_lt⟩
  have hheapArg : heapArg [0, heap] = heap := rfl
  rw [hheapArg] at hzf hsp_lt
  have hJread : readGraph mem (mem 1) = J := graphAt_iff_readGraph.mp hJ
  have hlen_read : readCitedEmbLen mem (mem 2) J.m = length J embJH :=
    readCitedEmbLen_eq_length hEmb hIsEmb
  set inp : Task1Input := Task1Input.mk (mem 0) (mem 1) (mem 2) heap H' J embJH
  have hs_eq : sparsifyInputSize inp = citedInputSize mem := by
    rw [citedInputSize_eq hH hJ hEmb]; rfl
  have hquad : sparsifyInputSize inp ≤ 2 * (heap + citedMaxWord mem heap + 2) ^ 2 := by
    rw [hs_eq]; exact citedInputSize_le_quad hHle hJle hH hJ hEmb hBnd
  have hJenc_le : ∀ x ∈ J.encode, x ≤ citedMaxWord mem heap :=
    mem_encode_le_citedMaxWord hJ hJle
  obtain ⟨hmax_le, hww⟩ := hpoly inp w hHval hJval hIsEmb
  obtain ⟨hwok1, hwokS⟩ := hww (citedMaxWord mem heap) hheap3 hquad hJenc_le hw16 hcw_w
  have hheap_w : heap < 2 ^ w := hwords heap (by simp)
  have h6_le_sp : 6 ≤ C_sp * (citedInputSize mem + 2) ^ c_sp := by
    have hpow : 1 ≤ (citedInputSize mem + 2) ^ c_sp := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hCsp6, hpow]
  have hsp_lt' : heap + C_sp * (citedInputSize mem + 2) ^ c_sp < 2 ^ w := hsp_lt
  by_cases hJm0 : J.m = 0
  · have hJn_w : J.n < 2 ^ w := hwok1.2.1 J.n (by simp [inp, Cited.Graph.encode])
    obtain ⟨o, st', c, hr, ⟨hval, hagr, hzf', cJtilde, kept, embJJtilde, hProp, hOut⟩, hc⟩ :=
      sparsifyGuestBody_runs_zero (mMax := mMax)
        (le_trans zero_le_one (sparsifyGuestGammaC_ge_one impl mMax))
        (sparsifyGuestGammaL_ge_one impl mMax) (sparsifyGuestKs_nonneg impl)
        hw16 (by omega) hJle hJ hJn_w hJm0 hzf
    refine ⟨o, st', c, hr, ⟨⟨by change heap ≤ o.value; omega,
        by change o.value ≤ heap + C_sp * (citedInputSize mem + 2) ^ c_sp; omega,
        hagr, hval ▸ hzf', trivial⟩,
      heap, H', J, embJH, cJtilde, kept, embJJtilde, rfl, hH, hJ, hEmb, hProp, hval ▸ hOut⟩, ?_⟩
    dsimp only [sparsifyGuestContractWithTime, WordRAM.heapContract]
    rw [hJread, hlen_read]
    have hL1 : 1 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := one_le_one_add_log J.n J.m
    have hγt1 : 1 ≤ sparsifyGuestGammaT impl mMax := sparsifyGuestGammaT_ge_one impl mMax
    have hKt80 : (80 : ℝ) ≤ sparsifyGuestKt impl := by
      unfold sparsifyGuestKt
      have := impl.decompose.hK_dec
      have := sparsifyProgConst_pos impl
      linarith
    have h80_le : (80 : ℝ) ≤ sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ 1 := by
      rw [pow_one]
      have hterm_nn : 0 ≤ (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 *
          (length J embJH : ℝ) := by positivity
      have hB1 : 1 ≤ 1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 *
          (length J embJH : ℝ) := by linarith
      have h1 : (80 : ℝ) ≤ sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax := by nlinarith
      have h2 : (80 : ℝ) ≤ sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
          (1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 *
            (length J embJH : ℝ)) := by nlinarith
      nlinarith
    have hceil : 80 ≤ ⌈sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ 1⌉₊ := by
      exact_mod_cast le_trans h80_le (Nat.le_ceil _)
    omega
  · have hJm_pos : 1 ≤ J.m := by omega
    have hLen1 : 1 ≤ length J embJH := hLen_imp hJm_pos
    obtain ⟨o, st', c, hr, ⟨hlo, hhi, hagr, hzf', cJtilde, kept, embJJtilde, hProp, hOut⟩, hc⟩ :=
      sparsifyGuestBody_runs_pos (mMax := mMax) hsp1 hw16 hheap_w hHle hJle hEmble
        hH hJ hEmb hBnd hHval hJval hIsEmb hJm hJm_pos hzf hwok1 hwokS
    refine ⟨o, st', c, hr, ⟨⟨hlo, le_trans hhi (by rwa [hs_eq] at hmax_le), hagr, hzf', trivial⟩,
      heap, H', J, embJH, cJtilde, kept, embJJtilde, rfl, hH, hJ, hEmb, hProp, hOut⟩, ?_⟩
    dsimp only [sparsifyGuestContractWithTime, WordRAM.heapContract]
    rw [hJread, hlen_read]
    exact le_trans hc (guest_cost_bound_pos (impl := impl) (inp := inp) hIsEmb hJ hEmb hJm hJm_pos hLen1)

/-! ### `DynSpanner.Program.SparsifyImpl` instance -/

/-- Deterministic `DynSpanner.Program.SparsifyImpl` instance built from the single fixed Word-RAM
program `sparsifyGuestProgram impl`, taking `invB : impl.decompose.InvPhiBound` and the `NoRand`
determinism facts of the three tool procedure lists as hypotheses. All constants (`K_s`, `p_s`,
`K_t`, `p_t`, `cw`, `C_space`, `c_space`) and `procs` are independent of the input and `mMax`. -/
noncomputable def sparsifyImplOfTools (impl : SpannerToolImpl)
    (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    DynSpanner.Program.SparsifyImpl :=
  let h := sparsifyGuest_meetsContract impl invB
  let C_sp := Classical.choose h
  let h1 := Classical.choose_spec h
  let c_sp := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let cw := Classical.choose h2
  let h3 := Classical.choose_spec h2
  { γ_c := sparsifyGuestGammaC impl
    γ_ℓ := sparsifyGuestGammaL impl
    K_s := sparsifyGuestKs impl
    p_s := 1
    K_t := sparsifyGuestKt impl
    γ_t := sparsifyGuestGammaT impl
    p_t := 1
    cw := cw
    space := fun s => C_sp * (s + 2) ^ c_sp
    C_space := C_sp
    c_space := c_sp
    hγ_c := sparsifyGuestGammaC_ge_one impl
    hγ_ℓ := sparsifyGuestGammaL_ge_one impl
    hK_s := sparsifyGuestKs_nonneg impl
    hK_t := sparsifyGuestKt_nonneg impl
    hγ_t := sparsifyGuestGammaT_ge_one impl
    hcw := h3.2.1
    hC_space := le_trans (by omega : 1 ≤ 6) h3.1
    hspace_le := fun _ => le_rfl
    hcw_space := h3.2.2.1
    procs := sparsifyGuestModule impl
    hprocs_nonempty := sparsifyGuestModule_nonempty impl
    hprocs_noRand := sparsifyGuestProgram_isDeterministic impl hdec hce hds
    spec := h3.2.2.2 }

theorem sparsifyImplOfTools_γ_c (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).γ_c = sparsifyGuestGammaC impl := rfl

theorem sparsifyImplOfTools_γ_ℓ (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).γ_ℓ = sparsifyGuestGammaL impl := rfl

theorem sparsifyImplOfTools_K_s (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).K_s = sparsifyGuestKs impl := rfl

theorem sparsifyImplOfTools_p_s (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).p_s = 1 := rfl

theorem sparsifyImplOfTools_K_t (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).K_t = sparsifyGuestKt impl := rfl

theorem sparsifyImplOfTools_γ_t (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).γ_t = sparsifyGuestGammaT impl := rfl

theorem sparsifyImplOfTools_p_t (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).p_t = 1 := rfl

theorem sparsifyImplOfTools_procs (impl : SpannerToolImpl) (invB : impl.decompose.InvPhiBound)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyImplOfTools impl invB hdec hce hds).procs = sparsifyGuestModule impl := rfl

/-! ### `MGraph` translation theorem -/

private lemma guestComposeAux_congr (G : Cited.Graph) (f g : ℕ → Walk) :
    ∀ (vs js : List ℕ), (∀ e ∈ js, e < G.m) → (∀ e < G.m, f e = g e) →
      composeAux G f vs js = composeAux G g vs js
  | [], [], _, _ => rfl
  | [_], [], _, _ => rfl
  | _ :: _ :: _, [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | [_], _ :: _, _, _ => rfl
  | u :: v :: vs, e :: es, hWe, hfg => by
    simp only [composeAux]
    rw [hfg e (hWe e (List.mem_cons_self ..)),
      guestComposeAux_congr G f g (v :: vs) es (fun e' he' => hWe e' (List.mem_cons_of_mem e he')) hfg]

/-- End-to-end `MGraph` execution theorem for `sparsifyGuestProgram impl`: when valid `MGraph`s
`(H', J)` and an embedding `embJH : MinCostFlow.Embedding` are encoded via
`(toCitedH H' J embJH, toCitedJ J, embToCited H' J embJH)` in guest memory `[0 .. heap)`,
running `sparsifyGuestProgram impl` deterministically outputs a `SparsifyOutRelocAt` layout
whose decoded `MGraph` sparsifier `outJtilde J kept` and embedding
`citedEmbToMGraph J cJtilde kept embJJtilde` satisfy all five Theorem 8.1 `MGraph` guarantees
within the Theorem 8.1 Word-RAM time and polynomial space bounds. -/
theorem sparsifyGuest_mGraph_correct (impl : SpannerToolImpl)
    (invB : impl.decompose.InvPhiBound) :
    ∃ (C_sp c_sp cw : ℕ),
      6 ≤ C_sp ∧ 2 ≤ cw ∧
      ∀ (mMax w heap : ℕ) (H' J : MGraph) (embJH : MinCostFlow.Embedding)
        (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        let cH := toCitedH H' J embJH
        let cJ := toCitedJ J
        let cEmb := embToCited H' J embJH
        let space := fun s => C_sp * (s + 2) ^ c_sp
        H'.IsValid → J.IsValid → embJH.IsEmbedding J H' →
        J.m ≤ mMax → (J.E.Nonempty → 1 ≤ embJH.length J) →
        16 ≤ 2 ^ w → 3 ≤ heap →
        mem 0 + cH.encode.length ≤ heap →
        mem 1 + cJ.encode.length ≤ heap →
        mem 2 + cJ.m ≤ heap →
        GraphAt mem (mem 0) cH → GraphAt mem (mem 1) cJ →
        EmbAt mem (mem 2) cJ.m cEmb → EmbBounded mem (mem 2) cJ.m cEmb heap →
        ZeroFrom mem heap →
        heap + space (citedInputSize mem) < 2 ^ w →
        cw * (Nat.log 2 (heap + citedMaxWord mem heap + 2) + 1) ≤ w →
        ∃ (o : Outcome) (st' : State) (c : ℕ)
          (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
          Runs w (sparsifyGuestProgram impl) ω (sparsifyGuestBody 1)
            (startState [0, heap] mem pos) o st' c ∧
          heap ≤ o.value ∧ o.value ≤ heap + space (citedInputSize mem) ∧
          (∀ x < heap, st'.mem x = mem x) ∧ ZeroFrom st'.mem o.value ∧
          SparsifyOutRelocAt st'.mem 0 heap o.value J.m cJtilde kept embJJtilde ∧
          c ≤ ⌈sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
            (1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 *
              (embJH.length J : ℝ)) *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))⌉₊ ∧
          let Jtilde := outJtilde J kept
          let outEmb := citedEmbToMGraph J cJtilde kept embJJtilde
          J.IsSubgraph Jtilde ∧
          outEmb.IsEmbedding J Jtilde ∧
          ((embJH.comp outEmb).vcong J H' (fun _ => 1) ≤
            (sparsifyGuestGammaC impl mMax + 1) * (embJH.length J : ℝ) *
              (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ))) ∧
          (((embJH.comp outEmb).length J : ℝ) ≤
            sparsifyGuestGammaL impl mMax * (embJH.length J : ℝ)) ∧
          ((Jtilde.m : ℝ) ≤ sparsifyGuestKs impl * (J.n : ℝ) *
            sparsifyGuestGammaL impl mMax * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) := by
  obtain ⟨C_sp, c_sp, cw, hCsp6, hcw2, _, hspec⟩ := sparsifyGuest_meetsContract impl invB
  refine ⟨C_sp, c_sp, cw, hCsp6, hcw2, ?_⟩
  intro mMax w heap H' J embJH mem pos ω cH cJ cEmb space
    hH' hJ hembJH hJm hLen hw16 hheap3 hHle hJle hEmble hGH hGJ hEmb hBnd hzf hsp_lt hcw_w
  have hcH_val : cH.IsValid := toCitedH_isValid hH' hJ hembJH
  have hcJ_val : cJ.IsValid := toCitedJ_isValid hJ
  have hcEmb_val : IsEmbedding cJ cH cEmb := embToCited_isEmbedding hJ hembJH
  have hcJ_m : cJ.m = J.m := toCitedJ_m J
  have hcJ_n : cJ.n = J.n := by dsimp only [cJ, toCitedJ]; exact vertsOf_length J.V
  have hcLen_eq : length cJ cEmb = embJH.length J := length_embToCited_eq H' J embJH
  have hcLen_imp : 1 ≤ cJ.m → 1 ≤ length cJ cEmb := fun hm => by
    rw [hcLen_eq]
    refine hLen ?_
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have : J.m = 0 := by simp [MGraph.m, hE]
    omega
  have hJread : readGraph mem (mem 1) = cJ := graphAt_iff_readGraph.mp hGJ
  have hpre : (sparsifyGuestContractWithTime mMax
      (sparsifyGuestGammaC impl mMax) (sparsifyGuestGammaL impl mMax)
      (sparsifyGuestKs impl) 1
      (sparsifyGuestKt impl) (sparsifyGuestGammaT impl mMax) 1
      cw space w).pre [0, heap] mem :=
    ⟨⟨heap, cH, cJ, cEmb, rfl, hw16, hheap3, hHle, hJle, hEmble,
      hGH, hGJ, hEmb, hBnd, hcH_val, hcJ_val, hcEmb_val, by omega, hcLen_imp, hcw_w⟩,
      hzf, hsp_lt⟩
  have hwords : ∀ a ∈ [0, heap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  obtain ⟨body, hbody, o, st', c, hr, hpost, hcost⟩ :=
    hspec mMax w [0, heap] mem pos ω hwords hpre
  have hbody_eq : body = sparsifyGuestBody 1 := by
    simp [sparsifyGuestProgram, sparsifyGuestModule] at hbody; exact hbody.symm
  subst hbody_eq
  rcases hpost with ⟨⟨hlo, hhi, hagr, hzf', _⟩,
    heap', cH', cJ', cEmb', cJtilde, kept, embJJtilde, hargs', hGH', hGJ', hEmb', hProp', hOut'⟩
  have hheap'_eq : heap' = heap := by
    have := List.cons.inj hargs'; exact (List.cons.inj this.2).1.symm
  subst hheap'_eq
  have hcH'_eq : cH' = cH := (graphAt_iff_readGraph.mp hGH').symm.trans (graphAt_iff_readGraph.mp hGH)
  have hcJ'_eq : cJ' = cJ := (graphAt_iff_readGraph.mp hGJ').symm.trans (graphAt_iff_readGraph.mp hGJ)
  subst hcH'_eq; subst hcJ'_eq
  have hcEmb'_eq : ∀ j < cJ.m, cEmb' j = cEmb j := fun j hj =>
    walkAt_inj (hEmb' j hj) (hEmb j hj)
  have hProp : CitedSparsifyProp mMax (sparsifyGuestGammaC impl mMax)
      (sparsifyGuestGammaL impl mMax) (sparsifyGuestKs impl) 1 cH cJ cEmb cJtilde kept embJJtilde := by
    have hlen_eq : length cJ cEmb' = length cJ cEmb := by
      unfold length; exact Finset.fold_congr fun j hj => by rw [hcEmb'_eq j (Finset.mem_range.mp hj)]
    have hvc_eq : vcong cJ cH (fun _ => 1) cEmb' = vcong cJ cH (fun _ => 1) cEmb := by
      unfold vcong vcongAt
      refine Finset.fold_congr fun x _ => ?_
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_congr rfl fun j hj => by rw [hcEmb'_eq j (Finset.mem_range.mp hj)]
    rcases hProp' with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩
    have hcomp_eq : vcong cJ cH (fun _ => 1) (compose cJtilde (restrictEmb cEmb' kept) embJJtilde) =
        vcong cJ cH (fun _ => 1) (compose cJtilde (restrictEmb cEmb kept) embJJtilde) := by
      unfold vcong vcongAt
      refine Finset.fold_congr fun x _ => ?_
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hres_eq : ∀ i < cJtilde.m, restrictEmb cEmb' kept i = restrictEmb cEmb kept i := fun i hi => by
        have hik : i < kept.length := by simpa [Cited.Graph.m, p4] using hi
        unfold restrictEmb
        rw [List.getD_eq_getElem kept 0 hik]
        exact hcEmb'_eq _ (p2 _ (List.getElem_mem hik))
      have hw := p6.2 j (Finset.mem_range.mp hj)
      have hed : ∀ e ∈ (embJJtilde j).edges, e < cJtilde.m := by
        rcases hw with ⟨_, _, ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩⟩
        · intro e he; simp [hPe] at he
        · exact hedges
      have hwalk_eq : compose cJtilde (restrictEmb cEmb' kept) embJJtilde j =
          compose cJtilde (restrictEmb cEmb kept) embJJtilde j :=
        guestComposeAux_congr cJtilde _ _ (embJJtilde j).verts (embJJtilde j).edges hed hres_eq
      rw [hwalk_eq]
    rw [hcomp_eq, hlen_eq, hvc_eq] at p7
    exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩
  have hmg := mGraph_props_of_citedSparsifyProp
    (le_trans zero_le_one (sparsifyGuestGammaC_ge_one impl mMax))
    hH' hJ hJm hLen hembJH hProp
  have hcost_mg : c ≤ ⌈sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
      (1 + (J.n : ℝ) + (J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 * (embJH.length J : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))⌉₊ := by
    dsimp only [sparsifyGuestContractWithTime, WordRAM.heapContract] at hcost
    rw [hJread, readCitedEmbLen_eq_length hEmb hcEmb_val, hcJ_n, hcJ_m, hcLen_eq, pow_one] at hcost
    exact hcost
  refine ⟨o, st', c, cJtilde, kept, embJJtilde, hr, hlo, hhi, hagr, hzf',
    hcJ_m ▸ hOut', hcost_mg, hmg.1, hmg.2.1, hmg.2.2.1, hmg.2.2.2.1, ?_⟩
  simpa [pow_one] using hmg.2.2.2.2

end MinCostFlow.Spanner
