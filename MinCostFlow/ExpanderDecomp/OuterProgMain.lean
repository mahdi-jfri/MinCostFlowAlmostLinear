module

public import MinCostFlow.ExpanderDecomp.OuterProgMainBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Top-Level Outer Expander Decomposition Specification (`OuterProgMain`)

Proves `outerDecompMainProc_spec`, instantiates `outerDecompModule : OuterDecompModule`, and
derives `outerDecompModule_noRand`, `outerDecomp_runsTo`, and
`expanderDecompositionUsed_of_router_and_stepB`, re-exporting `OuterProgMainBase`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 5. Main Entry Contract Proof and `OuterDecompModule` -/

/-- **Main contract theorem for the outer expander-decomposition module:**
when `outerDecompProcs base coreAdapterIdx routeIdx` is installed at `base` in `p`, with an
outer-to-core adapter meeting `coreAdapterContract` at `coreAdapterIdx` and a static router meeting
`routeOrCutContract` at `routeIdx`, procedure `base` meets
`outerDecompEntryContract (outerDecompK C_core C_rt) (outerDecompSpaceC C_sp) w`. -/
theorem outerDecompMainProc_spec
    {base coreAdapterIdx routeIdx w C_core C_rt C_sp_core C_sp_rt C_sp : ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {p : Program}
    (hHas : p.HasAt base (outerDecompProcs base coreAdapterIdx routeIdx))
    (hcoreCost : ∀ M r, CoreCostBounded ParamConfig.default M r (coreCost M r))
    (hsp_core : C_sp_core ≤ C_sp) (hsp_rt : C_sp_rt ≤ C_sp)
    (hCore : ∀ M r, MeetsContract w p coreAdapterIdx
      (coreAdapterContract M r (coreCost M r) C_core C_sp_core w))
    (hRoute : MeetsContract w p routeIdx (routeOrCutContract C_rt C_sp_rt w)) :
    MeetsContract w p base
      (outerDecompEntryContract (outerDecompK C_core C_rt) (outerDecompSpaceC C_sp) w) := by
  refine meetsContract_of_runs
    (by simpa [outerDecompProcs] using hHas 0 (by simp [outerDecompProcs]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gAddr, r, outAddr, h, G, rfl, hG_at, hv, _hloop, hM_thr, hr_eq, hZero,
    hgH, houtH, hdisjOG, hSpace, h16⟩
  set cfg := ParamConfig.default
  set n := G.n
  set M := G.m
  change gAddr + 2 + 2 * M ≤ h at hgH
  change outAddr + n ≤ h at houtH
  change DisjointRange outAddr n gAddr (2 + 2 * M) at hdisjOG
  have hM4 : 4 ≤ M := le_trans (four_le_thresholdB1 envelopeCr) hM_thr
  have hr1 : 1 ≤ r := by rw [hr_eq]; exact one_le_rOf (by omega)
  have hrl : r ≤ ell M := by rw [hr_eq]; exact rOf_le_ell M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have h2M_pow : 2 * M ≤ (NOf M r) ^ r := by
    have := two_mul_add_two_le_NOf_pow M hr1; omega
  have h2M_L : 2 * M < 2 ^ LParam M := by
    have := NOf_pow_add_two_le_two_pow_L M hr1 hrl; omega
  have hTot_sp : totalTimeRaw cfg n M r + 1 ≤
      outerDecompSpace (outerDecompSpaceC C_sp) n M (totalTimeRaw cfg n M r) :=
    totalTimeRaw_le_outerDecompSpace C_sp n M (totalTimeRaw cfg n M r)
  have hTree_sp : 13 + 3 * n + recTreeSpace (DOut cfg M r)
        (recPerEdgeSpace cfg C_sp M r 80) (recPerWitSpace cfg M r) M ≤
      outerDecompSpace (outerDecompSpaceC C_sp) n M (totalTimeRaw cfg n M r) := by
    rw [hr_eq]
    exact outerRec_treeSpace_le_outerDecompSpace (cfg := cfg) (C_sp := C_sp)
      (routeC := 80) (n := n) (M := M)
  have hSpace' : h + outerDecompSpace (outerDecompSpaceC C_sp) n M (totalTimeRaw cfg n M (rOf M)) < 2 ^ w := hSpace
  have hTot_lt : totalTimeRaw cfg n M r < 2 ^ w := by
    rw [hr_eq] at hTot_sp ⊢; linarith only [hTot_sp, hSpace']
  obtain ⟨hQ_le, hN2M_le, hb_le, h4M_le, hn16_le, ha0_le, hkE_le, hA_le, h250_lt⟩ :=
    qOut_add_le_totalTimeRaw (n := n) hM4
  rw [← hr_eq] at hQ_le hN2M_le hb_le h4M_le hn16_le ha0_le hkE_le hA_le h250_lt
  have hr_lt : r < 2 ^ w := hargs r (by simp)
  have hr_L : r ≤ LParam M := by
    have h1 : 2 ^ r ≤ (NOf M r) ^ r := Nat.pow_le_pow_left (by omega) r
    have h2 := NOf_pow_add_two_le_two_pow_L M hr1 hrl
    have h3 : 2 ^ r < 2 ^ LParam M := by omega
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h3)
  -- Subprocedures at `base`
  obtain ⟨hMainProc, hParamsC, hStripC, hRecSub⟩ :=
    outerDecompProcs_subprocs hHas (hcoreCost M r) hsp_core hsp_rt (hCore M r) hRoute
  -- Buffer layout
  let edgesAddr := gAddr + 2
  let paramAddr := h
  set locAddr := h + 12
  set nextLblAddr := locAddr + n
  set verts0Addr := nextLblAddr + 1
  set actVertsAddr := verts0Addr + n
  set h1 := actVertsAddr + n
  have hh1_eq : h1 = h + 13 + 3 * n := by
    dsimp only [h1, actVertsAddr, verts0Addr, nextLblAddr, locAddr]; ring
  have hh1_tree_lt : h1 + recTreeSpace (DOut cfg M r)
        (recPerEdgeSpace cfg C_sp M r 80) (recPerWitSpace cfg M r) M < 2 ^ w := by
    rw [hh1_eq]; rw [hr_eq] at hTree_sp ⊢; linarith only [hTree_sp, hSpace']
  have hh1_lt : h1 < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hh1_tree_lt
  have hmem_g0 : mem gAddr = n := graphAt_n hG_at
  have hmem_g1 : mem (gAddr + 1) = M := graphAt_m hG_at
  have hEdgesG : EdgesAt mem edgesAddr G.edges := graphAt_to_edgesAt hG_at
  -- Block 1 + Block 2: load `n, M`, compute addresses
  let st0 := startState [gAddr, r, outAddr, h] mem pos
  have hSetupA : Triple w p (fun s => s = st0)
      (.assign 4 (.load (.reg 0)) ;;
       .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
       .assign 6 (.bin .add (.reg 0) (.const 2)) ;;
       .assign 7 (.reg 3) ;;
       .assign 8 (.bin .add (.reg 7) (.const 12)))
      (normalPost fun s' => s'.mem = mem ∧
        s'.regs 0 = gAddr ∧ s'.regs 1 = r ∧ s'.regs 2 = outAddr ∧ s'.regs 3 = h ∧
        s'.regs 4 = n ∧ s'.regs 5 = M ∧ s'.regs 6 = edgesAddr ∧
        s'.regs 7 = paramAddr ∧ s'.regs 8 = locAddr)
      (fun _ => 35) := by
    intro s ω hs; subst s
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := n) (by simp [Expr.eval, st0, startState, hmem_g0]) ?_
    refine runs_seq_assign_le (v := M)
      (by simp [Expr.eval, BinOp.eval, st0, startState, (by omega : 1 < 2 ^ w),
            (by omega : gAddr + 1 < 2 ^ w), hmem_g1]) ?_
    refine runs_seq_assign_le (v := edgesAddr)
      (by simp [Expr.eval, BinOp.eval, st0, startState, (by omega : 2 < 2 ^ w),
            (by omega : gAddr + 2 < 2 ^ w), edgesAddr]) ?_
    refine runs_seq_assign_le (v := paramAddr) (by simp [Expr.eval, st0, startState, paramAddr]) ?_
    refine runs_assign_le (v := locAddr)
      (by simp [Expr.eval, BinOp.eval, (by omega : 12 < 2 ^ w), (by omega : h + 12 < 2 ^ w), locAddr, paramAddr])
      ⟨rfl, by simp [st0, startState], by simp [st0, startState], by simp [st0, startState],
        by simp [st0, startState], by simp, by simp, by simp, by simp, by simp⟩
      (by simp [Expr.size])
  rcases hSetupA st0 ω rfl with ⟨oA, stA, cA, hrunA, hqA, hcA⟩
  cases oA with
  | returned _ => exact False.elim hqA
  | normal =>
    rcases hqA with ⟨hA_mem, hA_0, hA_1, hA_2, hA_3, hA_4, hA_5, hA_6, hA_7, hA_8⟩
    have hSetupB : Triple w p (fun s => s = stA)
        (.assign 12 (.bin .add (.reg 8) (.reg 4)) ;;
         .assign 9 (.bin .add (.reg 12) (.const 1)) ;;
         .assign 10 (.bin .add (.reg 9) (.reg 4)) ;;
         .assign 13 (.bin .add (.reg 10) (.reg 4)))
        (normalPost fun s' => s'.mem = mem ∧
          s'.regs 1 = r ∧ s'.regs 2 = outAddr ∧ s'.regs 4 = n ∧ s'.regs 5 = M ∧
          s'.regs 6 = edgesAddr ∧ s'.regs 7 = paramAddr ∧ s'.regs 8 = locAddr ∧
          s'.regs 9 = verts0Addr ∧ s'.regs 10 = actVertsAddr ∧ s'.regs 12 = nextLblAddr ∧
          s'.regs 13 = h1)
        (fun _ => 25) := by
      intro s ω hs; subst s
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := nextLblAddr)
        (by simp [Expr.eval, BinOp.eval, hA_8, hA_4, (by omega : locAddr + n < 2 ^ w), nextLblAddr]) ?_
      refine runs_seq_assign_le (v := verts0Addr)
        (by simp [Expr.eval, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : nextLblAddr + 1 < 2 ^ w), verts0Addr]) ?_
      refine runs_seq_assign_le (v := actVertsAddr)
        (by simp [Expr.eval, BinOp.eval, hA_4, (by omega : verts0Addr + n < 2 ^ w), actVertsAddr]) ?_
      refine runs_assign_le (v := h1)
        (by simp [Expr.eval, BinOp.eval, hA_4, (by omega : actVertsAddr + n < 2 ^ w), h1])
        ⟨hA_mem, by simp [hA_1], by simp [hA_2], by simp [hA_4], by simp [hA_5], by simp [hA_6],
          by simp [hA_7], by simp [hA_8], by simp, by simp, by simp, by simp⟩
        (by simp [Expr.size])
    rcases hSetupB stA ω rfl with ⟨oB, stB, cB, hrunB, hqB, hcB⟩
    cases oB with
    | returned _ => exact False.elim hqB
    | normal =>
      rcases hqB with ⟨hB_mem, hB_1, hB_2, hB_4, hB_5, hB_6, hB_7, hB_8, hB_9, hB_10, hB_12, hB_13⟩
      -- Call `bParams`
      have hParCall := runs_call_of_meetsContract (r := 14) (p := p) (w := w) (st := stB)
        (args := [.reg 4, .reg 5, .reg 1, .reg 7]) (vs := [n, M, r, paramAddr]) hParamsC
        (by simp [evalArgs, Expr.eval, hB_4, hB_5, hB_1, hB_7])
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl
            · linarith only [hn16_le, hTot_lt]
            · linarith only [h4M_le, hTot_lt]
            · exact hr_lt
            · linarith only [hh1_eq, hh1_lt])
        ⟨n, M, r, paramAddr, rfl, hr1, hrl,
          by unfold ComputeParamsWordBound
             refine ⟨by linarith only [hh1_eq, hh1_lt], by linarith only [hn16_le, hTot_lt],
               by linarith only [h4M_le, hTot_lt], by linarith only [hQ_le, hTot_lt],
               by linarith only [ha0_le, hTot_lt], by linarith only [hkE_le, hTot_lt],
               by linarith only [hA_le, hTot_lt]⟩⟩ ω
      rcases hParCall with ⟨stP, cP, _, hrunP, hpostP, _, hP_other, hcP⟩
      dsimp only [computeParamsContract, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at hpostP hcP
      rcases hpostP with ⟨_, hPB_P, hP_fr⟩
      -- Execute `fillRangeStmt` to write `List.range n` at `verts0Addr`
      have hFill := fillRange_triple (w := w) (n := n) (vertsAddr := verts0Addr) p stP
        (by rw [hP_other 4 (by decide), hB_4])
        (by rw [hP_other 9 (by decide), hB_9])
        (by dsimp only [verts0Addr, nextLblAddr, locAddr]; linarith only [hh1_eq, hh1_lt]) h16
      rcases hFill stP ω rfl with ⟨oF, stF, cF, hrunF, hqF, hcF⟩
      cases oF with
      | returned _ => exact False.elim hqF
      | normal =>
        rcases hqF with ⟨hF_V0, hF_fr, hF_other⟩
        have hF_mem_eq : ∀ a, (a < paramAddr ∨ paramAddr + 12 ≤ a) →
            (a < verts0Addr ∨ verts0Addr + n ≤ a) → stF.mem a = mem a := fun a haP haV => by
          rw [hF_fr a haV, hP_fr a haP, hB_mem]
        have hF_E : EdgesAt stF.mem edgesAddr G.edges := fun i hi => by
          change i < M at hi
          refine ⟨?_, ?_⟩
          · rw [hF_mem_eq (edgesAddr + 2 * i)
                  (Or.inl (by dsimp only [edgesAddr, paramAddr]; linarith only [hgH, hi]))
                  (Or.inl (by dsimp only [edgesAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hgH, hi]))]
            exact (hEdgesG i hi).1
          · rw [hF_mem_eq (edgesAddr + 2 * i + 1)
                  (Or.inl (by dsimp only [edgesAddr, paramAddr]; linarith only [hgH, hi]))
                  (Or.inl (by dsimp only [edgesAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hgH, hi]))]
            exact (hEdgesG i hi).2
        have hF_loc0 : ∀ u < n, stF.mem (locAddr + u) = 0 := fun u hu => by
          rw [hF_mem_eq (locAddr + u)
                (Or.inr (by dsimp only [locAddr, paramAddr]; linarith only []))
                (Or.inl (by dsimp only [verts0Addr, nextLblAddr]; linarith only [hu]))]
          exact hZero (locAddr + u) (by dsimp only [locAddr]; linarith only [])
        have hF_nl0 : stF.mem nextLblAddr = 0 := by
          rw [hF_mem_eq nextLblAddr
                (Or.inr (by dsimp only [nextLblAddr, locAddr, paramAddr]; linarith only []))
                (Or.inl (by dsimp only [verts0Addr]; linarith only []))]
          exact hZero nextLblAddr (by dsimp only [nextLblAddr, locAddr]; linarith only [])
        -- Call `bStripIso` on `CompactSubgraph.ofGraph G = ⟨List.range n, G.edges⟩`
        have hStripCall := runs_call_of_meetsContract (r := 14) (p := p) (w := w) (st := stF)
          (args := [.reg 4, .reg 9, .reg 5, .reg 6, .reg 8, .reg 2, .reg 12, .reg 10])
          (vs := [n, verts0Addr, M, edgesAddr, locAddr, outAddr, nextLblAddr, actVertsAddr]) hStripC
          (by simp [evalArgs, Expr.eval,
                hF_other 4 (by decide), hP_other 4 (by decide), hB_4,
                hF_other 9 (by decide), hP_other 9 (by decide), hB_9,
                hF_other 5 (by decide), hP_other 5 (by decide), hB_5,
                hF_other 6 (by decide), hP_other 6 (by decide), hB_6,
                hF_other 8 (by decide), hP_other 8 (by decide), hB_8,
                hF_other 2 (by decide), hP_other 2 (by decide), hB_2,
                hF_other 12 (by decide), hP_other 12 (by decide), hB_12,
                hF_other 10 (by decide), hP_other 10 (by decide), hB_10])
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · linarith only [hn16_le, hTot_lt]
              · dsimp only [verts0Addr, nextLblAddr, locAddr]; linarith only [hh1_eq, hh1_lt]
              · linarith only [h4M_le, hTot_lt]
              · dsimp only [edgesAddr]; linarith only [hgH, hh1_eq, hh1_lt]
              · dsimp only [locAddr]; linarith only [hh1_eq, hh1_lt]
              · linarith only [houtH, hh1_eq, hh1_lt]
              · dsimp only [nextLblAddr, locAddr]; linarith only [hh1_eq, hh1_lt]
              · dsimp only [actVertsAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hh1_eq, hh1_lt])
          ⟨n, n, verts0Addr, M, edgesAddr, locAddr, outAddr, nextLblAddr, actVertsAddr,
            List.range n, G.edges, rfl, List.length_range, List.nodup_range,
            fun u hu => List.mem_range.mp hu, rfl, hv, hF_V0, hF_E, hF_loc0,
            by unfold StripIsoWordBound; rw [hF_nl0]
               dsimp only [verts0Addr, edgesAddr, locAddr, nextLblAddr, actVertsAddr]
               refine ⟨by linarith only [hh1_eq, hh1_lt], by linarith only [hgH, hh1_eq, hh1_lt],
                 by linarith only [hh1_eq, hh1_lt], by linarith only [houtH, hh1_eq, hh1_lt],
                 by linarith only [hh1_eq, hh1_lt], by linarith only [hh1_eq, hh1_lt],
                 by linarith only [hn16_le, hTot_lt], h16⟩,
            by unfold StripIsoDisjoint DisjointRange
               dsimp only [verts0Addr, edgesAddr, locAddr, nextLblAddr, actVertsAddr]
               refine ⟨Or.inl (by linarith only []), Or.inr (by linarith only [hgH]),
                 Or.inr (by linarith only [houtH]), Or.inl (by linarith only []),
                 Or.inl (by linarith only []), Or.inl (by linarith only [houtH]),
                 Or.elim hdisjOG (fun h1 => Or.inl (by linarith only [h1])) (fun h1 => Or.inr (by linarith only [h1])),
                 Or.inl (by linarith only [houtH]), Or.inl (by linarith only [houtH]),
                 Or.inr (by linarith only []), Or.inr (by linarith only [hgH]),
                 Or.inr (by linarith only [houtH]), Or.inl (by linarith only []),
                 Or.inr (by linarith only [hgH])⟩⟩ ω
        rcases hStripCall with ⟨stS, cS, kAct, hrunS, hpostS, hS_14, hS_other, hcS⟩
        dsimp only [stripIsolatedContract, List.getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at hpostS hcS
        have hV0_rd : readList stF.mem verts0Addr n = List.range n := by
          have := readList_eq_of_listAt hF_V0; simpa using this
        have hE_rd : readEdges stF.mem edgesAddr M = G.edges := readEdges_eq_of_edgesAt hF_E
        rw [hV0_rd, hE_rd, hF_nl0] at hpostS
        set iso₀ := (CompactSubgraph.ofGraph G).stripIsolated.1
        set act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
        rcases hpostS with ⟨hkAct_eq, hS_actV, hS_nl, hS_isoLbl, hS_fr⟩
        change kAct = act₀.verts.length at hkAct_eq
        change ListAt stS.mem actVertsAddr act₀.verts at hS_actV
        change stS.mem nextLblAddr = 0 + iso₀.length at hS_nl
        change ∀ u ∈ iso₀, stS.mem (outAddr + u) = 0 + iso₀.idxOf u at hS_isoLbl
        have hrep0 := CompactSubgraph.ofGraph_represents hv
        have hst0 := CompactSubgraph.stripIsolated_spec hrep0
        have he0_eq : act₀.edges = G.edges := hst0.2.2.2.2.2.1
        have he0_len : act₀.edges.length = M := congrArg List.length he0_eq
        have hunion0 : iso₀.toFinset ∪ act₀.vertSet = G.verts := hst0.2.2.1
        have hiso_ltN : ∀ u ∈ iso₀, u < n := fun u hu => by
          have hmem : u ∈ G.verts := hunion0 ▸ Finset.mem_union_left _ (List.mem_toFinset.mpr hu)
          exact Finset.mem_range.mp hmem
        have hiso_nd : iso₀.Nodup := hst0.1
        have hdisj0 : Disjoint iso₀.toFinset act₀.vertSet := hst0.2.1
        have hact_nd : act₀.verts.Nodup := hst0.2.2.2.2.1.1
        have hkAct_le : act₀.verts.length ≤ n := by
          have h1 : act₀.verts.toFinset ⊆ Finset.range n := by
            have hsub : act₀.vertSet ⊆ G.verts := hunion0 ▸ Finset.subset_union_right
            exact hsub
          have h2 := Finset.card_le_card h1
          rw [List.toFinset_card_of_nodup hact_nd, Finset.card_range] at h2; exact h2
        have hiso_act_len : iso₀.length + act₀.verts.length = n := by
          have h1 := congrArg Finset.card hunion0
          rw [Finset.card_union_of_disjoint hdisj0, List.toFinset_card_of_nodup hiso_nd] at h1
          dsimp only [CompactSubgraph.vertSet] at h1
          rw [List.toFinset_card_of_nodup hact_nd, Graph.verts, Finset.card_range] at h1
          exact h1
        have hact_sorted : act₀.verts.Pairwise (· < ·) :=
          pairwise_lt_filter (pairwise_lt_range n) _
        -- Build `RecGlobalEnv` for `outerDecompRecProc_spec`
        have hEnv : RecGlobalEnv cfg M r w G paramAddr locAddr outAddr nextLblAddr h1 :=
          { hA60 := by decide
            hα := inv_default_a0_le_cloudAlpha
            hv := hv
            hr1 := hr1
            hrl := hrl
            hM_eq := rfl
            hN2 := by linarith only [hN4]
            h2M_pow := h2M_pow
            h2M_L := h2M_L
            hparH := by dsimp only [paramAddr]; linarith only [hh1_eq]
            hlocH := by dsimp only [locAddr]; linarith only [hh1_eq]
            hlblH := by linarith only [houtH, hh1_eq]
            hnextH := by dsimp only [nextLblAddr, locAddr]; linarith only [hh1_eq]
            hdPL := Or.inl (by dsimp only [paramAddr, locAddr]; linarith only [])
            hdPLb := Or.inr (by dsimp only [paramAddr]; linarith only [houtH])
            hdPN := Or.inl (by dsimp only [paramAddr, nextLblAddr, locAddr]; linarith only [])
            hdLLb := Or.inr (by dsimp only [locAddr]; linarith only [houtH])
            hdLN := Or.inl (by dsimp only [nextLblAddr]; linarith only [])
            hdLbN := Or.inl (by dsimp only [nextLblAddr, locAddr]; linarith only [houtH])
            hN2M_w := by linarith only [hN2M_le, hTot_lt]
            hwb := by linarith only [hb_le, hTot_lt]
            hwM := by linarith only [h4M_le, hTot_lt]
            hwR := hr_lt
            hwN := by linarith only [hn16_le, hTot_lt]
            hw250 := by linarith only [h250_lt, hTot_lt] }
        have hS_PB : OuterParamBlockAt stS.mem paramAddr cfg n M r := by
          have hp : ∀ j < 12, stS.mem (paramAddr + j) = stP.mem (paramAddr + j) := fun j hj => by
            rw [hS_fr (paramAddr + j) (fun u hu => by
                  have huN := hiso_ltN u hu
                  dsimp only [paramAddr]; linarith only [huN, houtH])
                (by dsimp only [paramAddr, nextLblAddr, locAddr]; linarith only [hj])
                (Or.inl (by dsimp only [paramAddr, actVertsAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hj])),
                hF_fr (paramAddr + j) (Or.inl (by dsimp only [paramAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hj]))]
          exact ⟨by rw [hp 0 (by decide)]; exact hPB_P.1, by rw [hp 1 (by decide)]; exact hPB_P.2.1,
            by rw [hp 2 (by decide)]; exact hPB_P.2.2.1, by rw [hp 3 (by decide)]; exact hPB_P.2.2.2.1,
            by rw [hp 4 (by decide)]; exact hPB_P.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB_P.2.2.2.2.2.1,
            by rw [hp 6 (by decide)]; exact hPB_P.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB_P.2.2.2.2.2.2.2.1,
            by rw [hp 8 (by decide)]; exact hPB_P.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB_P.2.2.2.2.2.2.2.2.2.1,
            by rw [hp 10 (by decide)]; exact hPB_P.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB_P.2.2.2.2.2.2.2.2.2.2.2⟩
        have hS_E : EdgesAt stS.mem edgesAddr act₀.edges := by
          rw [he0_eq]
          intro i hi
          change i < M at hi
          have hm : ∀ j < 2 * M, stS.mem (edgesAddr + j) = stF.mem (edgesAddr + j) := fun j hj =>
            hS_fr (edgesAddr + j) (fun u hu => by
              have huN := hiso_ltN u hu
              dsimp only [edgesAddr]
              rcases hdisjOG with h1 | h1 <;> linarith only [huN, hj, h1])
              (by dsimp only [edgesAddr, nextLblAddr, locAddr]; linarith only [hgH, hj])
              (Or.inl (by dsimp only [edgesAddr, actVertsAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [hgH, hj]))
          exact ⟨by rw [hm (2 * i) (by linarith only [hi])]; exact (hF_E i hi).1,
                 by rw [Nat.add_assoc, hm (2 * i + 1) (by linarith only [hi]), ← Nat.add_assoc]; exact (hF_E i hi).2⟩
        have hS_loc0 : ∀ u < n, stS.mem (locAddr + u) = 0 := fun u hu => by
          rw [hS_fr (locAddr + u) (fun v hv => by
                have hvN := hiso_ltN v hv
                dsimp only [locAddr]; linarith only [hvN, houtH])
              (by dsimp only [nextLblAddr]; linarith only [hu])
              (Or.inl (by dsimp only [actVertsAddr, verts0Addr, nextLblAddr]; linarith only [hu]))]
          exact hF_loc0 u hu
        have hS_zero : ZeroFrom stS.mem h1 := fun a ha => by
          have ha' : actVertsAddr + n ≤ a := ha
          rw [hS_fr a (fun v hv => by
                have hvN := hiso_ltN v hv
                linarith only [hvN, houtH, hh1_eq, ha])
              (by dsimp only [nextLblAddr, locAddr]; linarith only [hh1_eq, ha])
              (Or.inr ha'),
              hF_mem_eq a (Or.inr (by dsimp only [paramAddr]; linarith only [hh1_eq, ha]))
                (Or.inr (by dsimp only [actVertsAddr] at ha'; linarith only [ha']))]
          exact hZero a (by linarith only [hh1_eq, ha])
        -- Call `outerDecompRecProc` via `outerDecompRecProc_spec`
        have hRecArgs : evalArgs w stS
            [.reg 14, .reg 10, .reg 5, .reg 6, .reg 7, .reg 8, .reg 2, .reg 12, .reg 13] =
            some [act₀.verts.length, actVertsAddr, act₀.edges.length, edgesAddr, paramAddr,
              locAddr, outAddr, nextLblAddr, h1] := by
          simp [evalArgs, Expr.eval, hS_14, hkAct_eq, he0_len,
            hS_other 10 (by decide), hF_other 10 (by decide), hP_other 10 (by decide), hB_10,
            hS_other 5 (by decide), hF_other 5 (by decide), hP_other 5 (by decide), hB_5,
            hS_other 6 (by decide), hF_other 6 (by decide), hP_other 6 (by decide), hB_6,
            hS_other 7 (by decide), hF_other 7 (by decide), hP_other 7 (by decide), hB_7,
            hS_other 8 (by decide), hF_other 8 (by decide), hP_other 8 (by decide), hB_8,
            hS_other 2 (by decide), hF_other 2 (by decide), hP_other 2 (by decide), hB_2,
            hS_other 12 (by decide), hF_other 12 (by decide), hP_other 12 (by decide), hB_12,
            hS_other 13 (by decide), hF_other 13 (by decide), hP_other 13 (by decide), hB_13]
        have hRecCall := outerDecompRecProc_spec hEnv hRecSub ω act₀.edges.length
          act₀ actVertsAddr edgesAddr h1 iso₀.length
          (startState [act₀.verts.length, actVertsAddr, act₀.edges.length, edgesAddr, paramAddr,
            locAddr, outAddr, nextLblAddr, h1] stS.mem stS.pos)
          le_rfl hst0.2.2.2.2.1
          (by rw [← hunion0]; exact Finset.subset_union_right)
          hact_sorted hst0.2.2.2.2.2.2.1 (by linarith only [he0_len]) le_rfl
          (by dsimp only [h1]; linarith only [hkAct_le])
          (by dsimp only [edgesAddr]; linarith only [he0_len, hgH, hh1_eq])
          (Or.inl (by dsimp only [actVertsAddr, verts0Addr, nextLblAddr]; linarith only []))
          (Or.inl (by dsimp only [actVertsAddr, verts0Addr, nextLblAddr, locAddr]; linarith only [houtH]))
          (Or.inl (by dsimp only [actVertsAddr, verts0Addr]; linarith only []))
          (Or.inr (by dsimp only [edgesAddr, locAddr]; linarith only [he0_len, hgH]))
          (Or.elim hdisjOG
            (fun h1 => Or.inl (by dsimp only [edgesAddr]; linarith only [h1]))
            (fun h1 => Or.inr (by dsimp only [edgesAddr]; linarith only [he0_len, h1])))
          (Or.inr (by dsimp only [edgesAddr, nextLblAddr, locAddr]; linarith only [he0_len, hgH]))
          hS_PB hS_actV hS_E hS_loc0 (by simpa [startState] using hS_nl) (by linarith only [hiso_act_len]) hS_zero
          (by rw [he0_len]; exact hh1_tree_lt)
          (by simp [startState]) (by simp [startState]) (by simp [startState])
          (by simp [startState]) (by simp [startState]) (by simp [startState])
          (by simp [startState]) (by simp [startState]) (by simp [startState])
        rcases hRecCall with ⟨hEnd, stRec, cRec, hrunRec, o, hoSpec, hoLbl, _, _, _, _, _, hRec_fr, hcRec⟩
        have hCallRec : Runs w p ω
            (.call 13 (outerMainIndicesOf base).bRec
              [.reg 14, .reg 10, .reg 5, .reg 6, .reg 7, .reg 8, .reg 2, .reg 12, .reg 13])
            stS .normal { stS with mem := stRec.mem, regs := Function.update stS.regs 13 hEnd, pos := stRec.pos }
            (argsSize [.reg 14, .reg 10, .reg 5, .reg 6, .reg 7, .reg 8, .reg 2, .reg 12, .reg 13] + cRec + 1) :=
          runs_call_iff.mpr ⟨_, _, .returned hEnd, stRec, cRec, hRecArgs, hRecSub.hSelf, hrunRec, rfl, rfl, rfl⟩
        let stAfterRec : State :=
          { stS with mem := stRec.mem, regs := Function.update stS.regs 13 hEnd, pos := stRec.pos }
        have hRet : Runs w p ω (.ret (.const 0)) stAfterRec (.returned 0) stAfterRec 2 :=
          runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
        have hrunAll : Runs w p ω (outerDecompMainProc (outerMainIndicesOf base)) st0
            (.returned 0) stAfterRec
            (cA + (cB + (cP + (cF + (cS + ((argsSize [.reg 14, .reg 10, .reg 5, .reg 6, .reg 7,
              .reg 8, .reg 2, .reg 12, .reg 13] + cRec + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨stA, cA, _, hrunA,
            runs_seq_iff.mpr (Or.inr ⟨stB, cB, _, hrunB,
              runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
                runs_seq_iff.mpr (Or.inr ⟨stF, cF, _, hrunF,
                  runs_seq_iff.mpr (Or.inr ⟨stS, cS, _, hrunS,
                    runs_seq_iff.mpr (Or.inr ⟨stAfterRec, _, 2, hCallRec, hRet, rfl⟩),
                    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        -- Combine `LabelsMatchParts` across `iso₀` and `act₀` and bridge to `IsExpanderDecomposition`
        have hisoLbl_end : LabelsMatchParts stRec.mem outAddr iso₀.toFinset
            (iso₀.map fun v => ({v} : Finset ℕ)) 0 (0 + iso₀.length) :=
          labelsMatchParts_singleton_list fun u hu => by
            have huN := hiso_ltN u hu
            rw [hRec_fr (outAddr + u) (by linarith only [huN, houtH, hh1_eq]) (fun v hv => by
                  have huv : u ≠ v := fun h => Finset.disjoint_left.mp hst0.2.1 (List.mem_toFinset.mpr hu) (h ▸ hv)
                  intro heq; exact huv (Nat.add_left_cancel heq))
                (by dsimp only [nextLblAddr, locAddr]; linarith only [huN, houtH])]
            exact hS_isoLbl u hu
        have hAllLbl : LabelsMatchParts stRec.mem outAddr G.verts
            ((iso₀.map fun v => ({v} : Finset ℕ)) ++ o.parts) 0 (stRec.mem nextLblAddr) := by
          rw [← hunion0]
          exact labelsMatchParts_union hst0.2.1 hisoLbl_end (by rw [Nat.zero_add]; exact hoLbl)
        have hBridge := isExpanderDecomposition_of_outerRecSpec hv hoSpec hAllLbl
        rcases hBridge with ⟨_, hExpDecomp, _, heSum_le, hwSum_le⟩
        have hE_eq : (1 : ℝ) / (cfg.E : ℝ) = 1 / 200 := by unfold cfg ParamConfig.default; norm_num
        rw [hE_eq, hr_eq] at hExpDecomp
        refine ⟨.returned 0, stAfterRec, _, hrunAll, ?_, ?_⟩
        · dsimp only [outerDecompEntryContract, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [readGraph_eq_of_graphAt hG_at]
          refine ⟨readList stRec.mem outAddr G.n, fun i hi => by simp [stAfterRec, readList], hExpDecomp⟩
        · dsimp only [outerDecompEntryContract, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [readGraph_eq_of_graphAt hG_at]
          have hRec_tot :
              o.edgeSum * recPerEdgeCost cfg C_core C_rt M r 80 +
                o.witnessEdgeSum * recPerWitCost cfg M r + 600 ≤
              outerRecCostK C_core C_rt 80 * totalTimeRaw cfg n M r + 600 :=
            outerRec_cost_le_totalTimeRaw hr_L heSum_le hwSum_le
          have hOver := topLevelOverhead_le (n := n) hM4
          rw [← hr_eq] at hOver
          dsimp at hcA hcB hcF
          simp only [argsSize, Expr.size, Nat.add_zero] at hcP hcS
          have hK_dist : outerDecompK C_core C_rt * totalTimeRaw cfg n M r + outerDecompK C_core C_rt =
              (outerRecCostK C_core C_rt 80 * totalTimeRaw cfg n M r + 600) +
                (2000 * totalTimeRaw cfg n M r + 1400) + outerRecCostK C_core C_rt 80 := by
            unfold outerDecompK; ring
          rw [← hr_eq]
          change _ ≤ outerDecompK C_core C_rt * totalTimeRaw cfg n M r + outerDecompK C_core C_rt
          simp only [argsSize, Expr.size, Nat.add_zero]
          linarith only [hcA, hcB, hcP, hcF, hcS, hcRec, hRec_tot, hOver, hK_dist]

/-- Concrete outer expander-decomposition module implementing `Used.OuterDecompModule` using
`outerDecompProcs` and `outerDecompMainProc_spec`. -/
noncomputable def outerDecompModule (K_B C_rt S_B C_sp_rt : ℕ) :
    OuterDecompModule K_B C_rt S_B C_sp_rt where
  procs := outerDecompProcs
  entryOff := 0
  K_out := outerDecompK (coreAdapterTimeConst K_B (C_rt + 2000) (C_rt + 1000)) C_rt
  C_sp_out := outerDecompSpaceC (max (coreAdapterSpaceConst S_B C_sp_rt) C_sp_rt)
  meets := fun base coreAdapterIdx routeIdx w p hHas hCore hRoute => by
    simpa only [Nat.add_zero] using
      outerDecompMainProc_spec (C_sp := max (coreAdapterSpaceConst S_B C_sp_rt) C_sp_rt)
        hHas coreAdapterCost_le (le_max_left _ _) (le_max_right _ _) hCore hRoute

/-- Every procedure in `outerDecompModule` is deterministic (`NoRand`). -/
theorem outerDecompModule_noRand (K_B C_rt S_B C_sp_rt base coreAdapterIdx routeIdx : ℕ) :
    ∀ s ∈ (outerDecompModule K_B C_rt S_B C_sp_rt).procs base coreAdapterIdx routeIdx, s.NoRand :=
  outerDecompProcs_noRand base coreAdapterIdx routeIdx

/-- End-to-end execution theorem (`RunsTo`) for `decompEntryProc base` paired with
`outerDecompProcs base coreAdapterIdx routeIdx` on any valid loopless graph `G` with
`thresholdB1 envelopeCr ≤ G.m`. -/
theorem outerDecomp_runsTo
    {base coreAdapterIdx routeIdx C_core C_rt C_sp_core C_sp_rt C_sp : ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {p : Program}
    (h0 : p.HasAt 0 [decompEntryProc base])
    (hHas : p.HasAt base (outerDecompProcs base coreAdapterIdx routeIdx))
    (hcoreCost : ∀ M r, CoreCostBounded ParamConfig.default M r (coreCost M r))
    (hsp_core : C_sp_core ≤ C_sp) (hsp_rt : C_sp_rt ≤ C_sp)
    (hCore : ∀ w M r, MeetsContract w p coreAdapterIdx
      (coreAdapterContract M r (coreCost M r) C_core C_sp_core w))
    (hRoute : ∀ w, MeetsContract w p routeIdx (routeOrCutContract C_rt C_sp_rt w))
    {G : Graph} (hv : G.IsValid) (hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m)
    (ω : ℕ → Bool) :
    ∃ (out : List ℕ) (steps : ℕ),
      RunsTo (wordSize (decompEntryWordC (outerDecompSpaceC C_sp)) (G.encode ++ [1, 200, rOf G.m])) p
        (G.encode ++ [1, 200, rOf G.m]) ω out steps ∧
      IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
        ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
          (decompEntryK (outerDecompK C_core C_rt) *
            Real.log ((G.m : ℝ) + 2) ^
              (decompEntryK (outerDecompK C_core C_rt) * (rOf G.m : ℝ) ^ 2)))
        out ∧
      (steps : ℝ) ≤ decompEntryK (outerDecompK C_core C_rt) *
        (G.n + ((G.m : ℝ) + 2) ^ (1 + decompEntryK (outerDecompK C_core C_rt) / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^
            (decompEntryK (outerDecompK C_core C_rt) * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) :=
  decompEntry_runsTo h0
    (fun w => outerDecompMainProc_spec hHas hcoreCost hsp_core hsp_rt (hCore w) (hRoute w))
    hv hl hm ω

/-- Instantiation of `Used.expanderDecompositionUsed_of_parts` with the concrete
`outerDecompModule`: any multi-pair static router module and Step B module immediately yield
`ExpanderDecompositionUsed`. -/
theorem expanderDecompositionUsed_of_router_and_stepB
    (hRoute : MultiPairRouterModule)
    (hStepB : StepBModule hRoute.C_rt hRoute.C_sp) :
    ExpanderDecompositionUsed :=
  expanderDecompositionUsed_of_parts hRoute hStepB
    (outerDecompModule hStepB.K_B hRoute.C_rt hStepB.S_B hRoute.C_sp)

end MinCostFlow.ExpanderDecomp
