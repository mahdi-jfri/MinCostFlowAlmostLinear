module

public import MinCostFlow.SparseCore.Program.CompInitSetup
import MinCostFlow.SparseCore.CompLSFBounds
import WordRAM.Tactic

/-!
# Initialization Verification (`CompInitProcs`)

Verifies `compInitProc` (`init` of `compLSFDS`): `compLSFDS_init` proves `CompLSFRepAt`,
`CompInitPost`, `DSRep.Respects`, and the exact amortized cost + potential bound
`c + compPhi ≤ compInitCost W k G₀ args` (charging zero window init cost to isolated components).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

set_option maxHeartbeats 600000 in
/-- Full verification of `compInitProc` (`init` of `compLSFDS`). -/
theorem compLSFDS_init {W : LSFWindowImpl} {w k bBfs bDgInit bWin : ℕ} {G₀ : MGraph}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {p : Program}
    (hpBfs : p.procs[bBfs]? = some compBfsCompProc)
    (hpDg : ∀ {vCap eCap} (G : MGraph) (vLs : List ℕ) (eLs : List (ℕ × ℕ × ℕ)),
      MeetsContract w p bDgInit (dgInitFromListsContract w vCap eCap G vLs eLs))
    (hpWin : p.HasAt bWin (W.procs bWin))
    (hpre : (compLSFDS W w k G₀).initPre args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).initSpace args mem < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω (compInitProc W.h bBfs bDgInit (bWin + W.initOff)) (startState args mem pos) o st' c ∧
      ∃ S' x',
        CompLSFRepAt W k (heapArg args) S' x' st'.mem ∧
        (compLSFDS W w k G₀).initPost args mem S' st'.mem ∧
        (compLSFRep W k).Respects (fun _ => False) (heapArg args)
          ((compLSFDS W w k G₀).initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + compPhi (heapArg args) x' st'.mem ≤ (compLSFDS W w k G₀).initCost args mem ∧
        x'.vCap = args.getD 6 0 ∧ x'.eCap = args.getD 7 0 ∧ x'.L_w = args.getD 5 0 := by
  classical
  rcases hpre with ⟨g0Ptr, vCap0, eCap0, lenArr, L_w, vCap, eCap, b, rfl,
    hk, hLw, h2h, hHw, heCap, hw16, hG₀, hV₀, hdg, hvCap_le, heCap_le, hg0_le, hlen_le, hLen, hWinPre⟩
  have hheap_eq : heapArg [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b] = b := rfl
  rw [hheap_eq] at hz hsp ⊢
  obtain ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩ := hdg.2.2.2.2.2.2.2.2.1
  let ctx : InitCtx W w k G₀ p mem :=
    { bBfs, bDgInit, bWin, g0Ptr, vCap0, eCap0, lenArr, L_w, vCap, eCap, b, vL,
      hk, hLw, h2h, hHw, heCap, hw16, hG₀, hV₀, hdg, hvL_len, hvL_nd, hvL_mem, hvL_at,
      hvCap_le, heCap_le, hg0_le, hlen_le, hLen, hWinPre, hargs, hz0 := hz, hsp,
      hpBfs, hpDg := fun G vLs eLs => hpDg G vLs eLs, hpWin }
  -- Step 1: run setup prefix
  obtain ⟨st0, c_set, hrun_set, hR0, hr32_0, hr33_0, hr34_0, hr35_0, hInv0, hc_set⟩ :=
    compInitSetup_runs (ω := ω) ctx
  -- Step 2: run component-discovery loop
  obtain ⟨stL, endAddr, comps, efIdx, winH, winX, c_loop, hrun_loop, hRL, hr32_L, hr33_L, hr34_L,
    hComps_all, hInvL, hc_loop⟩ :=
    compInitLoop_runs (ω := ω) ctx G₀.n 0 [] [] (fun _ _ => 0) (fun _ _ => dummyLSFConcrete) ctx.heap0 st0
      (Nat.zero_le _) (Nat.sub_zero _) (fun _ h => by simp at h) hR0 hr32_0 hr33_0 hr34_0 hr35_0 hInv0
  -- Step 3: run 3 epilogue stores + `ret endAddr`
  have hsp_lt : compTablesEnd b vCap eCap L_w G₀.m k + vCap + G₀.n + 3 * G₀.m +
      (edgefulComps G₀).sum (fun C => dynGraphSize vCap eCap +
        W.winSpace k L_w vCap eCap (compGraph G₀ C).n (compGraph G₀ C).m) < 2 ^ w := ctx.hsp_lt
  have hstat_lt : b + compStaticSize vCap eCap L_w < 2 ^ w := by
    dsimp [compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hnc_le : comps.length ≤ vCap := le_trans (init_numComps_le hInvL.2.2.2.2.1 hInvL.2.2.2.2.2.1)
    (le_trans (by have hsub : G₀.V ⊆ Finset.range vCap0 := fun v hv => Finset.mem_range.mpr (hdg.2.1 v hv)
                  simpa [MGraph.n] using Finset.card_le_card hsub) hvCap_le)
  have hne_le : efIdx.length ≤ G₀.m := le_trans
    (init_numEdgeful_le hInvL.2.2.2.2.1 hInvL.2.2.2.2.2.2.1 hInvL.2.2.2.2.2.2.2.1 hInvL.2.2.2.2.2.2.2.2.1)
    (init_sum_m_le fun X hX => hInvL.2.2.2.2.2.1 X (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1))
  have hend_le_sp : endAddr ≤ b + compInitSpace W k G₀ [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b] := by
    have h1 := hInvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hfilt_eq : (comps.toFinset.filter fun C => 1 ≤ (compGraph G₀ C).m) = edgefulComps G₀ := by
      ext C; simp only [Finset.mem_filter, List.mem_toFinset, edgefulComps, hComps_all]
    rw [hfilt_eq] at h1
    simp only [compInitSpace, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    dsimp only [InitCtx.heap0, compTablesEnd, compHandlesBase, ctx] at h1; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt hoff ⊢; omega
  have hRL8 : stL.regs 8 = b := hRL.r8
  let mf1 := Function.update stL.mem (b + compOffNumComps) comps.length
  let mf2 := Function.update mf1 (b + compOffNumEdgeful) efIdx.length
  let mf3 := Function.update mf2 (b + compOffEndAddr) endAddr
  have he1 : Runs w p ω (.store (.bin .add (.reg 8) (.const compOffNumComps)) (.reg 33))
      stL .normal { stL with mem := mf1 } 5 :=
    runs_store_iff.mpr ⟨b + compOffNumComps, comps.length,
      by have := hb_off compOffNumComps (by decide); simp [Expr.eval, BinOp.eval, hRL8, this.1, this.2],
      by simp [Expr.eval, hr33_L], rfl, rfl, by simp [Expr.size]⟩
  have he2 : Runs w p ω (.store (.bin .add (.reg 8) (.const compOffNumEdgeful)) (.reg 34))
      { stL with mem := mf1 } .normal { stL with mem := mf2 } 5 :=
    runs_store_iff.mpr ⟨b + compOffNumEdgeful, efIdx.length,
      by have := hb_off compOffNumEdgeful (by decide); simp [Expr.eval, BinOp.eval, hRL8, this.1, this.2],
      by simp [Expr.eval, hr34_L], rfl, rfl, by simp [Expr.size]⟩
  have he3 : Runs w p ω (.store (.bin .add (.reg 8) (.const compOffEndAddr)) (.reg 32))
      { stL with mem := mf2 } .normal { stL with mem := mf3 } 5 :=
    runs_store_iff.mpr ⟨b + compOffEndAddr, endAddr,
      by have := hb_off compOffEndAddr (by decide); simp [Expr.eval, BinOp.eval, hRL8, this.1, this.2],
      by simp [Expr.eval, hr32_L], rfl, rfl, by simp [Expr.size]⟩
  have he4 : Runs w p ω (.ret (.reg 32)) { stL with mem := mf3 } (.returned endAddr) { stL with mem := mf3 } 2 :=
    runs_ret_iff.mpr ⟨endAddr, by simp [Expr.eval, hr32_L], rfl, rfl, by simp [Expr.size]⟩
  have hrun_epi : Runs w p ω
      (.store (.bin .add (.reg 8) (.const compOffNumComps)) (.reg 33) ;;
       .store (.bin .add (.reg 8) (.const compOffNumEdgeful)) (.reg 34) ;;
       .store (.bin .add (.reg 8) (.const compOffEndAddr)) (.reg 32) ;;
       .ret (.reg 32)) stL (.returned endAddr) { stL with mem := mf3 } 20 :=
    runs_seq_add he1 (runs_seq_add he2 (runs_seq_add he3 he4))
  have hproc_eq : compInitProc W.h bBfs bDgInit (bWin + W.initOff) =
      (compInitSetupStmt W.h ;; compInitLoop bBfs bDgInit (bWin + W.initOff) ;;
       (.store (.bin .add (.reg 8) (.const compOffNumComps)) (.reg 33) ;;
        .store (.bin .add (.reg 8) (.const compOffNumEdgeful)) (.reg 34) ;;
        .store (.bin .add (.reg 8) (.const compOffEndAddr)) (.reg 32) ;;
        .ret (.reg 32))) := rfl
  have hrun_full : Runs w p ω (compInitProc W.h bBfs bDgInit (bWin + W.initOff))
      (startState [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b] mem pos)
      (.returned endAddr) { stL with mem := mf3 } (c_set + (c_loop + 20 + 1) + 1) := by
    rw [hproc_eq]; exact runs_seq_add hrun_set (runs_seq_add hrun_loop hrun_epi)
  -- Build `S'` and `x'` and prove `CompLSFRepAt`, `CompInitPost`, `Respects`, and cost bound
  set ℓ₀ := compReadLen mem lenArr W.h W.L_in W.P_fp G₀
  set S' : CompLSFFamily k := compLSFInitFamily W.lsfInit G₀ ℓ₀ k
  have hℓ₀_pos : ∀ e ∈ G₀.E, 0 < ℓ₀ e := fun e he => by
    dsimp only [ℓ₀, compReadLen]; simp [he, (hLen e he).2]
  have hC_inj : Function.Injective (fun c : Fin comps.length => comps[c.1]) := fun c1 c2 h =>
    Fin.ext (hInvL.2.2.2.2.1.getElem_inj_iff.mp h)
  have hC_surj : ∀ C, C ∈ components G₀ ↔ ∃ c : Fin comps.length, comps[c.1] = C := fun C =>
    ⟨fun hC => by obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hComps_all C).mp hC); exact ⟨⟨i, hi⟩, rfl⟩,
     fun ⟨c, hc⟩ => hc ▸ (hComps_all _).mpr (List.getElem_mem c.2)⟩
  let edgeC1f : ℕ → ℕ := fun e =>
    if h : ∃ c : Fin comps.length, e ∈ compEdgeSet G₀ comps[c.1] then h.choose.1 else 0
  let x' : CompLSFMeta k :=
    { vCap, eCap, L_w, h := W.h, L_in := W.L_in, P_fp := W.P_fp,
      numComps := comps.length, numEdgeful := efIdx.length, m0Total := G₀.m, endAddr,
      compOf := fun c => comps[c.1],
      edgefulIdx := fun c => if c.1 ∈ efIdx then efIdx.idxOf c.1 else 0,
      edgefulComp := fun ec => ⟨efIdx[ec.1], hInvL.2.2.2.2.2.2.2.1 _ (List.getElem_mem ec.2)⟩,
      edgeC1 := edgeC1f, edgeC2 := edgeC1f,
      gtVert := fun _ => 0, ghVert := fun _ => 0,
      gtList := fun _ => [], ghList := fun _ => [],
      winHandle := fun ec j => winH ec.1 j.1,
      winConc := fun ec j => winX ec.1 j.1 }
  have hmf3_ne : ∀ a, a ≠ b + compOffNumComps → a ≠ b + compOffNumEdgeful → a ≠ b + compOffEndAddr →
      mf3 a = stL.mem a := fun a h1 h2 h3 => by
    dsimp only [mf3, mf2, mf1]; rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hmf3_ge_hdr : ∀ a, b + compHdrSize ≤ a → mf3 a = stL.mem a := fun a ha =>
    hmf3_ne a (by dsimp [compOffNumComps, compHdrSize] at ha ⊢; omega)
      (by dsimp [compOffNumEdgeful, compHdrSize] at ha ⊢; omega)
      (by dsimp [compOffEndAddr, compHdrSize] at ha ⊢; omega)
  have hTE_le : compTablesEnd b vCap eCap L_w G₀.m k ≤ endAddr :=
    le_trans (by dsimp [InitCtx.heap0, ctx]; omega) hInvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- Contiguous region ordering
  have hB_vc : b + compHdrSize = compVCompBase b := rfl
  have hVC_ef : compVCompBase b + vCap = compEdgefulBase b vCap := rfl
  have hEF_efi : compEdgefulBase b vCap + vCap = compEdgefulIdxBase b vCap := rfl
  have hEFI_n0 : compEdgefulIdxBase b vCap + vCap = compN0Base b vCap := rfl
  have hN0_m0 : compN0Base b vCap + vCap = compM0Base b vCap := rfl
  have hM0_ec1 : compM0Base b vCap + vCap = compEdgeC1Base b vCap := rfl
  have hEC1_ec2 : compEdgeC1Base b vCap + eCap = compEdgeC2Base b vCap eCap := rfl
  have hEC2_ic : compEdgeC2Base b vCap eCap + eCap = compIsCrossBase b vCap eCap := rfl
  have hIC_ii : compIsCrossBase b vCap eCap + eCap = compIsInsBase b vCap eCap := rfl
  have hII_gh : compIsInsBase b vCap eCap + eCap = compGhostBase b vCap eCap := rfl
  have hGH_tm : compGhostBase b vCap eCap + (4 * vCap + 6 * eCap) = compTouchMarkBase b vCap eCap := rfl
  have hTM_one : compTouchMarkBase b vCap eCap + vCap = compOneLimbBase b vCap eCap := rfl
  have hOne_h : compOneLimbBase b vCap eCap + L_w = compHandlesBase b vCap eCap L_w :=
    compOneLimb_end_eq b vCap eCap L_w
  have hH_te : compHandlesBase b vCap eCap L_w + G₀.m * k = compTablesEnd b vCap eCap L_w G₀.m k := rfl
  have hRep : CompLSFRepAt W k b S' x' mf3 := by
    refine ⟨hk, rfl, rfl, rfl, hLw, h2h, heCap, hnc_le, hne_le, hTE_le, ?_, ?_, rfl, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hInvL.2.1 with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
        h15, h16, h17, h18, h19, h20⟩
      have hne3 : ∀ off, off ≠ compOffNumComps → off ≠ compOffNumEdgeful → off ≠ compOffEndAddr →
          mf3 (b + off) = stL.mem (b + off) := fun off h1 h2 h3 =>
        hmf3_ne _ (by omega) (by omega) (by omega)
      refine ⟨(hne3 _ (by decide) (by decide) (by decide)).trans h0,
        (hne3 _ (by decide) (by decide) (by decide)).trans h1,
        (hne3 _ (by decide) (by decide) (by decide)).trans h2,
        (hne3 _ (by decide) (by decide) (by decide)).trans h3,
        (hne3 _ (by decide) (by decide) (by decide)).trans h4,
        (hne3 _ (by decide) (by decide) (by decide)).trans h5,
        (hne3 _ (by decide) (by decide) (by decide)).trans h6,
        by dsimp only [mf3, mf2, mf1]; rw [Function.update_of_ne (by dsimp [compOffNumComps, compOffEndAddr]; omega),
          Function.update_of_ne (by dsimp [compOffNumComps, compOffNumEdgeful]; omega), Function.update_self],
        by dsimp only [mf3, mf2]; rw [Function.update_of_ne (by dsimp [compOffNumEdgeful, compOffEndAddr]; omega), Function.update_self],
        (hne3 _ (by decide) (by decide) (by decide)).trans h7,
        (hne3 _ (by decide) (by decide) (by decide)).trans h8,
        (hne3 _ (by decide) (by decide) (by decide)).trans h9,
        (hne3 _ (by decide) (by decide) (by decide)).trans h10,
        (hne3 _ (by decide) (by decide) (by decide)).trans h11,
        (hne3 _ (by decide) (by decide) (by decide)).trans h12,
        (hne3 _ (by decide) (by decide) (by decide)).trans h13,
        (hne3 _ (by decide) (by decide) (by decide)).trans h14,
        (hne3 _ (by decide) (by decide) (by decide)).trans h15,
        (hne3 _ (by decide) (by decide) (by decide)).trans h16,
        (hne3 _ (by decide) (by decide) (by decide)).trans h17,
        (hne3 _ (by decide) (by decide) (by decide)).trans h18,
        (hne3 _ (by decide) (by decide) (by decide)).trans h19,
        Function.update_self _ _ _,
        (hne3 _ (by decide) (by decide) (by decide)).trans h20⟩
    · refine ⟨ℓ₀, fun j => ⟨compLSFInv_initWith (W.hInitValid k j.1 hk j.2) hG₀ hV₀ hℓ₀_pos hk,
        rfl, rfl, rfl, rfl, rfl, fun c => ?_⟩⟩
      have hC := (hComps_all _).mpr (List.getElem_mem c.2)
      dsimp only [S', x', compLSFInitFamily]
      rw [(initCompLSFWith_compSt_basic (W.hInitValid k j.1 hk j.2) hG₀ hℓ₀_pos hk hC).2.1,
        (initCompLSFWith_compSt_basic (W.hInitValid k 0 hk hk) hG₀ hℓ₀_pos hk hC).2.1]
    · refine compEdgeTrack_init (W.hInitValid k 0 hk hk) hG₀ hV₀ hℓ₀_pos hk
        (fun v hv => lt_of_lt_of_le (hdg.2.1 v hv) hvCap_le)
        (fun e he => lt_of_lt_of_le (hdg.2.2.1 e he) heCap_le)
        hC_inj hC_surj fun e he => ?_
      obtain ⟨c, hc⟩ := (hC_surj (compOf G₀ (G₀.tail e))).mp
        (Finset.mem_image.mpr ⟨G₀.tail e, (hG₀ e he).1, rfl⟩)
      have heC : e ∈ compEdgeSet G₀ comps[c.1] := by
        rw [compEdgeSet, Finset.mem_filter]; exact ⟨he, hc ▸ self_mem_compOf (hG₀ e he).1⟩
      have hex : ∃ c' : Fin comps.length, e ∈ compEdgeSet G₀ comps[c'.1] := ⟨c, heC⟩
      have hch_eq : hex.choose = c := by
        by_contra hne
        exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀
          ((hComps_all _).mpr (List.getElem_mem hex.choose.2))
          ((hComps_all _).mpr (List.getElem_mem c.2)) (fun h => hne (hC_inj h)))
          hex.choose_spec heC
      have hef_eq : edgeC1f e = c.1 := by dsimp only [edgeC1f]; rw [dite_eq_left hex, hch_eq]
      exact ⟨c, hef_eq, hef_eq, hc ▸ self_mem_compOf (hG₀ e he).1⟩
    · intro c
      have hci := hInvL.2.2.2.2.2.2.2.2.2.2.1 c.1 c.2
      dsimp only [x']
      refine ⟨(hmf3_ge_hdr _ (by omega)).trans hci.2.1,
        (hmf3_ge_hdr _ (by omega)).trans hci.2.2.1,
        (hmf3_ge_hdr _ (by omega)).trans hci.2.2.2.1,
        fun hm1 => ?_⟩
      have hmem : c.1 ∈ efIdx := (hInvL.2.2.2.2.2.2.2.2.1 c.1 c.2).mp hm1
      have hidx_lt : efIdx.idxOf c.1 < efIdx.length := List.idxOf_lt_length_iff.mpr hmem
      obtain ⟨_, hefi, _⟩ := hInvL.2.2.2.2.2.2.2.2.2.2.2.1 (efIdx.idxOf c.1) hidx_lt
      have hget : efIdx[efIdx.idxOf c.1]'hidx_lt = c.1 := List.getElem_idxOf hidx_lt
      rw [hget] at hefi
      refine ⟨⟨efIdx.idxOf c.1, hidx_lt⟩, by simp [hmem],
        (hmf3_ge_hdr _ (by omega)).trans hefi, Fin.ext hget⟩
    · intro ec
      have hi := hInvL.2.2.2.2.2.2.2.1 _ (List.getElem_mem ec.2)
      have hm := (hInvL.2.2.2.2.2.2.2.2.1 _ hi).mpr (List.getElem_mem ec.2)
      refine ⟨hm, ?_⟩
      simp only [x', List.getElem_mem ec.2, ↓reduceIte]
      exact hInvL.2.2.2.2.2.2.1.idxOf_getElem ec.1 ec.2
    · intro c v hv
      have hC := (hComps_all _).mpr (List.getElem_mem c.2)
      dsimp only [S', x', compLSFInitFamily] at hv ⊢
      rw [(initCompLSFWith_compSt_basic (W.hInitValid k 0 hk hk) hG₀ hℓ₀_pos hk hC).2.1] at hv
      exact (hmf3_ge_hdr _ (by omega)).trans ((hInvL.2.2.2.2.2.2.2.2.2.2.1 c.1 c.2).1 v hv)
    · intro e he
      obtain ⟨c, hc⟩ := (hC_surj (compOf G₀ (G₀.tail e))).mp
        (Finset.mem_image.mpr ⟨G₀.tail e, (hG₀ e he).1, rfl⟩)
      have heC : e ∈ compEdgeSet G₀ comps[c.1] := by
        rw [compEdgeSet, Finset.mem_filter]; exact ⟨he, hc ▸ self_mem_compOf (hG₀ e he).1⟩
      have hex : ∃ c' : Fin comps.length, e ∈ compEdgeSet G₀ comps[c'.1] := ⟨c, heC⟩
      have hch_eq : hex.choose = c := by
        by_contra hne
        exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀
          ((hComps_all _).mpr (List.getElem_mem hex.choose.2))
          ((hComps_all _).mpr (List.getElem_mem c.2)) (fun h => hne (hC_inj h)))
          hex.choose_spec heC
      have hmem_e := (hInvL.2.2.2.2.2.2.2.2.2.2.1 c.1 c.2).2.2.2.2 e heC
      have hef_eq : edgeC1f e = c.1 := by dsimp only [edgeC1f]; rw [dite_eq_left hex, hch_eq]
      dsimp only [x']
      refine ⟨(hmf3_ge_hdr _ (by omega)).trans (hmem_e.1.trans hef_eq.symm),
        (hmf3_ge_hdr _ (by omega)).trans (hmem_e.2.trans hef_eq.symm)⟩
    · intro e he
      dsimp only [x'] at he ⊢
      have hz_cr : mf3 (compIsCrossBase b vCap eCap + e) = 0 :=
        (hmf3_ge_hdr _ (by omega)).trans (hInvL.2.2.1 _ (by dsimp [ctx]; omega) (by dsimp [ctx]; omega))
      have hz_in : mf3 (compIsInsBase b vCap eCap + e) = 0 :=
        (hmf3_ge_hdr _ (by omega)).trans (hInvL.2.2.1 _ (by dsimp [ctx]; omega) (by dsimp [ctx]; omega))
      exact ⟨by simpa [S', compLSFInitFamily, initCompLSFWith] using hz_cr,
        by simpa [S', compLSFInitFamily, initCompLSFWith] using hz_in⟩
    · refine ⟨fun v hv => ?_, fun _ _ hcr => by simp [S', compLSFInitFamily, initCompLSFWith] at hcr⟩
      have hzg : ∀ a, compGhostBase b vCap eCap ≤ a → a < compTouchMarkBase b vCap eCap → mf3 a = 0 := fun a ha1 ha2 =>
        (hmf3_ge_hdr a (by omega)).trans (hInvL.2.2.1 a (by dsimp [ctx]; omega) (by dsimp [ctx]; omega))
      dsimp only [x'] at hv ⊢
      refine ⟨⟨List.nodup_nil, (fun _ h => by cases h),
          hzg _ (by dsimp [ghostTHeadBase]; omega) (by dsimp [ghostTHeadBase]; omega),
          (fun _ hi => False.elim (Nat.not_lt_zero _ hi))⟩,
        hzg _ (by dsimp [ghostTCntBase]; omega) (by dsimp [ghostTCntBase]; omega),
        ⟨List.nodup_nil, (fun _ h => by cases h),
          hzg _ (by dsimp [ghostHHeadBase]; omega) (by dsimp [ghostHHeadBase]; omega),
          (fun _ hi => False.elim (Nat.not_lt_zero _ hi))⟩,
        hzg _ (by dsimp [ghostHCntBase]; omega) (by dsimp [ghostHCntBase]; omega)⟩
    · intro c hc
      dsimp only [x'] at hc ⊢
      exact (hmf3_ge_hdr _ (by omega)).trans (hInvL.2.2.1 _ (by dsimp [ctx]; omega) (by dsimp [ctx]; omega))
    · dsimp only [x']
      refine ⟨(hmf3_ge_hdr _ (by omega)).trans hInvL.2.2.2.1.1,
        fun t ht1 ht2 => (hmf3_ge_hdr _ (by omega)).trans (hInvL.2.2.2.1.2 t ht1 ht2)⟩
    · intro ec j
      obtain ⟨hi, _, hwj⟩ := hInvL.2.2.2.2.2.2.2.2.2.2.2.1 ec.1 ec.2
      obtain ⟨hm_h, hrep_j, hvj, hej, hLwj, hge_j, hle_j, hft_j⟩ := hwj j.1 j.2
      dsimp only [x']
      refine ⟨(hmf3_ge_hdr _ (by omega)).trans hm_h,
        ?_, hvj, hej, hLwj, le_trans (by dsimp [InitCtx.heap0, ctx]; omega) hge_j, hle_j⟩
      exact ((lsfRep_local W.h _ _ _ _ _ fun a ha =>
        (hmf3_ge_hdr a (by have := (hft_j a ha).1; dsimp [InitCtx.heap0, ctx] at this; omega)).symm).1 hrep_j)
    · intro ec1 ec2 j1 j2 hne a ha1 ha2
      exact hInvL.2.2.2.2.2.2.2.2.2.2.2.2.1 ec1.1 ec1.2 ec2.1 ec2.2 j1.1 j1.2 j2.1 j2.2
        (by rcases hne with h | h; exact Or.inl (fun heq => h (Fin.ext heq)); exact Or.inr (fun heq => h (Fin.ext heq)))
        a ha1 ha2
  -- Prove `Respects`
  have hResp : (compLSFRep W k).Respects (fun _ => False) b
      ((compLSFDS W w k G₀).initSpace [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b] mem)
      mem endAddr b x' mf3 := by
    refine ⟨by omega, hend_le_sp,
      fun a ha => (hmf3_ge_hdr a (by omega)).trans (hInvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a ha),
      fun a ha _ => (hmf3_ne a (by omega) (by omega) (by omega)).trans (hInvL.1 a ha),
      fun a hfa => Or.inr ⟨hfa.1, hfa.2⟩⟩
  -- Prove cost + initial potential bound
  have hPhi_bound : compPhi b x' mf3 ≤ (edgefulComps G₀).sum fun C =>
      k * (3000 * ((compGraph G₀ C).n + 1) * (Nat.log 2 ((compGraph G₀ C).n + 2) + 1)) := by
    rw [compPhi_eq_sum hRep]
    have hterm : ∀ ec : Fin x'.numEdgeful,
        (Finset.univ : Finset (Fin k)).sum (fun j => (LSFRep W.h).phi (x'.winHandle ec j) (x'.winConc ec j) mf3) ≤
        k * (3000 * ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 1) *
          (Nat.log 2 ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 2) + 1)) := fun ec => by
      have hC := (hComps_all _).mpr (List.getElem_mem (x'.edgefulComp ec).2)
      have hle_j : ∀ j : Fin k, (LSFRep W.h).phi (x'.winHandle ec j) (x'.winConc ec j) mf3 ≤
          3000 * ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 1) *
            (Nat.log 2 ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 2) + 1) := fun j => by
        have hbas := initCompLSFWith_compSt_basic (W.hInitValid k j.1 hk j.2) hG₀ hℓ₀_pos hk hC
        have hrep_j := (hRep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ec j).2.1
        have hVG : ((S' j).compSt (x'.compOf (x'.edgefulComp ec))).G.V =
            ((S' j).compSt (x'.compOf (x'.edgefulComp ec))).G₀.V := by
          dsimp only [S', compLSFInitFamily]; rw [hbas.2.1, hbas.1]
        have hphi_j := lsfPhi_le_of_init_rep hrep_j hVG
        dsimp only [S', compLSFInitFamily] at hphi_j
        rw [hbas.1] at hphi_j; exact hphi_j
      calc (Finset.univ : Finset (Fin k)).sum (fun j => (LSFRep W.h).phi (x'.winHandle ec j) (x'.winConc ec j) mf3)
          ≤ (Finset.univ : Finset (Fin k)).sum (fun _ =>
            3000 * ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 1) *
              (Nat.log 2 ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 2) + 1)) :=
            Finset.sum_le_sum fun j _ => hle_j j
        _ = k * (3000 * ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 1) *
            (Nat.log 2 ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 2) + 1)) := by simp
    calc (Finset.univ : Finset (Fin x'.numEdgeful)).sum (fun ec =>
            (Finset.univ : Finset (Fin k)).sum (fun j => (LSFRep W.h).phi (x'.winHandle ec j) (x'.winConc ec j) mf3))
        ≤ (Finset.univ : Finset (Fin x'.numEdgeful)).sum (fun ec =>
            k * (3000 * ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 1) *
              (Nat.log 2 ((compGraph G₀ (x'.compOf (x'.edgefulComp ec))).n + 2) + 1))) :=
          Finset.sum_le_sum fun ec _ => hterm ec
      _ = (edgefulComps G₀).sum (fun C =>
            k * (3000 * ((compGraph G₀ C).n + 1) * (Nat.log 2 ((compGraph G₀ C).n + 2) + 1))) := by
          refine Finset.sum_bij (fun ec _ => x'.compOf (x'.edgefulComp ec)) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro ec _
            have hC := (hComps_all _).mpr (List.getElem_mem (x'.edgefulComp ec).2)
            have hm := (hInvL.2.2.2.2.2.2.2.2.1 _ (x'.edgefulComp ec).2).mpr (List.getElem_mem ec.2)
            exact Finset.mem_filter.mpr ⟨hC, hm⟩
          · intro ec1 _ ec2 _ heq
            have h1 := hC_inj heq
            exact Fin.ext (hInvL.2.2.2.2.2.2.1.getElem_inj_iff.mp (congrArg Fin.val h1))
          · intro C hC
            have hC_m := (Finset.mem_filter.mp hC).1
            have hm := (Finset.mem_filter.mp hC).2
            obtain ⟨c, hc⟩ := (hC_surj C).mp hC_m
            have hmem := (hInvL.2.2.2.2.2.2.2.2.1 c.1 c.2).mp (hc.symm ▸ hm)
            have hlt := List.idxOf_lt_length_iff.mpr hmem
            refine ⟨⟨efIdx.idxOf c.1, hlt⟩, Finset.mem_univ _, ?_⟩
            dsimp only [x']; simp [List.getElem_idxOf hlt, hc]
  have hsum_m_ef : (edgefulComps G₀).sum (fun C => (compGraph G₀ C).m) ≤ G₀.m :=
    init_sum_m_le (Finset.filter_subset _ _)
  have hloop_clean : c_loop ≤ 120 * G₀.n +
      (edgefulComps G₀).sum (fun C =>
        W.winCost k L_w (compGraph G₀ C).n (compGraph G₀ C).m +
          250 * (compGraph G₀ C).n + 850 * (compGraph G₀ C).m + 450) + 6 := by
    simpa [ctx] using hc_loop
  have hcost_sum : (edgefulComps G₀).sum (fun C =>
        W.winCost k L_w (compGraph G₀ C).n (compGraph G₀ C).m +
          250 * (compGraph G₀ C).n + 850 * (compGraph G₀ C).m + 450) +
      (edgefulComps G₀).sum (fun C =>
        k * (3000 * ((compGraph G₀ C).n + 1) * (Nat.log 2 ((compGraph G₀ C).n + 2) + 1))) ≤
      50 * (edgefulComps G₀).sum (fun C => (compGraph G₀ C).m) +
      (edgefulComps G₀).sum (fun C =>
        W.winCost k L_w (compGraph G₀ C).n (compGraph G₀ C).m +
          k * (3000 * ((compGraph G₀ C).n + 1) * (Nat.log 2 ((compGraph G₀ C).n + 2) + 1)) +
          compInitCompMul * ((compGraph G₀ C).n + (compGraph G₀ C).m + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C _ => ?_
    dsimp only [compInitCompMul]; omega
  refine ⟨.returned endAddr, { stL with mem := mf3 }, c_set + (c_loop + 20 + 1) + 1, hrun_full,
    S', x', hRep, ?_, hResp, ?_, rfl, rfl, rfl⟩
  · rfl
  · rw [compLSFDS_initCost_eq]
    dsimp only [compInitLinMul]
    omega

end

end MinCostFlow.SparseCore.Program
