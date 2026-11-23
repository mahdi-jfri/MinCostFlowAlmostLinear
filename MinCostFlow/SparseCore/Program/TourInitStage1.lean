module

public import MinCostFlow.SparseCore.Program.TourInitStage1Outer
import Mathlib.Tactic

/-!
# Stage 1 of Tour Initialization (`tourInitStage1Body_runs`)

Assembles `tourInitHeader_runs`, the embedded order-store initialization, `tourInitOuter_runs`,
and `tourInitRoots_runs` into the verified Stage 1 theorem for the edgeless forest
`s₀ = tourInitStage1Abs recs rs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Amortized cost constant for Stage 1 (excluding the embedded `ordStore` init multiplier). -/
def TOUR_INIT1_BASE_MUL : ℕ := 2 * TOUR_JOIN_AMORT + 2000

theorem tourInitStage1Body_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord ordPtr fePtr rsPtr b ordWords pos ordInit : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordOp : ℕ → ℕ}
    (C : TourSplayOpsProcs w p)
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hOrdInitSpace : alloc_ord 3 [vCap, eCap, ordPtr, ordHandleOf b vCap eCap] ≤ ordArenaSize vCap eCap)
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hOrdAt : OrdListAt mem ordPtr (readOrd mem ordPtr) ordWords)
    (hOrdLe : ordPtr + ordWords ≤ b)
    (hRsLe : rsPtr + 1 + mem rsPtr ≤ b)
    (hValid : TourValid vCap eCap
      ⟨readOrd mem ordPtr,
        initTourForest (readOrdRecordsAt mem ordPtr) (readNatList mem fePtr) (readNatList mem rsPtr), ∅⟩)
    (hzero : ZeroFrom mem b)
    (hroom : b + tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3 < 2 ^ w) :
    let recs := readOrdRecordsAt mem ordPtr
    let rs := readNatList mem rsPtr
    let s0 := tourInitStage1Abs recs rs
    ∃ (hOut : ℕ) (st' : State) (c : ℕ) (x0 : TourConcrete R_ord.τ),
      Runs w p ω (tourInitStage1Body ordInit C.initNode C.join)
        (startState [vCap, eCap, ordPtr, rsPtr, b] mem pos) (.returned hOut) st' c ∧
      ordHandleOf b vCap eCap ≤ hOut ∧
      hOut ≤ b + tourFixedSize vCap eCap + ordArenaSize vCap eCap ∧
      ZeroFrom st'.mem hOut ∧
      (∀ a < b, st'.mem a = mem a) ∧
      (∀ a, tourFoot R_ord vCap eCap b x0 a → a < hOut) ∧
      TourRepAt R_ord vCap eCap b s0 x0 st'.mem ∧
      c + (tourRep R_ord vCap eCap).phi b x0 st'.mem ≤
        (TOUR_INIT1_BASE_MUL + mul_ord) * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap := by
  intro recs rs s0
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hwide : 18 ≤ 2 ^ w := by simp [tourFixedSize, ordArenaSize] at hroom; omega
  have hw : vCap + 2 * eCap + 4 < 2 ^ w := by simp [tourFixedSize, ordArenaSize] at hroom; omega
  have hordH_lt : ordHandleOf b vCap eCap < 2 ^ w := by simp [ordHandleOf, tourFixedSize, ordArenaSize] at hroom ⊢; omega
  have hvalid0 : TourValid vCap eCap s0 := tourValid_stage1 hValid
  -- Step 1: write header + node 0
  obtain ⟨stH, cH, hrunH, hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9, hH10, hH11, hH12,
    hHhdr, hHnd0, hHzMid, hHzOrd, hHlt, hcH⟩ :=
    tourInitHeader_runs (ordPtr := ordPtr) (rsPtr := rsPtr) (p := p) (pos := pos) ω hzero hordH_lt
  -- Step 2: call `ordInit [vCap, eCap, ordPtr, ordHandleOf b vCap eCap]`
  have hOrdAtH : OrdListAt stH.mem ordPtr (readOrd stH.mem ordPtr) ordWords := by
    have hwords_pos : 1 ≤ ordWords := by have := hOrdAt.2.2; omega
    have h0 : stH.mem ordPtr = mem ordPtr := hHlt ordPtr (by omega)
    have hrecs_eq : readOrdRecordsAt stH.mem ordPtr = recs := by
      simp only [readOrdRecordsAt, h0]
      exact readOrdRecords_eq_of_agree (mem ordPtr) (ordPtr + 1) fun a ha1 ha2 =>
        hHlt a (by have := hOrdAt.2.2; unfold readOrdRecordsAt at this; omega)
    refine ⟨by rw [hrecs_eq]; exact hOrdAt.1, rfl, by rw [hrecs_eq]; exact hOrdAt.2.2⟩
  have hreadOrdH : readOrd stH.mem ordPtr = readOrd mem ordPtr := by
    have hwords_pos : 1 ≤ ordWords := by have := hOrdAt.2.2; omega
    have h0 : stH.mem ordPtr = mem ordPtr := hHlt ordPtr (by omega)
    have hrecs_eq : readOrdRecordsAt stH.mem ordPtr = recs := by
      simp only [readOrdRecordsAt, h0]
      exact readOrdRecords_eq_of_agree (mem ordPtr) (ordPtr + 1) fun a ha1 ha2 =>
        hHlt a (by have := hOrdAt.2.2; unfold readOrdRecordsAt at this; omega)
    simp only [readOrd, hrecs_eq]; rfl
  have hOrdPre : (ordStoreCapContract vCap eCap mul_ord alloc_ord).initPre
      [vCap, eCap, ordPtr, ordHandleOf b vCap eCap] stH.mem :=
    ⟨ordPtr, ordHandleOf b vCap eCap, ordWords, rfl, hOrdAtH,
     by simp [ordHandleOf, tourFixedSize]; omega,
     ⟨hreadOrdH ▸ hValid.ordWithin, fun u v x hu hv => hValid.compat.unique u v x (hreadOrdH ▸ hu) (hreadOrdH ▸ hv)⟩⟩
  have hOrdArgsW : ∀ a ∈ [vCap, eCap, ordPtr, ordHandleOf b vCap eCap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> (try omega)
  have hhaO : heapArg [vCap, eCap, ordPtr, ordHandleOf b vCap eCap] = ordHandleOf b vCap eCap := rfl
  obtain ⟨bodyO, hgetO, oO, stO, cO, hrunO, sOrdO, ordX, hrepO, hpostO, hrespO, hcostO⟩ :=
    hOrdImpl.2.1 [vCap, eCap, ordPtr, ordHandleOf b vCap eCap] stH.mem stH.pos ω hOrdArgsW hOrdPre
      (by simpa [hhaO] using hHzOrd)
      (by simp only [ordStoreCapContract, hhaO]; simp only [ordHandleOf] at hOrdInitSpace ⊢; omega)
  rcases hrespO with ⟨hO_ge, hO_le, hO_zero, hO_fr, hO_foot⟩
  simp only [hhaO, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ, ordStoreLog_eq_tourLog]
    at hO_ge hO_le hO_zero hO_fr hO_foot hcostO hpostO
  have hO_le_arena : oO.value ≤ b + tourFixedSize vCap eCap + ordArenaSize vCap eCap := by
    simp only [ordHandleOf] at hO_le hOrdInitSpace; omega
  have hO_lt_ordH : ∀ a < ordHandleOf b vCap eCap, stO.mem a = stH.mem a := fun a ha =>
    hO_fr a ha (fun hf => hf)
  have hO_foot_rng : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX a →
      ordHandleOf b vCap eCap ≤ a ∧ a < oO.value := fun a ha => by
    rcases hO_foot a ha with hf | h12; exact hf.elim; exact h12
  have hcallO := runs_call_regs4 13 0 1 2 11 (st := stH) hgetO hH0 hH1 hH2 hH11 hrunO
  set hOut := oO.value
  have hroom_hOut : hOut + 2 < 2 ^ w := by omega
  set rO := Function.update stH.regs 13 hOut
  set rO1 := Function.update rO 14 (mem ordPtr)
  set rO2 := Function.update rO1 15 (ordPtr + 1)
  set rO3 := Function.update rO2 16 0
  set rO4 := Function.update rO3 17 0
  have hmemO_lt_b : ∀ a < b, stO.mem a = mem a := fun a ha =>
    (hO_lt_ordH a (by simp [ordHandleOf, tourFixedSize]; omega)).trans (hHlt a ha)
  have ha14 : Runs w p ω (.assign 14 (.load (.reg 2))) { stO with regs := rO } .normal { stO with regs := rO1 } 3 :=
    runs_assign_iff.mpr ⟨mem ordPtr, by
      simp [Expr.eval, rO, hH2, hmemO_lt_b ordPtr (by have := hOrdAt.2.2; omega)], rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 2) (.const 1))) { stO with regs := rO1 } .normal { stO with regs := rO2 } 4 :=
    runs_assign_iff.mpr ⟨ordPtr + 1, by
      simp [Expr.eval, rO1, rO, hH2, BinOp.eval, (by omega : 1 < 2 ^ w), (by have := hOrdAt.2.2; omega : ordPtr + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha16 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 16) (val := 0) (st := { stO with regs := rO2 }) (by omega)
  have ha17 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 17) (val := 0) (st := { stO with regs := rO3 }) (by omega)
  -- Step 3: Outer loop over `recs = readOrdRecords mem (mem ordPtr) (ordPtr + 1)`
  have hrecs_nd : (recs.map Prod.fst).Nodup := hOrdAt.1
  have hrecs_ord : ∀ p ∈ recs, s0.ord p.1 = p.2 := fun p hp => ordOfRecords_mem_iff hrecs_nd hp
  have hrecs_sum_le : (recs.map fun p => p.2.length).sum ≤ 2 * eCap := by
    have hnd_all : (recs.flatMap Prod.snd).Nodup := by
      have hgo : ∀ (L : List (ℕ × List End)), (L.map Prod.fst).Nodup →
          (∀ p ∈ L, p.2 = s0.ord p.1) → (L.flatMap Prod.snd).Nodup := by
        intro L hndL hEqL
        induction L with
        | nil => simp
        | cons hd tl ih =>
          rcases hd with ⟨v, xs⟩
          simp only [List.map_cons, List.nodup_cons] at hndL
          rw [List.flatMap_cons, List.nodup_append]
          refine ⟨by rw [hEqL _ List.mem_cons_self]; exact hvalid0.ordWithin.1 v,
            ih hndL.2 (fun q hq => hEqL q (List.mem_cons_of_mem _ hq)), fun a ha b hb hab => ?_⟩
          subst hab
          obtain ⟨q, hq, haq⟩ := List.mem_flatMap.mp hb
          rw [hEqL _ List.mem_cons_self] at ha
          rw [hEqL q (List.mem_cons_of_mem _ hq)] at haq
          have hvq : v = q.1 := hvalid0.compat.unique v q.1 a ha haq
          exact hndL.1 (hvq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
      exact hgo recs hrecs_nd fun p hp => (hrecs_ord p hp).symm
    have hcard : ((recs.flatMap Prod.snd).map endKey).length ≤ (Finset.range (2 * eCap)).card := by
      have hnd_k : ((recs.flatMap Prod.snd).map endKey).Nodup := hnd_all.map fun _ _ h => by simpa [endOfKey_endKey] using congrArg endOfKey h
      rw [← List.toFinset_card_of_nodup hnd_k]
      refine Finset.card_le_card fun k hk => ?_
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
      obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.mp hz
      rw [← hrecs_ord p hp] at hzp
      exact Finset.mem_range.mpr (endKey_lt_two_mul (hvalid0.ordWithin.2.2 p.1 z hzp))
    simpa [List.length_flatMap] using hcard
  obtain ⟨nnF, sF, treesF, noF, koF, ctF, stF, cF, hrunF, hnnF, hrF3, hrF4, hrF6, hrF13, hrF16,
    hnF, hinvF, hzF, hexF, hnoF, hactF, hinactF, hkoF, hnkF, hfeF, hirF, hctF_s, hctF_n, htF_cls,
    hvalF, hval0F, hfrF_out, hfrF_hdr, hfrF_mk, hcF⟩ :=
    tourInitOuter_runs C ω (hOrdAt.2.2 ▸ hOrdAt) (hOrdAt.2.2 ▸ hOrdLe) hvalid0 hO_ge hroom_hOut hw hwide hmemO_lt_b hrecs_sum_le (mem ordPtr) 0 (ordPtr + 1) 0 tourEmptyState [] (fun _ => 0) (fun _ => 0) (fun _ => none)
      { stO with regs := rO4 } (by omega) rfl (by have := hOrdAt.2.2; unfold readOrdRecordsAt at this; omega) rfl
      (by simp [rO4, rO3, rO2, rO1, rO, hH0]) (by simp [rO4, rO3, rO2, rO1, rO, hH1])
      (by simp [rO4, rO3, rO2, rO1, rO, hH2]) (by simp [rO4, rO3, rO2, rO1, rO, hH3])
      (by simp [rO4, rO3, rO2, rO1, rO, hH4]) (by simp [rO4, rO3, rO2, rO1, rO, hH5])
      (by simp [rO4, rO3, rO2, rO1, rO, hH6]) (by simp [rO4, rO3, rO2, rO1, rO, hH7])
      (by simp [rO4, rO3, rO2, rO1, rO, hH8]) (by simp [rO4, rO3, rO2, rO1, rO, hH9])
      (by simp [rO4, rO3, rO2, rO1, rO, hH10]) (by simp [rO4, rO3, rO2, rO1, rO, hH12])
      (by simp [rO4, rO3, rO2, rO1, rO]) (by simp [rO4, rO3, rO2, rO1])
      (by simp [rO4, rO3, rO2]) (by simp [rO4, rO3]) (by simp [rO4])
      (NodesAt.congr tourLayout hHnd0 fun a ha => hO_lt_ordH a (inRecords_lt_ordHandle_of_le (Nat.zero_le _) ha).2)
      ⟨fun _ h => by simp at h, fun _ h => by simp at h, by simp, fun _ h => by simp at h,
       fun u hu => by simp [tourEmptyState, tourZeroNode], fun u hu => by simp [tourEmptyState, tourZeroNode]⟩
      ⟨by omega, fun u hu => by simp [tourEmptyState, tourZeroNode]⟩ hO_zero
      (fun u => by simp; omega)
      (fun k hk => ⟨by rw [hO_lt_ordH _ (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize]; omega)]; exact hHzMid _ (by simp [nodeOfEndBase]; omega) (by simp [nodeOfEndBase, nodesBase]; omega), Nat.zero_le _⟩)
      (fun _ _ => rfl) (fun _ h => by simp at h)
      (fun k hk _ => by rw [hO_lt_ordH _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]; exact hHzMid _ (by simp [endOwnerBase]; omega) (by simp [endOwnerBase, nodesBase]; omega))
      (fun _ h1 h2 => by omega) (fun _ _ h => absurd rfl h)
      (fun v hv => by simp; rw [hO_lt_ordH _ (by simp [firstEndBase, ordHandleOf, tourFixedSize]; omega)]; exact hHzMid _ (by simp [firstEndBase]) (by simp [firstEndBase, nodesBase]; omega))
      (fun v hv => by simp; rw [hO_lt_ordH _ (by simp [isRootBase, ordHandleOf, tourFixedSize]; omega)]; exact hHzMid _ (by simp [isRootBase]; omega) (by simp [isRootBase, nodesBase]; omega))
      (fun _ ⟨_, h, _⟩ => by simp at h) (fun _ _ => rfl) (fun _ h => by simp at h)
      (fun _ h1 h2 => by omega) rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun a ha1 ha2 => by rw [hO_lt_ordH a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha2 ⊢; omega)]; exact hHzMid a (by simp [markArrBase] at ha1 ⊢; omega) ha2)
  -- Step 4: Store `HDR_NUM_NODES := nnF`, then mark roots in `rsPtr`, then `ret hOut`
  set mNN := Function.update stF.mem (b + HDR_NUM_NODES) nnF
  have hst_nn : Runs w p ω (.store (.bin .add (.reg 4) (.const HDR_NUM_NODES)) (.reg 16)) stF .normal { stF with mem := mNN } 5 :=
    runs_store_iff.mpr ⟨b + HDR_NUM_NODES, nnF,
      by simp [Expr.eval, hrF4, BinOp.eval, (by simp [HDR_NUM_NODES]; omega : HDR_NUM_NODES < 2 ^ w), (by simp [HDR_NUM_NODES, ordHandleOf, tourFixedSize] at hordH_lt ⊢; omega : b + HDR_NUM_NODES < 2 ^ w)],
      by simp [Expr.eval, hrF16], rfl, rfl, rfl⟩
  have hmNN_rs : mNN rsPtr = mem rsPtr := by
    dsimp only [mNN]; rw [Function.update_of_ne (by simp [HDR_NUM_NODES]; omega), hfrF_out rsPtr (Or.inl (by omega)), hmemO_lt_b rsPtr (by omega)]
  set rR1 := Function.update stF.regs 14 (mem rsPtr)
  set rR2 := Function.update rR1 15 (rsPtr + 1)
  set rR3 := Function.update rR2 17 0
  have haR1 : Runs w p ω (.assign 14 (.load (.reg 3))) { stF with mem := mNN } .normal { stF with mem := mNN, regs := rR1 } 3 :=
    runs_assign_iff.mpr ⟨mem rsPtr, by simp [Expr.eval, hrF3, hmNN_rs], rfl, rfl, rfl⟩
  have haR2 : Runs w p ω (.assign 15 (.bin .add (.reg 3) (.const 1))) { stF with mem := mNN, regs := rR1 } .normal { stF with mem := mNN, regs := rR2 } 4 :=
    runs_assign_iff.mpr ⟨rsPtr + 1, by simp [Expr.eval, rR1, hrF3, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : rsPtr + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have haR3 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 17) (val := 0) (st := { stF with mem := mNN, regs := rR2 }) (by omega)
  have hrs_eq_mNN : readNatList mNN rsPtr = rs := by
    apply List.ext_getElem (by simp [readNatList, readList_length, hmNN_rs, rs])
    intro i hi _
    simp only [readNatList, readList_length, hmNN_rs] at hi
    simp only [readNatList, readList_getElem, rs]
    dsimp only [mNN]; rw [Function.update_of_ne (by simp [HDR_NUM_NODES]; omega), hfrF_out _ (Or.inl (by omega)), hmemO_lt_b _ (by omega)]
  have hrs_vcap : ∀ r ∈ readNatList mNN rsPtr, r < vCap := fun r hr => by
    rw [hrs_eq_mNN] at hr
    exact hvalid0.verts_lt r (by simp [s0, tourInitStage1Abs, rs, hr])
  obtain ⟨stR, cR, hrunR, hrR13, hR_set, hR_fr, hcR⟩ :=
    tourInitRoots_runs (p := p) (vCap := vCap) (eCap := eCap) (b := b) (rsPtr := rsPtr) (hOut := hOut)
      (st0 := { stF with mem := mNN, regs := rR3 }) ω (by dsimp only; rw [hmNN_rs]; exact hRsLe) hrs_vcap hO_ge hroom_hOut
      (by simp [rR3, rR2, rR1, hrF6]) (by simp [rR3, rR2, rR1, hrF13])
      (by simp [rR3, rR2, rR1, hmNN_rs]) (by simp [rR3, rR2]) (by simp [rR3])
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stR) (r := 13) (v := hOut) hrR13
  -- Assemble `TourRepAt` for `s0`
  have hnnF_le : nnF ≤ 2 * eCap := hnnF ▸ hrecs_sum_le
  have hR_eq_stF : ∀ a, a ≠ b + HDR_NUM_NODES → (∀ r ∈ rs, a ≠ isRootBase b vCap + r) → stR.mem a = stF.mem a :=
    fun a h1 h2 => (hR_fr a (by rwa [hrs_eq_mNN])).trans (Function.update_of_ne h1 _ _)
  have hR_ord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX a → stO.mem a = stR.mem a := fun a ha => by
    have ⟨h1, h2⟩ := hO_foot_rng a ha
    rw [hR_eq_stF a (by simp [HDR_NUM_NODES, ordHandleOf, tourFixedSize] at h1 ⊢; omega)
      (fun r hr => by have := hvalid0.verts_lt r (by simp [s0, tourInitStage1Abs, rs, hr]); simp [isRootBase, ordHandleOf, tourFixedSize] at h1 ⊢; omega),
      hfrF_out a (Or.inr ⟨h1, h2⟩)]
  have hOrdFin := hOrdImpl.1 (ordHandleOf b vCap eCap) (readOrd mem ordPtr) ordX stO.mem stR.mem hR_ord_eq
  have hhdr_fin : TourHeaderAt vCap eCap b nnF stR.mem := by
    have hf : ∀ k < 15, k ≠ HDR_NUM_NODES → stR.mem (b + k) = stH.mem (b + k) := fun k hk hne => by
      rw [hR_eq_stF (b + k) (by omega) (fun r _ => by simp [isRootBase]; omega),
        hfrF_hdr (b + k) (by omega) (by omega), hO_lt_ordH (b + k) (by simp [ordHandleOf, tourFixedSize]; omega)]
    have hnn_mem : stR.mem (b + HDR_NUM_NODES) = nnF := by
      rw [hR_fr _ (fun r _ => by simp [HDR_NUM_NODES, isRootBase]; omega)]; simp [mNN]
    rcases hHhdr with ⟨z0, z1, z2, _, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14⟩
    exact ⟨(hf _ (by decide) (by decide)).trans z0, (hf _ (by decide) (by decide)).trans z1,
      (hf _ (by decide) (by decide)).trans z2, hnn_mem, (hf _ (by decide) (by decide)).trans z4,
      (hf _ (by decide) (by decide)).trans z5, (hf _ (by decide) (by decide)).trans z6,
      (hf _ (by decide) (by decide)).trans z7, (hf _ (by decide) (by decide)).trans z8,
      (hf _ (by decide) (by decide)).trans z9, (hf _ (by decide) (by decide)).trans z10,
      (hf _ (by decide) (by decide)).trans z11, (hf _ (by decide) (by decide)).trans z12,
      (hf _ (by decide) (by decide)).trans z13, (hf _ (by decide) (by decide)).trans z14⟩
  set x0 : TourConcrete R_ord.τ :=
    { ordX := ordX, numNodes := nnF, st := sF, trees := treesF,
      nodeOf := noF, keyOf := koF, compTree := ctF, slotOf := id, vertOf := id }
  have hrep0 : TourRepAt R_ord vCap eCap b s0 x0 stR.mem :=
    { valid := hvalid0
      ordRep := hOrdFin.1 (by simpa [hhaO, hpostO, hreadOrdH] using hrepO)
      ordFootGe := fun a ha => (hO_foot_rng a ha).1
      header := hhdr_fin
      numNodes_le := hnnF_le
      nodeOf_mem := fun k hk => by
        rw [hR_eq_stF _ (by simp [nodeOfEndBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [nodeOfEndBase, isRootBase]; omega)]
        exact hnoF k hk
      nodeOf_keyOf := hnkF
      keyOf_mem := fun u h1 h2 => by
        rw [hR_eq_stF _ (by simp [keyOfNodeBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [keyOfNodeBase, isRootBase]; omega)]
        exact hkoF u h1 h2
      firstEnd_mem := fun v hv => by
        rw [hR_eq_stF _ (by simp [firstEndBase, HDR_NUM_NODES]; omega) (fun r hr => by simp [firstEndBase, isRootBase]; omega)]
        exact hfeF v hv
      isRoot_mem := fun v hv => by
        by_cases hvr : v ∈ rs
        · rw [hR_set v (hrs_eq_mNN.symm ▸ hvr)]; simp [s0, tourInitStage1Abs, rs, hvr]
        · rw [hR_eq_stF _ (by simp [isRootBase, HDR_NUM_NODES]; omega) (fun r hr => by have : v ≠ r := fun heq => hvr (heq ▸ hr); omega), hirF v hv]
          have hiff : (∃ xs, (v, xs) ∈ recs ∧ xs ≠ []) ↔ v ∈ s0.rf.R := by
            simp only [s0, tourInitStage1Abs, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
              rs, hvr, or_false]
            exact ⟨fun ⟨xs, hm, hne⟩ => ⟨(v, xs), ⟨hm, by cases xs with | nil => exact absurd rfl hne | cons _ _ => rfl⟩, rfl⟩,
              fun ⟨⟨v', xs⟩, ⟨hm, hne⟩, heq⟩ => ⟨xs, heq ▸ hm, by cases xs with | nil => simp at hne | cons _ _ => simp⟩⟩
          dsimp only [recs] at hiff
          simp only [hiff]
      slot_bij := fun v hv => ⟨hv, rfl, rfl⟩
      slotOf_mem := fun v hv => by
        rw [hR_eq_stF _ (by simp [slotOfVertBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [slotOfVertBase, isRootBase]; omega),
          hfrF_mk _ (by simp [slotOfVertBase, markArrBase]; omega) (by simp [slotOfVertBase, nodesBase]; omega)]
        simp [decodeSlot, x0]
      vertOf_mem := fun sl hsl => by
        rw [hR_eq_stF _ (by simp [vertOfSlotBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [vertOfSlotBase, isRootBase]; omega),
          hfrF_mk _ (by simp [vertOfSlotBase, markArrBase]; omega) (by simp [vertOfSlotBase, nodesBase]; omega)]
        simp [decodeSlot, x0]
      active_end := fun v hv z hz => by
        have hmem_rec : (v, s0.ord v) ∈ recs := by
          by_contra hnot
          have hnil : s0.ord v = [] := by
            by_cases hex : ∃ ys, (v, ys) ∈ recs
            · obtain ⟨ys, hys⟩ := hex; exact absurd ((hrecs_ord (v, ys) hys).symm ▸ hys) hnot
            · exact ordOfRecords_eq_nil_of_not_mem fun ys hys => hex ⟨ys, hys⟩
          rw [hnil] at hz; simp at hz
        rw [hR_eq_stF _ (by simp [endOwnerBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [endOwnerBase, isRootBase]; omega)]
        exact hactF (v, s0.ord v) hmem_rec z hz
      inactive_owner := fun k hk hno => by
        rw [hR_eq_stF _ (by simp [endOwnerBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [endOwnerBase, isRootBase]; omega)]
        exact hinactF k hk fun p hp z hz heq => hno p.1 (by rw [heq, hrecs_ord p hp]; exact hz)
      markArr_zero := fun k hk => by
        rw [hR_eq_stF _ (by simp [markArrBase, HDR_NUM_NODES]; omega) (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [markArrBase, isRootBase]; omega)]
        exact hfrF_mk _ (by omega) (by simp [markArrBase, nodesBase]; omega)
      nodesAt := NodesAt.congr tourLayout hnF fun a ha =>
        hR_eq_stF a (by have := (inRecords_lt_ordHandle_of_le hnnF_le ha).1; simp [nodesBase, HDR_NUM_NODES] at this ⊢; omega)
          (fun r hr => by have h1 := (inRecords_lt_ordHandle_of_le hnnF_le ha).1; have h2 := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [nodesBase] at h1; simp [isRootBase]; omega)
      forestInv := hinvF
      nodes_exact := hexF
      comp_none := fun r _ hft0 => by
        rw [fullTour_of_empty_E hvalid0.compat.forest rfl r] at hft0
        exact hctF_n r fun xs hxs => (hrecs_ord (r, xs) hxs).symm.trans hft0
      comp_some := fun r _ hft_ne => by
        rw [fullTour_of_empty_E hvalid0.compat.forest rfl r] at hft_ne ⊢
        have hex : ∃ xs, (r, xs) ∈ recs ∧ xs ≠ [] := by
          by_contra hno
          have hnil : s0.ord r = [] := by
            by_cases hm : ∃ ys, (r, ys) ∈ recs
            · obtain ⟨ys, hys⟩ := hm; have h0 : ys = [] := by by_contra hne; exact hno ⟨ys, hys, hne⟩
              rw [hrecs_ord (r, ys) hys, h0]
            · exact ordOfRecords_eq_nil_of_not_mem fun ys hys => hm ⟨ys, hys⟩
          exact hft_ne hnil
        exact hctF_s r hex
      tree_class := fun t ht => by
        obtain ⟨v, ⟨xs, hxs, hne⟩, hct⟩ := htF_cls t ht
        refine Or.inl ⟨v, ?_, hct⟩
        simp only [s0, tourInitStage1Abs, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact Or.inl ⟨(v, xs), ⟨hxs, by cases xs with | nil => exact absurd rfl hne | cons _ _ => rfl⟩, rfl⟩
      inactive_single := fun u h1 h2 hno => by
        exfalso
        obtain ⟨t, ht_mem, hu_t⟩ := List.mem_flatMap.mp ((hexF u).mpr ⟨h1, h2⟩)
        obtain ⟨v, hv_ex, hct_v⟩ := htF_cls t ht_mem
        obtain ⟨t', hct', _, ht'_map⟩ := hctF_s v hv_ex
        have hteq : t = t' := Option.some.inj (hct_v.symm.trans hct'); subst hteq
        exact hno v (ht'_map ▸ List.mem_map_of_mem hu_t)
      val_active := fun u h1 h2 _ => by
        rw [hvalF u h1 h2]; simp [s0, tourInitStage1Abs, recs, rs, x0]
      val_inactive_rt := fun u h1 h2 hno => by
        exfalso
        obtain ⟨t, ht_mem, hu_t⟩ := List.mem_flatMap.mp ((hexF u).mpr ⟨h1, h2⟩)
        obtain ⟨v, hv_ex, hct_v⟩ := htF_cls t ht_mem
        obtain ⟨t', hct', _, ht'_map⟩ := hctF_s v hv_ex
        have hteq : t = t' := Option.some.inj (hct_v.symm.trans hct'); subst hteq
        exact hno v (ht'_map ▸ List.mem_map_of_mem hu_t)
      val_unused_rt := fun u hu hcond => by
        rcases hcond with rfl | hgt
        · exact hval0F
        · omega }
  refine ⟨hOut, stR, _, x0,
    tour_runs_seq_normal hrunH (tour_runs_seq_normal hcallO (tour_runs_seq_normal ha14 (tour_runs_seq_normal ha15
      (tour_runs_seq_normal ha16 (tour_runs_seq_normal ha17 (tour_runs_seq_normal hrunF (tour_runs_seq_normal hst_nn
        (tour_runs_seq_normal haR1 (tour_runs_seq_normal haR2 (tour_runs_seq_normal haR3 (tour_runs_seq_normal hrunR hret))))))))))),
    hO_ge, hO_le_arena,
    fun a ha => by
      rw [hR_eq_stF a (by simp [HDR_NUM_NODES, ordHandleOf, tourFixedSize] at hO_ge ⊢; omega)
        (fun r hr => by have := hrs_vcap r (hrs_eq_mNN.symm ▸ hr); simp [isRootBase, ordHandleOf, tourFixedSize] at hO_ge ⊢; omega)]
      exact hzF a ha,
    fun a ha => by
      rw [hR_eq_stF a (by simp [HDR_NUM_NODES]; omega) (fun r _ => by simp [isRootBase]; omega),
        hfrF_out a (Or.inl ha), hmemO_lt_b a ha],
    fun a ha => by
      rcases ha with ⟨_, hlt⟩ | hord
      · exact lt_of_lt_of_le hlt hO_ge
      · exact (hO_foot_rng a hord).2,
    hrep0, ?_⟩
  -- Cost bound
  have hrecs_h : readOrdRecordsAt stH.mem ordPtr = recs := by
    have hwords_pos : 1 ≤ ordWords := by have := hOrdAt.2.2; omega
    simp only [readOrdRecordsAt, hHlt ordPtr (by omega)]
    exact readOrdRecords_eq_of_agree (mem ordPtr) (ordPtr + 1) fun a ha1 ha2 =>
      hHlt a (by have := hOrdAt.2.2; unfold readOrdRecordsAt at this; omega)
  rw [hrecs_h] at hcostO
  dsimp only [tourRep, tourPhi, x0]
  rw [← hOrdFin.2]
  have hphi_nil : forestPhi [] = 0 := rfl
  rw [hphi_nil, Nat.mul_zero, Nat.zero_add] at hcF
  change cF + TOUR_PHI_MULT * forestPhi treesF ≤
    ordRecordsWords recs * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) + 20 at hcF
  have h2_le : ordRecordsWords recs * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) +
      25 * mem rsPtr + 500 ≤
      TOUR_INIT1_BASE_MUL * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap := by
    have h1 : ordRecordsWords recs * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) =
        (2 * TOUR_JOIN_AMORT + 1000) * ordRecordsWords recs * tourLog eCap := by ring
    have h2 : 25 * mem rsPtr ≤ 25 * mem rsPtr * tourLog eCap := Nat.le_mul_of_pos_right _ htl
    have h3 : 500 ≤ 500 * tourLog eCap := Nat.le_mul_of_pos_right _ htl
    have hspl : TOUR_INIT1_BASE_MUL * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap =
        TOUR_INIT1_BASE_MUL * tourLog eCap +
        TOUR_INIT1_BASE_MUL * ordRecordsWords recs * tourLog eCap +
        TOUR_INIT1_BASE_MUL * mem rsPtr * tourLog eCap := by ring
    have hA : (2 * TOUR_JOIN_AMORT + 1000) * ordRecordsWords recs * tourLog eCap ≤
        TOUR_INIT1_BASE_MUL * ordRecordsWords recs * tourLog eCap :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by unfold TOUR_INIT1_BASE_MUL; omega))
    have hB : 25 * mem rsPtr * tourLog eCap ≤ TOUR_INIT1_BASE_MUL * mem rsPtr * tourLog eCap :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by unfold TOUR_INIT1_BASE_MUL TOUR_JOIN_AMORT; omega))
    have hC : 500 * tourLog eCap ≤ TOUR_INIT1_BASE_MUL * tourLog eCap :=
      Nat.mul_le_mul_right _ (by unfold TOUR_INIT1_BASE_MUL TOUR_JOIN_AMORT; omega)
    omega
  have hO_mono : mul_ord * (1 + ordRecordsWords recs) * tourLog eCap ≤
      mul_ord * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have htot : (TOUR_INIT1_BASE_MUL + mul_ord) * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap =
      TOUR_INIT1_BASE_MUL * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap +
      mul_ord * (1 + ordRecordsWords recs + mem rsPtr) * tourLog eCap := by ring
  dsimp only at hcR
  rw [hmNN_rs] at hcR
  clear * - hcH hcostO hcF hcR h2_le hO_mono htot
  omega

end MinCostFlow.SparseCore.Program
