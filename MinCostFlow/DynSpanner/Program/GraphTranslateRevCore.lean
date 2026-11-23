module

public import MinCostFlow.DynSpanner.Program.GraphTranslateRevWalks
public import MinCostFlow.DynSpanner.Program.DynGraphInit

/-!
# Reverse Graph Translation Core (`gtReverseCore`)

Assembles `gtReverseCoreStmt` (`gtIdxReverseCore = 0` in `gtRevCoreProcs`) calling
`gtRevPrimProcs` (`gtIdxBuildKeptTriples`, `gtIdxDecodeWalks`) and `dgBatchProcs`
(`dgIdxInitFromLists`) to build `DynGraphAt (outJtilde J kept)` and
`MEmbAt (citedEmbToMGraph J cJtilde kept embJJtilde)` from a `SparsifyOutRelocAt` buffer.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

def gtIdxReverseCore : ℕ := 0

/-- Reverse core translator: builds `DynGraphAt (outJtilde J kept)` and `MEmbAt (citedEmbToMGraph)`:
`[jVsPtr, nJ, jEsPtr, mJ, jTailsPtr, jHeadsPtr, guestBase, spOutGuestPtr, vCap, eCap,
  triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr]`.
Returns end of written `walkBuf`. -/
def gtReverseCoreStmt (bBatch bRevPrim : ℕ) : Stmt :=
  .assign 14 (.bin .add (.reg 6) (.reg 7)) ;;
  .assign 15 (.load (.reg 14)) ;;
  .assign 16 (.load (.bin .add (.reg 14) (.const 1))) ;;
  .assign 17 (.load (.bin .add (.reg 14) (.const 2))) ;;
  .call 18 (bRevPrim + gtIdxBuildKeptTriples)
    [.bin .add (.reg 6) (.reg 16), .reg 2, .reg 4, .reg 5, .reg 10] ;;
  .call 19 (bBatch + dgIdxInitFromLists)
    [.reg 11, .reg 8, .reg 9, .reg 1, .reg 0, .reg 18, .reg 10] ;;
  .call 20 (bRevPrim + gtIdxDecodeWalks)
    [.reg 3, .reg 2, .reg 6, .reg 15, .reg 16, .reg 17, .reg 12, .reg 13] ;;
  .ret (.reg 20)

/-- Module containing `gtReverseCoreStmt`. -/
def gtRevCoreProcs (bBatch bRevPrim : ℕ) : List Stmt :=
  [gtReverseCoreStmt bBatch bRevPrim]

/-- Contract for `gtReverseCoreStmt`. -/
def gtReverseCoreContract (w vCap eCap : ℕ) (J : MGraph) (jVs jEs jTails jHeads : List ℕ)
    (retHeap : ℕ) (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk) : Contract where
  pre args mem := ∃ jVsPtr jEsPtr jTailsPtr jHeadsPtr guestBase spOutG
      triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr,
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jVsPtr, jVs.length, jEsPtr, jEs.length, jTailsPtr, jHeadsPtr, guestBase, spOutG,
      vCap, eCap, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr] ∧
    16 ≤ 2 ^ w ∧
    vCap < 2 ^ w ∧ eCap < 2 ^ w ∧
    guestBase + retHeap < 2 ^ w ∧
    triplesBufPtr + 3 * kept.length ≤ jtildeDynPtr ∧
    jtildeDynPtr + dynGraphSize vCap eCap ≤ mEmbOutPtr ∧
    mEmbOutPtr + eCap ≤ walkBufPtr ∧
    walkBufPtr + totWalk < 2 ^ w ∧
    ZeroFrom mem triplesBufPtr ∧
    J.IsValid ∧ (∀ v ∈ J.V, v < vCap) ∧ (∀ e ∈ J.E, e < eCap) ∧
    jVs = vertsOf J.V ∧ jEs = vertsOf J.E ∧
    jTails.length = jEs.length ∧ jHeads.length = jEs.length ∧
    (∀ j (hj : j < jEs.length),
      jTails.getD j 0 = J.tail (jEs[j]'hj) ∧ jHeads.getD j 0 = J.head (jEs[j]'hj)) ∧
    kept.Nodup ∧ (∀ k ∈ kept, k < jEs.length) ∧
    cJtilde.encode.all (· < 2 ^ w) ∧
    (∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w) ∧
    cJtilde.m = kept.length ∧
    (∀ j < jEs.length,
      (embJJtilde j).verts.length < 2 ^ w ∧ (embJJtilde j).edges.length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w)) ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem jEsPtr jEs ∧
    ListAt mem jTailsPtr jTails ∧ ListAt mem jHeadsPtr jHeads ∧
    jVsPtr + jVs.length ≤ triplesBufPtr ∧
    jEsPtr + jEs.length ≤ triplesBufPtr ∧
    jTailsPtr + jEs.length ≤ triplesBufPtr ∧
    jHeadsPtr + jEs.length ≤ triplesBufPtr ∧
    guestBase + retHeap ≤ triplesBufPtr ∧
    SparsifyOutRelocAt mem guestBase spOutG retHeap jEs.length cJtilde kept embJJtilde
  post args mem ret mem' := ∃ jVsPtr jEsPtr jTailsPtr jHeadsPtr guestBase spOutG
      triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr,
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jVsPtr, jVs.length, jEsPtr, jEs.length, jTailsPtr, jHeadsPtr, guestBase, spOutG,
      vCap, eCap, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr] ∧
    ret = walkBufPtr + totWalk ∧
    DynGraphAt mem' jtildeDynPtr vCap eCap (outJtilde J kept) ∧
    MEmbAt mem' mEmbOutPtr J.E eCap (citedEmbToMGraph J cJtilde kept embJJtilde) ∧
    (∀ j (hj : j < jEs.length),
      let wPtr := mem' (mEmbOutPtr + jEs[j]'hj)
      walkBufPtr ≤ wPtr ∧
      wPtr + (mWalkEncode (citedDecWalk jEs cJtilde kept embJJtilde j)).length ≤ walkBufPtr + totWalk) ∧
    ZeroFrom mem' (walkBufPtr + totWalk) ∧
    ∀ addr, addr < triplesBufPtr → mem' addr = mem addr
  cost args _ :=
    130 * args.getD 1 0 + 565 * kept.length +
    250 * ((List.range (args.getD 3 0)).map fun j => (embJJtilde j).edges.length).sum +
    200 * args.getD 3 0 + 260

end

public section

theorem gtReverseCore_meetsContract {w vCap eCap : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bRevPrim bRevCore : ℕ}
    {J : MGraph} {jVs jEs jTails jHeads : List ℕ} {retHeap : ℕ}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bRevCore + gtIdxReverseCore)
      (gtReverseCoreContract w vCap eCap J jVs jEs jTails jHeads retHeap cJtilde kept embJJtilde) := by
  refine meetsContract_of_runs
    (hpRevCore.get (i := gtIdxReverseCore) (by simp [gtRevCoreProcs, gtIdxReverseCore]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, guestBase, spOutG,
    triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr, rfl,
    hw16, hvCap_ltw, heCap_ltw, hgB_ltw, htr_le, hjtd_le, hmemb_le, hwb_ltw,
    hz, hJ_val, hvJ_cap, heJ_cap, hjV_eq, hjE_eq, hLenT, hLenHd, hTHd,
    hkept_nd, hkept_lt, hcJall, hcJ_w, hcJm, hembWalks,
    hjV_at, hjE_at, hjT_at, hjHd_at, hjV_le, hjE_le, hjT_le, hjHd_le, hsp_le, hspOut⟩
  rcases hspOut with ⟨hsp3, hjtilde_hb, hkept_hb, hemb_hb, hJtilde_at, hkept_at, hemb_at⟩
  set pJtilde := mem (guestBase + spOutG)
  set pKept := mem (guestBase + spOutG + 1)
  set pEmb := mem (guestBase + spOutG + 2)
  let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
  let eEdges := kept.map fun idx => (jEs.getD idx 0, jTails.getD idx 0, jHeads.getD idx 0)
  have hlt_jVP : jVsPtr < 2 ^ w := hargs jVsPtr (by simp)
  have hlt_nJ : jVs.length < 2 ^ w := hargs jVs.length (by simp)
  have hlt_jEP : jEsPtr < 2 ^ w := hargs jEsPtr (by simp)
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_jTP : jTailsPtr < 2 ^ w := hargs jTailsPtr (by simp)
  have hlt_jHP : jHeadsPtr < 2 ^ w := hargs jHeadsPtr (by simp)
  have hlt_gB : guestBase < 2 ^ w := hargs guestBase (by simp)
  have hlt_spO : spOutG < 2 ^ w := hargs spOutG (by simp)
  have hlt_trB : triplesBufPtr < 2 ^ w := hargs triplesBufPtr (by simp)
  have hlt_jtdP : jtildeDynPtr < 2 ^ w := hargs jtildeDynPtr (by simp)
  have hlt_mEP : mEmbOutPtr < 2 ^ w := hargs mEmbOutPtr (by simp)
  have hlt_wBP : walkBufPtr < 2 ^ w := hargs walkBufPtr (by simp)
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have hsp_addr_ltw : guestBase + spOutG < 2 ^ w := by omega
  have hsp1_ltw : guestBase + spOutG + 1 < 2 ^ w := by omega
  have hsp2_ltw : guestBase + spOutG + 2 < 2 ^ w := by omega
  have hpJtilde_ltw : pJtilde < 2 ^ w := by
    have : 2 ≤ cJtilde.encode.length := by rw [graph_encode_length]; omega
    omega
  have hpKept_ltw : pKept < 2 ^ w := by omega
  have hpEmb_ltw : pEmb < 2 ^ w := by omega
  have hgk_ltw : guestBase + pKept < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [gtRevCoreProcs, gtIdxReverseCore, List.getElem_cons_zero, gtReverseCoreStmt]
  refine runs_seq_assign_le (v := guestBase + spOutG)
    (by simp [Expr.eval, BinOp.eval, startState, hsp_addr_ltw]) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := pJtilde)
    (by simp [Expr.eval, Function.update_self]) rfl) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := pKept)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self, h1_lt, hsp1_ltw]) rfl) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := pEmb)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self, h2_lt, hsp2_ltw]) rfl) ?_
  have hK_w : ∀ idx ∈ kept, jEs[idx]! < 2 ^ w ∧ jTails[idx]! < 2 ^ w ∧ jHeads[idx]! < 2 ^ w := by
    intro idx hidx
    have hi := hkept_lt idx hidx
    have hJe : jEs[idx]'hi ∈ J.E := by
      have hm : jEs[idx]'hi ∈ vertsOf J.E := hjE_eq ▸ List.getElem_mem hi
      rwa [mem_vertsOf] at hm
    have hJt := (hJ_val _ hJe).1
    have hJh := (hJ_val _ hJe).2
    have he_w : jEs[idx]'hi < 2 ^ w := lt_trans (heJ_cap _ hJe) heCap_ltw
    have ht_w : J.tail (jEs[idx]'hi) < 2 ^ w := lt_trans (hvJ_cap _ hJt) hvCap_ltw
    have hh_w : J.head (jEs[idx]'hi) < 2 ^ w := lt_trans (hvJ_cap _ hJh) hvCap_ltw
    have hth := hTHd idx hi
    rw [List.getD_eq_getElem _ _ (hLenT ▸ hi)] at hth
    have hth2 := (hTHd idx hi).2
    rw [List.getD_eq_getElem _ _ (hLenHd ▸ hi)] at hth2
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (hLenT ▸ hi), List.getElem?_eq_getElem (hLenHd ▸ hi),
      Option.getD_some]
    exact ⟨he_w, hth.1 ▸ ht_w, hth2 ▸ hh_w⟩
  refine runs_seq_call_le (gtBuildKeptTriples_meetsContract hpRevPrim)
    (vs := [guestBase + pKept, jEsPtr, jTailsPtr, jHeadsPtr, triplesBufPtr])
    (by simp only [evalArgs, Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, startState]
        simp [hgk_ltw])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨guestBase + pKept, jEsPtr, jTailsPtr, jHeadsPtr, triplesBufPtr, rfl,
      hw16, by omega, by omega, by omega, by omega, by omega, hLenT, hLenHd, hkept_lt, hK_w,
      fun i hi => Or.inl (by omega), fun i hi => Or.inl (by omega),
      fun i hi => Or.inl (by omega), fun i hi => Or.inl (by omega),
      hkept_at, hjE_at, hjT_at, hjHd_at⟩ ?_
  intro retTr mem1 pos1 ⟨_, _, _, _, _, hargsTr, hretTr, htr_at, hfrTr⟩
  simp only [List.cons.injEq, and_true] at hargsTr
  rcases hargsTr with ⟨_, rfl, rfl, rfl, rfl⟩
  have hfrTr' : ∀ addr, addr < triplesBufPtr ∨ triplesBufPtr + 3 * kept.length ≤ addr →
      mem1 addr = mem addr := hfrTr
  have hz1 : ZeroFrom mem1 jtildeDynPtr := fun addr ha => by
    rw [hfrTr' addr (Or.inr (le_trans htr_le ha))]
    exact hz addr (le_trans (Nat.le_add_right _ _) (le_trans htr_le ha))
  have hkept_lt_m : ∀ k ∈ kept, k < J.m := fun k hk => by
    change k < J.E.card
    simpa [hjE_eq, vertsOf_length] using hkept_lt k hk
  have hOutJ_val : (outJtilde J kept).IsValid := outJtilde_isValid hJ_val kept hkept_lt_m
  have hOutJ_V : ∀ v ∈ (outJtilde J kept).V, v < vCap := fun v hv => hvJ_cap v hv
  have hOutJ_E : ∀ e ∈ (outJtilde J kept).E, e < eCap := fun e he =>
    heJ_cap e ((outJtilde_isSubgraph J kept hkept_lt_m).2.1 he)
  have hjV_mem1 : ListAt mem1 jVsPtr jVs := fun i hi => by
    rw [hfrTr' _ (Or.inl (by omega))]; exact hjV_at i hi
  have hjV_iff : ∀ v, v ∈ jVs ↔ v ∈ (outJtilde J kept).V := fun v => by
    simp [outJtilde, hjV_eq, mem_vertsOf]
  have heEdges_len : eEdges.length = kept.length := by simp [eEdges]
  have heEdges_nd : (eEdges.map Prod.fst).Nodup := by
    dsimp only [eEdges]
    rw [List.map_map]
    refine hkept_nd.map_on ?_
    intro k₁ hk₁ k₂ hk₂ heq
    dsimp only [Function.comp_apply] at heq
    have h1 := idxOf_getD_vertsOf (hkept_lt_m k₁ hk₁)
    have h2 := idxOf_getD_vertsOf (hkept_lt_m k₂ hk₂)
    rw [← hjE_eq] at h1 h2
    rw [heq] at h1
    exact h1.symm.trans h2
  have heEdges_spec : ∀ t ∈ eEdges,
      t.1 ∈ (outJtilde J kept).E ∧ t.2.1 = (outJtilde J kept).tail t.1 ∧ t.2.2 = (outJtilde J kept).head t.1 := by
    intro t ht
    rw [List.mem_map] at ht
    rcases ht with ⟨idx, hidx_mem, rfl⟩
    have hidx := hkept_lt idx hidx_mem
    have hth := hTHd idx hidx
    refine ⟨?_, ?_, ?_⟩
    · simp only [outJtilde, List.mem_toFinset, List.mem_map]
      exact ⟨idx, hidx_mem, by rw [hjE_eq]⟩
    · dsimp only [outJtilde]; rw [List.getD_eq_getElem _ 0 hidx]; exact hth.1
    · dsimp only [outJtilde]; rw [List.getD_eq_getElem _ 0 hidx]; exact hth.2
  have heEdges_cov : ∀ e ∈ (outJtilde J kept).E, ∃ t ∈ eEdges, t.1 = e := by
    intro e he
    simp only [outJtilde, List.mem_toFinset, List.mem_map] at he
    rcases he with ⟨idx, hidx_mem, he_eq⟩
    exact ⟨(jEs.getD idx 0, jTails.getD idx 0, jHeads.getD idx 0),
      List.mem_map.mpr ⟨idx, hidx_mem, rfl⟩, by rw [← hjE_eq] at he_eq; exact he_eq⟩
  have heEdges_at : ∀ i (hi : i < eEdges.length),
      mem1 (triplesBufPtr + 3 * i) = eEdges[i].1 ∧
      mem1 (triplesBufPtr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem1 (triplesBufPtr + 3 * i + 2) = eEdges[i].2.2 := fun i hi => by
    have hi' : i < kept.length := by simpa [heEdges_len] using hi
    have h := htr_at i hi'
    simpa [eEdges, hi'] using h
  refine runs_seq_call_le (dgInitFromLists_meetsContract (vCap := vCap) (eCap := eCap)
      (G := outJtilde J kept) (vL := jVs) (eEdges := eEdges) hpBatch hpEdge hpOps)
    (vs := [jtildeDynPtr, vCap, eCap, jVs.length, jVsPtr, kept.length, triplesBufPtr])
    (by simp only [evalArgs, Expr.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, startState]
        rw [hretTr]; rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨jtildeDynPtr, jVs.length, jVsPtr, kept.length, triplesBufPtr, rfl, hw16, by omega, hz1,
      hOutJ_val, hOutJ_V, hOutJ_E, rfl, hjV_mem1, hjV_iff,
      fun i hi => by omega, heEdges_len, heEdges_nd, heEdges_at, heEdges_spec, heEdges_cov,
      fun i hi => by omega⟩ ?_
  intro retDyn mem2 pos2 ⟨_, _, _, _, _, hargsDyn, _, hDyn_at, hfrDyn, hz2⟩
  simp only [List.cons.injEq, and_true] at hargsDyn
  rcases hargsDyn with ⟨rfl, _, _, _, rfl, _, rfl⟩
  have hmem2_eq : ∀ addr, addr < triplesBufPtr → mem2 addr = mem addr := fun addr ha =>
    (hfrDyn addr (Or.inl (by omega))).trans (hfrTr' addr (Or.inl ha))
  refine runs_seq_call_le (gtDecodeWalks_meetsContract hpRevPrim)
    (vs := [jEs.length, jEsPtr, guestBase, pJtilde, pKept, pEmb, mEmbOutPtr, walkBufPtr])
    (by simp only [evalArgs, Expr.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, startState]
        rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨jEs.length, jEsPtr, guestBase, pJtilde, pKept, pEmb, mEmbOutPtr, walkBufPtr,
      rfl, rfl, hw16, by omega, by omega, by omega, by omega, by omega, by omega,
      hjE_eq, heJ_cap, hkept_lt,
      fun j hj => by
        rcases hembWalks j hj with ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, h3, h4⟩
        dsimp only
        rw [hmem2_eq (guestBase + pEmb + j) (by omega)]
        have := (hemb_at j hj).1
        omega,
      hcJall, hcJ_w,
      fun i hi => (hmem2_eq (jEsPtr + i) (by omega)).trans (hjE_at i hi),
      fun i hi => (hmem2_eq (guestBase + pJtilde + i) (by omega)).trans (hJtilde_at i hi),
      fun i hi => (hmem2_eq (guestBase + pKept + i) (by
        simp only [List.length_cons] at hi; omega)).trans (hkept_at i hi),
      fun j hj => by
        have hp := hmem2_eq (guestBase + pEmb + j) (by omega)
        dsimp only
        rw [hp]
        intro i hi
        rw [hmem2_eq (guestBase + mem (guestBase + pEmb + j) + i)
          (by have := (hemb_at j hj).1; omega)]
        exact (hemb_at j hj).2 i hi,
      Or.inl hmemb_le,
      fun i hi => ⟨Or.inl (by omega), Or.inl (by omega)⟩,
      fun i hi => ⟨Or.inl (by omega), Or.inl (by omega)⟩,
      fun i hi => ⟨Or.inl (by omega), Or.inl (by omega)⟩,
      fun j hj => ⟨Or.inl (by omega), Or.inl (by omega)⟩,
      fun j hj i hi => by
        dsimp only
        rw [hmem2_eq (guestBase + pEmb + j) (by omega)]
        have := (hemb_at j hj).1
        exact ⟨Or.inl (by omega), Or.inl (by omega)⟩⟩ ?_
  intro retDec mem3 pos3 ⟨_, _, _, _, _, _, _, hargsDec, hretDec, hmEmb3, hwb3, hfrDec⟩
  simp only [List.cons.injEq, true_and, and_true] at hargsDec
  rcases hargsDec with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hDyn3 : DynGraphAt mem3 jtildeDynPtr vCap eCap (outJtilde J kept) :=
    hDyn_at.of_agree fun addr h1 h2 =>
      hfrDec addr (Or.inl (by omega)) (Or.inl (by omega))
  have hz3 : ZeroFrom mem3 (walkBufPtr + totWalk) := fun addr ha => by
    rw [hfrDec addr (Or.inr (by omega)) (Or.inr ha)]
    exact hz2 addr (by omega)
  have hfr3 : ∀ addr, addr < triplesBufPtr → mem3 addr = mem addr := fun addr ha =>
    (hfrDec addr (Or.inl (by omega)) (Or.inl (by omega))).trans (hmem2_eq addr ha)
  refine runs_ret_le (v := walkBufPtr + totWalk)
    (by simp [Expr.eval, Function.update_self, hretDec, totWalk])
    ⟨jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, guestBase, spOutG,
      triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr,
      rfl, rfl, hDyn3, hmEmb3, hwb3, hz3, hfr3⟩ ?_
  dsimp only [gtReverseCoreContract, gtBuildKeptTriplesContract, dgInitFromListsContract,
    gtDecodeWalksContract, argsSize, Expr.size]
  simp only [List.getD_cons_succ, List.getD_cons_zero, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]
  omega

end

end MinCostFlow.DynSpanner.Program
