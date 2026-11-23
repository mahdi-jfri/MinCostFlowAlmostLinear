module

public import MinCostFlow.Spanner.ProgTask2StepsDrainBase

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM True-branch step for `t2DrainQueue` -/

lemma t2Drain_vhat_forRange {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {ci hCurOld hCurNew : ℕ} (hci : ci < ctx.wd.comps.length)
    (hH_lo : stc.dsBaseAddr ≤ hCurOld) (hH_le : hCurOld ≤ hCurNew)
    (hH_hi : hCurNew ≤ Task2Input.maxHeapEnd impl inp)
    (L : List ℕ) (hL_sub : ∀ v ∈ L, v < (ctx.wd.comps[ci]'hci).J_sub.n)
    (hL_nd : L.Nodup) (memDS : ℕ → ℕ)
    (hSeqDS : WordRAM.SeqAt memDS hCurOld L) (hZDS : WordRAM.ZeroFrom memDS hCurNew)
    (r_init : ℕ → ℕ)
    (hr0 : r_init 3 = g₀.η₁) (hr9 : r_init 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr19 : r_init 19 = hCurOld) (hr20 : r_init 20 = L.length)
    (hr21 : r_init 21 = vhatBase ctx.wd ci) (pos₀ : ℕ) (ω : ℕ → Bool) :
    let voff := vhatBase ctx.wd ci
    let vhatSAddr := inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
    let vHeadA := inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length
    let body :=
      Stmt.assign 23 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 22))) ;;
      t2St (.reg 9) (t2Add (.reg 21) (.reg 23)) (.reg 3)
    ∃ st' c,
      Runs w p ω (forRange 22 (.const 0) (.reg 20) body) ⟨memDS, r_init, pos₀⟩ .normal st' c ∧
      (∀ r ≤ 21, st'.regs r = r_init r) ∧
      (∀ a, ¬(vhatSAddr ≤ a ∧ a < vHeadA) → st'.mem a = memDS a) ∧
      (∀ v ∈ L, st'.mem (vhatSAddr + voff + v) = g₀.η₁) ∧
      (∀ a, (∀ v ∈ L, a ≠ vhatSAddr + voff + v) → st'.mem a = memDS a) ∧
      c ≤ L.length * 24 + 7 := by
  intro voff vhatSAddr vHeadA body
  rcases drain_bounds ctx stc with ⟨_, _, _, _, _, _, _, h_vhd, h_vc, h_ps, h_ew, h_q, h_nlo, h_nds, _, _, _, _, hW, h_jm, hvsum⟩
  have hJm_pos : 1 ≤ inp.J.m := by
    have hci_m : 1 ≤ (ctx.wd.comps[ci]'hci).J_sub.m := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.1
    have hcomp_m := List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map_of_mem (f := fun c => c.J_sub.m) (List.getElem_mem hci))
    omega
  have hvoff_add : voff + (ctx.wd.comps[ci]'hci).J_sub.n ≤ 2 * inp.J.m := by
    have h1 := vhatBase_add_le hci
    have h2 := vhatBase_le_sum (wd := ctx.wd) (by omega : ci + 1 ≤ ctx.wd.comps.length)
    dsimp only [voff]; linarith
  have hL_len_le : L.length ≤ (ctx.wd.comps[ci]'hci).J_sub.n := by
    have hsub : L.toFinset ⊆ Finset.range (ctx.wd.comps[ci]'hci).J_sub.n := fun v hv =>
      Finset.mem_range.mpr (hL_sub v (List.mem_toFinset.mp hv))
    simpa [List.toFinset_card_of_nodup hL_nd] using Finset.card_le_card hsub
  have hL_w : L.length < 2 ^ w := by omega
  have hη_w : g₀.η₁ < 2 ^ w := by
    have hη_cap : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J := by
      rw [← ctx.hWInpJ]; exact task2_eta1Bound_le_cap (WSubs := ctx.WSubs) ctx.hstat ctx.hφ_lb
    have h3 : Task2Input.eta1Cap impl inp.J ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans (Nat.le_mul_of_pos_right _ hJm_pos)
        (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
    have := hS.hη_bd; omega
  let P0 : State → Prop := fun st =>
    (∀ r ≤ 21, st.regs r = r_init r) ∧
    (∀ a, ¬(vhatSAddr ≤ a ∧ a < vHeadA) → st.mem a = memDS a) ∧
    (∀ a, (∀ v ∈ L, a ≠ vhatSAddr + voff + v) → st.mem a = memDS a)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ r ≤ 21, st.regs r = r_init r) ∧ st.regs 22 = j ∧
    (∀ a, ¬(vhatSAddr ≤ a ∧ a < vHeadA) → st.mem a = memDS a) ∧
    (∀ v ∈ (L.take j).toFinset, st.mem (vhatSAddr + voff + v) = g₀.η₁) ∧
    (∀ a, (∀ v ∈ L, a ≠ vhatSAddr + voff + v) → st.mem a = memDS a)
  have htrip : Triple w p P0 (forRange 22 (.const 0) (.reg 20) body) (normalPost (Inv L.length))
      (fun _ => L.length * 24 + 7) := by
    have hfor := Triple.forRange_const (w := w) (p := p) (P := P0) (r := 22) (lo := .const 0) (hi := .reg 20)
      (body := body) (Inv := Inv) (stepBound := 15) (loVal := 0) (hiVal := L.length)
      (Nat.zero_le _) hW (fun _ => hL_w)
      (fun st hInv => by
        refine ⟨Expr.eval_const (by omega), ?_⟩
        rcases hInv with ⟨hr, hagr, hne⟩
        refine ⟨fun r hr_le => ?_, by simp, hagr, fun _ hv => by simp at hv, hne⟩
        dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le)
      (fun j st _ _ hI => hI.2.1)
      (fun j st _ _ hI => Expr.eval_reg_of_eq (by rw [hI.1 20 (by omega), hr20]))
      fun j _ hj => by
        set x := L[j]'hj
        have hx_lt : x < (ctx.wd.comps[ci]'hci).J_sub.n := hL_sub x (List.getElem_mem hj)
        have hseq_bd := drain_seqAt_nodup_add_le hL_nd hSeqDS hZDS hH_le hj
        have hSeqCur : ∀ (st : State), Inv j st → st.mem (hCurOld + (1 + j)) = x := fun st hI => by
          rw [hI.2.2.1 _ (by omega), show hCurOld + (1 + j) = hCurOld + 1 + j by omega]
          exact hSeqDS.2 j hj
        have hs1 := Triple.assign (w := w) (p := p) (P := Inv j) (r := 23)
          (e := t2Ld (.reg 19) (t2Add (.const 1) (.reg 22))) (val := fun _ => x)
          (Q := fun st₁ => Inv j st₁ ∧ st₁.regs 23 = x)
          (fun st hI => by
            have he_add := Expr.eval_add (Expr.eval_const hW) (Expr.eval_reg_of_eq hI.2.1) (by omega)
            have he_a := Expr.eval_add (Expr.eval_reg_of_eq ((hI.1 19 (by omega)).trans hr19)) he_add (by omega)
            simpa only [t2Ld, hSeqCur st hI] using Expr.eval_load he_a)
          (fun st hI => by
            rcases hI with ⟨hr, hr22, hagr, htk, hne⟩
            refine ⟨⟨fun r hr_le => ?_, ?_, hagr, htk, hne⟩, by simp⟩
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr22)
        have hdst_eq : vhatSAddr + (voff + x) = vhatSAddr + voff + x := by omega
        have hs2 := Triple.store (w := w) (p := p)
          (P := fun st₁ => Inv j st₁ ∧ st₁.regs 23 = x)
          (a := t2Add (.reg 9) (t2Add (.reg 21) (.reg 23))) (e := .reg 3)
          (addr := fun _ => vhatSAddr + (voff + x)) (val := fun _ => g₀.η₁)
          (Q := fun st₂ =>
            Inv (j + 1) { st₂ with regs := Function.update st₂.regs 22 (j + 1) } ∧ st₂.regs 22 = j)
          (fun st ⟨hI, hr23⟩ => Expr.eval_add
            (Expr.eval_reg_of_eq ((hI.1 9 (by omega)).trans hr9))
            (Expr.eval_add (Expr.eval_reg_of_eq ((hI.1 21 (by omega)).trans hr21))
              (Expr.eval_reg_of_eq hr23) (by omega)) (by omega))
          (fun st ⟨hI, _⟩ => Expr.eval_reg_of_eq ((hI.1 3 (by omega)).trans hr0))
          (fun st ⟨hI, _⟩ => by
            rcases hI with ⟨hr, hr22, hagr, htk, hne⟩
            refine ⟨⟨fun r hr_le => ?_, by simp, fun a ha => ?_, fun v hv => ?_,
                fun a ha_not => ?_⟩, by dsimp only; exact hr22⟩
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hagr a ha
            · have htk_succ : L.take (j + 1) = L.take j ++ [x] := by
                rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
              rw [htk_succ, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
                insert_empty_eq, Finset.mem_union, Finset.mem_singleton] at hv
              dsimp only
              rcases hv with hv_old | rfl
              · by_cases heq : v = x
                · subst heq; rw [← hdst_eq, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact htk v hv_old
              · rw [← hdst_eq, Function.update_self]
            · dsimp only; rw [Function.update_of_ne (by have := ha_not x (List.getElem_mem hj); omega)]
              exact hne a ha_not)
        exact Triple.seq_normal (T := fun _ => 15) hs1 hs2 fun _ _ _ _ => by simp only [Expr.size]; omega
    exact hfor.mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega
  obtain ⟨o, st', c, hr, hq, hc⟩ := htrip ⟨memDS, r_init, pos₀⟩ ω
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hregs, _, hagr, htk, hne⟩
    rw [List.take_of_length_le (le_refl _)] at htk
    exact ⟨st', c, hr, hregs, hagr, fun v hv => htk v (List.mem_toFinset.mpr hv), hne, by omega⟩

lemma t2Drain_node_true_step {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {i : ℕ} (hi : i < g₀.queue.length)
    {ci b next : ℕ} {rest : List (ℕ × ℕ)}
    {drained : Finset ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → impl.pathDS.R.τ}
    {hCur deleteCountJ : ℕ} {st : State} {ω : ℕ → Bool}
    (hD : T2DrainInv ctx stc g₀ memStart drained states reps hCur deleteCountJ st.mem)
    (hci : ci < ctx.wd.comps.length) (hb_m : b < (ctx.wd.comps[ci]'hci).J_sub.m)
    (hx_in : g₀.queue[i] ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts)
    (hdel_lt : st.mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length +
      compEdgeBase ctx.wd ci + b) < g₀.η₁)
    (hnext_chain : IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd next rest)
    (hr0 : st.regs 0 = inp.v1) (hr3 : st.regs 3 = g₀.η₁)
    (hr7 : st.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr8 : st.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr9 : st.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr10 : st.regs 10 = inp.dsHandlesAddr ctx.wd.W.m) (hr11 : st.regs 11 = hCur)
    (hr15 : st.regs 15 = ci) (hr16 : st.regs 16 = b)
    (hr17 : st.regs 17 = compEdgeBase ctx.wd ci + b) :
    let trueBody :=
      t2St (.reg 7) (.reg 17) (.reg 3) ;;
      t2St (.reg 0) (.const 5) (t2Add (t2Ld (.reg 0) (.const 5)) (.const 1)) ;;
      Stmt.assign 18 (t2Ld (.reg 10) (.reg 15)) ;;
      Stmt.assign 19 (.reg 11) ;;
      Stmt.call 11 (dsBase + 1) [.reg 18, .reg 16, .reg 11] ;;
      Stmt.assign 20 (.load (.reg 19)) ;;
      Stmt.assign 21 (t2Ld (.reg 8) (.reg 15)) ;;
      forRange 22 (.const 0) (.reg 20) (
        Stmt.assign 23 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 22))) ;;
        t2St (.reg 9) (t2Add (.reg 21) (.reg 23)) (.reg 3)
      )
    let kDel := t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m
    ∃ st' c states' reps' hCur',
      Runs w p ω trueBody st .normal st' c ∧
      (∀ r ≤ 14, r ≠ 11 → st'.regs r = st.regs r) ∧
      st'.regs 11 = hCur' ∧
      (∀ k, (states k).deleted ⊆ (states' k).deleted) ∧
      T2DrainInv ctx stc g₀ memStart drained states' reps' hCur' (deleteCountJ + 1) st'.mem ∧
      b ∈ (states' ci).deleted ∧
      IncChainBound st'.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd next rest ∧
      c + t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
            (∑ k ∈ Finset.range ctx.wd.comps.length, ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
              ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
                (· ∈ (states' k).deleted)).card))
            (∑ k ∈ Finset.range ctx.wd.comps.length, ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
              ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
                (· ∈ (states' k).Vhat)).card))
            0 reps' st'.mem + 52 ≤
        t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
            (∑ k ∈ Finset.range ctx.wd.comps.length, ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
              ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
                (· ∈ (states k).deleted)).card))
            (∑ k ∈ Finset.range ctx.wd.comps.length, ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
              ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
                (· ∈ (states k).Vhat)).card))
            0 reps st.mem := by
  intro trueBody kDel
  rcases drain_bounds ctx stc with ⟨h_v1, h_emb, h_hdl, h_ceb, h_vho, h_del, h_vh, h_vhd, h_vc, h_ps,
    h_ew, h_q, h_nlo, h_nds, h_dsc, h_stc, h_mhe, h_mwb, hW, h_jm, hvsum⟩
  have hmW := ctx.hmW_le; have hK := ctx.hK_le
  have hds_b := ctx.ds_bounds; have hci_b := hds_b.1 ci hci
  have hJm_pos : 1 ≤ inp.J.m := by
    have hci_m : 1 ≤ (ctx.wd.comps[ci]'hci).J_sub.m := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.1
    have hcomp_m := List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map_of_mem (f := fun c => c.J_sub.m) (List.getElem_mem hci))
    omega
  have hη₁_cap : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J := by
    rw [← ctx.hWInpJ]; exact task2_eta1Bound_le_cap (WSubs := ctx.WSubs) ctx.hstat ctx.hφ_lb
  have hη_w : g₀.η₁ < 2 ^ w := by
    have h3 : Task2Input.eta1Cap impl inp.J ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans (Nat.le_mul_of_pos_right _ hJm_pos)
        (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
    have := hS.hη_bd; omega
  have hb_ndel : b ∉ (states ci).deleted := fun hmem => by
    have := ((hD.hDelR ci hci b hb_m).2).mpr hmem; omega
  have hdel_add1_cur :
      ∑ k ∈ Finset.range ctx.wd.comps.length, (states k).deleted.card + 1 ≤ inp.J.m := by
    let D' : ℕ → Finset ℕ := fun k => if k = ci then insert b (states ci).deleted else (states k).deleted
    have hD' : ∀ k (hk : k < ctx.wd.comps.length) z, z ∈ D' k → z < (ctx.wd.comps[k]'hk).J_sub.m := by
      intro k hk z hz; by_cases hkc : k = ci
      · subst hkc; simp only [D', ↓reduceIte, Finset.mem_insert] at hz
        exact hz.elim (fun h => h ▸ hb_m) (fun h => (hD.hDelSub k hk z h).1)
      · simp only [D', hkc, ↓reduceIte] at hz; exact (hD.hDelSub k hk z hz).1
    have hle := drain_del_family_card_le_J ctx D' hD'
    have hmem : ci ∈ Finset.range ctx.wd.comps.length := Finset.mem_range.mpr hci
    rw [← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem] at hle ⊢
    have hrest : ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci, (D' k).card =
        ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci, (states k).deleted.card :=
      Finset.sum_congr rfl fun k hk => by simp [D', Finset.ne_of_mem_erase hk]
    rw [hrest] at hle
    have hcard_ci : (D' ci).card = (states ci).deleted.card + 1 := by
      simp [D', Finset.card_insert_of_notMem hb_ndel]
    omega
  have hdel_tot1 : deleteCountJ + 1 ≤ g₀.η₁ * inp.J.m := by
    rw [hD.hDelEq]
    have hmul : (g₀.η₁ - 1) * inp.J.m + inp.J.m = g₀.η₁ * inp.J.m := by
      calc (g₀.η₁ - 1) * inp.J.m + inp.J.m = (g₀.η₁ - 1 + 1) * inp.J.m := by ring
        _ = g₀.η₁ * inp.J.m := by rw [Nat.sub_add_cancel hS.hη_pos]
    linarith [hS.hPrevDel, hdel_add1_cur]
  have hdel_w : deleteCountJ + 1 < 2 ^ w := by
    have h1 : Task2Input.eta1Cap impl inp.J * inp.J.m ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans (by omega : Task2Input.eta1Cap impl inp.J * inp.J.m ≤
          Task2Input.eta1Cap impl inp.J * inp.J.m + 2 * Task1Input.mwCap impl inp.J + 2)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have := Nat.mul_le_mul_right inp.J.m (le_trans hS.hη_bd hη₁_cap); omega
  have hSpace_w : hCur + impl.pathDS.params.delSpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m ctx.wd.J0_strip.m < 2 ^ w := by
    have hinit_le : g₀.initCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
      rw [hS.hInitC]; exact Nat.mul_le_mul (le_trans hS.hη_bd hη₁_cap) hK
    have hgp_le : g₀.getPathCountJ ≤ Task1Input.mwCap impl inp.J := by
      have : g₀.getPathCountJ ≤ ctx.wd.W.m := by have := hS.hGetC; omega
      exact le_trans this hmW
    have hdel_cap1 := le_trans hdel_tot1 (Nat.mul_le_mul_right _ (le_trans hS.hη_bd hη₁_cap))
    have hsum_mul : (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1) * t2DsOne impl inp.J ≤
        Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := by
      have hm := Nat.mul_le_mul_right (t2DsOne impl inp.J)
        (show g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1 ≤
          Task2Input.eta1Cap impl inp.J * inp.J.m +
          Task2Input.eta1Cap impl inp.J * inp.J.m + Task1Input.mwCap impl inp.J by omega)
      simpa only [Nat.add_mul] using hm
    have h_mhe_eq : Task2Input.maxHeapEnd impl inp =
        Task2Input.staticEndCap impl inp + Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := rfl
    have hcur_le_mhe : hCur + t2DsOne impl inp.J ≤ Task2Input.maxHeapEnd impl inp := by
      rw [h_mhe_eq]
      calc hCur + t2DsOne impl inp.J
          ≤ stc.dsBaseAddr + (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ) * t2DsOne impl inp.J +
              t2DsOne impl inp.J := Nat.add_le_add_right hD.hHCur_le _
        _ = stc.dsBaseAddr + (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1) * t2DsOne impl inp.J := by
              rw [add_assoc, ← Nat.succ_mul]
        _ ≤ Task2Input.staticEndCap impl inp +
              (Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
               Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
               Task1Input.mwCap impl inp.J * t2DsOne impl inp.J) := Nat.add_le_add h_dsc hsum_mul
        _ = _ := by ring
    exact lt_of_le_of_lt (Nat.add_le_add_left hci_b.2.1 hCur)
      (lt_of_le_of_lt hcur_le_mhe (lt_of_le_of_lt h_mhe h_mwb))
  have hcur_w : hCur < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hSpace_w
  have hdelIdx_lt : compEdgeBase ctx.wd ci + b < inp.J.m := by
    have ha1 := compEdgeBase_add_le hci
    have ha2 := compEdgeBase_le_sum (wd := ctx.wd) (by omega : ci + 1 ≤ ctx.wd.comps.length); omega
  set delA := inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + (compEdgeBase ctx.wd ci + b)
  set mem1 := Function.update st.mem delA g₀.η₁
  have hr_u1 : Runs w p ω (t2St (.reg 7) (.reg 17) (.reg 3)) st .normal { st with mem := mem1 } 5 :=
    runs_store_iff.mpr ⟨delA, g₀.η₁,
      Expr.eval_add (Expr.eval_reg_of_eq hr7) (Expr.eval_reg_of_eq hr17) (by omega),
      Expr.eval_reg_of_eq hr3, rfl, rfl, by simp [Expr.size]⟩
  set st1 : State := { st with mem := mem1 }
  set mem2 := Function.update mem1 (inp.v1 + 5) (deleteCountJ + 1)
  have he_v15 : (t2Add (.reg 0) (.const 5)).eval w st1 = some (inp.v1 + 5) :=
    Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by omega)) (by omega)
  have hr_u2 : Runs w p ω (t2St (.reg 0) (.const 5) (t2Add (t2Ld (.reg 0) (.const 5)) (.const 1)))
      st1 .normal { st1 with mem := mem2 } 10 := by
    have hm : mem1 (inp.v1 + 5) = deleteCountJ := by
      dsimp only [mem1]; rw [Function.update_of_ne (by omega), hD.h5]
    have he_del_p1 := Expr.eval_add (by simpa only [t2Ld, st1, hm] using Expr.eval_load he_v15)
      (Expr.eval_const hW) hdel_w
    exact runs_store_iff.mpr ⟨inp.v1 + 5, deleteCountJ + 1, he_v15, he_del_p1, rfl, rfl, by simp [Expr.size]⟩
  set st2 : State := { st1 with mem := mem2 }
  have hhdl_eq : mem2 (inp.dsHandlesAddr ctx.wd.W.m + ci) = st.mem (inp.dsHandlesAddr ctx.wd.W.m + ci) := by
    dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  set r3 := Function.update st2.regs 18 (st.mem (inp.dsHandlesAddr ctx.wd.W.m + ci))
  have hr_u3 : Runs w p ω (Stmt.assign 18 (t2Ld (.reg 10) (.reg 15))) st2 .normal { st2 with regs := r3 } 5 := by
    have he_a := Expr.eval_add (st := st2) (Expr.eval_reg_of_eq hr10) (Expr.eval_reg_of_eq hr15)
      (by omega : inp.dsHandlesAddr ctx.wd.W.m + ci < 2 ^ w)
    have he_l := Expr.eval_load (st := st2) he_a
    dsimp only [st2] at he_l; rw [hhdl_eq] at he_l
    exact runs_assign_iff.mpr ⟨_, he_l, rfl, rfl, by simp [Expr.size]⟩
  set st3 : State := { st2 with regs := r3 }
  set r4 := Function.update r3 19 hCur
  have hr_u4 : Runs w p ω (Stmt.assign 19 (.reg 11)) st3 .normal { st3 with regs := r4 } 2 :=
    runs_assign_iff.mpr ⟨hCur, Expr.eval_reg_of_eq (by dsimp only [st3, r3]; rw [Function.update_of_ne (by omega)]; exact hr11),
      rfl, rfl, by simp [Expr.size]⟩
  set st4 : State := { st3 with regs := r4 }
  have hDS2_pair := hD.hDS.frame_below (mem' := mem2) hSpec.1
    (fun k hk => by dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
    (fun a ha => by dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
  obtain ⟨body_del, o_del, st_ds, c_del, s', x', L, hp_del, hr_del, hCur_le_o, h_o_le, h_below_ds,
      hs'G, _, _, _, hs'del, hs'Vh, hSeqDS, hLnd, hLVh, hDS_ds, hPhi_ds⟩ :=
    hDS2_pair.1.call_delete (ω := ω) (pos := st4.pos) hSpec hci (le_refl _) (by omega) hb_m hb_ndel
      hcur_w (by omega) hci_b.2.2.2.1 hSpace_w
  rw [hhdl_eq] at hr_del
  set r5 := Function.update r4 11 o_del.value
  have hr_u5 : Runs w p ω (Stmt.call 11 (dsBase + 1) [.reg 18, .reg 16, .reg 11]) st4 .normal
      { st_ds with regs := r5 } (3 + c_del + 1) := by
    have e18 : (Expr.reg 18).eval w st4 = some (st.mem (inp.dsHandlesAddr ctx.wd.W.m + ci)) :=
      Expr.eval_reg_of_eq (by dsimp only [st4, r4]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _)
    have e16 : (Expr.reg 16).eval w st4 = some b :=
      Expr.eval_reg_of_eq (by dsimp only [st4, r4, r3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr16)
    have e11 : (Expr.reg 11).eval w st4 = some hCur :=
      Expr.eval_reg_of_eq (by dsimp only [st4, r4, r3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr11)
    exact runs_call_iff.mpr ⟨_, body_del, o_del, st_ds, c_del, by simp [evalArgs, e18, e16, e11],
      hp_del, hr_del, rfl, rfl, by simp [argsSize, Expr.size]⟩
  set st5 : State := { st_ds with regs := r5 }
  have hs'Valid := (hDS_ds.at_ci ci hci).2.2.2.2.2.2.2.2
  simp only [Function.update_self] at hs'Valid
  have hs'Vh_sub : s'.Vhat ⊆ Finset.range (ctx.wd.comps[ci]'hci).J_sub.n := by
    have := hs'Valid.2.2.2.2.2.2.2.1
    rwa [hs'G, (hD.hDS.at_ci ci hci).2.2.2.2.1, List.getD_eq_getElem _ _ hci, Graph.verts] at this
  have hVh0_sub : (states ci).Vhat ⊆ Finset.range (ctx.wd.comps[ci]'hci).J_sub.n := by
    have := (hD.hDS.at_ci ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rwa [(hD.hDS.at_ci ci hci).2.2.2.2.1, List.getD_eq_getElem _ _ hci, Graph.verts] at this
  have hL_sub : ∀ v ∈ L, v < (ctx.wd.comps[ci]'hci).J_sub.n := fun v hv =>
    Finset.mem_range.mp (hs'Vh_sub (Finset.sdiff_subset (hLVh ▸ List.mem_toFinset.mpr hv)))
  have h_o_hi : o_del.value ≤ Task2Input.maxHeapEnd impl inp := by
    have hsp_le : hCur + impl.pathDS.params.delSpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m ctx.wd.J0_strip.m ≤
        hCur + t2DsOne impl inp.J := Nat.add_le_add_left hci_b.2.1 hCur
    have hcur_le : hCur + t2DsOne impl inp.J ≤ Task2Input.maxHeapEnd impl inp := by
      have hm := Nat.mul_le_mul_right (t2DsOne impl inp.J)
        (show g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1 ≤
          Task2Input.eta1Cap impl inp.J * inp.J.m +
          Task2Input.eta1Cap impl inp.J * inp.J.m + Task1Input.mwCap impl inp.J by
          have hinit_le : g₀.initCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
            rw [hS.hInitC]; exact Nat.mul_le_mul (le_trans hS.hη_bd hη₁_cap) hK
          have hgp_le : g₀.getPathCountJ ≤ Task1Input.mwCap impl inp.J := by
            have : g₀.getPathCountJ ≤ ctx.wd.W.m := by have := hS.hGetC; omega
            exact le_trans this hmW
          have := le_trans hdel_tot1 (Nat.mul_le_mul_right _ (le_trans hS.hη_bd hη₁_cap))
          omega)
      have hsum_add : (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1) * t2DsOne impl inp.J ≤
          Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := by simpa only [Nat.add_mul] using hm
      have h_mhe_eq : Task2Input.maxHeapEnd impl inp =
          Task2Input.staticEndCap impl inp + Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := rfl
      rw [h_mhe_eq]
      calc hCur + t2DsOne impl inp.J
          ≤ stc.dsBaseAddr + (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ) * t2DsOne impl inp.J +
              t2DsOne impl inp.J := Nat.add_le_add_right hD.hHCur_le _
        _ = stc.dsBaseAddr + (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ + 1) * t2DsOne impl inp.J := by
              rw [add_assoc, ← Nat.succ_mul]
        _ ≤ Task2Input.staticEndCap impl inp +
              (Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
               Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
               Task1Input.mwCap impl inp.J * t2DsOne impl inp.J) := Nat.add_le_add h_dsc hsum_add
        _ = _ := by ring
    exact le_trans h_o_le (le_trans hsp_le hcur_le)
  set r6 := Function.update r5 20 L.length
  have hr_u6 : Runs w p ω (Stmt.assign 20 (.load (.reg 19))) st5 .normal { st5 with regs := r6 } 3 := by
    have he19 := Expr.eval_reg_of_eq (w := w) (show st5.regs 19 = hCur by
      dsimp only [st5, r5]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _)
    exact runs_assign_iff.mpr ⟨L.length, by simpa only [st5, hSeqDS.1] using Expr.eval_load (st := st5) he19,
      rfl, rfl, by simp [Expr.size]⟩
  set st6 : State := { st5 with regs := r6 }
  have hvoff_mem : st6.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) = vhatBase ctx.wd ci := by
    dsimp only [st6, st5]; rw [h_below_ds _ (by omega)]
    dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact (hD.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hVho ci hci)
  set r7 := Function.update r6 21 (vhatBase ctx.wd ci)
  have hr_u7 : Runs w p ω (Stmt.assign 21 (t2Ld (.reg 8) (.reg 15))) st6 .normal { st6 with regs := r7 } 5 := by
    have he8 : st6.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length := by
      dsimp only [st6, r6, r5, r4, r3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr8
    have he15 : st6.regs 15 = ci := by
      dsimp only [st6, r6, r5, r4, r3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr15
    have hvoff_w : inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci < 2 ^ w := by omega
    have he_add : (t2Add (.reg 8) (.reg 15)).eval w st6 =
        some (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) :=
      Expr.eval_add (Expr.eval_reg_of_eq he8) (Expr.eval_reg_of_eq he15) hvoff_w
    have he_u7 := Expr.eval_load he_add
    dsimp only [t2Ld]; rw [hvoff_mem] at he_u7
    exact runs_assign_iff.mpr ⟨vhatBase ctx.wd ci, he_u7, rfl, rfl, by simp [Expr.size]⟩
  set st7 : State := { st6 with regs := r7 }
  have hr7_lt : ∀ r ≤ 19, r ≠ 11 → r7 r = r4 r := fun r hr hne => by
    dsimp only [r7, r6, r5]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne hne]
  have hr4_lt : ∀ r ≤ 14, r4 r = st.regs r := fun r hr => by
    dsimp only [r4, r3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  obtain ⟨st8, c_vh, hr_u8, h8_regs, h8_agr, h8_L, h8_ne, hc_vh⟩ :=
    t2Drain_vhat_forRange ctx stc hS hci hD.hDS.h_ge hCur_le_o h_o_hi L hL_sub hLnd st7.mem
      hSeqDS hDS_ds.zero_from r7
      (by rw [hr7_lt 3 (by omega) (by omega), hr4_lt 3 (by omega)]; exact hr3)
      (by rw [hr7_lt 9 (by omega) (by omega), hr4_lt 9 (by omega)]; exact hr9)
      (by rw [hr7_lt 19 (by omega) (by omega)]; dsimp only [r4]; exact Function.update_self _ _ _)
      (by dsimp only [r7, r6]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _)
      (by dsimp only [r7]; exact Function.update_self _ _ _)
      st7.pos ω
  set c_tr := 5 + (10 + (5 + (2 + (3 + c_del + 1 + (3 + (5 + c_vh + 1) + 1) + 1) + 1) + 1) + 1) + 1
  have hr_all : Runs w p ω trueBody st .normal st8 c_tr :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hr_u1,
      runs_seq_iff.mpr (Or.inr ⟨st2, 10, _, hr_u2,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hr_u3,
          runs_seq_iff.mpr (Or.inr ⟨st4, 2, _, hr_u4,
            runs_seq_iff.mpr (Or.inr ⟨st5, 3 + c_del + 1, _, hr_u5,
              runs_seq_iff.mpr (Or.inr ⟨st6, 3, _, hr_u6,
                runs_seq_iff.mpr (Or.inr ⟨st7, 5, c_vh, hr_u7, hr_u8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  set states' := Function.update states ci s'
  set reps' := Function.update reps ci x'
  have hDS8_pair := hDS_ds.frame_below (mem' := st8.mem) hSpec.1
    (fun k hk => by rw [h8_agr _ (by omega)])
    (fun a ha => by rw [h8_agr _ (by omega)])
  have hdel_mono : ∀ k, (states k).deleted ⊆ (states' k).deleted := fun k => by
    by_cases hkc : k = ci
    · subst hkc; simp only [states', Function.update_self, hs'del]; exact Finset.subset_insert _ _
    · simp only [states', Function.update_of_ne hkc]; exact Finset.Subset.refl _
  have hD8 : T2DrainInv ctx stc g₀ memStart drained states' reps' o_del.value (deleteCountJ + 1) st8.mem := by
    refine
      { hAgr := fun a ha7 ha5 hcd hvh hds => ?_
        h5 := by
          rw [h8_agr _ (by omega)]; dsimp only [st7, st6, st5]
          rw [h_below_ds _ (by omega)]; exact Function.update_self _ _ _
        h7 := by
          rw [h8_agr _ (by omega)]; dsimp only [st7, st6, st5]
          rw [h_below_ds _ (by omega)]; dsimp only [mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hD.h7]
        hDelEq := by
          have hmem_ci : ci ∈ Finset.range ctx.wd.comps.length := Finset.mem_range.mpr hci
          rw [← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem_ci]
          have hrest : ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci, (states' k).deleted.card =
              ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci, (states k).deleted.card :=
            Finset.sum_congr rfl fun k hk => by simp [states', Function.update_of_ne (Finset.ne_of_mem_erase hk)]
          rw [hrest]; simp only [states', Function.update_self, hs'del, Finset.card_insert_of_notMem hb_ndel]
          have hprev := hD.hDelEq; rw [← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem_ci] at hprev; omega
        hDS := hDS8_pair.1
        hDelR := fun ci' hci' b' hb' => ?_
        hVhatS := fun ci' hci' y' hy' => ?_
        hDelSub := fun ci' hci' b' hb' => ?_
        hDelMono := fun k => Finset.Subset.trans (hD.hDelMono k) (hdel_mono k)
        hVhMono := fun ci' => by
          by_cases hkc : ci' = ci
          · subst hkc; simp only [states', Function.update_self]; exact Finset.Subset.trans (hD.hVhMono ci') hs'Vh
          · simp only [states', Function.update_of_ne hkc]; exact hD.hVhMono ci'
        hDr_sub := hD.hDr_sub
        hDr_del := fun x hx hxn ci' hci' b' hb' hxb => hdel_mono ci' (hD.hDr_del x hx hxn ci' hci' b' hb' hxb)
        hHCur_le := by
          have h1 : o_del.value ≤ hCur + t2DsOne impl inp.J :=
            le_trans h_o_le (Nat.add_le_add_left hci_b.2.1 hCur)
          have h2 : hCur + t2DsOne impl inp.J ≤ stc.dsBaseAddr +
              (g₀.initCountJ + (deleteCountJ + 1) + g₀.getPathCountJ) * t2DsOne impl inp.J :=
            calc hCur + t2DsOne impl inp.J
                ≤ stc.dsBaseAddr + (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ) * t2DsOne impl inp.J +
                    t2DsOne impl inp.J := Nat.add_le_add_right hD.hHCur_le _
              _ = stc.dsBaseAddr + (g₀.initCountJ + (deleteCountJ + 1) + g₀.getPathCountJ) *
                    t2DsOne impl inp.J := by
                  rw [show g₀.initCountJ + (deleteCountJ + 1) + g₀.getPathCountJ =
                    (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ) + 1 by omega, Nat.succ_mul, add_assoc]
          exact le_trans h1 h2
        hCur_ge := le_trans hD.hCur_ge hCur_le_o }
    · rw [h8_agr a (fun ⟨h1, h2⟩ => hvh ⟨h1, h2⟩)]; dsimp only [st7, st6, st5]
      rw [h_below_ds a hds]; dsimp only [mem2, mem1]
      rw [Function.update_of_ne ha5, Function.update_of_ne (fun h : a = delA => hcd ⟨by omega, by omega⟩)]
      exact hD.hAgr a ha7 ha5 hcd hvh hds
    · have hsum_j : compEdgeBase ctx.wd ci' + b' < inp.J.m := by
        have ha1 := compEdgeBase_add_le hci'
        have ha2 := compEdgeBase_le_sum (wd := ctx.wd) (by omega : ci' + 1 ≤ ctx.wd.comps.length); omega
      have heq_mem : st8.mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length +
          compEdgeBase ctx.wd ci' + b') = mem1 (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length +
          compEdgeBase ctx.wd ci' + b') := by
        rw [h8_agr _ (by omega)]; dsimp only [st7, st6, st5]; rw [h_below_ds _ (by omega)]
        dsimp only [mem2]; exact Function.update_of_ne (by omega) _ _
      rw [heq_mem]
      by_cases hsame : ci' = ci ∧ b' = b
      · rcases hsame with ⟨rfl, rfl⟩
        simp only [states', Function.update_self, hs'del, Finset.mem_insert, true_or, iff_true]
        dsimp only [mem1, delA]
        rw [show inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci' + b' =
          inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + (compEdgeBase ctx.wd ci' + b') by omega,
          Function.update_self]
        exact ⟨le_refl _, rfl⟩
      · have hne : inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci' + b' ≠ delA := by
          intro heq; apply hsame; exact compEdgeBase_inj hci' hci hb' hb_m (by dsimp only [delA] at heq; omega)
        dsimp only [mem1]; rw [Function.update_of_ne hne]; have hold := hD.hDelR ci' hci' b' hb'
        by_cases hkc : ci' = ci
        · subst hkc; have hbb : b' ≠ b := fun he => hsame ⟨rfl, he⟩
          simpa only [states', Function.update_self, hs'del, Finset.mem_insert, hbb, false_or] using hold
        · simpa only [states', Function.update_of_ne hkc] using hold
    · have hvh_lt : vhatBase ctx.wd ci' + y' < 2 * inp.J.m := by
        have ha1 := vhatBase_add_le hci'
        have ha2 := vhatBase_le_sum (wd := ctx.wd) (by omega : ci' + 1 ≤ ctx.wd.comps.length); omega
      by_cases hkc : ci' = ci
      · subst hkc; simp only [states', Function.update_self]
        by_cases hyL : y' ∈ L
        · have hy_s' : y' ∈ s'.Vhat := (Finset.mem_sdiff.mp (hLVh ▸ List.mem_toFinset.mpr hyL)).1
          rw [h8_L y' hyL]; exact ⟨le_refl _, by simp [hy_s']⟩
        · have heq : st8.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci' + y') =
              st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci' + y') := by
            rw [h8_ne (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci' + y')
              fun v hv he => hyL (Nat.add_left_cancel he ▸ hv)]
            dsimp only [st7, st6, st5]; rw [h_below_ds _ (by omega)]
            dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          rw [heq]; have hold := hD.hVhatS ci' hci' y' hy'
          have hy_iff : y' ∈ s'.Vhat ↔ y' ∈ (states ci').Vhat :=
            ⟨fun hys => by by_contra hno; exact hyL (List.mem_toFinset.mp (hLVh.symm ▸ Finset.mem_sdiff.mpr ⟨hys, hno⟩)),
             fun hys => hs'Vh hys⟩
          rwa [hy_iff]
      · have heq : st8.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci' + y') =
            st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci' + y') := by
          rw [h8_ne _ fun v hv he => hkc (vhatBase_inj hci' hci hy' (hL_sub v hv) (by omega)).1]
          dsimp only [st7, st6, st5]; rw [h_below_ds _ (by omega)]
          dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        rw [heq]; simp only [states', Function.update_of_ne hkc]; exact hD.hVhatS ci' hci' y' hy'
    · by_cases hkc : ci' = ci
      · subst hkc; simp only [states', Function.update_self, hs'del, Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact ⟨hb_m, g₀.queue[i], (hS.hQ_sub _ (List.getElem_mem hi)).2.1, hx_in⟩
        · exact hD.hDelSub ci' hci' b' hb'
      · simp only [states', Function.update_of_ne hkc] at hb'; exact hD.hDelSub ci' hci' b' hb'
  have hnext_chain' : IncChainBound st8.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd next rest :=
    hnext_chain.mono fun a ha1 ha2 => by
      rw [hD8.hAgr a (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact (hD.hAgr a (by omega) (by omega) (by omega) (by omega) (by omega)).symm
  have hundel_step := drain_undelRem_step ctx states hci hb_m hb_ndel s' hs'del fun k hk => by
    intro z hz; exact Finset.mem_range.mpr (hD.hDelSub k hk z hz).1
  have hvhat_step := drain_vhatRem_step ctx states hci s' hVh0_sub hs'Vh_sub hs'Vh hLnd hLVh
  refine ⟨st8, _, states', reps', o_del.value, hr_all,
    fun r hr hne => by
      rw [h8_regs r (by omega), hr7_lt r (by omega) hne]
      dsimp only [st4, r4, r3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
    by
      rw [h8_regs 11 (by omega)]; dsimp only [r7, r6, r5]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _,
    hdel_mono, hD8, by simp [states', Function.update_self, hs'del], hnext_chain', ?_⟩
  dsimp only [t2RoundPhi] at ⊢ hPhi_ds hDS8_pair hDS2_pair
  dsimp only [states', reps'] at hundel_step hvhat_step ⊢
  rw [hDS8_pair.2, hundel_step, hvhat_step, Nat.add_mul _ 1 kDel, Nat.one_mul, Nat.add_mul _ L.length 32]
  have hkdel_eq : ⌈impl.pathDS.params.K_del *
      impl.pathDS.params.γ_query ((ctx.wInp.prep.phiNum_dec : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ))
        ctx.wd.J0_strip.m⌉₊ + 100 = kDel := rfl
  have hL24 : L.length * 24 ≤ L.length * 32 := Nat.mul_le_mul_left _ (by omega)
  rw [← hkdel_eq]
  omega

end MinCostFlow.Spanner
