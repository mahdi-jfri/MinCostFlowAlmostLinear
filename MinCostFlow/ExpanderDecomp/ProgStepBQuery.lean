module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBLayout
public import MinCostFlow.ExpanderDecomp.ProgStepBQueryDisp

import Mathlib.Tactic.Linarith

/-!
# Step B Per-Round Sub-Core Query Loop Verification (`ProgStepBQuery`)

Proves `sbQueryLoop_run` for `sbQueryLoopStmt bSubCore`: iterates over all `nBlocks` blocks,
skipping inactive blocks, and for each active block `j` relabels its witness graph `W_j` onto
`Finset.range b` (`W'_j.n = b ≤ 2048 * LParam M * (NOf M r) ^ r`), calls `bSubCore` via
`stepBSubCoreContract`, lifts the returned `CoreOutAt` back to `blockSet vs b j`, and dispatches
via `sbQueryOneBlock_afterCall`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma runs_seq_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st1 st2 : State} {c1 c2 : ℕ}
    (h1 : Runs w p ω s st .normal st1 c1) (h2 : Runs w p ω t st1 .normal st2 c2) :
    Runs w p ω (.seq s t) st .normal st2 (c1 + c2 + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩)

private lemma runs_seq_n_mp {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st2 : State} {c : ℕ} (h : Runs w p ω (.seq s t) st .normal st2 c) :
    ∃ st1 c1 c2, Runs w p ω s st .normal st1 c1 ∧ Runs w p ω t st1 .normal st2 c2 ∧
      c = c1 + c2 + 1 := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hc, _⟩ | h2
  · cases hc
  · exact h2

private lemma runs_cond_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {v c1 : ℕ} (he : e.eval w st = some v) (hv : v ≠ 0)
    (hs : Runs w p ω s st .normal st' c1) :
    Runs w p ω (.cond e s t) st .normal st' (e.size + c1 + 1) :=
  runs_cond_iff.mpr ⟨v, c1, he, by simp only [hv, ↓reduceIte]; exact hs, rfl⟩

private lemma runs_loop_f {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st1 st2 : State} {v c1 c2 : ℕ} (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st1 c1) (h2 : Runs w p ω (.loop e body) st1 .normal st2 c2) :
    Runs w p ω (.loop e body) st .normal st2 (e.size + c1 + c2 + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st1, c1, c2, he, hv, h1, h2, rfl⟩))

private lemma runs_assign_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {r v : ℕ} {e : Expr}
    {st : State} (he : e.eval w st = some v) :
    Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v } (e.size + 1) :=
  runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

/-- Helper: every edge of `witnessEdges (bst.rounds j) (bst.numRounds j)` has both endpoints in
`blockSet vs b j`. -/
private lemma witnessEdges_mem_blockSet {cfg : CoreParams} {q : ℕ} {G : Graph} {X : Finset ℕ}
    {vs : List ℕ} {b nBlocks z tRound j : ℕ} {bst : BlockGameState}
    (hmod : SbModelInv cfg q G X vs b nBlocks z tRound bst) (hj : j < nBlocks) :
    ∀ e ∈ witnessEdges (bst.rounds j) (bst.numRounds j),
      e.1 ∈ blockSet vs b j ∧ e.2 ∈ blockSet vs b j := by
  have hgen : ∀ m, (∀ idx < m, IsPerfectMatchingOn (blockSet vs b j) (bst.rounds j idx)) →
      ∀ e ∈ witnessEdges (bst.rounds j) m, e.1 ∈ blockSet vs b j ∧ e.2 ∈ blockSet vs b j := by
    intro m hm e he
    induction m with
    | zero => simp [witnessEdges] at he
    | succ m ih =>
      rw [witnessEdges] at he
      rcases List.mem_append.mp he with h1 | h2
      · exact ih (fun idx hidx => hm idx (Nat.lt_succ_of_lt hidx)) h1
      · exact (hm m (Nat.lt_succ_self m)).1 e h2
  exact hgen (bst.numRounds j) (hmod.rounds_pm j hj)

/-- Execute `r33 := q - 1 ;; bSubCore ;; sbLiftOutStmt` on the relabeled witness graph `W'_j`. -/
private lemma sbQueryOneBlock_subAndLift {cfg : ParamConfig} {M r q w bSubCore Sprev Tprev : ℕ}
    {n b blkA rangeB_A wRelA pA locA subOutA h12 : ℕ}
    {p : Program} {B_l : List ℕ} {B_j : Finset ℕ} {es : List (ℕ × ℕ)} {stB : State} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hB_len : B_l.length = b) (hB_nd : B_l.Nodup) (hB_fin : B_l.toFinset = B_j)
    (hB_B : ListAt stB.mem blkA B_l) (hes_B : ∀ e ∈ es, e.1 ∈ B_j ∧ e.2 ∈ B_j) (hb_le_n : b ≤ n)
    (hcp_B : CoreParamsAt stB.mem pA (coreParamsOf cfg M r) r)
    (hW'_atB : GraphAt stB.mem wRelA (relabelGraph B_l es))
    (hW'_valid : (relabelGraph B_l es).IsValid)
    (hW'_n_bound : (relabelGraph B_l es).n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hRange_B : VertsAt stB.mem rangeB_A b (Finset.range b))
    (hW'_loop : ∀ e ∈ (relabelGraph B_l es).inside (Finset.range b), e.1 ≠ e.2)
    (hb_le : b ≤ (coreParamsOf cfg M r).N ^ (q - 1))
    (hW'_deg : ∀ v ∈ Finset.range b, (relabelGraph B_l es).degIn (Finset.range b) v ≤ (coreParamsOf cfg M r).Δ)
    (hW'_m : (relabelGraph B_l es).m ≤ (coreParamsOf cfg M r).Δ * b)
    (hlocB : ∀ u < n, stB.mem (locA + u) = 0)
    (hzfB : ZeroFrom stB.mem h12)
    (hgeom : wRelA + 2 + 2 * es.length ≤ h12 ∧ rangeB_A + b ≤ h12 ∧
      pA + coreParamsSize r ≤ h12 ∧ locA + n ≤ h12 ∧ subOutA + 2 + b ≤ h12 ∧
      locA + n ≤ wRelA ∧ locA + n ≤ rangeB_A ∧
      DisjointRange locA n pA (coreParamsSize r) ∧ locA + n ≤ subOutA ∧
      wRelA + 2 + 2 * es.length ≤ subOutA ∧ rangeB_A + b ≤ subOutA ∧
      pA + coreParamsSize r ≤ subOutA ∧ blkA + b ≤ subOutA ∧
      h12 + Sprev < 2 ^ w ∧ q < 2 ^ w ∧ 16 < 2 ^ w)
    (hregsB : stB.regs 0 = q ∧ stB.regs 4 = b ∧ stB.regs 7 = pA ∧ stB.regs 8 = locA ∧
      stB.regs 12 = h12 ∧ stB.regs 28 = blkA ∧ stB.regs 30 = subOutA ∧
      stB.regs 31 = rangeB_A ∧ stB.regs 32 = wRelA) :
    ∃ (res_j : CoreResult) (st1 : State) (c2 : ℕ),
      Runs w p ω (seqStmts [
        .assign 33 (.bin .sub (.reg 0) (.const 1)),
        .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
        sbLiftOutStmt]) stB .normal st1 c2 ∧
      CoreOutAt st1.mem subOutA res_j ∧
      CoreSpec (coreParamsOf cfg M r) (q - 1) (Graph.mk n es) B_j res_j ∧
      h12 ≤ st1.regs 12 ∧ st1.regs 12 ≤ h12 + Sprev ∧
      ZeroFrom st1.mem (st1.regs 12) ∧
      (∀ u < n, st1.mem (locA + u) = 0) ∧
      (∀ a < h12, (a < subOutA ∨ subOutA + 2 + b ≤ a) → st1.mem a = stB.mem a) ∧
      (∀ r < 33, r ≠ 12 → st1.regs r = stB.regs r) ∧
      c2 ≤ Tprev + 45 * b + 60 := by
  set W'_j := relabelGraph B_l es
  have hW'_n : W'_j.n = b := hB_len
  have hW'_m_eq : W'_j.m = es.length := relabelGraph_m B_l es
  rcases hgeom with ⟨hg1, hg2, hg3, hg4, hg5, hg6, hg7, hd_lp, hg8, hg9, hg10, hg11, hg12, h12w, hqw, hw16⟩
  rcases hregsB with ⟨hr0, hr4, hr7, hr8, hr12, hr28, hr30, hr31, hr32⟩
  have hd_lp' : DisjointRange locA W'_j.n pA (coreParamsSize r) :=
    Or.elim hd_lp (fun h => Or.inl (by rw [hW'_n]; omega)) Or.inr
  have hPreSub : (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev).pre
      [q - 1, wRelA, b, rangeB_A, pA, locA, subOutA, h12] stB.mem :=
    ⟨wRelA, b, rangeB_A, pA, locA, subOutA, h12, W'_j, Finset.range b,
      rfl, ha0, ha, hrl, by omega, hcp_B, hW'_atB, hW'_valid, hW'_n_bound, hRange_B,
      hW'_n.symm ▸ Finset.Subset.refl _, hW'_loop, hb_le, hW'_deg, hW'_m,
      fun u hu => hlocB u (lt_of_lt_of_le (hW'_n ▸ hu) hb_le_n),
      by rw [hW'_m_eq]; exact hg1, hg2, hg3, by rw [hW'_n]; omega, hg5,
      Or.inl (by rw [hW'_n]; omega), Or.inl (by rw [hW'_n]; omega), hd_lp',
      Or.inl (by rw [hW'_n]; omega),
      Or.inr (by rw [hW'_m_eq]; omega), Or.inr hg10, Or.inr hg11, hzfB, h12w⟩
  have hrun : ∃ o st1 c2,
      Runs w p ω (seqStmts [
        .assign 33 (.bin .sub (.reg 0) (.const 1)),
        .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
        sbLiftOutStmt]) stB o st1 c2 ∧
      (normalPost fun st1 =>
        (∃ res_j, CoreOutAt st1.mem subOutA res_j ∧ CoreSpec (coreParamsOf cfg M r) (q - 1) (Graph.mk n es) B_j res_j) ∧
        h12 ≤ st1.regs 12 ∧ st1.regs 12 ≤ h12 + Sprev ∧
        ZeroFrom st1.mem (st1.regs 12) ∧
        (∀ u < n, st1.mem (locA + u) = 0) ∧
        (∀ a < h12, (a < subOutA ∨ subOutA + 2 + b ≤ a) → st1.mem a = stB.mem a) ∧
        (∀ r < 33, r ≠ 12 → st1.regs r = stB.regs r)) o st1 ∧
      c2 ≤ Tprev + 45 * b + 60 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := q - 1)
      (Expr.eval_sub (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by omega)) hqw) ?_
    have hEvArgs : evalArgs w { mem := stB.mem, regs := Function.update stB.regs 33 (q - 1), pos := stB.pos }
        [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12] =
        some [q - 1, wRelA, b, rangeB_A, pA, locA, subOutA, h12] := by
      simp only [evalArgs, Expr.eval, Function.update_self,
        Function.update_of_ne (by decide : (32 : ℕ) ≠ 33), hr32,
        Function.update_of_ne (by decide : (4 : ℕ) ≠ 33), hr4,
        Function.update_of_ne (by decide : (31 : ℕ) ≠ 33), hr31,
        Function.update_of_ne (by decide : (7 : ℕ) ≠ 33), hr7,
        Function.update_of_ne (by decide : (8 : ℕ) ≠ 33), hr8,
        Function.update_of_ne (by decide : (30 : ℕ) ≠ 33), hr30,
        Function.update_of_ne (by decide : (12 : ℕ) ≠ 33), hr12]
    have hWords : ∀ v ∈ ([q - 1, wRelA, b, rangeB_A, pA, locA, subOutA, h12] : List ℕ), v < 2 ^ w := by
      intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine runs_seq_call_le hSub hEvArgs hWords hPreSub ?_
    intro v memC posC hpostC
    have hpC := hpostC wRelA b rangeB_A pA locA subOutA h12 W'_j (Finset.range b)
      rfl ha0 ha hrl (by omega) hcp_B hW'_atB hW'_valid hW'_n_bound hRange_B
      (hW'_n.symm ▸ Finset.Subset.refl _) hW'_loop hb_le hW'_deg hW'_m
      (fun u hu => hlocB u (lt_of_lt_of_le (hW'_n ▸ hu) hb_le_n))
      (by rw [hW'_m_eq]; exact hg1) hg2 hg3 (by rw [hW'_n]; omega) hg5
      (Or.inl (by rw [hW'_n]; omega)) (Or.inl (by rw [hW'_n]; omega)) hd_lp'
      (Or.inl (by rw [hW'_n]; omega))
      (Or.inr (by rw [hW'_m_eq]; omega)) (Or.inr hg10) (Or.inr hg11) hzfB h12w
    rcases hpC with ⟨⟨res', hOut', hSpec'⟩, hv_ge, hv_le, hzfC, _, hfrC⟩
    have hlocC : ∀ u < n, memC (locA + u) = 0 := fun u hu => by
      rw [hfrC (locA + u) (by omega) (Or.inl (by omega))]; exact hlocB u hu
    have hB_C : ListAt memC blkA B_l := fun idx hidx => by
      rw [hfrC _ (by omega) (Or.inl (by omega))]; exact hB_B idx hidx
    have hstC_props :
        let stC : State := State.mk memC (Function.update (Function.update stB.regs 33 (q - 1)) 12 v) posC
        stC.mem = memC ∧ stC.regs 12 = v ∧ (∀ r < 33, r ≠ 12 → stC.regs r = stB.regs r) ∧
        stC.regs 28 = blkA ∧ stC.regs 30 = subOutA :=
      ⟨rfl, by simp, fun r hr hne => by dsimp only; rw [Function.update_of_ne hne, Function.update_of_ne (by omega)],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr28],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30]⟩
    generalize (State.mk memC (Function.update (Function.update stB.regs 33 (q - 1)) 12 v) posC) = stC at hstC_props ⊢
    rcases hstC_props with ⟨hstC_mem, hstC_12, hstC_lt33, hstC_28, hstC_30⟩
    have hcost_sub : (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev).cost
        [q - 1, wRelA, b, rangeB_A, pA, locA, subOutA, h12] stB.mem = Tprev := rfl
    refine runs_triple_le
      (sbLiftOut_triple (w := w) (b := b) (blkA := blkA) (subOutA := subOutA)
        (p := p) (mem := memC) (verts := B_l) (res' := res') (st₀ := stC)
        hB_len hB_nd hB_C hOut' (by cases res' <;> exact hSpec'.1)
        (Or.inr hg12) (by omega) (by omega) hw16 hstC_28 hstC_30 hstC_mem) rfl ?_
      (by rw [hcost_sub]; simp only [argsSize, Expr.size]; omega)
    rintro (_ | _) stD hD
    · rcases hD with ⟨hlt33_D, _, hfrD, hOut_lifted⟩
      have hr12_D : stD.regs 12 = v := (hlt33_D 12 (by decide)).trans hstC_12
      refine ⟨⟨liftCoreResult B_l res', hOut_lifted, coreSpec_of_relabel hB_nd hB_len hB_fin hes_B hSpec'⟩,
        by rw [hr12_D]; exact hv_ge, by rw [hr12_D]; exact hv_le,
        fun a ha => by rw [hr12_D] at ha; rw [hfrD a (Or.inr (by omega))]; exact hzfC a ha,
        fun u hu => by rw [hfrD (locA + u) (Or.inl (by omega))]; exact hlocC u hu,
        fun a ha hout => by rw [hfrD a (by omega), hfrC a ha hout],
        fun r hr hne => (hlt33_D r hr).trans (hstC_lt33 r hr hne)⟩
    · exact hD
  rcases hrun with ⟨o, st1, c2, hr2, hp2, hc2⟩
  cases o with
  | returned _ => exact False.elim hp2
  | normal =>
    rcases hp2 with ⟨⟨res_j, hOut_j, hSpec_j⟩, h12ge, h12le, hzf1, hloc1, hfr1, hlt33⟩
    exact ⟨res_j, st1, c2, hr2, hOut_j, hSpec_j, h12ge, h12le, hzf1, hloc1, hfr1, hlt33, hc2⟩

/-- Execute the relabel + `bSubCore` + lift prefix of an active block `j < nBlocks`. -/
private lemma sbQueryOneBlock_callPrefix {cfg : ParamConfig} {M r q w bSubCore Sprev Tprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 tRound j : ℕ}
    {p : Program} {memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {st : State} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt memStart pA (coreParamsOf cfg M r) r)
    (hX_at : VertsAt memStart xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hb_le : b ≤ (coreParamsOf cfg M r).N ^ (q - 1))
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (ht_le : tRound ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z tRound bst)
    (hpers_w : ∀ i < nBlocks,
      let ps := sbPersist h0 k b nBlocks (LParam M)
      GraphAt memStart (ps.wBaseA + i * ps.wStride)
        (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))))
    (hrangeB_at : ListAt memStart (sbPersist h0 k b nBlocks (LParam M)).rangeB_A (List.range b))
    (hcur_lay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ cutRecsA ∧
      pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧
      hSub0 = tmpA + 4 * b + 2 + b ∧
      xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧ locA + G.n ≤ h0 ∧
      DisjointRange locA G.n xA k ∧ DisjointRange locA G.n pA (coreParamsSize r) ∧
      hSub0 + nBlocks * Sprev < 2 ^ w ∧ 16 < 2 ^ w)
    (hj_lt : j < nBlocks)
    (hInv : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st) :
    ∃ (res_j : CoreResult) (st1 : State) (c1 : ℕ),
      Runs w p ω (seqStmts [
        .assign 28 (.bin .add (.reg 3) (.bin .mul (.reg 27) (.reg 4))),
        .assign 29 (.bin .add (.reg 20) (.bin .mul (.reg 27) (.reg 16))),
        .assign 30 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 4))),
        .assign 31 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
        .assign 32 (.bin .add (.reg 31) (.reg 4)),
        sbRelabelGraphStmt,
        .assign 33 (.bin .sub (.reg 0) (.const 1)),
        .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
        sbLiftOutStmt])
        st .normal st1 c1 ∧
      CoreOutAt st1.mem (tmpA + 4 * b) res_j ∧
      CoreSpec (coreParamsOf cfg M r) (q - 1)
        (Graph.mk G.n (witnessEdges (bst.rounds j) (bst.numRounds j)))
        (blockSet (X.sort (· ≤ ·)) b j) res_j ∧
      st.regs 12 ≤ st1.regs 12 ∧ st1.regs 12 ≤ st.regs 12 + Sprev ∧
      ZeroFrom st1.mem (st1.regs 12) ∧ (∀ u < G.n, st1.mem (locA + u) = 0) ∧
      (∀ a < st.regs 12, (a < (sbPersist h0 k b nBlocks (LParam M)).wRelA ∨
          (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ a) →
        (a < tmpA + 4 * b ∨ tmpA + 4 * b + 2 + b ≤ a) → st1.mem a = st.mem a) ∧
      ((∀ r < 28, r ≠ 12 → st1.regs r = st.regs r) ∧
        st1.regs 28 = xA + j * b ∧
        st1.regs 29 = (sbPersist h0 k b nBlocks (LParam M)).wBaseA + j * (sbPersist h0 k b nBlocks (LParam M)).wStride ∧
        st1.regs 30 = tmpA + 4 * b) ∧
      c1 ≤ Tprev + 1720 * b * LParam M + 120 * b + 200 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set vs := X.sort (· ≤ ·)
  set cp := coreParamsOf cfg M r
  set es := witnessEdges (bst.rounds j) (bst.numRounds j)
  set W_j := Graph.mk G.n es
  set B_j := blockSet vs b j
  set B_l := B_j.sort (· ≤ ·)
  set W'_j := relabelGraph B_l es
  rcases hcur_lay with ⟨hP_le, hpairs_eq, htmp_eq, hhSub_eq, hx_le, hp_le, hloc_le,
    hd_loc_x, hd_loc_p, hmem_w, hw16⟩
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hjb_le : j * b + b ≤ nBlocks * b := by
    have : (j + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); linarith
  have hjw_le : j * ps.wStride + ps.wStride ≤ nBlocks * ps.wStride := by
    have : (j + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right ps.wStride (by omega); linarith
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hW_pre := sbModelInv_block_pre hcfg hX_sub (Finset.sort_nodup X (· ≤ ·))
    (by ext u; simp) hb_le (by show tRound ≤ 49 * LParam M + 1; omega)
    (hnb_eq ▸ hmod) (hnb_eq ▸ hj_lt)
  have hWm_eq : es.length = bst.numRounds j * (b / 2) := hW_pre.2.2.2.2.2.2.1
  have hnr_le : bst.numRounds j ≤ 49 * LParam M := (hmod.numRounds_le j hj_lt).trans ht_le
  have hWlen_le : 2 + 2 * es.length ≤ ps.wStride := by
    have h1 : bst.numRounds j * (b / 2) ≤ (49 * LParam M + 1) * (b / 2) :=
      Nat.mul_le_mul_right (b / 2) (by omega)
    have h2 : ps.wStride = 2 + 2 * ((49 * LParam M + 1) * (b / 2)) := by dsimp only [ps, sbPersist]; ring
    omega
  have hWm_bL : 70 * es.length ≤ 1720 * b * LParam M := by
    have h1 : bst.numRounds j * (b / 2) ≤ (49 * LParam M) * (b / 2) := Nat.mul_le_mul_right _ hnr_le
    have h2 : 70 * ((49 * LParam M) * (b / 2)) = 35 * 49 * (2 * (b / 2)) * LParam M := by ring
    have h3 : 2 * (b / 2) ≤ b := Nat.mul_div_le b 2
    have h4 : 35 * 49 * (2 * (b / 2)) * LParam M ≤ 35 * 49 * b * LParam M := by
      have := Nat.mul_le_mul_right (LParam M) (Nat.mul_le_mul_left (35 * 49) h3); linarith
    have h5 : 35 * 49 * b * LParam M ≤ 1720 * b * LParam M := by
      have : 35 * 49 ≤ 1720 := by decide
      have := Nat.mul_le_mul_right (LParam M) (Nat.mul_le_mul_right b this); linarith
    omega
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  have hfr_lo : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) → st.mem a = memStart a := fun a ha hloc => by
    have hfp := hInv.frame_persist
    dsimp only at hfp; rw [hps_id] at hfp
    exact hfp a (by omega) hloc (Or.inl (by omega))
  have hB0 : VertsAt memStart (xA + j * b) b B_j := vertsAt_blockSet hX_at (by rw [← hnb_eq]; exact hj_lt)
  have hB_len : B_l.length = b := by rw [Finset.length_sort, ← hB0.1]
  have hB_nd : B_l.Nodup := Finset.sort_nodup B_j (· ≤ ·)
  have hB_fin : B_l.toFinset = B_j := by ext u; simp [B_l]
  have hB_sub : ∀ u ∈ B_l, u < G.n := fun u hu =>
    Finset.mem_range.mp (hW_pre.1 (by dsimp only [B_j] at hB_fin; rw [← hB_fin]; exact List.mem_toFinset.mpr hu))
  have hb_le_Gn : b ≤ G.n := by
    have := Finset.card_le_card hW_pre.1; rw [Finset.card_range, hW_pre.2.2.2.1] at this; exact this
  have hB_st : ListAt st.mem (xA + j * b) B_l := fun idx hidx => by
    rw [hfr_lo _ (by omega) (by rcases hd_loc_x with h | h <;> [right; left] <;> omega)]
    exact hB0.2 idx hidx
  have hW_st : GraphAt st.mem (ps.wBaseA + j * ps.wStride) W_j := by
    have hfw := hInv.frame_w; rw [hps_id] at hfw
    have hW0 := hpers_w j hj_lt; dsimp only at hW0
    rw [graphAt_mk_iff] at hW0 ⊢
    exact ⟨(hfw _ (by omega) (by omega)).trans hW0.1,
      (hfw _ (by omega) (by omega)).trans hW0.2.1,
      fun idx hidx => ⟨(hfw _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).1,
        (hfw _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).2⟩⟩
  have hes_B : ∀ e ∈ es, e.1 ∈ B_j ∧ e.2 ∈ B_j := witnessEdges_mem_blockSet hmod hj_lt
  have hes_Bl : ∀ e ∈ es, e.1 ∈ B_l.toFinset ∧ e.2 ∈ B_l.toFinset := by simpa only [hB_fin] using hes_B
  have hW'_n : W'_j.n = b := hB_len
  have hW'_n_bound : W'_j.n ≤ 2048 * LParam M * (NOf M r) ^ r := by
    rw [hW'_n]
    have hN1 : 1 ≤ NOf M r := by have := four_le_NOf M r; omega
    have hL1 : 1 ≤ LParam M := hcfg.hL
    have h1 : b ≤ (NOf M r) ^ r := le_trans hb_le (Nat.pow_le_pow_right hN1 (by omega))
    have h2 : 1 ≤ 2048 * LParam M := by omega
    exact le_trans h1 (Nat.le_mul_of_pos_left _ h2)
  have hW'_valid : W'_j.IsValid := relabelGraph_isValid hes_Bl
  have hW'_loop : ∀ e ∈ W'_j.inside (Finset.range b), e.1 ≠ e.2 :=
    relabelGraph_loopless hB_nd hB_len hes_Bl (by simpa only [hB_fin] using hW_pre.2.2.1)
  have hW'_deg : ∀ v ∈ Finset.range b, W'_j.degIn (Finset.range b) v ≤ cp.Δ := fun v hv => by
    have hv' : v < B_l.length := hB_len.symm ▸ Finset.mem_range.mp hv
    rw [← hB_len, relabelGraph_degIn (n := G.n) hB_nd hes_Bl (Finset.Subset.refl _) hv',
      image_range_getD, hB_fin]
    exact hW_pre.2.2.2.2.2.1 _ (by
      dsimp only [B_j] at hB_fin; rw [← hB_fin]
      exact List.mem_toFinset.mpr (by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv', Option.getD_some]
        exact List.getElem_mem hv'))
  have hW'_m : W'_j.m ≤ cp.Δ * b := by rw [relabelGraph_m]; exact hW_pre.2.2.2.2.2.2.2
  have hq_lt_w : q < 2 ^ w := by unfold coreParamsSize at hp_le; omega
  have hrun1 : ∃ o stB cA,
      Runs w p ω (seqStmts [
        .assign 28 (.bin .add (.reg 3) (.bin .mul (.reg 27) (.reg 4))),
        .assign 29 (.bin .add (.reg 20) (.bin .mul (.reg 27) (.reg 16))),
        .assign 30 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 4))),
        .assign 31 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
        .assign 32 (.bin .add (.reg 31) (.reg 4)),
        sbRelabelGraphStmt]) st o stB cA ∧
      (normalPost fun stB =>
        (∀ r < 28, stB.regs r = st.regs r) ∧
        stB.regs 28 = xA + j * b ∧ stB.regs 29 = ps.wBaseA + j * ps.wStride ∧
        stB.regs 30 = tmpA + 4 * b ∧ stB.regs 31 = ps.rangeB_A ∧ stB.regs 32 = ps.wRelA ∧
        (∀ u < G.n, stB.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + G.n ≤ a) → (a < ps.wRelA ∨ ps.wRelA + 2 + 2 * es.length ≤ a) →
          stB.mem a = st.mem a) ∧
        GraphAt stB.mem ps.wRelA W'_j) o stB ∧
      cA ≤ 1720 * b * LParam M + 75 * b + 135 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := xA + j * b)
      (Expr.eval_add (Expr.eval_reg_of_eq hInv.args.r3)
        (Expr.eval_mul (Expr.eval_reg_of_eq hInv.r27) (Expr.eval_reg_of_eq hInv.args.r4) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.wBaseA + j * ps.wStride)
      (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hInv.args.r20]))
        (Expr.eval_mul (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hInv.r27]))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hInv.args.r16])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := tmpA + 4 * b)
      (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.r24]))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r4])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.rangeB_A)
      (by have heq : ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A := by omega
          exact heq ▸ Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r20]))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r5]))
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r16])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.wRelA)
      (by have heq : ps.rangeB_A + b = ps.wRelA := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r4])) (by omega)) ?_
    have hstA_props :
        let stA : State :=
          State.mk st.mem (Function.update (Function.update (Function.update (Function.update (Function.update st.regs
            28 (xA + j * b)) 29 (ps.wBaseA + j * ps.wStride)) 30 (tmpA + 4 * b)) 31 ps.rangeB_A) 32 ps.wRelA) st.pos
        stA.mem = st.mem ∧ (∀ r < 28, stA.regs r = st.regs r) ∧
        stA.regs 28 = xA + j * b ∧ stA.regs 29 = ps.wBaseA + j * ps.wStride ∧
        stA.regs 30 = tmpA + 4 * b ∧ stA.regs 31 = ps.rangeB_A ∧ stA.regs 32 = ps.wRelA := by
      refine ⟨rfl, fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        by simp, by simp, by simp, by simp, by simp⟩
    generalize (State.mk st.mem (Function.update (Function.update (Function.update (Function.update (Function.update st.regs
      28 (xA + j * b)) 29 (ps.wBaseA + j * ps.wStride)) 30 (tmpA + 4 * b)) 31 ps.rangeB_A) 32 ps.wRelA) st.pos) = stA at hstA_props ⊢
    rcases hstA_props with ⟨hstA_mem, hstA_lt28, hstA_28, hstA_29, hstA_30, hstA_31, hstA_32⟩
    refine runs_triple_le
      (sbRelabelGraph_triple (w := w) (n := G.n) (b := b) (blkA := xA + j * b)
        (wAddr := ps.wBaseA + j * ps.wStride) (wRelA := ps.wRelA) (locA := locA)
        (p := p) (mem := st.mem) (verts := B_l) (es := es) (st₀ := stA)
        hB_len hB_nd hB_st hB_sub hW_st hes_Bl hInv.loc0
        (by rcases hd_loc_x with h | h <;> [left; right] <;> omega)
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (by omega) (by omega) (by omega) (by omega) hw16
        ((hstA_lt28 4 (by decide)).trans hInv.args.r4)
        ((hstA_lt28 8 (by decide)).trans hInv.args.r8)
        hstA_28 hstA_29 hstA_32 hstA_mem) rfl ?_ (by simp only [Expr.size]; omega)
    rintro (_ | _) stB hB
    · rcases hB with ⟨hlt33_B, _, hlocB, hfrB, hW'_atB⟩
      exact ⟨fun r hr => (hlt33_B r (by omega)).trans (hstA_lt28 r hr),
        (hlt33_B 28 (by decide)).trans hstA_28, (hlt33_B 29 (by decide)).trans hstA_29,
        (hlt33_B 30 (by decide)).trans hstA_30, (hlt33_B 31 (by decide)).trans hstA_31,
        (hlt33_B 32 (by decide)).trans hstA_32, hlocB, hfrB, hW'_atB⟩
    · exact hB
  rcases hrun1 with ⟨o, stB, cA, hrA, hpA, hcA⟩
  cases o with
  | returned _ => exact False.elim hpA
  | normal =>
    rcases hpA with ⟨hlt28_B, hr28_B, hr29_B, hr30_B, hr31_B, hr32_B, hlocB, hfrB, hW'_atB⟩
    have hfrB_lo : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) → stB.mem a = memStart a := fun a ha hloc =>
      (hfrB a hloc (Or.inl (by omega))).trans (hfr_lo a ha hloc)
    have hcp_B : CoreParamsAt stB.mem pA cp r := by
      have hm : ∀ a, pA ≤ a → a < pA + coreParamsSize r → stB.mem a = memStart a := fun a h1 h2 =>
        hfrB_lo a (by omega) (by rcases hd_loc_p with h | h <;> [right; left] <;> omega)
      refine ⟨(hm pA (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.1,
        (hm (pA + 1) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.1,
        (hm (pA + 2) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.1,
        (hm (pA + 3) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.2.1,
        fun i hi => (hm (pA + 4 + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.1 i hi),
        fun i hi => (hm (pA + 5 + r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.1 i hi),
        fun i hi => (hm (pA + 6 + 2 * r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.2 i hi)⟩
    have hRange_B : VertsAt stB.mem ps.rangeB_A b (Finset.range b) := by
      refine ⟨by simp, ?_⟩
      rw [sort_range_eq_list_range]
      intro idx hidx
      simp only [List.length_range] at hidx
      have hfw := hInv.frame_w; rw [hps_id] at hfw
      rw [hfrB _ (Or.inr (by omega)) (Or.inl (by omega)), hfw _ (by omega) (by omega)]
      exact hrangeB_at idx (by simpa using hidx)
    have hB_B : ListAt stB.mem (xA + j * b) B_l := fun idx hidx => by
      rw [hfrB _ (by rcases hd_loc_x with h | h <;> [right; left] <;> omega) (Or.inl (by omega))]
      exact hB_st idx hidx
    have hzfB : ZeroFrom stB.mem (st.regs 12) := fun a ha => by
      have hge := hInv.h_ge; rw [hfrB a (Or.inr (by omega)) (Or.inr (by omega))]; exact hInv.zf a ha
    have h12_sp : st.regs 12 + Sprev < 2 ^ w := by
      have := hInv.h_le
      have h1 : (j + 1) * Sprev ≤ nBlocks * Sprev := Nat.mul_le_mul_right Sprev (by omega)
      rw [Nat.succ_mul] at h1; omega
    have hge := hInv.h_ge
    have hSubGeom : ps.wRelA + 2 + 2 * es.length ≤ st.regs 12 ∧ ps.rangeB_A + b ≤ st.regs 12 ∧
        pA + coreParamsSize r ≤ st.regs 12 ∧ locA + G.n ≤ st.regs 12 ∧ tmpA + 4 * b + 2 + b ≤ st.regs 12 ∧
        locA + G.n ≤ ps.wRelA ∧ locA + G.n ≤ ps.rangeB_A ∧
        DisjointRange locA G.n pA (coreParamsSize r) ∧ locA + G.n ≤ tmpA + 4 * b ∧
        ps.wRelA + 2 + 2 * es.length ≤ tmpA + 4 * b ∧ ps.rangeB_A + b ≤ tmpA + 4 * b ∧
        pA + coreParamsSize r ≤ tmpA + 4 * b ∧ xA + j * b + b ≤ tmpA + 4 * b ∧
        st.regs 12 + Sprev < 2 ^ w ∧ q < 2 ^ w ∧ 16 < 2 ^ w := by
      clear hSub hcp_at hX_at hX_sub hmod hpers_w hrangeB_at hInv hcfg hW_pre hfr_lo hB0 hB_len hB_nd
        hB_fin hB_sub hB_st hW_st hes_B hes_Bl hW'_n hW'_n_bound hW'_valid hW'_loop hW'_deg hW'_m
        hrA hlt28_B hr28_B hr29_B hr30_B hr31_B hr32_B hlocB hfrB hW'_atB hfrB_lo hcp_B hRange_B hB_B hzfB
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, hd_loc_p, by omega,
        by omega, by omega, by omega, by omega, h12_sp, hq_lt_w, hw16⟩
    obtain ⟨res_j, st1, cB, hrB, hOut_j, hSpec_j, h12ge, h12le, hzf1, hloc1, hfr1B, hlt33_1, hcB⟩ :=
      sbQueryOneBlock_subAndLift (ω := ω) hSub ha0 ha hrl hq2 hqr hB_len hB_nd hB_fin hB_B hes_B
        hb_le_Gn hcp_B hW'_atB hW'_valid hW'_n_bound hRange_B hW'_loop hb_le hW'_deg hW'_m hlocB hzfB
        hSubGeom
        ⟨(hlt28_B 0 (by decide)).trans hInv.args.r0, (hlt28_B 4 (by decide)).trans hInv.args.r4,
          (hlt28_B 7 (by decide)).trans hInv.args.r7, (hlt28_B 8 (by decide)).trans hInv.args.r8,
          hlt28_B 12 (by decide), hr28_B, hr30_B, hr31_B, hr32_B⟩
    have hcomb : Runs w p ω (seqStmts [
        .assign 28 (.bin .add (.reg 3) (.bin .mul (.reg 27) (.reg 4))),
        .assign 29 (.bin .add (.reg 20) (.bin .mul (.reg 27) (.reg 16))),
        .assign 30 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 4))),
        .assign 31 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
        .assign 32 (.bin .add (.reg 31) (.reg 4)),
        sbRelabelGraphStmt,
        .assign 33 (.bin .sub (.reg 0) (.const 1)),
        .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
        sbLiftOutStmt]) st .normal st1 (cA + cB + 1) := by
      dsimp only [seqStmts] at hrA hrB ⊢
      rcases runs_seq_n_mp hrA with ⟨s1, c1a, c1b, h1a, h1b, rfl⟩
      rcases runs_seq_n_mp h1b with ⟨s2, c2a, c2b, h2a, h2b, rfl⟩
      rcases runs_seq_n_mp h2b with ⟨s3, c3a, c3b, h3a, h3b, rfl⟩
      rcases runs_seq_n_mp h3b with ⟨s4, c4a, c4b, h4a, h4b, rfl⟩
      rcases runs_seq_n_mp h4b with ⟨s5, c5a, c5b, h5a, h5b, rfl⟩
      have h := runs_seq_n h1a (runs_seq_n h2a (runs_seq_n h3a (runs_seq_n h4a (runs_seq_n h5a (runs_seq_n h5b hrB)))))
      have hceq : c1a + (c2a + (c3a + (c4a + (c5a + (c5b + cB + 1) + 1) + 1) + 1) + 1) + 1 =
          c1a + (c2a + (c3a + (c4a + (c5a + c5b + 1) + 1) + 1) + 1) + 1 + cB + 1 := by omega
      rwa [hceq] at h
    refine ⟨res_j, st1, cA + cB + 1, hcomb, hOut_j, hSpec_j, h12ge, h12le, hzf1, hloc1,
      fun a ha hrel hout => by
        by_cases hloc_in : locA ≤ a ∧ a < locA + G.n
        · have ha_eq : a = locA + (a - locA) := by omega
          rw [ha_eq, hloc1 (a - locA) (by omega), hInv.loc0 (a - locA) (by omega)]
        · rw [hfr1B a ha hout, hfrB a (by omega) (by omega)],
      ⟨fun r hr hne => (hlt33_1 r (by omega) hne).trans (hlt28_B r hr),
        (hlt33_1 28 (by decide) (by decide)).trans hr28_B,
        (hlt33_1 29 (by decide) (by decide)).trans hr29_B,
        (hlt33_1 30 (by decide) (by decide)).trans hr30_B⟩, by omega⟩

/-- Execute a single block `j < nBlocks` of `sbQueryLoopStmt bSubCore`. -/
private lemma sbQueryOneBlock_step {cfg : ParamConfig} {M r q w bSubCore Sprev Tprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 tRound j : ℕ}
    {p : Program} {memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {st : State} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt memStart pA (coreParamsOf cfg M r) r)
    (hX_at : VertsAt memStart xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hb_even : Even b) (hb_le : b ≤ (coreParamsOf cfg M r).N ^ (q - 1))
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (ht_le : tRound ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z tRound bst)
    (hpers_w : ∀ i < nBlocks,
      let ps := sbPersist h0 k b nBlocks (LParam M)
      GraphAt memStart (ps.wBaseA + i * ps.wStride)
        (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))))
    (hrangeB_at : ListAt memStart (sbPersist h0 k b nBlocks (LParam M)).rangeB_A (List.range b))
    (hcur_lay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ cutRecsA ∧
      pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧
      hSub0 = tmpA + 4 * b + 2 + b ∧
      xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧ locA + G.n ≤ h0 ∧
      DisjointRange locA G.n xA k ∧ DisjointRange locA G.n pA (coreParamsSize r) ∧
      hSub0 + nBlocks * Sprev < 2 ^ w ∧ 16 < 2 ^ w)
    (hj_lt : j < nBlocks)
    (hInv : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st) :
    ∃ res' cutIds' pairs' cPrimeAddrs' compAddrs' cPrimeLists' compLists' st' cost,
      Runs w p ω (sbQueryOneBlockStmt bSubCore) st .normal st' cost ∧
      SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
        tmpA hSub0 memStart G X bst (j + 1) res' cutIds' pairs' cPrimeAddrs' compAddrs'
        cPrimeLists' compLists'
        { mem := st'.mem, regs := Function.update st'.regs 27 (j + 1), pos := st'.pos } ∧
      st'.regs 14 = st.regs 14 ∧ st'.regs 15 = st.regs 15 ∧ st'.regs 27 = j ∧
      cost ≤ Tprev + 1720 * b * LParam M + 390 * b + 660 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hw16 : 16 < 2 ^ w := hcur_lay.2.2.2.2.2.2.2.2.2.2
  have hact_w : ps.actA + j < 2 ^ w := by rcases hcur_lay with ⟨hP, hp, ht, hh, _, _, _, _, _, hm, _⟩; omega
  have hact_mem_j : st.mem (ps.actA + j) = if bst.active j then 1 else 0 := by
    have h := hInv.act_mem j hj_lt; simp only [lt_irrefl, false_and, ite_false] at h; exact h
  cases hact_j : bst.active j with
  | false =>
    rw [hact_j] at hact_mem_j; simp only [Bool.false_eq_true, ↓reduceIte] at hact_mem_j
    have hrun : ∃ o st' cost,
        Runs w p ω (sbQueryOneBlockStmt bSubCore) st o st' cost ∧
        (normalPost fun st' => st' = st) o st' ∧ cost ≤ 20 := by
      refine runs_start_le ?_
      dsimp only [sbQueryOneBlockStmt]
      refine runs_cond_le (v := 0)
        (Expr.eval_eq_false
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hInv.args.r17) (Expr.eval_reg_of_eq hInv.r27) hact_w)
            hact_mem_j)
          (Expr.eval_const (by omega)) (by decide) (by omega))
        (fun h => absurd rfl h) (fun _ => ?_)
      exact runs_nop_le rfl (by simp only [Expr.size]; omega)
    rcases hrun with ⟨o, st', cost, hruns, hpost, hcost⟩
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rw [hpost] at hruns
      refine ⟨res, cutIds, pairs, cPrimeAddrs, compAddrs, cPrimeLists, compLists, st, cost,
        hruns, ?_, rfl, rfl, hInv.r27, by omega⟩
      refine ⟨sbArgs_of_eq hInv.args (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r13],
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r22],
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r23],
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r24],
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r25],
        by dsimp only; rw [Function.update_of_ne (by decide), hInv.r26],
        by dsimp only; rw [Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.h_ge,
        by dsimp only; rw [Function.update_of_ne (by decide)]; have := hInv.h_le; rw [Nat.succ_mul]; omega,
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.zf,
        hInv.loc0,
        fun i hi hact => by
          by_cases hij : i = j
          · subst hij; simp [hact_j] at hact
          · exact hInv.res_spec i (by omega) hact,
        by rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, hact_j]
           simp only [Bool.false_eq_true, ite_false, List.append_nil]; exact hInv.cutIds_eq,
        by rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, hact_j]
           simp only [Bool.false_eq_true, ite_false, List.append_nil]; exact hInv.pairs_eq,
        hInv.lens_eq, hInv.recs_at,
        ?_,
        fun i hi => ⟨(hInv.saved_mem i hi).1, fun hij1 hact S' hS' => by
          by_cases hij : i = j
          · subst hij; simp [hact_j] at hact
          · exact (hInv.saved_mem i hi).2 (by omega) hact S' hS'⟩,
        hInv.frame_persist, hInv.frame_w⟩
      intro i hi
      dsimp only
      rw [hInv.act_mem i hi]
      by_cases hij : i = j
      · subst hij; simp [hact_j]
      · have hiff : i < j + 1 ↔ i < j := by omega
        simp only [hiff]
  | true =>
    rw [hact_j] at hact_mem_j; simp only [↓reduceIte] at hact_mem_j
    have hsav_le : ∀ i < nBlocks, bst.active i = false → (bst.savedS i).card ≤ b := fun i hi hf => by
      have hsub := (hmod.inactive_exp i hi hf).1
      have hcard := card_blockSet (Finset.sort_nodup X (· ≤ ·)) (by rw [← hnb_eq]; exact hi)
      exact (Finset.card_le_card hsub).trans (le_of_eq hcard)
    obtain ⟨res_j, st1, c1, hruns1, hOut_j, hSpec_j, h12ge, h12le, hzf1, hloc1, hfr1, hregs1, hc1⟩ :=
      sbQueryOneBlock_callPrefix (ω := ω) hSub ha0 ha hrl hq2 hqr hcp_at hX_at hX_sub hb_le hnb_eq
        ht_le hmod hpers_w hrangeB_at hcur_lay hj_lt hInv
    obtain ⟨cutIds', pairs', cPrimeAddrs', compAddrs', cPrimeLists', compLists', st', c2,
      hruns2, hInv', h14', h15', h27', hc2⟩ :=
      sbQueryOneBlock_afterCall (ω := ω) hX_at hX_sub hb_even hnb_eq hcur_lay hj_lt hact_j hsav_le hInv
        hOut_j hSpec_j h12ge h12le hzf1 hloc1 hfr1 hregs1
    -- Reassociate right-nested `seqStmts` of `hruns1` followed by `hruns2`
    have hseq : Runs w p ω (seqStmts [
        .assign 28 (.bin .add (.reg 3) (.bin .mul (.reg 27) (.reg 4))),
        .assign 29 (.bin .add (.reg 20) (.bin .mul (.reg 27) (.reg 16))),
        .assign 30 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 4))),
        .assign 31 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
        .assign 32 (.bin .add (.reg 31) (.reg 4)),
        sbRelabelGraphStmt,
        .assign 33 (.bin .sub (.reg 0) (.const 1)),
        .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
        sbLiftOutStmt,
        sbQueryAfterCallStmt]) st .normal st' (c1 + c2 + 1) := by
      dsimp only [seqStmts] at hruns1 ⊢
      rcases runs_seq_n_mp hruns1 with ⟨s1, c1a, c1b, h1a, h1b, rfl⟩
      rcases runs_seq_n_mp h1b with ⟨s2, c2a, c2b, h2a, h2b, rfl⟩
      rcases runs_seq_n_mp h2b with ⟨s3, c3a, c3b, h3a, h3b, rfl⟩
      rcases runs_seq_n_mp h3b with ⟨s4, c4a, c4b, h4a, h4b, rfl⟩
      rcases runs_seq_n_mp h4b with ⟨s5, c5a, c5b, h5a, h5b, rfl⟩
      rcases runs_seq_n_mp h5b with ⟨s6, c6a, c6b, h6a, h6b, rfl⟩
      rcases runs_seq_n_mp h6b with ⟨s7, c7a, c7b, h7a, h7b, rfl⟩
      rcases runs_seq_n_mp h7b with ⟨s8, c8a, c8b, h8a, h8b, rfl⟩
      have hcomb := runs_seq_n h1a (runs_seq_n h2a (runs_seq_n h3a
        (runs_seq_n h4a (runs_seq_n h5a (runs_seq_n h6a
          (runs_seq_n h7a (runs_seq_n h8a (runs_seq_n h8b hruns2))))))))
      have hceq : c1a + (c2a + (c3a + (c4a + (c5a + (c6a + (c7a + (c8a + (c8b + c2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
          c1a + (c2a + (c3a + (c4a + (c5a + (c6a + (c7a + (c8a + c8b + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 + c2 + 1 := by omega
      rwa [hceq] at hcomb
    have hcond_eval : (.bin .eq (.load (.bin .add (.reg 17) (.reg 27))) (.const 1) : Expr).eval w st = some 1 :=
      Expr.eval_eq_true
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hInv.args.r17) (Expr.eval_reg_of_eq hInv.r27) hact_w)
          hact_mem_j)
        (Expr.eval_const (by omega)) rfl (by omega)
    have hfull : Runs w p ω (sbQueryOneBlockStmt bSubCore) st .normal st'
        (Expr.size (.bin .eq (.load (.bin .add (.reg 17) (.reg 27))) (.const 1)) + (c1 + c2 + 1) + 1) :=
      runs_cond_t hcond_eval (by decide) hseq
    exact ⟨Function.update res j res_j, cutIds', pairs', cPrimeAddrs', compAddrs', cPrimeLists', compLists',
      st', _, hfull, hInv', h14', h15', h27', by simp only [Expr.size]; omega⟩

/-- Full execution of `sbQueryLoopStmt bSubCore` across all `nBlocks` blocks in one round. -/
theorem sbQueryLoop_run {cfg : ParamConfig} {M r q w bSubCore Sprev Tprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 tRound : ℕ}
    {p : Program} {G : Graph} {X : Finset ℕ} {bst : BlockGameState} {st₀ : State} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt st₀.mem pA (coreParamsOf cfg M r) r)
    (hX_at : VertsAt st₀.mem xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hb_even : Even b) (hb_le : b ≤ (coreParamsOf cfg M r).N ^ (q - 1))
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (ht_le : tRound ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z tRound bst)
    (hpers : SbPersistAt st₀.mem G X b nBlocks (LParam M) h0 bst)
    (hcur_lay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ cutRecsA ∧
      pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧
      hSub0 = tmpA + 4 * b + 2 + b ∧
      xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧ locA + G.n ≤ h0 ∧
      DisjointRange locA G.n xA k ∧ DisjointRange locA G.n pA (coreParamsSize r) ∧
      hSub0 + nBlocks * Sprev < 2 ^ w ∧ 16 < 2 ^ w)
    (hargs : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st₀)
    (hr12 : st₀.regs 12 = hSub0) (hr13 : st₀.regs 13 = 0)
    (hr22 : st₀.regs 22 = cutRecsA) (hr23 : st₀.regs 23 = pairsA) (hr24 : st₀.regs 24 = tmpA)
    (hr25 : st₀.regs 25 = 0) (hr26 : st₀.regs 26 = pairsA + 1)
    (hzf : ZeroFrom st₀.mem hSub0) (hloc0 : ∀ u < G.n, st₀.mem (locA + u) = 0) :
    ∃ res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st' cost,
      Runs w p ω (sbQueryLoopStmt bSubCore) st₀ .normal st' cost ∧
      SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
        tmpA hSub0 st₀.mem G X bst nBlocks res cutIds pairs cPrimeAddrs compAddrs
        cPrimeLists compLists st' ∧
      st'.regs 14 = st₀.regs 14 ∧ st'.regs 15 = st₀.regs 15 ∧
      cost ≤ nBlocks * Tprev + 1720 * k * LParam M + 390 * k + 680 * nBlocks + 20 := by
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le (X.sort (· ≤ ·)) b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hpers_w : ∀ i < nBlocks,
      let ps := sbPersist h0 k b nBlocks (LParam M)
      GraphAt st₀.mem (ps.wBaseA + i * ps.wStride)
        (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))) := fun i hi => by
    have := hpers.w_at i hi; rwa [← hX_at.1] at this
  have hrangeB_at : ListAt st₀.mem (sbPersist h0 k b nBlocks (LParam M)).rangeB_A (List.range b) := by
    have := hpers.rangeB_at; rwa [← hX_at.1] at this
  have hnb_w : nBlocks < 2 ^ w := by
    rcases hcur_lay with ⟨hP, hp, ht, hh, _, _, _, _, _, hm, _⟩
    dsimp only [sbPersist] at hP; omega
  have hw16 : 16 < 2 ^ w := hcur_lay.2.2.2.2.2.2.2.2.2.2
  have hloop : ∀ (rem j : ℕ) (res : ℕ → CoreResult) (cutIds : List ℕ)
      (pairs : List (Finset ℕ × Finset ℕ)) (cPrimeAddrs compAddrs : List ℕ)
      (cPrimeLists compLists : List (List ℕ)) (st : State),
      j + rem = nBlocks →
      SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
        tmpA hSub0 st₀.mem G X bst j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st →
      ∃ res' cutIds' pairs' cPrimeAddrs' compAddrs' cPrimeLists' compLists' st' cost,
        Runs w p ω (forUp 27 (.reg 5) (sbQueryOneBlockStmt bSubCore)) st .normal st' cost ∧
        SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
          tmpA hSub0 st₀.mem G X bst nBlocks res' cutIds' pairs' cPrimeAddrs' compAddrs'
          cPrimeLists' compLists' st' ∧
        st'.regs 14 = st.regs 14 ∧ st'.regs 15 = st.regs 15 ∧
        cost ≤ rem * (Tprev + 1720 * b * LParam M + 390 * b + 680) + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st hsum hInv
      have hj_eq : j = nBlocks := by omega
      subst hj_eq
      have hcond : (.bin .lt (.reg 27) (.reg 5) : Expr).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq hInv.r27) (Expr.eval_reg_of_eq hInv.args.r5)
          (le_refl _) (by omega)
      exact ⟨res, cutIds, pairs, cPrimeAddrs, compAddrs, cPrimeLists, compLists, st, _,
        runs_loop_f hcond, hInv, rfl, rfl, by simp only [Expr.size]; omega⟩
    | succ rem ih =>
      intro j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st hsum hInv
      have hj_lt : j < nBlocks := by omega
      have hcond : (.bin .lt (.reg 27) (.reg 5) : Expr).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq hInv.r27) (Expr.eval_reg_of_eq hInv.args.r5)
          hj_lt (by omega)
      obtain ⟨res1, cutIds1, pairs1, cPA1, oPA1, cPL1, oPL1, st1, c1,
        hrun1, hInv1, h14_1, h15_1, h27_1, hc1⟩ :=
        sbQueryOneBlock_step hSub ha0 ha hrl hq2 hqr hcp_at hX_at hX_sub hb_even hb_le hnb_eq
          ht_le hmod hpers_w hrangeB_at hcur_lay hj_lt hInv
      let st2 : State := { mem := st1.mem, regs := Function.update st1.regs 27 (j + 1), pos := st1.pos }
      have hinc : Runs w p ω (.assign 27 (.bin .add (.reg 27) (.const 1))) st1 .normal st2
          (Expr.size (.bin .add (.reg 27) (.const 1)) + 1) :=
        runs_assign_n (Expr.eval_add (Expr.eval_reg_of_eq h27_1) (Expr.eval_const (by omega)) (by omega))
      obtain ⟨res', cutIds', pairs', cPA', oPA', cPL', oPL', st', c2,
        hrun2, hInv', h14', h15', hc2⟩ :=
        ih (j + 1) res1 cutIds1 pairs1 cPA1 oPA1 cPL1 oPL1 st2 (by omega) hInv1
      have hstep := runs_loop_t hcond (by decide) (runs_seq_n hrun1 hinc) hrun2
      have h14_2 : st2.regs 14 = st.regs 14 := by
        dsimp only [st2]; rw [Function.update_of_ne (by decide), h14_1]
      have h15_2 : st2.regs 15 = st.regs 15 := by
        dsimp only [st2]; rw [Function.update_of_ne (by decide), h15_1]
      refine ⟨res', cutIds', pairs', cPA', oPA', cPL', oPL', st', _, hstep, hInv',
        h14'.trans h14_2, h15'.trans h15_2, ?_⟩
      simp only [Expr.size]
      rw [Nat.succ_mul]
      omega
  let stInit : State := { mem := st₀.mem, regs := Function.update st₀.regs 27 0, pos := st₀.pos }
  have hinit_run : Runs w p ω (.assign 27 (.const 0)) st₀ .normal stInit (Expr.size (.const 0) + 1) :=
    runs_assign_n (Expr.eval_const (by omega))
  have hInv0 : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 st₀.mem G X bst 0 (fun _ => .cut ∅) [] [] [] [] [] [] stInit := by
    refine ⟨sbArgs_of_eq hargs (fun r hr => by dsimp only [stInit]; rw [Function.update_of_ne (by omega)]),
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr13],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr22],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr23],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr24],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr25]; rfl,
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr26]; simp,
      by dsimp only [stInit]; rw [Function.update_self],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr12],
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr12]; simp,
      by dsimp only [stInit]; rw [Function.update_of_ne (by decide), hr12]; exact hzf,
      hloc0, fun i hi => absurd hi (Nat.not_lt_zero i), rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, fun idx hidx => absurd hidx (Nat.not_lt_zero idx),
      fun i hi => by
        simp only [Nat.not_lt_zero, false_and, ite_false]
        have := hpers.act_at i hi; rwa [← hX_at.1] at this,
      fun i hi => ⟨fun hf => by have := hpers.inact_saved i hi hf; rwa [← hX_at.1] at this,
        fun h0 => absurd h0 (Nat.not_lt_zero i)⟩,
      fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨res', cutIds', pairs', cPA', oPA', cPL', oPL', st', cLoop,
    hrunLoop, hInv', h14', h15', hcLoop⟩ :=
    hloop nBlocks 0 (fun _ => .cut ∅) [] [] [] [] [] [] stInit (by omega) hInv0
  have h14_0 : stInit.regs 14 = st₀.regs 14 := by dsimp only [stInit]; rw [Function.update_of_ne (by decide)]
  have h15_0 : stInit.regs 15 = st₀.regs 15 := by dsimp only [stInit]; rw [Function.update_of_ne (by decide)]
  refine ⟨res', cutIds', pairs', cPA', oPA', cPL', oPL', st', _,
    runs_seq_n hinit_run hrunLoop, hInv', h14'.trans h14_0, h15'.trans h15_0, ?_⟩
  have hmul : nBlocks * (Tprev + 1720 * b * LParam M + 390 * b + 680) =
      nBlocks * Tprev + 1720 * (nBlocks * b) * LParam M + 390 * (nBlocks * b) + 680 * nBlocks := by ring
  have hnb_bL : 1720 * (nBlocks * b) * LParam M ≤ 1720 * k * LParam M :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnb_b)
  simp only [Expr.size]
  omega

end MinCostFlow.ExpanderDecomp
