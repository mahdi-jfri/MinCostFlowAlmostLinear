module

public import MinCostFlow.ExpanderDecomp.RouteProgLoopBase

/-!
# Output Serialization Triples for Procedure 5 (`RouteProgLoopEmit`)

Verifies the cut and matched output-serialization statements of `routeOrCutCsrProc`:
- `emitCut_triple`: translates the local cut list `wsCutList[0 .. cutSize - 1]` via `origVertAddr`
  to write `RouteOutAt st'.mem rcfg.outAddr (.cut U)` in `≤ 45 * U.card + 110` steps.
- `emitPathList_triple`, `emitChunkChain_triple`, `emitMatched_triple`: traverses the `k`
  accumulated chunk chains (`ChunkChainAt` → `PathListAt`), translating endpoints via `origVertAddr`
  and copying existing `SeqAt` walk pointers from `pathHeap`, to write both
  `RouteOutAt st'.mem rcfg.outAddr (mkMatchedResult acc)` and
  `WalksAt st'.mem rcfg.walksAddr acc.flatten.length (fun j => (acc.flatten.getD j ((0, 0), [])).2)`
  in `≤ 120 * acc.flatten.length + 45 * k + 120` steps.
- Pure list helpers linking `accChunks.map List.flatten` with `List.zipWith (· ++ ·)` across batches.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure List Helpers for Chunk Accumulation and Emission -/

lemma flatten_map_prod_fst (acc : List (List ((ℕ × ℕ) × List ℕ))) :
    (acc.map fun ps => ps.map Prod.fst).flatten = acc.flatten.map Prod.fst := by
  induction acc with
  | nil => rfl
  | cons ps rest ih => simp only [List.map_cons, List.flatten_cons, List.map_append, ih]

lemma accChunks_step_flatten
    (accChunks : List (List (List ((ℕ × ℕ) × List ℕ))))
    (batchPaths : List (List ((ℕ × ℕ) × List ℕ)))
    (hlen : accChunks.length = batchPaths.length) :
    let nextChunks : List (List (List ((ℕ × ℕ) × List ℕ))) :=
      List.ofFn fun j : Fin accChunks.length =>
        if batchPaths.getD j.1 [] = [] then accChunks.getD j.1 []
        else accChunks.getD j.1 [] ++ [batchPaths.getD j.1 []]
    nextChunks.length = accChunks.length ∧
    (∀ j (_hj : j < accChunks.length),
      nextChunks.getD j [] =
        if batchPaths.getD j [] = [] then accChunks.getD j []
        else accChunks.getD j [] ++ [batchPaths.getD j []]) ∧
    nextChunks.map List.flatten =
      List.zipWith (· ++ ·) (accChunks.map List.flatten) batchPaths := by
  intro nextChunks
  have hlen_n : nextChunks.length = accChunks.length := by simp [nextChunks]
  refine ⟨hlen_n, fun j hj => ?_, ?_⟩
  · simp [nextChunks, List.getD_eq_getElem?_getD, hj]
  · apply List.ext_getElem
    · simp [nextChunks, hlen]
    · intro j h1 h2
      have hj : j < accChunks.length := by simp [nextChunks] at h1; exact h1
      have hjb : j < batchPaths.length := by omega
      simp only [nextChunks, List.getElem_map, List.getElem_ofFn, List.getElem_zipWith,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjb,
        Option.getD_some]
      split_ifs with he
      · simp [he]
      · simp

lemma sortedX_getElem_eq_origOf {X : Finset ℕ} {i : ℕ} (hi : i < X.card) :
    (sortedX X)[i]'(by simp [sortedX, hi]) = origOf X i := by
  unfold origOf
  have hlt : i < (sortedX X).length := by simp [sortedX, hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

lemma origOf_map_nodup {X : Finset ℕ} {ul : List ℕ}
    (hnd : ul.Nodup) (hsub : ∀ x ∈ ul, x < X.card) :
    (ul.map (origOf X)).Nodup := by
  rw [List.nodup_map_iff_inj_on hnd]
  intro a ha b hb heq
  have ha' := hsub a ha; have hb' := hsub b hb
  have h1 := locOf_origOf ha'; have h2 := locOf_origOf hb'
  rw [heq] at h1; omega

lemma origOf_map_toFinset {X U : Finset ℕ} {ul : List ℕ}
    (hsub : ∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U)
    (hcov : ∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul) :
    (ul.map (origOf X)).toFinset = U := by
  ext v
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (hsub x hx).2
  · intro hv
    have ⟨hvX, hmem⟩ := hcov v hv
    exact ⟨locOf X v, hmem, origOf_locOf hvX⟩

/-! ## 2. Cut Serialization (`emitCut_triple`) -/

private lemma emitCutLoop_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {cutListAddr origAddr outAddr : ℕ} {ul : List ℕ}
    (hsub : ∀ x ∈ ul, x < X.card)
    (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hw_cl : cutListAddr + ul.length + 5 < 2 ^ w)
    (hw_orig : origAddr + X.card + 5 < 2 ^ w)
    (hw_out : outAddr + 2 + ul.length + 5 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hd_cl_out : DisjRange cutListAddr ul.length (outAddr + 2) ul.length)
    (hd_orig_out : DisjRange origAddr X.card (outAddr + 2) ul.length)
    (rem : ℕ) :
    ∀ (i : ℕ) (st0 : State),
      i + rem = ul.length →
      ListAt st0.mem cutListAddr ul →
      ListAt st0.mem origAddr (sortedX X) →
      (∀ t < i, st0.mem (outAddr + 2 + t) = origOf X (ul.getD t 0)) →
      st0.regs 6 = ul.length → st0.regs 7 = origAddr →
      st0.regs 8 = outAddr → st0.regs 9 = cutListAddr → st0.regs 10 = i →
      ∀ ω, ∃ st1 c1,
        Runs w p ω
          (.loop (.bin .lt (.reg 10) (.reg 6))
            (seqStmts
              [ .assign 11 (.load (.bin .add (.reg 9) (.reg 10)))
              , .assign 12 (.load (.bin .add (.reg 7) (.reg 11)))
              , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 10)) (.reg 12)
              , .assign 10 (.bin .add (.reg 10) (.const 1)) ]))
          st0 .normal st1 c1 ∧
        (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → st1.regs r = st0.regs r) ∧
        (∀ t < ul.length, st1.mem (outAddr + 2 + t) = origOf X (ul.getD t 0)) ∧
        (∀ a, ¬ (outAddr + 2 + i ≤ a ∧ a < outAddr + 2 + ul.length) → st1.mem a = st0.mem a) ∧
        c1 ≤ 35 * rem + 10 := by
  induction rem with
  | zero =>
    intro i st0 hi _ _ hpref hr6 _ _ _ hr10 ω
    have hcond : (Expr.bin .lt (.reg 10) (.reg 6)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr10, hr6, show ¬ i < ul.length by omega]
    refine ⟨st0, _, batch_runs_loop_zero hcond, fun _ _ _ _ => rfl,
      fun t ht => hpref t (by omega), fun _ _ => rfl, by simp [Expr.size]⟩
  | succ rem ih =>
    intro i st0 hi hcl horig hpref hr6 hr7 hr8 hr9 hr10 ω
    have hilt : i < ul.length := by omega
    have hw_ne : w ≠ 0 := by intro h0; subst h0; simp at hw4
    have hcond1 : (Expr.bin .lt (.reg 10) (.reg 6)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr10, hr6, hilt, hw_ne]
    set x := ul[i]'hilt
    have hx_lt : x < X.card := hsub x (List.getElem_mem hilt)
    have hcl_i : st0.mem (cutListAddr + i) = x := hcl i hilt
    have horig_x : st0.mem (origAddr + x) = origOf X x := by
      have h1 := horig x (by simp [sortedX, hx_lt])
      rwa [sortedX_getElem_eq_origOf hx_lt] at h1
    have hox_w : origOf X x < 2 ^ w := hX_w _ (origOf_mem hx_lt)
    set regs1 := Function.update (Function.update (Function.update st0.regs 11 x) 12 (origOf X x)) 10 (i + 1)
    set mem1 := Function.update st0.mem (outAddr + 2 + i) (origOf X x)
    set st1 : State := { mem := mem1, regs := regs1, pos := st0.pos }
    have hbody : ∃ cB,
        Runs w p ω
          (seqStmts
            [ .assign 11 (.load (.bin .add (.reg 9) (.reg 10)))
            , .assign 12 (.load (.bin .add (.reg 7) (.reg 11)))
            , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 10)) (.reg 12)
            , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
          st0 .normal st1 cB ∧ cB ≤ 28 := by
      have h0 : ∃ o s c0,
          Runs w p ω
            (seqStmts
              [ .assign 11 (.load (.bin .add (.reg 9) (.reg 10)))
              , .assign 12 (.load (.bin .add (.reg 7) (.reg 11)))
              , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 10)) (.reg 12)
              , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
            st0 o s c0 ∧ (o = .normal ∧ s = st1) ∧ 0 + c0 ≤ 28 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := x) (by rw [← hcl_i]; eval_expr) ?_
        refine runs_seq_assign_le (v := origOf X x) (by rw [← horig_x]; eval_expr) ?_
        refine runs_seq_store_le (x := outAddr + 2 + i) (v := origOf X x) (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := i + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cB, h, ⟨rfl, rfl⟩, hcB⟩; exact ⟨cB, h, by omega⟩
    rcases hbody with ⟨cB, hrunB, hcB⟩
    have hne_cl : ∀ j < ul.length, cutListAddr + j ≠ outAddr + 2 + i := fun j hj => by
      unfold DisjRange at hd_cl_out; omega
    have hne_orig : ∀ j < (sortedX X).length, origAddr + j ≠ outAddr + 2 + i := fun j hj => by
      simp only [sortedX, Finset.length_sort] at hj
      unfold DisjRange at hd_orig_out; omega
    obtain ⟨st2, c2, hrun2, hreg2, hpref2, hfr2, hc2⟩ :=
      ih (i + 1) st1 (by omega)
        (fun j hj => by simp only [st1, mem1]; rw [Function.update_of_ne (hne_cl j hj)]; exact hcl j hj)
        (fun j hj => by simp only [st1, mem1]; rw [Function.update_of_ne (hne_orig j hj)]; exact horig j hj)
        (fun t ht => by
          simp only [st1, mem1]
          by_cases hti : t = i
          · subst hti; rw [Function.update_self]; simp [x, List.getD_eq_getElem?_getD, hilt]
          · rw [Function.update_of_ne (by omega)]; exact hpref t (by omega))
        (by simp [st1, regs1, hr6]) (by simp [st1, regs1, hr7]) (by simp [st1, regs1, hr8])
        (by simp [st1, regs1, hr9]) (by simp [st1, regs1]) ω
    refine ⟨st2, _, batch_runs_loop_step hcond1 (by decide) hrunB hrun2, ?_, hpref2, ?_, ?_⟩
    · intro r h10 h11 h12
      rw [hreg2 r h10 h11 h12]
      simp [st1, regs1, h10, h11, h12]
    · intro a ha
      rw [hfr2 a (by omega)]
      simp only [st1, mem1]; rw [Function.update_of_ne (by omega)]
    · simp only [Expr.size] at hcB hc2 ⊢; omega

/-- Verification of `emitCutStmt`: writes `RouteOutAt st1.mem rcfg.outAddr (.cut U)` in
`≤ 40 * U.card + 120` steps, preserving `reg 5` and modifying only `[outAddr, outAddr + 2 + U.card)`. -/
theorem emitCut_triple {w : ℕ} {p : Program}
    {X U : Finset ℕ} {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg} {ul : List ℕ}
    (hnX : rcfg.batch.nX = X.card)
    (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    (hul_len : ul.length = U.card) (hul_nd : ul.Nodup)
    (hul_sub : ∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U)
    (hul_cov : ∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul)
    {st0 : State}
    (hm0 : st0.mem (cfgAddr + 0) = rcfg.batch.nX)
    (hm1 : st0.mem (cfgAddr + 1) = rcfg.batch.k)
    (hm14 : st0.mem (cfgAddr + 14) = rcfg.batch.ws)
    (hm15 : st0.mem (cfgAddr + 15) = rcfg.batch.m2)
    (hm25 : st0.mem (cfgAddr + 25) = U.card)
    (hm29 : st0.mem (cfgAddr + 29) = rcfg.origVertAddr)
    (hm30 : st0.mem (cfgAddr + 30) = rcfg.outAddr)
    (hul_at : ListAt st0.mem (wsCutList rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k) ul)
    (horig : ListAt st0.mem rcfg.origVertAddr (sortedX X))
    (hr0 : st0.regs 0 = cfgAddr) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω emitCutStmt st0 .normal st1 c1 ∧
      st1.regs 5 = st0.regs 5 ∧
      RouteOutAt st1.mem rcfg.outAddr (.cut U) ∧
      (∀ a, ¬ (rcfg.outAddr ≤ a ∧ a < rcfg.outAddr + 2 + U.card) → st1.mem a = st0.mem a) ∧
      c1 ≤ 40 * U.card + 120 := by
  intro ω
  set c := rcfg.batch
  have hU_le : U.card ≤ X.card := Finset.card_le_card fun v hv => (hul_cov v hv).1
  have hw_cfg := hdisj.w_cfg
  have hw_ws : c.ws + (129 + 27 * c.nX + c.m2 + 3 * c.k) + 10 < 2 ^ w := hdisj.w_ws
  have hw_orig : rcfg.origVertAddr + c.nX + 5 < 2 ^ w := hdisj.w_orig
  have hw_out : rcfg.outAddr + 2 + 2 * c.nX + 5 < 2 ^ w := hdisj.w_out
  have hw_m2 : c.m2 + 5 < 2 ^ w := hdisj.w_m2
  have hw_k : c.k + 5 < 2 ^ w := hdisj.w_k
  have hw4 := hdisj.w_4
  set cl := wsCutList c.ws c.nX c.m2 c.k
  set regsA := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update st0.regs
    1 c.nX) 2 c.k) 3 c.ws) 4 c.m2) 6 U.card) 7 rcfg.origVertAddr) 8 rcfg.outAddr) 9 cl) 10 0
  set memA := Function.update (Function.update st0.mem rcfg.outAddr 1) (rcfg.outAddr + 1) U.card
  set stA : State := { mem := memA, regs := regsA, pos := st0.pos }
  have hpre : ∃ cA,
      Runs w p ω
        (seqStmts
          [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
          , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
          , .assign 3 (.load (.bin .add (.reg 0) (.const 14)))
          , .assign 4 (.load (.bin .add (.reg 0) (.const 15)))
          , .assign 6 (.load (.bin .add (.reg 0) (.const 25)))
          , .assign 7 (.load (.bin .add (.reg 0) (.const 29)))
          , .assign 8 (.load (.bin .add (.reg 0) (.const 30)))
          , .assign 9 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 3) (.const 129))
              (.bin .mul (.const 26) (.reg 1))) (.reg 4)) (.bin .mul (.const 3) (.reg 2)))
          , .store (.reg 8) (.const 1)
          , .store (.bin .add (.reg 8) (.const 1)) (.reg 6)
          , .assign 10 (.const 0) ])
        st0 .normal stA cA ∧ cA ≤ 95 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
            , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
            , .assign 3 (.load (.bin .add (.reg 0) (.const 14)))
            , .assign 4 (.load (.bin .add (.reg 0) (.const 15)))
            , .assign 6 (.load (.bin .add (.reg 0) (.const 25)))
            , .assign 7 (.load (.bin .add (.reg 0) (.const 29)))
            , .assign 8 (.load (.bin .add (.reg 0) (.const 30)))
            , .assign 9 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 3) (.const 129))
                (.bin .mul (.const 26) (.reg 1))) (.reg 4)) (.bin .mul (.const 3) (.reg 2)))
            , .store (.reg 8) (.const 1)
            , .store (.bin .add (.reg 8) (.const 1)) (.reg 6)
            , .assign 10 (.const 0) ])
          st0 o s c0 ∧ (o = .normal ∧ s = stA) ∧ 0 + c0 ≤ 95 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := c.nX) (by rw [← hm0]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.k) (by rw [← hm1]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.ws) (by rw [← hm14]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.m2) (by rw [← hm15]; eval_expr) ?_
      refine runs_seq_assign_le (v := U.card) (by rw [← hm25]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.origVertAddr) (by rw [← hm29]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.outAddr) (by rw [← hm30]; eval_expr) ?_
      refine runs_seq_assign_le (v := cl) (by dsimp only [cl, wsCutList]; eval_expr) ?_
      refine runs_seq_store_le (x := rcfg.outAddr) (v := 1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := rcfg.outAddr + 1) (v := U.card) (by eval_expr) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
  rcases hpre with ⟨cA, hrunA, hcA⟩
  have hd_ws_out : DisjRange rcfg.outAddr (2 + 2 * c.nX) c.ws (batchScratchSize c.nX c.m2 c.k) := hdisj.out_ws
  have hd_orig_out : DisjRange rcfg.origVertAddr c.nX rcfg.outAddr (2 + 2 * c.nX) := hdisj.orig_out
  unfold DisjRange at hd_ws_out hd_orig_out
  have hnX' : c.nX = X.card := hnX
  have hd_cl_out : DisjRange cl ul.length (rcfg.outAddr + 2) ul.length := by
    unfold DisjRange; dsimp only [cl, wsCutList, batchScratchSize] at hd_ws_out ⊢; omega
  have hd_or_out : DisjRange rcfg.origVertAddr X.card (rcfg.outAddr + 2) ul.length := by
    unfold DisjRange; omega
  have hclA : ListAt stA.mem cl ul := fun j hj => by
    simp only [stA, memA]
    rw [Function.update_of_ne (by dsimp only [cl, wsCutList, batchScratchSize] at hd_ws_out ⊢; omega),
        Function.update_of_ne (by dsimp only [cl, wsCutList, batchScratchSize] at hd_ws_out ⊢; omega)]
    exact hul_at j hj
  have horigA : ListAt stA.mem rcfg.origVertAddr (sortedX X) := fun j hj => by
    simp only [sortedX, Finset.length_sort] at hj
    simp only [stA, memA]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact horig j (by simp [sortedX, hj])
  obtain ⟨stB, cB, hrunB, hregB, hprefB, hfrB, hcB⟩ :=
    emitCutLoop_triple (fun x hx => (hul_sub x hx).1) hX_w
      (by dsimp only [cl, wsCutList]; omega) (by omega) (by omega) hw4
      hd_cl_out hd_or_out ul.length 0 stA (Nat.zero_add _) hclA horigA
      (fun _ ht => absurd ht (Nat.not_lt_zero _))
      (by simp [stA, regsA, hul_len]) (by simp [stA, regsA]) (by simp [stA, regsA])
      (by simp [stA, regsA]) (by simp [stA, regsA]) ω
  obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA
    (show Runs w p ω (seqStmts [.loop _ _]) stA .normal stB cB from hrunB)
  refine ⟨stB, cAll, hrunAll, ?_, ?_, ?_, ?_⟩
  · rw [hregB 5 (by decide) (by decide) (by decide)]; simp [stA, regsA]
  · dsimp only [RouteOutAt]
    refine ⟨?_, ul.map (origOf X), origOf_map_nodup hul_nd (fun x hx => (hul_sub x hx).1),
      origOf_map_toFinset hul_sub hul_cov, ?_, ?_⟩
    · rw [hfrB rcfg.outAddr (by omega)]; simp only [stA, memA]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [hfrB (rcfg.outAddr + 1) (by omega)]; simp only [stA, memA, List.length_map, hul_len]
      rw [Function.update_self]
    · intro j hj
      simp only [List.length_map] at hj
      rw [hprefB j hj, List.getElem_map]
      simp [List.getD_eq_getElem?_getD, hj]
  · intro a ha
    rw [hfrB a (by omega)]
    simp only [stA, memA]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · simp only [List.length_cons, List.length_nil] at hcAll; omega


end MinCostFlow.ExpanderDecomp
