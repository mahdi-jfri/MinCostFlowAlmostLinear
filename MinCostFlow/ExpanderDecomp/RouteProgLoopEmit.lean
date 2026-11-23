module

public import MinCostFlow.ExpanderDecomp.RouteProgLoopCutEmit

/-!
# Matched Output Serialization for Procedure 5 (`RouteProgLoopEmit`)

Verifies `emitPathListLoopStmt`, `emitChunkChainLoopStmt`, and `emitMatchedStmt`: traverses the
`k` accumulated chunk chains (`ChunkChainAt` → `PathListAt`), translating endpoints via
`origVertAddr` and copying `SeqAt` walk pointers from `pathHeap`, to write both
`RouteOutAt st'.mem rcfg.outAddr (mkMatchedResult acc)` and
`WalksAt st'.mem rcfg.walksAddr acc.flatten.length ...` in `≤ 120 * total + 40 * k + 120` steps.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Matched Serialization (`emitPathList_triple`, `emitChunkChain_triple`, `emitMatched_triple`) -/

private lemma emitPathList_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pLo pHi origAddr outAddr walksAddr nX : ℕ}
    (hnX : nX = X.card) (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hw_hp : pHi + 10 < 2 ^ w) (hw_orig : origAddr + nX + 5 < 2 ^ w)
    (hw_out : outAddr + 2 + 2 * nX + 5 < 2 ^ w)
    (hw_walks : walksAddr + 1 + nX + 5 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hd_orig_out : DisjRange origAddr nX outAddr (2 + 2 * nX))
    (hd_orig_walks : DisjRange origAddr nX walksAddr (1 + nX))
    (hd_out_hp : DisjRange outAddr (2 + 2 * nX) pLo (pHi - pLo))
    (hd_walks_hp : DisjRange walksAddr (1 + nX) pLo (pHi - pLo))
    (hd_out_walks : DisjRange outAddr (2 + 2 * nX) walksAddr (1 + nX))
    (hp_le : pLo ≤ pHi)
    (ps : List ((ℕ × ℕ) × List ℕ)) :
    ∀ (head cnt : ℕ) (st0 : State),
      cnt + ps.length ≤ nX →
      PathListAt st0.mem X pLo pHi head ps →
      ListAt st0.mem origAddr (sortedX X) →
      st0.regs 7 = origAddr → st0.regs 8 = outAddr → st0.regs 9 = walksAddr →
      st0.regs 10 = cnt → st0.regs 13 = head →
      ∀ ω, ∃ st1 c1,
        Runs w p ω emitPathListLoopStmt st0 .normal st1 c1 ∧
        (∀ r, r ≠ 10 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → st1.regs r = st0.regs r) ∧
        st1.regs 10 = cnt + ps.length ∧
        (∀ j (hj : j < ps.length),
          st1.mem (outAddr + 2 + 2 * (cnt + j)) = (ps[j]'hj).1.1 ∧
          st1.mem (outAddr + 2 + 2 * (cnt + j) + 1) = (ps[j]'hj).1.2 ∧
          pLo ≤ st1.mem (walksAddr + 1 + (cnt + j)) ∧
          st1.mem (walksAddr + 1 + (cnt + j)) + 1 + (ps[j]'hj).2.length ≤ pHi ∧
          SeqAt st1.mem (st1.mem (walksAddr + 1 + (cnt + j))) (ps[j]'hj).2) ∧
        (∀ a, ¬ ((outAddr + 2 + 2 * cnt ≤ a ∧ a < outAddr + 2 + 2 * (cnt + ps.length)) ∨
                 (walksAddr + 1 + cnt ≤ a ∧ a < walksAddr + 1 + (cnt + ps.length))) →
          st1.mem a = st0.mem a) ∧
        c1 ≤ 80 * ps.length + 10 := by
  induction ps with
  | nil =>
    intro head cnt st0 _ hpl _ _ _ _ hr10 hr13 ω
    have hh0 : head = 0 := hpl
    have hcond0 : (Expr.bin .lt (.const 0) (.reg 13)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr13, hh0, show 0 < 2 ^ w by omega]
    refine ⟨st0, _, batch_runs_loop_zero hcond0, fun _ _ _ _ _ _ _ _ => rfl, hr10,
      fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, by simp [Expr.size]⟩
  | cons q rest ih =>
    rcases q with ⟨⟨s, t⟩, es⟩
    intro head cnt st0 hcnt hpl horig hr7 hr8 hr9 hr10 hr13 ω
    simp only [List.length_cons] at hcnt
    rcases hpl with ⟨hp_lo, hp_hi, hne0, hsX, htX, hm0, hm1, hwp_lo, hwp_hi, hseq, hpl_rest⟩
    have hw_ne : w ≠ 0 := by intro h0; subst h0; simp at hw4
    have hcond1 : (Expr.bin .lt (.const 0) (.reg 13)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr13, show 0 < 2 ^ w by omega, show 0 < head by omega, hw_ne]
    set sLoc := locOf X s; set tLoc := locOf X t
    set wPtr := st0.mem (head + 2); set nxt := st0.mem (head + 3)
    have hsLoc_lt : sLoc < X.card := locOf_lt hsX
    have htLoc_lt : tLoc < X.card := locOf_lt htX
    have horig_s : st0.mem (origAddr + sLoc) = s := by
      have h1 := horig sLoc (by simp [sortedX, hsLoc_lt])
      rw [sortedX_getElem_eq_origOf hsLoc_lt, origOf_locOf hsX] at h1; exact h1
    have horig_t : st0.mem (origAddr + tLoc) = t := by
      have h1 := horig tLoc (by simp [sortedX, htLoc_lt])
      rw [sortedX_getElem_eq_origOf htLoc_lt, origOf_locOf htX] at h1; exact h1
    have hs_w : s < 2 ^ w := hX_w s hsX
    have ht_w : t < 2 ^ w := hX_w t htX
    have hnxt_w : nxt < 2 ^ w := by
      cases rest with
      | nil => have : nxt = 0 := hpl_rest; omega
      | cons r _ => rcases r with ⟨⟨_, _⟩, _⟩; have := hpl_rest.2.1; omega
    set regs1 := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update st0.regs 14 sLoc) 15 tLoc) 16 wPtr) 17 s) 18 t) 10 (cnt + 1)) 13 nxt
    set mem1 := Function.update (Function.update (Function.update st0.mem
      (outAddr + 2 + 2 * cnt) s) (outAddr + 3 + 2 * cnt) t) (walksAddr + 1 + cnt) wPtr
    set st1 : State := { mem := mem1, regs := regs1, pos := st0.pos }
    have hbody : ∃ cB,
        Runs w p ω
          (seqStmts
            [ .assign 14 (.load (.reg 13))
            , .assign 15 (.load (.bin .add (.reg 13) (.const 1)))
            , .assign 16 (.load (.bin .add (.reg 13) (.const 2)))
            , .assign 17 (.load (.bin .add (.reg 7) (.reg 14)))
            , .assign 18 (.load (.bin .add (.reg 7) (.reg 15)))
            , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.bin .mul (.const 2) (.reg 10))) (.reg 17)
            , .store (.bin .add (.bin .add (.reg 8) (.const 3)) (.bin .mul (.const 2) (.reg 10))) (.reg 18)
            , .store (.bin .add (.bin .add (.reg 9) (.const 1)) (.reg 10)) (.reg 16)
            , .assign 10 (.bin .add (.reg 10) (.const 1))
            , .assign 13 (.load (.bin .add (.reg 13) (.const 3))) ])
          st0 .normal st1 cB ∧ cB ≤ 72 := by
      have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
      have hne_nxt_1 : head + 3 ≠ outAddr + 2 + 2 * cnt := by unfold DisjRange at hd_out_hp; omega
      have hne_nxt_2 : head + 3 ≠ outAddr + 3 + 2 * cnt := by unfold DisjRange at hd_out_hp; omega
      have hne_nxt_3 : head + 3 ≠ walksAddr + 1 + cnt := by unfold DisjRange at hd_walks_hp; omega
      have h0 : ∃ o s0 c0,
          Runs w p ω
            (seqStmts
              [ .assign 14 (.load (.reg 13))
              , .assign 15 (.load (.bin .add (.reg 13) (.const 1)))
              , .assign 16 (.load (.bin .add (.reg 13) (.const 2)))
              , .assign 17 (.load (.bin .add (.reg 7) (.reg 14)))
              , .assign 18 (.load (.bin .add (.reg 7) (.reg 15)))
              , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.bin .mul (.const 2) (.reg 10))) (.reg 17)
              , .store (.bin .add (.bin .add (.reg 8) (.const 3)) (.bin .mul (.const 2) (.reg 10))) (.reg 18)
              , .store (.bin .add (.bin .add (.reg 9) (.const 1)) (.reg 10)) (.reg 16)
              , .assign 10 (.bin .add (.reg 10) (.const 1))
              , .assign 13 (.load (.bin .add (.reg 13) (.const 3))) ])
            st0 o s0 c0 ∧ (o = .normal ∧ s0 = st1) ∧ 0 + c0 ≤ 72 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := sLoc) (by rw [← hm0]; eval_expr) ?_
        refine runs_seq_assign_le (v := tLoc) (by rw [← hm1]; eval_expr) ?_
        refine runs_seq_assign_le (v := wPtr) (by eval_expr) ?_
        refine runs_seq_assign_le (v := s) (by rw [← horig_s]; eval_expr) ?_
        refine runs_seq_assign_le (v := t) (by rw [← horig_t]; eval_expr) ?_
        refine runs_seq_store_le (x := outAddr + 2 + 2 * cnt) (v := s) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := outAddr + 3 + 2 * cnt) (v := t) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := walksAddr + 1 + cnt) (v := wPtr) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_assign_le (v := cnt + 1) (by eval_expr) ?_
        refine runs_assign_le (v := nxt)
          (by simp [Expr.eval, BinOp.eval, hr13, show 3 < 2 ^ w by omega, show head + 3 < 2 ^ w by omega,
               Function.update_of_ne hne_nxt_3, Function.update_of_ne hne_nxt_2,
               Function.update_of_ne hne_nxt_1, nxt]) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cB, h, ⟨rfl, rfl⟩, hcB⟩; exact ⟨cB, h, by omega⟩
    rcases hbody with ⟨cB, hrunB, hcB⟩
    have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
    have hmem1_hp : ∀ a, pLo ≤ a → a < pHi → st1.mem a = st0.mem a := fun a ha1 ha2 => by
      simp only [st1, mem1]
      rw [Function.update_of_ne (by unfold DisjRange at hd_walks_hp; omega),
          Function.update_of_ne (by unfold DisjRange at hd_out_hp; omega),
          Function.update_of_ne (by unfold DisjRange at hd_out_hp; omega)]
    have hmem1_orig : ∀ j < (sortedX X).length, st1.mem (origAddr + j) = st0.mem (origAddr + j) := fun j hj => by
      simp only [sortedX, Finset.length_sort] at hj
      simp only [st1, mem1]
      rw [Function.update_of_ne (by unfold DisjRange at hd_orig_walks; omega),
          Function.update_of_ne (by unfold DisjRange at hd_orig_out; omega),
          Function.update_of_ne (by unfold DisjRange at hd_orig_out; omega)]
    obtain ⟨st2, c2, hrun2, hreg2, hr10_2, hed2, hfr2, hc2⟩ :=
      ih nxt (cnt + 1) st1 (by omega) (hpl_rest.congr hmem1_hp)
        (fun j hj => (hmem1_orig j hj).trans (horig j hj))
        (by simp [st1, regs1, hr7]) (by simp [st1, regs1, hr8]) (by simp [st1, regs1, hr9])
        (by simp [st1, regs1]) (by simp [st1, regs1]) ω
    refine ⟨st2, _, batch_runs_loop_step hcond1 (by decide) hrunB hrun2, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h10 h13 h14 h15 h16 h17 h18
      rw [hreg2 r h10 h13 h14 h15 h16 h17 h18]
      simp [st1, regs1, h10, h13, h14, h15, h16, h17, h18]
    · simp only [List.length_cons] at hr10_2 ⊢; omega
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        have hfr_o1 : st2.mem (outAddr + 2 + 2 * cnt) = st1.mem (outAddr + 2 + 2 * cnt) :=
          hfr2 _ (by unfold DisjRange at hd_out_walks; omega)
        have hfr_o2 : st2.mem (outAddr + 2 + 2 * cnt + 1) = st1.mem (outAddr + 2 + 2 * cnt + 1) :=
          hfr2 _ (by unfold DisjRange at hd_out_walks; omega)
        have hfr_w : st2.mem (walksAddr + 1 + cnt) = st1.mem (walksAddr + 1 + cnt) :=
          hfr2 _ (by unfold DisjRange at hd_out_walks; omega)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hfr_o1]; simp only [st1, mem1]
          rw [Function.update_of_ne (by unfold DisjRange at hd_out_walks; omega),
              Function.update_of_ne (by omega), Function.update_self]
        · rw [hfr_o2, show outAddr + 2 + 2 * cnt + 1 = outAddr + 3 + 2 * cnt by omega]; simp only [st1, mem1]
          rw [Function.update_of_ne (by unfold DisjRange at hd_out_walks; omega), Function.update_self]
        · rw [hfr_w]; simp only [st1, mem1]; rw [Function.update_self]; exact hwp_lo
        · rw [hfr_w]; simp only [st1, mem1]; rw [Function.update_self]; exact hwp_hi
        · rw [hfr_w]; simp only [st1, mem1]; rw [Function.update_self]
          exact ⟨(hfr2 wPtr (by unfold DisjRange at hd_out_hp hd_walks_hp; omega)).trans
            ((hmem1_hp wPtr hwp_lo (by omega)).trans hseq.1),
            fun idx hidx => (hfr2 (wPtr + 1 + idx) (by unfold DisjRange at hd_out_hp hd_walks_hp; omega)).trans
              ((hmem1_hp (wPtr + 1 + idx) (by omega) (by omega)).trans (hseq.2 idx hidx))⟩
      | succ j' =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
        have h := hed2 j' hj
        rwa [show cnt + 1 + j' = cnt + (j' + 1) by omega] at h
    · intro a ha
      rw [hfr2 a (by simp only [List.length_cons] at ha; omega)]
      simp only [st1, mem1]
      rw [Function.update_of_ne (by simp only [List.length_cons] at ha; omega),
          Function.update_of_ne (by simp only [List.length_cons] at ha; omega),
          Function.update_of_ne (by simp only [List.length_cons] at ha; omega)]
    · simp only [List.length_cons, Expr.size] at hcB hc2 ⊢; omega

private lemma emitChunkChain_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pLo pHi cLo cHi origAddr outAddr walksAddr nX : ℕ}
    (hnX : nX = X.card) (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hw_hp : pHi + 10 < 2 ^ w) (hw_ch : cHi + 10 < 2 ^ w) (hw_orig : origAddr + nX + 5 < 2 ^ w)
    (hw_out : outAddr + 2 + 2 * nX + 5 < 2 ^ w)
    (hw_walks : walksAddr + 1 + nX + 5 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hd_orig_out : DisjRange origAddr nX outAddr (2 + 2 * nX))
    (hd_orig_walks : DisjRange origAddr nX walksAddr (1 + nX))
    (hd_out_hp : DisjRange outAddr (2 + 2 * nX) pLo (pHi - pLo))
    (hd_walks_hp : DisjRange walksAddr (1 + nX) pLo (pHi - pLo))
    (hd_out_ch : DisjRange outAddr (2 + 2 * nX) cLo (cHi - cLo))
    (hd_walks_ch : DisjRange walksAddr (1 + nX) cLo (cHi - cLo))
    (hd_out_walks : DisjRange outAddr (2 + 2 * nX) walksAddr (1 + nX))
    (hp_le : pLo ≤ pHi) (hc_le : cLo ≤ cHi)
    (chunks : List (List ((ℕ × ℕ) × List ℕ))) :
    ∀ (head tail cnt : ℕ) (st0 : State),
      cnt + chunks.flatten.length ≤ nX →
      ChunkChainAt st0.mem X pLo pHi cLo cHi head tail chunks →
      ListAt st0.mem origAddr (sortedX X) →
      st0.regs 7 = origAddr → st0.regs 8 = outAddr → st0.regs 9 = walksAddr →
      st0.regs 10 = cnt → st0.regs 12 = head →
      ∀ ω, ∃ st1 c1,
        Runs w p ω emitChunkChainLoopStmt st0 .normal st1 c1 ∧
        (∀ r, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → st1.regs r = st0.regs r) ∧
        st1.regs 10 = cnt + chunks.flatten.length ∧
        (∀ j (hj : j < chunks.flatten.length),
          st1.mem (outAddr + 2 + 2 * (cnt + j)) = (chunks.flatten[j]'hj).1.1 ∧
          st1.mem (outAddr + 2 + 2 * (cnt + j) + 1) = (chunks.flatten[j]'hj).1.2 ∧
          pLo ≤ st1.mem (walksAddr + 1 + (cnt + j)) ∧
          st1.mem (walksAddr + 1 + (cnt + j)) + 1 + (chunks.flatten[j]'hj).2.length ≤ pHi ∧
          SeqAt st1.mem (st1.mem (walksAddr + 1 + (cnt + j))) (chunks.flatten[j]'hj).2) ∧
        (∀ a, ¬ ((outAddr + 2 + 2 * cnt ≤ a ∧ a < outAddr + 2 + 2 * (cnt + chunks.flatten.length)) ∨
                 (walksAddr + 1 + cnt ≤ a ∧ a < walksAddr + 1 + (cnt + chunks.flatten.length))) →
          st1.mem a = st0.mem a) ∧
        c1 ≤ 120 * chunks.flatten.length + 10 := by
  induction chunks with
  | nil =>
    intro head tail cnt st0 _ hcc _ _ _ _ hr10 hr12 ω
    have hh0 : head = 0 := hcc.1
    have hcond0 : (Expr.bin .lt (.const 0) (.reg 12)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr12, hh0, show 0 < 2 ^ w by omega]
    refine ⟨st0, _, batch_runs_loop_zero hcond0, fun _ _ _ _ _ _ _ _ _ => rfl, hr10,
      fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, by simp [Expr.size]⟩
  | cons ps rest ih =>
    intro head tail cnt st0 hcnt hcc horig hr7 hr8 hr9 hr10 hr12 ω
    have hw_ne : w ≠ 0 := by intro h0; subst h0; simp at hw4
    have hprops : cLo ≤ head ∧ head + 2 ≤ cHi ∧ head ≠ 0 ∧ ps ≠ [] ∧
        PathListAt st0.mem X pLo pHi (st0.mem head) ps ∧
        ChunkChainAt st0.mem X pLo pHi cLo cHi (st0.mem (head + 1)) (if rest = [] then 0 else tail) rest := by
      cases rest with
      | nil =>
        rcases hcc with ⟨_, h1, h2, h3, h4, h5, h6⟩
        exact ⟨h1, h2, h3, h4, h5, h6, rfl⟩
      | cons qs rest' =>
        rcases hcc with ⟨h1, h2, h3, h4, h5, _, _, h6⟩
        exact ⟨h1, h2, h3, h4, h5, h6⟩
    rcases hprops with ⟨hc_lo', hc_hi', hne0, hps_ne, hpl, hcc_rest⟩
    have hps_pos : 1 ≤ ps.length := by cases ps with | nil => exact absurd rfl hps_ne | cons _ _ => simp
    have hcond1 : (Expr.bin .lt (.const 0) (.reg 12)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr12, show 0 < 2 ^ w by omega, show 0 < head by omega, hw_ne]
    set pHead := st0.mem head
    have hpHead_w : pHead < 2 ^ w := by
      cases ps with
      | nil => exact absurd rfl hps_ne
      | cons q _ => rcases q with ⟨⟨_, _⟩, _⟩; have := hpl.2.1; omega
    set stA : State := { st0 with regs := Function.update st0.regs 13 pHead }
    have hrunA : ∃ cA, Runs w p ω (.assign 13 (.load (.reg 12))) st0 .normal stA cA ∧ cA ≤ 8 := by
      have h0 : ∃ o s c0, Runs w p ω (.assign 13 (.load (.reg 12))) st0 o s c0 ∧
          (o = .normal ∧ s = stA) ∧ 0 + c0 ≤ 8 :=
        runs_assign_le (v := pHead) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
    rcases hrunA with ⟨cA, hrunA, hcA⟩
    obtain ⟨stB, cB, hrunB, hregB, hr10_B, hedB, hfrB, hcB⟩ :=
      emitPathList_triple hnX hX_w hw_hp hw_orig hw_out hw_walks hw4
        hd_orig_out hd_orig_walks hd_out_hp hd_walks_hp hd_out_walks hp_le ps pHead cnt stA
        (by simp only [List.flatten_cons, List.length_append] at hcnt; omega) hpl horig
        (by simp [stA, hr7]) (by simp [stA, hr8]) (by simp [stA, hr9])
        (by simp [stA, hr10]) (by simp [stA]) ω
    have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
    have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' hc_le
    have hmemB_hp : ∀ a, pLo ≤ a → a < pHi → stB.mem a = st0.mem a := fun a ha1 ha2 =>
      hfrB a (by unfold DisjRange at hd_out_hp hd_walks_hp; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
    have hmemB_ch : ∀ a, cLo ≤ a → a < cHi → stB.mem a = st0.mem a := fun a ha1 ha2 =>
      hfrB a (by unfold DisjRange at hd_out_ch hd_walks_ch; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
    have hmemB_orig : ListAt stB.mem origAddr (sortedX X) := fun j hj => by
      simp only [sortedX, Finset.length_sort] at hj
      exact (hfrB (origAddr + j) (by unfold DisjRange at hd_orig_out hd_orig_walks; simp only [List.flatten_cons, List.length_append] at hcnt; omega)).trans
        (horig j (by simp [sortedX, hj]))
    set nxtChunk := st0.mem (head + 1)
    have hnxtC_w : nxtChunk < 2 ^ w := by
      cases rest with
      | nil => have : nxtChunk = 0 := hcc_rest.1; omega
      | cons qs rest' =>
        cases rest' with
        | nil => have := hcc_rest.2.2.1; omega
        | cons _ _ => have := hcc_rest.2.1; omega
    have hr12_B : stB.regs 12 = head := (hregB 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr12])
    set stC : State := { stB with regs := Function.update stB.regs 12 nxtChunk }
    have hrunC : ∃ cC, Runs w p ω (.assign 12 (.load (.bin .add (.reg 12) (.const 1)))) stB .normal stC cC ∧ cC ≤ 10 := by
      have hmb : stB.mem (head + 1) = nxtChunk := hmemB_ch (head + 1) (by omega) (by omega)
      have h0 : ∃ o s c0, Runs w p ω (.assign 12 (.load (.bin .add (.reg 12) (.const 1)))) stB o s c0 ∧
          (o = .normal ∧ s = stC) ∧ 0 + c0 ≤ 10 :=
        runs_assign_le (v := nxtChunk) (by rw [← hmb]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cC, h, ⟨rfl, rfl⟩, hcC⟩; exact ⟨cC, h, by omega⟩
    rcases hrunC with ⟨cC, hrunC, hcC⟩
    have hrunBody : Runs w p ω (seqStmts [.assign 13 (.load (.reg 12)), emitPathListLoopStmt,
        .assign 12 (.load (.bin .add (.reg 12) (.const 1)))]) st0 .normal stC (cA + (cB + cC + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stA, cA, _, hrunA, runs_seq_iff.mpr (Or.inr ⟨stB, cB, cC, hrunB, hrunC, rfl⟩), rfl⟩)
    obtain ⟨stD, cD, hrunD, hregD, hr10_D, hedD, hfrD, hcD⟩ :=
      ih nxtChunk (if rest = [] then 0 else tail) (cnt + ps.length) stC
        (by simp only [List.flatten_cons, List.length_append] at hcnt; omega)
        (hcc_rest.congr hmemB_hp hmemB_ch) hmemB_orig
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr7]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr8]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr9]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact hr10_B)
        (by simp [stC]) ω
    refine ⟨stD, _, batch_runs_loop_step hcond1 (by decide) hrunBody hrunD, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h10 h12 h13 h14 h15 h16 h17 h18
      rw [hregD r h10 h12 h13 h14 h15 h16 h17 h18]
      simp only [stC]; rw [Function.update_of_ne h12]
      rw [hregB r h10 h13 h14 h15 h16 h17 h18]; simp [stA, h13]
    · simp only [List.flatten_cons, List.length_append] at hr10_D ⊢; omega
    · intro j hj
      simp only [List.flatten_cons, List.length_append] at hj ⊢
      by_cases hjp : j < ps.length
      · have he := hedB j hjp
        simp only [List.getElem_append_left hjp]
        have hfr1 : stD.mem (outAddr + 2 + 2 * (cnt + j)) = stB.mem (outAddr + 2 + 2 * (cnt + j)) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
        have hfr2 : stD.mem (outAddr + 2 + 2 * (cnt + j) + 1) = stB.mem (outAddr + 2 + 2 * (cnt + j) + 1) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
        have hfr3 : stD.mem (walksAddr + 1 + (cnt + j)) = stB.mem (walksAddr + 1 + (cnt + j)) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
        have hmemD_hp : ∀ a, pLo ≤ a → a < pHi → stD.mem a = stB.mem a := fun a ha1 ha2 =>
          hfrD a (by unfold DisjRange at hd_out_hp hd_walks_hp; simp only [List.flatten_cons, List.length_append] at hcnt; omega)
        refine ⟨hfr1.trans he.1, hfr2.trans he.2.1, hfr3 ▸ he.2.2.1, hfr3 ▸ he.2.2.2.1, ?_⟩
        rw [hfr3]
        exact ⟨(hmemD_hp _ he.2.2.1 (by omega)).trans he.2.2.2.2.1,
          fun idx hidx => (hmemD_hp _ (by omega) (by omega)).trans (he.2.2.2.2.2 idx hidx)⟩
      · have hj' : j - ps.length < rest.flatten.length := by omega
        have he := hedD (j - ps.length) hj'
        simp only [List.getElem_append_right (Nat.le_of_not_lt hjp)]
        rwa [show cnt + ps.length + (j - ps.length) = cnt + j by omega] at he
    · intro a ha
      simp only [List.flatten_cons, List.length_append] at ha
      exact (hfrD a (by omega)).trans (hfrB a (by omega))
    · simp only [List.flatten_cons, List.length_append, Expr.size] at hcA hcB hcC hcD ⊢; omega

private lemma emitMatchedLoop_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pLo pHi cLo cHi accHeadAddr origAddr outAddr walksAddr nX k : ℕ}
    {accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))}
    (hnX : nX = X.card) (hk : k = accChunks.length)
    (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hw_ah : accHeadAddr + k + 5 < 2 ^ w)
    (hw_hp : pHi + 10 < 2 ^ w) (hw_ch : cHi + 10 < 2 ^ w) (hw_orig : origAddr + nX + 5 < 2 ^ w)
    (hw_out : outAddr + 2 + 2 * nX + 5 < 2 ^ w)
    (hw_walks : walksAddr + 1 + nX + 5 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hd_orig_out : DisjRange origAddr nX outAddr (2 + 2 * nX))
    (hd_orig_walks : DisjRange origAddr nX walksAddr (1 + nX))
    (hd_out_ah : DisjRange outAddr (2 + 2 * nX) accHeadAddr k)
    (hd_walks_ah : DisjRange walksAddr (1 + nX) accHeadAddr k)
    (hd_out_hp : DisjRange outAddr (2 + 2 * nX) pLo (pHi - pLo))
    (hd_walks_hp : DisjRange walksAddr (1 + nX) pLo (pHi - pLo))
    (hd_out_ch : DisjRange outAddr (2 + 2 * nX) cLo (cHi - cLo))
    (hd_walks_ch : DisjRange walksAddr (1 + nX) cLo (cHi - cLo))
    (hd_out_walks : DisjRange outAddr (2 + 2 * nX) walksAddr (1 + nX))
    (hp_le : pLo ≤ pHi) (hc_le : cLo ≤ cHi)
    (rem : ℕ) :
    ∀ (j cnt : ℕ) (st0 : State),
      j + rem = k →
      let tailFlat := ((accChunks.map List.flatten).drop j).flatten
      cnt + tailFlat.length ≤ nX →
      (∀ idx (_hidx : idx < k), ∃ tailPtr,
        ChunkChainAt st0.mem X pLo pHi cLo cHi (st0.mem (accHeadAddr + idx)) tailPtr (accChunks.getD idx [])) →
      ListAt st0.mem origAddr (sortedX X) →
      st0.regs 2 = k → st0.regs 6 = accHeadAddr →
      st0.regs 7 = origAddr → st0.regs 8 = outAddr → st0.regs 9 = walksAddr →
      st0.regs 10 = cnt → st0.regs 11 = j →
      ∀ ω, ∃ st1 c1,
        Runs w p ω
          (.loop (.bin .lt (.reg 11) (.reg 2))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
              , emitChunkChainLoopStmt
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          st0 .normal st1 c1 ∧
        (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 →
          st1.regs r = st0.regs r) ∧
        st1.regs 10 = cnt + tailFlat.length ∧
        (∀ t (ht : t < tailFlat.length),
          st1.mem (outAddr + 2 + 2 * (cnt + t)) = (tailFlat[t]'ht).1.1 ∧
          st1.mem (outAddr + 2 + 2 * (cnt + t) + 1) = (tailFlat[t]'ht).1.2 ∧
          pLo ≤ st1.mem (walksAddr + 1 + (cnt + t)) ∧
          st1.mem (walksAddr + 1 + (cnt + t)) + 1 + (tailFlat[t]'ht).2.length ≤ pHi ∧
          SeqAt st1.mem (st1.mem (walksAddr + 1 + (cnt + t))) (tailFlat[t]'ht).2) ∧
        (∀ a, ¬ ((outAddr + 2 + 2 * cnt ≤ a ∧ a < outAddr + 2 + 2 * (cnt + tailFlat.length)) ∨
                 (walksAddr + 1 + cnt ≤ a ∧ a < walksAddr + 1 + (cnt + tailFlat.length))) →
          st1.mem a = st0.mem a) ∧
        c1 ≤ 125 * tailFlat.length + 35 * rem + 10 := by
  induction rem with
  | zero =>
    intro j cnt st0 hj tailFlat _ _ _ hr2 _ _ _ _ hr10 hr11 ω
    have hj_eq : j = k := by omega
    have htf : tailFlat = [] := by
      dsimp only [tailFlat]; rw [List.drop_eq_nil_iff.mpr (by simp [← hk, hj_eq])]; rfl
    have hcond0 : (Expr.bin .lt (.reg 11) (.reg 2)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr11, hr2, show ¬ j < k by omega]
    refine ⟨st0, _, batch_runs_loop_zero hcond0, fun _ _ _ _ _ _ _ _ _ _ => rfl, by simp [htf, hr10],
      fun _ ht => by simp [htf] at ht, fun _ _ => rfl, by simp [Expr.size]⟩
  | succ rem ih =>
    intro j cnt st0 hj tailFlat hcnt hch horig hr2 hr6 hr7 hr8 hr9 hr10 hr11 ω
    have hjlt : j < k := by omega
    have hj_ac : j < accChunks.length := by omega
    have hw_ne : w ≠ 0 := by intro h0; subst h0; simp at hw4
    have hcond1 : (Expr.bin .lt (.reg 11) (.reg 2)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr11, hr2, hjlt, hw_ne]
    set cj := accChunks.getD j []
    have hdrop_eq : (accChunks.map List.flatten).drop j =
        cj.flatten :: (accChunks.map List.flatten).drop (j + 1) := by
      have hj_map : j < (accChunks.map List.flatten).length := by simp [hj_ac]
      rw [List.drop_eq_getElem_cons hj_map, List.getElem_map]
      simp [cj, List.getD_eq_getElem?_getD, hj_ac]
    have htf_eq : tailFlat = cj.flatten ++ ((accChunks.map List.flatten).drop (j + 1)).flatten := by
      dsimp only [tailFlat]; rw [hdrop_eq, List.flatten_cons]
    obtain ⟨tailPtr, hcc_j⟩ := hch j hjlt
    set headPtr := st0.mem (accHeadAddr + j)
    have hhead_w : headPtr < 2 ^ w := by
      change ChunkChainAt st0.mem X pLo pHi cLo cHi headPtr tailPtr cj at hcc_j
      cases hcj : cj with
      | nil => rw [hcj] at hcc_j; have : headPtr = 0 := hcc_j.1; omega
      | cons ps rest =>
        rw [hcj] at hcc_j
        cases rest with
        | nil => have := hcc_j.2.2.1; omega
        | cons _ _ => have := hcc_j.2.1; omega
    set stA : State := { st0 with regs := Function.update st0.regs 12 headPtr }
    have hrunA : ∃ cA, Runs w p ω (.assign 12 (.load (.bin .add (.reg 6) (.reg 11)))) st0 .normal stA cA ∧ cA ≤ 10 := by
      have h0 : ∃ o s c0, Runs w p ω (.assign 12 (.load (.bin .add (.reg 6) (.reg 11)))) st0 o s c0 ∧
          (o = .normal ∧ s = stA) ∧ 0 + c0 ≤ 10 :=
        runs_assign_le (v := headPtr) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
    rcases hrunA with ⟨cA, hrunA, hcA⟩
    obtain ⟨stB, cB, hrunB, hregB, hr10_B, hedB, hfrB, hcB⟩ :=
      emitChunkChain_triple (p := p) hnX hX_w hw_hp hw_ch hw_orig hw_out hw_walks hw4
        hd_orig_out hd_orig_walks hd_out_hp hd_walks_hp hd_out_ch hd_walks_ch hd_out_walks
        hp_le hc_le cj headPtr tailPtr cnt stA
        (by rw [htf_eq, List.length_append] at hcnt; omega) hcc_j horig
        (by simp [stA, hr7]) (by simp [stA, hr8]) (by simp [stA, hr9])
        (by simp [stA, hr10]) (by simp [stA]) ω
    have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
    have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' hc_le
    have hmemB_hp : ∀ a, pLo ≤ a → a < pHi → stB.mem a = st0.mem a := fun a ha1 ha2 =>
      hfrB a (by unfold DisjRange at hd_out_hp hd_walks_hp; rw [htf_eq, List.length_append] at hcnt; omega)
    have hmemB_ch : ∀ a, cLo ≤ a → a < cHi → stB.mem a = st0.mem a := fun a ha1 ha2 =>
      hfrB a (by unfold DisjRange at hd_out_ch hd_walks_ch; rw [htf_eq, List.length_append] at hcnt; omega)
    have hmemB_ah : ∀ idx < k, stB.mem (accHeadAddr + idx) = st0.mem (accHeadAddr + idx) := fun idx hidx =>
      hfrB _ (by unfold DisjRange at hd_out_ah hd_walks_ah; rw [htf_eq, List.length_append] at hcnt; omega)
    have hmemB_orig : ListAt stB.mem origAddr (sortedX X) := fun idx hidx => by
      simp only [sortedX, Finset.length_sort] at hidx
      exact (hfrB _ (by unfold DisjRange at hd_orig_out hd_orig_walks; rw [htf_eq, List.length_append] at hcnt; omega)).trans
        (horig idx (by simp [sortedX, hidx]))
    have hr11_B : stB.regs 11 = j :=
      (hregB 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr11])
    set stC : State := { stB with regs := Function.update stB.regs 11 (j + 1) }
    have hrunC : ∃ cC, Runs w p ω (.assign 11 (.bin .add (.reg 11) (.const 1))) stB .normal stC cC ∧ cC ≤ 8 := by
      have h0 : ∃ o s c0, Runs w p ω (.assign 11 (.bin .add (.reg 11) (.const 1))) stB o s c0 ∧
          (o = .normal ∧ s = stC) ∧ 0 + c0 ≤ 8 :=
        runs_assign_le (v := j + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cC, h, ⟨rfl, rfl⟩, hcC⟩; exact ⟨cC, h, by omega⟩
    rcases hrunC with ⟨cC, hrunC, hcC⟩
    have hrunBody : Runs w p ω (seqStmts [.assign 12 (.load (.bin .add (.reg 6) (.reg 11))),
        emitChunkChainLoopStmt, .assign 11 (.bin .add (.reg 11) (.const 1))]) st0 .normal stC (cA + (cB + cC + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stA, cA, _, hrunA, runs_seq_iff.mpr (Or.inr ⟨stB, cB, cC, hrunB, hrunC, rfl⟩), rfl⟩)
    obtain ⟨stD, cD, hrunD, hregD, hr10_D, hedD, hfrD, hcD⟩ :=
      ih (j + 1) (cnt + cj.flatten.length) stC (by omega)
        (by rw [htf_eq, List.length_append] at hcnt; omega)
        (fun idx hidx => by
          obtain ⟨tp, hcc⟩ := hch idx hidx
          exact ⟨tp, by rw [show stC.mem _ = stB.mem _ from rfl, hmemB_ah idx hidx]; exact hcc.congr hmemB_hp hmemB_ch⟩)
        hmemB_orig
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr2]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr6]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr7]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr8]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact (hregB 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, hr9]))
        (by simp only [stC]; rw [Function.update_of_ne (by decide)]; exact hr10_B)
        (by simp [stC]) ω
    refine ⟨stD, _, batch_runs_loop_step hcond1 (by decide) hrunBody hrunD, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h10 h11 h12 h13 h14 h15 h16 h17 h18
      rw [hregD r h10 h11 h12 h13 h14 h15 h16 h17 h18]
      simp only [stC]; rw [Function.update_of_ne h11]
      rw [hregB r h10 h12 h13 h14 h15 h16 h17 h18]; simp [stA, h12]
    · rw [htf_eq, List.length_append]; omega
    · intro t ht
      have ht' : t < (cj.flatten ++ ((accChunks.map List.flatten).drop (j + 1)).flatten).length := by
        rw [← htf_eq]; exact ht
      have hget_eq : (tailFlat[t]'ht) =
          (cj.flatten ++ ((accChunks.map List.flatten).drop (j + 1)).flatten)[t]'ht' := by
        congr 1
      rw [hget_eq]
      by_cases htc : t < cj.flatten.length
      · have he := hedB t htc
        simp only [List.getElem_append_left htc]
        have hfr1 : stD.mem (outAddr + 2 + 2 * (cnt + t)) = stB.mem (outAddr + 2 + 2 * (cnt + t)) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; rw [htf_eq, List.length_append] at hcnt; omega)
        have hfr2 : stD.mem (outAddr + 2 + 2 * (cnt + t) + 1) = stB.mem (outAddr + 2 + 2 * (cnt + t) + 1) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; rw [htf_eq, List.length_append] at hcnt; omega)
        have hfr3 : stD.mem (walksAddr + 1 + (cnt + t)) = stB.mem (walksAddr + 1 + (cnt + t)) :=
          hfrD _ (by unfold DisjRange at hd_out_walks; rw [htf_eq, List.length_append] at hcnt; omega)
        have hmemD_hp : ∀ a, pLo ≤ a → a < pHi → stD.mem a = stB.mem a := fun a ha1 ha2 =>
          hfrD a (by unfold DisjRange at hd_out_hp hd_walks_hp; rw [htf_eq, List.length_append] at hcnt; omega)
        refine ⟨hfr1.trans he.1, hfr2.trans he.2.1, hfr3 ▸ he.2.2.1, hfr3 ▸ he.2.2.2.1, ?_⟩
        rw [hfr3]
        exact ⟨(hmemD_hp _ he.2.2.1 (by omega)).trans he.2.2.2.2.1,
          fun idx hidx => (hmemD_hp _ (by omega) (by omega)).trans (he.2.2.2.2.2 idx hidx)⟩
      · have ht2 : t - cj.flatten.length < ((accChunks.map List.flatten).drop (j + 1)).flatten.length := by
          rw [List.length_append] at ht'; omega
        have he := hedD (t - cj.flatten.length) ht2
        simp only [List.getElem_append_right (Nat.le_of_not_lt htc)]
        rwa [show cnt + cj.flatten.length + (t - cj.flatten.length) = cnt + t by omega] at he
    · intro a ha
      rw [htf_eq, List.length_append] at ha
      exact (hfrD a (by omega)).trans (hfrB a (by omega))
    · rw [htf_eq, List.length_append]; simp only [Expr.size] at hcA hcB hcC hcD ⊢; omega

/-- Verification of `emitMatchedStmt`: writes `RouteOutAt` at `outAddr` and `WalksAt` at
`walksAddr` for `mkMatchedResult (accChunks.map List.flatten)` in
`≤ 120 * total + 40 * k + 120` steps, preserving `reg 5` and modifying only
`[outAddr, outAddr + 2 + 2*total)` and `[walksAddr, walksAddr + 1 + total)`. -/
theorem emitMatched_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    {accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))}
    (hnX : rcfg.batch.nX = X.card) (hk : rcfg.batch.k = accChunks.length)
    (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    (hp_le : pLo ≤ pHi) (hc_le : cLo ≤ cHi)
    (htot_le : (accChunks.map List.flatten).flatten.length ≤ X.card)
    {st0 : State}
    (hm1 : st0.mem (cfgAddr + 1) = rcfg.batch.k)
    (hm12 : st0.mem (cfgAddr + 12) = rcfg.batch.accHeadAddr)
    (hm29 : st0.mem (cfgAddr + 29) = rcfg.origVertAddr)
    (hm30 : st0.mem (cfgAddr + 30) = rcfg.outAddr)
    (hm31 : st0.mem (cfgAddr + 31) = rcfg.walksAddr)
    (hch : ∀ j (_hj : j < rcfg.batch.k), ∃ tailPtr,
      ChunkChainAt st0.mem X pLo pHi cLo cHi (st0.mem (rcfg.batch.accHeadAddr + j)) tailPtr (accChunks.getD j []))
    (horig : ListAt st0.mem rcfg.origVertAddr (sortedX X))
    (hr0 : st0.regs 0 = cfgAddr) :
    let acc := accChunks.map List.flatten
    let res := mkMatchedResult acc
    ∀ ω, ∃ st1 c1,
      Runs w p ω emitMatchedStmt st0 .normal st1 c1 ∧
      st1.regs 5 = st0.regs 5 ∧
      RouteOutAt st1.mem rcfg.outAddr res ∧
      WalksAt st1.mem rcfg.walksAddr acc.flatten.length (fun idx => (acc.flatten.getD idx ((0, 0), [])).2) ∧
      (∀ idx (hidx : idx < acc.flatten.length),
        pLo ≤ st1.mem (rcfg.walksAddr + 1 + idx) ∧
        st1.mem (rcfg.walksAddr + 1 + idx) + 1 + (acc.flatten[idx]'hidx).2.length ≤ pHi) ∧
      (∀ a, ¬ ((rcfg.outAddr ≤ a ∧ a < rcfg.outAddr + 2 + 2 * acc.flatten.length) ∨
               (rcfg.walksAddr ≤ a ∧ a < rcfg.walksAddr + 1 + acc.flatten.length)) →
        st1.mem a = st0.mem a) ∧
      c1 ≤ 130 * acc.flatten.length + 40 * rcfg.batch.k + 120 := by
  intro acc res ω
  set c := rcfg.batch
  have htot_le' : acc.flatten.length ≤ c.nX := by rw [hnX]; exact htot_le
  have hw_cfg := hdisj.w_cfg; have hw_ah : c.accHeadAddr + c.k + 5 < 2 ^ w := hdisj.w_ah
  have hw_orig : rcfg.origVertAddr + c.nX + 5 < 2 ^ w := hdisj.w_orig
  have hw_out : rcfg.outAddr + 2 + 2 * c.nX + 5 < 2 ^ w := hdisj.w_out
  have hw_walks : rcfg.walksAddr + 1 + c.nX + 5 < 2 ^ w := hdisj.w_walks
  have hw_k : c.k + 5 < 2 ^ w := hdisj.w_k; have hw4 := hdisj.w_4
  set regsA := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update st0.regs 2 c.k) 6 c.accHeadAddr) 7 rcfg.origVertAddr)
    8 rcfg.outAddr) 9 rcfg.walksAddr) 10 0) 11 0
  set stA : State := { st0 with regs := regsA }
  have hpre : ∃ cA,
      Runs w p ω
        (seqStmts
          [ .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
          , .assign 6 (.load (.bin .add (.reg 0) (.const 12)))
          , .assign 7 (.load (.bin .add (.reg 0) (.const 29)))
          , .assign 8 (.load (.bin .add (.reg 0) (.const 30)))
          , .assign 9 (.load (.bin .add (.reg 0) (.const 31)))
          , .assign 10 (.const 0)
          , .assign 11 (.const 0) ])
        st0 .normal stA cA ∧ cA ≤ 55 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
            , .assign 6 (.load (.bin .add (.reg 0) (.const 12)))
            , .assign 7 (.load (.bin .add (.reg 0) (.const 29)))
            , .assign 8 (.load (.bin .add (.reg 0) (.const 30)))
            , .assign 9 (.load (.bin .add (.reg 0) (.const 31)))
            , .assign 10 (.const 0)
            , .assign 11 (.const 0) ])
          st0 o s c0 ∧ (o = .normal ∧ s = stA) ∧ 0 + c0 ≤ 55 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := c.k) (by rw [← hm1]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.accHeadAddr) (by rw [← hm12]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.origVertAddr) (by rw [← hm29]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.outAddr) (by rw [← hm30]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.walksAddr) (by rw [← hm31]; eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
  rcases hpre with ⟨cA, hrunA, hcA⟩
  obtain ⟨stB, cB, hrunB, hregB, hr10_B, hedB, hfrB, hcB⟩ :=
    emitMatchedLoop_triple hnX hk hX_w hdisj.w_ah hdisj.w_hp hdisj.w_ch hdisj.w_orig
      hdisj.w_out hdisj.w_walks hw4 hdisj.orig_out hdisj.orig_walks hdisj.out_ah hdisj.walks_ah
      hdisj.out_hp hdisj.walks_hp hdisj.out_ch hdisj.walks_ch hdisj.out_walks hp_le hc_le
      c.k 0 0 stA (Nat.zero_add _) (by simpa only [List.drop_zero, Nat.zero_add] using htot_le') hch horig
      (by simp [stA, regsA, c]) (by simp [stA, regsA, c]) (by simp [stA, regsA])
      (by simp [stA, regsA]) (by simp [stA, regsA]) (by simp [stA, regsA]) (by simp [stA, regsA]) ω
  simp only [List.drop_zero, Nat.zero_add] at hr10_B hedB hfrB hcB
  have hr8_B : stB.regs 8 = rcfg.outAddr :=
    (hregB 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, regsA])
  have hr9_B : stB.regs 9 = rcfg.walksAddr :=
    (hregB 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, regsA])
  have hcnt_w : acc.flatten.length < 2 ^ w := by omega
  set memC := Function.update (Function.update (Function.update stB.mem rcfg.outAddr 0)
    (rcfg.outAddr + 1) acc.flatten.length) rcfg.walksAddr acc.flatten.length
  set stC : State := { stB with mem := memC }
  have hpost : ∃ cC,
      Runs w p ω
        (seqStmts
          [ .store (.reg 8) (.const 0)
          , .store (.bin .add (.reg 8) (.const 1)) (.reg 10)
          , .store (.reg 9) (.reg 10) ])
        stB .normal stC cC ∧ cC ≤ 30 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .store (.reg 8) (.const 0)
            , .store (.bin .add (.reg 8) (.const 1)) (.reg 10)
            , .store (.reg 9) (.reg 10) ])
          stB o s c0 ∧ (o = .normal ∧ s = stC) ∧ 0 + c0 ≤ 30 := by
      dsimp only [seqStmts]
      refine runs_seq_store_le (x := rcfg.outAddr) (v := 0) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := rcfg.outAddr + 1) (v := acc.flatten.length) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := rcfg.walksAddr) (v := acc.flatten.length) (by eval_expr) (by eval_expr)
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cC, h, ⟨rfl, rfl⟩, hcC⟩; exact ⟨cC, h, by omega⟩
  rcases hpost with ⟨cC, hrunC, hcC⟩
  have hrunBC : Runs w p ω (seqStmts [.loop (.bin .lt (.reg 11) (.reg 2))
      (seqStmts [.assign 12 (.load (.bin .add (.reg 6) (.reg 11))), emitChunkChainLoopStmt,
        .assign 11 (.bin .add (.reg 11) (.const 1))]),
      .store (.reg 8) (.const 0), .store (.bin .add (.reg 8) (.const 1)) (.reg 10),
      .store (.reg 9) (.reg 10)]) stA .normal stC (cB + cC + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stB, cB, cC, hrunB, hrunC, rfl⟩)
  obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA hrunBC
  have hd_ow : DisjRange rcfg.outAddr (2 + 2 * c.nX) rcfg.walksAddr (1 + c.nX) := hdisj.out_walks
  have hd_ohp : DisjRange rcfg.outAddr (2 + 2 * c.nX) pLo (pHi - pLo) := hdisj.out_hp
  have hd_whp : DisjRange rcfg.walksAddr (1 + c.nX) pLo (pHi - pLo) := hdisj.walks_hp
  unfold DisjRange at hd_ow hd_ohp hd_whp
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
  have hmemC_eq_B : ∀ a, a ≠ rcfg.outAddr → a ≠ rcfg.outAddr + 1 → a ≠ rcfg.walksAddr → stC.mem a = stB.mem a :=
    fun a h1 h2 h3 => by simp only [stC, memC]; rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  refine ⟨stC, cAll, hrunAll, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hregB 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [stA, regsA])
  · dsimp only [res, mkMatchedResult, RouteOutAt]
    rw [flatten_map_prod_fst]
    refine ⟨?_, ?_, ?_⟩
    · simp only [stC, memC]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · simp only [stC, memC, List.length_map]; rw [Function.update_of_ne (by omega), Function.update_self]
    · intro idx hidx
      simp only [List.length_map] at hidx
      have he := hedB idx hidx
      rw [List.getElem_map, hmemC_eq_B _ (by omega) (by omega) (by omega),
          hmemC_eq_B _ (by omega) (by omega) (by omega)]
      exact ⟨he.1, he.2.1⟩
  · refine ⟨by simp only [stC, memC]; rw [Function.update_self], fun idx hidx => ?_⟩
    have he := hedB idx hidx
    rw [hmemC_eq_B _ (by omega) (by omega) (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    have hwp1 := he.2.2.1; have hwp2 := he.2.2.2.1
    exact ⟨(hmemC_eq_B _ (by omega) (by omega) (by omega)).trans he.2.2.2.2.1,
      fun t ht => by
        dsimp only [acc] at ht
        exact (hmemC_eq_B _ (by omega) (by omega) (by omega)).trans (he.2.2.2.2.2 t ht)⟩
  · intro idx hidx
    have he := hedB idx hidx
    rw [hmemC_eq_B _ (by omega) (by omega) (by omega)]
    exact ⟨he.2.2.1, he.2.2.2.1⟩
  · intro a ha
    rw [hmemC_eq_B a (by omega) (by omega) (by omega)]
    exact hfrB a (by dsimp only [acc] at ha; omega)
  · dsimp only [acc]; simp only [List.length_cons, List.length_nil] at hcAll; omega

end MinCostFlow.ExpanderDecomp

