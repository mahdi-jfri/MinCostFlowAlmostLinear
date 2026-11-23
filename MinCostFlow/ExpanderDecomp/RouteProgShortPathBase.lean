module

public import MinCostFlow.ExpanderDecomp.RouteProgShortPathSpec

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short-Path Blocking Sub-Triples (`RouteProgShortPathBase`)

Verifies the helper sub-statements of `shortPathBlockProc`: `spLoadCfg_triple`,
`spInitFilter_triple`, `spIsolateLoop_triple`, `spFilterInPlace_triple`, and `spWriteRet_triple`.
Definitions, pure lemmas, and disjointness live in `RouteProgShortPathSpec.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. Helper Sub-Triples -/

private lemma spLoadCfg_step {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {i cfgAddr : ℕ} {f mem0 : ℕ → ℕ} {st : State} {rest : Stmt} {P : Outcome → State → Prop} {c1 : ℕ}
    (hw : cfgAddr + 24 < 2 ^ w) (hi : i ≤ 11)
    (hm : st.mem = mem0) (hregs : ∀ r ≤ i, st.regs r = f r) (hf0 : f 0 = cfgAddr)
    (hmem : mem0 (cfgAddr + i) = f (i + 1))
    (hrest : ∀ st1 : State, st1.mem = mem0 → (∀ r ≤ i + 1, st1.regs r = f r) →
      ∃ o st' c, Runs w p ω rest st1 o st' c ∧ P o st' ∧ c ≤ c1) :
    ∃ o st' c,
      Runs w p ω (.seq (.assign (i + 1) (.load (.bin .add (.reg 0) (.const i)))) rest) st o st' c ∧
      P o st' ∧ c ≤ c1 + 7 := by
  have hr0 : st.regs 0 = cfgAddr := (hregs 0 (Nat.zero_le _)).trans hf0
  have hev : (Expr.load (.bin .add (.reg 0) (.const i))).eval w st = some (f (i + 1)) := by
    simp [Expr.eval, BinOp.eval, hr0, show i < 2 ^ w by omega, show cfgAddr + i < 2 ^ w by omega, hm, hmem]
  have ha : Runs w p ω (.assign (i + 1) (.load (.bin .add (.reg 0) (.const i)))) st .normal
      { st with regs := Function.update st.regs (i + 1) (f (i + 1)) }
      ((Expr.load (.bin .add (.reg 0) (.const i))).size + 1) :=
    runs_assign_iff.mpr ⟨f (i + 1), hev, rfl, rfl, rfl⟩
  have hregs1 : ∀ r ≤ i + 1, (Function.update st.regs (i + 1) (f (i + 1))) r = f r := by
    intro r hr
    by_cases h : r = i + 1
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hregs r (by omega)
  obtain ⟨o, st', c, hrun, hp, hle⟩ :=
    hrest { st with regs := Function.update st.regs (i + 1) (f (i + 1)) } hm hregs1
  refine ⟨o, st', _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha, hrun, rfl⟩), hp, ?_⟩
  simp only [Expr.size]; omega

theorem spLoadCfg_triple {w : ℕ} {p : Program}
    {cfg : SpCfg} {cfgAddr : ℕ} {st0 : State}
    (hcfg : SpCfgAt st0.mem cfgAddr cfg)
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 24 < 2 ^ w) :
    Triple w p (fun st => st = st0) spLoadCfgStmt
      (normalPost fun st1 =>
        st1.mem = st0.mem ∧
        ∀ r ≤ 12, st1.regs r =
          match r with
          | 0 => cfgAddr | 1 => cfg.bfsCfgAddr | 2 => cfg.dfsCfgAddr
          | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
          | 5 => cfg.usedListAddr | 6 => cfg.sBufAddr
          | 7 => cfg.srcInPtr | 8 => cfg.srcInLen
          | 9 => cfg.d | 10 => cfg.bfsGenIn | 11 => cfg.dfsGenIn | _ => cfg.heapIn)
      (fun _ => 95) := by
  let f : ℕ → ℕ := fun r =>
    match r with
    | 0 => cfgAddr | 1 => cfg.bfsCfgAddr | 2 => cfg.dfsCfgAddr
    | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
    | 5 => cfg.usedListAddr | 6 => cfg.sBufAddr
    | 7 => cfg.srcInPtr | 8 => cfg.srcInLen
    | 9 => cfg.d | 10 => cfg.bfsGenIn | 11 => cfg.dfsGenIn | _ => cfg.heapIn
  rcases hcfg with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩
  wram_enter; subst st; dsimp only; simp only [Nat.zero_add]; unfold spLoadCfgStmt; dsimp only [seqStmts]
  have hr0' : ∀ r ≤ 0, st0.regs r = f r := fun r hr => by
    have : r = 0 := by omega
    subst this; exact hr0
  refine spLoadCfg_step (f := f) hw_cfg (by decide) rfl hr0' rfl hc0 (c1 := 88) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc1 (c1 := 81) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc2 (c1 := 74) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc3 (c1 := 67) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc4 (c1 := 60) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc5 (c1 := 53) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc6 (c1 := 46) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc7 (c1 := 39) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc8 (c1 := 32) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc9 (c1 := 25) (fun s hm hr => ?_)
  refine spLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc10 (c1 := 18) (fun s hm hr => ?_)
  have hs0 : s.regs 0 = cfgAddr := hr 0 (by decide)
  have hev12 : (Expr.load (.bin .add (.reg 0) (.const 11))).eval w s = some (f 12) := by
    simp [Expr.eval, BinOp.eval, hs0, show 11 < 2 ^ w by omega, show cfgAddr + 11 < 2 ^ w by omega,
      hm, hc11, f]
  refine ⟨.normal, { s with regs := Function.update s.regs 12 (f 12) }, _,
    runs_assign_iff.mpr ⟨f 12, hev12, rfl, rfl, rfl⟩, ⟨hm, fun r hr' => ?_⟩, ?_⟩
  · dsimp only
    by_cases h : r = 12
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hr r (by omega)
  · simp only [Expr.size]; omega

theorem spInitFilter_triple {w : ℕ} {p : Program}
    {X V S : Finset ℕ} {spCfg : SpCfg} {st0 : State}
    (hSX : S ⊆ X)
    (hsrc_list : ListAt st0.mem spCfg.srcInPtr ((S.sort (· ≤ ·)).map (locOf X)))
    (hsrc_len : spCfg.srcInLen = S.card)
    (hmask : ∀ v < X.card, st0.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V)
    (hdisj_ms : DisjRange spCfg.maskArrAddr X.card spCfg.sBufAddr X.card)
    (hdisj_ss : DisjRange spCfg.sBufAddr X.card spCfg.srcInPtr spCfg.srcInLen)
    (hw_mask : spCfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_sbuf : spCfg.sBufAddr + X.card + 5 < 2 ^ w)
    (hw_src : spCfg.srcInPtr + spCfg.srcInLen + 5 < 2 ^ w)
    (hw_mb : spCfg.maskBadVal < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr3 : st0.regs 3 = spCfg.maskArrAddr)
    (hr4 : st0.regs 4 = spCfg.maskBadVal)
    (hr6 : st0.regs 6 = spCfg.sBufAddr)
    (hr7 : st0.regs 7 = spCfg.srcInPtr)
    (hr8 : st0.regs 8 = spCfg.srcInLen) :
    Triple w p (fun st => st = st0) spInitFilterStmt
      (normalPost fun st' =>
        (∀ r ≤ 12, st'.regs r = st0.regs r) ∧
        st'.regs 14 = (S ∩ V).card ∧
        ListAt st'.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) ∧
        (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st'.mem a = st0.mem a))
      (fun _ => 45 * S.card + 20) := by
  set sl := S.sort (· ≤ ·) with hsl_def
  have hsl_len : sl.length = S.card := Finset.length_sort _
  have hfilt_eq : sl.filter (fun x => decide (x ∈ V)) = (S ∩ V).sort (· ≤ ·) :=
    sort_filter_eq_inter_sort S V
  have hS_le_X : S.card ≤ X.card := Finset.card_le_card hSX
  wram_enter; subst st
  unfold spInitFilterStmt; dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 14 0) 21 0
      pos := st0.pos }
  have hloop :
      Triple w p
        (fun st =>
          (∀ r ≤ 12, st.regs r = st0.regs r) ∧
          st.regs 21 ≤ sl.length ∧
          st.regs 14 = ((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).length ∧
          ListAt st.mem spCfg.sBufAddr
            (((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).map (locOf X)) ∧
          (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a))
        (.loop (.bin .lt (.reg 21) (.reg 8))
          (seqStmts
            [ .assign 22 (.load (.bin .add (.reg 7) (.reg 21)))
            , .cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4))
                .nop
                (seqStmts
                  [ .store (.bin .add (.reg 6) (.reg 14)) (.reg 22)
                  , .assign 14 (.bin .add (.reg 14) (.const 1)) ])
            , .assign 21 (.bin .add (.reg 21) (.const 1)) ]))
        (normalPost fun st =>
          (∀ r ≤ 12, st.regs r = st0.regs r) ∧
          st.regs 14 = (S ∩ V).card ∧
          ListAt st.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) ∧
          (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 21) (.reg 8)).size + 38 + 1) * (sl.length - st.regs 21) +
          (Expr.bin .lt (.reg 21) (.reg 8)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => sl.length - st.regs 21)
      (condVal := fun st => if st.regs 21 < sl.length then 1 else 0)
      (bodyBound := 38) ?_ ?_ ?_
    · intro st ⟨hrr, h21_le, _, _, _⟩
      have h8 : st.regs 8 = sl.length := by rw [hrr 8 (by decide), hr8, hsrc_len, hsl_len]
      eval_expr
    · intro st ⟨hrr, h21_le, h14_eq, hlat, hfr⟩ hv
      have h21_eq : st.regs 21 = sl.length := by split_ifs at hv; omega
      rw [h21_eq, List.take_length, hfilt_eq, Finset.length_sort] at h14_eq
      rw [h21_eq, List.take_length, hfilt_eq] at hlat
      exact ⟨hrr, h14_eq, hlat, hfr⟩
    · intro stL ⟨hrr, h21_le, h14_eq, hlat, hfr⟩ hv
      have h21_lt : stL.regs 21 < sl.length := by split_ifs at hv <;> omega
      have h3 : stL.regs 3 = spCfg.maskArrAddr := (hrr 3 (by decide)).trans hr3
      have h4 : stL.regs 4 = spCfg.maskBadVal := (hrr 4 (by decide)).trans hr4
      have h6 : stL.regs 6 = spCfg.sBufAddr := (hrr 6 (by decide)).trans hr6
      have h7 : stL.regs 7 = spCfg.srcInPtr := (hrr 7 (by decide)).trans hr7
      set x := sl[stL.regs 21]'h21_lt
      have hxS : x ∈ S := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h21_lt)
      have hxX : x ∈ X := hSX hxS
      have hx_loc_lt : locOf X x < X.card := locOf_lt hxX
      have hsrc_mem : stL.mem (spCfg.srcInPtr + stL.regs 21) = locOf X x := by
        rw [hfr _ (by rcases hdisj_ss with h | h <;> omega)]
        have hl := hsrc_list (stL.regs 21) (by simp [h21_lt])
        rw [List.getElem_map] at hl; exact hl
      have hmask_mem : stL.mem (spCfg.maskArrAddr + locOf X x) = st0.mem (spCfg.maskArrAddr + locOf X x) :=
        hfr _ (by rcases hdisj_ms with h | h <;> omega)
      have h14_le : stL.regs 14 ≤ stL.regs 21 := by
        rw [h14_eq]
        exact (List.length_filter_le _ _).trans (by simp)
      have htake_succ : sl.take (stL.regs 21 + 1) = sl.take (stL.regs 21) ++ [x] :=
        List.take_succ_eq_append_getElem h21_lt
      have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_assign_le (v := locOf X x) (by rw [← hsrc_mem]; eval_expr) ?_
      set stA : State := { stL with regs := Function.update stL.regs 22 (locOf X x) }
      by_cases hxV : x ∈ V
      · have hneq : st0.mem (spCfg.maskArrAddr + locOf X x) ≠ spCfg.maskBadVal := by
          have := (hmask (locOf X x) hx_loc_lt).mpr (by rwa [origOf_locOf hxX])
          exact this
        have hev_cond :
            (Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)).eval w stA = some 0 := by
          simp [Expr.eval, BinOp.eval, stA, h3, h4, show spCfg.maskArrAddr + locOf X x < 2 ^ w by omega,
            hmask_mem, hneq]
        have hcond : ∃ stB c1,
            Runs w p ω
              (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)) .nop
                (seqStmts
                  [ .store (.bin .add (.reg 6) (.reg 14)) (.reg 22)
                  , .assign 14 (.bin .add (.reg 14) (.const 1)) ]))
              stA .normal stB c1 ∧
            stB = { stA with
              mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 14) (locOf X x)
              regs := Function.update stA.regs 14 (stL.regs 14 + 1) } ∧
            c1 ≤ 24 := by
          have hbranch : ∃ o st' c,
              Runs w p ω
                (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)) .nop
                  (seqStmts
                    [ .store (.bin .add (.reg 6) (.reg 14)) (.reg 22)
                    , .assign 14 (.bin .add (.reg 14) (.const 1)) ]))
                stA o st' c ∧
              (o = .normal ∧ st' = { stA with
                mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 14) (locOf X x)
                regs := Function.update stA.regs 14 (stL.regs 14 + 1) }) ∧
              0 + c ≤ 24 := by
            refine runs_cond_zero_le hev_cond ?_
            dsimp only [seqStmts]
            refine runs_seq_store_le (x := spCfg.sBufAddr + stL.regs 14) (v := locOf X x)
              (by eval_expr) (by eval_expr) ?_
            refine runs_assign_le (v := stL.regs 14 + 1)
              (by eval_expr) ?_ (by wram_cost)
            exact ⟨rfl, rfl⟩
          rcases hbranch with ⟨_, stB, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
          exact ⟨_, c1, hrun, rfl, by omega⟩
        rcases hcond with ⟨stB, c1, hrun1, rfl, hc1⟩
        have hstep2 : ∃ o st' c2,
            Runs w p ω (.assign 21 (.bin .add (.reg 21) (.const 1)))
              { stA with
                mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 14) (locOf X x)
                regs := Function.update stA.regs 14 (stL.regs 14 + 1) } o st' c2 ∧
            normalPost (fun st =>
              ((∀ r ≤ 12, st.regs r = st0.regs r) ∧
                st.regs 21 ≤ sl.length ∧
                st.regs 14 = ((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).length ∧
                ListAt st.mem spCfg.sBufAddr
                  (((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).map (locOf X)) ∧
                (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a)) ∧
              sl.length - st.regs 21 < sl.length - stL.regs 21) o st' ∧
            0 + c2 ≤ 6 := by
          refine runs_assign_le (v := stL.regs 21 + 1)
            (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨?_, by simp [stA]; omega, ?_, ?_, ?_⟩, by simp [stA]; omega⟩
          · intro r hr; simp [stA, Function.update_of_ne (by omega : r ≠ 21),
              Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 22), hrr r hr]
          · simp only [stA, Function.update_self, Function.update_of_ne (by decide : (14 : ℕ) ≠ 21),
              htake_succ, List.filter_append, List.filter_cons, decide_eq_true hxV, ↓reduceIte,
              List.filter_nil, List.length_append, List.length_singleton]
            omega
          · intro j hj
            have hfe : (sl.take (stL.regs 21 + 1)).filter (fun x => decide (x ∈ V)) =
                (sl.take (stL.regs 21)).filter (fun x => decide (x ∈ V)) ++ [x] := by
              simp [htake_succ, hxV]
            simp only [stA, Function.update_self, hfe, List.map_append, List.map_singleton,
              List.length_append, List.length_map, List.length_singleton] at hj ⊢
            by_cases hje : j = stL.regs 14
            · subst hje
              simp only [Function.update_self]
              rw [List.getElem_append_right (by simp [h14_eq])]
              simp
            · have hjlt : j < stL.regs 14 := by omega
              rw [Function.update_of_ne (by omega)]
              rw [List.getElem_append_left (by simp; omega)]
              exact hlat j (by simp; omega)
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hfr a ha
        rcases hstep2 with ⟨o, st', c2, hrun2, hp2, hc2⟩
        exact ⟨o, st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨_, c1, c2, hrun1, hrun2, rfl⟩), hp2,
          by simp only [Expr.size]; omega⟩
      · have heq : st0.mem (spCfg.maskArrAddr + locOf X x) = spCfg.maskBadVal := by
          by_contra hne
          have := (hmask (locOf X x) hx_loc_lt).mp hne
          rw [origOf_locOf hxX] at this; exact hxV this
        have hev_cond :
            (Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)).eval w stA = some 1 := by
          simp [Expr.eval, BinOp.eval, stA, h3, h4, show spCfg.maskArrAddr + locOf X x < 2 ^ w by omega,
            hmask_mem, heq, hw_ne]
        have hrun1 : Runs w p ω
            (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)) .nop
              (seqStmts
                [ .store (.bin .add (.reg 6) (.reg 14)) (.reg 22)
                , .assign 14 (.bin .add (.reg 14) (.const 1)) ]))
            stA .normal stA ((Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4)).size + 1 + 1) :=
          runs_cond_iff.mpr ⟨1, 1, hev_cond, by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), rfl⟩
        have hstep2 : ∃ o st' c2,
            Runs w p ω (.assign 21 (.bin .add (.reg 21) (.const 1))) stA o st' c2 ∧
            normalPost (fun st =>
              ((∀ r ≤ 12, st.regs r = st0.regs r) ∧
                st.regs 21 ≤ sl.length ∧
                st.regs 14 = ((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).length ∧
                ListAt st.mem spCfg.sBufAddr
                  (((sl.take (st.regs 21)).filter (fun x => decide (x ∈ V))).map (locOf X)) ∧
                (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a)) ∧
              sl.length - st.regs 21 < sl.length - stL.regs 21) o st' ∧
            0 + c2 ≤ 6 := by
          refine runs_assign_le (v := stL.regs 21 + 1)
            (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨?_, by simp [stA]; omega, ?_, ?_, hfr⟩, by simp [stA]; omega⟩
          · intro r hr; simp [stA, Function.update_of_ne (by omega : r ≠ 21),
              Function.update_of_ne (by omega : r ≠ 22), hrr r hr]
          · simp only [stA, Function.update_self, Function.update_of_ne (by decide : (14 : ℕ) ≠ 21),
              Function.update_of_ne (by decide : (14 : ℕ) ≠ 22),
              htake_succ, List.filter_append, List.filter_cons, decide_eq_false hxV,
              Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
            exact h14_eq
          · simp only [stA, Function.update_self, htake_succ, List.filter_append, List.filter_cons,
              decide_eq_false hxV, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
            exact hlat
        rcases hstep2 with ⟨o, st', c2, hrun2, hp2, hc2⟩
        exact ⟨o, st', _, runs_seq_iff.mpr (Or.inr ⟨_, _, c2, hrun1, hrun2, rfl⟩), hp2,
          by simp only [Expr.size]; omega⟩
  obtain ⟨o, st', c, hrun, hpost, hc⟩ :=
    hloop st1 ω ⟨fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 21),
      Function.update_of_ne (by omega : r ≠ 14)], Nat.zero_le _, by simp [st1],
      fun j hj => by simp [st1] at hj, fun _ _ => rfl⟩
  cases o with
  | returned _ => exact hpost.elim
  | normal =>
    refine ⟨.normal, st', c, hrun, hpost, ?_⟩
    simp only [Expr.size, st1, Function.update_self, hsl_len] at hc ⊢; omega

theorem spIsolateLoop_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {U : Finset ℕ} {ul : List ℕ} {spCfg : SpCfg} {st0 : State}
    (hul_len : ul.length = U.card)
    (hul_sub : ∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U)
    (hul_cov : ∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul)
    (hul_at : ListAt st0.mem spCfg.usedListAddr ul)
    (hdisj_mu : DisjRange spCfg.maskArrAddr X.card spCfg.usedListAddr X.card)
    (hw_mask : spCfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_ul : spCfg.usedListAddr + X.card + 5 < 2 ^ w)
    (_hw_mb : spCfg.maskBadVal < 2 ^ w)
    (hw_nX : X.card + 5 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr3 : st0.regs 3 = spCfg.maskArrAddr)
    (hr4 : st0.regs 4 = spCfg.maskBadVal)
    (hr5 : st0.regs 5 = spCfg.usedListAddr)
    (hr24 : st0.regs 24 = U.card) :
    Triple w p (fun st => st = st0) spIsolateLoopStmt
      (normalPost fun st' =>
        (∀ r ≤ 25, st'.regs r = st0.regs r) ∧
        (∀ v < X.card, origOf X v ∈ U → st'.mem (spCfg.maskArrAddr + v) = spCfg.maskBadVal) ∧
        (∀ v < X.card, origOf X v ∉ U → st'.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v)) ∧
        (∀ a, a < spCfg.maskArrAddr ∨ spCfg.maskArrAddr + X.card ≤ a → st'.mem a = st0.mem a))
      (fun _ => 30 * U.card + 15) := by
  have hU_le_X : U.card ≤ X.card := by
    have hsub : U ⊆ X := fun v hv => (hul_cov v hv).1
    exact Finset.card_le_card hsub
  wram_enter; subst st
  unfold spIsolateLoopStmt; dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st1 : State := { st0 with regs := Function.update st0.regs 26 0 }
  have hloop :
      Triple w p
        (fun st =>
          (∀ r ≤ 25, st.regs r = st0.regs r) ∧
          st.regs 26 ≤ ul.length ∧
          (∀ v < X.card, v ∈ ul.take (st.regs 26) → st.mem (spCfg.maskArrAddr + v) = spCfg.maskBadVal) ∧
          (∀ v < X.card, v ∉ ul.take (st.regs 26) →
            st.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v)) ∧
          (∀ a, a < spCfg.maskArrAddr ∨ spCfg.maskArrAddr + X.card ≤ a → st.mem a = st0.mem a))
        (.loop (.bin .lt (.reg 26) (.reg 24))
          (seqStmts
            [ .assign 27 (.load (.bin .add (.reg 5) (.reg 26)))
            , .store (.bin .add (.reg 3) (.reg 27)) (.reg 4)
            , .assign 26 (.bin .add (.reg 26) (.const 1)) ]))
        (normalPost fun st =>
          (∀ r ≤ 25, st.regs r = st0.regs r) ∧
          (∀ v < X.card, origOf X v ∈ U → st.mem (spCfg.maskArrAddr + v) = spCfg.maskBadVal) ∧
          (∀ v < X.card, origOf X v ∉ U → st.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v)) ∧
          (∀ a, a < spCfg.maskArrAddr ∨ spCfg.maskArrAddr + X.card ≤ a → st.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 26) (.reg 24)).size + 24 + 1) * (ul.length - st.regs 26) +
          (Expr.bin .lt (.reg 26) (.reg 24)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => ul.length - st.regs 26)
      (condVal := fun st => if st.regs 26 < ul.length then 1 else 0)
      (bodyBound := 24) ?_ ?_ ?_
    · intro st ⟨hrr, h26_le, _, _, _⟩
      have h24 : st.regs 24 = ul.length := by rw [hrr 24 (by decide), hr24, hul_len]
      eval_expr
    · intro st ⟨hrr, h26_le, hset, hkeep, hfr⟩ hv
      have h26_eq : st.regs 26 = ul.length := by split_ifs at hv; omega
      rw [h26_eq, List.take_length] at hset hkeep
      refine ⟨hrr, ?_, ?_, hfr⟩
      · intro v hv hu
        have hloc : locOf X (origOf X v) ∈ ul := (hul_cov (origOf X v) hu).2
        rw [locOf_origOf hv] at hloc
        exact hset v hv hloc
      · intro v hv hu
        apply hkeep v hv
        intro hmem; exact hu (hul_sub v hmem).2
    · intro stL ⟨hrr, h26_le, hset, hkeep, hfr⟩ hv
      have h26_lt : stL.regs 26 < ul.length := by split_ifs at hv <;> omega
      have h3 : stL.regs 3 = spCfg.maskArrAddr := (hrr 3 (by decide)).trans hr3
      have h4 : stL.regs 4 = spCfg.maskBadVal := (hrr 4 (by decide)).trans hr4
      have h5 : stL.regs 5 = spCfg.usedListAddr := (hrr 5 (by decide)).trans hr5
      set u := ul[stL.regs 26]'h26_lt
      have hu_lt : u < X.card := (hul_sub u (List.getElem_mem h26_lt)).1
      have hul_mem : stL.mem (spCfg.usedListAddr + stL.regs 26) = u := by
        rw [hfr _ (by rcases hdisj_mu with h | h <;> omega)]
        exact hul_at (stL.regs 26) h26_lt
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u) (by rw [← hul_mem]; eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.maskArrAddr + u) (v := spCfg.maskBadVal)
        (by eval_expr) (by eval_expr) ?_
      refine runs_assign_le (v := stL.regs 26 + 1) (by eval_expr) ?_ (by wram_cost)
      refine ⟨⟨?_, by simp; omega, ?_, ?_, ?_⟩, by simp; omega⟩
      · intro r hr; simp [Function.update_of_ne (by omega : r ≠ 26),
          Function.update_of_ne (by omega : r ≠ 27), hrr r hr]
      · intro v hv hmem
        simp only [Function.update_self, List.take_succ_eq_append_getElem h26_lt,
          List.mem_append, List.mem_singleton] at hmem
        dsimp only
        by_cases hveq : v = u
        · subst hveq; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]
          rcases hmem with h1 | h2
          · exact hset v hv h1
          · exact absurd h2 hveq
      · intro v hv hnot
        simp only [Function.update_self, List.take_succ_eq_append_getElem h26_lt,
          List.mem_append, List.mem_singleton, not_or] at hnot
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hkeep v hv hnot.1
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
  obtain ⟨o, st', c, hrun, hpost, hc⟩ :=
    hloop st1 ω ⟨fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 26)],
      Nat.zero_le _, fun _ _ h => by simp [st1] at h, fun _ _ _ => rfl, fun _ _ => rfl⟩
  cases o with
  | returned _ => exact hpost.elim
  | normal =>
    refine ⟨.normal, st', c, hrun, hpost, ?_⟩
    simp only [Expr.size, st1, Function.update_self, hul_len] at hc ⊢; omega

theorem spFilterInPlace_triple {w : ℕ} {p : Program}
    {X V1 V2 : Finset ℕ} {S : Finset ℕ} {spCfg : SpCfg} {st0 : State}
    (hV1X : V1 ⊆ X)
    (hV2V1 : V2 ⊆ V1)
    (hsbuf_list : ListAt st0.mem spCfg.sBufAddr (((S ∩ V1).sort (· ≤ ·)).map (locOf X)))
    (hmask : ∀ v < X.card, st0.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V2)
    (hdisj_ms : DisjRange spCfg.maskArrAddr X.card spCfg.sBufAddr X.card)
    (hw_mask : spCfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_sbuf : spCfg.sBufAddr + X.card + 5 < 2 ^ w)
    (_hw_mb : spCfg.maskBadVal < 2 ^ w)
    (hw_nX : X.card + 5 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr3 : st0.regs 3 = spCfg.maskArrAddr)
    (hr4 : st0.regs 4 = spCfg.maskBadVal)
    (hr6 : st0.regs 6 = spCfg.sBufAddr)
    (hr14 : st0.regs 14 = (S ∩ V1).card) :
    Triple w p (fun st => st = st0) spFilterInPlaceStmt
      (normalPost fun st' =>
        (∀ r ≤ 25, st'.regs r = st0.regs r) ∧
        st'.regs 27 = (S ∩ V2).card ∧
        ListAt st'.mem spCfg.sBufAddr (((S ∩ V2).sort (· ≤ ·)).map (locOf X)) ∧
        (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st'.mem a = st0.mem a))
      (fun _ => 45 * (S ∩ V1).card + 20) := by
  set sl := (S ∩ V1).sort (· ≤ ·) with hsl_def
  have hsl_len : sl.length = (S ∩ V1).card := Finset.length_sort _
  have hSV1_le_X : (S ∩ V1).card ≤ X.card :=
    Finset.card_le_card (Finset.Subset.trans Finset.inter_subset_right hV1X)
  have hfilt_eq : sl.filter (fun x => decide (x ∈ V2)) = (S ∩ V2).sort (· ≤ ·) := by
    rw [hsl_def, sort_filter_eq_inter_sort, Finset.inter_assoc, Finset.inter_eq_right.mpr hV2V1]
  wram_enter; subst st
  unfold spFilterInPlaceStmt; dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 26 0) 27 0
      pos := st0.pos }
  have hloop :
      Triple w p
        (fun st =>
          (∀ r ≤ 25, st.regs r = st0.regs r) ∧
          st.regs 26 ≤ sl.length ∧
          st.regs 27 = ((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).length ∧
          ListAt st.mem spCfg.sBufAddr
            (((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).map (locOf X)) ∧
          (∀ k (hk : k < sl.length), st.regs 26 ≤ k →
            st.mem (spCfg.sBufAddr + k) = locOf X (sl[k]'hk)) ∧
          (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a))
        (.loop (.bin .lt (.reg 26) (.reg 14))
          (seqStmts
            [ .assign 28 (.load (.bin .add (.reg 6) (.reg 26)))
            , .cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4))
                .nop
                (seqStmts
                  [ .store (.bin .add (.reg 6) (.reg 27)) (.reg 28)
                  , .assign 27 (.bin .add (.reg 27) (.const 1)) ])
            , .assign 26 (.bin .add (.reg 26) (.const 1)) ]))
        (normalPost fun st =>
          (∀ r ≤ 25, st.regs r = st0.regs r) ∧
          st.regs 27 = (S ∩ V2).card ∧
          ListAt st.mem spCfg.sBufAddr (((S ∩ V2).sort (· ≤ ·)).map (locOf X)) ∧
          (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 26) (.reg 14)).size + 38 + 1) * (sl.length - st.regs 26) +
          (Expr.bin .lt (.reg 26) (.reg 14)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => sl.length - st.regs 26)
      (condVal := fun st => if st.regs 26 < sl.length then 1 else 0)
      (bodyBound := 38) ?_ ?_ ?_
    · intro st ⟨hrr, h26_le, _, _, _, _⟩
      have h14 : st.regs 14 = sl.length := by rw [hrr 14 (by decide), hr14, hsl_len]
      eval_expr
    · intro st ⟨hrr, h26_le, h27_eq, hlat, _, hfr⟩ hv
      have h26_eq : st.regs 26 = sl.length := by split_ifs at hv; omega
      rw [h26_eq, List.take_length, hfilt_eq, Finset.length_sort] at h27_eq
      rw [h26_eq, List.take_length, hfilt_eq] at hlat
      exact ⟨hrr, h27_eq, hlat, hfr⟩
    · intro stL ⟨hrr, h26_le, h27_eq, hlat, htail, hfr⟩ hv
      have h26_lt : stL.regs 26 < sl.length := by split_ifs at hv <;> omega
      have h3 : stL.regs 3 = spCfg.maskArrAddr := (hrr 3 (by decide)).trans hr3
      have h4 : stL.regs 4 = spCfg.maskBadVal := (hrr 4 (by decide)).trans hr4
      have h6 : stL.regs 6 = spCfg.sBufAddr := (hrr 6 (by decide)).trans hr6
      set x := sl[stL.regs 26]'h26_lt
      have hxV1 : x ∈ V1 := (Finset.mem_inter.mp ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h26_lt))).2
      have hxX : x ∈ X := hV1X hxV1
      have hx_loc_lt : locOf X x < X.card := locOf_lt hxX
      have hsbuf_mem : stL.mem (spCfg.sBufAddr + stL.regs 26) = locOf X x :=
        htail (stL.regs 26) h26_lt le_rfl
      have hmask_mem : stL.mem (spCfg.maskArrAddr + locOf X x) = st0.mem (spCfg.maskArrAddr + locOf X x) :=
        hfr _ (by rcases hdisj_ms with h | h <;> omega)
      have h27_le : stL.regs 27 ≤ stL.regs 26 := by
        rw [h27_eq]
        exact (List.length_filter_le _ _).trans (by simp)
      have htake_succ : sl.take (stL.regs 26 + 1) = sl.take (stL.regs 26) ++ [x] :=
        List.take_succ_eq_append_getElem h26_lt
      have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_assign_le (v := locOf X x) (by rw [← hsbuf_mem]; eval_expr) ?_
      set stA : State := { stL with regs := Function.update stL.regs 28 (locOf X x) }
      by_cases hxV2 : x ∈ V2
      · have hneq : st0.mem (spCfg.maskArrAddr + locOf X x) ≠ spCfg.maskBadVal :=
          (hmask (locOf X x) hx_loc_lt).mpr (by rwa [origOf_locOf hxX])
        have hev_cond :
            (Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)).eval w stA = some 0 := by
          simp [Expr.eval, BinOp.eval, stA, h3, h4, show spCfg.maskArrAddr + locOf X x < 2 ^ w by omega,
            hmask_mem, hneq]
        have hcond : ∃ stB c1,
            Runs w p ω
              (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)) .nop
                (seqStmts
                  [ .store (.bin .add (.reg 6) (.reg 27)) (.reg 28)
                  , .assign 27 (.bin .add (.reg 27) (.const 1)) ]))
              stA .normal stB c1 ∧
            stB = { stA with
              mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 27) (locOf X x)
              regs := Function.update stA.regs 27 (stL.regs 27 + 1) } ∧
            c1 ≤ 24 := by
          have hbranch : ∃ o st' c,
              Runs w p ω
                (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)) .nop
                  (seqStmts
                    [ .store (.bin .add (.reg 6) (.reg 27)) (.reg 28)
                    , .assign 27 (.bin .add (.reg 27) (.const 1)) ]))
                stA o st' c ∧
              (o = .normal ∧ st' = { stA with
                mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 27) (locOf X x)
                regs := Function.update stA.regs 27 (stL.regs 27 + 1) }) ∧
              0 + c ≤ 24 := by
            refine runs_cond_zero_le hev_cond ?_
            dsimp only [seqStmts]
            refine runs_seq_store_le (x := spCfg.sBufAddr + stL.regs 27) (v := locOf X x)
              (by eval_expr) (by eval_expr) ?_
            refine runs_assign_le (v := stL.regs 27 + 1)
              (by eval_expr) ?_ (by wram_cost)
            exact ⟨rfl, rfl⟩
          rcases hbranch with ⟨_, stB, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
          exact ⟨_, c1, hrun, rfl, by omega⟩
        rcases hcond with ⟨stB, c1, hrun1, rfl, hc1⟩
        have hstep2 : ∃ o st' c2,
            Runs w p ω (.assign 26 (.bin .add (.reg 26) (.const 1)))
              { stA with
                mem := Function.update stA.mem (spCfg.sBufAddr + stL.regs 27) (locOf X x)
                regs := Function.update stA.regs 27 (stL.regs 27 + 1) } o st' c2 ∧
            normalPost (fun st =>
              ((∀ r ≤ 25, st.regs r = st0.regs r) ∧
                st.regs 26 ≤ sl.length ∧
                st.regs 27 = ((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).length ∧
                ListAt st.mem spCfg.sBufAddr
                  (((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).map (locOf X)) ∧
                (∀ k (hk : k < sl.length), st.regs 26 ≤ k →
                  st.mem (spCfg.sBufAddr + k) = locOf X (sl[k]'hk)) ∧
                (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a)) ∧
              sl.length - st.regs 26 < sl.length - stL.regs 26) o st' ∧
            0 + c2 ≤ 6 := by
          refine runs_assign_le (v := stL.regs 26 + 1)
            (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨?_, by simp [stA]; omega, ?_, ?_, ?_, ?_⟩, by simp [stA]; omega⟩
          · intro r hr; simp [stA, Function.update_of_ne (by omega : r ≠ 26),
              Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 28), hrr r hr]
          · simp only [stA, Function.update_self, Function.update_of_ne (by decide : (27 : ℕ) ≠ 26),
              htake_succ, List.filter_append, List.filter_cons, decide_eq_true hxV2, ↓reduceIte,
              List.filter_nil, List.length_append, List.length_singleton]
            omega
          · intro j hj
            have hfe : (sl.take (stL.regs 26 + 1)).filter (fun x => decide (x ∈ V2)) =
                (sl.take (stL.regs 26)).filter (fun x => decide (x ∈ V2)) ++ [x] := by
              simp [htake_succ, hxV2]
            simp only [stA, Function.update_self, hfe, List.map_append, List.map_singleton,
              List.length_append, List.length_map, List.length_singleton] at hj ⊢
            by_cases hje : j = stL.regs 27
            · subst hje
              simp only [Function.update_self]
              rw [List.getElem_append_right (by simp [h27_eq])]
              simp
            · have hjlt : j < stL.regs 27 := by omega
              rw [Function.update_of_ne (by omega)]
              rw [List.getElem_append_left (by simp; omega)]
              exact hlat j (by simp; omega)
          · intro k hk hge
            simp only [stA, Function.update_self] at hge
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact htail k hk (by omega)
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hfr a ha
        rcases hstep2 with ⟨o, st', c2, hrun2, hp2, hc2⟩
        exact ⟨o, st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨_, c1, c2, hrun1, hrun2, rfl⟩), hp2,
          by simp only [Expr.size]; omega⟩
      · have heq : st0.mem (spCfg.maskArrAddr + locOf X x) = spCfg.maskBadVal := by
          by_contra hne
          have := (hmask (locOf X x) hx_loc_lt).mp hne
          rw [origOf_locOf hxX] at this; exact hxV2 this
        have hev_cond :
            (Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)).eval w stA = some 1 := by
          simp [Expr.eval, BinOp.eval, stA, h3, h4, show spCfg.maskArrAddr + locOf X x < 2 ^ w by omega,
            hmask_mem, heq, hw_ne]
        have hrun1 : Runs w p ω
            (.cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)) .nop
              (seqStmts
                [ .store (.bin .add (.reg 6) (.reg 27)) (.reg 28)
                , .assign 27 (.bin .add (.reg 27) (.const 1)) ]))
            stA .normal stA ((Expr.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4)).size + 1 + 1) :=
          runs_cond_iff.mpr ⟨1, 1, hev_cond, by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), rfl⟩
        have hstep2 : ∃ o st' c2,
            Runs w p ω (.assign 26 (.bin .add (.reg 26) (.const 1))) stA o st' c2 ∧
            normalPost (fun st =>
              ((∀ r ≤ 25, st.regs r = st0.regs r) ∧
                st.regs 26 ≤ sl.length ∧
                st.regs 27 = ((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).length ∧
                ListAt st.mem spCfg.sBufAddr
                  (((sl.take (st.regs 26)).filter (fun x => decide (x ∈ V2))).map (locOf X)) ∧
                (∀ k (hk : k < sl.length), st.regs 26 ≤ k →
                  st.mem (spCfg.sBufAddr + k) = locOf X (sl[k]'hk)) ∧
                (∀ a, a < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ a → st.mem a = st0.mem a)) ∧
              sl.length - st.regs 26 < sl.length - stL.regs 26) o st' ∧
            0 + c2 ≤ 6 := by
          refine runs_assign_le (v := stL.regs 26 + 1)
            (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨?_, by simp [stA]; omega, ?_, ?_, ?_, hfr⟩, by simp [stA]; omega⟩
          · intro r hr; simp [stA, Function.update_of_ne (by omega : r ≠ 26),
              Function.update_of_ne (by omega : r ≠ 28), hrr r hr]
          · simp only [stA, Function.update_self, Function.update_of_ne (by decide : (27 : ℕ) ≠ 26),
              Function.update_of_ne (by decide : (27 : ℕ) ≠ 28),
              htake_succ, List.filter_append, List.filter_cons, decide_eq_false hxV2,
              Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
            exact h27_eq
          · simp only [stA, Function.update_self, htake_succ, List.filter_append, List.filter_cons,
              decide_eq_false hxV2, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
            exact hlat
          · intro k hk hge
            simp only [stA, Function.update_self] at hge
            exact htail k hk (by omega)
        rcases hstep2 with ⟨o, st', c2, hrun2, hp2, hc2⟩
        exact ⟨o, st', _, runs_seq_iff.mpr (Or.inr ⟨_, _, c2, hrun1, hrun2, rfl⟩), hp2,
          by simp only [Expr.size]; omega⟩
  obtain ⟨o, st', c, hrun, hpost, hc⟩ :=
    hloop st1 ω ⟨fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 26),
      Function.update_of_ne (by omega : r ≠ 27)], Nat.zero_le _, by simp [st1],
      fun j hj => by simp [st1] at hj,
      fun k hk _ => by have hl := hsbuf_list k (by simp [hk]); rw [List.getElem_map] at hl; exact hl,
      fun _ _ => rfl⟩
  cases o with
  | returned _ => exact hpost.elim
  | normal =>
    refine ⟨.normal, st', c, hrun, hpost, ?_⟩
    simp only [Expr.size, st1, hsl_len] at hc ⊢; omega

theorem spWriteRet_triple {w : ℕ} {p : Program}
    {cfgAddr : ℕ} {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 24 < 2 ^ w) :
    Triple w p (fun st => st = st0) spWriteRetStmt
      (retPost fun v st' =>
        v = st0.regs 20 ∧
        st'.mem (cfgAddr + 12) = st0.regs 18 ∧
        st'.mem (cfgAddr + 13) = st0.regs 19 ∧
        st'.mem (cfgAddr + 14) = st0.regs 17 ∧
        st'.mem (cfgAddr + 15) = st0.regs 20 ∧
        st'.mem (cfgAddr + 16) = st0.regs 15 ∧
        st'.mem (cfgAddr + 17) = st0.regs 16 ∧
        (∀ a, a < cfgAddr + 12 ∨ cfgAddr + 18 ≤ a → st'.mem a = st0.mem a))
      (fun _ => 60) := by
  wram_enter; subst st
  unfold spWriteRetStmt; dsimp only [seqStmts]
  refine runs_seq_store_le (x := cfgAddr + 12) (v := st0.regs 18) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 13) (v := st0.regs 19) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 14) (v := st0.regs 17) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 15) (v := st0.regs 20) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 16) (v := st0.regs 15) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 17) (v := st0.regs 16) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := st0.regs 20) (by eval_expr) ?_ (by wram_cost)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp
  · intro a ha
    simp only [Function.update_of_ne (by omega : a ≠ cfgAddr + 17),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 16),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 15),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 14),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 13),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 12)]

end MinCostFlow.ExpanderDecomp
