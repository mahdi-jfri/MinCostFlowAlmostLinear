module

public import MinCostFlow.ExpanderDecomp.RouteProgCurBBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sorted Target-Set Builder Verification (`RouteProgCurB`)

Prefix-sum pass (`curBPrefix_triple`), scatter pass (`curBScatter_triple`), and full contract
proof (`buildCurB_meetsContract`) for `buildCurBProc`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma curBPrefix_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr : ℕ}
    (hp : RouteTerminalPairs X pairs)
    (hdisj : CurBDisj w X.card pairs.length pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr)
    {st0 : State}
    (hlen : ∀ i (hi : i < pairs.length), st0.mem (bLenAddr + i) = (pairs[i]'hi).2.card)
    (hr2 : st0.regs 2 = pairs.length) (hr3 : st0.regs 3 = bOffAddr)
    (hr4 : st0.regs 4 = bLenAddr) (hr6 : st0.regs 6 = bCurAddr) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω curBPrefixStmt st0 .normal st' c ∧
        (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → st'.regs r = st0.regs r) ∧
        st'.regs 8 = pairBOff pairs pairs.length ∧
        (∀ i ≤ pairs.length, st'.mem (bOffAddr + i) = pairBOff pairs i) ∧
        (∀ i < pairs.length, st'.mem (bCurAddr + i) = pairBOff pairs i) ∧
        (∀ a, ¬ ((bOffAddr ≤ a ∧ a < bOffAddr + pairs.length + 1) ∨
                 (bCurAddr ≤ a ∧ a < bCurAddr + pairs.length)) → st'.mem a = st0.mem a) ∧
        c ≤ 40 * pairs.length + 25 := by
  have hw_bo := hdisj.w_bo; have hw_bl := hdisj.w_bl; have hw_bc := hdisj.w_bc
  have hw_nX := hdisj.w_nX; have hw_k := hdisj.w_k; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem i : ℕ) (st : State),
      i + rem = pairs.length →
      (∀ j (hj : j < pairs.length), st.mem (bLenAddr + j) = (pairs[j]'hj).2.card) →
      st.regs 2 = pairs.length → st.regs 3 = bOffAddr → st.regs 4 = bLenAddr →
      st.regs 6 = bCurAddr → st.regs 7 = i → st.regs 8 = pairBOff pairs i →
      (∀ j < i, st.mem (bOffAddr + j) = pairBOff pairs j) →
      (∀ j < i, st.mem (bCurAddr + j) = pairBOff pairs j) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 7) (.reg 2))
              (seqStmts
                [ .store (.bin .add (.reg 3) (.reg 7)) (.reg 8)
                , .store (.bin .add (.reg 6) (.reg 7)) (.reg 8)
                , .assign 9 (.load (.bin .add (.reg 4) (.reg 7)))
                , .assign 8 (.bin .add (.reg 8) (.reg 9))
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → st'.regs r = st.regs r) ∧
          st'.regs 8 = pairBOff pairs pairs.length ∧
          (∀ j < pairs.length, st'.mem (bOffAddr + j) = pairBOff pairs j) ∧
          (∀ j < pairs.length, st'.mem (bCurAddr + j) = pairBOff pairs j) ∧
          (∀ a, ¬ ((bOffAddr ≤ a ∧ a < bOffAddr + pairs.length) ∨
                   (bCurAddr ≤ a ∧ a < bCurAddr + pairs.length)) → st'.mem a = st.mem a) ∧
          c ≤ 40 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi _ h2 h3 h4 h6 h7 h8 hbo hbc ω
      have hi_eq : i = pairs.length := by omega
      subst hi_eq
      refine ⟨st, _, runs_loop_zero (by simp [Expr.eval, BinOp.eval, h7, h2]),
        fun _ _ _ _ => rfl, h8, hbo, hbc, fun _ _ => rfl, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i st hi hlen_s h2 h3 h4 h6 h7 h8 hbo hbc ω
      have hi_lt : i < pairs.length := by omega
      have hpos_le : pairBOff pairs i ≤ X.card := pairBOff_le_card hp i
      have hpos1_le : pairBOff pairs (i + 1) ≤ X.card := pairBOff_le_card hp (i + 1)
      have hsucc : pairBOff pairs (i + 1) = pairBOff pairs i + (pairs[i]'hi_lt).2.card :=
        pairBOff_succ pairs hi_lt
      have hcond : (Expr.bin .lt (.reg 7) (.reg 2)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h7, h2, hi_lt, hw_ne]
      set mem1 := Function.update (Function.update st.mem (bOffAddr + i) (pairBOff pairs i))
        (bCurAddr + i) (pairBOff pairs i)
      set regs1 := Function.update (Function.update (Function.update
        st.regs 9 (pairs[i]'hi_lt).2.card) 8 (pairBOff pairs (i + 1))) 7 (i + 1)
      set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
      have hmem1_len : mem1 (bLenAddr + i) = (pairs[i]'hi_lt).2.card := by
        simp only [mem1,
          Function.update_of_ne (by rcases hdisj.bl_bc with x | x <;> omega : bLenAddr + i ≠ bCurAddr + i),
          Function.update_of_ne (by rcases hdisj.bo_bl with x | x <;> omega : bLenAddr + i ≠ bOffAddr + i)]
        exact hlen_s i hi_lt
      have hbody : ∃ cB,
          Runs w p ω
            (seqStmts
              [ .store (.bin .add (.reg 3) (.reg 7)) (.reg 8)
              , .store (.bin .add (.reg 6) (.reg 7)) (.reg 8)
              , .assign 9 (.load (.bin .add (.reg 4) (.reg 7)))
              , .assign 8 (.bin .add (.reg 8) (.reg 9))
              , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
            st .normal st1 cB ∧ cB ≤ 32 := by
        have h0' : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .store (.bin .add (.reg 3) (.reg 7)) (.reg 8)
                , .store (.bin .add (.reg 6) (.reg 7)) (.reg 8)
                , .assign 9 (.load (.bin .add (.reg 4) (.reg 7)))
                , .assign 8 (.bin .add (.reg 8) (.reg 9))
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 32 := by
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := bOffAddr + i) (v := pairBOff pairs i) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := bCurAddr + i) (v := pairBOff pairs i) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := (pairs[i]'hi_lt).2.card)
            (by simp only [Expr.eval, BinOp.eval, h4, h7, show bLenAddr + i < 2 ^ w by omega, ↓reduceIte]
                exact congrArg some hmem1_len) ?_
          refine runs_seq_assign_le (v := pairBOff pairs (i + 1))
            (by simp only [Expr.eval, BinOp.eval, Function.update_self,
                  Function.update_of_ne (by decide : (8 : ℕ) ≠ 9), h8,
                  show pairBOff pairs i + (pairs[i]'hi_lt).2.card < 2 ^ w by omega, ↓reduceIte,
                  Option.some.injEq]; exact hsucc.symm) ?_
          refine runs_assign_le (v := i + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
        exact ⟨cB, hrun, by omega⟩
      rcases hbody with ⟨cB, hrunB, hcB⟩
      have hlen1 : ∀ j (hj : j < pairs.length), st1.mem (bLenAddr + j) = (pairs[j]'hj).2.card := by
        intro j hj
        simp only [st1, mem1,
          Function.update_of_ne (by rcases hdisj.bl_bc with x | x <;> omega : bLenAddr + j ≠ bCurAddr + i),
          Function.update_of_ne (by rcases hdisj.bo_bl with x | x <;> omega : bLenAddr + j ≠ bOffAddr + i)]
        exact hlen_s j hj
      obtain ⟨stF, cIH, hrunIH, hregsIH, h8F, hboF, hbcF, hfrF, hcIH⟩ :=
        ih (i + 1) st1 (by omega) hlen1
          (by simp [st1, regs1, h2]) (by simp [st1, regs1, h3]) (by simp [st1, regs1, h4])
          (by simp [st1, regs1, h6]) (by simp [st1, regs1]) (by simp [st1, regs1])
          (fun j hj => by
            simp only [st1, mem1,
              Function.update_of_ne (by rcases hdisj.bo_bc with x | x <;> omega : bOffAddr + j ≠ bCurAddr + i)]
            by_cases hji : j < i
            · rw [Function.update_of_ne (by omega)]; exact hbo j hji
            · have : j = i := by omega
              subst this; simp)
          (fun j hj => by
            by_cases hji : j < i
            · simp only [st1, mem1,
                Function.update_of_ne (by omega : bCurAddr + j ≠ bCurAddr + i),
                Function.update_of_ne (by rcases hdisj.bo_bc with x | x <;> omega : bCurAddr + j ≠ bOffAddr + i)]
              exact hbc j hji
            · have : j = i := by omega
              subst this; simp [st1, mem1]) ω
      refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
        fun r h7' h8' h9' => (hregsIH r h7' h8' h9').trans (by simp [st1, regs1, h7', h8', h9']),
        h8F, hboF, hbcF,
        fun a ha => (hfrF a ha).trans (by
          simp only [st1, mem1,
            Function.update_of_ne (by omega : a ≠ bCurAddr + i),
            Function.update_of_ne (by omega : a ≠ bOffAddr + i)]),
        by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 7 0) 8 0
      pos := st0.pos }
  have hinit : ∃ c1,
      Runs w p ω (seqStmts [ .assign 7 (.const 0), .assign 8 (.const 0) ]) st0 .normal st1 c1 ∧
      c1 ≤ 8 := by
    have h0' : ∃ o s c,
        Runs w p ω (seqStmts [ .assign 7 (.const 0), .assign 8 (.const 0) ]) st0 o s c ∧
        (o = .normal ∧ s = st1) ∧ 0 + c ≤ 8 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
    exact ⟨c1, hrun, by omega⟩
  rcases hinit with ⟨c1, hrun1, hc1⟩
  obtain ⟨st2, c2, hrun2, hregs2, h8_2, hbo2, hbc2, hfr2, hc2⟩ :=
    hloop pairs.length 0 st1 (Nat.zero_add _) hlen
      (by simp [st1, hr2]) (by simp [st1, hr3]) (by simp [st1, hr4]) (by simp [st1, hr6])
      (by simp [st1]) (by simp [st1, pairBOff_zero])
      (fun _ h => by omega) (fun _ h => by omega) ω
  have h2_2 : st2.regs 2 = pairs.length := by
    rw [hregs2 2 (by decide) (by decide) (by decide)]; simp [st1, hr2]
  have h2_3 : st2.regs 3 = bOffAddr := by
    rw [hregs2 3 (by decide) (by decide) (by decide)]; simp [st1, hr3]
  have htot_le : pairBOff pairs pairs.length ≤ X.card := pairBOff_le_card hp pairs.length
  set st3 : State :=
    { st2 with mem := Function.update st2.mem (bOffAddr + pairs.length) (pairBOff pairs pairs.length) }
  have hrun3 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 2)) (.reg 8)) st2 .normal st3
      ((Expr.bin .add (.reg 3) (.reg 2)).size + (Expr.reg 8).size + 1) :=
    runs_store_iff.mpr ⟨bOffAddr + pairs.length, pairBOff pairs pairs.length,
      by simp [Expr.eval, BinOp.eval, h2_3, h2_2, show bOffAddr + pairs.length < 2 ^ w by omega],
      by simp [Expr.eval, h8_2],
      rfl, rfl, rfl⟩
  have hrun_all : Runs w p ω curBPrefixStmt st0 .normal st3
      (c1 + c2 + ((Expr.bin .add (.reg 3) (.reg 2)).size + (Expr.reg 8).size + 1) + 2) := by
    unfold curBPrefixStmt; dsimp only [seqStmts] at hrun1 ⊢
    rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
    refine runs_seq_iff.mpr (Or.inr ⟨q, cq1, _, hq1,
      runs_seq_iff.mpr (Or.inr ⟨st1, cq2, _, hq2,
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hrun3, rfl⟩), rfl⟩), by omega⟩)
  refine ⟨st3, _, hrun_all,
    fun r h7 h8 h9 => (hregs2 r h7 h8 h9).trans (by simp [st1, h7, h8]),
    h8_2, ?_, ?_, ?_, by simp only [Expr.size]; omega⟩
  · intro i hi
    by_cases hlt : i < pairs.length
    · rw [show st3.mem _ = Function.update st2.mem _ _ _ from rfl, Function.update_of_ne (by omega)]
      exact hbo2 i hlt
    · have : i = pairs.length := by omega
      subst this; simp [st3]
  · intro i hi
    rw [show st3.mem _ = Function.update st2.mem _ _ _ from rfl,
        Function.update_of_ne (by rcases hdisj.bo_bc with x | x <;> omega)]
    exact hbc2 i hi
  · intro a ha
    rw [show st3.mem a = Function.update st2.mem _ _ a from rfl,
        Function.update_of_ne (by omega)]
    exact hfr2 a (by omega)

private lemma curBScatter_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr : ℕ}
    (hp : RouteTerminalPairs X pairs)
    (hdisj : CurBDisj w X.card pairs.length pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr)
    {st0 : State}
    (hbp : LocalBPairsAt st0.mem pairBAddr X pairs)
    (hcur0 : ∀ i < pairs.length, st0.mem (bCurAddr + i) = pairBOff pairs i)
    (hr0 : st0.regs 0 = pairBAddr) (hr1 : st0.regs 1 = X.card)
    (hr5 : st0.regs 5 = bDataAddr) (hr6 : st0.regs 6 = bCurAddr) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω curBScatterStmt st0 .normal st' c ∧
        (∀ r, r ≠ 7 → r ≠ 9 → r ≠ 10 → r ≠ 11 → st'.regs r = st0.regs r) ∧
        (∀ i (hi : i < pairs.length),
          ListAt st'.mem (bDataAddr + pairBOff pairs i) (((pairs[i]'hi).2.sort (· ≤ ·)).map (locOf X))) ∧
        (∀ a, ¬ ((bDataAddr ≤ a ∧ a < bDataAddr + X.card) ∨
                 (bCurAddr ≤ a ∧ a < bCurAddr + pairs.length)) → st'.mem a = st0.mem a) ∧
        c ≤ 55 * X.card + 15 := by
  have hw_pb := hdisj.w_pb; have hw_bd := hdisj.w_bd; have hw_bc := hdisj.w_bc
  have hw_nX := hdisj.w_nX; have hw_k := hdisj.w_k; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem v : ℕ) (st : State),
      v + rem = X.card →
      LocalBPairsAt st.mem pairBAddr X pairs →
      st.regs 0 = pairBAddr → st.regs 1 = X.card → st.regs 5 = bDataAddr →
      st.regs 6 = bCurAddr → st.regs 7 = v →
      (∀ i (hi : i < pairs.length),
        st.mem (bCurAddr + i) = pairBOff pairs i + (localPrefix X (pairs[i]'hi).2 v).length) →
      (∀ i (hi : i < pairs.length),
        ListAt st.mem (bDataAddr + pairBOff pairs i) (localPrefix X (pairs[i]'hi).2 v)) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 7) (.reg 1))
              (seqStmts
                [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 9)
                    (seqStmts
                      [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                      , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                      , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                      , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 7 → r ≠ 9 → r ≠ 10 → r ≠ 11 → st'.regs r = st.regs r) ∧
          (∀ i (hi : i < pairs.length),
            ListAt st'.mem (bDataAddr + pairBOff pairs i) (((pairs[i]'hi).2.sort (· ≤ ·)).map (locOf X))) ∧
          (∀ a, ¬ ((bDataAddr ≤ a ∧ a < bDataAddr + X.card) ∨
                   (bCurAddr ≤ a ∧ a < bCurAddr + pairs.length)) → st'.mem a = st.mem a) ∧
          c ≤ 55 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro v st hv _ h0 h1 h5 h6 h7 _ hlist ω
      have hv_eq : v = X.card := by omega
      subst hv_eq
      refine ⟨st, _, runs_loop_zero (by simp [Expr.eval, BinOp.eval, h7, h1]),
        fun _ _ _ _ _ => rfl, ?_, fun _ _ => rfl, by simp [Expr.size]⟩
      intro i hi
      have hBiX : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
      simpa [localPrefix_card_eq X hBiX] using hlist i hi
    | succ rem ih =>
      intro v st hv hbp_s h0 h1 h5 h6 h7 hcur hlist ω
      have hv_lt : v < X.card := by omega
      have hcond : (Expr.bin .lt (.reg 7) (.reg 1)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h7, h1, hv_lt, hw_ne]
      set tag := st.mem (pairBAddr + v)
      have htag_le : tag ≤ pairs.length := (hbp_s v hv_lt).1
      by_cases htag0 : tag = 0
      · set st1 : State :=
          { mem := st.mem
            regs := Function.update (Function.update st.regs 9 0) 7 (v + 1)
            pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 9)
                    (seqStmts
                      [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                      , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                      , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                      , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 48 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
                  , .cond (.reg 9)
                      (seqStmts
                        [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                        , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                        , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                        , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
                      .nop
                  , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 48 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := 0)
              (by simp [Expr.eval, BinOp.eval, h0, h7, show pairBAddr + v < 2 ^ w by omega,
                   show st.mem (pairBAddr + v) = 0 from htag0]) ?_
            refine runs_seq_cond_zero_le (by eval_expr) ?_
            refine runs_seq_nop_le ?_
            refine runs_assign_le (v := v + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hnot_all : ∀ i (hi : i < pairs.length), origOf X v ∉ (pairs[i]'hi).2 := by
          intro i hi hm; have := ((hbp_s v hv_lt).2 i hi).mpr hm; omega
        obtain ⟨stF, cIH, hrunIH, hregsIH, hlistF, hfrF, hcIH⟩ :=
          ih (v + 1) st1 (by omega) hbp_s
            (by simp [st1, h0]) (by simp [st1, h1]) (by simp [st1, h5]) (by simp [st1, h6])
            (by simp [st1])
            (fun i hi => by
              have hBiX : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
              rw [localPrefix_succ' hBiX hv_lt]; simp [st1, hnot_all i hi, hcur i hi])
            (fun i hi => by
              have hBiX : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
              rw [localPrefix_succ' hBiX hv_lt]; simp [st1, hnot_all i hi]; exact hlist i hi) ω
        refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h7' h9' h10' h11' => (hregsIH r h7' h9' h10' h11').trans (by simp [st1, h7', h9']),
          hlistF, hfrF, by simp only [Expr.size]; omega⟩
      · set idx := tag - 1
        have hidx_lt : idx < pairs.length := by omega
        have htag_eq : tag = idx + 1 := by omega
        have hv_in : origOf X v ∈ (pairs[idx]'hidx_lt).2 := ((hbp_s v hv_lt).2 idx hidx_lt).mp htag_eq
        have hBiX : (pairs[idx]'hidx_lt).2 ⊆ X := (hp.1 _ (List.getElem_mem hidx_lt)).2.1
        set prefLen := (localPrefix X (pairs[idx]'hidx_lt).2 v).length
        set wpos := pairBOff pairs idx + prefLen
        have hwpos_mem : st.mem (bCurAddr + idx) = wpos := hcur idx hidx_lt
        have hwpos_lt : wpos + 1 ≤ X.card := by
          have h1 : (localPrefix X (pairs[idx]'hidx_lt).2 (v + 1)).length ≤ (pairs[idx]'hidx_lt).2.card :=
            localPrefix_length_le' (v + 1)
          rw [localPrefix_succ' hBiX hv_lt] at h1; simp [hv_in] at h1
          have h2 := pairBOff_succ pairs hidx_lt
          have h3 := pairBOff_le_card hp (idx + 1)
          omega
        set mem1 := Function.update (Function.update st.mem (bDataAddr + wpos) v)
          (bCurAddr + idx) (wpos + 1)
        set regs1 := Function.update (Function.update (Function.update (Function.update
          st.regs 9 tag) 10 idx) 11 wpos) 7 (v + 1)
        set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 9)
                    (seqStmts
                      [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                      , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                      , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                      , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 48 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
                  , .cond (.reg 9)
                      (seqStmts
                        [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                        , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                        , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                        , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
                      .nop
                  , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 48 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := tag) (by eval_expr) ?_
            refine runs_seq_cond_pos_le (v := tag) (by eval_expr) (by omega) ?_
            refine runs_seq_seq_le ?_
            refine runs_seq_assign_le (v := idx) (by eval_expr) ?_
            refine runs_seq_seq_le ?_
            refine runs_seq_assign_le (v := wpos) (by rw [← hwpos_mem]; eval_expr) ?_
            refine runs_seq_seq_le ?_
            refine runs_seq_store_le (x := bDataAddr + wpos) (v := v) (by eval_expr) (by eval_expr) ?_
            refine runs_seq_store_le (x := bCurAddr + idx) (v := wpos + 1) (by eval_expr) (by eval_expr) ?_
            refine runs_assign_le (v := v + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hbp1 : LocalBPairsAt st1.mem pairBAddr X pairs := by
          intro u hu
          simp only [st1, mem1,
            Function.update_of_ne (by rcases hdisj.bc_pb with x | x <;> omega : pairBAddr + u ≠ bCurAddr + idx),
            Function.update_of_ne (by rcases hdisj.bd_pb with x | x <;> omega : pairBAddr + u ≠ bDataAddr + wpos)]
          exact hbp_s u hu
        have hcur1 : ∀ i (hi : i < pairs.length),
            st1.mem (bCurAddr + i) = pairBOff pairs i + (localPrefix X (pairs[i]'hi).2 (v + 1)).length := by
          intro i hi
          have hBiX' : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
          rw [localPrefix_succ' hBiX' hv_lt]
          by_cases heq : i = idx
          · subst heq; simp [st1, mem1, hv_in, wpos, prefLen]; omega
          · have hnot : origOf X v ∉ (pairs[i]'hi).2 := by
              intro hm; have := ((hbp_s v hv_lt).2 i hi).mpr hm; omega
            simp only [st1, mem1,
              Function.update_of_ne (by omega : bCurAddr + i ≠ bCurAddr + idx),
              Function.update_of_ne (by rcases hdisj.bd_bc with x | x <;> omega : bCurAddr + i ≠ bDataAddr + wpos),
              hnot, ↓reduceIte, List.append_nil]
            exact hcur i hi
        have hlist1 : ∀ i (hi : i < pairs.length),
            ListAt st1.mem (bDataAddr + pairBOff pairs i) (localPrefix X (pairs[i]'hi).2 (v + 1)) := by
          intro i hi
          have hBiX' : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
          rw [localPrefix_succ' hBiX' hv_lt]
          by_cases heq : i = idx
          · subst heq
            simp only [hv_in, ↓reduceIte]
            intro j hj
            rw [Nat.add_assoc]
            have hbc_ne : bDataAddr + (pairBOff pairs idx + j) ≠ bCurAddr + idx := by
              have hlen1 : (localPrefix X (pairs[idx]'hidx_lt).2 v ++ [v]).length = prefLen + 1 := by simp [prefLen]
              rcases hdisj.bd_bc with x | x <;> omega
            simp only [st1, mem1, Function.update_of_ne hbc_ne]
            by_cases hjp : j < prefLen
            · rw [List.getElem_append_left hjp, Function.update_of_ne (by omega), ← Nat.add_assoc]
              exact hlist idx hidx_lt j hjp
            · have hj_eq : j = prefLen := by simp at hj; omega
              subst hj_eq
              rw [List.getElem_append_right (le_refl _)]
              simp [wpos, prefLen]
          · have hnot : origOf X v ∉ (pairs[i]'hi).2 := by
              intro hm; have := ((hbp_s v hv_lt).2 i hi).mpr hm; omega
            simp only [hnot, ↓reduceIte, List.append_nil]
            intro j hj
            have hj_le : j < (pairs[i]'hi).2.card := lt_of_lt_of_le hj (localPrefix_length_le' v)
            have hdisj_slot : pairBOff pairs i + j ≠ wpos := by
              rcases lt_or_gt_of_ne heq with hlt | hgt
              · have h1 := pairBOff_succ pairs hi
                have h2 := pairBOff_mono pairs (show i + 1 ≤ idx by omega)
                omega
              · have h1 : prefLen < (pairs[idx]'hidx_lt).2.card := by
                  have h' : (localPrefix X (pairs[idx]'hidx_lt).2 (v + 1)).length ≤ (pairs[idx]'hidx_lt).2.card :=
                    localPrefix_length_le' (v + 1)
                  rw [localPrefix_succ' hBiX hv_lt] at h'; simp [hv_in] at h'; omega
                have h2 := pairBOff_succ pairs hidx_lt
                have h3 := pairBOff_mono pairs (show idx + 1 ≤ i by omega)
                omega
            have hlt_X : pairBOff pairs i + j < X.card := by
              have h1 := pairBOff_succ pairs hi
              have h2 := pairBOff_le_card hp (i + 1)
              omega
            rw [Nat.add_assoc]
            simp only [st1, mem1,
              Function.update_of_ne (by rcases hdisj.bd_bc with x | x <;> omega : bDataAddr + (pairBOff pairs i + j) ≠ bCurAddr + idx),
              Function.update_of_ne (by omega : bDataAddr + (pairBOff pairs i + j) ≠ bDataAddr + wpos)]
            rw [← Nat.add_assoc]
            exact hlist i hi j hj
        obtain ⟨stF, cIH, hrunIH, hregsIH, hlistF, hfrF, hcIH⟩ :=
          ih (v + 1) st1 (by omega) hbp1
            (by simp [st1, regs1, h0]) (by simp [st1, regs1, h1])
            (by simp [st1, regs1, h5]) (by simp [st1, regs1, h6])
            (by simp [st1, regs1]) hcur1 hlist1 ω
        refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h7' h9' h10' h11' => (hregsIH r h7' h9' h10' h11').trans (by simp [st1, regs1, h7', h9', h10', h11']),
          hlistF,
          fun a ha => (hfrF a ha).trans (by
            simp only [st1, mem1,
              Function.update_of_ne (by omega : a ≠ bCurAddr + idx),
              Function.update_of_ne (by omega : a ≠ bDataAddr + wpos)]),
          by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State := { st0 with regs := Function.update st0.regs 7 0 }
  have hinit : Runs w p ω (.assign 7 (.const 0)) st0 .normal st1 ((Expr.const 0).size + 1) :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨stF, cL, hrunL, hregsL, hlistF, hfrF, hcL⟩ :=
    hloop X.card 0 st1 (Nat.zero_add _) hbp
      (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr5]) (by simp [st1, hr6])
      (by simp [st1])
      (fun i hi => by simp [st1, localPrefix_zero', hcur0 i hi])
      (fun i hi => by simp [st1, localPrefix_zero', ListAt]) ω
  refine ⟨stF, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, cL, hinit, hrunL, rfl⟩),
    fun r h7 h9 h10 h11 => (hregsL r h7 h9 h10 h11).trans (by simp [st1, h7]),
    hlistF, hfrF, by simp only [Expr.size]; omega⟩

/-- `buildCurBProc` meets `buildCurBContract` deterministically. -/
theorem buildCurB_meetsContract {w : ℕ} {p : Program} {idx : ℕ}
    (hproc : p.procs[idx]? = some buildCurBProc)
    (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) :
    MeetsContract w p idx (buildCurBContract w X pairs) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hnX, hk, hp, hbp, hdisj⟩
  set pairBAddr := args.getD 0 0
  set bOffAddr := args.getD 3 0
  set bLenAddr := args.getD 4 0
  set bDataAddr := args.getD 5 0
  set bCurAddr := args.getD 6 0
  have hw_nX := hdisj.w_nX; have hw4 := hdisj.w_4
  refine ⟨buildCurBProc, hproc, ?_⟩
  set st0 := startState args mem pos
  have hr_arg : ∀ i < 7, st0.regs i = args.getD i 0 := fun i hi => by
    simp [st0, startState, List.getD_eq_getElem?_getD, hi, hlen]
  -- Pass 0: curBZeroStmt
  obtain ⟨st1, c1, hrun1, hregs1, hzero1, hfr1, hc1⟩ :=
    curBZero_triple (p := p) hdisj
      (by rw [hr_arg 2 (by decide)]; exact hk)
      (by rw [hr_arg 4 (by decide)]) ω
  have hbp1 : LocalBPairsAt st1.mem pairBAddr X pairs := by
    intro v hv
    rw [hfr1 _ (by rcases hdisj.bl_pb with x | x <;> omega)]
    exact hbp v hv
  -- Pass 1: curBCountStmt
  obtain ⟨st2, c2, hrun2, hregs2, hlen2, hfr2, hc2⟩ :=
    curBCount_triple (p := p) hp hdisj hbp1 hzero1
      (by rw [hregs1 0 (by decide), hr_arg 0 (by decide)])
      (by rw [hregs1 1 (by decide), hr_arg 1 (by decide)]; exact hnX)
      (by rw [hregs1 4 (by decide), hr_arg 4 (by decide)]) ω
  have hbp2 : LocalBPairsAt st2.mem pairBAddr X pairs := by
    intro v hv
    rw [hfr2 _ (by rcases hdisj.bl_pb with x | x <;> omega)]
    exact hbp1 v hv
  -- Pass 2: curBPrefixStmt
  obtain ⟨st3, c3, hrun3, hregs3, h8_3, hbo3, hbc3, hfr3, hc3⟩ :=
    curBPrefix_triple (p := p) hp hdisj hlen2
      (by rw [hregs2 2 (by decide) (by decide) (by decide) (by decide), hregs1 2 (by decide),
              hr_arg 2 (by decide)]; exact hk)
      (by rw [hregs2 3 (by decide) (by decide) (by decide) (by decide), hregs1 3 (by decide),
              hr_arg 3 (by decide)])
      (by rw [hregs2 4 (by decide) (by decide) (by decide) (by decide), hregs1 4 (by decide),
              hr_arg 4 (by decide)])
      (by rw [hregs2 6 (by decide) (by decide) (by decide) (by decide), hregs1 6 (by decide),
              hr_arg 6 (by decide)]) ω
  have hbp3 : LocalBPairsAt st3.mem pairBAddr X pairs := by
    intro v hv
    rw [hfr3 _ (by rcases hdisj.bo_pb with x | x <;> rcases hdisj.bc_pb with y | y <;> omega)]
    exact hbp2 v hv
  -- Pass 3: curBScatterStmt
  obtain ⟨st4, c4, hrun4, hregs4, hlist4, hfr4, hc4⟩ :=
    curBScatter_triple (p := p) hp hdisj hbp3 hbc3
      (by rw [hregs3 0 (by decide) (by decide) (by decide),
              hregs2 0 (by decide) (by decide) (by decide) (by decide),
              hregs1 0 (by decide), hr_arg 0 (by decide)])
      (by rw [hregs3 1 (by decide) (by decide) (by decide),
              hregs2 1 (by decide) (by decide) (by decide) (by decide),
              hregs1 1 (by decide), hr_arg 1 (by decide)]; exact hnX)
      (by rw [hregs3 5 (by decide) (by decide) (by decide),
              hregs2 5 (by decide) (by decide) (by decide) (by decide),
              hregs1 5 (by decide), hr_arg 5 (by decide)])
      (by rw [hregs3 6 (by decide) (by decide) (by decide),
              hregs2 6 (by decide) (by decide) (by decide) (by decide),
              hregs1 6 (by decide), hr_arg 6 (by decide)]) ω
  have h4_8 : st4.regs 8 = pairBOff pairs pairs.length := by
    rw [hregs4 8 (by decide) (by decide) (by decide) (by decide), h8_3]
  have htot_le : pairBOff pairs pairs.length ≤ X.card := pairBOff_le_card hp pairs.length
  have hrun5 : Runs w p ω (.ret (.reg 8)) st4 (.returned (pairBOff pairs pairs.length)) st4
      ((Expr.reg 8).size + 1) :=
    runs_ret_iff.mpr ⟨pairBOff pairs pairs.length,
      by simp [Expr.eval, h4_8],
      rfl, rfl, rfl⟩
  have hrun_all : Runs w p ω buildCurBProc st0 (.returned (pairBOff pairs pairs.length)) st4
      (c1 + (c2 + (c3 + (c4 + ((Expr.reg 8).size + 1) + 1) + 1) + 1) + 1) := by
    unfold buildCurBProc; dsimp only [seqStmts]
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
        runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3,
          runs_seq_iff.mpr (Or.inr ⟨st4, c4, _, hrun4, hrun5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned (pairBOff pairs pairs.length), st4, _, hrun_all, ?_, ?_⟩
  · dsimp only [buildCurBContract, Outcome.value]
    have hbo4 : ∀ i ≤ pairs.length, st4.mem (bOffAddr + i) = pairBOff pairs i := fun i hi => by
      rw [hfr4 _ (by rcases hdisj.bo_bd with x | x <;> rcases hdisj.bo_bc with y | y <;> omega)]
      exact hbo3 i hi
    have hlen4 : ∀ i (hi : i < pairs.length), st4.mem (bLenAddr + i) = (pairs[i]'hi).2.card := fun i hi => by
      rw [hfr4 _ (by rcases hdisj.bl_bd with x | x <;> rcases hdisj.bl_bc with y | y <;> omega),
          hfr3 _ (by rcases hdisj.bo_bl with x | x <;> rcases hdisj.bl_bc with y | y <;> omega)]
      exact hlen2 i hi
    refine ⟨rfl, htot_le, ⟨by rw [hbo4 pairs.length le_rfl]; exact htot_le, fun i hi => ?_⟩, ?_⟩
    · dsimp only
      rw [hbo4 i (by omega), hlen4 i hi, Nat.add_assoc, hbo4 (i + 1) (by omega)]
      exact ⟨(pairBOff_succ pairs hi).symm, rfl, hlist4 i hi⟩
    · intro a ha
      rw [hfr4 a (by intro h; rcases h with h | h; exact ha (Or.inr (Or.inr (Or.inl h))); exact ha (Or.inr (Or.inr (Or.inr h)))),
          hfr3 a (by intro h; rcases h with h | h; exact ha (Or.inl h); exact ha (Or.inr (Or.inr (Or.inr h)))),
          hfr2 a (fun h => ha (Or.inr (Or.inl h))),
          hfr1 a (fun h => ha (Or.inr (Or.inl h)))]
      rfl
  · dsimp only [buildCurBContract, buildCurBCost, Expr.size]
    omega

end MinCostFlow.ExpanderDecomp
