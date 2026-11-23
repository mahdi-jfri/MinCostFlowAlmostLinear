module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchSub1

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Cut-Stage Sub-Statement Triples (`RouteProgBatchBase`)

Verified Word-RAM triples for `batchFilterLiveStmt` and `batchCopyBallStmt`, re-exporting
`RouteProgBatchLayout`, `RouteProgBatchLemmas`, `RouteProgBatchDisj`, and `RouteProgBatchSub1`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Verification of `batchFilterLiveStmt`: filters `inBase[0 .. l.length - 1]` into `outBuf`,
keeping entries `v` with `liveStamp[v] ≠ liveGen`. -/
lemma batchFilterLive_triple {w : ℕ} {p : Program}
    {X Vlive : Finset ℕ} {liveStampAddr liveGen inBase outBuf : ℕ} {l : List ℕ}
    (hl_lt : ∀ v ∈ l, v < X.card)
    (hl_len : l.length ≤ X.card)
    (hdisj_out_in : DisjRange outBuf X.card inBase l.length)
    (hdisj_out_ls : DisjRange outBuf X.card liveStampAddr X.card)
    (hw_in : inBase + l.length + 5 < 2 ^ w)
    (hw_out : outBuf + X.card + 5 < 2 ^ w)
    (hw_ls : liveStampAddr + X.card + 5 < 2 ^ w)
    (hw_lg : liveGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hlist : ListAt st0.mem inBase l)
    (hls : ∀ v < X.card, st0.mem (liveStampAddr + v) ≠ liveGen ↔ origOf X v ∈ Vlive)
    (hr22 : st0.regs 22 = liveStampAddr) (hr23 : st0.regs 23 = liveGen)
    (hr24 : st0.regs 24 = inBase) (hr26 : st0.regs 26 = l.length) (hr27 : st0.regs 27 = outBuf) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω batchFilterLiveStmt st0 .normal st' c ∧
        (∀ r, r ≠ 25 → r ≠ 28 → r ≠ 29 → r ≠ 30 → st'.regs r = st0.regs r) ∧
        st'.regs 25 = (l.filter fun v => decide (origOf X v ∈ Vlive)).length ∧
        ListAt st'.mem outBuf (l.filter fun v => decide (origOf X v ∈ Vlive)) ∧
        (∀ a, ¬ (outBuf ≤ a ∧ a < outBuf + X.card) → st'.mem a = st0.mem a) ∧
        c ≤ 45 * l.length + 20 := by
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem rpos : ℕ) (st : State),
      rpos + rem = l.length →
      ListAt st.mem inBase l →
      (∀ v < X.card, st.mem (liveStampAddr + v) ≠ liveGen ↔ origOf X v ∈ Vlive) →
      ListAt st.mem outBuf ((l.take rpos).filter fun v => decide (origOf X v ∈ Vlive)) →
      st.regs 22 = liveStampAddr → st.regs 23 = liveGen → st.regs 24 = inBase →
      st.regs 25 = ((l.take rpos).filter fun v => decide (origOf X v ∈ Vlive)).length →
      st.regs 26 = l.length → st.regs 27 = outBuf → st.regs 28 = rpos →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 28) (.reg 26))
              (seqStmts
                [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
                , .cond (.bin .eq (.reg 30) (.reg 23))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 28 (.bin .add (.reg 28) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 25 → r ≠ 28 → r ≠ 29 → r ≠ 30 → st'.regs r = st.regs r) ∧
          st'.regs 25 = (l.filter fun v => decide (origOf X v ∈ Vlive)).length ∧
          ListAt st'.mem outBuf (l.filter fun v => decide (origOf X v ∈ Vlive)) ∧
          (∀ a, ¬ (outBuf ≤ a ∧ a < outBuf + X.card) → st'.mem a = st.mem a) ∧
          c ≤ 45 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro rpos st hr _ _ hpref _ _ _ h25 h26 _ h28 ω
      have hr_eq : rpos = l.length := by omega
      have htk : l.take rpos = l := by rw [hr_eq, List.take_length]
      refine ⟨st, _, batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, h28, h26, hr_eq]),
        fun _ _ _ _ _ => rfl, by simpa [htk] using h25, by simpa [htk] using hpref,
        fun _ _ => rfl, by simp [Expr.size]⟩
    | succ rem ih =>
      intro rpos st hr hlist_s hls_s hpref h22 h23 h24 h25 h26 h27 h28 ω
      have hr_lt : rpos < l.length := by omega
      set v := l[rpos]'hr_lt
      have hv_lt : v < X.card := hl_lt v (List.getElem_mem hr_lt)
      set pref := (l.take rpos).filter fun x => decide (origOf X x ∈ Vlive)
      have hpref_le : pref.length ≤ rpos := by
        have h1 : pref.length ≤ (l.take rpos).length :=
          List.length_filter_le (fun x => decide (origOf X x ∈ Vlive)) (l.take rpos)
        simp only [List.length_take] at h1; omega
      have hpref_succ : (l.take (rpos + 1)).filter (fun x => decide (origOf X x ∈ Vlive)) =
          pref ++ if origOf X v ∈ Vlive then [v] else [] := by
        rw [List.take_succ_eq_append_getElem hr_lt, List.filter_append, List.filter_cons, List.filter_nil]
        by_cases hV : origOf X v ∈ Vlive <;> simp [pref, v, hV]
      have hv_mem : st.mem (inBase + rpos) = v := hlist_s rpos hr_lt
      set sv := st.mem (liveStampAddr + v)
      have hcond : (Expr.bin .lt (.reg 28) (.reg 26)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h28, h26, hr_lt, hw_ne]
      by_cases hV : origOf X v ∈ Vlive
      · have hsv_ne : sv ≠ liveGen := (hls_s v hv_lt).mpr hV
        set mem1 := Function.update st.mem (outBuf + pref.length) v
        set regs1 := Function.update (Function.update (Function.update (Function.update
          st.regs 29 v) 30 sv) 25 (pref.length + 1)) 28 (rpos + 1)
        set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
                , .cond (.bin .eq (.reg 30) (.reg 23))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 38 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                  , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
                  , .cond (.bin .eq (.reg 30) (.reg 23))
                      .nop
                      (seqStmts
                        [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                        , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                  , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 38 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := v) (by rw [← hv_mem]; eval_expr) ?_
            refine runs_seq_assign_le (v := sv) (by eval_expr) ?_
            refine runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, h23, hsv_ne])
              (fun h => absurd rfl h) (fun _ => ?_)
            refine batch_runs_seq_seq_le ?_
            refine runs_seq_store_le (x := outBuf + pref.length) (v := v) (by eval_expr) (by eval_expr) ?_
            refine runs_seq_assign_le (v := pref.length + 1) (by eval_expr) ?_
            refine runs_assign_le (v := rpos + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hlist1 : ListAt st1.mem inBase l := fun j hj => by
          simp only [st1, mem1, Function.update_of_ne (by rcases hdisj_out_in with x | x <;> omega : inBase + j ≠ outBuf + pref.length)]
          exact hlist_s j hj
        have hls1 : ∀ u < X.card, st1.mem (liveStampAddr + u) ≠ liveGen ↔ origOf X u ∈ Vlive := by
          intro u hu
          simp only [st1, mem1, Function.update_of_ne (by rcases hdisj_out_ls with x | x <;> omega : liveStampAddr + u ≠ outBuf + pref.length)]
          exact hls_s u hu
        have hpref1 : ListAt st1.mem outBuf ((l.take (rpos + 1)).filter fun x => decide (origOf X x ∈ Vlive)) := by
          rw [hpref_succ]; simp only [hV, ↓reduceIte]
          intro j hj
          by_cases hjp : j < pref.length
          · rw [List.getElem_append_left hjp]
            simp only [st1, mem1, Function.update_of_ne (by omega : outBuf + j ≠ outBuf + pref.length)]
            exact hpref j hjp
          · have hj_eq : j = pref.length := by simp at hj; omega
            subst hj_eq; rw [List.getElem_append_right (le_refl _)]; simp [st1, mem1]
        obtain ⟨stF, cIH, hrunIH, hregsIH, h25F, hlistF, hfrF, hcIH⟩ :=
          ih (rpos + 1) st1 (by omega) hlist1 hls1 hpref1
            (by simp [st1, regs1, h22]) (by simp [st1, regs1, h23]) (by simp [st1, regs1, h24])
            (by simp [st1, regs1, hpref_succ, hV]) (by simp [st1, regs1, h26])
            (by simp [st1, regs1, h27]) (by simp [st1, regs1]) ω
        refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h25' h28' h29' h30' => (hregsIH r h25' h28' h29' h30').trans (by simp [st1, regs1, h25', h28', h29', h30']),
          h25F, hlistF,
          fun a ha => (hfrF a ha).trans (by simp [st1, mem1, Function.update_of_ne (by omega : a ≠ outBuf + pref.length)]),
          by simp only [Expr.size]; omega⟩
      · have hsv_eq : sv = liveGen := by by_contra hne; exact hV ((hls_s v hv_lt).mp hne)
        set st1 : State :=
          { mem := st.mem
            regs := Function.update (Function.update (Function.update st.regs 29 v) 30 sv) 28 (rpos + 1)
            pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
                , .cond (.bin .eq (.reg 30) (.reg 23))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 38 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                  , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
                  , .cond (.bin .eq (.reg 30) (.reg 23))
                      .nop
                      (seqStmts
                        [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                        , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                  , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 38 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := v) (by rw [← hv_mem]; eval_expr) ?_
            refine runs_seq_assign_le (v := sv) (by eval_expr) ?_
            refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, h23, hsv_eq, hw_ne])
              (fun _ => ?_) (fun h => by omega)
            refine runs_seq_nop_le ?_
            refine runs_assign_le (v := rpos + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        obtain ⟨stF, cIH, hrunIH, hregsIH, h25F, hlistF, hfrF, hcIH⟩ :=
          ih (rpos + 1) st1 (by omega) hlist_s hls_s
            (by simpa [hpref_succ, hV] using hpref)
            (by simp [st1, h22]) (by simp [st1, h23]) (by simp [st1, h24])
            (by simp [st1, h25, hpref_succ, hV]) (by simp [st1, h26])
            (by simp [st1, h27]) (by simp [st1]) ω
        refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h25' h28' h29' h30' => (hregsIH r h25' h28' h29' h30').trans (by simp [st1, h28', h29', h30']),
          h25F, hlistF, hfrF, by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 25 0) 28 0
      pos := st0.pos }
  have hinit : ∃ c1,
      Runs w p ω (seqStmts [ .assign 25 (.const 0), .assign 28 (.const 0) ]) st0 .normal st1 c1 ∧
      c1 ≤ 8 := by
    have h0' : ∃ o s c,
        Runs w p ω (seqStmts [ .assign 25 (.const 0), .assign 28 (.const 0) ]) st0 o s c ∧
        (o = .normal ∧ s = st1) ∧ 0 + c ≤ 8 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
    exact ⟨c1, hrun, by omega⟩
  rcases hinit with ⟨c1, hrun1, hc1⟩
  obtain ⟨stF, cL, hrunL, hregsL, h25F, hlistF, hfrF, hcL⟩ :=
    hloop l.length 0 st1 (Nat.zero_add _) hlist hls (by simp [ListAt])
      (by simp [st1, hr22]) (by simp [st1, hr23]) (by simp [st1, hr24])
      (by simp [st1]) (by simp [st1, hr26]) (by simp [st1, hr27]) (by simp [st1]) ω
  have hrun_all : Runs w p ω batchFilterLiveStmt st0 .normal stF (c1 + cL + 1) := by
    unfold batchFilterLiveStmt; dsimp only [seqStmts] at hrun1 ⊢
    rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
    exact runs_seq_iff.mpr (Or.inr ⟨q, cq1, _, hq1,
      runs_seq_iff.mpr (Or.inr ⟨st1, cq2, cL, hq2, hrunL, rfl⟩), by omega⟩)
  refine ⟨stF, c1 + cL + 1, hrun_all,
    fun r h25' h28' h29' h30' => (hregsL r h25' h28' h29' h30').trans (by simp [st1, h25', h28']),
    h25F, hlistF, hfrF, by omega⟩

/-- Verification of `batchCopyBallStmt`: scans `ballList[0 .. bl.length - 1]`, setting
`liveStamp[u] := liveGen` and appending `u` to `cutList[cut0 ..]`. -/
lemma batchCopyBall_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {liveStampAddr liveGen ballListAddr cutListAddr : ℕ}
    {bl ul0 : List ℕ}
    (hbl_lt : ∀ x ∈ bl, x < X.card)
    (hlen_le : ul0.length + bl.length ≤ X.card)
    (hdisj_ls_cl : DisjRange liveStampAddr X.card cutListAddr X.card)
    (hdisj_ls_bl : DisjRange liveStampAddr X.card ballListAddr X.card)
    (hdisj_cl_bl : DisjRange cutListAddr X.card ballListAddr X.card)
    (hw_ls : liveStampAddr + X.card + 5 < 2 ^ w)
    (hw_bl : ballListAddr + X.card + 5 < 2 ^ w)
    (hw_cl : cutListAddr + X.card + 5 < 2 ^ w)
    (hw_lg : liveGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hbl_at : ListAt st0.mem ballListAddr bl)
    (hul_at : ListAt st0.mem cutListAddr ul0)
    (hr22 : st0.regs 22 = liveStampAddr) (hr23 : st0.regs 23 = liveGen)
    (hr24 : st0.regs 24 = ballListAddr) (hr25 : st0.regs 25 = cutListAddr)
    (hr26 : st0.regs 26 = bl.length) (hr27 : st0.regs 27 = ul0.length) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω batchCopyBallStmt st0 .normal st' c ∧
        (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → st'.regs r = st0.regs r) ∧
        st'.regs 27 = ul0.length + bl.length ∧
        ListAt st'.mem cutListAddr (ul0 ++ bl) ∧
        (∀ v < X.card,
          st'.mem (liveStampAddr + v) =
            if v ∈ bl then liveGen else st0.mem (liveStampAddr + v)) ∧
        (∀ a, ¬ ((liveStampAddr ≤ a ∧ a < liveStampAddr + X.card) ∨
                 (cutListAddr ≤ a ∧ a < cutListAddr + X.card)) → st'.mem a = st0.mem a) ∧
        c ≤ 40 * bl.length + 15 := by
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem j : ℕ) (st : State),
      j + rem = bl.length →
      ListAt st.mem ballListAddr bl →
      ListAt st.mem cutListAddr (ul0 ++ bl.take j) →
      (∀ v < X.card, st.mem (liveStampAddr + v) =
        if v ∈ bl.take j then liveGen else st0.mem (liveStampAddr + v)) →
      (∀ a, ¬ ((liveStampAddr ≤ a ∧ a < liveStampAddr + X.card) ∨
               (cutListAddr ≤ a ∧ a < cutListAddr + X.card)) → st.mem a = st0.mem a) →
      st.regs 22 = liveStampAddr → st.regs 23 = liveGen →
      st.regs 24 = ballListAddr → st.regs 25 = cutListAddr →
      st.regs 26 = bl.length → st.regs 27 = ul0.length + j → st.regs 28 = j →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 28) (.reg 26))
              (seqStmts
                [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                , .store (.bin .add (.reg 22) (.reg 29)) (.reg 23)
                , .store (.bin .add (.reg 25) (.reg 27)) (.reg 29)
                , .assign 27 (.bin .add (.reg 27) (.const 1))
                , .assign 28 (.bin .add (.reg 28) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → st'.regs r = st.regs r) ∧
          st'.regs 27 = ul0.length + bl.length ∧
          ListAt st'.mem cutListAddr (ul0 ++ bl) ∧
          (∀ v < X.card, st'.mem (liveStampAddr + v) =
            if v ∈ bl then liveGen else st0.mem (liveStampAddr + v)) ∧
          (∀ a, ¬ ((liveStampAddr ≤ a ∧ a < liveStampAddr + X.card) ∨
                   (cutListAddr ≤ a ∧ a < cutListAddr + X.card)) → st'.mem a = st0.mem a) ∧
          c ≤ 40 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j st hj _ hul hls hfr _ _ _ _ h26 h27 h28 ω
      have hj_eq : j = bl.length := by omega
      have htk : bl.take j = bl := by rw [hj_eq, List.take_length]
      refine ⟨st, _, batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, h28, h26, hj_eq]),
        fun _ _ _ _ => rfl, by omega, by simpa [htk] using hul, by simpa [htk] using hls,
        hfr, by simp [Expr.size]⟩
    | succ rem ih =>
      intro j st hj hbl_s hul hls hfr h22 h23 h24 h25 h26 h27 h28 ω
      have hj_lt : j < bl.length := by omega
      set u := bl[j]'hj_lt
      have hu_lt : u < X.card := hbl_lt u (List.getElem_mem hj_lt)
      have hu_mem : st.mem (ballListAddr + j) = u := hbl_s j hj_lt
      have hcond : (Expr.bin .lt (.reg 28) (.reg 26)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h28, h26, hj_lt, hw_ne]
      set mem1 := Function.update (Function.update st.mem (liveStampAddr + u) liveGen)
        (cutListAddr + (ul0.length + j)) u
      set regs1 := Function.update (Function.update (Function.update st.regs 29 u)
        27 (ul0.length + j + 1)) 28 (j + 1)
      set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
      have hbody : ∃ cB,
          Runs w p ω
            (seqStmts
              [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
              , .store (.bin .add (.reg 22) (.reg 29)) (.reg 23)
              , .store (.bin .add (.reg 25) (.reg 27)) (.reg 29)
              , .assign 27 (.bin .add (.reg 27) (.const 1))
              , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
            st .normal st1 cB ∧ cB ≤ 32 := by
        have h0' : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
                , .store (.bin .add (.reg 22) (.reg 29)) (.reg 23)
                , .store (.bin .add (.reg 25) (.reg 27)) (.reg 29)
                , .assign 27 (.bin .add (.reg 27) (.const 1))
                , .assign 28 (.bin .add (.reg 28) (.const 1)) ])
              st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 32 := by
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := u) (by rw [← hu_mem]; eval_expr) ?_
          refine runs_seq_store_le (x := liveStampAddr + u) (v := liveGen) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := cutListAddr + (ul0.length + j)) (v := u) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := ul0.length + j + 1) (by eval_expr) ?_
          refine runs_assign_le (v := j + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
        exact ⟨cB, hrun, by omega⟩
      rcases hbody with ⟨cB, hrunB, hcB⟩
      have hbl1 : ListAt st1.mem ballListAddr bl := fun idx hidx => by
        simp only [st1, mem1,
          Function.update_of_ne (by rcases hdisj_cl_bl with x | x <;> omega : ballListAddr + idx ≠ cutListAddr + (ul0.length + j)),
          Function.update_of_ne (by rcases hdisj_ls_bl with x | x <;> omega : ballListAddr + idx ≠ liveStampAddr + u)]
        exact hbl_s idx hidx
      have hul1 : ListAt st1.mem cutListAddr (ul0 ++ bl.take (j + 1)) := by
        rw [List.take_succ_eq_append_getElem hj_lt, ← List.append_assoc]
        intro idx hidx
        have hlen_p : (ul0 ++ bl.take j).length = ul0.length + j := by simp; omega
        by_cases hlt : idx < ul0.length + j
        · rw [List.getElem_append_left (by omega)]
          simp only [st1, mem1,
            Function.update_of_ne (by omega : cutListAddr + idx ≠ cutListAddr + (ul0.length + j)),
            Function.update_of_ne (by rcases hdisj_ls_cl with x | x <;> omega : cutListAddr + idx ≠ liveStampAddr + u)]
          exact hul idx (by omega)
        · have heq : idx = ul0.length + j := by simp at hidx; omega
          subst heq
          rw [List.getElem_append_right (by omega)]
          simp [st1, mem1, hlen_p, u]
      have hls1 : ∀ v < X.card, st1.mem (liveStampAddr + v) =
          if v ∈ bl.take (j + 1) then liveGen else st0.mem (liveStampAddr + v) := by
        intro v hv
        rw [List.take_succ_eq_append_getElem hj_lt]
        simp only [st1, mem1,
          Function.update_of_ne (by rcases hdisj_ls_cl with x | x <;> omega : liveStampAddr + v ≠ cutListAddr + (ul0.length + j)),
          List.mem_append, List.mem_singleton]
        by_cases hvu : v = u
        · simp [hvu, u]
        · rw [Function.update_of_ne (by omega)]
          simp [hvu, u, hls v hv]
      have hfr1 : ∀ a, ¬ ((liveStampAddr ≤ a ∧ a < liveStampAddr + X.card) ∨
               (cutListAddr ≤ a ∧ a < cutListAddr + X.card)) → st1.mem a = st0.mem a := fun a ha => by
        simp only [st1, mem1,
          Function.update_of_ne (by omega : a ≠ cutListAddr + (ul0.length + j)),
          Function.update_of_ne (by omega : a ≠ liveStampAddr + u)]
        exact hfr a ha
      obtain ⟨stF, cIH, hrunIH, hregsIH, h27F, hulF, hlsF, hfrF, hcIH⟩ :=
        ih (j + 1) st1 (by omega) hbl1 hul1 hls1 hfr1
          (by simp [st1, regs1, h22]) (by simp [st1, regs1, h23])
          (by simp [st1, regs1, h24]) (by simp [st1, regs1, h25])
          (by simp [st1, regs1, h26]) (by simp [st1, regs1]; omega) (by simp [st1, regs1]) ω
      refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunB hrunIH,
        fun r h27' h28' h29' => (hregsIH r h27' h28' h29').trans (by simp [st1, regs1, h27', h28', h29']),
        h27F, hulF, hlsF, hfrF, by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State := { st0 with regs := Function.update st0.regs 28 0 }
  have hinit : Runs w p ω (.assign 28 (.const 0)) st0 .normal st1 ((Expr.const 0).size + 1) :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨stF, cL, hrunL, hregsL, h27F, hulF, hlsF, hfrF, hcL⟩ :=
    hloop bl.length 0 st1 (Nat.zero_add _) hbl_at (by simpa using hul_at)
      (fun _ _ => by simp [st1]) (fun _ _ => rfl)
      (by simp [st1, hr22]) (by simp [st1, hr23]) (by simp [st1, hr24])
      (by simp [st1, hr25]) (by simp [st1, hr26]) (by simp [st1, hr27]) (by simp [st1]) ω
  refine ⟨stF, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, cL, hinit, hrunL, rfl⟩),
    fun r h27' h28' h29' => (hregsL r h27' h28' h29').trans (by simp [st1, h28']),
    h27F, hulF, hlsF, hfrF, by simp only [Expr.size]; omega⟩

end MinCostFlow.ExpanderDecomp
