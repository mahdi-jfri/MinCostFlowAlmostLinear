module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchDisj

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Route-Stage Sub-Statement Triples (`RouteProgBatchSub1`)

Verified Word-RAM triples for `batchMarkMatchedStmt`, `batchCompactAStmt`, and
`batchAppendChunkStmt`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 8. Verification of Sub-Statements -/

lemma batch_runs_loop_zero {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

lemma batch_runs_loop_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {v c₁ c₂ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h₁ : Runs w p ω body st .normal st₁ c₁)
    (h₂ : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h₁, h₂, rfl⟩))

lemma batch_runs_seq_seq_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ s₃ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω (.seq s₁ (.seq s₂ s₃)) st o st' c ∧ Q o st' ∧ (k + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.seq s₁ s₂) s₃) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  rcases runs_seq_iff.mp hr with ⟨v, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂₃, hr₁, hr₂₃, rfl⟩
  · refine ⟨.returned v, st', (c₁ + 1) + 1,
      runs_seq_iff.mpr (Or.inl ⟨v, c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨v, c₁, hr₁, rfl, rfl⟩), rfl, rfl⟩),
      hq, by omega⟩
  · rcases runs_seq_iff.mp hr₂₃ with ⟨v, c₂, hr₂, rfl, rfl⟩ | ⟨st₂, c₂, c₃, hr₂, hr₃, rfl⟩
    · refine ⟨.returned v, st', (c₁ + c₂ + 1) + 1,
        runs_seq_iff.mpr (Or.inl ⟨v, c₁ + c₂ + 1,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), rfl, rfl⟩),
        hq, by omega⟩
    · refine ⟨o, st', (c₁ + c₂ + 1) + c₃ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₂, c₁ + c₂ + 1, c₃,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hr₃, rfl⟩),
        hq, by omega⟩

/-- Verification of `batchMarkMatchedStmt`: walks `PathListAt` starting at `head`, stamping
`matchAStamp[locOf X a] := batchGen` and clearing `pairB[locOf X b] := 0`. -/
lemma batchMarkMatched_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairBAddr matchAStampAddr batchGen pLo pHi : ℕ}
    (hdisj_pb_ma : DisjRange pairBAddr X.card matchAStampAddr X.card)
    (hdisj_pb_p : DisjRange pairBAddr X.card pLo (pHi - pLo))
    (hdisj_ma_p : DisjRange matchAStampAddr X.card pLo (pHi - pLo))
    (hp_le : pLo ≤ pHi)
    (hw_pb : pairBAddr + X.card + 5 < 2 ^ w)
    (hw_ma : matchAStampAddr + X.card + 5 < 2 ^ w)
    (hw_p : pHi + 5 < 2 ^ w)
    (_hw_bg : batchGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (ps : List ((ℕ × ℕ) × List ℕ)) :
    ∀ (head : ℕ) (st0 : State),
      PathListAt st0.mem X pLo pHi head ps →
      st0.regs 8 = pairBAddr →
      st0.regs 16 = matchAStampAddr →
      st0.regs 17 = batchGen →
      st0.regs 22 = head →
      ∀ ω,
        ∃ st' c,
          Runs w p ω batchMarkMatchedStmt st0 .normal st' c ∧
          (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → st'.regs r = st0.regs r) ∧
          (∀ v < X.card,
            st'.mem (matchAStampAddr + v) =
              if origOf X v ∈ (ps.map fun q => q.1.1).toFinset then batchGen
              else st0.mem (matchAStampAddr + v)) ∧
          (∀ v < X.card,
            st'.mem (pairBAddr + v) =
              if origOf X v ∈ (ps.map fun q => q.1.2).toFinset then 0
              else st0.mem (pairBAddr + v)) ∧
          (∀ a, ¬ ((matchAStampAddr ≤ a ∧ a < matchAStampAddr + X.card) ∨
                   (pairBAddr ≤ a ∧ a < pairBAddr + X.card)) → st'.mem a = st0.mem a) ∧
          c ≤ 40 * ps.length + 5 := by
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
  induction ps with
  | nil =>
    intro head st0 hpl _ _ _ hr22 ω
    have h0 : head = 0 := hpl
    refine ⟨st0, (Expr.reg 22).size + 1,
      batch_runs_loop_zero (by simp [Expr.eval, hr22, h0]),
      fun _ _ _ _ => rfl, fun _ _ => by simp, fun _ _ => by simp, fun _ _ => rfl,
      by simp [Expr.size]⟩
  | cons q rest ih =>
    intro head st0 hpl hr8 hr16 hr17 hr22 ω
    rcases q with ⟨⟨s, t⟩, es⟩
    rcases hpl with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, _, _, _, hrest⟩
    have hs_lt : locOf X s < X.card := locOf_lt hsX
    have ht_lt : locOf X t < X.card := locOf_lt htX
    set nextNd := st0.mem (head + 3)
    have hcond : (Expr.reg 22).eval w st0 = some head := by simp [Expr.eval, hr22]
    set mem1 := Function.update (Function.update st0.mem (matchAStampAddr + locOf X s) batchGen)
      (pairBAddr + locOf X t) 0
    have hmem1_next : mem1 (head + 3) = nextNd := by
      simp only [mem1,
        Function.update_of_ne (by rcases hdisj_pb_p with x | x <;> omega : head + 3 ≠ pairBAddr + locOf X t),
        Function.update_of_ne (by rcases hdisj_ma_p with x | x <;> omega : head + 3 ≠ matchAStampAddr + locOf X s)]
      rfl
    set st1 : State :=
      { mem := mem1
        regs := Function.update (Function.update (Function.update st0.regs 23 (locOf X s))
          24 (locOf X t)) 22 nextNd
        pos := st0.pos }
    have hbody : ∃ cB,
        Runs w p ω
          (seqStmts
            [ .assign 23 (.load (.reg 22))
            , .assign 24 (.load (.bin .add (.reg 22) (.const 1)))
            , .store (.bin .add (.reg 16) (.reg 23)) (.reg 17)
            , .store (.bin .add (.reg 8) (.reg 24)) (.const 0)
            , .assign 22 (.load (.bin .add (.reg 22) (.const 3))) ])
          st0 .normal st1 cB ∧ cB ≤ 35 := by
      have h0' : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .assign 23 (.load (.reg 22))
              , .assign 24 (.load (.bin .add (.reg 22) (.const 1)))
              , .store (.bin .add (.reg 16) (.reg 23)) (.reg 17)
              , .store (.bin .add (.reg 8) (.reg 24)) (.const 0)
              , .assign 22 (.load (.bin .add (.reg 22) (.const 3))) ])
            st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 35 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := locOf X s) (by rw [← hm0]; eval_expr) ?_
        refine runs_seq_assign_le (v := locOf X t) (by rw [← hm1]; eval_expr) ?_
        refine runs_seq_store_le (x := matchAStampAddr + locOf X s) (v := batchGen)
          (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := pairBAddr + locOf X t) (v := 0)
          (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := nextNd)
          (by simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (22 : ℕ) ≠ 24),
                Function.update_of_ne (by decide : (22 : ℕ) ≠ 23), hr22, show 3 < 2 ^ w by omega,
                show head + 3 < 2 ^ w by omega, ↓reduceIte]
              exact congrArg some hmem1_next) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
      exact ⟨cB, hrun, by omega⟩
    rcases hbody with ⟨cB, hrunB, hcB⟩
    have hrest1 : PathListAt st1.mem X pLo pHi nextNd rest :=
      hrest.congr (fun k hk1 hk2 => by
        simp only [st1, mem1,
          Function.update_of_ne (by rcases hdisj_pb_p with x | x <;> omega : k ≠ pairBAddr + locOf X t),
          Function.update_of_ne (by rcases hdisj_ma_p with x | x <;> omega : k ≠ matchAStampAddr + locOf X s)])
    obtain ⟨stF, cIH, hrunIH, hregsIH, hmaIH, hpbIH, hfrIH, hcIH⟩ :=
      ih nextNd st1 hrest1
        (by simp [st1, hr8]) (by simp [st1, hr16]) (by simp [st1, hr17]) (by simp [st1]) ω
    refine ⟨stF, _, batch_runs_loop_step hcond hne hrunB hrunIH,
      fun r h22 h23 h24 => (hregsIH r h22 h23 h24).trans (by simp [st1, h22, h23, h24]),
      ?_, ?_, ?_, by simp only [Expr.size, List.length_cons]; omega⟩
    · intro v hv
      rw [hmaIH v hv]
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
      by_cases hmr : origOf X v ∈ (rest.map fun q => q.1.1).toFinset
      · simp [hmr]
      · simp only [hmr, or_false, ↓reduceIte]
        simp only [st1, mem1,
          Function.update_of_ne (by rcases hdisj_pb_ma with x | x <;> omega : matchAStampAddr + v ≠ pairBAddr + locOf X t)]
        by_cases hvs : origOf X v = s
        · have hv_eq : v = locOf X s := by rw [← hvs, locOf_origOf hv]
          simp only [hvs, ↓reduceIte]; rw [hv_eq, Function.update_self]
        · have hv_ne : v ≠ locOf X s := fun h => hvs (by rw [h, origOf_locOf hsX])
          simp [hvs, Function.update_of_ne (by omega : matchAStampAddr + v ≠ matchAStampAddr + locOf X s)]
    · intro v hv
      rw [hpbIH v hv]
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
      by_cases hmr : origOf X v ∈ (rest.map fun q => q.1.2).toFinset
      · simp [hmr]
      · simp only [hmr, or_false, ↓reduceIte]
        by_cases hvt : origOf X v = t
        · have hv_eq : v = locOf X t := by rw [← hvt, locOf_origOf hv]
          simp only [st1, mem1, hvt, ↓reduceIte]; rw [hv_eq, Function.update_self]
        · have hv_ne : v ≠ locOf X t := fun h => hvt (by rw [h, origOf_locOf htX])
          simp [st1, mem1, hvt,
            Function.update_of_ne (by omega : pairBAddr + v ≠ pairBAddr + locOf X t),
            Function.update_of_ne (by rcases hdisj_pb_ma with x | x <;> omega : pairBAddr + v ≠ matchAStampAddr + locOf X s)]
    · intro a ha
      rw [hfrIH a ha]
      simp only [st1, mem1,
        Function.update_of_ne (by omega : a ≠ pairBAddr + locOf X t),
        Function.update_of_ne (by omega : a ≠ matchAStampAddr + locOf X s)]

/-- Verification of `batchCompactAStmt`: compacts `base[0 .. l.length - 1]` in-place, keeping
entries `v` with `matchAStamp[v] ≠ batchGen`. -/
lemma batchCompactA_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {matchAStampAddr batchGen base : ℕ} {l : List ℕ} {M : Finset ℕ}
    (hl_lt : ∀ v ∈ l, v < X.card)
    (hdisj : DisjRange base l.length matchAStampAddr X.card)
    (hw_base : base + l.length + 5 < 2 ^ w)
    (hw_ma : matchAStampAddr + X.card + 5 < 2 ^ w)
    (hw_bg : batchGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hlist : ListAt st0.mem base l)
    (hma : ∀ v < X.card, st0.mem (matchAStampAddr + v) = batchGen ↔ origOf X v ∈ M)
    (hr16 : st0.regs 16 = matchAStampAddr)
    (hr17 : st0.regs 17 = batchGen)
    (hr23 : st0.regs 23 = base)
    (hr24 : st0.regs 24 = l.length) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω batchCompactAStmt st0 .normal st' c ∧
        (∀ r, r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → st'.regs r = st0.regs r) ∧
        st'.regs 25 = (l.filter fun v => decide (origOf X v ∉ M)).length ∧
        ListAt st'.mem base (l.filter fun v => decide (origOf X v ∉ M)) ∧
        (∀ a, ¬ (base ≤ a ∧ a < base + l.length) → st'.mem a = st0.mem a) ∧
        c ≤ 45 * l.length + 20 := by
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem rpos : ℕ) (st : State),
      rpos + rem = l.length →
      (∀ v < X.card, st.mem (matchAStampAddr + v) = batchGen ↔ origOf X v ∈ M) →
      ListAt st.mem base ((l.take rpos).filter fun v => decide (origOf X v ∉ M)) →
      (∀ j (hj : rpos ≤ j) (hjl : j < l.length), st.mem (base + j) = l[j]'hjl) →
      st.regs 16 = matchAStampAddr → st.regs 17 = batchGen →
      st.regs 23 = base → st.regs 24 = l.length →
      st.regs 25 = ((l.take rpos).filter fun v => decide (origOf X v ∉ M)).length → st.regs 26 = rpos →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 26) (.reg 24))
              (seqStmts
                [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
                , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
                , .cond (.bin .eq (.reg 28) (.reg 17))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 26 (.bin .add (.reg 26) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → st'.regs r = st.regs r) ∧
          st'.regs 25 = (l.filter fun v => decide (origOf X v ∉ M)).length ∧
          ListAt st'.mem base (l.filter fun v => decide (origOf X v ∉ M)) ∧
          (∀ a, ¬ (base ≤ a ∧ a < base + l.length) → st'.mem a = st.mem a) ∧
          c ≤ 45 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro rpos st hr _ hpref _ _ _ _ h24 h25 h26 ω
      have hr_eq : rpos = l.length := by omega
      have htk : l.take rpos = l := by rw [hr_eq, List.take_length]
      refine ⟨st, _, batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, h26, h24, hr_eq]),
        fun _ _ _ _ _ => rfl, by simpa [htk] using h25, by simpa [htk] using hpref,
        fun _ _ => rfl, by simp [Expr.size]⟩
    | succ rem ih =>
      intro rpos st hr hma_s hpref hsuf h16 h17 h23 h24 h25 h26 ω
      have hr_lt : rpos < l.length := by omega
      set v := l[rpos]'hr_lt
      have hv_lt : v < X.card := hl_lt v (List.getElem_mem hr_lt)
      set pref := (l.take rpos).filter fun x => decide (origOf X x ∉ M)
      have hpref_le : pref.length ≤ rpos := by
        have h1 : pref.length ≤ (l.take rpos).length :=
          List.length_filter_le (fun x => decide (origOf X x ∉ M)) (l.take rpos)
        simp only [List.length_take] at h1; omega
      have hpref_succ : (l.take (rpos + 1)).filter (fun x => decide (origOf X x ∉ M)) =
          pref ++ if origOf X v ∉ M then [v] else [] := by
        rw [List.take_succ_eq_append_getElem hr_lt, List.filter_append, List.filter_cons, List.filter_nil]
        by_cases hM : origOf X v ∉ M <;> simp [pref, v, hM]
      have hv_mem : st.mem (base + rpos) = v := hsuf rpos le_rfl hr_lt
      set sv := st.mem (matchAStampAddr + v)
      have hcond : (Expr.bin .lt (.reg 26) (.reg 24)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h26, h24, hr_lt, hw_ne]
      by_cases hM : origOf X v ∈ M
      · have hsv_eq : sv = batchGen := (hma_s v hv_lt).mpr hM
        set st1 : State :=
          { mem := st.mem
            regs := Function.update (Function.update (Function.update st.regs 27 v) 28 sv) 26 (rpos + 1)
            pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
                , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
                , .cond (.bin .eq (.reg 28) (.reg 17))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 26 (.bin .add (.reg 26) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 38 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
                  , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
                  , .cond (.bin .eq (.reg 28) (.reg 17))
                      .nop
                      (seqStmts
                        [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                        , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                  , .assign 26 (.bin .add (.reg 26) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 38 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := v) (by rw [← hv_mem]; eval_expr) ?_
            refine runs_seq_assign_le (v := sv) (by eval_expr) ?_
            refine runs_seq_cond_le (v := 1)
              (by simp [Expr.eval, BinOp.eval, h17, hsv_eq, hw_ne])
              (fun _ => ?_) (fun h => by omega)
            refine runs_seq_nop_le ?_
            refine runs_assign_le (v := rpos + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        obtain ⟨stF, cIH, hrunIH, hregsIH, h25F, hlistF, hfrF, hcIH⟩ :=
          ih (rpos + 1) st1 (by omega) hma_s
            (by rw [hpref_succ]; simp only [hM, not_true_eq_false, ↓reduceIte, List.append_nil]; exact hpref)
            (fun j hj1 hj2 => hsuf j (by omega) hj2)
            (by simp [st1, h16]) (by simp [st1, h17]) (by simp [st1, h23]) (by simp [st1, h24])
            (by rw [hpref_succ]; simp only [st1, h25, hM, not_true_eq_false, ↓reduceIte, List.append_nil,
                  Function.update_of_ne (by decide : (25 : ℕ) ≠ 26),
                  Function.update_of_ne (by decide : (25 : ℕ) ≠ 28),
                  Function.update_of_ne (by decide : (25 : ℕ) ≠ 27)]) (by simp [st1]) ω
        refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h25' h26' h27' h28' => (hregsIH r h25' h26' h27' h28').trans (by simp [st1, h26', h27', h28']),
          h25F, hlistF, hfrF, by simp only [Expr.size]; omega⟩
      · have hsv_ne : sv ≠ batchGen := fun h => hM ((hma_s v hv_lt).mp h)
        set mem1 := Function.update st.mem (base + pref.length) v
        set regs1 := Function.update (Function.update (Function.update (Function.update
          st.regs 27 v) 28 sv) 25 (pref.length + 1)) 26 (rpos + 1)
        set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
                , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
                , .cond (.bin .eq (.reg 28) (.reg 17))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                      , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                , .assign 26 (.bin .add (.reg 26) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 38 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
                  , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
                  , .cond (.bin .eq (.reg 28) (.reg 17))
                      .nop
                      (seqStmts
                        [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                        , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
                  , .assign 26 (.bin .add (.reg 26) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 38 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := v) (by rw [← hv_mem]; eval_expr) ?_
            refine runs_seq_assign_le (v := sv) (by eval_expr) ?_
            refine runs_seq_cond_le (v := 0)
              (by simp [Expr.eval, BinOp.eval, h17, hsv_ne])
              (fun h => absurd rfl h) (fun _ => ?_)
            refine batch_runs_seq_seq_le ?_
            refine runs_seq_store_le (x := base + pref.length) (v := v) (by eval_expr) (by eval_expr) ?_
            refine runs_seq_assign_le (v := pref.length + 1) (by eval_expr) ?_
            refine runs_assign_le (v := rpos + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hma1 : ∀ u < X.card, st1.mem (matchAStampAddr + u) = batchGen ↔ origOf X u ∈ M := by
          intro u hu
          simp only [st1, mem1, Function.update_of_ne (by rcases hdisj with x | x <;> omega : matchAStampAddr + u ≠ base + pref.length)]
          exact hma_s u hu
        have hpref1 : ListAt st1.mem base ((l.take (rpos + 1)).filter fun x => decide (origOf X x ∉ M)) := by
          rw [hpref_succ]; simp only [hM, not_false_eq_true, ↓reduceIte]
          intro j hj
          by_cases hjp : j < pref.length
          · rw [List.getElem_append_left hjp]
            simp only [st1, mem1, Function.update_of_ne (by omega : base + j ≠ base + pref.length)]
            exact hpref j hjp
          · have hj_eq : j = pref.length := by simp at hj; omega
            subst hj_eq; rw [List.getElem_append_right (le_refl _)]; simp [st1, mem1]
        have hsuf1 : ∀ j (hj1 : rpos + 1 ≤ j) (hj2 : j < l.length), st1.mem (base + j) = l[j]'hj2 := by
          intro j hj1 hj2
          simp only [st1, mem1, Function.update_of_ne (by omega : base + j ≠ base + pref.length)]
          exact hsuf j (by omega) hj2
        obtain ⟨stF, cIH, hrunIH, hregsIH, h25F, hlistF, hfrF, hcIH⟩ :=
          ih (rpos + 1) st1 (by omega) hma1 hpref1 hsuf1
            (by simp [st1, regs1, h16]) (by simp [st1, regs1, h17])
            (by simp [st1, regs1, h23]) (by simp [st1, regs1, h24])
            (by rw [hpref_succ]; simp only [st1, regs1, hM, not_false_eq_true, ↓reduceIte,
                  List.length_append, List.length_singleton,
                  Function.update_of_ne (by decide : (25 : ℕ) ≠ 26), Function.update_self]) (by simp [st1, regs1]) ω
        refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h25' h26' h27' h28' => (hregsIH r h25' h26' h27' h28').trans (by simp [st1, regs1, h25', h26', h27', h28']),
          h25F, hlistF,
          fun a ha => (hfrF a ha).trans (by simp [st1, mem1, Function.update_of_ne (by omega : a ≠ base + pref.length)]),
          by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 25 0) 26 0
      pos := st0.pos }
  have hinit : ∃ c1,
      Runs w p ω (seqStmts [ .assign 25 (.const 0), .assign 26 (.const 0) ]) st0 .normal st1 c1 ∧
      c1 ≤ 8 := by
    have h0' : ∃ o s c,
        Runs w p ω (seqStmts [ .assign 25 (.const 0), .assign 26 (.const 0) ]) st0 o s c ∧
        (o = .normal ∧ s = st1) ∧ 0 + c ≤ 8 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
    exact ⟨c1, hrun, by omega⟩
  rcases hinit with ⟨c1, hrun1, hc1⟩
  obtain ⟨stF, cL, hrunL, hregsL, h25F, hlistF, hfrF, hcL⟩ :=
    hloop l.length 0 st1 (Nat.zero_add _) hma (by simp [ListAt])
      (fun j _ hj => hlist j hj)
      (by simp [st1, hr16]) (by simp [st1, hr17]) (by simp [st1, hr23]) (by simp [st1, hr24])
      (by simp [st1]) (by simp [st1]) ω
  have hrun_all : Runs w p ω batchCompactAStmt st0 .normal stF (c1 + cL + 1) := by
    unfold batchCompactAStmt; dsimp only [seqStmts] at hrun1 ⊢
    rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
    exact runs_seq_iff.mpr (Or.inr ⟨q, cq1, _, hq1,
      runs_seq_iff.mpr (Or.inr ⟨st1, cq2, cL, hq2, hrunL, rfl⟩), by omega⟩)
  refine ⟨stF, c1 + cL + 1, hrun_all,
    fun r h25' h26' h27' h28' => (hregsL r h25' h26' h27' h28').trans (by simp [st1, h25', h26']),
    h25F, hlistF, hfrF, by omega⟩

/-- Verification of `batchAppendChunkStmt`: if `spLen > 0`, allocates a 2-word chunk `[spHead, 0]`
at `chunkHeapPtr` and tail-links it onto `(accHead[i], accTail[i])`. -/
lemma batchAppendChunk_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {accHeadAddr accTailAddr k i pLo pHi cLo cHi spHead : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))} {newPs : List ((ℕ × ℕ) × List ℕ)}
    (hi : i < k)
    (hp_le : pLo ≤ pHi) (hc_le : cLo ≤ cHi) (hc_pos : 0 < cLo)
    (hdisj_ah_at : DisjRange accHeadAddr k accTailAddr k)
    (hdisj_ah_c : DisjRange accHeadAddr k cLo (cHi + 2 - cLo))
    (hdisj_at_c : DisjRange accTailAddr k cLo (cHi + 2 - cLo))
    (hdisj_ah_p : DisjRange accHeadAddr k pLo (pHi - pLo))
    (hdisj_at_p : DisjRange accTailAddr k pLo (pHi - pLo))
    (hdisj_pc : DisjRange pLo (pHi - pLo) cLo (cHi + 2 - cLo))
    (hw_ah : accHeadAddr + k + 5 < 2 ^ w)
    (hw_at : accTailAddr + k + 5 < 2 ^ w)
    (hw_c : cHi + 5 < 2 ^ w)
    (hw_p : pHi + 5 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hch : ChunkChainAt st0.mem X pLo pHi cLo cHi
      (st0.mem (accHeadAddr + i)) (st0.mem (accTailAddr + i)) chunks)
    (hpl : PathListAt st0.mem X pLo pHi spHead newPs)
    (hr12 : st0.regs 12 = accHeadAddr) (hr13 : st0.regs 13 = accTailAddr)
    (hr21 : st0.regs 21 = cHi) (hr22 : st0.regs 22 = spHead)
    (hr25 : st0.regs 25 = newPs.length) (hr29 : st0.regs 29 = i) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω batchAppendChunkStmt st0 .normal st' c ∧
        (∀ r, r ≠ 21 → r ≠ 26 → r ≠ 27 → st'.regs r = st0.regs r) ∧
        st'.regs 21 = (if newPs = [] then cHi else cHi + 2) ∧
        ChunkChainAt st'.mem X pLo pHi cLo (if newPs = [] then cHi else cHi + 2)
          (st'.mem (accHeadAddr + i)) (st'.mem (accTailAddr + i))
          (if newPs = [] then chunks else chunks ++ [newPs]) ∧
        chunkAddrs st'.mem (st'.mem (accHeadAddr + i))
          (if newPs = [] then chunks else chunks ++ [newPs]).length =
          (if newPs = [] then chunkAddrs st0.mem (st0.mem (accHeadAddr + i)) chunks.length
           else chunkAddrs st0.mem (st0.mem (accHeadAddr + i)) chunks.length ++ [cHi]) ∧
        (∀ a, ¬ (a = accHeadAddr + i ∨ a = accTailAddr + i ∨
                 (cLo ≤ a ∧ a < cHi + 2)) → st'.mem a = st0.mem a) ∧
        (∀ j < k, j ≠ i →
          st'.mem (accHeadAddr + j) = st0.mem (accHeadAddr + j) ∧
          st'.mem (accTailAddr + j) = st0.mem (accTailAddr + j)) ∧
        (∀ a, cLo ≤ a → a < cHi →
          (chunks = [] ∨ a ≠ st0.mem (accTailAddr + i) + 1) → st'.mem a = st0.mem a) ∧
        c ≤ 50 := by
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hp_le
  have hc_sub : cLo + (cHi + 2 - cLo) = cHi + 2 := Nat.add_sub_cancel' (by omega)
  intro ω
  cases newPs with
  | nil =>
    have hcond : (Expr.reg 25).eval w st0 = some 0 := by simp [Expr.eval, hr25]
    refine ⟨st0, _, runs_cond_iff.mpr ⟨0, 1, hcond, by simp [runs_nop_iff], rfl⟩,
      fun _ _ _ _ => rfl, by simp [hr21], by simpa using hch, by simp,
      fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, by simp [Expr.size]⟩
  | cons q rest =>
    set newPs' := q :: rest
    have hne_nil : newPs' ≠ [] := List.cons_ne_nil _ _
    have hspHead_lt : spHead < 2 ^ w := by
      rcases q with ⟨⟨_, _⟩, _⟩; rcases hpl with ⟨_, hhi, _⟩; omega
    set oldHead := st0.mem (accHeadAddr + i)
    set oldTail := st0.mem (accTailAddr + i)
    have hmem_ch := ChunkChainAt.append_fresh hch hne_nil hpl hc_le rfl (by omega) hdisj_pc hp_le
    dsimp only at hmem_ch
    set mem1 := Function.update (Function.update st0.mem cHi spHead) (cHi + 1) 0
    have hmem1_ah : mem1 (accHeadAddr + i) = oldHead := by
      simp only [mem1,
        Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + i ≠ cHi + 1),
        Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + i ≠ cHi)]
      rfl
    have hmem1_at : mem1 (accTailAddr + i) = oldTail := by
      simp only [mem1,
        Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + i ≠ cHi + 1),
        Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + i ≠ cHi)]
      rfl
    by_cases hh0 : oldHead = 0
    · set memF := Function.update (Function.update mem1 (accHeadAddr + i) cHi) (accTailAddr + i) cHi
      set regsF := Function.update (Function.update st0.regs 26 0) 21 (cHi + 2)
      set stF : State := { mem := memF, regs := regsF, pos := st0.pos }
      have hrun : ∃ c, Runs w p ω batchAppendChunkStmt st0 .normal stF c ∧ c ≤ 50 := by
        have h0' : ∃ o s c, Runs w p ω batchAppendChunkStmt st0 o s c ∧
            (o = .normal ∧ s = stF) ∧ 0 + c ≤ 50 := by
          unfold batchAppendChunkStmt
          refine runs_cond_pos_le (v := newPs'.length) (by simp [Expr.eval, hr25, newPs']) (by simp [newPs']) ?_
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := cHi) (v := spHead) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := cHi + 1) (v := 0) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := 0)
            (by simp only [Expr.eval, BinOp.eval, hr12, hr29, show accHeadAddr + i < 2 ^ w by omega, ↓reduceIte]
                exact congrArg some (hmem1_ah.trans hh0)) ?_
          refine runs_seq_cond_le (v := 0) (by eval_expr) (fun h => absurd rfl h) (fun _ => ?_)
          refine runs_seq_store_le (x := accHeadAddr + i) (v := cHi) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := accTailAddr + i) (v := cHi) (by eval_expr) (by eval_expr) ?_
          refine runs_assign_le (v := cHi + 2) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0' with ⟨_, _, c, hrun, ⟨rfl, rfl⟩, hc⟩
        exact ⟨c, hrun, by omega⟩
      rcases hrun with ⟨c, hrun, hc⟩
      have hch_eq : ChunkChainAt stF.mem X pLo pHi cLo (cHi + 2)
          (stF.mem (accHeadAddr + i)) (stF.mem (accTailAddr + i)) (chunks ++ [newPs']) := by
        have h1 : stF.mem (accHeadAddr + i) = cHi := by
          simp only [stF, memF,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + i ≠ accTailAddr + i),
            Function.update_self]
        have h2 : stF.mem (accTailAddr + i) = cHi := by simp [stF, memF]
        rw [h1, h2]
        simp only [hh0, ↓reduceIte] at hmem_ch
        exact hmem_ch.congr
          (fun k hk1 hk2 => by
            simp only [stF, memF,
              Function.update_of_ne (by rcases hdisj_at_p with x | x <;> omega : k ≠ accTailAddr + i),
              Function.update_of_ne (by rcases hdisj_ah_p with x | x <;> omega : k ≠ accHeadAddr + i)])
          (fun k hk1 hk2 => by
            simp only [stF, memF,
              Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : k ≠ accTailAddr + i),
              Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : k ≠ accHeadAddr + i)])
      have haddrs_eq : chunkAddrs stF.mem (stF.mem (accHeadAddr + i)) (chunks ++ [newPs']).length =
          chunkAddrs st0.mem oldHead chunks.length ++ [cHi] := by
        have h1 : stF.mem (accHeadAddr + i) = cHi := by
          simp only [stF, memF,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + i ≠ accTailAddr + i),
            Function.update_self]
        have hch_nil : chunks = [] := by
          by_contra hne; exact (hch.head_ne_zero hne).1 hh0
        subst hch_nil; simp [h1, chunkAddrs]
      refine ⟨stF, c, hrun,
        fun r h21 h26 h27 => by simp [stF, regsF, h21, h26],
        by simp [stF, regsF, newPs'],
        by simp only [newPs', List.cons_ne_nil, ↓reduceIte]; exact hch_eq,
        by simp only [newPs', List.cons_ne_nil, ↓reduceIte]; exact haddrs_eq,
        fun a ha => by
          simp only [stF, memF, mem1,
            Function.update_of_ne (by tauto : a ≠ accTailAddr + i),
            Function.update_of_ne (by tauto : a ≠ accHeadAddr + i),
            Function.update_of_ne (by omega : a ≠ cHi + 1),
            Function.update_of_ne (by omega : a ≠ cHi)],
        fun j hj hji => ⟨by
          simp only [stF, memF, mem1,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + j ≠ accTailAddr + i),
            Function.update_of_ne (by omega : accHeadAddr + j ≠ accHeadAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + j ≠ cHi + 1),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + j ≠ cHi)],
          by
          simp only [stF, memF, mem1,
            Function.update_of_ne (by omega : accTailAddr + j ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accTailAddr + j ≠ accHeadAddr + i),
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + j ≠ cHi + 1),
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + j ≠ cHi)]⟩,
        fun a ha1 ha2 _ => by
          simp only [stF, memF, mem1,
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : a ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : a ≠ accHeadAddr + i),
            Function.update_of_ne (by omega : a ≠ cHi + 1),
            Function.update_of_ne (by omega : a ≠ cHi)],
        hc⟩
    · have hchunks_ne : chunks ≠ [] := by intro he; subst he; exact hh0 hch.1
      have hinfo := hch.head_ne_zero hchunks_ne
      have ht_lo : cLo ≤ oldTail := hinfo.2.1
      have ht_hi : oldTail + 2 ≤ cHi := hinfo.2.2.1
      have hoh_lt : oldHead < 2 ^ w := by
        cases chunks with
        | nil => exact absurd rfl hchunks_ne
        | cons _ r => cases r with | nil => have := hch.1; omega | cons _ _ => have := hch.2.1; omega
      set mem2 := Function.update mem1 (oldTail + 1) cHi
      set memF := Function.update mem2 (accTailAddr + i) cHi
      set regsF := Function.update (Function.update (Function.update st0.regs 26 oldHead) 27 oldTail) 21 (cHi + 2)
      set stF : State := { mem := memF, regs := regsF, pos := st0.pos }
      have hrun : ∃ c, Runs w p ω batchAppendChunkStmt st0 .normal stF c ∧ c ≤ 50 := by
        have h0' : ∃ o s c, Runs w p ω batchAppendChunkStmt st0 o s c ∧
            (o = .normal ∧ s = stF) ∧ 0 + c ≤ 50 := by
          unfold batchAppendChunkStmt
          refine runs_cond_pos_le (v := newPs'.length) (by simp [Expr.eval, hr25, newPs']) (by simp [newPs']) ?_
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := cHi) (v := spHead) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := cHi + 1) (v := 0) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := oldHead)
            (by simp only [Expr.eval, BinOp.eval, hr12, hr29, show accHeadAddr + i < 2 ^ w by omega, ↓reduceIte]
                exact congrArg some hmem1_ah) ?_
          refine runs_seq_cond_le (v := oldHead) (by eval_expr) (fun _ => ?_) (fun h => absurd h hh0)
          refine batch_runs_seq_seq_le ?_
          refine runs_seq_assign_le (v := oldTail)
            (by simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (13 : ℕ) ≠ 26),
                  Function.update_of_ne (by decide : (29 : ℕ) ≠ 26), hr13, hr29,
                  show accTailAddr + i < 2 ^ w by omega, ↓reduceIte]
                exact congrArg some hmem1_at) ?_
          refine runs_seq_store_le (x := oldTail + 1) (v := cHi) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := accTailAddr + i) (v := cHi) (by eval_expr) (by eval_expr) ?_
          refine runs_assign_le (v := cHi + 2) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0' with ⟨_, _, c, hrun, ⟨rfl, rfl⟩, hc⟩
        exact ⟨c, hrun, by omega⟩
      rcases hrun with ⟨c, hrun, hc⟩
      have hch_eq : ChunkChainAt stF.mem X pLo pHi cLo (cHi + 2)
          (stF.mem (accHeadAddr + i)) (stF.mem (accTailAddr + i)) (chunks ++ [newPs']) := by
        have h1 : stF.mem (accHeadAddr + i) = oldHead := by
          simp only [stF, memF, mem2,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + i ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + i ≠ oldTail + 1)]
          exact hmem1_ah
        have h2 : stF.mem (accTailAddr + i) = cHi := by simp [stF, memF]
        rw [h1, h2]
        simp only [hh0, ↓reduceIte] at hmem_ch
        exact hmem_ch.congr
          (fun k hk1 hk2 => by
            simp only [stF, memF, Function.update_of_ne (by rcases hdisj_at_p with x | x <;> omega : k ≠ accTailAddr + i)])
          (fun k hk1 hk2 => by
            simp only [stF, memF, Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : k ≠ accTailAddr + i)])
      have haddrs_eq : chunkAddrs stF.mem (stF.mem (accHeadAddr + i)) (chunks ++ [newPs']).length =
          chunkAddrs st0.mem oldHead chunks.length ++ [cHi] := by
        have h1 : stF.mem (accHeadAddr + i) = oldHead := by
          simp only [stF, memF, mem2,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + i ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + i ≠ oldTail + 1)]
          exact hmem1_ah
        rw [h1, List.length_append, List.length_singleton]
        have hca := hch.chunkAddrs_append_fresh (mem' := stF.mem) (cHi := cHi) (fun a ha => by
          have hab := hch.chunkAddrs_bounds a ha
          simp only [stF, memF, mem2, mem1,
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : a + 1 ≠ accTailAddr + i)]
          by_cases hat : a = oldTail
          · subst hat; simp
          · simp [hat, Function.update_of_ne (by omega : a + 1 ≠ cHi + 1),
              Function.update_of_ne (by omega : a + 1 ≠ cHi)])
        simpa [hh0] using hca
      refine ⟨stF, c, hrun,
        fun r h21 h26 h27 => by simp [stF, regsF, h21, h26, h27],
        by simp [stF, regsF, newPs'],
        by simp only [newPs', List.cons_ne_nil, ↓reduceIte]; exact hch_eq,
        by simp only [newPs', List.cons_ne_nil, ↓reduceIte]; exact haddrs_eq,
        fun a ha => by
          simp only [stF, memF, mem2, mem1,
            Function.update_of_ne (by tauto : a ≠ accTailAddr + i),
            Function.update_of_ne (by omega : a ≠ oldTail + 1),
            Function.update_of_ne (by omega : a ≠ cHi + 1),
            Function.update_of_ne (by omega : a ≠ cHi)],
        fun j hj hji => ⟨by
          simp only [stF, memF, mem2, mem1,
            Function.update_of_ne (by rcases hdisj_ah_at with x | x <;> omega : accHeadAddr + j ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + j ≠ oldTail + 1),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + j ≠ cHi + 1),
            Function.update_of_ne (by rcases hdisj_ah_c with x | x <;> omega : accHeadAddr + j ≠ cHi)],
          by
          simp only [stF, memF, mem2, mem1,
            Function.update_of_ne (by omega : accTailAddr + j ≠ accTailAddr + i),
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + j ≠ oldTail + 1),
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + j ≠ cHi + 1),
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : accTailAddr + j ≠ cHi)]⟩,
        fun a ha1 ha2 hne_t => by
          have hne_t' : a ≠ oldTail + 1 := hne_t.resolve_left (by intro hnil; subst hnil; exact hh0 hch.1)
          simp only [stF, memF, mem2, mem1,
            Function.update_of_ne (by rcases hdisj_at_c with x | x <;> omega : a ≠ accTailAddr + i),
            Function.update_of_ne hne_t',
            Function.update_of_ne (by omega : a ≠ cHi + 1),
            Function.update_of_ne (by omega : a ≠ cHi)],
        hc⟩

end MinCostFlow.ExpanderDecomp
