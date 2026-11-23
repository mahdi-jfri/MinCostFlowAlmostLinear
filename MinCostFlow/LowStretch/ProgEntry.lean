module

public import MinCostFlow.LowStretch.ProgEntryProcs
public import MinCostFlow.LowStretch.ProgEntryCost

/-!
# The entry

The entry `entryB bCl` is procedure `0`. It reads `n` and `m`. If `n < 2` it returns the empty
tree. Otherwise it runs the preprocessing (procedure `1`), reads the five control cells, calls the
cluster procedure at `bCl` on the first cluster, and copies the tree to address `0` with `outS`.

`entry_run` shows that, at word size `wordSize (340 + A) G.encode` and when the cluster procedure
meets `clC`, the entry returns a spanning tree with small total stretch, within
`preCost G + clB A G + 4 n kidCost + 30 m + 17 n + 1400` steps.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The arguments of the call of the cluster procedure: `n`, `m` in registers `0`, `1`, the
number of nodes in register `2`, the threshold, its exponent, `s` and `nS` in registers `3` to
`6`, and the addresses of the arrays. -/
def clArgs : List Expr :=
  [.reg 0, .reg 1, .const 2, lin 8 4 0, lin 8 3 0, .reg 2, lin 9 9 7, lin 9 9 9, lin 9 9 11,
    lin 9 9 13, lin 9 9 15, lin 9 9 17, lin 9 9 19, lin 9 9 21, lin 9 9 23, lin 9 9 24,
    lin 9 10 24, lin 10 10 28, lin 15 11 30, lin 15 11 32, lin 2 3 0, .reg 3, .reg 4, .reg 5,
    lin 15 11 28, .reg 6, lin 15 11 34, lin 15 13 34, lin 15 13 35]

theorem clArgs_size : argsSize clArgs = 197 := rfl

/-- The entry: procedure `0`. The preprocessing is at `1`, `copyWords` at `26`, and the cluster
procedure at `bCl`. -/
def entryB (bCl : ℕ) : Stmt :=
  .seq (.assign 0 (.load (.const 0)))
  (.seq (.assign 1 (.load (.const 1)))
  (.cond (.bin .lt (.reg 0) (.const 2)) (.ret (.const 0))
  (.seq (.call 2 1 [.reg 0, .reg 1])
  (.seq (.assign 3 (.load (lin 11 11 28)))
  (.seq (.assign 4 (.load (lin 12 11 28)))
  (.seq (.assign 5 (.load (lin 13 11 28)))
  (.seq (.assign 6 (.load (lin 14 11 28)))
  (.seq (.call 7 bCl clArgs)
  (outS 26 (lin 15 13 34))))))))))

theorem lin_eval_eq {w : ℕ} {st : State} {n m c u v x : ℕ} (h0 : st.regs 0 = n)
    (h1 : st.regs 1 = m) (hb : c + u * m + v * n + u + v < 2 ^ w) (hx : c + u * m + v * n = x) :
    (lin c u v).eval w st = some x :=
  hx ▸ lin_eval h0 h1 hb

theorem evalArgs_cons_of {w : ℕ} {st : State} {e : Expr} {es : List Expr} {v : ℕ} {vs : List ℕ}
    (he : e.eval w st = some v) (hs : evalArgs w st es = some vs) :
    evalArgs w st (e :: es) = some (v :: vs) := by
  simp [evalArgs, he, hs]

variable {G : WGraph}

/-- **The run of the entry.** -/
theorem entry_run {p : Program} {A bCl : ℕ} (hp : p.HasAt 0 (entryB bCl :: preProcs 1))
    (hCl : ∀ w G T, MeetsContract w p bCl (clC w A G T)) (h : Allowed G) (ω : ℕ → Bool) :
    ∃ o st c, Runs (wordSize (340 + A) G.encode) p ω (entryB bCl)
        (startState [G.encode.length] (initMem G.encode) 0) o st c ∧
      (∃ Tr : List ℕ, o = .returned Tr.length ∧ ListAt st.mem 0 Tr ∧ G.IsSpanningTree Tr ∧
        G.totalStretch Tr ≤ Kst * G.m * logLogFactor G.n) ∧
      c ≤ preCost G + clB A G + 4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n + 30 * G.m +
        17 * G.n + 1400 := by
  have hn := h.conn.1
  have hroom := fun T hok hN => clC_word (T := T) A h hok hN
  generalize hwd : wordSize (340 + A) G.encode = w at hroom ⊢
  have hword := word_bound (c := 340 + A) (by omega) G
  rw [hwd] at hword
  have hX : aH G.n G.m + (pgOf G).maxω + 2 < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_self_pow (by norm_num) _) hword
  unfold aH at hX
  have hpre1 : p.HasAt 1 (preProcs 1) := fun i hi => by
    have := hp (i + 1) (by simp only [List.length_cons]; omega)
    simpa [Nat.add_comm] using this
  have hPre := preP_meets (w := w) hpre1 G
  have hcp : p.HasAt 26 [copyWords] := copy_at hpre1
  have hm0 : initMem G.encode 0 = G.n := by simp [initMem, WGraph.encode]
  have hm1 : initMem G.encode 1 = G.m := by simp [initMem, WGraph.encode]
  dsimp only [entryB]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := G.n)
    (Expr.eval_load_of_eq (Expr.eval_const (by omega)) hm0) ?_
  refine runs_seq_assign_le (v := G.m)
    (Expr.eval_load_of_eq (Expr.eval_const (by omega)) hm1) ?_
  refine runs_cond_le (Expr.eval_lt_op (Expr.eval_reg_of_eq (v := G.n) (by simp [startState]))
    (Expr.eval_const (by omega)) (by omega)) ?_ ?_
  · -- `n = 1`: the empty tree
    intro hc
    have hn2 : G.n < 2 := by
      by_contra hh
      simp [hh] at hc
    obtain ⟨θ, T, hθ, hT⟩ := exists_tree h
    have hsp := run_spec h hθ hT
    have hT0 : T = [] := List.eq_nil_of_length_eq_zero (by have := hsp.1.2.2.1; omega)
    subst hT0
    refine runs_ret_le (Expr.eval_const (by omega)) ⟨[], rfl, listAt_nil _ _, hsp⟩ ?_
    simp only [Expr.size]
    omega
  intro hc
  have hn2 : 2 ≤ G.n := by
    by_contra hh
    simp only [show G.n < 2 by omega, ite_true] at hc
    exact one_ne_zero hc
  have hI : InG w G (initMem G.encode) := inG_init h hn2 hword
  have hZ : ZeroFrom (initMem G.encode) (aPAR G.n G.m) := fun a ha =>
    zeroFrom_initMem _ a (by rw [encode_length]; unfold aPAR at ha; omega)
  refine runs_seq_call_le (vs := [G.n, G.m]) hPre (by simp [evalArgs, Expr.eval])
    (by wram_words) ⟨rfl, hI, hZ⟩ ?_
  intro N mem2 pos2 hpost
  obtain ⟨T, rfl, hE, c0, c1, c2, c3, c4⟩ := hpost
  have hok := hE.ok
  have hw4 := hI.add_lt
  unfold aH at hw4
  have hN2 := hE.N_le
  have hθw := rootθ_lt hI hok.tree
  have h1θ := one_le_rootθ (T := T) (G := G)
  have hlθ : Nat.log 2 (rootθ T G) ≤ rootθ T G := (Nat.log_lt_self 2 (by omega)).le
  have hs := hE.lay.l17
  have hnS := hE.lay.l20
  simp only [eaOf, aNODES, aLAB, aSA, aOUT] at hs hnS
  refine runs_seq_assign_le (v := rootθ T G) (Expr.eval_load_of_eq
    (lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp) (by omega)
      (show 11 + 11 * G.m + 28 * G.n = aCTL G.n G.m + 1 by unfold aCTL; omega)) c1) ?_
  refine runs_seq_assign_le (v := Nat.log 2 (rootθ T G)) (Expr.eval_load_of_eq
    (lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp) (by omega)
      (show 12 + 11 * G.m + 28 * G.n = aCTL G.n G.m + 2 by unfold aCTL; omega)) c2) ?_
  refine runs_seq_assign_le (v := (rootRec T G).nodes.length) (Expr.eval_load_of_eq
    (lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp) (by omega)
      (show 13 + 11 * G.m + 28 * G.n = aCTL G.n G.m + 3 by unfold aCTL; omega)) c3) ?_
  refine runs_seq_assign_le (v := (rootRec T G).S.length) (Expr.eval_load_of_eq
    (lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp) (by omega)
      (show 14 + 11 * G.m + 28 * G.n = aCTL G.n G.m + 4 by unfold aCTL; omega)) c4) ?_
  refine runs_seq_call_le (vs := (eaOf G T).args) (hCl w G T) ?_ ?_
    ⟨eaOf G T, rfl, hE, hroom T hok hN2⟩ ?_
  · simp only [clArgs, EA.args, eaOf]
    repeat' refine evalArgs_cons_of ?_ ?_
    all_goals first
      | rfl
      | exact Expr.eval_reg_of_eq (by simp)
      | exact Expr.eval_const (by omega)
      | (refine lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp)
          ?_ ?_ <;>
        (try simp only [aPW, aEXP, aKPAR, aKCH1, aKCH2, aKMW, aKMP, aKSZ, aKLO, aHEAD, aORDL,
          aLCA, aGOFF, aGORD, aLAB, aLOC, aPAR, aNODES, aSA, aOUT, aH]) <;> omega)
  · simp only [EA.args, eaOf, aPW, aEXP, aKPAR, aKCH1, aKCH2, aKMW, aKMP, aKSZ, aKLO, aHEAD,
      aORDL, aLCA, aGOFF, aGORD, aLAB, aLOC, aPAR, aNODES, aSA, aOUT, aH, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;> omega
  intro v mem3 pos3 hcl
  obtain ⟨Tr, hRun, rfl, hList⟩ := hcl (eaOf G T) rfl
  have hsp := run_spec h hok.inv hRun
  have hlen : Tr.length = G.n - 1 := hsp.1.2.2.1
  have hclc := clCost_le w A h hok hN2
  refine outS_run hcp (OUT := aOUT G.n G.m)
    (lin_eval_eq (n := G.n) (m := G.m) (by simp) (by simp) (by omega)
      (by unfold aOUT; omega)) (by simp) hList (by unfold aOUT; omega)
    (by unfold aOUT; omega) (by omega) (fun st' hl => ⟨Tr, rfl, hl, hsp⟩) ?_
  simp only [preC, clC, argsSize, Expr.size, lin_size, clArgs_size]
  omega

end MinCostFlow.LowStretch
