module

public import MinCostFlow.SparseCore.Program.ReadLib

import WordRAM.Tactic

/-!
# A split of the tree that moves the live ends at the new vertex

A vertex split of `G` at `v` (new vertex `v'`) splits the tree `T` too (`tViewUpdate`). When the
batch lists the kept ends at `v` (tag `3`), every unlisted end moves, but the frozen edges of the
tree (deleted from `G`) must not move. One way to split `T` is to list the ends that move: after
the live part of the tree (`liveT`) has been split, its ends at `v'` are exactly the ends of `T`
that move (`split_move_cond`, `ReadTree.lean`).

`splitMoveStmt` (`[tPtr, livePtr, v, v', out]`) writes at `out` the edges of the split live part
`K` with tail at `v'`, then those with head at `v'` (`collectStmt`), and applies the split to `T`
with these two lists as the moved ends (`dgApplySplit`, tag `2`). It costs at most
`800 · deg_K(v') + 600` (`splitMove_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- `[tPtr, livePtr, v, v', out]`: list the edges of the graph at `livePtr` with tail at `v'`
(at `out`) and with head at `v'` (right after), and split the graph at `tPtr` at `v` with these
lists as the moved ends. -/
def splitMoveStmt (L : ReadLib) : Stmt :=
  .call 5 L.collect [.reg 1, .reg 3, .const 0, .reg 4] ;;
  .call 6 L.collect [.reg 1, .reg 3, .const 1, .bin .add (.reg 4) (.reg 5)] ;;
  .call 7 (L.split + dgIdxApplySplit)
    [.reg 0, .const 2, .reg 2, .reg 3, .reg 5, .reg 6, .reg 4] ;;
  .ret (.const 0)

theorem splitMoveStmt_noRand (L : ReadLib) : (splitMoveStmt L).NoRand := by
  simp [splitMoveStmt, Stmt.NoRand]

/-- Contract of `splitMoveStmt` for the tree `T` (caps `vCap`, `tCap`), the graph `K` (caps
`vCap`, `eCap`) whose ends at `v'` are the ends of `T` that move, and the moved sets `St`, `Sh` of
the split. The blocks lie below the scratch `[out, out + 2 eCap)`. -/
def splitMoveContract (w vCap eCap tCap : ℕ) (T K : MGraph) (St Sh : Finset ℕ) : Contract where
  pre args mem := ∃ tPtr livePtr v v' out, args = [tPtr, livePtr, v, v', out] ∧
    16 ≤ 2 ^ w ∧ tPtr + dynGraphSize vCap tCap ≤ out ∧ livePtr + dynGraphSize vCap eCap ≤ out ∧
    out + 2 * eCap < 2 ^ w ∧ v ∈ T.V ∧ v' ∉ T.V ∧ v' < vCap ∧ v' ∈ K.V ∧
    DynGraphAt mem tPtr vCap tCap T ∧ DynGraphAt mem livePtr vCap eCap K ∧
    (∀ e ∈ T.E, (e ∈ K.E ∧ K.tail e = v') ↔ (T.tail e = v ∧ e ∈ St)) ∧
    (∀ e ∈ T.E, (e ∈ K.E ∧ K.head e = v') ↔ (T.head e = v ∧ e ∈ Sh))
  post args mem ret mem' := ∃ tPtr livePtr v v' out, args = [tPtr, livePtr, v, v', out] ∧
    ret = 0 ∧ DynGraphAt mem' tPtr vCap tCap (T.applyUpdate (.split v v' (St ∩ T.E) (Sh ∩ T.E))) ∧
    ∀ a, (a < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ a) → (a < out ∨ out + 2 * eCap ≤ a) →
      mem' a = mem a
  cost args _ := 800 * K.deg (args.getD 3 0) + 600

/-- `splitMoveStmt` meets `splitMoveContract`. -/
theorem splitMove_meetsContract {w : ℕ} {p : Program} {L : ReadLib} {f vCap eCap tCap : ℕ}
    {T K : MGraph} {St Sh : Finset ℕ} (hL : L.Has p) (hp : p.procs[f]? = some (splitMoveStmt L)) :
    MeetsContract w p f (splitMoveContract w vCap eCap tCap T K St Sh) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨tPtr, livePtr, v, v', out, rfl, hw16, hT1, hl1, hout, hvT, hv'T,
    hv'c, hv'K, hT, hK, hcT, hcH⟩
  have hv'w : v' < 2 ^ w := hargs _ (by simp)
  have hvw : v < 2 ^ w := hargs _ (by simp)
  have hlw : livePtr < 2 ^ w := hargs _ (by simp)
  have htw : tPtr < 2 ^ w := hargs _ (by simp)
  have hKcap : ∀ e ∈ K.E, e < eCap := hK.2.2.1
  have hDe : 0 < dynGraphSize vCap eCap := by simp [dynGraphSize]
  apply runs_start_le
  -- the edges of `K` with tail at `v'`
  refine runs_seq_call_le (hL.collect vCap eCap K) (vs := [livePtr, v', 0, out]) (by eval_expr)
    (by wram_words) ⟨livePtr, v', 0, out, rfl, hw16, by omega, by omega, hv'K, by omega, hK,
      fun i _ => Or.inr (by omega)⟩ ?_
  rintro nt mem1 pos1 ⟨_, _, _, _, hEq1, Lt, hLtnd, hLtm, rfl, hLtAt, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq1
  replace hfr1 : ∀ a, a < out ∨ out + Lt.length ≤ a → mem1 a = mem a := hfr1
  have hLtle : Lt.length ≤ eCap :=
    length_le_of_nodup_lt hLtnd fun e he => hKcap e ((hLtm e).mp he).1
  have hK1 : DynGraphAt mem1 livePtr vCap eCap K :=
    hK.of_agree fun a _ ha => hfr1 a (Or.inl (by omega))
  -- the edges of `K` with head at `v'`
  refine runs_seq_call_le (hL.collect vCap eCap K) (vs := [livePtr, v', 1, out + Lt.length])
    (by eval_expr) (by wram_words) ⟨livePtr, v', 1, out + Lt.length, rfl, hw16, by omega,
      by omega, hv'K, by omega, hK1, fun i _ => Or.inr (by omega)⟩ ?_
  rintro nh mem2 pos2 ⟨_, _, _, _, hEq2, Lh, hLhnd, hLhm, rfl, hLhAt, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq2
  replace hfr2 : ∀ a, a < out + Lt.length ∨ out + Lt.length + Lh.length ≤ a → mem2 a = mem1 a :=
    hfr2
  have hLhle : Lh.length ≤ eCap :=
    length_le_of_nodup_lt hLhnd fun e he => hKcap e ((hLhm e).mp he).1
  have hdeg : Lt.length + Lh.length = K.deg v' := tails_add_heads_eq_deg hLtnd hLhnd hLtm hLhm
  have hT2 : DynGraphAt mem2 tPtr vCap tCap T := by
    refine hT.of_agree fun a _ ha => ?_
    rw [hfr2 a (Or.inl (by omega)), hfr1 a (Or.inl (by omega))]
  have hLat : ListAt mem2 out (Lt ++ Lh) := by
    rw [listAt_append]
    exact ⟨hLtAt.congr fun k hk1 hk2 => hfr2 k (Or.inl hk2), hLhAt⟩
  -- split `T` with the two lists as the moved ends
  refine runs_seq_call_le (hL.applySplit vCap tCap T St Sh Lt Lh)
    (vs := [tPtr, 2, v, v', Lt.length, Lh.length, out]) (by eval_expr) (by wram_words)
    ⟨tPtr, 2, v, v', Lt.length, Lh.length, out, rfl, hw16, by omega, by omega, hvT, hv'T, hv'c,
      hT2, rfl, rfl, hLat, fun x hx => ?_, fun i _ => Or.inr (by omega),
      Or.inl ⟨rfl, fun e he => ?_, fun e he => ?_⟩⟩ ?_
  · rcases List.mem_append.mp hx with hx | hx
    · have := hKcap x ((hLtm x).mp hx).1; omega
    · have := hKcap x ((hLhm x).mp hx).1; omega
  · rw [hLtm]; exact hcT e he
  · rw [hLhm]; exact hcH e he
  rintro r3 mem3 pos3 ⟨_, _, _, _, _, _, _, hEq3, _, hT3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq3
  obtain ⟨rfl, -, rfl, rfl, -, -, rfl⟩ := hEq3
  replace hfr3 : ∀ a, a < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ a → mem3 a = mem2 a := hfr3
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨tPtr, livePtr, v, v', out, rfl, rfl, hT3, fun a ha1 ha2 => ?_⟩ ?_
  · show mem3 a = mem a
    rw [hfr3 a ha1, hfr2 a (by omega), hfr1 a (by omega)]
  · simp only [splitMoveContract, collectContract, dgApplySplitContract, List.getD_cons_succ, List.getD_cons_zero,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, argsSize, Expr.size]
    omega

end MinCostFlow.SparseCore.Program.Read
