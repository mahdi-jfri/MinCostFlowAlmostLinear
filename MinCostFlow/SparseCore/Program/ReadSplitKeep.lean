module

public import MinCostFlow.SparseCore.Program.ReadLib

import WordRAM.Tactic

/-!
# A split of the tree that keeps the listed and the frozen ends

When the batch lists the kept ends of a split at `v` (tag `3`), the other way to split the tree
`T` is to keep the listed ends and the frozen ends at `v`: these are exactly the ends of `T` at `v`
that stay (`split_keep_cond`, `ReadTree.lean`), since a frozen edge is not an edge of `G` and so
never moves.

`splitKeepStmt` (`[tPtr, frzPtr, a, out]`) reads the encoded split at `a`
(`[3, v, v', kt, kh] ++ Lt ++ Lh`), writes at `out` the list `Lt`, then the frozen edges with tail
at `v` (`collectStmt`), then `Lh`, then the frozen edges with head at `v`, and applies the split
to `T` with tag `3` and these two longer lists. It costs at most
`700 · (|Lt| + |Lh|) + 800 · deg_frozen(v) + 700` (`splitKeep_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- `[tPtr, frzPtr, a, out]`: for the split encoded at `a` with its kept lists, write at `out` the
kept tails, the tails at `v` of the graph at `frzPtr`, the kept heads and the heads at `v` of the
graph at `frzPtr`, and split the graph at `tPtr` with tag `3` and these lists. -/
def splitKeepStmt (L : ReadLib) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 5 (.load (.bin .add (.reg 2) (.const 2))) ;;
  .assign 6 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 7 (.load (.bin .add (.reg 2) (.const 4))) ;;
  .call 8 L.copy [.bin .add (.reg 2) (.const 5), .reg 3, .reg 6] ;;
  .call 9 L.collect [.reg 1, .reg 4, .const 0, .bin .add (.reg 3) (.reg 6)] ;;
  .assign 10 (.bin .add (.bin .add (.reg 3) (.reg 6)) (.reg 9)) ;;
  .call 8 L.copy [.bin .add (.bin .add (.reg 2) (.const 5)) (.reg 6), .reg 10, .reg 7] ;;
  .call 11 L.collect [.reg 1, .reg 4, .const 1, .bin .add (.reg 10) (.reg 7)] ;;
  .call 8 (L.split + dgIdxApplySplit)
    [.reg 0, .const 3, .reg 4, .reg 5, .bin .add (.reg 6) (.reg 9),
      .bin .add (.reg 7) (.reg 11), .reg 3] ;;
  .ret (.const 0)

theorem splitKeepStmt_noRand (L : ReadLib) : (splitKeepStmt L).NoRand := by
  simp [splitKeepStmt, Stmt.NoRand]

/-- Contract of `splitKeepStmt` for the tree `T` and the frozen graph `Fz` (caps `vCap`, `tCap`),
the split at `v` with new vertex `v'` and moved sets `St`, `Sh`, whose encoding at `a` lists the
kept ends `Lt`, `Lh`. With the frozen ends at `v`, these are the ends of `T` that stay. The blocks
and the encoding lie below the scratch `[out, out + |Lt| + |Lh| + 2 tCap)`. -/
def splitKeepContract (w vCap tCap : ℕ) (T Fz : MGraph) (v v' : ℕ) (St Sh : Finset ℕ)
    (Lt Lh : List ℕ) : Contract where
  pre args mem := ∃ tPtr frzPtr a out, args = [tPtr, frzPtr, a, out] ∧
    16 ≤ 2 ^ w ∧ ListAt mem a ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) ∧
    tPtr + dynGraphSize vCap tCap ≤ out ∧ frzPtr + dynGraphSize vCap tCap ≤ out ∧
    a + 5 + Lt.length + Lh.length ≤ out ∧ out + Lt.length + Lh.length + 2 * tCap < 2 ^ w ∧
    (∀ x ∈ Lt ++ Lh, x < 2 ^ w) ∧ v ∈ T.V ∧ v' ∉ T.V ∧ v' < vCap ∧ v ∈ Fz.V ∧
    DynGraphAt mem tPtr vCap tCap T ∧ DynGraphAt mem frzPtr vCap tCap Fz ∧
    (∀ e ∈ T.E, (e ∈ Lt ∨ (e ∈ Fz.E ∧ Fz.tail e = v)) ↔ (T.tail e = v ∧ e ∉ St)) ∧
    (∀ e ∈ T.E, (e ∈ Lh ∨ (e ∈ Fz.E ∧ Fz.head e = v)) ↔ (T.head e = v ∧ e ∉ Sh))
  post args mem ret mem' := ∃ tPtr frzPtr a out, args = [tPtr, frzPtr, a, out] ∧ ret = 0 ∧
    DynGraphAt mem' tPtr vCap tCap (T.applyUpdate (.split v v' (St ∩ T.E) (Sh ∩ T.E))) ∧
    ∀ x, (x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x) →
      (x < out ∨ out + Lt.length + Lh.length + 2 * tCap ≤ x) → mem' x = mem x
  cost _ _ := 700 * (Lt.length + Lh.length) + 800 * Fz.deg v + 700

/-- `splitKeepStmt` meets `splitKeepContract`. -/
theorem splitKeep_meetsContract {w : ℕ} {p : Program} {L : ReadLib} {f vCap tCap : ℕ}
    {T Fz : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} {Lt Lh : List ℕ} (hL : L.Has p)
    (hp : p.procs[f]? = some (splitKeepStmt L)) :
    MeetsContract w p f (splitKeepContract w vCap tCap T Fz v v' St Sh Lt Lh) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨tPtr, frzPtr, a, out, rfl, hw16, hAt, hT1, hF1, ha1, hout, hLw,
    hvT, hv'T, hv'c, hvF, hT, hF, hcT, hcH⟩
  have htw : tPtr < 2 ^ w := hargs _ (by simp)
  have hfw : frzPtr < 2 ^ w := hargs _ (by simp)
  have haw : a < 2 ^ w := hargs _ (by simp)
  have hFcap : ∀ e ∈ Fz.E, e < tCap := hF.2.2.1
  have hvc : v < vCap := hF.2.1 v hvF
  rw [listAt_append, listAt_append] at hAt
  obtain ⟨⟨hHd, hLtAt0⟩, hLhAt0⟩ := hAt
  simp only [List.length_append, List.length_cons, List.length_nil] at hLtAt0 hLhAt0
  have hm1 : mem (a + 1) = v := hHd 1 (by simp)
  have hm2 : mem (a + 2) = v' := hHd 2 (by simp)
  have hm3 : mem (a + 3) = Lt.length := hHd 3 (by simp)
  have hm4 : mem (a + 4) = Lh.length := hHd 4 (by simp)
  have hDt : vCap < dynGraphSize vCap tCap := by simp only [dynGraphSize]; omega
  have hTw : tPtr + dynGraphSize vCap tCap < 2 ^ w := by omega
  have hFw : frzPtr + dynGraphSize vCap tCap < 2 ^ w := by omega
  have hvw : v < 2 ^ w := by omega
  have hv'w : v' < 2 ^ w := by omega
  have hLtAt : ListAt mem (a + 5) Lt := fun i hi => by
    have := hLtAt0 i hi
    rwa [show a + (0 + 1 + 1 + 1 + 1 + 1) + i = a + 5 + i by omega] at this
  have hLhAt : ListAt mem (a + 5 + Lt.length) Lh := fun i hi => by
    have := hLhAt0 i hi
    rwa [show a + (0 + 1 + 1 + 1 + 1 + 1 + Lt.length) + i = a + 5 + Lt.length + i by omega] at this
  apply runs_start_le
  refine runs_seq_assign_le (v := v) (by eval_expr) ?_
  refine runs_seq_assign_le (v := v') (by eval_expr) ?_
  refine runs_seq_assign_le (v := Lt.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := Lh.length) (by eval_expr) ?_
  -- copy the kept tails to `out`
  refine runs_seq_call_le (hL.copy) (vs := [a + 5, out, Lt.length]) (by eval_expr)
    (by wram_words) ⟨a + 5, out, Lt.length, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩
    ?_
  rintro r1 mem1 pos1 ⟨_, _, _, hEq1, -, hcp1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  obtain ⟨rfl, rfl, rfl⟩ := hEq1
  replace hcp1 : ∀ i < Lt.length, mem1 (out + i) = mem (a + 5 + i) := hcp1
  replace hfr1 : ∀ x, x < out ∨ out + Lt.length ≤ x → mem1 x = mem x := hfr1
  have hLt1 : ListAt mem1 out Lt := fun i hi => (hcp1 i hi).trans (hLtAt i hi)
  have hF1' : DynGraphAt mem1 frzPtr vCap tCap Fz := hF.of_agree fun x _ hx => hfr1 x (by omega)
  -- the frozen tails at `v`
  refine runs_seq_call_le (hL.collect vCap tCap Fz) (vs := [frzPtr, v, 0, out + Lt.length])
    (by eval_expr) (by wram_words) ⟨frzPtr, v, 0, out + Lt.length, rfl, hw16, hFw,
      by omega, hvF, by omega, hF1', fun i _ => Or.inr (by omega)⟩ ?_
  rintro r2 mem2 pos2 ⟨_, _, _, _, hEq2, Ft, hFtnd, hFtm, rfl, hFtAt, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq2
  replace hfr2 : ∀ x, x < out + Lt.length ∨ out + Lt.length + Ft.length ≤ x → mem2 x = mem1 x :=
    hfr2
  have hFtle : Ft.length ≤ tCap :=
    length_le_of_nodup_lt hFtnd fun e he => hFcap e ((hFtm e).mp he).1
  refine runs_seq_assign_le (v := out + Lt.length + Ft.length) (by eval_expr) ?_
  -- copy the kept heads
  have hLh2 : ListAt mem2 (a + 5 + Lt.length) Lh := by
    intro i hi
    rw [hfr2 _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]
    exact hLhAt i hi
  refine runs_seq_call_le (hL.copy) (vs := [a + 5 + Lt.length, out + Lt.length + Ft.length,
    Lh.length]) (by eval_expr) (by wram_words)
    ⟨a + 5 + Lt.length, out + Lt.length + Ft.length, Lh.length, rfl, by omega, by omega,
      by omega, Or.inr (by omega)⟩ ?_
  rintro r3 mem3 pos3 ⟨_, _, _, hEq3, -, hcp3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq3
  obtain ⟨rfl, rfl, rfl⟩ := hEq3
  replace hcp3 : ∀ i < Lh.length, mem3 (out + Lt.length + Ft.length + i) =
      mem2 (a + 5 + Lt.length + i) := hcp3
  replace hfr3 : ∀ x, x < out + Lt.length + Ft.length ∨
      out + Lt.length + Ft.length + Lh.length ≤ x → mem3 x = mem2 x := hfr3
  have hLh3 : ListAt mem3 (out + Lt.length + Ft.length) Lh := fun i hi =>
    (hcp3 i hi).trans (hLh2 i hi)
  have hF3 : DynGraphAt mem3 frzPtr vCap tCap Fz := by
    refine hF.of_agree fun x _ hx => ?_
    rw [hfr3 x (Or.inl (by omega)), hfr2 x (Or.inl (by omega)), hfr1 x (Or.inl (by omega))]
  -- the frozen heads at `v`
  refine runs_seq_call_le (hL.collect vCap tCap Fz)
    (vs := [frzPtr, v, 1, out + Lt.length + Ft.length + Lh.length]) (by eval_expr)
    (by wram_words) ⟨frzPtr, v, 1, out + Lt.length + Ft.length + Lh.length, rfl, hw16,
      hFw, by omega, hvF, by omega, hF3, fun i _ => Or.inr (by omega)⟩ ?_
  rintro r4 mem4 pos4 ⟨_, _, _, _, hEq4, Fh, hFhnd, hFhm, rfl, hFhAt, hfr4⟩
  simp only [List.cons.injEq, and_true] at hEq4
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq4
  replace hfr4 : ∀ x, x < out + Lt.length + Ft.length + Lh.length ∨
      out + Lt.length + Ft.length + Lh.length + Fh.length ≤ x → mem4 x = mem3 x := hfr4
  have hFhle : Fh.length ≤ tCap :=
    length_le_of_nodup_lt hFhnd fun e he => hFcap e ((hFhm e).mp he).1
  have hdeg : Ft.length + Fh.length = Fz.deg v := tails_add_heads_eq_deg hFtnd hFhnd hFtm hFhm
  have hLs : out + ((Lt ++ Ft).length + (Lh ++ Fh).length) < 2 ^ w := by
    simp only [List.length_append]; omega
  -- the lists for the split, and `T` unchanged so far
  have hList : ListAt mem4 out ((Lt ++ Ft) ++ (Lh ++ Fh)) := by
    rw [listAt_append, listAt_append, listAt_append]
    simp only [List.length_append]
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_, ?_⟩
    · rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by omega))]
      exact hLt1 i hi
    · rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inl (by omega))]
      exact hFtAt i hi
    · rw [← Nat.add_assoc out, hfr4 _ (Or.inl (by omega))]
      exact hLh3 i hi
    · rw [← Nat.add_assoc out]
      exact hFhAt
  have hT4 : DynGraphAt mem4 tPtr vCap tCap T := by
    refine hT.of_agree fun x _ hx => ?_
    rw [hfr4 x (Or.inl (by omega)), hfr3 x (Or.inl (by omega)), hfr2 x (Or.inl (by omega)),
      hfr1 x (Or.inl (by omega))]
  refine runs_seq_call_le (hL.applySplit vCap tCap T St Sh (Lt ++ Ft) (Lh ++ Fh))
    (vs := [tPtr, 3, v, v', Lt.length + Ft.length, Lh.length + Fh.length, out]) (by eval_expr)
    (by wram_words) ⟨tPtr, 3, v, v', Lt.length + Ft.length, Lh.length + Fh.length, out, rfl, hw16,
      hTw, by simpa only [List.length_append] using hLs, hvT, hv'T, hv'c, hT4,
      List.length_append, List.length_append, hList, fun x hx => ?_, fun i _ => Or.inr (by omega),
      Or.inr ⟨rfl, fun e he => ?_, fun e he => ?_⟩⟩ ?_
  · simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact hLw x (List.mem_append_left _ hx)
    · have := hFcap x ((hFtm x).mp hx).1; omega
    · exact hLw x (List.mem_append_right _ hx)
    · have := hFcap x ((hFhm x).mp hx).1; omega
  · rw [List.mem_append, hFtm]; simpa [endAt] using hcT e he
  · rw [List.mem_append, hFhm]; simpa [endAt] using hcH e he
  rintro r5 mem5 pos5 ⟨_, _, _, _, _, _, _, hEq5, _, hT5, hfr5⟩
  simp only [List.cons.injEq, and_true] at hEq5
  obtain ⟨rfl, -, rfl, rfl, -, -, rfl⟩ := hEq5
  replace hfr5 : ∀ x, x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x → mem5 x = mem4 x := hfr5
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨tPtr, frzPtr, a, out, rfl, rfl, hT5, fun x hx1 hx2 => ?_⟩ ?_
  · show mem5 x = mem x
    rw [hfr5 x hx1, hfr4 x (by omega), hfr3 x (by omega), hfr2 x (by omega), hfr1 x (by omega)]
  · simp only [splitKeepContract, collectContract, copyWordsContract, dgApplySplitContract,
      List.getD_cons_succ, List.getD_cons_zero, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, argsSize, Expr.size]
    omega

end MinCostFlow.SparseCore.Program.Read
