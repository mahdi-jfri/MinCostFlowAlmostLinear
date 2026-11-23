module

public import MinCostFlow.SparseCore.Program.ReadSplitMove
public import MinCostFlow.SparseCore.Program.ReadSplitKeep
public import MinCostFlow.SparseCore.Program.ReadTree

import WordRAM.Tactic

/-!
# The split of the tree for one split of the batch

A vertex split `.split v v' St Sh` of `G` splits the tree `T` of the LSF view too
(`tViewUpdate`). The batch lists the ends at `v` that move (tag `2`) or that stay (tag `3`), as
edges of `G`.

* With tag `2`, the same lists are the moved ends of `T` (`split_tag2_cond`), so the split of the
  library applies directly.
* With tag `3`, every end of `T` at `v` that is not listed would move, also a frozen one, which
  must stay. `splitTStmt` compares the live degree `M` of `v'` after the split with the frozen
  degree `F` of `v`, and runs the cheaper of the two ways: list the `M` live ends at `v'` as moved
  ends (`splitMoveStmt`), or list the kept ends and the `F` frozen ends at `v` as kept ends
  (`splitKeepStmt`).

So the cost is at most `1000 · len + 800 · min(M, F) + 1000` for an encoding of `len` words
(`splitT_meetsContract`). The potential of the tree pays the term `min(M, F)`
(`split_amortized`, `ReadTree.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The ends of `T` that move and that stay, without lists -/

/-- The tails at `v'` of the live part after the split are the tails of `T` that move. -/
theorem move_cond_tail {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (h : TreeAgree G T)
    (hu : G.UpdateIsValid (.split v v' St Sh)) (e : ℕ) (he : e ∈ T.E) :
    let K := liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))
    (e ∈ K.E ∧ K.tail e = v') ↔ (T.tail e = v ∧ e ∈ St) := by
  intro K
  have hL := split_move_cond h hu (L := (K.E.filter fun e => K.tail e = v').toList)
    (fun e => by simp [K])
  rw [← hL e he]
  simp [K]

/-- The heads at `v'` of the live part after the split are the heads of `T` that move. -/
theorem move_cond_head {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (h : TreeAgree G T)
    (hu : G.UpdateIsValid (.split v v' St Sh)) (e : ℕ) (he : e ∈ T.E) :
    let K := liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))
    (e ∈ K.E ∧ K.head e = v') ↔ (T.head e = v ∧ e ∈ Sh) := by
  intro K
  have hL := split_move_cond_head h hu (L := (K.E.filter fun e => K.head e = v').toList)
    (fun e => by simp [K])
  rw [← hL e he]
  simp [K]

/-- The kept tails of `G` at `v` and the frozen tails at `v` are the tails of `T` that stay. -/
theorem keep_cond_tail {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (h : TreeAgree G T)
    (hu : G.UpdateIsValid (.split v v' St Sh)) {Lt : List ℕ}
    (hL : ∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∉ St) (e : ℕ) (he : e ∈ T.E) :
    (e ∈ Lt ∨ (e ∈ (frozenT G T).E ∧ (frozenT G T).tail e = v)) ↔ (T.tail e = v ∧ e ∉ St) := by
  have hK := split_keep_cond h hu hL
    (Ft := ((frozenT G T).E.filter fun e => (frozenT G T).tail e = v).toList)
    (fun e => by simp)
  rw [← hK e he, List.mem_append]
  simp

/-- The kept heads of `G` at `v` and the frozen heads at `v` are the heads of `T` that stay. -/
theorem keep_cond_head {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (h : TreeAgree G T)
    (hu : G.UpdateIsValid (.split v v' St Sh)) {Lh : List ℕ}
    (hL : ∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh) (e : ℕ) (he : e ∈ T.E) :
    (e ∈ Lh ∨ (e ∈ (frozenT G T).E ∧ (frozenT G T).head e = v)) ↔ (T.head e = v ∧ e ∉ Sh) := by
  have hK := split_keep_cond_head h hu hL
    (Fh := ((frozenT G T).E.filter fun e => (frozenT G T).head e = v).toList)
    (fun e => by simp)
  rw [← hK e he, List.mem_append]
  simp

/-! ## The procedure -/

/-- `[tPtr, livePtr, frzPtr, a, out]`: split the tree at `tPtr` for the split encoded at `a`, with
the live part (already split) at `livePtr`, the frozen part at `frzPtr`, and scratch at `out`.
The procedures `splitMoveStmt` and `splitKeepStmt` are at `fMove` and `fKeep`. -/
def splitTStmt (L : ReadLib) (fMove fKeep : ℕ) : Stmt :=
  .assign 5 (.load (.reg 3)) ;;
  .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .assign 7 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .cond (.bin .eq (.reg 5) (.const 2))
    (.call 8 (L.split + dgIdxApplySplit)
      [.reg 0, .const 2, .reg 6, .reg 7, .load (.bin .add (.reg 3) (.const 3)),
        .load (.bin .add (.reg 3) (.const 4)), .bin .add (.reg 3) (.const 5)])
    (.call 8 (L.ops + dgIdxGetDeg) [.reg 1, .reg 7] ;;
     .call 9 (L.ops + dgIdxGetDeg) [.reg 2, .reg 6] ;;
     .cond (.bin .lt (.reg 9) (.reg 8))
       (.call 10 fKeep [.reg 0, .reg 2, .reg 3, .reg 4])
       (.call 10 fMove [.reg 0, .reg 1, .reg 6, .reg 7, .reg 4])) ;;
  .ret (.const 0)

theorem splitTStmt_noRand (L : ReadLib) (fMove fKeep : ℕ) : (splitTStmt L fMove fKeep).NoRand := by
  simp [splitTStmt, Stmt.NoRand]

/-- Contract of `splitTStmt` for the split `.split v v' St Sh` of `G`, encoded in `len` words, and
the tree `T`. The live part is already split; the frozen part is not. The blocks and the encoding
lie below the scratch `[out, out + len + 2 tCap)`. -/
def splitTContract (w vCap eCap tCap : ℕ) (G T : MGraph) (v v' : ℕ) (St Sh : Finset ℕ)
    (len : ℕ) : Contract where
  pre args mem := ∃ tPtr livePtr frzPtr a out, args = [tPtr, livePtr, frzPtr, a, out] ∧
    16 ≤ 2 ^ w ∧ UpdateAt mem a G (.split v v' St Sh) len ∧ (∀ i < len, mem (a + i) < 2 ^ w) ∧
    (∀ i < len, a + i < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ a + i) ∧ TreeAgree G T ∧ G.UpdateIsValid (.split v v' St Sh) ∧ v' < vCap ∧ eCap ≤ tCap ∧
    tPtr + dynGraphSize vCap tCap ≤ out ∧ livePtr + dynGraphSize vCap eCap ≤ out ∧
    frzPtr + dynGraphSize vCap tCap ≤ out ∧ a + len ≤ out ∧ out + len + 2 * tCap < 2 ^ w ∧
    DynGraphAt mem tPtr vCap tCap T ∧
    DynGraphAt mem livePtr vCap eCap
      (liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))) ∧
    DynGraphAt mem frzPtr vCap tCap (frozenT G T)
  post args mem ret mem' := ∃ tPtr livePtr frzPtr a out, args = [tPtr, livePtr, frzPtr, a, out] ∧
    ret = 0 ∧ DynGraphAt mem' tPtr vCap tCap (tViewUpdate T (.split v v' St Sh)) ∧
    ∀ x, (x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x) → (x < out ∨ out + len + 2 * tCap ≤ x) →
      mem' x = mem x
  cost _ _ := 1000 * len + 800 * min
    ((liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))).deg v')
    ((frozenT G T).deg v) + 1000

/-- The entries of a list in memory are words when the cells are. -/
theorem listAt_words {mem : ℕ → ℕ} {a w : ℕ} {l : List ℕ} (hl : ListAt mem a l)
    (hw : ∀ i < l.length, mem (a + i) < 2 ^ w) : ∀ x ∈ l, x < 2 ^ w := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [← hl i hi]
  exact hw i hi

/-- `splitTStmt` meets `splitTContract`. -/
theorem splitT_meetsContract {w : ℕ} {p : Program} {L : ReadLib} {f fMove fKeep vCap eCap tCap : ℕ}
    {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} {len : ℕ} (hL : L.Has p)
    (hp : p.procs[f]? = some (splitTStmt L fMove fKeep))
    (hpMove : p.procs[fMove]? = some (splitMoveStmt L))
    (hpKeep : p.procs[fKeep]? = some (splitKeepStmt L)) :
    MeetsContract w p f (splitTContract w vCap eCap tCap G T v v' St Sh len) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨tPtr, livePtr, frzPtr, a, out, rfl, hw16, hU, hUw, hUdisj, hag,
    hu, hv'c, heT, hT1, hl1, hF1, ha1, hout, hT, hK, hF⟩
  set K := liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh)) with hKdef
  have htw : tPtr < 2 ^ w := hargs _ (by simp)
  have hlw : livePtr < 2 ^ w := hargs _ (by simp)
  have hfw : frzPtr < 2 ^ w := hargs _ (by simp)
  have haw : a < 2 ^ w := hargs _ (by simp)
  have hDt : vCap < dynGraphSize vCap tCap := by simp only [dynGraphSize]; omega
  have hTw : tPtr + dynGraphSize vCap tCap < 2 ^ w := by omega
  have hv'w : v' < 2 ^ w := by omega
  have hu' := hu
  obtain ⟨hvG, hv'G, hS, _⟩ := hu'
  have hvT : v ∈ T.V := hag.2.2.1 ▸ hvG
  have hv'T : v' ∉ T.V := hag.2.2.1 ▸ hv'G
  have hvw : v < 2 ^ w := by have := hF.2.1 v hvG; omega
  have hsame := tree_split_same T v v' St Sh
  rcases hU with ⟨Lt, Lh, hLtnd, hLhnd, hLtm, hLhm, rfl, hAt⟩ |
    ⟨Lt, Lh, hLtnd, hLhnd, hLtm, hLhm, rfl, hAt⟩
  · -- tag `2`: the lists of the batch are the moved ends of `T`
    have hHd := (listAt_append.mp (listAt_append.mp hAt).1).1
    have hm0 : mem a = 2 := hHd 0 (by simp)
    have hm1 : mem (a + 1) = v := hHd 1 (by simp)
    have hm2 : mem (a + 2) = v' := hHd 2 (by simp)
    have hm3 : mem (a + 3) = Lt.length := hHd 3 (by simp)
    have hm4 : mem (a + 4) = Lh.length := hHd 4 (by simp)
    have hLat : ListAt mem (a + 5) (Lt ++ Lh) := by
      have h' : ListAt mem a ([2, v, v', Lt.length, Lh.length] ++ (Lt ++ Lh)) := by
        rwa [← List.append_assoc]
      exact (listAt_append.mp h').2
    have hLw : ∀ x ∈ Lt ++ Lh, x < 2 ^ w :=
      listAt_words hLat fun i hi => by simp only [List.length_append] at hi; exact hUw (5 + i) (by omega) |>.trans_eq' (by rw [Nat.add_assoc])
    apply runs_start_le
    refine runs_seq_assign_le (v := 2) (by eval_expr) ?_
    refine runs_seq_assign_le (v := v) (by eval_expr) ?_
    refine runs_seq_assign_le (v := v') (by eval_expr) ?_
    refine runs_seq_cond_le (by eval_expr) (fun _ => ?_) (fun h => by simp at h)
    refine runs_seq_call_le (hL.applySplit vCap tCap T St Sh Lt Lh)
      (vs := [tPtr, 2, v, v', Lt.length, Lh.length, a + 5]) (by eval_expr) (by wram_words)
      ⟨tPtr, 2, v, v', Lt.length, Lh.length, a + 5, rfl, hw16, hTw, by omega, hvT,
        hv'T, hv'c, hT, rfl, rfl, hLat, hLw, fun i hi => by have := hUdisj (5 + i) (by omega); omega,
        Or.inl ⟨rfl, split_tag2_cond hag hu hLtm, split_tag2_cond_head hag hu hLhm⟩⟩ ?_
    rintro r1 mem1 pos1 ⟨_, _, _, _, _, _, _, hEq1, _, hT1', hfr1⟩
    simp only [List.cons.injEq, and_true] at hEq1
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hEq1
    replace hfr1 : ∀ x, x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x → mem1 x = mem x := hfr1
    refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, livePtr, frzPtr, a, out, rfl, rfl,
      DynGraphAt.of_same hT1' hsame, fun x hx _ => hfr1 x hx⟩ ?_
    simp only [splitTContract, dgApplySplitContract, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, argsSize, Expr.size]
    omega
  · -- tag `3`: keep the listed and the frozen ends, or move the live ends at `v'`
    have hHd := (listAt_append.mp (listAt_append.mp hAt).1).1
    have hm0 : mem a = 3 := hHd 0 (by simp)
    have hm1 : mem (a + 1) = v := hHd 1 (by simp)
    have hm2 : mem (a + 2) = v' := hHd 2 (by simp)
    have hLat : ListAt mem (a + 5) (Lt ++ Lh) := by
      have h' : ListAt mem a ([3, v, v', Lt.length, Lh.length] ++ (Lt ++ Lh)) := by
        rwa [← List.append_assoc]
      exact (listAt_append.mp h').2
    have hLw : ∀ x ∈ Lt ++ Lh, x < 2 ^ w :=
      listAt_words hLat fun i hi => by simp only [List.length_append] at hi; exact hUw (5 + i) (by omega) |>.trans_eq' (by rw [Nat.add_assoc])
    have hv'K : v' ∈ K.V := by simp [K, liveT, MGraph.applyUpdate]
    have hvF : v ∈ (frozenT G T).V := hvG
    apply runs_start_le
    refine runs_seq_assign_le (v := 3) (by eval_expr) ?_
    refine runs_seq_assign_le (v := v) (by eval_expr) ?_
    refine runs_seq_assign_le (v := v') (by eval_expr) ?_
    refine runs_seq_cond_le (by eval_expr) (fun h => by simp at h) (fun _ => ?_)
    refine runs_seq_assoc_le ?_
    refine runs_seq_call_le (hL.getDeg vCap eCap K) (vs := [livePtr, v']) (by eval_expr)
      (by wram_words) ⟨livePtr, v', rfl, hw16, by omega, hv'K, hK⟩ ?_
    rintro M mem1 pos1 ⟨_, _, hEq1, hmem1, rfl⟩
    subst mem1
    simp only [List.cons.injEq, and_true] at hEq1
    obtain ⟨rfl, rfl⟩ := hEq1
    refine runs_seq_assoc_le ?_
    refine runs_seq_call_le (hL.getDeg vCap tCap (frozenT G T)) (vs := [frzPtr, v])
      (by eval_expr) (by wram_words) ⟨frzPtr, v, rfl, hw16, by omega, hvF, hF⟩ ?_
    rintro Fd mem2 pos2 ⟨_, _, hEq2, hmem2, rfl⟩
    subst mem2
    simp only [List.cons.injEq, and_true] at hEq2
    obtain ⟨rfl, rfl⟩ := hEq2
    refine runs_seq_cond_le (by eval_expr) (fun hlt => ?_) (fun hge => ?_)
    · -- keep: the frozen degree is the smaller
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hlt
      refine runs_seq_call_le (splitKeep_meetsContract (vCap := vCap) (tCap := tCap) (T := T)
        (Fz := frozenT G T) (v := v) (v' := v') (St := St) (Sh := Sh) (Lt := Lt) (Lh := Lh) hL
        hpKeep) (vs := [tPtr, frzPtr, a, out]) (by eval_expr) (by wram_words)
        ⟨tPtr, frzPtr, a, out, rfl, hw16, hAt, hT1, hF1, by omega, by omega, hLw, hvT, hv'T, hv'c,
          hvF, hT, hF, keep_cond_tail hag hu hLtm, keep_cond_head hag hu hLhm⟩ ?_
      rintro r3 mem3 pos3 ⟨_, _, _, _, hEq3, _, hT3, hfr3⟩
      simp only [List.cons.injEq, and_true] at hEq3
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq3
      replace hfr3 : ∀ x, (x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x) →
          (x < out ∨ out + Lt.length + Lh.length + 2 * tCap ≤ x) → mem3 x = mem x := hfr3
      refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, livePtr, frzPtr, a, out, rfl, rfl,
        DynGraphAt.of_same hT3 hsame, fun x hx1 hx2 => hfr3 x hx1 (by omega)⟩ ?_
      have hmin : min (K.deg v') ((frozenT G T).deg v) = (frozenT G T).deg v := by omega
      simp only [splitTContract, splitKeepContract, dgGetDegContract, ← hKdef, hmin, argsSize,
        Expr.size]
      omega
    · -- move: the live degree at `v'` is the smaller
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at hge
      refine runs_seq_call_le (splitMove_meetsContract (vCap := vCap) (eCap := eCap)
        (tCap := tCap) (T := T) (K := K) (St := St) (Sh := Sh) hL hpMove)
        (vs := [tPtr, livePtr, v, v', out]) (by eval_expr) (by wram_words)
        ⟨tPtr, livePtr, v, v', out, rfl, hw16, hT1, hl1, by omega, hvT, hv'T, hv'c, hv'K, hT, hK,
          move_cond_tail hag hu, move_cond_head hag hu⟩ ?_
      rintro r3 mem3 pos3 ⟨_, _, _, _, _, hEq3, _, hT3, hfr3⟩
      simp only [List.cons.injEq, and_true] at hEq3
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq3
      replace hfr3 : ∀ x, (x < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ x) →
          (x < out ∨ out + 2 * eCap ≤ x) → mem3 x = mem x := hfr3
      refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, livePtr, frzPtr, a, out, rfl, rfl,
        DynGraphAt.of_same hT3 hsame, fun x hx1 hx2 => hfr3 x hx1 (by omega)⟩ ?_
      have hmin : min (K.deg v') ((frozenT G T).deg v) = K.deg v' := by omega
      simp only [splitTContract, splitMoveContract, dgGetDegContract, ← hKdef, hmin, argsSize,
        Expr.size, List.getD_cons_succ, List.getD_cons_zero]
      omega

end MinCostFlow.SparseCore.Program.Read
