module

public import MinCostFlow.HierPaths.InitProgBucketGather

/-!
# Building a compressed section from keyed words

The counting sort provides the row offsets and the stable order of records.
A second scan copies their payloads immediately after the offset table.
The counts and record indices remain in a separate scratch interval.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.LowStretch

/-- Arguments are the key table, payload table, record count, key count and output address. -/
def initBucket (sort gather : ℕ) : Stmt :=
  .assign 5 (.bin .add (.bin .add (.reg 4) (.reg 3)) (.const 1)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 2)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
  .call 8 sort [.reg 0, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7] ;;
  .call 8 gather [.reg 7, .reg 1, .reg 2, .reg 5] ;;
  .ret (.reg 8)

theorem initBucket_noRand (sort gather : ℕ) : (initBucket sort gather).NoRand := by
  simp [initBucket, Stmt.NoRand]

/-- The exact sorted rows are written. Space beyond the result holds the running counts and
record order, and the enclosing caller can clear it in linear time. -/
def initBucketContract (w k : ℕ) (rs : List (ℕ × ℕ)) : Contract where
  pre args mem := ∃ keys vals dst, args = [keys, vals, rs.length, k, dst] ∧
    ListAt mem keys (rs.map Prod.fst) ∧ ListAt mem vals (rs.map Prod.snd) ∧
    keys + rs.length ≤ dst ∧ vals + rs.length ≤ dst ∧
    (∀ i < rs.length, initBucketKey rs i < k) ∧
    dst + (k + 1) + rs.length + k + rs.length + k + 2 < 2 ^ w
  post args mem r mem' := ∃ keys vals dst, args = [keys, vals, rs.length, k, dst] ∧
    r = dst + (k + 1) + rs.length ∧ ListAt mem' dst (csrList k (buckets rs)) ∧
    ∀ y, y < dst ∨ r + k + rs.length ≤ y → mem' y = mem y
  cost _ _ := 160 * (rs.length + k + 1)

private theorem initBucketValue_eq (rs : List (ℕ × ℕ)) {i : ℕ} (hi : i < rs.length) :
    (rs.map Prod.snd).getD i 0 = initBucketValue rs i := by
  rw [initBucketValue, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _
    (by simpa only [List.length_map] using hi), List.getElem_map]

theorem initBucket_meetsContract {w f sort gather k : ℕ} {rs : List (ℕ × ℕ)} {p : Program}
    (hp : p.procs[f]? = some (initBucket sort gather))
    (hsort : p.HasAt sort [csrB]) (hGather : p.procs[gather]? = some initBucketGather) :
    MeetsContract w p f (initBucketContract w k rs) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨keys, vals, dst, rfl, hkey, hval, hksep, hvsep, hk, hroom⟩ := hpre
  let n := rs.length
  let a := dst + (k + 1)
  let c := a + n
  let o := c + k
  let ord := initBucketOrder rs k
  let key := fun i => mem (keys + i)
  have h1 : 1 < 2 ^ w := by omega
  have hkeys (i : ℕ) (hi : i < n) : key i = initBucketKey rs i := by
    change mem (keys + i) = (rs.getD i (0, 0)).1
    rw [List.getD_eq_getElem _ _ hi]
    have h := hkey i (by simpa using hi)
    rw [List.getElem_map] at h
    exact h
  have hord : ord.length = n := initBucketOrder_length rs k hk
  have ha : a < 2 ^ w := by dsimp [a]; omega
  have hc : c < 2 ^ w := by dsimp [c, a, n]; omega
  have ho : o < 2 ^ w := by dsimp [o, c, a, n]; omega
  refine runs_start_le ?_
  unfold initBucket
  refine runs_seq_assign_le (v := a) (Expr.eval_eq_of_eq (Expr.eval_add
    (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_reg_of_eq (v := k) rfl)
      (by dsimp [a] at ha; omega))
    (Expr.eval_const h1) (by dsimp [a] at ha; omega)) (by dsimp [a]; omega)) ?_
  refine runs_seq_assign_le (v := c)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hc) ?_
  refine runs_seq_assign_le (v := o)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) ho) ?_
  refine runs_seq_call_le (csrB_spec (w := w) hsort)
    (vs := [keys, n, k, dst, c, o]) rfl ?_
    ⟨keys, n, k, dst, c, o, rfl, fun i hi => by change key i < k; rw [hkeys i hi]; exact hk i hi, hksep,
      by dsimp [c, a]; omega, le_rfl, hroom⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact hw _ (by simp [n])
  intro z mem₁ pos₁ hp₁
  obtain ⟨hof, hindices, hf⟩ := hp₁
  have hgrp (u : ℕ) : grp key n u = grp (initBucketKey rs) n u :=
    List.filter_congr (fun i hi => by rw [hkeys i (List.mem_range.mp hi)])
  have hoff (u : ℕ) : offOf key n u = offOf (initBucketKey rs) n u := by
    unfold offOf
    congr 1
    exact List.filter_congr (fun i hi => by rw [hkeys i (List.mem_range.mp hi)])
  have hOff : ListAt mem₁ dst (csrOffsets k (buckets rs)) := by
    intro i hi
    have hi' : i ≤ k := by simpa [csrOffsets] using hi
    have hiMem := hof i hi'
    change mem₁ (dst + i) = offOf key n i at hiMem
    rw [hiMem, hoff, initBucket_offset]
    simp [csrOffsets, initCSRPrefix]
  have hOrd : ListAt mem₁ o ord := by
    apply initBucket_listAt_from_rows
    intro u hu i hi
    rw [initBucket_prefix_group, ← hoff]
    have hi' : i < (grp key n u).length := hgrp u ▸ hi
    have hm := hindices u hu i hi'
    change mem₁ (o + offOf key n u + i) = (grp key n u).getD i 0 at hm
    rwa [hgrp, List.getD_eq_getElem _ _ hi] at hm
  have hFrame (y : ℕ) (hy : y < dst ∨ o + n ≤ y) : mem₁ y = mem y := by
    apply hf y
    change ¬ csrOut dst c o k n y
    unfold csrOut
    dsimp [o, c, a] at hy ⊢
    omega
  have hVal : ListAt mem₁ vals (rs.map Prod.snd) :=
    listAt_congr (fun i hi => (hFrame _ (.inl (by simpa using (show vals + i < dst by
      have hi' : i < n := by simpa using hi
      omega)))).symm) hval
  refine runs_seq_call_le (initBucketGather_meetsContract (w := w) (ord := ord)
    (vals := rs.map Prod.snd) hGather) (vs := [o, vals, ord.length, a]) ?_ ?_ ?_ ?_
  · rw [hord]
    rfl
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ho
    · exact hw _ (by simp)
    · rw [hord]; exact hw _ (by simp [n])
    · exact ha
  · refine ⟨o, vals, a, rfl, hOrd, hVal, ?_, ?_, ?_, ?_, ?_, ?_, h1⟩
    · intro i hi
      simpa using initBucketOrder_lt rs k hi
    · exact .inr (by rw [hord]; exact Nat.le_add_right _ _)
    · exact .inl (by simpa using (hvsep.trans (Nat.le_add_right dst (k + 1))))
    · rw [hord]; dsimp [o, c, a, n]; omega
    · simp only [List.length_map]; dsimp [n] at *; omega
    · rw [hord]; exact hc
  intro r mem₂ pos₂ hp₂
  obtain ⟨o', vals', a', ha', hr, hdata, hfr⟩ := hp₂
  simp only [List.cons.injEq, and_true] at ha'
  obtain ⟨_, _, _, hda⟩ := ha'
  subst a'
  rw [hord] at hr
  have hCsr : ListAt mem₂ dst (csrList k (buckets rs)) := by
    rw [csrList, listAt_append]
    have hlen : (csrOffsets k (buckets rs)).length = k + 1 := by simp [csrOffsets]
    rw [hlen]
    refine ⟨listAt_congr (fun i hi => (hfr _ (.inl (by rw [hlen] at hi; dsimp [a]; omega))).symm)
      hOff, ?_⟩
    have he : ord.map (fun i => (rs.map Prod.snd).getD i 0) = csrData k (buckets rs) := by
      rw [← initBucketOrder_values]
      apply List.map_congr_left
      intro i hi
      exact initBucketValue_eq rs (initBucketOrder_lt rs k hi)
    rw [← he]
    exact hdata
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨keys, vals, dst, rfl, hr, hCsr, ?_⟩ ?_
  · intro y hy
    change y < dst ∨ r + k + n ≤ y at hy
    dsimp [o, c] at hFrame
    exact (hfr _ (by dsimp [a] at *; omega)).trans (hFrame _ (by rw [hr] at hy; exact hy))
  · simp [initBucketGatherContract, initBucketContract, csrC, argsSize, Expr.size, hord, n]
    omega

end MinCostFlow.HierPaths

end
