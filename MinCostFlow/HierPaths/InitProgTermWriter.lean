module

public import MinCostFlow.HierPaths.InitProgTermColumns

/-!
# Section 7 of the initialized hierarchy

Read both endpoint columns from the static hierarchy, interleave them in
connector order, and put their connector numbers in compressed terminal lists.
All four temporary columns are cleared by the last call.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.LowStretch

def initTermWriter (first second columns finish : ℕ) : Stmt :=
  .call 7 first secArgs ;;
  .call 8 second [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 7] ;;
  .assign 9 (.bin .sub (.reg 7) (.reg 6)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 9)) ;;
  .assign 11 (.bin .add (.reg 8) (.reg 10)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 10)) ;;
  .assign 13 (.bin .shiftLeft (.const 1) (.load (.bin .add (.reg 4) (.const 7)))) ;;
  .call 14 columns [.reg 6, .reg 7, .reg 9, .reg 8, .reg 11] ;;
  .call 15 finish [.reg 8, .reg 11, .reg 10, .reg 13, .reg 12, .reg 6] ;;
  .ret (.reg 15)

theorem initTermWriter_noRand (first second columns finish : ℕ) :
    (initTermWriter first second columns finish).NoRand := by simp [initTermWriter, Stmt.NoRand]

def initTermWriterScratch (S : StaticData) : ℕ := 8 * S.numConn + 2 * S.numTerm + 2

def initTermWriterCost (S : StaticData) : ℕ :=
  2 * initEndpointSectionCost S + 900 * (S.numConn + S.numTerm + 1)

private theorem initEndpointColumns_length (S : StaticData) (i : ℕ) (hi : i < 2) :
    (initEndpointWords S i).length = S.numConn := by
  rw [initEndpointWords_eq_map S i hi, List.length_map]
  rfl

theorem initTermWriter_meetsContract {w a f first second columns finish : ℕ}
    {S : StaticData} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (initTermWriter first second columns finish))
    (hA : MeetsContract w p first (SecContract w (buildInv w S a G)
      ⟨first, fun _ => initEndpointWords S 0, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hB : MeetsContract w p second (SecContract w (buildInv w S a G)
      ⟨second, fun _ => initEndpointWords S 1, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hCols : MeetsContract w p columns (initTermColumnsContract w))
    (hFin : MeetsContract w p finish (initBucketMoveContract w S.numTerm (initTermRecords S))) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initTermSection S, fun _ => initTermWriterCost S, fun _ => initTermWriterScratch S⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hroom⟩ := hpre
  obtain ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩ := hInv
  have hInv := (show buildInv w S a G base mem from
    ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩)
  subst base
  let base := [ga, pn, pd, M, h, h₁]
  let n := S.numConn
  let N := 2 * n
  let P := S.numTerm
  let B := dst + n
  let K := B + n
  let V := K + N
  let tmp := V + N
  have hnR : (initTermRecords S).length = N := initTermRecords_length S
  have hlen : (initTermSection S).length = P + 1 + N :=
    initTermSection_length hgood.b_pos hgood.valid
  have room : tmp + (P + 1) + N + P + N + P + 2 < 2 ^ w := by
    change dst + (initTermSection S).length + initTermWriterScratch S < 2 ^ w at hroom
    rw [hlen] at hroom
    dsimp [tmp, V, K, B, N, n, P, initTermWriterScratch] at *
    omega
  have ht : tmp < 2 ^ w := by omega
  have hV : V < 2 ^ w := by dsimp only [tmp] at room; omega
  have hK : K < 2 ^ w := by dsimp only [tmp, V] at room; omega
  have hBword : B < 2 ^ w := by dsimp only [tmp, V, K] at room; omega
  have hN : N < 2 ^ w := by omega
  have hn : n < 2 ^ w := by dsimp only [N] at hN; omega
  have hP : P < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  change h₁ + 25 ≤ dst at hdst
  have hlenA : (initEndpointWords S 0).length = n := initEndpointColumns_length S 0 (by decide)
  have hlenB : (initEndpointWords S 1).length = n := initEndpointColumns_length S 1 (by decide)
  refine runs_start_le ?_
  unfold initTermWriter
  refine runs_seq_call_le hA (vs := base ++ [dst]) rfl hw
    ⟨base, dst, rfl, hbl, hInv, hzero, hdst, by simpa only [hlenA, Nat.add_zero] using hBword⟩ ?_
  intro r mem₁ pos₁ hp₁
  obtain ⟨base', dst', ha, hr, hwordsA, hz₁, hf₁⟩ := hp₁
  have hd : dst' = dst := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst dst'
  change r = dst + (initEndpointWords S 0).length at hr
  rw [hlenA] at hr
  change r = B at hr
  subst r
  have hInv₁ := buildInv_stable w S a G base mem mem₁ hInv (fun y hy =>
    hf₁ y (by change h₁ + 25 ≤ dst at hdst; change y < h₁ at hy; omega))
  refine runs_seq_call_le hB (vs := base ++ [B]) rfl ?_
    ⟨base, B, rfl, hbl, hInv₁, hz₁, by change h₁ + 25 ≤ B; exact hdst.trans (Nat.le_add_right _ _),
      by simpa only [hlenB, Nat.add_zero] using hK⟩ ?_
  · intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hw v (List.mem_append_left _ hv)
    · exact hBword
  intro r mem₂ pos₂ hp₂
  obtain ⟨base', B', ha, hr, hwordsB, hz₂, hf₂⟩ := hp₂
  have he : B' = B := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst B'
  change r = B + (initEndpointWords S 1).length at hr
  rw [hlenB] at hr
  change r = K at hr
  subst r
  have hAw : ListAt mem₂ dst (initEndpointWords S 0) :=
    listAt_congr (fun i hi => (hf₂ _ (by rw [hlenA] at hi; dsimp [B]; omega)).symm) hwordsA
  have hsub : B - dst = n := Nat.add_sub_cancel_left _ _
  refine runs_seq_assign_le (v := n) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := B) rfl) (Expr.eval_reg_of_eq (v := dst) rfl)
      hBword) hsub) ?_
  refine runs_seq_assign_le (v := N) (Expr.eval_eq_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := n) rfl) (Expr.eval_reg_of_eq (v := n) rfl)
      (by dsimp [N] at hN; omega)) (by dsimp [N]; omega)) ?_
  refine runs_seq_assign_le (v := V) (Expr.eval_add
    (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hV) ?_
  refine runs_seq_assign_le (v := tmp) (Expr.eval_add
    (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) ht) ?_
  have hh7 : h + 7 < 2 ^ w := by
    obtain ⟨_, _, hl⟩ := staticOut_owner_facts hS
    change h₁ + 25 ≤ dst at hdst
    have hdstw : dst < 2 ^ w := hw _ (by simp)
    omega
  have hx : mem₂ (h + 7) = S.x := by
    obtain ⟨hx, _, hl⟩ := staticOut_owner_facts hS
    change h₁ + 25 ≤ dst at hdst
    exact (hf₂ _ (by dsimp [B]; omega)).trans ((hf₁ _ (by omega)).trans hx)
  refine runs_seq_assign_le (v := P) ?_ ?_
  · have he : (1 : ℕ) <<< S.x = P := by simp [Nat.shiftLeft_eq, P, StaticData.numTerm]
    exact Expr.eval_eq_of_eq (Expr.eval_shiftLeft (Expr.eval_const h1)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
        (Expr.eval_const (by omega)) hh7) hx) (he ▸ hP)) he
  refine runs_seq_call_le hCols (vs := [dst, B, n, K, V]) rfl ?_
    ⟨dst, B, n, K, V, rfl, Nat.le_add_right _ _, le_rfl, le_rfl, ht, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hBword
    · exact hn
    · exact hK
    · exact hV
  intro r mem₃ pos₃ hp₃
  obtain ⟨A', B', n', K', V', ha, hr, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hA', hB', hn', hK', hV'⟩ := ha
  subst A' B' n' K' V'
  obtain ⟨hkeys, hvals⟩ := initTermColumns_records S hAw hwordsB hr
  refine runs_seq_call_le hFin (vs := [K, V, N, P, tmp, dst]) rfl ?_ ?_ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hK
    · exact hV
    · exact hN
    · exact hP
    · exact ht
    · exact hw _ (by simp)
  · refine ⟨K, V, tmp, dst, by rw [initTermRecords_length],
      ⟨K, V, tmp, by rw [initTermRecords_length], hkeys, hvals, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [initTermRecords_length]
      exact Nat.le_add_right V N
    · rw [initTermRecords_length]
    · exact fun _ hi => initTermRecords_key_lt hgood.b_pos hgood.valid hi
    · simpa only [initTermRecords_length] using room
    · exact (Nat.le_add_right dst n).trans
        ((Nat.le_add_right B n).trans ((Nat.le_add_right K N).trans (Nat.le_add_right V N)))
    · intro y hy
      have hty : tmp ≤ y := by rw [initTermRecords_length] at hy; omega
      exact (hf₃ y (.inr (.inr hty))).trans (hz₂ _ (by dsimp [tmp, V] at hty; omega))
  intro r mem₄ pos₄ hp₄
  obtain ⟨_, _, _, dst', ha, hr, hdata, hz₄, hf₄⟩ := hp₄
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, hd⟩ := ha
  subst dst'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨base, dst, rfl, ?_, hdata, hz₄, ?_⟩ ?_
  · change r = dst + (initTermSection S).length
    rw [hlen]
    simpa [initTermRecords_length, Nat.add_assoc] using hr
  · intro y hy
    have hB' : y < B := hy.trans_le (Nat.le_add_right _ _)
    have hK' : y < K := hB'.trans_le (Nat.le_add_right _ _)
    exact (hf₄ _ hy).trans ((hf₃ _ (.inl hK')).trans ((hf₂ _ hB').trans (hf₁ _ hy)))
  · have hdist : tmp - dst = 6 * n := by dsimp [tmp, V, K, B, N]; omega
    simp [SecContract, initTermWriterCost, initTermColumnsContract, initBucketMoveContract,
      initTermRecords_length, Expr.size, argsSize, secArgs, hdist, N]
    omega

/-- The terminal list section agrees with the initialized block. -/
theorem initTermSection_eq (S : StaticData) (a : ℕ) (s : PathDSAbsState)
    (hb : 0 < S.b) (hH : S.H.IsValid S.x S.b) :
    (initConcrete S a s).sections.getD 7 [] = initTermSection S := by
  change csrList S.numTerm (termConns S.H S.x S.b) = _
  unfold initTermSection
  congr 1
  funext u
  exact (initTermRecords_buckets hb hH u).symm

/-- The two endpoint entries use the same ordered-traversal helpers. -/
def initTermWriterHelpers (k : ℕ) : List Stmt :=
  [initEndpointWriter 0 (k + 9), initEndpointWriter 1 (k + 9), initTermColumns,
    initBucketMove (k + 4) (k + 5) (k + 6), initBucket (k + 7) (k + 8),
    initFillWord, moveDown, csrB, initBucketGather] ++ endpointHelpers (k + 9)

/-- The relocatable writer for section 7. -/
def termBucketW (a : ℕ) : SecW a where
  body k := initTermWriter k (k + 1) (k + 2) (k + 3)
  helpers := initTermWriterHelpers
  l S _ _ := initTermSection S
  cost S _ _ := initTermWriterCost S
  scratch S _ _ := initTermWriterScratch S
  noRand k := ⟨initTermWriter_noRand _ _ _ _, by
    simp [initTermWriterHelpers, endpointHelpers, initEndpointWriter, Stmt.NoRand,
      initTermColumns_noRand, initBucketMove_noRand, initBucket_noRand, initBucketGather_noRand,
      initFillWord_noRand, moveDown, forRange, forUp, csrB_noRand,
      initEndpointDepth_noRand, initEndpointLevel_noRand, initEndpointChild_noRand,
      initEndpointRange_noRand, initEndpointRow_noRand, initCSRSeek_noRand,
      initCSRCount_noRand, initEndpointCopy_noRand]⟩
  spec w p f k hp hh S G := by
    have hE (field idx : ℕ) (hfield : field < 2)
        (hidx : p.procs[idx]? = some (initEndpointWriter field (k + 9))) :
        MeetsContract w p idx (SecContract w (buildInv w S a G)
          ⟨idx, fun _ => initEndpointWords S field, fun _ => initEndpointSectionCost S, fun _ => 0⟩) :=
      initEndpointWriter_meetsContract (by omega) hidx
        (hh 9 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 10 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 11 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 12 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 13 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 14 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 15 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 16 (by simp [initTermWriterHelpers, endpointHelpers]))
        (hh 17 (by simp [initTermWriterHelpers, endpointHelpers]))
    have hFirst : p.procs[k]? = some (initEndpointWriter 0 (k + 9)) := by
      simpa [initTermWriterHelpers] using hh 0 (by simp [initTermWriterHelpers])
    have hSecond := hh 1 (by simp [initTermWriterHelpers])
    have hCols := hh 2 (by simp [initTermWriterHelpers])
    have hFinish := hh 3 (by simp [initTermWriterHelpers])
    have hBucket := hh 4 (by simp [initTermWriterHelpers])
    have hClear := hh 5 (by simp [initTermWriterHelpers])
    have hMove := hh 6 (by simp [initTermWriterHelpers])
    have hSort : p.HasAt (k + 7) [csrB] := by
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst i
      simpa [initTermWriterHelpers] using hh 7 (by simp [initTermWriterHelpers])
    have hGather := hh 8 (by simp [initTermWriterHelpers])
    exact initTermWriter_meetsContract hp (hE 0 _ (by decide) hFirst)
      (hE 1 _ (by decide) hSecond) (initTermColumns_meetsContract hCols)
      (initBucketMove_meetsContract hFinish (initBucket_meetsContract hBucket hSort hGather)
        (initFillWord_meetsContract hClear) (moveDown_meetsContract hMove))

end MinCostFlow.HierPaths

end
