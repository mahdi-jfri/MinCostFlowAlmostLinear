module

public import MinCostFlow.HierPaths.InitProgReverseModel

/-!
# Section 6 of the initialized hierarchy

Rebuild the projected edge rows in scratch. The data words serve as
keys, and the designated endpoint column supplies their payloads.
Stable bucketing writes the reverse index and reclaims the scratch.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

def initReverseWriter (edges endpoints repeatProc finish : ℕ) : Stmt :=
  .call 7 edges secArgs ;;
  .call 8 endpoints [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 7] ;;
  .assign 9 (.bin .sub (.reg 8) (.reg 7)) ;;
  .call 10 repeatProc [.reg 6, .reg 7, .reg 9, .reg 8] ;;
  .call 11 finish [.bin .add (.bin .add (.reg 6) (.reg 9)) (.const 1), .reg 8,
    .bin .sub (.reg 10) (.reg 8), .load (.bin .add (.reg 0) (.const 1)), .reg 10, .reg 6] ;;
  .ret (.reg 11)

theorem initReverseWriter_noRand (a b c d : ℕ) : (initReverseWriter a b c d).NoRand := by
  simp [initReverseWriter, Stmt.NoRand]

def initReverseWriterScratch (S : StaticData) (G : Graph) : ℕ :=
  initProjectedWriterScratch S false + 2 * S.numConn + 3 * (initReverseRecords S).length +
    2 * G.m + 4

def initReverseWriterCost (S : StaticData) (G : Graph) : ℕ :=
  initProjectedWriterCost S G false + initEndpointSectionCost S +
    500 * ((initReverseRecords S).length + S.numConn + G.m + 1)

private theorem initRepeatRows_cost_eq (w k : ℕ) (f : ℕ → List ℕ) (vals : ℕ → ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (initRepeatRowsContract w k f vals).cost args mem = 15 * (csrData k f).length + 54 * k + 15 := by
  unfold initRepeatRowsContract
  rw [rangeCost_add, rangeCost_const, rangeCost_zero_eq_range]
  simp only [Nat.sub_zero]
  have he (l : List ℕ) : (l.map (fun i => 15 * (f i).length)).sum = 15 * (l.flatMap f).length := by
    induction l with
    | nil => simp
    | cons i l ih => simp [ih, Nat.mul_add]
  rw [he]
  change _ = 15 * ((List.range k).flatMap f).length + 54 * k + 15
  omega

set_option maxHeartbeats 800000 in
theorem initReverseWriter_meetsContract {w a f edges endpoints repeatProc finish fill : ℕ}
    {S : StaticData} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (initReverseWriter edges endpoints repeatProc finish))
    (hEdge : MeetsContract w p edges (SecContract w (buildInv w S a G)
      ⟨edges, fun _ => initProjectedSection S false, fun _ => initProjectedWriterCost S G false,
        fun _ => initProjectedWriterScratch S false⟩))
    (hEnd : MeetsContract w p endpoints (SecContract w (buildInv w S a G)
      ⟨endpoints, fun _ => initEndpointWords S 0, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hRepeat : p.procs[repeatProc]? = some (initRepeatRows fill))
    (hFill : p.procs[fill]? = some initFillWord)
    (hFin : MeetsContract w p finish (initBucketMoveContract w G.m (initReverseRecords S))) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initReverseSection S G, fun _ => initReverseWriterCost S G,
        fun _ => initReverseWriterScratch S G⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hroom⟩ := hpre
  obtain ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩ := hInv
  have hInv := (show buildInv w S a G base mem from
    ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩)
  subst base
  change h₁ + 25 ≤ dst at hdst
  let base := [ga, pn, pd, M, h, h₁]
  let N := S.numConn
  let rs := initReverseRecords S
  let K := rs.length
  let E := initProjectedSection S false
  let ep := dst + E.length
  let vals := ep + N
  let tmp := vals + K
  let keys := dst + N + 1
  have hE : E.length = N + 1 + K := by
    dsimp [E, initProjectedSection]
    rw [csrList, List.length_append, length_csrOffsets, initReverseData_length]
  have hLen := initReverseSection_length hgood
  change dst + (initReverseSection S G).length + initReverseWriterScratch S G < 2 ^ w at hroom
  rw [hLen] at hroom
  have hKr : (initReverseRecords S).length = K := rfl
  have hBound : tmp + (G.m + 1) + K + G.m + K + G.m + 2 < 2 ^ w := by
    dsimp only [tmp, vals, ep, initReverseWriterScratch] at *
    rw [hE]
    omega
  have hEdgeRoom : dst + E.length + initProjectedWriterScratch S false < 2 ^ w := by
    rw [hE]
    dsimp only [initReverseWriterScratch] at hroom
    omega
  have ht : tmp < 2 ^ w := by omega
  have hvals : vals < 2 ^ w := by dsimp [tmp] at ht; omega
  have hep : ep < 2 ^ w := by dsimp [vals] at hvals; omega
  have h1 : 1 < 2 ^ w := by omega
  have hM : G.m < 2 ^ w := by omega
  have hN : N < 2 ^ w := by omega
  have hK : K < 2 ^ w := by omega
  have hKeys : keys < 2 ^ w := by dsimp [ep] at hep; rw [hE] at hep; dsimp [keys]; omega
  have hEps : (initEndpointWords S 0).length = N := by
    rw [initEndpointWords_eq_map S 0 (by decide), List.length_map]
    rfl
  refine runs_start_le ?_
  unfold initReverseWriter
  refine runs_seq_call_le hEdge (vs := base ++ [dst]) rfl hw
    ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hEdgeRoom⟩ ?_
  intro r mem₁ pos₁ hp₁
  obtain ⟨_, dst', ha, hr, hEd, hz₁, hf₁⟩ := hp₁
  have hd : dst' = dst := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst dst'
  change r = ep at hr
  subst r
  have hInv₁ := buildInv_stable w S a G base mem mem₁ hInv
    (fun y hy => hf₁ y (by change y < h₁ at hy; omega))
  refine runs_seq_call_le hEnd (vs := base ++ [ep]) rfl ?_
    ⟨base, ep, rfl, hbl, hInv₁, hz₁,
      by change h₁ + 25 ≤ ep; exact hdst.trans (Nat.le_add_right _ _),
      by simpa only [hEps, Nat.add_zero] using hvals⟩ ?_
  · intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hw v (List.mem_append_left _ hv)
    · exact hep
  intro r mem₂ pos₂ hp₂
  obtain ⟨_, ep', ha, hr, hPayload, hz₂, hf₂⟩ := hp₂
  have hd : ep' = ep := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst ep'
  change r = ep + (initEndpointWords S 0).length at hr
  rw [hEps] at hr
  change r = vals at hr
  subst r
  have hEd₂ : ListAt mem₂ dst E :=
    listAt_congr (fun i hi => (hf₂ _ (by dsimp [ep]; omega)).symm) hEd
  have hEg : (initRepeatRowsWords N (initProjectedRow S false) (initReversePayload S)).length = K := by
    rw [← initReverseRecords_vals, List.length_map]
  have hvalsAt (i : ℕ) (hi : i < N) :
      mem₂ (ep + i) = initReversePayload S i ∧ initReversePayload S i < 2 ^ w := by
    have hi' : i < (connRecs S.H S.x S.b).length := hi
    have hz := connRec_spec hgood.b_pos hgood.valid (getD_mem_connRecs hi')
    have hP : S.numTerm < 2 ^ w := by
      obtain ⟨_, _, hlen⟩ := staticOut_owner_facts hS
      change 10 + S.numTerm ≤ S.encode.length at hlen
      omega
    rw [initEndpointWords_eq_map S 0 (by decide)] at hPayload
    have h := hPayload i (by simpa using hi')
    rw [List.getElem_map] at h
    refine ⟨?_, hz.2.2.2.1.trans hP⟩
    unfold initReversePayload
    rw [List.getD_eq_getElem _ _ hi']
    exact h
  refine runs_seq_assign_le (v := N) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := vals) rfl) (Expr.eval_reg_of_eq (v := ep) rfl) hvals)
    (Nat.add_sub_cancel_left _ _)) ?_
  have hRepeated := initRepeatRows_meetsContract (w := w) (k := N)
    (f := initProjectedRow S false) (vals := initReversePayload S) hRepeat hFill
  refine runs_seq_call_le hRepeated (vs := [dst, ep, N, vals]) rfl ?_
    ⟨dst, ep, vals, rfl, hEd₂, Nat.le_add_right _ _, le_rfl, hvalsAt, by simpa [hEg] using ht, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hep
    · exact hN
    · exact hvals
  intro r mem₃ pos₃ hp₃
  obtain ⟨dst', ep', vals', ha, hr, hVals, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, he⟩ := ha
  subst vals'
  rw [hEg] at hr
  change r = tmp at hr
  subst r
  have hKeysAt : ListAt mem₃ keys (rs.map Prod.fst) := by
    have h := (listAt_append.mp hEd₂).2
    rw [length_csrOffsets] at h
    rw [initReverseRecords_keys]
    refine listAt_congr (fun i hi => (hf₃ _ (.inl ?_)).symm) ?_
    · rw [initReverseData_length] at hi
      dsimp only [keys, vals, ep]
      rw [hE]
      omega
    · simpa only [keys, Nat.add_assoc] using h
  have hValues : ListAt mem₃ vals (rs.map Prod.snd) := by
    rw [initReverseRecords_vals]
    exact hVals
  have hga : ga + 1 < dst := by have := graph_encode_length G; omega
  have hGraphM : mem₃ (ga + 1) = G.m := (hf₃ _ (.inl (by dsimp [vals, ep]; omega))).trans
    ((hf₂ _ (by dsimp [ep]; omega)).trans ((hf₁ _ hga).trans (graphAt_m hG)))
  have hkeys' : dst + N < 2 ^ w := by dsimp [keys] at hKeys; omega
  have hga' : ga + 1 < 2 ^ w := hga.trans (hw _ (by simp))
  have hkm : tmp - vals = K := Nat.add_sub_cancel_left _ _
  refine runs_seq_call_le hFin (vs := [keys, vals, K, G.m, tmp, dst]) ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hkeys', hKeys, hga', hGraphM, hkm,
      hK, keys, N]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact hw _ (by simp)
  · refine ⟨keys, vals, tmp, dst, rfl, ⟨keys, vals, tmp, rfl, hKeysAt, hValues, ?_, le_rfl,
      fun _ hi => initReverseRecords_key_lt hgood hi, hBound⟩, ?_, ?_⟩
    · dsimp only [tmp, vals, ep, keys]
      rw [hE]
      omega
    · dsimp [tmp, vals, ep]; omega
    · intro y hy
      have hty : tmp ≤ y := by omega
      exact (hf₃ _ (.inr hty)).trans (hz₂ _ (by dsimp [tmp] at hty; omega))
  intro r mem₄ pos₄ hp₄
  obtain ⟨_, _, _, dst', ha, hr, hdata, hzero₄, hf₄⟩ := hp₄
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, hd⟩ := ha
  subst dst'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨base, dst, rfl, ?_, hdata, hzero₄, ?_⟩ ?_
  · change r = dst + (initReverseSection S G).length
    rw [hLen]
    simpa [Nat.add_assoc] using hr
  · intro y hy
    exact (hf₄ _ hy).trans ((hf₃ _ (.inl (by dsimp [vals, ep]; omega))).trans
      ((hf₂ _ (by dsimp [ep]; omega)).trans (hf₁ _ hy)))
  · rw [initRepeatRows_cost_eq, initReverseData_length]
    have hd : tmp - dst = 2 * N + 1 + 2 * K := by dsimp [tmp, vals, ep]; rw [hE]; omega
    simp [SecContract, initReverseWriterCost, initBucketMoveContract,
      Expr.size, argsSize, secArgs, hd]
    omega

end MinCostFlow.HierPaths

end
