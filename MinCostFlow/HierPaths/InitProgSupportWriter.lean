module

public import MinCostFlow.HierPaths.InitProgSupportColumnProc

/-!
# Section 9 of the initialized hierarchy

Build vertex walks and the two support columns in scratch. Stable
bucketing writes the support offsets and entries and reclaims scratch.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

def initSupportSection (S : StaticData) (G : Graph) : List ℕ :=
  csrList G.n (buckets (initSupportRecords S))

def initSupportWriter (vertices keys vals finish : ℕ) : Stmt :=
  .call 7 vertices secArgs ;;
  .assign 8 (.bin .add (.reg 4) (.const 10)) ;;
  .assign 9 (.bin .shiftLeft (.const 1) (.load (.bin .add (.reg 4) (.const 7)))) ;;
  .assign 10 (.load (.bin .add (.reg 4) (.const 9))) ;;
  .call 11 keys [.reg 8, .reg 9, .reg 7, .reg 10, .reg 6] ;;
  .call 12 vals [.reg 8, .reg 9, .reg 11, .reg 10, .reg 6] ;;
  .call 13 finish [.reg 7, .reg 11, .bin .sub (.reg 12) (.reg 11), .load (.reg 0), .reg 12, .reg 6] ;;
  .ret (.reg 13)

theorem initSupportWriter_noRand (a b c d : ℕ) : (initSupportWriter a b c d).NoRand := by
  simp [initSupportWriter, Stmt.NoRand]

def initSupportWriterScratch (S : StaticData) (G : Graph) : ℕ :=
  initProjectedWriterScratch S true + (initProjectedSection S true).length +
    3 * (initSupportRecords S).length + 2 * G.n + 3

def initSupportWriterCost (S : StaticData) (G : Graph) : ℕ :=
  initProjectedWriterCost S G true + 600 * ((initSupportRecords S).length + G.n +
    (initProjectedSection S true).length + 1)

set_option maxHeartbeats 800000 in
theorem initSupportWriter_meetsContract {w a f vertices keys vals finish : ℕ}
    {S : StaticData} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (initSupportWriter vertices keys vals finish))
    (hVerts : MeetsContract w p vertices (SecContract w (buildInv w S a G)
      ⟨vertices, fun _ => initProjectedSection S true, fun _ => initProjectedWriterCost S G true,
        fun _ => initProjectedWriterScratch S true⟩))
    (hKeys : MeetsContract w p keys (initSupportColumnContract w S true))
    (hVals : MeetsContract w p vals (initSupportColumnContract w S false))
    (hFin : MeetsContract w p finish (initBucketMoveContract w G.n (initSupportRecords S))) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initSupportSection S G, fun _ => initSupportWriterCost S G,
        fun _ => initSupportWriterScratch S G⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hroom⟩ := hpre
  obtain ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩ := hInv
  have hInv := (show buildInv w S a G base mem from
    ⟨ga, pn, pd, M, h, h₁, hbase, hS, hsep, hG, hgh, hnum, hden, hgood, hbw⟩)
  subst base
  change h₁ + 25 ≤ dst at hdst
  let base := [ga, pn, pd, M, h, h₁]
  let V := initProjectedSection S true
  let N := S.numConn
  let P := S.numTerm
  let rs := initSupportRecords S
  let K := rs.length
  let owner := h + 10
  let keyAddr := dst + V.length
  let valAddr := keyAddr + K
  let tmp := valAddr + K
  have hpc : P = 2 ^ S.x := rfl
  have hVlen : V.length = N + 1 + (csrData N (initProjectedRow S true)).length := by
    dsimp [V, initProjectedSection, N]
    rw [csrList, List.length_append, length_csrOffsets]
  have hKlen : K = 3 * P + 3 * (csrData N (initProjectedRow S true)).length :=
    initSupportRecords_length S
  have hLen : (initSupportSection S G).length = G.n + 1 + K := by
    rw [initSupportSection, csrList, List.length_append, length_csrOffsets,
      initBucket_data_length _ _ (fun _ hi => initSupportRecords_key_lt hgood hi)]
  change dst + (initSupportSection S G).length + initSupportWriterScratch S G < 2 ^ w at hroom
  rw [hLen] at hroom
  change dst + (G.n + 1 + K) + (_ + V.length + 3 * K + 2 * G.n + 3) < 2 ^ w at hroom
  have hBound : tmp + (G.n + 1) + K + G.n + K + G.n + 2 < 2 ^ w := by
    dsimp only [tmp, valAddr, keyAddr]
    omega
  have hvRoom : dst + V.length + initProjectedWriterScratch S true < 2 ^ w := by omega
  have h3 : 3 < 2 ^ w := by omega
  have hK : K < 2 ^ w := by omega
  have hN : N < 2 ^ w := by omega
  have hP : P < 2 ^ w := by omega
  have hKey : keyAddr < 2 ^ w := by dsimp only [keyAddr]; omega
  have hVal : valAddr < 2 ^ w := by dsimp only [valAddr, keyAddr]; omega
  have hTmp : tmp < 2 ^ w := by omega
  have hx : mem (h + 7) = S.x := (staticOut_owner_facts hS).1
  have hOwn : ListAt mem owner (initSupportOwners S) := (staticOut_owner_facts hS).2.1
  have hEnc : 10 + P ≤ S.encode.length := (staticOut_owner_facts hS).2.2
  have ho : owner + P ≤ dst := by dsimp [owner]; omega
  have ho' : owner < 2 ^ w := by omega
  have hnc : mem (h + 9) = N := by
    have hs := listAt_csrList_get (k := 6) (f := fun i => S.sections.getD i []) hS (i := 0)
      (by decide)
    simpa [StaticData.sections, Nat.add_assoc, N] using hs 2 (by simp [StaticData.sections])
  have h10 : 10 < 2 ^ w := by dsimp [owner] at ho'; omega
  have h7 : h + 7 < dst := by dsimp [owner] at ho; omega
  have h9 : h + 9 < dst := by dsimp [owner] at ho; omega
  have hWord : dst < 2 ^ w := hw _ (by simp)
  have hGa : ga < dst := by omega
  refine runs_start_le ?_
  unfold initSupportWriter
  refine runs_seq_call_le hVerts (vs := base ++ [dst]) rfl hw
    ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hvRoom⟩ ?_
  intro r mem₁ pos₁ hp₁
  obtain ⟨_, dst', ha, hr, hV, hz₁, hf₁⟩ := hp₁
  have hd : dst' = dst := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst dst'
  change r = keyAddr at hr
  subst r
  refine runs_seq_assign_le (v := owner) (Expr.eval_add
    (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_const h10) ho') ?_
  refine runs_seq_assign_le (v := P) (Expr.eval_eq_of_eq (Expr.eval_shiftLeft
    (Expr.eval_const (show 1 < 2 ^ w by omega))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (show 7 < 2 ^ w by omega)) (h7.trans hWord)) ((hf₁ _ h7).trans hx))
    (by rw [Nat.shiftLeft_eq, Nat.one_mul, ← hpc]; exact hP)) (by rw [Nat.shiftLeft_eq, Nat.one_mul, hpc])) ?_
  refine runs_seq_assign_le (v := N) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_const (show 9 < 2 ^ w by omega))
    (h9.trans hWord)) ((hf₁ _ h9).trans hnc)) ?_
  have hOwn₁ : ListAt mem₁ owner (initSupportOwners S) := listAt_congr (fun i hi =>
    (hf₁ _ (by rw [initSupportOwners_length] at hi; omega)).symm) hOwn
  have hVK : dst + V.length ≤ keyAddr := le_rfl
  have hkArgs : ∀ v ∈ [owner, P, keyAddr, N, dst], v < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  refine runs_seq_call_le hKeys (vs := [owner, P, keyAddr, N, dst]) rfl hkArgs
    ⟨owner, keyAddr, dst, rfl, hOwn₁, hV, ho.trans (Nat.le_add_right _ _), hVK,
      by rw [initSupportColumn_length]; exact hVal, h3⟩ ?_
  intro r mem₂ pos₂ hp₂
  obtain ⟨_, ka, _, ha, hr, hKeyAt, hf₂⟩ := hp₂
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, hk, _, _⟩ := ha
  subst ka
  rw [initSupportColumn_length] at hr
  change r = valAddr at hr
  subst r
  have hOwn₂ : ListAt mem₂ owner (initSupportOwners S) :=
    listAt_congr (fun i hi => (hf₂ _ (.inl (by rw [initSupportOwners_length] at hi; omega))).symm) hOwn₁
  have hV₂ : ListAt mem₂ dst V :=
    listAt_congr (fun i hi => (hf₂ _ (.inl (by omega))).symm) hV
  have hvArgs : ∀ v ∈ [owner, P, valAddr, N, dst], v < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  refine runs_seq_call_le hVals (vs := [owner, P, valAddr, N, dst]) rfl hvArgs
    ⟨owner, valAddr, dst, rfl, hOwn₂, hV₂, by dsimp only [valAddr]; omega,
      Nat.le_add_right _ _, by rw [initSupportColumn_length]; exact hTmp, h3⟩ ?_
  intro r mem₃ pos₃ hp₃
  obtain ⟨_, va, _, ha, hr, hValAt, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, hv, _, _⟩ := ha
  subst va
  rw [initSupportColumn_length] at hr
  change r = tmp at hr
  subst r
  have hKeysAt : ListAt mem₃ keyAddr (rs.map Prod.fst) := by
    rw [show rs.map Prod.fst = initSupportColumn S true from initSupportRecords_column S true]
    exact listAt_congr (fun i hi => (hf₃ _ (.inl (by
      rw [initSupportColumn_length] at hi
      exact Nat.add_lt_add_left hi keyAddr))).symm) hKeyAt
  have hValues : ListAt mem₃ valAddr (rs.map Prod.snd) := by
    rw [show rs.map Prod.snd = initSupportColumn S false from initSupportRecords_column S false]
    exact hValAt
  have hBelow (y : ℕ) (hy : y < dst) : mem₃ y = mem y :=
    (hf₃ _ (.inl (by dsimp only [valAddr, keyAddr]; omega))).trans
      ((hf₂ _ (.inl (by dsimp only [keyAddr]; omega))).trans (hf₁ _ hy))
  have hGn : mem₃ ga = G.n := (hBelow _ hGa).trans (graphAt_n hG)
  have hGn' : G.n < 2 ^ w := by omega
  have htk : tmp - valAddr = K := Nat.add_sub_cancel_left _ _
  refine runs_seq_call_le hFin (vs := [keyAddr, valAddr, K, G.n, tmp, dst]) ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, BinOp.eval, startState, htk, hK, hGn]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  · refine ⟨keyAddr, valAddr, tmp, dst, rfl,
      ⟨keyAddr, valAddr, tmp, rfl, hKeysAt, hValues, ?_, le_rfl,
       fun _ hi => initSupportRecords_key_lt hgood hi, hBound⟩,
      ?_, ?_⟩
    · exact Nat.le_add_right _ _
    · dsimp only [tmp, valAddr, keyAddr]; omega
    · intro y hy
      have hy' : tmp ≤ y := by omega
      have hv : valAddr ≤ tmp := Nat.le_add_right _ _
      have hk : keyAddr ≤ valAddr := Nat.le_add_right _ _
      exact (hf₃ _ (.inr hy')).trans ((hf₂ _ (.inr (hv.trans hy'))).trans
        (hz₁ _ (hk.trans (hv.trans hy'))))

  intro r mem₄ pos₄ hp₄
  obtain ⟨_, _, _, dst', ha, hr, hSection, hz, hf₄⟩ := hp₄
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, hd⟩ := ha
  subst dst'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨base, dst, rfl, ?_, hSection, hz, fun y hy => (hf₄ _ hy).trans (hBelow _ hy)⟩ ?_
  · change r = dst + (initSupportSection S G).length
    rw [hLen]
    simpa [Nat.add_assoc] using hr
  · have hdist : tmp - dst = V.length + 2 * K := by dsimp only [tmp, valAddr, keyAddr]; omega
    simp [SecContract, initSupportWriterCost, initSupportColumnContract, initBucketMoveContract,
      Expr.size, argsSize, secArgs, hdist]
    dsimp only [V, N, P, K, rs] at hVlen hKlen
    dsimp only [V, K, rs]
    omega

end MinCostFlow.HierPaths

end
