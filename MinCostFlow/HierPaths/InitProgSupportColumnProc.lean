module

public import MinCostFlow.HierPaths.InitProgSupportColumns

/-!
# Concatenating the two parts of a support column

The column starts with the terminal words and continues with the walk
words. Both input tables are preserved.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the owners, terminal count, destination, connector count and walk section. -/
def initSupportColumnProc (emit rows : ℕ) : Stmt :=
  .call 5 emit [.reg 0, .reg 1, .const 0, .reg 2] ;;
  .call 6 rows [.reg 4, .reg 3, .reg 5] ;;
  .ret (.reg 6)

theorem initSupportColumnProc_noRand (emit rows : ℕ) : (initSupportColumnProc emit rows).NoRand := by
  simp [initSupportColumnProc, Stmt.NoRand]

def initSupportColumnContract (w : ℕ) (S : StaticData) (keys : Bool) : Contract where
  pre args mem := ∃ owner dst verts, args = [owner, S.numTerm, dst, S.numConn, verts] ∧
    ListAt mem owner (initSupportOwners S) ∧ ListAt mem verts (initProjectedSection S true) ∧
    owner + S.numTerm ≤ dst ∧ verts + (initProjectedSection S true).length ≤ dst ∧
    dst + (initSupportColumn S keys).length < 2 ^ w ∧ 3 < 2 ^ w
  post args mem r mem' := ∃ owner dst verts, args = [owner, S.numTerm, dst, S.numConn, verts] ∧
    r = dst + (initSupportColumn S keys).length ∧ ListAt mem' dst (initSupportColumn S keys) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 50 * (S.numTerm + (csrData S.numConn (initProjectedRow S true)).length) +
    90 * S.numConn + 80

theorem initSupportColumn_length (S : StaticData) (keys : Bool) :
    (initSupportColumn S keys).length = (initSupportRecords S).length := by
  rw [← initSupportRecords_column, List.length_map]

theorem initSupportColumnProc_meetsContract {w j emit rows : ℕ} {keys : Bool} {S : StaticData}
    {p : Program} (hp : p.procs[j]? = some (initSupportColumnProc emit rows))
    (he : p.procs[emit]? = some (initSupportEmit keys false))
    (hr : MeetsContract w p rows (initSupportRowsContract w S.numConn keys (initProjectedRow S true))) :
    MeetsContract w p j (initSupportColumnContract w S keys) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨owner, dst, verts, rfl, hOwn, hVerts, ho, hv, hroom, h3⟩ := hpre
  let n := S.numTerm
  let part := initAppendPrefix
    (initSupportWords keys false ((initSupportOwners S).getD · 0) 0) n
  let walk := initAppendPrefix (initSupportRowWords keys (initProjectedRow S true)) S.numConn
  let mid := dst + 3 * n
  have hPart : part.length = 3 * n := initSupportPrefix_length _ _ _ _ _
  have hroom' : mid + walk.length < 2 ^ w := by
    change dst + (part ++ walk).length < 2 ^ w at hroom
    rw [List.length_append, hPart, ← Nat.add_assoc] at hroom
    exact hroom
  have hMid : mid < 2 ^ w := by omega
  have hD : dst ≤ mid := Nat.le_add_right ..
  refine runs_start_le ?_
  unfold initSupportColumnProc
  refine runs_seq_call_le (initSupportEmit_meetsContract (l := initSupportOwners S) (row := 0) he)
    (vs := [owner, n, 0, dst]) ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState, Nat.mod_eq_of_lt (show 0 < 2 ^ w by omega), n]
  · intro v h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp [n])
    · omega
    · exact hw _ (by simp)
  · refine ⟨owner, dst, by simp [n], hOwn, ?_, ?_, h3⟩
    · simpa only [initSupportOwners_length] using ho
    · simpa only [initSupportOwners_length] using hMid
  intro r mem₁ pos₁ hpost
  obtain ⟨owner', dst', ha, hp₁, hPartAt, hf₁⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨howner, _, _, hdst⟩ := ha
  subst owner' dst'
  rw [initSupportOwners_length] at hp₁ hPartAt
  change r = mid at hp₁
  subst r
  have hVerts₁ : ListAt mem₁ verts (initProjectedSection S true) :=
    listAt_congr (fun i hi => (hf₁ _ (.inl (by omega))).symm) hVerts
  refine runs_seq_call_le hr (vs := [verts, S.numConn, mid]) rfl ?_
    ⟨verts, mid, rfl, hVerts₁, hv.trans hD, hroom', h3⟩ ?_
  · intro v h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hMid
  intro r mem₂ pos₂ hpost
  obtain ⟨verts', mid', ha, hp₂, hWalkAt, hf₂⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hverts, _, hmid⟩ := ha
  subst verts' mid'
  have hEnd : r = dst + (initSupportColumn S keys).length := by
    change _ = dst + (part ++ walk).length
    rw [hp₂, List.length_append, hPart, ← Nat.add_assoc]
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨owner, dst, verts, rfl, hEnd, ?_, fun y hy => ?_⟩ ?_
  · change ListAt mem₂ dst (part ++ walk)
    refine listAt_append.mpr ⟨listAt_congr (fun i hi => (hf₂ _ (.inl (by
      rw [hPart] at hi; dsimp [mid]; omega))).symm) hPartAt, ?_⟩
    rw [hPart]
    exact hWalkAt
  · change y < dst ∨ r ≤ y at hy
    exact (hf₂ _ (hy.imp_left (fun h => h.trans_le hD))).trans
      (hf₁ _ (hy.imp_right (fun h => by omega)))
  · simp [initSupportColumnContract, initSupportRowsContract, initSupportEmitContract,
      initSupportOwners_length, Expr.size, argsSize, n]
    omega

end MinCostFlow.HierPaths

end
