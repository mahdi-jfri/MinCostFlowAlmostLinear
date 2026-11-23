module

public import MinCostFlow.HierPaths.BuildTopScheduleLayout

/-!
# Preserving the depth schedule during the recursion

An advance can update its reply directory and the next boundary pointer.
The schedule occupies earlier addresses, so the driver can keep using it.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- An advance preserves all schedule rows below the initial heap. -/
theorem buildTopAdvance_scheduleFrame {w K table n x b i h v : ℕ}
    {D : BuildTopDepthInput} {mem mem' : ℕ → ℕ}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hi : i < n) (hd : D.replyDir = buildTopScheduleReplies table n x i)
    (hstart : buildTopScheduleEnd table n x ≤ h)
    (hp : (D.advanceContract w K space).post
      (D.args h ++ [buildTopSchedulePointer table n (i + 1)]) mem v mem') :
    ∀ y < table + 13 * n, mem' y = mem y := by
  obtain ⟨h',out,dir,he,_,_,_,_,_,hf,_⟩ := hp
  have hh : h' = h := by
    have e := congrArg (fun ws : List ℕ => ws.getD 12 0) he
    simpa [BuildTopDepthInput.args] using e.symm
  have ho : out = buildTopSchedulePointer table n (i + 1) := by
    have e := congrArg (fun ws : List ℕ => ws.getD 13 0) he
    simpa [BuildTopDepthInput.args] using e.symm
  subst h' out
  intro y hy
  obtain ⟨_,_,hr,_⟩ := buildTopSchedule_disjoint (table := table) (x := x) (b := b) hi
  have hptr : table + 13 * n ≤ buildTopSchedulePointer table n (i + 1) := by
    unfold buildTopSchedulePointer
    omega
  exact hf y (by
    unfold buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer at hstart
    omega) (by omega) (.inl (hd ▸ hy.trans_le (hptr.trans hr.le)))

/-- The advance links the next graph directory and keeps previous reply directories. -/
theorem buildTopAdvance_scheduleLink {w K table n x b i h v : ℕ}
    {D : BuildTopDepthInput} {mem mem' : ℕ → ℕ}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hi : i < n) (hd : D.replyDir = buildTopScheduleReplies table n x i)
    (hstart : buildTopScheduleEnd table n x ≤ h)
    (hp : (D.advanceContract w K space).post
      (D.args h ++ [buildTopSchedulePointer table n (i + 1)]) mem v mem') :
    h ≤ v ∧ (∀ j < i, ∀ g < numGroups x b j,
      mem' (buildTopScheduleReplies table n x j + g) =
        mem (buildTopScheduleReplies table n x j + g)) ∧
    ∃ (dir : ℕ) (addr : ℕ → ℕ) (reply : ℕ → BuildLevelData), h ≤ dir ∧ v = dir + D.count * D.branch ∧
      mem' (buildTopSchedulePointer table n (i + 1)) = dir ∧
      (∀ g < D.count, mem' (D.replyDir + g) = addr g ∧
        h ≤ addr g ∧ addr g + ((reply g).encode D.branch).length ≤ dir ∧
        ListAt mem' (addr g) ((reply g).encode D.branch) ∧
        (reply g).Good (D.graph g) (D.start g) D.childSize D.branch D.scale D.rank
          D.degree D.pathLog D.coreLog D.denominator) ∧
      ∀ k < D.count * D.branch,
        mem' (dir + k) = buildTopChildAddr (addr (k / D.branch)) D.branch
          (k % D.branch) (reply (k / D.branch)) := by
  obtain ⟨h',out,dir,he,hlo,_,hv,hout,_,hf,addr,reply,hreply,hchild⟩ := hp
  have hh : h' = h := by
    have e := congrArg (fun ws : List ℕ => ws.getD 12 0) he
    simpa [BuildTopDepthInput.args] using e.symm
  have ho : out = buildTopSchedulePointer table n (i + 1) := by
    have e := congrArg (fun ws : List ℕ => ws.getD 13 0) he
    simpa [BuildTopDepthInput.args] using e.symm
  subst h' out
  refine ⟨hlo.trans (hv ▸ Nat.le_add_right _ _), ?_, dir, addr, reply, hlo, hv, hout,
    hreply, hchild⟩
  intro j hj g hg
  have hprev := buildTopSchedule_replyOrder (table := table) (n := n) (x := x) (b := b) hj
  obtain ⟨_,_,_,hspan⟩ := buildTopSchedule_disjoint
    (table := table) (x := x) (b := b) hi
  have hcell : buildTopScheduleReplies table n x j + g < D.replyDir := by omega
  have hn : buildTopSchedulePointer table n (i + 1) < buildTopScheduleReplies table n x j := by
    unfold buildTopScheduleReplies buildTopSchedulePointer
    omega
  exact hf _ (by omega) (by omega) (.inl hcell)

end MinCostFlow.HierPaths

end
