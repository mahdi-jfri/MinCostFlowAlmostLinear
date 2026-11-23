module

public import MinCostFlow.HierPaths.BuildTopDepthSpec
public import MinCostFlow.HierPaths.BuildTopNextDir

/-!
# Advancing from a parent depth to its children

After the parent scan, append the next graph directory. Keep both the
reply blocks and the old directories for the final static output.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

/-- Append the next graph directory and record its start at the supplied cell. -/
def buildTopAdvance (depth next : ℕ) : Stmt :=
  .call 14 depth [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12] ;;
  .assign 15 (.bin .mul (.reg 5) (.reg 4)) ;;
  .call 16 next [.reg 1, .reg 14, .reg 4, .reg 15] ;;
  .store (.reg 13) (.reg 14) ;;
  .ret (.bin .add (.reg 14) (.reg 15))

theorem buildTopAdvance_noRand (depth next : ℕ) : (buildTopAdvance depth next).NoRand := by
  simp [buildTopAdvance, Stmt.NoRand]

namespace BuildTopDepthInput

variable (D : BuildTopDepthInput)

def advanceContract (w K : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Contract where
  pre args mem := ∃ h out, args = D.args h ++ [out] ∧ (D.contract w K space).pre (D.args h) mem ∧
    0 < D.branch ∧ out < h ∧ (out < D.replyDir ∨ D.replyDir + D.count ≤ out) ∧
    h + rangeCost (D.spaceStep space) 0 D.count + D.count * D.branch < 2 ^ w
  post args mem v mem' := ∃ h out dir,
    args = D.args h ++ [out] ∧ h ≤ dir ∧ dir ≤ h + rangeCost (D.spaceStep space) 0 D.count ∧
    v = dir + D.count * D.branch ∧ mem' out = dir ∧ ZeroFrom mem' v ∧
    (∀ x < h, x ≠ out → (x < D.replyDir ∨ D.replyDir + D.count ≤ x) → mem' x = mem x) ∧
    ∃ (addr : ℕ → ℕ) (reply : ℕ → BuildLevelData),
      (∀ g < D.count, mem' (D.replyDir + g) = addr g ∧
        h ≤ addr g ∧ addr g + ((reply g).encode D.branch).length ≤ dir ∧
        ListAt mem' (addr g) ((reply g).encode D.branch) ∧
        (reply g).Good (D.graph g) (D.start g) D.childSize D.branch D.scale D.rank
          D.degree D.pathLog D.coreLog D.denominator) ∧
      ∀ i < D.count * D.branch,
        mem' (dir + i) = buildTopChildAddr (addr (i / D.branch)) D.branch
          (i % D.branch) (reply (i / D.branch))
  cost args mem := (D.contract w K space).cost args mem + 100 * (D.count * D.branch) + 60

end BuildTopDepthInput

/-- Run a certified depth and build the directory needed by the next depth. -/
theorem buildTopAdvance_meetsContract {w K f depth next : ℕ} {p : Program} {D : BuildTopDepthInput}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (buildTopAdvance depth next))
    (hd : MeetsContract w p depth (D.contract w K space))
    (hn : ∀ addr reply, MeetsContract w p next (buildTopNextDirContract w D.count D.branch addr reply)) :
    MeetsContract w p f (D.advanceContract w K space) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h,out,rfl,hDepth,hk,ho,hOF,hRoom⟩ := hpre
  have hDepth' := hDepth
  obtain ⟨h', he, _, _, _, h1, _, hsep, _, _⟩ := hDepth'
  have he' : h' = h := by
    have x := congrArg (fun l : List ℕ => l.getD 12 0) he
    simpa [BuildTopDepthInput.args] using x.symm
  subst h'
  let n := D.count * D.branch
  have hn' : n < 2 ^ w := by omega
  have hWords : ∀ v ∈ D.args h, v < 2 ^ w := fun v hv => hw v (List.mem_append_left _ hv)
  refine runs_start_le ?_
  unfold buildTopAdvance
  refine runs_seq_call_le hd (vs := D.args h) rfl hWords hDepth ?_
  intro dir mem₁ pos₁ hpost
  obtain ⟨a, he, hLo, hHi, hZero, hFrame, hReply⟩ := hpost
  have ha : a = h := by
    have x := congrArg (fun l : List ℕ => l.getD 12 0) he
    simpa [BuildTopDepthInput.args] using x.symm
  subst a
  classical
  have hSelect : ∀ g, ∃ (a : ℕ) (R : BuildLevelData), g < D.count →
      mem₁ (D.replyDir + g) = a ∧ h ≤ a ∧ a + (R.encode D.branch).length ≤ dir ∧
      ListAt mem₁ a (R.encode D.branch) ∧
      R.Good (D.graph g) (D.start g) D.childSize D.branch D.scale D.rank D.degree D.pathLog
        D.coreLog D.denominator := by
    intro g
    by_cases hg : g < D.count
    · obtain ⟨a,R,hs⟩ := hReply g hg
      exact ⟨a, R, fun _ => hs⟩
    · exact ⟨0, ⟨fun _ => ⟨0, []⟩, fun _ _ => [], fun _ _ => []⟩, fun h => (hg h).elim⟩
  choose addr replies hR using hSelect
  refine runs_seq_assign_le (v := n) (Expr.eval_mul (Expr.eval_reg_of_eq (v := D.count) rfl)
    (Expr.eval_reg_of_eq (v := D.branch) rfl) hn') ?_
  refine runs_seq_call_le (hn addr replies) (vs := [D.replyDir, dir, D.branch, n]) rfl ?_
    ⟨D.replyDir, dir, rfl, hk, hsep.trans hLo, by omega, h1, ?_⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hWords _ (by simp [BuildTopDepthInput.args])
    · omega
    · exact hWords _ (by simp [BuildTopDepthInput.args])
    · exact hn'
  · intro g hg
    obtain ⟨ha, _, hb, hc, _⟩ := hR g hg
    exact ⟨ha,hb,hc⟩
  intro _ mem₂ pos₂ hpost
  obtain ⟨d', a', hEq, hTbl, hf⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨_,_,_⟩ := hEq
  subst d' a'
  have hOut : out < 2 ^ w := by omega
  refine runs_seq_store_le (x := out) (v := dir) (Expr.eval_reg_of_eq (v := out) rfl)
    (Expr.eval_reg_of_eq (v := dir) rfl) ?_
  refine runs_ret_le (v := dir + n) (Expr.eval_add (Expr.eval_reg_of_eq rfl)
    (Expr.eval_reg_of_eq rfl) (by omega)) ?_ ?_
  · refine ⟨h,out,dir,rfl,hLo,hHi,rfl,Function.update_self ..,?_,?_,addr,replies,?_,?_⟩
    · intro x hx
      change dir + n ≤ x at hx
      exact (Function.update_of_ne (by omega) _ _).trans
        ((hf x (.inr hx)).trans (hZero x (by omega)))
    · intro x hx hn' hskip
      exact (Function.update_of_ne hn' _ _).trans
        ((hf x (.inl (by omega))).trans (hFrame x hx hskip))
    · intro g hg
      obtain ⟨ha, hlo, hb, hc, hGood⟩ := hR g hg
      have hmem (x : ℕ) (hx : x < dir) (hne : x ≠ out) :=
        (Function.update_of_ne hne dir mem₂).trans (hf x (.inl hx))
      refine ⟨(hmem _ (by omega) (by rcases hOF with ho | ho <;> omega)).trans ha,
        hlo,hb,listAt_congr ?_ hc,hGood⟩
      intro i hi
      exact (hmem _ (by omega) (by omega)).symm
    · intro i hi
      exact (Function.update_of_ne (by omega) _ _).trans (hTbl i hi)
  · simp [BuildTopDepthInput.advanceContract, BuildTopDepthInput.contract,
      buildTopNextDirContract, Expr.size, argsSize, n]
    omega

end MinCostFlow.HierPaths

end
