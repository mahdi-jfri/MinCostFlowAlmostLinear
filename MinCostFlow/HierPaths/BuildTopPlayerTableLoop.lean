module

public import MinCostFlow.HierPaths.BuildTopPlayerTable

/-!
# Filling the runtime player table

The first row uses the root routing scale. After writing it, the loop
switches to the common scale used at every other depth.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def buildTopDepthPlayer (term scale rank degree log root inner j : ℕ) : BuildTopDepthInput where
  graphDir := 0
  replyDir := 0
  termBase := term
  childSize := 0
  branch := 0
  count := 0
  scale := scale
  rank := rank
  degree := degree
  pathLog := log
  coreLog := log
  denominator := if j = 0 then root else inner
  graphAddr := fun _ => 0
  graph := fun _ => ⟨0, []⟩

def buildTopPlayerTableLoopBody (write : ℕ) : Stmt :=
  .call 9 write [
    .bin .add (.reg 0) (.bin .mul (.const 7) (.reg 10)),
    .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 6, .reg 7] ;;
  .assign 7 (.reg 8)

/-- Arguments are table, row count, terminal table, scale, rank, degree, logarithm,
root router scale, and non-root router scale. -/
def buildTopPlayerTableLoop (write : ℕ) : Stmt :=
  forRange 10 (.const 0) (.reg 1) (buildTopPlayerTableLoopBody write) ;;
  .ret (.reg 0)

theorem buildTopPlayerTableLoop_noRand (write : ℕ) : (buildTopPlayerTableLoop write).NoRand := by
  simp [buildTopPlayerTableLoop, buildTopPlayerTableLoopBody, forRange, forUp, Stmt.NoRand]

private theorem playerTableStep {w f dst n term scale rank degree log root inner i : ℕ}
    {p : Program} {s : State}
    (hf : p.procs[f]? = some buildTopPlayerTableRow)
    (r0 : s.regs 0 = dst) (r2 : s.regs 2 = term) (r3 : s.regs 3 = scale)
    (r4 : s.regs 4 = rank) (r5 : s.regs 5 = degree) (r6 : s.regs 6 = log)
    (r7 : s.regs 7 = (buildTopDepthPlayer term scale rank degree log root inner i).denominator)
    (r8 : s.regs 8 = inner) (ri : s.regs 10 = i) (hi : i < n)
    (hroom : dst + 7 * n < 2 ^ w)
    (hwords : ∀ v ∈ (buildTopDepthPlayer term scale rank degree log root inner i).playerWords,
      v < 2 ^ w) :
    Triple w p (fun t => t = s) (buildTopPlayerTableLoopBody f)
      (normalPost fun t =>
        ListAt t.mem (dst + 7 * i)
          (buildTopDepthPlayer term scale rank degree log root inner i).playerWords ∧
        (∀ y, y < dst + 7 * i ∨ dst + 7 * i + 7 ≤ y → t.mem y = s.mem y) ∧
        t.regs 7 = inner ∧ ∀ r, r ≠ 7 → r ≠ 9 → t.regs r = s.regs r)
      (fun _ => 70) := by
  intro t ω rfl
  let D := buildTopDepthPlayer term scale rank degree log root inner i
  have h7 : 7 < 2 ^ w := by omega
  have hm : 7 * i < 2 ^ w := by omega
  have ha : dst + 7 * i < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopPlayerTableLoopBody
  refine runs_seq_call_le (buildTopPlayerTableRow_meetsContract (D := D) hf)
    (vs := (dst + 7 * i) :: D.playerWords) ?_ ?_ ⟨rfl,by omega⟩ ?_
  · have he := Expr.eval_add (Expr.eval_reg_of_eq r0)
      (Expr.eval_mul (Expr.eval_const h7) (Expr.eval_reg_of_eq ri) hm) ha
    simp only [evalArgs, he]
    simp [Expr.eval, r2,r3,r4,r5,r6,r7, D, BuildTopDepthInput.playerWords, buildTopDepthPlayer]
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · exact hwords _ hv
  intro v mem' pos' hpost
  refine runs_assign_le (v := inner) (Expr.eval_reg_of_eq (by simpa using r8)) ?_ ?_
  · refine ⟨hpost.2.1,hpost.2.2,by simp,?_⟩
    intro r h₇ h₉
    simp [Function.update_of_ne h₇, Function.update_of_ne h₉]
  · simp [Expr.size, argsSize]

/-- Write all player rows and preserve every address outside the table. -/
theorem buildTopPlayerTableLoop_runs {w write dst n term scale rank degree log root inner pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} (ω : ℕ → Bool)
    (hf : p.procs[write]? = some buildTopPlayerTableRow) (h1 : 1 < 2 ^ w)
    (hroom : dst + 7 * n < 2 ^ w)
    (hwords : ∀ i < n, ∀ v ∈ (buildTopDepthPlayer term scale rank degree log root inner i).playerWords,
      v < 2 ^ w) :
    ∃ t c, Runs w p ω (buildTopPlayerTableLoop write)
      (startState [dst,n,term,scale,rank,degree,log,root,inner] mem pos) (.returned dst) t c ∧
      (∀ i < n, ListAt t.mem (dst + 7 * i)
        (buildTopDepthPlayer term scale rank degree log root inner i).playerWords) ∧
      (∀ y, y < dst ∨ dst + 7 * n ≤ y → t.mem y = mem y) ∧ c ≤ 79 * n + 12 := by
  let D := buildTopDepthPlayer term scale rank degree log root inner
  let I := fun i (s : State) => (∀ j < i, ListAt s.mem (dst + 7 * j) (D j).playerWords) ∧
    ∀ y, y < dst ∨ dst + 7 * i ≤ y → s.mem y = mem y
  let J := fun i (s : State) => s.regs 0 = dst ∧ s.regs 1 = n ∧ s.regs 2 = term ∧
    s.regs 3 = scale ∧ s.regs 4 = rank ∧ s.regs 5 = degree ∧ s.regs 6 = log ∧
    s.regs 7 = (D i).denominator ∧ s.regs 8 = inner ∧ s.regs 10 = i ∧ I i s
  have hn : n < 2 ^ w := by omega
  have hl := Triple.forRange_le (p := p) (w := w) (r := 10)
    (lo := .const 0) (hi := .reg 1) (body := buildTopPlayerTableLoopBody write)
    (P := fun t => t = startState [dst,n,term,scale,rank,degree,log,root,inner] mem pos) (Inv := J)
    (fun _ => 70) 0 n (Nat.zero_le _) h1 (fun _ => hn)
    (fun t ht => by
      subst t
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by simp,
        fun j hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => by obtain ⟨_,_,_,_,_,_,_,_,_,hi,_⟩ := h; exact hi)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1) ?_
  · have hrun : ∃ o t c, Runs w p ω (buildTopPlayerTableLoop write)
        (startState [dst,n,term,scale,rank,degree,log,root,inner] mem pos) o t c ∧
        (o = .returned dst ∧ I n t) ∧ c ≤ 79 * n + 12 := by
      refine runs_start_le ?_
      unfold buildTopPlayerTableLoop
      refine runs_seq_triple_le hl rfl ?_
      intro t ⟨r0,_,_,_,_,_,_,_,_,_,hI⟩
      refine runs_ret_le (Expr.eval_reg_of_eq r0) ⟨rfl,hI⟩ ?_
      simp [Expr.size, rangeCost_const]
      omega
    obtain ⟨o,t,c,hr,⟨rfl,hI⟩,hc⟩ := hrun
    exact ⟨t,c,hr,hI.1,hI.2,hc⟩
  intro i _ hi s ω' ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,ri,hI⟩
  obtain ⟨o,t,c,hr,hpost,hc⟩ :=
    playerTableStep hf r0 r2 r3 r4 r5 r6 r7 r8 ri hi hroom (hwords i hi) s ω' rfl
  refine ⟨o,t,c,hr,?_,hc⟩
  cases o with
  | returned v => exact hpost.elim
  | normal =>
    obtain ⟨hrow,hframe,hinner,hregs⟩ := hpost
    refine ⟨⟨(hregs 0 (by decide) (by decide)).trans r0,
      (hregs 1 (by decide) (by decide)).trans r1, (hregs 2 (by decide) (by decide)).trans r2,
      (hregs 3 (by decide) (by decide)).trans r3, (hregs 4 (by decide) (by decide)).trans r4,
      (hregs 5 (by decide) (by decide)).trans r5, (hregs 6 (by decide) (by decide)).trans r6,
      by simpa [D,buildTopDepthPlayer] using hinner,
      (hregs 8 (by decide) (by decide)).trans r8, by simp, ?_, ?_⟩,
      (hregs 10 (by decide) (by decide)).trans ri⟩
    · intro j hj
      by_cases he : j = i
      · subst j
        exact hrow
      · have hj' : j < i := by omega
        intro k hk
        have hk' : k < 7 := by simpa [BuildTopDepthInput.playerWords] using hk
        rw [hframe _ (by omega)]
        exact hI.1 j hj' k hk
    · intro y hy
      exact (hframe y (by omega)).trans (hI.2 y (by omega))

/-- Package the table pass for use by the parameter setup procedure. -/
theorem buildTopPlayerTableLoop_meetsContract {w f write dst n term scale rank degree log root inner : ℕ}
    {p : Program}
    (hf : p.procs[f]? = some (buildTopPlayerTableLoop write))
    (hw : p.procs[write]? = some buildTopPlayerTableRow) :
    MeetsContract w p f {
      pre := fun args _ => args = [dst,n,term,scale,rank,degree,log,root,inner] ∧
        1 < 2 ^ w ∧ dst + 7 * n < 2 ^ w ∧
        ∀ i < n, ∀ v ∈ (buildTopDepthPlayer term scale rank degree log root inner i).playerWords,
          v < 2 ^ w
      post := fun _ mem v mem' => v = dst ∧
        (∀ i < n, ListAt mem' (dst + 7 * i)
          (buildTopDepthPlayer term scale rank degree log root inner i).playerWords) ∧
        ∀ y, y < dst ∨ dst + 7 * n ≤ y → mem' y = mem y
      cost := fun _ _ => 79 * n + 12 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hp => ?_
  obtain ⟨rfl,h1,hroom,hwords⟩ := hp
  obtain ⟨t,c,hr,ht,hframe,hc⟩ := buildTopPlayerTableLoop_runs ω hw h1 hroom hwords
  exact ⟨.returned dst,t,c,hr,⟨rfl,ht,hframe⟩,hc⟩

end MinCostFlow.HierPaths

end
