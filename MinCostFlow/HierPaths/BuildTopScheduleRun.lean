module

public import MinCostFlow.HierPaths.BuildTopScheduleRow
import WordRAM.Tactic

/-! # Building the schedule from the player words

Each row begins with a call to the complete row writer. The player words
are supplied in a separate table, which is preserved during the pass.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def BuildTopDepthInput.playerWords (D : BuildTopDepthInput) : List ℕ :=
  [D.termBase, D.scale, D.rank, D.degree, D.pathLog, D.coreLog, D.denominator]

def buildTopScheduleLoad (k : ℕ) : Expr :=
  .load (.bin .add (.reg 7) (.const k))

/-- Registers 6 and 7 hold the addresses of the current output and player rows. -/
def buildTopScheduleRunBody (write : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 2) (.bin .mul (.const 13) (.reg 5))) ;;
  .assign 7 (.bin .add (.reg 4) (.bin .mul (.const 7) (.reg 5))) ;;
  .call 8 write [.reg 6, buildTopScheduleLoad 0, buildTopScheduleLoad 1, buildTopScheduleLoad 2,
    buildTopScheduleLoad 3, buildTopScheduleLoad 4, buildTopScheduleLoad 5, buildTopScheduleLoad 6,
    .reg 0, .reg 1, .reg 5, .reg 2, .const 0, .reg 3]

/-- Arguments are the exponents, schedule address, depth count, and player-table address. -/
def buildTopScheduleRun (write : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 3) (buildTopScheduleRunBody write) ;;
  .ret (.reg 2)

theorem buildTopScheduleRun_noRand (write : ℕ) : (buildTopScheduleRun write).NoRand := by
  simp [buildTopScheduleRun, buildTopScheduleRunBody, forRange, forUp, Stmt.NoRand]

private theorem scheduleRunBody_triple {w write players geometry addresses x b table n src j : ℕ}
    {p : Program} {s : State} {D : BuildTopDepthInput}
    (hf : p.procs[write]? = some (buildTopScheduleRow players geometry addresses))
    (hp : p.procs[players]? = some buildTopSchedulePlayers)
    (hg : p.procs[geometry]? = some buildTopScheduleGeometry)
    (ha : p.procs[addresses]? = some buildTopScheduleAddresses)
    (hs : D.childSize = groupSize x b (j + 1))
    (hk : D.branch = branching x b j) (hn : D.count = numGroups x b j)
    (hd : D.replyDir = buildTopScheduleReplies table n x j)
    (rx : s.regs 0 = x) (rb : s.regs 1 = b) (rt : s.regs 2 = table) (rn : s.regs 3 = n)
    (rs : s.regs 4 = src) (rj : s.regs 5 = j)
    (hj : j < n) (hdepth : n ≤ leafDepth x b) (hb : 0 < b) (hbx : b ≤ x)
    (hP : 2 ^ x < 2 ^ w) (hend : buildTopScheduleEnd table n x < 2 ^ w)
    (hsrc : src + 7 * n < 2 ^ w) (hinput : ListAt s.mem (src + 7 * j) D.playerWords)
    (hwords : ∀ v ∈ D.playerWords, v < 2 ^ w) :
    Triple w p (fun t => t = s) (buildTopScheduleRunBody write)
      (normalPost fun t =>
        ListAt t.mem (table + 13 * j) (D.scheduleWords (buildTopSchedulePointer table n j)
          (buildTopSchedulePointer table n (j + 1))) ∧
        (∀ y, y < table + 13 * j ∨ table + 13 * j + 13 ≤ y → t.mem y = s.mem y) ∧
        ∀ r < 6, t.regs r = s.regs r) (fun _ => 380) := by
  intro t ω rfl
  obtain ⟨hrow,_,hrep,hspan⟩ := buildTopSchedule_disjoint (table := table) (x := x) (b := b) hj
  have hptr : buildTopSchedulePointer table n (j + 1) < 2 ^ w :=
    hrep.trans ((Nat.le_add_right _ _).trans_lt (hspan.trans_lt hend))
  have htable : table + 13 * n < 2 ^ w := by
    unfold buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer at hend
    omega
  have hr : table + 13 * j + 13 < 2 ^ w := by omega
  have h13 : 13 < 2 ^ w := by omega
  have h7 : 7 < 2 ^ w := by omega
  have hget (k : ℕ) (h : k < 7) :
      t.mem (src + 7 * j + k) = D.playerWords.getD k 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa [BuildTopDepthInput.playerWords] using h)]
    exact hinput k (by simpa [BuildTopDepthInput.playerWords] using h)
  have hcell (k : ℕ) (h : k < 7) : src + 7 * j + k < 2 ^ w := by omega
  have hsmall (k : ℕ) (h : k < 7) : k < 2 ^ w := h.trans h7
  suffices h : ∃ o u c, Runs w p ω (buildTopScheduleRunBody write) t o u c ∧
      normalPost (fun s' =>
        ListAt s'.mem (table + 13 * j) (D.scheduleWords (buildTopSchedulePointer table n j)
          (buildTopSchedulePointer table n (j + 1))) ∧
        (∀ y, y < table + 13 * j ∨ table + 13 * j + 13 ≤ y → s'.mem y = t.mem y) ∧
        ∀ r < 6, s'.regs r = t.regs r) o u ∧ 0 + c ≤ 380 by
    simpa only [Nat.zero_add] using h
  unfold buildTopScheduleRunBody
  refine runs_seq_assign_le (v := table + 13 * j)
    (Expr.eval_add (Expr.eval_reg_of_eq rt) (Expr.eval_mul (Expr.eval_const h13)
      (Expr.eval_reg_of_eq rj) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := src + 7 * j)
    (Expr.eval_add (Expr.eval_reg_of_eq rs) (Expr.eval_mul (Expr.eval_const h7)
      (Expr.eval_reg_of_eq rj) (by omega)) (by omega)) ?_
  let vs := [table + 13 * j,D.termBase,D.scale,D.rank,D.degree,D.pathLog,D.coreLog,
    D.denominator,x,b,j,table,0,n]
  refine runs_call_le (buildTopScheduleRow_meetsContract hf hp hg ha hs hk hn hd) (vs := vs)
    ?_ ?_ ⟨rfl,hj,hdepth,hb,hbx,hP,hend⟩ ?_
  · have hz : src + 7 * j < 2 ^ w := by omega
    have hm0 : t.mem (src + 7 * j) = D.termBase := by
      simpa [BuildTopDepthInput.playerWords] using hget 0 (by decide)
    simp (disch := decide) [evalArgs, Expr.eval, BinOp.eval, buildTopScheduleLoad, vs,
      hget, hcell, hsmall, BuildTopDepthInput.playerWords, List.getElem?_cons_zero,
      rx, rb, rt, rn, rj, hz, hm0]
  · have hx := x.lt_two_pow_self.trans hP
    have hv : ∀ v ∈ [x,b,j,table,0,n], v < 2 ^ w := by
      intro v h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx
      · exact hbx.trans_lt hx
      · omega
      · omega
      · exact Nat.two_pow_pos _
      · omega
    intro v h
    change v ∈ (table + 13 * j) :: (D.playerWords ++ [x,b,j,table,0,n]) at h
    rcases List.mem_cons.mp h with rfl | h
    · omega
    rcases List.mem_append.mp h with h | h
    · exact hwords _ h
    · exact hv _ h
  · intro v m pos h
    refine ⟨⟨h.2.1,h.2.2,?_⟩,?_⟩
    · intro r hr'
      simp [Function.update_of_ne (show r ≠ 8 by omega),
        Function.update_of_ne (show r ≠ 7 by omega), Function.update_of_ne (show r ≠ 6 by omega)]
    · simp [argsSize, Expr.size, buildTopScheduleLoad]

/-- Build every row from the disjoint player table, preserving the rest of memory. -/
theorem buildTopScheduleRun_runs {w write players geometry addresses x b table n src pos : ℕ}
    {p : Program} {D : ℕ → BuildTopDepthInput} {mem : ℕ → ℕ} (ω : ℕ → Bool)
    (hf : p.procs[write]? = some (buildTopScheduleRow players geometry addresses))
    (hp : p.procs[players]? = some buildTopSchedulePlayers)
    (hg : p.procs[geometry]? = some buildTopScheduleGeometry)
    (ha : p.procs[addresses]? = some buildTopScheduleAddresses)
    (hD : ∀ j < n, (D j).childSize = groupSize x b (j + 1) ∧
      (D j).branch = branching x b j ∧ (D j).count = numGroups x b j ∧
      (D j).replyDir = buildTopScheduleReplies table n x j)
    (hdepth : n ≤ leafDepth x b) (hb : 0 < b) (hbx : b ≤ x)
    (hP : 2 ^ x < 2 ^ w) (hend : buildTopScheduleEnd table n x < 2 ^ w)
    (hsrc : src + 7 * n < 2 ^ w) (hsep : src + 7 * n ≤ table ∨ table + 13 * n ≤ src)
    (hwords : ∀ j < n, ∀ v ∈ (D j).playerWords, v < 2 ^ w)
    (hinput : ∀ j < n, ListAt mem (src + 7 * j) (D j).playerWords) :
    ∃ t c, Runs w p ω (buildTopScheduleRun write)
      (startState [x,b,table,n,src] mem pos) (.returned table) t c ∧
      (∀ j < n, ListAt t.mem (table + 13 * j) ((D j).scheduleWords
        (buildTopSchedulePointer table n j) (buildTopSchedulePointer table n (j + 1)))) ∧
      (∀ y, y < table ∨ table + 13 * n ≤ y → t.mem y = mem y) ∧ c ≤ 389 * n + 12 := by
  let rows := fun j => (D j).scheduleWords (buildTopSchedulePointer table n j)
    (buildTopSchedulePointer table n (j + 1))
  let I := fun i (s : State) => (∀ j < i, ListAt s.mem (table + 13 * j) (rows j)) ∧
    ∀ y, y < table ∨ table + 13 * i ≤ y → s.mem y = mem y
  let J := fun i (s : State) => s.regs 0 = x ∧ s.regs 1 = b ∧ s.regs 2 = table ∧
    s.regs 3 = n ∧ s.regs 4 = src ∧ s.regs 5 = i ∧ I i s
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hP
  have hn : n < 2 ^ w := by omega
  have hloop := Triple.forRange_le (p := p) (w := w) (r := 5)
    (lo := .const 0) (hi := .reg 3) (body := buildTopScheduleRunBody write)
    (P := fun t => t = startState [x,b,table,n,src] mem pos) (Inv := J)
    (fun _ => 380) 0 n (Nat.zero_le _) h1 (fun _ => hn)
    (fun t ht => by
      subst t
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, rfl, rfl, rfl, by simp,
        fun j hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.1) ?_
  · have hrun : ∃ o t c, Runs w p ω (buildTopScheduleRun write)
        (startState [x,b,table,n,src] mem pos) o t c ∧
        (o = .returned table ∧ I n t) ∧ c ≤ 389 * n + 12 := by
      refine runs_start_le ?_
      unfold buildTopScheduleRun
      refine runs_seq_triple_le hloop rfl ?_
      intro t ⟨_,_,ht,_,_,_,hI⟩
      refine runs_ret_le (Expr.eval_reg_of_eq ht) ⟨rfl,hI⟩ ?_
      simp [Expr.size, rangeCost_const]
      omega
    obtain ⟨o,t,c,hr,⟨rfl,hI⟩,hc⟩ := hrun
    exact ⟨t,c,hr,hI.1,hI.2,hc⟩
  intro i _ hi s ω' ⟨rx,rb,rt,rn,rs,ri,hI⟩
  obtain ⟨hS,hk,hN,hd⟩ := hD i hi
  have htable : ListAt s.mem (src + 7 * i) (D i).playerWords := by
    intro k hk
    have hk' : k < 7 := by simpa [BuildTopDepthInput.playerWords] using hk
    rw [hI.2 _ (by rcases hsep with h | h <;> omega)]
    exact hinput i hi k hk
  obtain ⟨o,t,c,hr,hp',hc⟩ :=
    scheduleRunBody_triple hf hp hg ha hS hk hN hd rx rb rt rn rs ri hi hdepth hb hbx
      hP hend hsrc htable (hwords i hi) s ω' rfl
  refine ⟨o,t,c,hr,?_,hc⟩
  cases o with
  | returned v => exact hp'.elim
  | normal =>
    obtain ⟨hrow,hframe,hregs⟩ := hp'
    refine ⟨⟨(hregs 0 (by decide)).trans rx, (hregs 1 (by decide)).trans rb,
      (hregs 2 (by decide)).trans rt, (hregs 3 (by decide)).trans rn,
      (hregs 4 (by decide)).trans rs, by simp, ?_, ?_⟩, (hregs 5 (by decide)).trans ri⟩
    · intro j hj
      by_cases he : j = i
      · subst j
        exact hrow
      · have hj' : j < i := by omega
        intro k hk
        have hk' : k < 13 := by simpa [rows, BuildTopDepthInput.scheduleWords] using hk
        rw [hframe _ (by omega)]
        exact hI.1 j hj' k hk
    · intro y hy
      exact (hframe y (by omega)).trans (hI.2 y (by omega))

end MinCostFlow.HierPaths

end
