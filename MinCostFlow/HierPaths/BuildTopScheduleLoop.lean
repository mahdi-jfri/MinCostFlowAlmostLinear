module

public import MinCostFlow.HierPaths.BuildTopScheduleWrite
import WordRAM.Tactic

/-! # Filling the geometry columns of the depth schedule -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The three geometry cells begin at column three in each thirteen-word row. -/
def buildTopScheduleCell (table j : ℕ) : ℕ := table + 13 * j + 3

/-- Call the geometry writer for one row. -/
def buildTopScheduleLoopBody (write : ℕ) : Stmt :=
  .call 5 write [.reg 0, .reg 1, .reg 4,
    .bin .add (.bin .add (.reg 2) (.bin .mul (.const 13) (.reg 4))) (.const 3)]

/-- Arguments are the root exponent, branching exponent, table, and row count. -/
def buildTopScheduleLoop (write : ℕ) : Stmt :=
  forRange 4 (.const 0) (.reg 3) (buildTopScheduleLoopBody write) ;;
  .ret (.reg 2)

theorem buildTopScheduleLoop_noRand (write : ℕ) : (buildTopScheduleLoop write).NoRand := by
  simp [buildTopScheduleLoop, buildTopScheduleLoopBody, forRange, forUp, Stmt.NoRand]

private def geometryUpdates (x b table j : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let dst := buildTopScheduleCell table j
  Function.update (Function.update (Function.update mem dst (groupSize x b (j + 1)))
    (dst + 1) (branching x b j)) (dst + 2) (numGroups x b j)

private theorem geometryStep_triple {w write x b table j : ℕ} {p : Program} {s : State}
    (hf : p.procs[write]? = some buildTopScheduleGeometry)
    (rx : s.regs 0 = x) (rb : s.regs 1 = b) (rt : s.regs 2 = table) (rj : s.regs 4 = j)
    (hw : 2 ^ x < 2 ^ w) (hb : b ≤ x)
    (hj : j + 1 < 2 ^ w) (hm : (j + 1) * b < 2 ^ w)
    (ht : table + 13 * j + 13 < 2 ^ w) :
    Triple w p (fun t => t = s) (buildTopScheduleLoopBody write)
      (normalPost fun t => t.mem = geometryUpdates x b table j s.mem ∧
        ∀ r, r ≠ 5 → t.regs r = s.regs r) (fun _ => 112) := by
  intro t ω rfl
  have h13 : 13 < 2 ^ w := by omega
  have hmul : 13 * j < 2 ^ w := by omega
  have ha : table + 13 * j < 2 ^ w := by omega
  have hd : buildTopScheduleCell table j + 2 < 2 ^ w := by
    unfold buildTopScheduleCell
    omega
  have hx := x.lt_two_pow_self.trans hw
  change ∃ o t' c, Runs w p ω (buildTopScheduleLoopBody write) t o t' c ∧
    normalPost (fun u => u.mem = geometryUpdates x b table j t.mem ∧
      ∀ r, r ≠ 5 → u.regs r = t.regs r) o t' ∧ c ≤ 112
  suffices h : ∃ o t' c, Runs w p ω (buildTopScheduleLoopBody write) t o t' c ∧
      normalPost (fun u => u.mem = geometryUpdates x b table j t.mem ∧
        ∀ r, r ≠ 5 → u.regs r = t.regs r) o t' ∧ 0 + c ≤ 112 by
    simpa only [Nat.zero_add] using h
  unfold buildTopScheduleLoopBody
  refine runs_call_le (buildTopScheduleGeometry_meetsContract hf)
    (k := 0) (vs := [x, b, j, buildTopScheduleCell table j]) ?_ ?_ ⟨rfl,hw,hj,hm,hd⟩ ?_
  · have hdst := Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq rt)
        (Expr.eval_mul (Expr.eval_const h13) (Expr.eval_reg_of_eq rj) hmul) ha)
      (Expr.eval_const (show 3 < 2 ^ w by omega))
      (show table + 13 * j + 3 < 2 ^ w by omega)
    simp only [evalArgs, hdst, buildTopScheduleCell]
    simp [Expr.eval, rx, rb, rj]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hx
    · exact hb.trans_lt hx
    · omega
    · omega
  · intro v mem' pos' hp
    exact ⟨⟨hp.2, fun r hr => Function.update_of_ne hr _ _⟩, by
      simp [argsSize, Expr.size]⟩

/-- The initialized prefix contains precisely the three geometric words of each row. -/
def BuildTopScheduleGeometryAt (mem : ℕ → ℕ) (x b table n : ℕ) : Prop :=
  ∀ j < n, mem (buildTopScheduleCell table j) = groupSize x b (j + 1) ∧
    mem (buildTopScheduleCell table j + 1) = branching x b j ∧
    mem (buildTopScheduleCell table j + 2) = numGroups x b j

private theorem geometryUpdates_prefix {x b table i : ℕ} {mem : ℕ → ℕ}
    (h : BuildTopScheduleGeometryAt mem x b table i) :
    BuildTopScheduleGeometryAt (geometryUpdates x b table i mem) x b table (i + 1) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simp [geometryUpdates, Function.update_of_ne]
  · have hj' : j < i := by omega
    obtain ⟨ha, hb, hc⟩ := h j hj'
    have hkeep (k : ℕ) (hk : k ≤ 2) :
        geometryUpdates x b table i mem (buildTopScheduleCell table j + k) =
          mem (buildTopScheduleCell table j + k) := by
      have hlt : buildTopScheduleCell table j + k < buildTopScheduleCell table i := by
        unfold buildTopScheduleCell
        omega
      unfold geometryUpdates
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    exact ⟨(by simpa using (hkeep 0 (by decide)).trans ha : _),
      (hkeep 1 (by decide)).trans hb, (hkeep 2 (by decide)).trans hc⟩

/-- Outside the geometry columns of the scheduled rows, the previous contents are preserved. -/
def BuildTopScheduleGeometryFrame (mem mem' : ℕ → ℕ) (table n : ℕ) : Prop :=
  ∀ y, (∀ j < n, y < buildTopScheduleCell table j ∨ buildTopScheduleCell table j + 3 ≤ y) →
    mem' y = mem y

private theorem geometryUpdates_frame {x b table i : ℕ} {mem mem' : ℕ → ℕ}
    (hf : BuildTopScheduleGeometryFrame mem mem' table i) :
    BuildTopScheduleGeometryFrame mem (geometryUpdates x b table i mem') table (i + 1) := by
  intro y hy
  have hout := hy i (Nat.lt_succ_self i)
  unfold geometryUpdates
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]
  exact hf y fun j hj => hy j (hj.trans (Nat.lt_succ_self i))

/-- Fill the geometry columns of every active depth in linear time in the depth count. -/
theorem buildTopScheduleLoop_runs {w write x b table count pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} (ω : ℕ → Bool)
    (hf : p.procs[write]? = some buildTopScheduleGeometry)
    (hb : 0 < b) (hbx : b ≤ x) (hw : 2 ^ x < 2 ^ w)
    (hn : count ≤ leafDepth x b) (ht : table + 13 * count < 2 ^ w) :
    ∃ t c, Runs w p ω (buildTopScheduleLoop write)
      (startState [x,b,table,count] mem pos) (.returned table) t c ∧
      BuildTopScheduleGeometryAt t.mem x b table count ∧
      BuildTopScheduleGeometryFrame mem t.mem table count ∧ c ≤ 121 * count + 12 := by
  let J := fun i (s : State) => s.regs 0 = x ∧ s.regs 1 = b ∧ s.regs 2 = table ∧
    s.regs 3 = count ∧ s.regs 4 = i ∧ BuildTopScheduleGeometryAt s.mem x b table i ∧
    BuildTopScheduleGeometryFrame mem s.mem table i
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hw
  have hcount : count < 2 ^ w := by omega
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 4) (lo := .const 0)
    (hi := .reg 3) (body := buildTopScheduleLoopBody write)
    (P := fun t => t = startState [x,b,table,count] mem pos) (Inv := J)
    (fun _ => 112) 0 count (Nat.zero_le _) h1 (fun _ => hcount)
    (fun t ht => by
      subst t
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, rfl, rfl, by simp,
        fun j hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.1) ?_
  · have hr : ∃ o t c, Runs w p ω (buildTopScheduleLoop write)
        (startState [x,b,table,count] mem pos) o t c ∧
        (o = .returned table ∧ BuildTopScheduleGeometryAt t.mem x b table count ∧
          BuildTopScheduleGeometryFrame mem t.mem table count) ∧
        c ≤ 121 * count + 12 := by
      refine runs_start_le ?_
      unfold buildTopScheduleLoop
      refine runs_seq_triple_le hloop rfl ?_
      intro t ⟨_,_,hTable,_,_,hgeom,hframe⟩
      refine runs_ret_le (Expr.eval_reg_of_eq hTable) ⟨rfl,hgeom,hframe⟩ ?_
      simp [Expr.size, rangeCost_const]
      omega
    obtain ⟨o,t,c,hr,⟨rfl,hg,hf'⟩,hc⟩ := hr
    exact ⟨t,c,hr,hg,hf',hc⟩
  intro i _ hi s ω' ⟨rx,rb,rt,rn,ri,hgeom,hframe⟩
  obtain ⟨hj,hm⟩ := (buildTopScheduleWords_fit hb hbx hw).2 i (hi.trans_le hn)
  obtain ⟨o,t,c,hr,hp,hc⟩ :=
    geometryStep_triple hf rx rb rt ri hw hbx hj hm (by omega) s ω' rfl
  refine ⟨o,t,c,hr,?_,hc⟩
  cases o with
  | returned v => exact hp.elim
  | normal =>
    obtain ⟨hmem,hreg⟩ := hp
    exact ⟨⟨(hreg 0 (by decide)).trans rx, (hreg 1 (by decide)).trans rb,
      (hreg 2 (by decide)).trans rt, (hreg 3 (by decide)).trans rn, by simp,
      hmem ▸ geometryUpdates_prefix hgeom, hmem ▸ geometryUpdates_frame hframe⟩, (hreg 4 (by decide)).trans ri⟩

end MinCostFlow.HierPaths

end
