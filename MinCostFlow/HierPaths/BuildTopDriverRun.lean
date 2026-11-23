module

public import MinCostFlow.HierPaths.BuildTopDriver
public import MinCostFlow.HierPaths.InitProgCSR

/-!
# Cost and correctness of the depth schedule

The driver consumes a memory-resident schedule. At each depth the
invariant supplies that depth's input layout and receives its reply
from the verified advance procedure.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Execute a schedule whose graph inputs are discovered from previous replies. -/
theorem buildTopDriver_runs {w K advance table count heap pos : ℕ} {p : Program}
    {mem : ℕ → ℕ} {inCell outCell rate : ℕ → ℕ}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {I : ℕ → ℕ → (ℕ → ℕ) → Prop} (ω : ℕ → Bool)
    (hn : count < 2 ^ w) (h1 : 1 < 2 ^ w)
    (hroom : table + 13 * count < 2 ^ w) (hinit : I 0 heap mem)
    (ha : ∀ D : BuildTopDepthInput, MeetsContract w p advance (D.advanceContract w K space))
    (hready : ∀ i < count, ∀ h m, I i h m →
      ∃ D : BuildTopDepthInput,
        ListAt m (table + 13 * i) (D.scheduleWords (inCell i) (outCell i)) ∧
        m (inCell i) = D.graphDir ∧
        (∀ v ∈ D.args h ++ [outCell i], v < 2 ^ w) ∧
        (D.advanceContract w K space).pre (D.args h ++ [outCell i]) m ∧
        (D.advanceContract w K space).cost (D.args h ++ [outCell i]) m + 62 ≤ rate i ∧
        (∀ v m', (D.advanceContract w K space).post (D.args h ++ [outCell i]) m v m' →
          I (i + 1) v m')) :
    ∃ v t c, Runs w p ω (buildTopDriver advance) (startState [table, count, heap] mem pos)
      (.returned v) t c ∧ I count v t.mem ∧
      c ≤ rangeCost rate 0 count + 9 * count + 12 := by
  let J := fun i (s : State) => s.regs 0 = table ∧ s.regs 1 = count ∧ s.regs 3 = i ∧
    I i (s.regs 2) s.mem
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 3) (lo := .const 0)
    (hi := .reg 1) (body := buildTopDriverBody advance)
    (P := fun t => t = startState [table, count, heap] mem pos) (Inv := J)
    rate 0 count (Nat.zero_le _) h1 (fun _ => hn)
    (fun t ht => by subst t; exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, by simp, hinit⟩)
    (fun _ _ _ _ hi => hi.2.2.1)
    (fun _ _ _ _ hi => Expr.eval_reg_of_eq hi.2.1) ?_
  · have hRun : ∃ o t c, Runs w p ω (buildTopDriver advance)
        (startState [table, count, heap] mem pos) o t c ∧
        (o = .returned (t.regs 2) ∧ I count (t.regs 2) t.mem) ∧
        c ≤ rangeCost rate 0 count + 9 * count + 12 := by
      refine runs_start_le ?_
      unfold buildTopDriver
      refine runs_seq_triple_le hloop rfl ?_
      intro t ⟨_, _, _, hI⟩
      refine runs_ret_le (v := t.regs 2) (Expr.eval_reg_of_eq rfl) ⟨rfl, hI⟩ ?_
      simp [Expr.size]
      omega
    obtain ⟨o, t, c, hr, ⟨ho, hI⟩, hc⟩ := hRun
    exact ⟨t.regs 2, t, c, ho ▸ hr, hI, hc⟩
  intro i _ hi s ω' ⟨r0,r1,r3,hI⟩
  obtain ⟨D, hrow, hin, hw, hp, hrate, hnext⟩ := hready i hi _ _ hI
  have hslot : table + 13 * i + 13 < 2 ^ w := by omega
  obtain ⟨o,t,c,hr,hpost,hcost⟩ :=
    buildTopDriverBody_triple (ha D) r0 rfl r3 hslot hrow hin hw hp s ω' rfl
  refine ⟨o,t,c,hr,?_,?_⟩
  · cases o with
    | returned v => exact hpost.elim
    | normal =>
      obtain ⟨hregs,hpost⟩ := hpost
      refine ⟨⟨?_, ?_, by simp, ?_⟩, (hregs _ (by decide) (by decide)).trans r3⟩
      · simpa using (hregs _ (by decide) (by decide)).trans r0
      · simpa using (hregs _ (by decide) (by decide)).trans r1
      · exact hnext _ _ hpost
  · exact hcost.trans hrate

/-- The same assembled advance serves every depth and every certified parent graph. -/
theorem buildTopAdvance_from_level {w K advance depth call level next row read seek : ℕ}
    {p : Program}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (ha : p.procs[advance]? = some (buildTopAdvance depth next))
    (hd : p.procs[depth]? = some (buildTopDepth call))
    (hc : p.procs[call]? = some (buildTopParentCall level))
    (hl : ProvidesBuildLevel w K space p level)
    (hn : p.procs[next]? = some (buildTopNextDir row))
    (hr : p.procs[row]? = some (buildTopNextRow read))
    (hp : p.procs[read]? = some (buildTopReplyRead seek))
    (hs : p.procs[seek]? = some initCSRSeek) :
    ∀ D : BuildTopDepthInput, MeetsContract w p advance (D.advanceContract w K space) := by
  intro D
  exact buildTopAdvance_meetsContract ha (buildTopDepth_meetsContract hd hc hl)
    (fun _ _ => buildTopNextDir_meetsContract hn hr hp hs)

end MinCostFlow.HierPaths

end
