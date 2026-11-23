module

public import MinCostFlow.MinRatio.DetectSlotStep
public import MinCostFlow.MinRatio.DetectTreeReset
import WordRAM.Tactic

/-!
# Reporting and resetting one ready tree slot

The proof of Theorem 5.1 (pages 29–30) reports each ready edge and
resets its absolute flow account. The report append also prepares
the replacement record, which PointWrite installs in the same slot.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LinkCut

/-- Append the external name, then install the reset record. The
registers hold the handle, name tables, slot, cursor, old record,
threshold, limb count, and heap in that order. -/
@[expose] def detectTreeReportBody (prepare write : ℕ) : Stmt :=
  .call 9 prepare [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
  .call 10 write [.reg 0, .reg 3, .reg 8, .reg 9] ;;
  .ret (.reg 10)

/-- The reporting step contains no random statements. -/
theorem detectTreeReportBody_noRand (prepare write : ℕ) :
    (detectTreeReportBody prepare write).NoRand := by
  simp [detectTreeReportBody, Stmt.NoRand]

/-- The append and point write produce the extended report and the
exact updated tree within the amortized budget of one point write. -/
theorem detectTreeReport_runs {w L constant init handle names inv slot cursor src th heap pos
    prepare report : ℕ}
    {fmt : Num.Format w} {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {edge : PathEdgeValue} {threshold : ℤ}
    (written : List ℕ)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hp : MeetsContract w p prepare (detectSlotStepContract w fmt.limbBits report written edge threshold))
    (hw : ∀ a ∈ [handle, names, inv, slot, cursor, src, th, L, heap], a < 2 ^ w)
    (hpre : (detectSlotStepContract w fmt.limbBits report written edge threshold).pre
      [names, inv, slot, cursor, src, th, L, heap] mem)
    (hrep : R.rep handle s x mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hcursor : ¬ R.foot handle x cursor)
    (hreport : ∀ a, report ≤ a → a < report + written.length + 1 → a < heap ∧ ¬ R.foot handle x a)
    (hwrite : ∀ mem', PathEdgeAt mem' heap fmt.limbBits L (some { edge with detector := -threshold }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 s
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w) :
    ∃ (ret cost : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectTreeReportBody prepare (op 5))
        (startState [handle, names, inv, slot, cursor, src, th, L, heap] mem pos)
        (.returned ret) out cost ∧
      R.rep handle (pathTreeWrite s slot (some { edge with detector := -threshold })) y out.mem ∧
      ListAt out.mem report (written ++ [mem (inv + mem (names + slot))]) ∧
      ZeroFrom out.mem ret ∧ heap + (2 + 4 * L) ≤ ret ∧
      ret ≤ heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ cursor → out.mem a = mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle x a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + R.phi handle y out.mem ≤
        pathTreeBudget constant L s.n + R.phi handle x mem + 87 * L + 162 := by
  let st := startState [handle, names, inv, slot, cursor, src, th, L, heap] mem pos
  obtain ⟨mid, c, ptr, hrun, hpost, hreg, hother, hc⟩ :=
    runs_call_of_meetsContract (st := st) (r := 9)
      (args := [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8])
      (vs := [names, inv, slot, cursor, src, th, L, heap])
      hp (by simp [evalArgs, Expr.eval, st, startState])
      (fun a ha => hw a (List.mem_cons_of_mem _ ha)) hpre ω
  obtain ⟨_, _, _, _, _, _, _, _, heq, hptr, hlist, hrecord, hframe, hzero⟩ := hpost
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hpw : ptr < 2 ^ w := by omega
  have hlocal : ∀ a, R.foot handle x a → mem a = mid.mem a := by
    intro a ha
    exact (hframe a (hfoot a ha) (fun h => hcursor (h ▸ ha))).symm
  obtain ⟨hrep₁, hphi⟩ := himpl.1 handle s x mem mid.mem hlocal
  obtain ⟨s', c', after, y, ret, hcall, hrep', hpost, hm, hcost⟩ :=
    pathTree_runs_call (i := 5) (reg := 10) (st := mid) (ω := ω)
      (args := [.reg 0, .reg 3, .reg 8, .reg 9]) (vs := [handle, slot, heap, ptr])
      himpl (by simp [evalArgs, Expr.eval, hother, hreg, st, startState])
      (by have h₀ := hw handle (by simp); have h₁ := hw slot (by simp)
          have h₂ := hw heap (by simp); wram_words)
      rfl (hrep₁ hrep) (hptr.symm ▸ hwrite mid.mem hrecord)
      (fun a ha => by have := hfoot a ha; change a < ptr; omega) hzero (by
        change ptr + allocation 5 s.n [handle, slot, heap, ptr] < 2 ^ w
        rwa [hptr])
  change s' = pathTreeWrite s slot (readPathEdge mid.mem heap fmt.limbBits L) at hpost
  rw [readPathEdge_eq hrecord] at hpost
  rw [hpost] at hrep'
  let out := { after with regs := Function.update mid.regs 10 ret }
  have hret : Runs w p ω (.ret (.reg 10)) out (.returned ret) out 2 :=
    runs_ret_iff.mpr ⟨ret, by simp [Expr.eval, out], rfl, rfl, rfl⟩
  have hlist' := hlist.congr (mem' := after.mem) (fun a ha hb => by
    rw [List.length_append, List.length_singleton] at hb
    obtain ⟨hbelow, houtside⟩ := hreport a ha hb
    exact hm.2.2.2.1 a (by change a < ptr; omega) houtside)
  refine ⟨ret, c + (c' + 2 + 1) + 1, out, y, ?_, hrep', hlist', hm.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hrun,
      runs_seq_iff.mpr (Or.inr ⟨out, c', 2, hcall, hret, rfl⟩), rfl⟩)
  · have hlo : ptr ≤ ret := hm.1
    omega
  · have hhi : ret ≤ ptr + allocation 5 s.n [handle, slot, heap, ptr] := hm.2.1
    rwa [hptr] at hhi
  · intro a ha hnot hne
    exact (hm.2.2.2.1 a (by change a < ptr; omega) hnot).trans (hframe a ha hne)
  · intro a ha
    rcases hm.2.2.2.2 a ha with hold | ⟨hlo, hhi⟩
    · exact Or.inl hold
    · change ptr ≤ a at hlo
      exact Or.inr ⟨by omega, hhi⟩
  · simp [detectSlotStepContract, argsSize, Expr.size] at hc
    change c' + R.phi handle y after.mem ≤
      pathTreeBudget constant L s.n + R.phi handle x mid.mem + 5 at hcost
    change c + (c' + 2 + 1) + 1 + R.phi handle y after.mem ≤ _
    rw [← hphi] at hcost
    omega

/-- Call the report body using the registers left by search and read.
The caller supplies the report tables, cursor, threshold and workspace. -/
@[expose] def detectTreeReportCall (entry : ℕ) : Stmt :=
  .call 12 entry [.reg 0, .reg 6, .reg 7, .reg 3, .reg 8, .reg 4, .reg 9, .reg 10, .reg 11]

/-- The report call preserves all caller registers except the returned
heap in register 12, and retains the footprint and potential bounds. -/
theorem detectTreeReport_call {w L constant init handle names inv slot cursor src th heap
    prepare report entry : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {edge : PathEdgeValue} {threshold : ℤ}
    (written : List ℕ)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hregs : st.regs 0 = handle ∧ st.regs 6 = names ∧ st.regs 7 = inv ∧ st.regs 3 = slot ∧
      st.regs 8 = cursor ∧ st.regs 4 = src ∧ st.regs 9 = th ∧ st.regs 10 = L ∧ st.regs 11 = heap)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hp : MeetsContract w p prepare (detectSlotStepContract w fmt.limbBits report written edge threshold))
    (hw : ∀ a ∈ [handle, names, inv, slot, cursor, src, th, L, heap], a < 2 ^ w)
    (hpre : (detectSlotStepContract w fmt.limbBits report written edge threshold).pre
      [names, inv, slot, cursor, src, th, L, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hcursor : ¬ R.foot handle x cursor)
    (hreport : ∀ a, report ≤ a → a < report + written.length + 1 → a < heap ∧ ¬ R.foot handle x a)
    (hwrite : ∀ mem', PathEdgeAt mem' heap fmt.limbBits L (some { edge with detector := -threshold }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 s
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w) :
    ∃ (ret cost : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectTreeReportCall entry) st .normal out cost ∧ out.regs 12 = ret ∧
      (∀ r, r ≠ 12 → out.regs r = st.regs r) ∧
      R.rep handle (pathTreeWrite s slot (some { edge with detector := -threshold })) y out.mem ∧
      ListAt out.mem report (written ++ [st.mem (inv + st.mem (names + slot))]) ∧
      ZeroFrom out.mem ret ∧ heap + (2 + 4 * L) ≤ ret ∧
      ret ≤ heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ cursor → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle x a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + R.phi handle y out.mem ≤
        pathTreeBudget constant L s.n + R.phi handle x st.mem + 87 * L + 172 := by
  obtain ⟨h₀, h₆, h₇, h₃, h₈, h₄, h₉, h₁₀, h₁₁⟩ := hregs
  obtain ⟨ret, c, after, y, hrun, hrest⟩ := detectTreeReport_runs (pos := st.pos) (ω := ω)
    written himpl hp hw hpre hrep hfoot hcursor hreport hwrite hroom
  let out := { after with regs := Function.update st.regs 12 ret }
  have hcall : Runs w p ω (detectTreeReportCall entry) st .normal out (c + 10) := by
    refine runs_call_iff.mpr ⟨[handle, names, inv, slot, cursor, src, th, L, heap],
      _, .returned ret, after, c, ?_, hentry, hrun, rfl, rfl, ?_⟩
    · simp [evalArgs, Expr.eval, h₀, h₆, h₇, h₃, h₈, h₄, h₉, h₁₀, h₁₁]
    · simp [argsSize, Expr.size]
      omega
  obtain ⟨hy, hl, hz, hlo, hhi, hf, hft, hc⟩ := hrest
  exact ⟨ret, c + 10, out, y, hcall, by simp [out],
    fun r hr => Function.update_of_ne hr _ _, hy, hl, hz, hlo, hhi, hf, hft, by
      change c + 10 + R.phi handle y after.mem ≤ _
      omega⟩

end MinCostFlow.MinRatio
