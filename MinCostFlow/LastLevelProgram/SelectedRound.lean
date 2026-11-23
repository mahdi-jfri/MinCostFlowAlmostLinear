module

public import MinCostFlow.LastLevelProgram.SelectTreeCall
public import MinCostFlow.LastLevelProgram.SelectedTraversal
import WordRAM.Tactic

/-!
# Tree selection and numeric update in one round

A round of Definition 5.8 (pages 19–20) selects a low-stretch tree,
uses the selected count to build its adjacency lists, and computes
the rounded stretches and next weights.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Pass the selector's return word to the numeric call, then return its
fresh memory pointer. -/
def selectedRoundBody (select numeric countReg resultReg : ℕ)
    (selectArgs numericArgs : List Expr) : Stmt :=
  .seq (.call countReg select selectArgs)
    (.seq (.call resultReg numeric numericArgs) (.ret (.reg resultReg)))

/-- The round wrapper uses ordinary calls and returns. -/
theorem selectedRoundBody_noRand (select numeric countReg resultReg : ℕ)
    (selectArgs numericArgs : List Expr) :
    (selectedRoundBody select numeric countReg resultReg selectArgs numericArgs).NoRand := by
  simp [selectedRoundBody, Stmt.NoRand]

/-- Forward the numeric arguments in register order. Register 22 holds
the retained edge count returned by the selector. -/
def selectedRoundNumericArgs : List Expr := (List.range 25).map Expr.reg

/-- Evaluating the numeric arguments forwards the live count in the
selected-array slot and all other arguments from the round's input. -/
theorem selectedRoundNumericArgs_eval (mem mid : ℕ → ℕ) (pos nextPos w count : ℕ)
    (adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      old stride denom stretchStride selected records adjTails adjHeads : ℕ) :
    let input := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
      old,stride,denom,stretchStride,selected,records,0,adjTails,adjHeads]
    let st := startState input mem pos
    evalArgs w {mem := mid, regs := Function.update st.regs 22 count, pos := nextPos}
      selectedRoundNumericArgs =
      some [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
        old,stride,denom,stretchStride,selected,records,count,adjTails,adjHeads] := by
  rfl

/-- The reserved count slot can be replaced by any fitting count
without changing the word bounds for the other arguments. -/
theorem selectedRound_count_words {w count : ℕ} (before after : List ℕ)
    (hinput : ∀ a ∈ before ++ [0] ++ after, a < 2^w)
    (hcount : count < 2^w) :
    ∀ a ∈ before ++ [count] ++ after, a < 2^w := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact hinput a (List.mem_append_left _ (List.mem_append_left _ ha))
    · simpa only [List.mem_singleton.mp ha] using hcount
  · exact hinput a (List.mem_append_right _ ha)

/-- The numeric forwarding has one register expression per argument. -/
theorem selectedRoundNumericArgs_cost : argsSize selectedRoundNumericArgs = 25 := by
  decide

/-- Sequence the two installed calls. The numeric contract can depend
on the selected count and list read from the output of the first call. -/
theorem selectedRound_runs {w select numeric countReg resultReg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {selectArgs numericArgs : List Expr} {sa : List ℕ} {C : Contract} {budget : ℕ}
    {result : ℕ → (ℕ → ℕ) → Prop}
    (hselect : MeetsContract w p select C)
    (hargs : evalArgs w st selectArgs = some sa)
    (hwords : ∀ a ∈ sa, a < 2^w) (hpre : C.pre sa st.mem)
    (hnext : ∀ count mem pos, C.post sa st.mem count mem →
      ∃ (D : Contract) (na : List ℕ), MeetsContract w p numeric D ∧
        evalArgs w {mem := mem, regs := Function.update st.regs countReg count, pos := pos}
          numericArgs = some na ∧
        (∀ a ∈ na, a < 2^w) ∧ D.pre na mem ∧ D.cost na mem ≤ budget ∧
        ∀ ret out, D.post na mem ret out → ret < 2^w ∧ result ret out) :
    ∃ o out cost, Runs w p ω
      (selectedRoundBody select numeric countReg resultReg selectArgs numericArgs) st o out cost ∧
      result o.value out.mem ∧
      cost ≤ argsSize selectArgs + C.cost sa st.mem + argsSize numericArgs + budget + 6 := by
  unfold selectedRoundBody
  apply runs_start_le
  refine runs_seq_call_le hselect hargs hwords hpre ?_
  intro count mid pos hp
  obtain ⟨D, na, hd, hna, hnwords, hnp, hcost, hret⟩ := hnext count mid pos hp
  refine runs_seq_call_le hd hna hnwords hnp ?_
  intro ret out _ hout
  obtain ⟨hfit, hresult⟩ := hret ret out hout
  refine runs_ret_le (v := ret) (by eval_expr) hresult ?_
  simp only [Expr.size]
  omega

/-- The round's selection arguments follow the numeric argument block.
The count placeholder is overwritten by selection before the numeric call. -/
def selectedRoundEntry (select numeric arity : ℕ) : Stmt :=
  selectedRoundBody select numeric 22 (25 + arity)
    ((List.range' 25 arity).map Expr.reg) selectedRoundNumericArgs

/-- The round forwards the appended selection arguments unchanged. -/
theorem selectedRoundEntry_selectArgs {w : ℕ} (input selection : List ℕ)
    (hLen : input.length = 25) (mem : ℕ → ℕ) (pos : ℕ) :
    evalArgs w (startState (input ++ selection) mem pos)
      ((List.range' 25 selection.length).map Expr.reg) = some selection := by
  apply evalArgs_registerRange
  intro i _
  change (input ++ selection).getD (25 + i) 0 = selection.getD i 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hLen]
  simp [List.getD_eq_getElem?_getD]

/-- A round with appended selection inputs still forwards the retained
count and all 24 other numeric arguments. -/
theorem selectedRoundEntry_numericArgs (mem mid : ℕ → ℕ) (pos nextPos w count : ℕ)
    (adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      old stride denom stretchStride selected records adjTails adjHeads : ℕ)
    (selection : List ℕ) :
    let input := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
      old,stride,denom,stretchStride,selected,records,0,adjTails,adjHeads]
    let st := startState (input ++ selection) mem pos
    evalArgs w {mem := mid, regs := Function.update st.regs 22 count, pos := nextPos}
      selectedRoundNumericArgs =
      some [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
        old,stride,denom,stretchStride,selected,records,count,adjTails,adjHeads] := by
  rfl

/-- The round entry uses no random instructions. -/
theorem selectedRoundEntry_noRand (select numeric arity : ℕ) :
    (selectedRoundEntry select numeric arity).NoRand :=
  selectedRoundBody_noRand _ _ _ _ _ _

/-- Run a selected-tree round with the concrete 25-word numeric
argument list. Only the retained count changes between the two calls. -/
theorem selectedRound_numeric_runs {w select numeric : ℕ} {p : Program} {ω : ℕ → Bool}
    {G T : MGraph} {base budget : ℕ} {C : Contract} {sa : List ℕ}
    {result : ℕ → (ℕ → ℕ) → Prop}
    (mem : ℕ → ℕ)
    (pos adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      old stride denom stretchStride selected records adjTails adjHeads : ℕ)
    (hselect : MeetsContract w p select C) :
    let before := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
      old,stride,denom,stretchStride,selected,records]
    let after := [adjTails,adjHeads]
    let st := startState ((before ++ [0] ++ after) ++ sa) mem pos
    (∀ a ∈ sa, a < 2^w) →
    (∀ a ∈ before ++ [0] ++ after, a < 2^w) → C.pre sa mem →
    (∀ k mid, C.post sa mem k mid → selectedTreeAt G T base selected k mem mid) →
    G.n < 2^w →
    (∀ count mid, selectedTreeAt G T base selected count mem mid →
      ∃ D : Contract, MeetsContract w p numeric D ∧
        D.pre (before ++ [count] ++ after) mid ∧ D.cost (before ++ [count] ++ after) mid ≤ budget ∧
        ∀ ret out, D.post (before ++ [count] ++ after) mid ret out → ret < 2^w ∧ result ret out) →
    ∃ o out cost, Runs w p ω
      (selectedRoundEntry select numeric sa.length) st o out cost ∧
      result o.value out.mem ∧ cost ≤ argsSize ((List.range' 25 sa.length).map Expr.reg) + C.cost sa mem + budget + 31 := by
  intro before after st hwords hinput hpre hpost hn hnext
  have hargs := selectedRoundEntry_selectArgs (w := w) (before ++ [0] ++ after) sa rfl mem pos
  have hrun := selectedRound_runs (ω := ω) (numeric := numeric) (resultReg := 25 + sa.length) (countReg := 22)
    (numericArgs := selectedRoundNumericArgs) (budget := budget) (result := result)
    hselect hargs hwords hpre
  obtain ⟨o, out, cost, hr, hres, hc⟩ := hrun (by
    intro count mid nextPos hg
    have htree := hpost count mid hg
    obtain ⟨D, hd, hdp, hcost, hret⟩ := hnext count mid htree
    obtain ⟨kept, hk, hsize, _⟩ := htree
    have hfit : count < 2^w := hk.symm ▸ hsize.trans_lt hn
    refine ⟨D, before ++ [count] ++ after, hd, ?_,
      selectedRound_count_words before after hinput hfit, hdp, hcost, hret⟩
    exact selectedRoundEntry_numericArgs mem mid pos nextPos w count adj parents edges depths queue
      r n levels dist lengths L heap tails heads P m old stride denom stretchStride selected
      records adjTails adjHeads sa)
  refine ⟨o, out, cost, hr, hres, ?_⟩
  rw [selectedRoundNumericArgs_cost] at hc
  change cost ≤ argsSize ((List.range' 25 sa.length).map Expr.reg) + C.cost sa mem + 25 + budget + 6 at hc
  omega

/-- Install the packed round entry with its numeric result predicate
and a separate memory premise for inputs preserved by selection. -/
theorem selectedRoundEntry_meetsContract {w entry select numeric : ℕ} {p : Program}
    {G T : MGraph} {base budget : ℕ} {C : Contract} {sa : List ℕ}
    {result : ℕ → (ℕ → ℕ) → Prop}
    (adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      old stride denom stretchStride selected records adjTails adjHeads : ℕ)
    (hselect : MeetsContract w p select C)
    (ready : (ℕ → ℕ) → Prop)
    (hp : p.procs[entry]? = some (selectedRoundEntry select numeric sa.length)) :
    let before := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,
      old,stride,denom,stretchStride,selected,records]
    let after := [adjTails,adjHeads]
    (∀ mem k mid, C.post sa mem k mid → selectedTreeAt G T base selected k mem mid) →
    G.n < 2^w →
    (∀ mem count mid, ready mem → selectedTreeAt G T base selected count mem mid →
      ∃ D : Contract, MeetsContract w p numeric D ∧
        D.pre (before ++ [count] ++ after) mid ∧ D.cost (before ++ [count] ++ after) mid ≤ budget ∧
        ∀ ret out, D.post (before ++ [count] ++ after) mid ret out → ret < 2^w ∧ result ret out) →
    MeetsContract w p entry {
      pre := fun args mem => args = (before ++ [0] ++ after) ++ sa ∧ C.pre sa mem ∧ ready mem
      post := fun _ _ ret out => result ret out
      cost := fun _ mem =>
        argsSize ((List.range' 25 sa.length).map Expr.reg) + C.cost sa mem + budget + 31 } := by
  intro before after hpost hn hnext
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨ha, hc, hready⟩ := hpre
  subst args
  obtain ⟨o, out, cost, hrun, hres, hcost⟩ :=
    selectedRound_numeric_runs (ω := ω) (numeric := numeric) mem pos adj parents edges depths queue
      r n levels dist lengths L heap tails heads P m old stride denom stretchStride selected
      records adjTails adjHeads hselect (fun a ha => hwords a (List.mem_append_right _ ha))
      (fun a ha => hwords a (List.mem_append_left _ ha)) hc (hpost mem) hn
      (fun count mid htree => hnext mem count mid hready htree)
  exact ⟨o, out, cost, hrun, hres, hcost⟩

/-- Forwarding a contiguous range of registers costs one per register. -/
theorem registerRange_argsSize (start count : ℕ) :
    argsSize ((List.range' start count).map Expr.reg) = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, List.map_cons]
    simp [argsSize, Expr.size, ih, Nat.add_comm]

/-- Forwarding to the selector and then to the relocated entry costs
twice the register bound plus the fixed argument slots of the calls. -/
theorem selectedRound_forwarding_cost (R : ℕ) (guest : List ℕ)
    (base modulus src len : ℕ) (localArgs : List ℕ) (hlocal : localArgs.length = 4) :
    let values := relocatedTreeArgs R guest base modulus src len
    argsSize ((List.range' 25 (localArgs ++ values).length).map Expr.reg) +
      argsSize ((List.range' 4 values.length).map Expr.reg) = 2 * R + 12 := by
  intro values
  rw [registerRange_argsSize, registerRange_argsSize, List.length_append, hlocal]
  have hv : values.length = R + 4 := by simp [values, relocatedTreeArgs]
  omega

end MinCostFlow.LastLevelProgram
