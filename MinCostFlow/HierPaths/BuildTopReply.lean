module

public import MinCostFlow.HierPaths.BuildTopModel
public import MinCostFlow.HierPaths.InitProgCSR

/-!
# Reading an encoded parent reply

A reply contains three compressed tables. Two offset reads locate a row
in the selected table. The same procedure reads child graphs, child
embeddings and sibling matchings.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def buildTopReplyRead (seek : ℕ) : Stmt :=
  .call 4 seek [.reg 0, .const 3, .reg 1] ;;
  .call 5 seek [.reg 4, .reg 2, .reg 3] ;;
  .ret (.reg 5)

theorem buildTopReplyRead_noRand (seek : ℕ) : (buildTopReplyRead seek).NoRand := by
  simp [buildTopReplyRead, Stmt.NoRand]

/-- Read the address of a row of a reply section. The last offset can also be read. -/
def buildTopReplyReadContract (w sec k i : ℕ) (rows : ℕ → List ℕ)
    (sections : List (List ℕ)) : Contract where
  pre args mem := ∃ addr, args = [addr, sec, k, i] ∧ sections.length = 3 ∧
    sec < 3 ∧ i ≤ k ∧ sections.getD sec [] = csrList k rows ∧
    ListAt mem addr (layoutList sections) ∧ addr + (layoutList sections).length < 2 ^ w
  post args mem v mem' :=
    let addr := args.getD 0 0
    let secAddr := initCSRAddr addr 3 (sections.getD · []) sec
    v = initCSRAddr secAddr k rows i ∧ mem' = mem
  cost _ _ := 42

theorem buildTopReplyRead_meetsContract {w f seek sec k i : ℕ}
    {rows : ℕ → List ℕ} {sections : List (List ℕ)} {p : Program}
    (hp : p.procs[f]? = some (buildTopReplyRead seek))
    (hs : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f (buildTopReplyReadContract w sec k i rows sections) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, rfl, hl, hsec, hi, he, hdata, hroom⟩ := hpre
  let F := (sections.getD · [])
  let a := initCSRAddr addr 3 F sec
  have hcsr : layoutList sections = csrList 3 F := by rw [layoutList, hl]
  rw [hcsr] at hdata hroom
  have h3 : 3 < 2 ^ w := by
    have hh := length_csrOffsets 3 F
    rw [csrList, List.length_append, hh] at hroom
    omega
  have hAt := initCSRAddr_listAt hdata hsec
  change ListAt mem a (sections.getD sec []) at hAt
  rw [he] at hAt
  have hbound : a + (csrList k rows).length < 2 ^ w := by
    have hh := initCSRAddr_le_end (addr := addr) (f := F) (k := 3) (i := sec + 1)
      (Nat.succ_le_of_lt hsec)
    rw [initCSRAddr_succ] at hh
    change a + (sections.getD sec []).length ≤ _ at hh
    rw [he] at hh
    exact hh.trans_lt hroom
  refine runs_start_le ?_
  unfold buildTopReplyRead
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := 3) (f := F) hs)
    (vs := [addr, 3, sec]) ?_ ?_ ⟨addr, sec, rfl, hsec.le, hdata, hroom⟩ ?_
  · simp [evalArgs, Expr.eval, startState, h3]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact h3
    · exact hsec.trans h3
  intro r mem₁ pos₁ hpost
  obtain ⟨hr, hm⟩ := hpost
  change r = a at hr
  change mem₁ = mem at hm
  subst r mem₁
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := k) (f := rows) hs)
    (vs := [a, k, i]) rfl ?_ ⟨a, i, rfl, hi, hAt, hbound⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · omega
    · exact hw _ (by simp)
    · exact hw _ (by simp)
  intro r mem₂ pos₂ hpost
  obtain ⟨hr, hm⟩ := hpost
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨hr, hm⟩ ?_
  simp [buildTopReplyReadContract, initCSRSeekContract, Expr.size, argsSize]

end MinCostFlow.HierPaths

end
