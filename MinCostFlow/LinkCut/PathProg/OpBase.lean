module

public import MinCostFlow.LinkCut.PathProg.Account
public import MinCostFlow.LinkCut.PathProg.WrapQuery

/-!
# What each operation must show

`OpDone` is the conclusion that `DSRep.Implements` asks of operation `i`, for the contract
`pathContract fmt L` and the representation `pathRep`. The lemma `opDone_of` builds it from the
run of a wrapper: the new arena, the kept facts `StateOk`, the frame of the call and the cost
bound.

The rest of the file states the potential bounds of the model for each operation in the form
the cost proofs use (`expose_pot`, `summary_pot`, `apply_pot`, `link_pot`, `cut_pot`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

/-- The contract that the program implements. -/
noncomputable abbrev pathContract {w : ℕ} (fmt : Format w) (L : ℕ) :
    DataStructure PathTreeState :=
  pathTreeMachineContract fmt L pathC (pathAlloc L)

/-- What `DSRep.Implements` asks of a call of operation `i` on the state `s` kept as `(s, S)`
at handle `b`. -/
def OpDone {w : ℕ} (p : Program) (fmt : Format w) (L b0 i b : ℕ) (s : PathTreeState)
    (S : List ℕ) (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) : Prop :=
  ∃ body, p.procs[b0 + 1 + i]? = some body ∧ ∃ o st' c,
    Runs w p ω body (startState args mem pos) o st' c ∧ ∃ s' x',
      (pathRep fmt.limbBits L pathC).rep b s' x' st'.mem ∧
      (pathContract fmt L).post i s args mem s' st'.mem ∧
      (pathRep fmt.limbBits L pathC).Respects ((pathRep fmt.limbBits L pathC).foot b (s, S))
        (heapArg args) ((pathContract fmt L).space i s args mem) mem o.value b x' st'.mem ∧
      c + (pathRep fmt.limbBits L pathC).phi b x' st'.mem ≤
        (pathContract fmt L).cost i s args mem + (pathRep fmt.limbBits L pathC).phi b (s, S) mem

/-- An operation is done when its wrapper runs to a new arena, keeps `StateOk`, keeps the size,
meets the postcondition, stays in its frame and meets its budget. -/
theorem opDone_of {w : ℕ} {p : Program} {fmt : Format w} {L b0 i b : ℕ} {s s' : PathTreeState}
    {S S' : List ℕ} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {body : Stmt}
    {o : Outcome} {st' : State} {c : ℕ}
    (hbody : p.procs[b0 + 1 + i]? = some body)
    (hr : Runs w p ω body (startState args mem pos) o st' c)
    (hA : ArenaAt fmt.limbBits L b s' S' st'.mem) (hok : StateOk s' S') (hn : s'.n = s.n)
    (hpost : (pathContract fmt L).post i s args mem s' st'.mem)
    (hv1 : heapArg args ≤ o.value)
    (hv2 : o.value ≤ heapArg args + (pathContract fmt L).space i s args mem)
    (hfr : OpFrame b s.n L (heapArg args) o.value mem st'.mem)
    (hcost : c + pathPhi pathC L s' S' ≤ pathTreeBudget pathC L s.n + pathPhi pathC L s S) :
    OpDone p fmt L b0 i b s S args mem pos ω := by
  refine ⟨body, hbody, o, st', c, hr, s', (s', S'), ⟨rfl, hA, hok⟩, hpost,
    ⟨hv1, hv2, hfr.1, fun a ha hout => hfr.2 a ha hout, fun a ha => Or.inl ?_⟩, hcost⟩
  have ha' : b ≤ a ∧ a < arenaEnd b s'.n L := ha
  rw [hn] at ha'
  exact ha'

/-- The arena of an operation ends below its heap pointer. -/
theorem end_le {h L C b heap : ℕ} {s : PathTreeState} {S : List ℕ}
    (hfoot : ∀ a, (pathRep h L C).foot b (s, S) a → a < heap) : arenaEnd b s.n L ≤ heap := by
  have hlt := nb_lt_end b s.n L
  have hf : (pathRep h L C).foot b (s, S) (arenaEnd b s.n L - 1) :=
    (⟨by unfold arenaNb at hlt; omega, by omega⟩ : b ≤ _ ∧ _ < arenaEnd b s.n L)
  have := hfoot _ hf
  omega

/-- The space of an operation. -/
theorem space_op {w : ℕ} (fmt : Format w) (L i : ℕ) (hi : i ≠ 7) (s : PathTreeState)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (pathContract fmt L).space i s args mem = 20 * treeLimbs L + 100 := by
  show pathAlloc L i s.n args = _
  unfold pathAlloc
  rw [ite_eq_right hi]

/-! ### The potential bounds of the model -/

section Pot

variable {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}

theorem expose_pot (W : LctInvWith pathPayload s trees free depth) {v : ℕ}
    (hv : v ∈ trees.flatMap AuxTree.toList) :
    (lctExposeCost pathPayload s v).2.1 + sumTreePhi pathPayload (lctExpose pathPayload s v) ≤
        sumTreePhi pathPayload s + 6 * Nat.log 2 (2 * s.n + 1) ∧
      (lctExposeCost pathPayload s v).2.2 + heavyCount pathPayload (lctExpose pathPayload s v) ≤
        heavyCount pathPayload s + 2 * Nat.log 2 (2 * s.n + 1) + 2 := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, -, h1, h2⟩ :=
    lctExpose_spec pathPayload_laws W htv hvt
  exact ⟨h1, h2⟩

theorem summary_pot (W : LctInvWith pathPayload s trees free depth) {u v : ℕ}
    (hu : isVertex s.n u) (hv : isVertex s.n v) (hconn : pathTreeConnected s u v) :
    (lctPathSummaryCost pathPayload s u v).2.2.1 +
        sumTreePhi pathPayload (lctPathSummary pathPayload s u v).1 ≤
        sumTreePhi pathPayload s + 12 * Nat.log 2 (2 * s.n + 1) ∧
      (lctPathSummaryCost pathPayload s u v).2.2.2 +
        heavyCount pathPayload (lctPathSummary pathPayload s u v).1 ≤
        heavyCount pathPayload s + 5 * Nat.log 2 (2 * s.n + 1) + 5 := by
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp (isVertex_mem_active W hu)
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv)
  obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2⟩ :=
    lctPathSummary_spec pathPayload_laws W htu hut hu htv hvt ((conn_iff W hu hv).mp hconn)
  exact ⟨h1, h2⟩

theorem apply_pot (W : LctInvWith pathPayload s trees free depth) {u v : ℕ}
    (hu : isVertex s.n u) (hv : isVertex s.n v) (hconn : pathTreeConnected s u v) (t : PathTag) :
    (lctPathSummaryCost pathPayload s u v).2.2.1 +
        sumTreePhi pathPayload (lctPathApply pathPayload s u v t) ≤
        sumTreePhi pathPayload s + 12 * Nat.log 2 (2 * s.n + 1) ∧
      (lctPathSummaryCost pathPayload s u v).2.2.2 +
        heavyCount pathPayload (lctPathApply pathPayload s u v t) ≤
        heavyCount pathPayload s + 5 * Nat.log 2 (2 * s.n + 1) + 5 := by
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp (isVertex_mem_active W hu)
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv)
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2⟩ :=
    lctPathApply_spec pathPayload_laws W htu hut hu htv hvt ((conn_iff W hu hv).mp hconn) t
  exact ⟨h1, h2⟩

theorem cut_pot (W : LctInvWith pathPayload s trees free depth) (u v : ℕ) :
    (lctCutCost pathPayload s u v).2.1 + sumTreePhi pathPayload (lctCut pathPayload s u v) ≤
        sumTreePhi pathPayload s + 15 * Nat.log 2 (2 * s.n + 1) ∧
      (lctCutCost pathPayload s u v).2.2 + heavyCount pathPayload (lctCut pathPayload s u v) ≤
        heavyCount pathPayload s + 5 * Nat.log 2 (2 * s.n + 1) + 10 :=
  ⟨(lctCut_spec pathPayload_laws W u v).1, (lctCut_spec pathPayload_laws W u v).2.1⟩

theorem link_pot (W : LctInvWith pathPayload s trees free depth) {u v : ℕ}
    (hu : isVertex s.n u) (hv : isVertex s.n v) (hnc : ¬ pathTreeConnected s u v)
    (hf : s.freeHead ≠ 0) (e : Option PathEdgeValue) :
    (lctLinkCost pathPayload s u v e).2.1 + sumTreePhi pathPayload (lctLink pathPayload s u v e) ≤
        sumTreePhi pathPayload s + 14 * Nat.log 2 (2 * s.n + 1) ∧
      (lctLinkCost pathPayload s u v e).2.2 +
        heavyCount pathPayload (lctLink pathPayload s u v e) ≤
        heavyCount pathPayload s + 6 * Nat.log 2 (2 * s.n + 1) + 9 := by
  cases free with
  | nil => exact absurd (W.freeListInv : s.freeHead = 0) hf
  | cons ne rest =>
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, h1, h2⟩ :=
      lctLink_spec pathPayload_laws W rfl hu hv (fun h => hnc ((conn_iff W hu hv).mpr h)) e
    exact ⟨h1, h2⟩

end Pot

end MinCostFlow.LinkCut.PathProg
