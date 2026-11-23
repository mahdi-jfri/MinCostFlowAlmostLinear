module

public import MinCostFlow.LinkCut.PathProg.InitState
public import MinCostFlow.LinkCut.PathTree.FindCorrect
public import MinCostFlow.MinRatio.PathTreeContract

/-!
# How memory holds a path tree

The arena at handle `b` holds a state `s` and the index stack `S` (`ArenaAt`): five header words,
the records of nodes `0 .. 2 n` in the path layout of width `treeLimbs L`, and the index below the
records. The operations also keep some facts about the state that the contract does not mention
(`StateOk`): pointers stay below `2 n + 1`, the ready roots are on the stack, free slots have no
children, and only edges hold values.

The potential (`pathPhi`) is the potential of the model, at `C (L + 1) ^ 2` word operations per
unit, plus `340` per entry of the stack, which pays for popping it later.

The initialization writes the arena of `lctInit` (`pathInit_rep`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

/-- The arena at handle `b` holds the state `s` and the index stack `S`. -/
structure ArenaAt (h L b : ℕ) (s : PathTreeState) (S : List ℕ) (mem : ℕ → ℕ) : Prop where
  fh : mem b = s.freeHead
  hn : mem (b + 1) = s.n
  hL : mem (b + 2) = L
  hK : mem (b + 3) = treeLimbs L
  hnb : mem (b + 4) = arenaNb b s.n
  nodes : (pathLayout h (treeLimbs L)).NodesAt mem (arenaNb b s.n) (2 * s.n) s.splay
  idx : IdxAt mem (arenaNb b s.n) (2 * s.n) S

/-- The facts about the state that the operations keep. -/
structure StateOk (s : PathTreeState) (S : List ℕ) : Prop where
  ptr : PtrOk (2 * s.n) s.splay
  inv : ∃ trees fl d, LctInvWith pathPayload s trees fl d ∧ ReadyIdx s trees S ∧ FreeShape s fl
  vals : ValsOnEdges s

/-- The potential: the model's potential at `C (L + 1) ^ 2` per unit, and `340` per stack
entry. -/
noncomputable def pathPhi (C L : ℕ) (s : PathTreeState) (S : List ℕ) : ℕ :=
  pathTreePotential C L (sumTreePhi pathPayload s) (heavyCount pathPayload s) + 340 * S.length

/-- The representation of the path tree in memory. -/
noncomputable def pathRep (h L C : ℕ) : DSRep PathTreeState where
  τ := PathTreeState × List ℕ
  rep b s x mem := x.1 = s ∧ ArenaAt h L b s x.2 mem ∧ StateOk s x.2
  phi _ x _ := pathPhi C L x.1 x.2
  foot b x a := b ≤ a ∧ a < arenaEnd b x.1.n L

theorem recW_stride (h L : ℕ) :
    (pathLayout h (treeLimbs L)).nodeStride = recW (treeLimbs L) := by
  rw [pathLayout_stride]; rfl

theorem inRecords_foot {h L b n a : ℕ}
    (ha : (pathLayout h (treeLimbs L)).InRecords (arenaNb b n) (2 * n) a) :
    b ≤ a ∧ a < arenaEnd b n L := by
  obtain ⟨h1, h2⟩ := ha
  unfold NodeLayout.nodeAddr at h2
  rw [recW_stride] at h2
  unfold arenaEnd
  unfold arenaNb at h1 h2 ⊢
  constructor <;> omega

theorem inIndex_foot {L b n a : ℕ} (ha : InIndex (arenaNb b n) (2 * n) a) :
    b ≤ a ∧ a < arenaEnd b n L := by
  obtain ⟨h1, h2⟩ := ha
  unfold arenaEnd
  unfold arenaNb at h1 h2 ⊢
  constructor <;> omega

theorem nb_room (b n : ℕ) : 2 * (2 * n) + 3 ≤ arenaNb b n := by unfold arenaNb; omega

/-- An arena depends only on the cells of its footprint. -/
theorem ArenaAt.congr {h L b : ℕ} {s : PathTreeState} {S : List ℕ} {mem mem' : ℕ → ℕ}
    (hA : ArenaAt h L b s S mem) (hag : ∀ a, b ≤ a → a < arenaEnd b s.n L → mem' a = mem a) :
    ArenaAt h L b s S mem' := by
  have hend : b + 5 ≤ arenaEnd b s.n L := by unfold arenaEnd arenaNb; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hag b (le_refl _) (by omega)]; exact hA.fh
  · rw [hag _ (by omega) (by omega)]; exact hA.hn
  · rw [hag _ (by omega) (by omega)]; exact hA.hL
  · rw [hag _ (by omega) (by omega)]; exact hA.hK
  · rw [hag _ (by omega) (by omega)]; exact hA.hnb
  · exact hA.nodes.congr _ fun a ha => hag a (inRecords_foot ha).1 (inRecords_foot ha).2
  · exact hA.idx.congr (nb_room b s.n) fun a ha =>
      hag a (inIndex_foot (L := L) ha).1 (inIndex_foot ha).2

theorem pathRep_local (h L C : ℕ) : (pathRep h L C).Local := by
  intro b s x mem mem' hag
  refine ⟨?_, rfl⟩
  rintro ⟨rfl, hA, hO⟩
  exact ⟨rfl, hA.congr fun a h1 h2 => (hag a ⟨h1, h2⟩).symm, hO⟩

/-! ### The initial state -/

theorem lctInit_n (n : ℕ) : (lctInit pathPayload n none).n = n := rfl

theorem initPar_le (n x : ℕ) : initPar n x ≤ 2 * n := by
  unfold initPar; split_ifs <;> omega

theorem pathInit_stateOk (n : ℕ) : StateOk (lctInit pathPayload n none) [] := by
  obtain ⟨W, -, -, -, -⟩ := lctInit_spec pathPayload_laws n (none : Option PathEdgeValue)
  refine ⟨fun x _ => ?_, ⟨_, _, _, W, fun t _ hr => ?_, fun e _ => ?_⟩, fun x _ => ?_⟩
  · rw [lctInit_node]; exact ⟨Nat.zero_le _, Nat.zero_le _, initPar_le n x, Nat.zero_le _⟩
  · rw [lctInit_node] at hr
    simp [pathRs, PathSummary.empty] at hr
  · rw [lctInit_node]; exact ⟨rfl, rfl, rfl⟩
  · rw [lctInit_node]

/-- The memory after the initialization holds `lctInit`. -/
theorem pathInit_arena {h n L heap : ℕ} {mem m : ℕ → ℕ} (hI : InitMem n L heap mem m) :
    ArenaAt h L heap (lctInit pathPayload n none) [] m :=
  ⟨hI.fh, hI.hn, hI.hL, hI.hK, hI.hnb, initMem_nodesAt hI, initMem_idx hI⟩

end MinCostFlow.LinkCut.PathProg
