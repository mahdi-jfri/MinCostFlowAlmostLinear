module

public import MinCostFlow.HierPaths.BuildTopLabels
public import MinCostFlow.ExpanderDecomp.ProgPortGraph
import MinCostFlow.Expander.GraphHelpers

/-!
# Building the root port graph

Enumerate the input vertices and pass the entire input edge list to
the verified port graph procedure. The graph and owner buffers are
reserved before the cloud builder's heap.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander
  MinCostFlow.ExpanderDecomp MinCostFlow.LowStretch

/-- Address arguments are input, vertex list, local IDs, owners, host graph, work and heap. -/
def buildTopPort (iota port : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 0) (.const 2)) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 10 iota [.reg 7, .reg 1, .const 1, .const 0] ;;
  .call 10 port [.reg 7, .reg 1, .reg 9, .reg 8, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .ret (.reg 10)

theorem buildTopPort_noRand (iota port : ℕ) : (buildTopPort iota port).NoRand := by
  simp [buildTopPort, Stmt.NoRand]

def buildTopPortContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    GraphAt mem ga G ∧ G.IsValid ∧ ZeroFrom mem va ∧
    ga + G.encode.length ≤ va ∧ va + G.n ≤ la ∧ la + G.n ≤ oa ∧
    oa + 2 * G.m ≤ ja ∧ ja + 2 + 20 * G.m ≤ wa ∧
    wa + portGraphWorkSpace G.n G.m ≤ h ∧ h + portGraphHeapSpace G.m ≤ 2 ^ w ∧
    16 < 2 ^ w
  post args mem r mem' := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    GraphAt mem' ja (portGraph cloud G G.verts) ∧
    ListAt mem' oa ((List.range (2 * G.m)).map (portOwner G G.verts)) ∧
    h ≤ r ∧ r ≤ h + portGraphHeapSpace G.m ∧ ZeroFrom mem' r ∧
    ∀ y < va, mem' y = mem y
  cost _ _ := portGraphCost G.n G.m + 30 * (G.n + 1) + 80

theorem buildTopPort_meetsContract {w f iota port : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopPort iota port))
    (hi : p.HasAt iota [iotaP]) (ht : p.HasAt port (portGraphProcs port)) :
    MeetsContract w p f (buildTopPortContract w G) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, va, la, oa, ja, wa, h, rfl, hg, hv, hz, hs, hl, ho, hj, hwk, hh, hroom, h16⟩ := hpre
  let n := G.n
  let m := G.m
  let ea := ga + 2
  have hlen := graph_encode_length G
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hHeap : h < 2 ^ w := hw _ (by simp)
  have hN : n < 2 ^ w := by dsimp [n]; omega
  have hM : m < 2 ^ w := by dsimp [m]; omega
  have hEa : ea < 2 ^ w := by dsimp [ea]; omega
  have hW : 4 ≤ portGraphWorkSpace G.n G.m := by simp [portGraphWorkSpace]
  have hIota : va + n + 1 < 2 ^ w := by dsimp [n]; omega
  refine runs_start_le ?_
  unfold buildTopPort
  refine runs_seq_assign_le (v := n) (Expr.eval_load_of_eq
    (Expr.eval_reg_of_eq (v := ga) rfl) (graphAt_n hg)) ?_
  refine runs_seq_assign_le (v := ea) (Expr.eval_add (Expr.eval_reg_of_eq (v := ga) rfl)
    (Expr.eval_const h2) hEa) ?_
  refine runs_seq_assign_le (v := m) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (v := ga) rfl) (Expr.eval_const h1) (by omega)) (graphAt_m hg)) ?_
  refine runs_seq_call_le (iotaP_spec hi) (vs := [n, va, 1, 0]) ?_ ?_
    ⟨n, va, 1, 0, rfl, hIota, by simpa using hN⟩ ?_
  · simp [evalArgs, Expr.eval, startState, h1]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hN
    · exact hw _ (by simp)
    · exact h1
    · omega
  intro _ mem₁ pos₁ hpost
  obtain ⟨hvert, hf₁⟩ := hpost n va 1 0 rfl
  have hList : ListAt mem₁ va (List.range n) := by
    intro i hi'
    rw [List.getElem_range]
    simpa using hvert i (by simpa using hi')
  have hEdges : EdgesAt mem₁ ea G.edges := by
    intro i hi'
    obtain ⟨hL, hR⟩ := graphAt_to_edgesAt hg i hi'
    change i < m at hi'
    exact ⟨(hf₁ _ (.inl (by dsimp [ea,m] at *; omega))).trans hL,
      (hf₁ _ (.inl (by dsimp [ea,m] at *; omega))).trans hR⟩
  have hX : (List.range n).toFinset = G.verts := by ext i; simp [Graph.verts, n]
  have hBounds : PortGraphBounds w n n m va ea la oa ja wa h := by
    unfold PortGraphBounds
    dsimp only [n,m,ea]
    exact ⟨by omega, by omega, by omega, by omega, by omega, hh, hroom, h16⟩
  have hDis : PortGraphDisjoint n n m va ea la oa ja wa := by
    unfold PortGraphDisjoint DisjointRange
    dsimp only [n,m,ea]
    repeat' apply And.intro
    all_goals first | (left; omega) | (right; omega)
  refine runs_seq_call_le (portGraph_spec ht) (vs := [n, va, m, ea, la, oa, ja, wa, h]) rfl ?_
    ⟨n, n, va, m, ea, la, oa, ja, wa, h, List.range n, G.edges, rfl, List.length_range,
      List.pairwise_lt_range, fun u hu => List.mem_range.mp hu, rfl, ?_, hList, hEdges,
      fun u hu => (hf₁ _ (.inr (by omega))).trans (hz _ (by omega)),
      fun y hy => (hf₁ _ (.inr (by omega))).trans (hz _ (by omega)), hBounds, hDis⟩ ?_
  · intro v hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (apply hw; simp)
  · intro e he
    have hValid := hv e he
    simpa only [List.mem_range] using hValid
  intro r mem₂ pos₂ hpost
  have hrV : readList mem₁ va n = List.range n := by simpa using readList_eq_of_listAt hList
  have hrE : readEdges mem₁ ea m = G.edges := readEdges_eq_of_edgesAt hEdges
  simp only [portGraphContract, List.getD_cons_zero, List.getD_cons_succ] at hpost
  rw [hrV, hrE, hX] at hpost
  obtain ⟨_, _, hG, hhr, hcap, hz₂, hf₂⟩ := hpost
  obtain ⟨hG, hOwner⟩ := hG G (inside_verts_of_isValid hv)
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨ga, va, la, oa, ja, wa, h, rfl, hG, ?_, hhr, hcap, hz₂, ?_⟩ ?_
  · intro i hi'
    rw [List.getElem_map, List.getElem_range]
    exact hOwner i (by simpa using hi')
  · intro y hy
    exact (hf₂ y (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))).trans
      (hf₁ _ (.inl hy))
  · simp [buildTopPortContract, portGraphContract, iotaC, Expr.size, argsSize, n, m]; omega

end MinCostFlow.HierPaths

end
