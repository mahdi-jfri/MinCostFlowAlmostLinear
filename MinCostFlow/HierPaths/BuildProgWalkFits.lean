module

public import MinCostFlow.HierPaths.BuildProgStoreWalk
public import MinCostFlow.HierPaths.BuildProgPlayerViews
import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Word bounds and input reads for routed walks

The graph supplies both ends of every raw edge. Validity bounds the vertices
visited by the walk. The compressed walk table supplies the raw edge numbers,
so a single scratch vertex block and position array work for every walk.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

private theorem edgeWords_at {E : List (ℕ × ℕ)} {mem : ℕ → ℕ} {a i : ℕ}
    (ha : ListAt mem a (E.flatMap fun e => [e.1, e.2])) (hi : i < E.length) :
    mem (a + 2 * i) = (edgeAt E i).1 ∧ mem (a + 2 * i + 1) = (edgeAt E i).2 := by
  induction E generalizing a i with
  | nil => simp at hi
  | cons e E ih =>
    change ListAt mem a ([e.1, e.2] ++ E.flatMap fun e => [e.1, e.2]) at ha
    obtain ⟨hHead, hTail⟩ := listAt_append.mp ha
    cases i with
    | zero => exact ⟨hHead 0 (by simp), hHead 1 (by simp)⟩
    | succ i =>
      have ht := ih hTail (by simpa using hi)
      have h1 : a + 2 * (i + 1) = a + 2 + 2 * i := by omega
      have h2 : a + 2 * (i + 1) + 1 = a + 2 + 2 * i + 1 := by omega
      simpa only [h1, h2, edgeAt, List.getD_cons_succ, List.length_cons, List.length_nil] using ht

private theorem valid_edgeAt {G : Graph} (hG : G.IsValid) {i : ℕ} (hi : i < G.edges.length) :
    (edgeAt G.edges i).1 < G.n ∧ (edgeAt G.edges i).2 < G.n := by
  apply hG
  simp only [edgeAt, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem walkVerts_lt {G : Graph} (hG : G.IsValid) {u v : ℕ} {wk : List ℕ}
    (hWalk : IsEdgeWalk G.edges u v wk) (hu : u < G.n) :
    ∀ a ∈ walkVerts G.edges u wk, a < G.n := by
  induction hWalk with
  | nil u => simpa [walkVerts] using hu
  | @cons u x v j es hj hend hTail ih =>
    have hx : x < G.n := by
      have he := valid_edgeAt hG hj
      rcases hend with ⟨_, heq⟩ | ⟨heq, _⟩
      · exact heq ▸ he.2
      · exact heq ▸ he.1
    intro a ha
    simp only [walkVerts, otherEnd_eq hend, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hu
    · exact ih hx a ha

/-- Fit the shortcut subroutine's precondition from the stored graph, a valid
routed walk and the address bounds of the reusable scratch regions. -/
theorem pathPre_of_routedWalk {w : ℕ} {G : Graph} {u v : ℕ} {emb : ℕ → List ℕ}
    {mem : ℕ → ℕ} {tb n i ends vs P out : ℕ}
    (hG : G.IsValid) (hWalk : IsEdgeWalk G.edges u v (emb i)) (hu : u < G.n)
    (hi : i < n) (hAt : ListAt mem tb (csrList n emb))
    (hEdges : ListAt mem ends (G.edges.flatMap fun e => [e.1, e.2]))
    (hTable : tb + (csrList n emb).length ≤ vs)
    (hEdgeEnd : ends + 2 * G.m ≤ vs)
    (hScratch : vs + (emb i).length + 1 ≤ P) (hPos : P + G.n ≤ out)
    (hFit : out + (emb i).length < 2 ^ w) (hw : 1 < 2 ^ w)
    (hZero : ∀ a < G.n, mem (P + a) = 0) :
    PathPre w G.edges u (emb i) mem (routedWalkBase tb n emb i) (emb i).length ends vs P out := by
  let wk := emb i
  let ws := routedWalkBase tb n emb i
  let len := wk.length
  have hWs : ws + len ≤ vs := by
    have hp := csr_end_le n emb hi
    change n + 1 + routedWalkOffset emb i + len ≤ _ at hp
    change ws + len ≤ _
    dsimp [ws, routedWalkBase]
    omega
  have hRaw : ListAt mem ws wk := listAt_csrList_get hAt hi
  have hJ : ∀ j < len, wk.getD j 0 < G.m := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact hWalk.lt_length _ (List.getElem_mem hj)
  have hv := walkVerts_lt hG hWalk hu
  constructor
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hWs, by omega, hw⟩
    · intro j hj
      rw [List.getD_eq_getElem _ _ hj]
      exact hRaw j hj
    · intro j hj
      exact (edgeWords_at hEdges (hJ j hj)).1
    · intro j hj
      exact (edgeWords_at hEdges (hJ j hj)).2
    · intro j hj
      have he := hJ j hj
      change (emb i).getD j 0 < G.m at he
      omega
    · intro j hj
      have he := hJ j hj
      change (emb i).getD j 0 < G.m at he
      obtain ⟨h1, h2⟩ := valid_edgeAt hG he
      exact ⟨by omega, by omega⟩
  · exact fun a ha => hZero a (hv a ha)
  · omega
  · intro a _
    omega
  · intro a ha
    have hb := hv a ha
    omega
  · exact hFit
  · omega
  · omega

end MinCostFlow.HierPaths
