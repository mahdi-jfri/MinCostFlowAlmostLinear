module

public import MinCostFlow.HierPaths.BuildProgGameGraph

/-!
# Reservations for the game graphs

Each child can receive at most one matching of at most half its size in
one round. Its graph is stored in a fixed interval large enough for
all rounds and the final injection.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

private theorem perfect_matching_endpoint_count {s : ℕ} {edges : List (ℕ × ℕ)}
    (h : IsPerfectMatchingOn (Finset.range s) edges) : 2 * edges.length ≤ s := by
  let words := edges.flatMap fun e => [e.1,e.2]
  have hLen : words.length = 2 * edges.length := by
    simp [words,List.length_flatMap,Nat.mul_comm]
  have hSubset : words.toFinset ⊆ Finset.range s := by
    intro v hv
    have hv' : v ∈ words := List.mem_toFinset.mp hv
    obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp hv'
    have hMem : v = e.1 ∨ v = e.2 := by simpa using hm
    rcases hMem with rfl | rfl
    · exact (h.1 e he).1
    · exact (h.1 e he).2
  have hCard := Finset.card_le_card hSubset
  rw [List.toFinset_card_of_nodup h.2.1, hLen, Finset.card_range] at hCard
  exact hCard

private theorem witness_word_count {s : ℕ} {M : ℕ → List (ℕ × ℕ)} {n : ℕ}
    (h : ∀ j < n, IsPerfectMatchingOn (Finset.range s) (M j)) :
    2 * (witnessEdges M n).length ≤ n * s := by
  induction n with
  | zero => simp [witnessEdges]
  | succ n ih =>
    have hp := perfect_matching_endpoint_count (h n (Nat.lt_succ_self n))
    have hPrev := ih fun j hj => h j (hj.trans (Nat.lt_succ_self n))
    simp only [witnessEdges,List.length_append,Nat.succ_mul,Nat.mul_add]
    omega

/-- The game invariant bounds the degree and encoding length of a child graph. -/
theorem gameGraph_bounds_of_inv {G₀ : Graph} {X : Finset ℕ} {s off d P t : ℕ} {st : ChildState}
    (hinv : ChildInv G₀ X s off d P t st) :
    let G := gameGraph s st
    G.IsValid ∧ G.IsLoopless ∧ G.encode.length ≤ 2+t*s ∧ ∀ v < G.n, G.deg v ≤ t := by
  let G := gameGraph s st
  have hm : ∀ j < st.rounds.length, IsPerfectMatchingOn (Finset.range s) (st.M j) :=
    fun j hj => (hinv.2.2.1 j hj).1
  have he : G.encode.length = 2 + 2 * G.edges.length := by
    simp [Graph.encode, List.length_flatMap, Nat.mul_comm]
    omega
  have hEdge := witness_word_count hm
  change 2 * G.edges.length ≤ st.rounds.length * s at hEdge
  refine ⟨witness_valid hm,witness_loopless hm,
    he ▸ Nat.add_le_add_left (hEdge.trans (Nat.mul_le_mul_right _ hinv.1)) 2, ?_⟩
  intro v _
  exact (witness_deg_le hm v).trans hinv.1

/-- A scheduled child graph has the validity and degree bounds needed for
the core, and uses at most two header words plus one word per terminal
per prior round. -/
theorem BuildGamePlayerBounds.gameGraph_bounds {S : BuildGameSchedule} {cfg : ParamConfig}
    {β : ℝ} {bh : ℕ} (h : BuildGamePlayerBounds S cfg β bh)
    {t c : ℕ} (ht : t ≤ S.data.limit) (hc : c < S.count) :
    let G := gameGraph S.base.childSize (S.states t c)
    G.IsValid ∧ G.IsLoopless ∧ G.encode.length ≤ 2 + t * S.base.childSize ∧
      ∀ v < G.n, G.deg v ≤ t := by
  obtain ⟨hi,_⟩ := gameRun_inv h.router h.host h.positive h.expansion h.bh h.core h.children
    h.even h.coreSize h.coreDegree t ht
  exact gameGraph_bounds_of_inv (hi c hc)

/-- Each original child reservation pays for the graph header, all the
bounded rounds, and the final matching. -/
def BuildGameSchedule.slotWords (S : BuildGameSchedule) : ℕ :=
  2 + (S.data.limit + 1) * S.base.childSize

/-- Disjoint reservations and input tables at one parent. The arena may
grow above the reply pointers while the reservations stay fixed. -/
structure GameFixedLayout (w : ℕ) (S : BuildGameSchedule) : Prop where
  bits : 3 < 2^w
  size : 2 ≤ S.base.childSize
  host : S.addrs.host + S.base.host.encode.length ≤ S.directory
  verts : S.addrs.verts + (finsetWords S.base.verts).length ≤ S.directory
  directory : S.directory + S.data.limit ≤ S.saved
  saved : S.saved + S.count ≤ S.addrs.graphs
  graphs : S.addrs.graphs + S.count ≤ S.addrs.offsets
  slots : ∀ c < S.count, S.addrs.offsets + S.count ≤ S.childAddr c ∧
    S.childAddr c + S.slotWords ≤ S.addrs.replies
  slotsApart : ∀ c < S.count, ∀ c' < S.count, c ≠ c' →
    S.childAddr c + S.slotWords ≤ S.childAddr c' ∨ S.childAddr c' + S.slotWords ≤ S.childAddr c
  offsets : S.addrs.offsets + S.count ≤ S.addrs.replies
  replies : S.addrs.replies + S.count + 1 ≤ S.addrs.heap
  offsetWords : ∀ c < S.count, S.offset c + S.base.childSize < 2^w

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The active-table update fits below the graph reservations and above
the permanent saved table. -/
theorem GameFixedLayout.stepLayout {w : ℕ} {S : BuildGameSchedule}
    (h : GameFixedLayout w S) {t : ℕ} (ha : 0 < (S.round t).jobs.count)
    (hh : S.addrs.heap ≤ S.heap t) :
    GameStepLayout w (S.round t) (S.data.addrs t) S.start S.saved (S.child t) := by
  have hn := S.count_le t
  refine ⟨ha,Nat.lt_of_lt_of_le (by decide) h.size,fun _ hi _ hj => S.child_injective t hi hj,
    fun _ _ => rfl,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hw := h.offsetWords _ (S.child_active hi).1
    exact (Nat.le_add_right _ _).trans_lt hw
  · intro i hi
    have hci := (S.child_active hi).1
    have hSaved := h.saved
    change S.saved + S.child t i < S.addrs.graphs
    omega
  · change S.addrs.graphs + (S.round t).jobs.count ≤ S.addrs.offsets
    have := h.graphs
    omega
  · change S.addrs.offsets + (S.round t).jobs.count ≤ S.addrs.replies
    have := h.offsets
    omega
  · change S.addrs.replies + (S.round t).jobs.count + 1 ≤ S.heap t
    have hr := h.replies
    omega

/-- The graph and its endpoint array have a linear number of words. -/
theorem buildGraph_encode_length (G : Graph) : G.encode.length = 2 + 2 * G.m := by
  simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]
  omega

/-- The child's graph in a matched round is still inside its reserved interval. -/
theorem BuildGamePlayerBounds.matchedCap {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (hP : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit)
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {i : ℕ}
    (hRes : (S.round t).result.1 = .matched Ms emb)
    (hne : (S.round t).indices.isEmpty = false) (hi : i < Ms.length) :
    let D := (S.round t).applyData Ms emb
    D.cap i ≤ D.addr i + S.slotWords := by
  let D := (S.round t).applyData Ms emb
  have hcnt := hP.rows ht (fun he => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr he)) hRes
  have hi' : i < (S.round t).indices.length := hcnt ▸ hi
  have hAt : D.child i ∈ (S.round t).indices := by
    change (S.round t).indices.getD i 0 ∈ (S.round t).indices
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hc := (S.child_active (mem_batchJobIndices.mp hAt).1).1
  have hg := (hP.gameGraph_bounds (Nat.succ_le_of_lt ht) hc).2.2.1
  have hGraph := hP.graph_succ ht hRes hne hi
  change appendGameMatching (D.graph i) (D.offset i) (Ms.getD i []) =
    gameGraph S.base.childSize (S.states (t+1) (S.child t (D.child i))) at hGraph
  rw [← hGraph,buildGraph_encode_length] at hg
  have he : (appendGameMatching (D.graph i) (D.offset i) (Ms.getD i [])).m =
      (D.graph i).m + (D.row i).count := by
    simp [appendGameMatching,Graph.m,ApplyBatchData.row,matchingWalkRow,D,BuildRoundData.applyData]
  rw [he] at hg
  change 2 + 2 * ((D.graph i).m+(D.row i).count) ≤ 2 + (t+1) * S.base.childSize at hg
  change D.addr i + 2 + 2 * ((D.graph i).m+(D.row i).count) ≤ D.addr i + _
  have hh : (t+1) * S.base.childSize ≤ (S.data.limit+1) * S.base.childSize :=
    Nat.mul_le_mul_right _ (by omega)
  unfold BuildGameSchedule.slotWords
  omega

end MinCostFlow.HierPaths
