module

public import MinCostFlow.LastLevelProgram.TraversalDistances
import WordRAM.Tactic

/-!
# Building the tables used by tree stretch queries

Traverse the compact tree, compute its root distances, and build the
higher ancestor rows. The last step leaves the distances and depths intact.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF

/-- Arguments are `[adj, parents, edges, depths, queue, root, n, levels,
distances, lengths, L, heap]`. -/
def buildTreeTablesBody (traverse distance ancestors : ℕ) : Stmt :=
  .call 12 traverse [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5] ;;
  .call 13 distance [.bin .add (.reg 4) (.const 1),.reg 1,.reg 2,.reg 8,
    .reg 9,.reg 10,.reg 11,.bin .sub (.reg 12) (.const 1)] ;;
  .call 14 ancestors [.reg 1,.reg 6,.reg 7] ;;
  .ret (.reg 13)


/-- Traversing the tree preserves the initialized length and distance
blocks above the adjacency base. Its return count gives the number of
vertices to pass to the distance builder, including the root. -/
theorem rootedDistance_pre_of_traversal {w h P : ℕ} {T : MGraph} {r : ℕ}
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (adj parents edges depths queue count n m dist lengths L heap : ℕ)
    (hpost : (traverseTreeQueueContract w T r).post
      [adj,parents,edges,depths,queue,r] mem count out)
    (hV : ∀ x, x ∈ T.V ↔ x < n) (he : ∀ e ∈ T.E, e < m)
    (hw : 1 < 2^w) (hO : queue+n ≤ dist) (hPa : parents+n ≤ dist)
    (hEa : edges+n ≤ dist) (hLen : lengths+m*L ≤ dist)
    (hD : dist+n*L ≤ heap) (hroom : heap+(n-1)*L < 2^w)
    (hAdjLen : adj ≤ lengths) (hAdjDist : adj ≤ dist)
    (hz : ZeroFrom mem heap)
    (hroot : Valid mem (dist+r*L) h L ∧ intVal mem (dist+r*L) h L = 0)
    (hblocks : ∀ e ∈ T.E, Valid mem (lengths+e*L) h L ∧
      intVal mem (lengths+e*L) h L = len e)
    (hfit : ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x)) :
    count = n ∧ (rootedDistanceContract w h P T r len).pre
      [queue+1,parents,edges,dist,lengths,L,heap,n-1] out := by
  obtain ⟨st,floor,done,hmem,hq,hcover,hcount,hframe⟩ := hpost
  subst out
  change RootedQueueAt st T r mem adj parents edges depths queue floor done [] at hq
  change ∀ a ≥ adj, st.mem a = mem a at hframe
  have hnd : done.Nodup := by simpa using hq.2.2.2.2.2.2.2.2.2.1
  have hset : done.toFinset = Finset.range n :=
    Finset.ext fun x => List.mem_toFinset.trans ((hcover x).trans ((hV x).trans Finset.mem_range.symm))
  have hlength : done.length = n := by
    rw [← List.toFinset_card_of_nodup hnd,hset,Finset.card_range]
  have hblock (a : ℕ) (ha : adj ≤ a) :
      (Valid mem a h L → Valid st.mem a h L) ∧ intVal st.mem a h L = intVal mem a h L := by
    have he (i : ℕ) (_ : i < L) := hframe (a+i) (by omega)
    exact ⟨fun hv i hi => (he i hi).trans_lt (hv i hi),intVal_congr he⟩
  have hr := hblock (dist+r*L) (by omega)
  refine ⟨hcount.trans hlength,queue,parents,edges,dist,lengths,L,heap,n,m,st,mem,adj,depths,
    floor,done,rfl,rfl,hq,hcover,hV,he,hw,hO,hPa,hEa,hLen,hD,hroom,?_,?_,?_,hfit⟩
  · intro a ha
    exact (hframe a (by omega)).trans (hz a ha)
  · exact ⟨hr.1 hroot.1,hr.2.trans hroot.2⟩
  · intro e he
    have hb := hblock (lengths+e*L) (by omega)
    obtain ⟨hv,heq⟩ := hblocks e he
    exact ⟨hb.1 hv,hb.2.trans heq⟩

/-- The three table calls share a memory layout. The higher ancestor
rows are disjoint from the depth, length, and distance blocks. -/
theorem buildTreeTables_runs {w h P traverse distance ancestors : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (len : ℕ → ℤ)
    (ht : MeetsContract w p traverse (traverseTreeQueueContract w T r))
    (hd : MeetsContract w p distance (rootedDistanceContract w h P T r len))
    (ha : MeetsContract w p ancestors (rootedAncestorTableContract w T r))
    (mem : ℕ → ℕ) (ω : ℕ → Bool) (pos adj parents edges depths queue n levels dist lengths L heap m : ℕ)
    (hwords : ∀ a ∈ [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap], a < 2^w)
    (hw : 1 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < n) (he : ∀ e ∈ T.E, e < m)
    (htrav : (traverseTreeQueueContract w T r).pre [adj,parents,edges,depths,queue,r] mem)
    (hPbase : parents+(levels+1)*n ≤ edges)
    (hDbase : depths+n ≤ dist) (hEbase : edges+n ≤ depths)
    (hO : queue+n ≤ dist) (hLen : lengths+m*L ≤ dist)
    (hAdjLen : adj ≤ lengths) (hAdjDist : adj ≤ dist)
    (hAdj : edges ≤ adj)
    (hD : dist+n*L ≤ heap) (hroom : heap+(n-1)*L < 2^w)
    (hzero : ZeroFrom mem heap)
    (hroot : Valid mem (dist+r*L) h L ∧ intVal mem (dist+r*L) h L = 0)
    (hblocks : ∀ e ∈ T.E, Valid mem (lengths+e*L) h L ∧ intVal mem (lengths+e*L) h L = len e)
    (hfit : ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x)) :
    ∃ o out c, Runs w p ω (buildTreeTablesBody traverse distance ancestors)
      (startState [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap] mem pos) o out c ∧
      (o.value = heap+(n-1)*L ∧ ZeroFrom out.mem o.value ∧
        (∀ i < levels+1, ∀ x < n, out.mem (parents+i*n+x) = ancestorJump (parent T r) i x) ∧
        (∀ x < n, out.mem (depths+x) = depth T r x) ∧
        (∀ a, adj ≤ a → a < dist → out.mem a = mem a) ∧
        (∀ x ∈ T.V, Valid out.mem (dist+x*L) h L ∧ fixVal out.mem (dist+x*L) h L P =
          walkLength (fun e => (len e : ℝ) / (2 : ℝ)^P) (T.forestPath x r)) ∧
        ∀ a < parents, out.mem a = mem a) ∧
      c ≤ 114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+80 := by
  have hr := (hV r).1 hT.2
  have hqn : queue+1 < 2^w := by omega
  have hn := hwords n (by simp)
  have hpm : parents+n ≤ edges := by
    have hh := Nat.mul_le_mul_right n (show 1 ≤ levels+1 by omega)
    simpa using (Nat.add_le_add_left hh parents).trans hPbase
  have hadj := hwords adj (by simp)
  have hparents := hwords parents (by simp)
  have hedges := hwords edges (by simp)
  have hdepths := hwords depths (by simp)
  have hqueue := hwords queue (by simp)
  have hrootW := hwords r (by simp)
  have hlevels := hwords levels (by simp)
  have hdistW := hwords dist (by simp)
  have hlengths := hwords lengths (by simp)
  have hL := hwords L (by simp)
  have hheap := hwords heap (by simp)
  apply runs_start_le
  unfold buildTreeTablesBody
  refine runs_seq_call_le ht (vs := [adj,parents,edges,depths,queue,r]) (by eval_expr) ?_ htrav ?_
  · wram_words
  · intro count traversed pos' hpost
    obtain ⟨hcount,hpre⟩ := rootedDistance_pre_of_traversal (P := P) len mem traversed adj
      parents edges depths queue count n m dist lengths L heap hpost hV he hw hO (by omega)
      (by omega) hLen hD hroom hAdjLen hAdjDist hzero hroot hblocks hfit
    subst count
    have hsub : n-1 < 2^w := by omega
    refine runs_seq_call_le hd (vs := [queue+1,parents,edges,dist,lengths,L,heap,n-1])
      (by eval_expr) ?_ hpre ?_
    · wram_words
    · intro endHeap mid pos'' hmid
      obtain ⟨hret,hz,hframe,hdist⟩ := hmid
      change endHeap = heap+(n-1)*L at hret
      change ∀ a < dist, mid a = traversed a at hframe
      obtain ⟨st,floor,done,hmem,hq,hcover,_,hkeep⟩ := hpost
      change st.mem = traversed at hmem
      change RootedQueueAt st T r mem adj parents edges depths queue floor done [] at hq
      change ∀ a ≥ adj, traversed a = mem a at hkeep
      have hmetadata := hq.2.2.2.2.2.2.2.2.2.2.2.2.1
      have htab (x : ℕ) (hx : x < n) :
          mid (parents+x) = parent T r x ∧ mid (depths+x) = depth T r x := by
        have hmemx := List.mem_append_left [] ((hcover x).2 ((hV x).2 hx))
        have hh := hmetadata x hmemx
        rw [hframe _ (by omega),hframe _ (by omega),← hmem]
        exact ⟨hh.1,hh.2.2⟩
      refine runs_seq_call_le ha (vs := [parents,n,levels]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨parents,n,levels,rfl,hV,hw,by omega,fun x hx => (htab x hx).1⟩
      · intro _ out _ hout
        obtain ⟨hjump,houtside⟩ := hout
        change ∀ a, a < parents+n ∨ parents+(levels+1)*n ≤ a → out a = mid a at houtside
        have hretW : endHeap < 2^w := hret ▸ hroom
        refine runs_ret_le (v := endHeap) (by eval_expr) ?_ ?_
        · refine ⟨hret,?_,hjump,?_,?_,?_,?_⟩
          · intro a h
            change endHeap ≤ a at h
            exact (houtside a (Or.inr (by omega))).trans (hz a h)
          · intro x hx
            exact (houtside _ (Or.inr (by omega))).trans (htab x hx).2
          · intro a hal har
            exact (houtside a (Or.inr (by omega))).trans
              ((hframe a har).trans (hkeep a hal))
          · intro x hx
            have hh (j : ℕ) (_ : j < L) : out (dist+x*L+j) = mid (dist+x*L+j) :=
              houtside _ (Or.inr (by omega))
            obtain ⟨hv,hval⟩ := hdist x hx
            exact ⟨fun j hj => (hh j hj).trans_lt (hv j hj),
              by unfold fixVal at *; rw [intVal_congr hh]; exact hval⟩
          · intro a ha
            have hf := hq.2.2.2.2.2.2.2.2.2.2.2.2.2 a ha
            rw [hmem] at hf
            exact (houtside a (Or.inl (ha.trans_le (Nat.le_add_right _ _)))).trans
              ((hframe a (by omega)).trans hf)
        · simp [traverseTreeQueueContract,rootedDistanceContract,rootedAncestorTableContract,
            argsSize,Expr.size]
          omega

/-- Callable tree-table construction, preserving the compact length
array and returning the heap pointer after the distance scratch blocks. -/
def buildTreeTablesContract (w h Q m : ℕ) (T : MGraph) (r : ℕ) (len : ℕ → ℤ) : Contract where
  pre args mem := ∃ adj parents edges depths queue n levels dist lengths L heap,
    args = [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap] ∧
    1 < 2^w ∧ (∀ x, x ∈ T.V ↔ x < n) ∧ (∀ e ∈ T.E, e < m) ∧
    (traverseTreeQueueContract w T r).pre [adj,parents,edges,depths,queue,r] mem ∧
    parents+(levels+1)*n ≤ edges ∧ depths+n ≤ dist ∧ edges+n ≤ depths ∧
    queue+n ≤ dist ∧ lengths+m*L ≤ dist ∧ adj ≤ lengths ∧ adj ≤ dist ∧ edges ≤ adj ∧
    dist+n*L ≤ heap ∧ heap+(n-1)*L < 2^w ∧ ZeroFrom mem heap ∧
    (Valid mem (dist+r*L) h L ∧ intVal mem (dist+r*L) h L = 0) ∧
    (∀ e ∈ T.E, Valid mem (lengths+e*L) h L ∧ intVal mem (lengths+e*L) h L = len e) ∧
    ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x)
  post args mem ret out :=
    let adj := args.getD 0 0
    let parents := args.getD 1 0
    let depths := args.getD 3 0
    let n := args.getD 6 0
    let levels := args.getD 7 0
    let dist := args.getD 8 0
    let L := args.getD 10 0
    let heap := args.getD 11 0
    ret = heap+(n-1)*L ∧ ZeroFrom out ret ∧
    (∀ i < levels+1, ∀ x < n, out (parents+i*n+x) = ancestorJump (parent T r) i x) ∧
    (∀ x < n, out (depths+x) = depth T r x) ∧
    (∀ a, adj ≤ a → a < dist → out a = mem a) ∧
    (∀ x ∈ T.V, Valid out (dist+x*L) h L ∧ fixVal out (dist+x*L) h L Q =
      walkLength (fun e => (len e : ℝ) / (2 : ℝ)^Q) (T.forestPath x r)) ∧
    ∀ a < parents, out a = mem a
  cost args _ :=
    let n := args.getD 6 0
    let levels := args.getD 7 0
    let L := args.getD 10 0
    114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+80

/-- The composed table builder implements its callable interface. -/
theorem buildTreeTables_meetsContract {w h Q m entry traverse distance ancestors : ℕ}
    {p : Program} {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (len : ℕ → ℤ)
    (he : p.procs[entry]? = some (buildTreeTablesBody traverse distance ancestors))
    (ht : MeetsContract w p traverse (traverseTreeQueueContract w T r))
    (hd : MeetsContract w p distance (rootedDistanceContract w h Q T r len))
    (ha : MeetsContract w p ancestors (rootedAncestorTableContract w T r)) :
    MeetsContract w p entry (buildTreeTablesContract w h Q m T r len) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨adj,parents,edges,depths,queue,n,levels,dist,lengths,L,heap,rfl,hw,hV,hEdge,
    htrav,hPbase,hDbase,hEbase,hO,hLen,hAdjLen,hAdjDist,hAdj,hD,hroom,hzero,hroot,hblocks,hfit⟩ := hpre
  exact buildTreeTables_runs hT len ht hd ha mem ω pos adj parents edges depths queue n levels
    dist lengths L heap m hwords hw hV hEdge htrav hPbase hDbase hEbase hO hLen hAdjLen hAdjDist
    hAdj hD hroom hzero hroot hblocks hfit
end MinCostFlow.LastLevelProgram
