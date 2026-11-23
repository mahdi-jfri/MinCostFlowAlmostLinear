module

public import MinCostFlow.LastLevelProgram.TraversalMetadata
public import MinCostFlow.LastLevelProgram.RootDistanceModel
public import MinCostFlow.LastLevelProgram.AncestorTable
import MinCostFlow.LastLevelProgram.TreeDistance
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Computing distances from the completed rooted queue

The queue tail lists the nonroot vertices in parent-first order. Its
parent and edge tables supply the indexed distance pass.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF

/-- Starting with a completed queue and a zero root distance, the pass
produces all root distances at the common length scale. -/
theorem rootedQueueAt_distances {w h step : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r)
    (hs : MeetsContract w p step (rootDistanceStepContract w h))
    {st : State} {immutable : ℕ → ℕ} {adj parents edges depths queue floor : ℕ}
    {done : List ℕ}
    (hq : RootedQueueAt st T r immutable adj parents edges depths queue floor done [])
    (hcover : ∀ x, x ∈ done ↔ x ∈ T.V)
    (pos dist lengths L P heap n m : ℕ) (len : ℕ → ℤ)
    (hV : ∀ x, x ∈ T.V ↔ x < n) (he : ∀ e ∈ T.E, e < m)
    (hw : 1 < 2^w) (hL : L < 2^w)
    (hO : queue+n ≤ dist) (hPa : parents+n ≤ dist) (hEa : edges+n ≤ dist)
    (hLen : lengths+m*L ≤ dist) (hD : dist+n*L ≤ heap)
    (hroom : heap+(n-1)*L < 2^w) (hzero : ZeroFrom st.mem heap)
    (hroot : Valid st.mem (dist+r*L) h L ∧ intVal st.mem (dist+r*L) h L = 0)
    (hblocks : ∀ e ∈ T.E, Valid st.mem (lengths+e*L) h L ∧
      intVal st.mem (lengths+e*L) h L = len e)
    (hfit : ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x)) :
    Triple w p (fun s => s = startState [queue+1,parents,edges,dist,lengths,L,heap,n-1] st.mem pos)
      (rootDistancePass step) (normalPost fun s =>
        s.regs 6 = heap+(n-1)*L ∧ ZeroFrom s.mem (s.regs 6) ∧
        (∀ a < dist, s.mem a = st.mem a) ∧
        ∀ v ∈ T.V, Valid s.mem (dist+v*L) h L ∧ fixVal s.mem (dist+v*L) h L P =
          walkLength (fun e => (len e : ℝ) / (2 : ℝ)^P) (T.forestPath v r))
      (fun _ => (55*L+75)*(n-1)+7) := by
  obtain ⟨children,hnd,hlist,hchild,hmeta,ho⟩ := rootedQueueAt_distanceOrder hT hq hcover
  have hv : T.V = Finset.range n := Finset.ext fun x => (hV x).trans Finset.mem_range.symm
  have hcard : T.V.card = n := by simp [hv]
  have hr := (hV r).1 hT.2
  have hlen : children.length = n-1 := by
    have hset : children.toFinset = T.V.erase r := by
      ext x
      simp [hchild,Finset.mem_erase,and_comm]
    rw [← List.toFinset_card_of_nodup hnd,hset,Finset.card_erase_of_mem hT.2,hcard]
  let child := fun i => children.getD i 0
  let par := fun i => parent T r (child i)
  let edge := fun i => parentEdge T r (child i)
  have hget (i : ℕ) (hi : i < n-1) :
      child i = children[i]'(by omega) := by
    have hi' : i < children.length := by omega
    simp [child,hi']
  have hchild' (i : ℕ) (hi : i < n-1) : child i ∈ T.V ∧ child i ≠ r := by
    rw [hget i hi]
    exact (hchild _).1 (List.getElem_mem _)
  have hvalue := rootDistancePass_inputs hT st.mem len h L lengths (n-1) child par edge
    hchild' (fun _ _ => rfl) (fun _ _ => rfl) hblocks hfit
  refine (rootDistancePass_triple hs st.mem pos (queue+1) parents edges dist lengths L heap
    (n-1) n m r child par edge (rootDistanceNumerator T r len) hw hL (by omega) hr
    (by omega) hPa hEa hLen hD hroom hzero ?_ ?_ ?_ hvalue).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  · simpa only [rootDistanceNumerator_root hT] using hroot
  · intro i hi
    obtain ⟨hx,hnr⟩ := hchild' i hi
    obtain ⟨hp,hie,_⟩ := hmeta _ ((hcover _).2 hx)
    exact ⟨(hV _).1 hx,(hV _).1 (parent_mem hT hx),he _ (parentEdge_mem hT hx hnr),
      (hlist i (by omega)).trans (hget i hi).symm,hp,hie hnr⟩
  · intro i hi
    rcases ho i (by omega) with h | ⟨j,hj,hji,h⟩
    · exact Or.inl (by unfold par; rwa [hget i hi])
    · exact Or.inr ⟨j,hji,by unfold par; rw [hget i hi,hget j (by omega)]; exact h⟩
  · intro o out ho
    cases o with
    | returned => exact ho
    | normal =>
      obtain ⟨hret,hz,hf,hout⟩ := ho
      refine ⟨hret,hz,hf,?_⟩
      intro v hv'
      have hmem : v = r ∨ ∃ j < n-1, child j = v := by
        by_cases hvr : v = r
        · exact Or.inl hvr
        · obtain ⟨j,hj,hjv⟩ := List.mem_iff_getElem.mp ((hchild v).2 ⟨hv',hvr⟩)
          exact Or.inr ⟨j,by omega,(hget j (by omega)).trans hjv⟩
      obtain ⟨hvalid,hdist⟩ := hout v hmem
      exact ⟨hvalid,rootDistanceBlock_decode hT hv' out.mem len _ h L P hdist⟩

/-- The traversal's parent table is row zero of the jump table.
Building the higher rows preserves the disjoint depth table. -/
theorem rootedQueueAt_ancestorTable {w row : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (hp : p.procs[row]? = some ancestorRowBody)
    {st : State} {immutable : ℕ → ℕ} {adj parents edges depths queue floor : ℕ}
    {done : List ℕ}
    (hq : RootedQueueAt st T r immutable adj parents edges depths queue floor done [])
    (hcover : ∀ x, x ∈ done ↔ x ∈ T.V)
    (pos n levels : ℕ) (hV : ∀ x, x ∈ T.V ↔ x < n)
    (hw : 1 < 2^w) (hlevels : levels < 2^w)
    (hroom : parents+(levels+1)*n < 2^w)
    (hsep : parents+(levels+1)*n ≤ depths) :
    Triple w p (fun s => s = startState [parents,n,levels] st.mem pos)
      (ancestorTableLoop row) (normalPost fun s =>
        (∀ i < levels+1, ∀ x < n, s.mem (parents+i*n+x) = ancestorJump (parent T r) i x) ∧
        (∀ x < n, s.mem (depths+x) = depth T r x) ∧
        (∀ a, a < parents+n ∨ parents+(levels+1)*n ≤ a → s.mem a = st.mem a))
      (fun _ => (20*n+40)*levels+7) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hm,_⟩ := hq
  have hmeta (x : ℕ) (hx : x < n) :
      st.mem (parents+x) = parent T r x ∧ st.mem (depths+x) = depth T r x := by
    have hx' := List.mem_append_left [] ((hcover x).2 ((hV x).2 hx))
    exact ⟨(hm x hx').1,(hm x hx').2.2⟩
  have hparent (x : ℕ) (hx : x < n) : parent T r x < n ∧
      st.mem (parents+x) = parent T r x :=
    ⟨(hV _).1 (parent_mem hT ((hV x).2 hx)),(hmeta x hx).1⟩
  refine (ancestorTableLoop_triple hp st.mem pos parents n levels (parent T r)
    hw hlevels hroom hparent).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o s hs
  cases o with
  | returned => exact hs
  | normal =>
    obtain ⟨htable,hframe⟩ := hs
    exact ⟨fun i hi => htable i (Nat.le_of_lt_succ hi),
      fun x hx => (hframe _ (Or.inr (by omega))).trans (hmeta x hx).2,hframe⟩

/-- A row count whose power of two covers the compact vertex count
also covers every depth in the traversal table. -/
theorem compactTree_depth_bounds {T : MGraph} {r x n rows w : ℕ}
    (hT : IsRootedTree T r) (hV : ∀ v, v ∈ T.V ↔ v < n)
    (hx : x < n) (hnRows : n ≤ 2^rows) (hnWord : n ≤ 2^w) :
    depth T r x < 2^rows ∧ depth T r x < 2^w := by
  have hv : T.V = Finset.range n := Finset.ext fun v => (hV v).trans Finset.mem_range.symm
  have hd := depth_lt_card_vertices hT ((hV x).2 hx)
  rw [hv,Finset.card_range] at hd
  exact ⟨hd.trans_le hnRows,hd.trans_le hnWord⟩

/-- Callable ancestor-table builder. Arguments are the parent-table
base, the compact vertex count, and the number of additional rows. -/
def rootedAncestorTableBody (row : ℕ) : Stmt :=
  ancestorTableLoop row ;; .ret (.const 0)

/-- The ancestor-table builder uses no `rand` statement. -/
theorem rootedAncestorTableBody_noRand (row : ℕ) : (rootedAncestorTableBody row).NoRand := by
  simp [rootedAncestorTableBody, ancestorTableLoop, forRange, forUp, Stmt.NoRand]

/-- The ancestor table overwrites only the higher rows. This lets the
distance and depth arrays remain in the same memory. -/
@[expose] def rootedAncestorTableContract (w : ℕ) (T : MGraph) (r : ℕ) : Contract where
  pre args mem := ∃ base n levels,
    args = [base,n,levels] ∧ (∀ x, x ∈ T.V ↔ x < n) ∧
    1 < 2^w ∧ base+(levels+1)*n < 2^w ∧
    ∀ x < n, mem (base+x) = parent T r x
  post args mem _ out :=
    let base := args.getD 0 0
    let n := args.getD 1 0
    let levels := args.getD 2 0
    (∀ i < levels+1, ∀ x < n, out (base+i*n+x) = ancestorJump (parent T r) i x) ∧
    ∀ a, a < base+n ∨ base+(levels+1)*n ≤ a → out a = mem a
  cost args _ := (20*args.getD 1 0+40)*args.getD 2 0+10

/-- The traversal's indexed parent table can be passed from another
procedure to the verified ancestor-table builder. -/
theorem rootedAncestorTable_meetsContract {w entry row : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (he : p.procs[entry]? = some (rootedAncestorTableBody row))
    (hp : p.procs[row]? = some ancestorRowBody) :
    MeetsContract w p entry (rootedAncestorTableContract w T r) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,n,levels,rfl,hV,hw,hroom,hbase⟩ := hpre
  have hl := hwords levels (by simp)
  have hparent (x : ℕ) (hx : x < n) : parent T r x < n ∧ mem (base+x) = parent T r x :=
    ⟨(hV _).1 (parent_mem hT ((hV x).2 hx)),hbase x hx⟩
  let st := startState [base,n,levels] mem pos
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := ancestorTableLoop_triple hp mem pos base n levels
    (parent T r) hw hl hroom hparent st ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨htable,hframe⟩ := hpost
    have hret : Runs w p ω (.ret (.const 0)) mid (.returned 0) mid 2 :=
      runs_ret_iff.mpr ⟨0,by eval_expr,rfl,rfl,rfl⟩
    refine ⟨.returned 0,mid,c+3,
      runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hr,hret,by omega⟩),?_,?_⟩
    · exact ⟨fun i hi => htable i (Nat.le_of_lt_succ hi),hframe⟩
    · change c ≤ (20*n+40)*levels+7 at hcost
      change c+3 ≤ (20*n+40)*levels+10
      omega


/-- Arguments are `[queue + 1, parents, edges, distances, lengths, L, heap, n - 1]`. -/
def rootedDistanceBody (step : ℕ) : Stmt :=
  rootDistancePass step ;; .ret (.reg 6)

/-- The distance pass body uses no `rand` statement. -/
theorem rootedDistanceBody_noRand (step : ℕ) : (rootedDistanceBody step).NoRand := by
  simp [rootedDistanceBody, rootDistancePass, distanceVisitChild, forRange, forUp, Stmt.NoRand]

/-- The completed queue and numeric format supply the distance pass.
All distances decode at the same scale as the edge lengths. -/
@[expose] def rootedDistanceContract (w h P : ℕ) (T : MGraph) (r : ℕ) (len : ℕ → ℤ) : Contract where
  pre args mem := ∃ queue parents edges dist lengths L heap n m st immutable adj depths floor done,
    args = [queue+1,parents,edges,dist,lengths,L,heap,n-1] ∧ st.mem = mem ∧
    RootedQueueAt st T r immutable adj parents edges depths queue floor done [] ∧
    (∀ x, x ∈ done ↔ x ∈ T.V) ∧ (∀ x, x ∈ T.V ↔ x < n) ∧ (∀ e ∈ T.E, e < m) ∧
    1 < 2^w ∧ queue+n ≤ dist ∧ parents+n ≤ dist ∧ edges+n ≤ dist ∧
    lengths+m*L ≤ dist ∧ dist+n*L ≤ heap ∧ heap+(n-1)*L < 2^w ∧ ZeroFrom mem heap ∧
    (Valid mem (dist+r*L) h L ∧ intVal mem (dist+r*L) h L = 0) ∧
    (∀ e ∈ T.E, Valid mem (lengths+e*L) h L ∧ intVal mem (lengths+e*L) h L = len e) ∧
    ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x)
  post args mem ret out :=
    let dist := args.getD 3 0
    let L := args.getD 5 0
    ret = args.getD 6 0 + args.getD 7 0 * L ∧ ZeroFrom out ret ∧
    (∀ a < dist, out a = mem a) ∧
    ∀ v ∈ T.V, Valid out (dist+v*L) h L ∧ fixVal out (dist+v*L) h L P =
      walkLength (fun e => (len e : ℝ) / (2 : ℝ)^P) (T.forestPath v r)
  cost args _ := (55*args.getD 5 0+75)*args.getD 7 0+10

/-- The distance pass returns its new heap pointer and preserves the
tables below the distance array. -/
theorem rootedDistance_meetsContract {w h P entry step : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (len : ℕ → ℤ)
    (he : p.procs[entry]? = some (rootedDistanceBody step))
    (hs : MeetsContract w p step (rootDistanceStepContract w h)) :
    MeetsContract w p entry (rootedDistanceContract w h P T r len) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨queue,parents,edges,dist,lengths,L,heap,n,m,st,immutable,adj,depths,floor,done,
    rfl,hm,hq,hcover,hV,hE,hw,hO,hPa,hEa,hLen,hD,hroom,hzero,hroot,hblocks,hfit⟩ := hpre
  subst mem
  have hL := hwords L (by simp)
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := rootedQueueAt_distances hT hs hq hcover pos dist lengths
    L P heap n m len hV hE hw hL hO hPa hEa hLen hD hroom hzero hroot hblocks hfit
    (startState [queue+1,parents,edges,dist,lengths,L,heap,n-1] st.mem pos) ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨hret,hz,hframe,hout⟩ := hpost
    have hrun : Runs w p ω (.ret (.reg 6)) mid (.returned (mid.regs 6)) mid 2 :=
      runs_ret_iff.mpr ⟨mid.regs 6,rfl,rfl,rfl,rfl⟩
    refine ⟨.returned (mid.regs 6),mid,c+3,
      runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hr,hrun,by omega⟩),⟨hret,hz,hframe,hout⟩,?_⟩
    change c ≤ (55*L+75)*(n-1)+7 at hcost
    change c+3 ≤ (55*L+75)*(n-1)+10
    omega
end MinCostFlow.LastLevelProgram
