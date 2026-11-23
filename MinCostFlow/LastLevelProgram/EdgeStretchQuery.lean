module

public import MinCostFlow.LastLevelProgram.AncestorQuery
public import MinCostFlow.LastLevelProgram.EdgeStretchCall
import WordRAM.Tactic

/-!
# A stretch query on precomputed tree tables

Find the lowest common ancestor and pass the three root-distance blocks
to the rounded stretch calculation of Definition 5.8 (pages 19–20).
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF

/-- Arguments are `[ancestors, n, rows, u, v, depths, distances, edge, L, P, heap]`.
The distance table has one block of `L` words per vertex. -/
def edgeStretchQueryBody (ancestor stretch : ℕ) : Stmt :=
  .call 11 ancestor [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5] ;;
  .call 12 stretch
    [.bin .add (.reg 6) (.bin .mul (.reg 3) (.reg 8)),
     .bin .add (.reg 6) (.bin .mul (.reg 4) (.reg 8)),
     .bin .add (.reg 6) (.bin .mul (.reg 11) (.reg 8)),
     .reg 7,.reg 8,.reg 9,.reg 10] ;;
  .ret (.reg 12)

/-- One ancestor query and one rounded stretch call suffice for an edge.
The distance table covers the vertices of the compact tree. -/
theorem edgeStretchQuery_runs {w h ancestor stretch : ℕ} {p : Program}
    {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r)
    (ha : MeetsContract w p ancestor (rootedTreeAncestorContract w T r))
    (hs : MeetsContract w p stretch (edgeStretchContract w h))
    (base n rows u v db dist edge L P heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [base,n,rows,u,v,db,dist,edge,L,P,heap], a < 2^w)
    (hvertices : ∀ x, x ∈ T.V ↔ x < n) (hu : u < n) (hv : v < n)
    (hroom : dist + n*L < 2^w)
    (hapre : (rootedTreeAncestorContract w T r).pre [base,n,rows,u,v,db] mem)
    (hspre : (edgeStretchContract w h).pre
      [dist+u*L,dist+v*L,dist+lca T r u v*L,edge,L,P,heap] mem)
    (hheap : heap+edgeStretchSpace L < 2^w) :
    ∃ o st c, Runs w p ω (edgeStretchQueryBody ancestor stretch)
      (startState [base,n,rows,u,v,db,dist,edge,L,P,heap] mem pos) o st c ∧
      (edgeStretchContract w h).post
        [dist+u*L,dist+v*L,dist+lca T r u v*L,edge,L,P,heap] mem o.value st.mem ∧
      c ≤ 86*rows + edgeStretchCost L + 95 := by
  let z := lca T r u v
  have hz : z < n := (hvertices _).1 (lca_mem hT ((hvertices _).2 hu) ((hvertices _).2 hv))
  have haddr (x : ℕ) (hx : x < n) : dist+x*L < 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right L hx.le) dist).trans_lt hroom
  have hmul (x : ℕ) (hx : x < n) : x*L < 2^w :=
    (Nat.le_add_left _ _).trans_lt (haddr x hx)
  have hbase := hwords base (by simp)
  have hn := hwords n (by simp)
  have hrows := hwords rows (by simp)
  have huw := hwords u (by simp)
  have hvw := hwords v (by simp)
  have hdb := hwords db (by simp)
  have hdist := hwords dist (by simp)
  have hedge := hwords edge (by simp)
  have hL := hwords L (by simp)
  have hP := hwords P (by simp)
  have hh := hwords heap (by simp)
  apply runs_start_le
  unfold edgeStretchQueryBody
  refine runs_seq_call_le ha (vs := [base,n,rows,u,v,db]) (by eval_expr) ?_ hapre ?_
  · wram_words
  · intro q m pos' hpost
    obtain ⟨hq,hm⟩ := hpost
    change q = z at hq
    subst q
    subst m
    have hu' := haddr u hu
    have hv' := haddr v hv
    have hz' := haddr z hz
    have hmu := hmul u hu
    have hmv := hmul v hv
    have hmz := hmul z hz
    refine runs_seq_call_le hs (vs := [dist+u*L,dist+v*L,dist+z*L,edge,L,P,heap])
      (by eval_expr) ?_ hspre ?_
    · wram_words
    · intro result out last hp
      have hr := hp.1
      change result = heap+edgeStretchSpace L at hr
      have hret : result < 2^w := hr ▸ hheap
      refine runs_ret_le (v := result) (by eval_expr) hp ?_
      simp [rootedTreeAncestorContract,edgeStretchContract,heapContract,argsSize,Expr.size]
      omega

/-- The query uses the same heap region as the rounded stretch call. Its
precondition supplies the ancestor tables and the numeric block bounds. -/
def edgeStretchQueryContract (w h : ℕ) (T : MGraph) (r : ℕ) : Contract where
  pre args mem := ∃ base n rows u v db dist edge L P heap,
    args = [base,n,rows,u,v,db,dist,edge,L,P,heap] ∧
    (∀ x, x ∈ T.V ↔ x < n) ∧ u < n ∧ v < n ∧ dist+n*L < 2^w ∧
    (rootedTreeAncestorContract w T r).pre [base,n,rows,u,v,db] mem ∧
    (edgeStretchContract w h).pre
      [dist+u*L,dist+v*L,dist+lca T r u v*L,edge,L,P,heap] mem ∧
    heap+edgeStretchSpace L < 2^w
  post args mem result out :=
    let u := args.getD 3 0
    let v := args.getD 4 0
    let dist := args.getD 6 0
    let L := args.getD 8 0
    (edgeStretchContract w h).post
      [dist+u*L,dist+v*L,dist+lca T r u v*L,args.getD 7 0,L,args.getD 9 0,args.getD 10 0]
      mem result out
  cost args _ := 86*args.getD 2 0 + edgeStretchCost (args.getD 8 0) + 95

/-- A call to the edge query computes a rounded stretch and preserves the
input tables below the heap pointer. -/
theorem edgeStretchQuery_meetsContract {w h entry ancestor stretch : ℕ} {p : Program}
    {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (he : p.procs[entry]? = some (edgeStretchQueryBody ancestor stretch))
    (ha : MeetsContract w p ancestor (rootedTreeAncestorContract w T r))
    (hs : MeetsContract w p stretch (edgeStretchContract w h)) :
    MeetsContract w p entry (edgeStretchQueryContract w h T r) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,n,rows,u,v,db,dist,edge,L,P,heap,rfl,hvertices,hu,hv,hroom,hapre,hspre,hheap⟩ := hpre
  exact edgeStretchQuery_runs hT ha hs base n rows u v db dist edge L P heap pos mem ω
    hwords hvertices hu hv hroom hapre hspre hheap

end MinCostFlow.LastLevelProgram
