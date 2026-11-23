module

public import MinCostFlow.LastLevelProgram.TraversalDiscovery
public import MinCostFlow.LastLevelProgram.TraversalOrder
public import MinCostFlow.LastLevelProgram.TraversalCost
import MinCostFlow.LastLevelProgram.TreeDistance
import Mathlib.Tactic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Metadata of the vertices in the traversal queue

The parent, edge, and depth tables agree with the rooted tree on the
discovered vertices. Updating a fresh child leaves those earlier
entries intact.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open LSF

/-- The three tables agree with the tree for every discovered vertex.
The root does not need an incoming edge. -/
def TreeMetadataAt (mem : ℕ → ℕ) (parents edges depths : ℕ) (T : MGraph)
    (r : ℕ) (discovered : List ℕ) : Prop :=
  ∀ x ∈ discovered, mem (parents+x) = parent T r x ∧
    (x ≠ r → mem (edges+x) = parentEdge T r x) ∧ mem (depths+x) = depth T r x

/-- The singleton queue has correct metadata after writing its root
parent and starting with a zero root depth. -/
theorem treeMetadataAt_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (mem : ℕ → ℕ) (parents edges depths : ℕ)
    (hp : mem (parents+r) = r) (hd : mem (depths+r) = 0) :
    TreeMetadataAt mem parents edges depths T r [r] := by
  intro x hx
  have he : x = r := List.mem_singleton.mp hx
  subst x
  simp [parent,depth,forestPath_self hT.isForest,hp,hd]

/-- A visit leaves earlier metadata unchanged, given disjoint metadata
arrays and fresh discoveries. -/
theorem scanTreeQueueModel_metadata_preserve {T : MGraph} {r : ℕ}
    (immutable : ℕ → ℕ) (parents edges depths queue current parentVertex currentDepth n : ℕ)
    (records discovered : List ℕ) (start : ℕ × (ℕ → ℕ))
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hbound : ∀ x ∈ discovered, x < n)
    (hnew : ∀ q ∈ records, immutable q ≠ parentVertex →
      immutable q < n ∧ immutable q ∉ discovered)
    (hmeta : TreeMetadataAt start.2 parents edges depths T r discovered) :
    let out := records.foldl
      (scanTreeQueueModelStep immutable parents edges depths queue current parentVertex currentDepth) start
    TreeMetadataAt out.2 parents edges depths T r discovered := by
  intro out x hx
  have hxn := hbound x hx
  have hf (a : ℕ) (ha : a = parents+x ∨ a = edges+x ∨ a = depths+x) :
      out.2 a = start.2 a := by
    apply scanTreeQueueModel_frame
    · left
      rcases ha with rfl | rfl | rfl <;> omega
    · intro ptr hptr hneq
      obtain ⟨hptrn,hfresh⟩ := hnew ptr hptr hneq
      have hne : x ≠ immutable ptr := fun h => hfresh (h ▸ hx)
      rcases ha with rfl | rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩
  unfold TreeMetadataAt at hmeta
  rw [hf _ (Or.inl rfl), hf _ (Or.inr (Or.inl rfl)),hf _ (Or.inr (Or.inr rfl))]
  exact hmeta x hx

/-- A scan installs the tree metadata for all the newly appended
children, when their neighbor list contains no duplicates. -/
theorem scanTreeQueueModel_metadata_children {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (immutable : ℕ → ℕ)
    (parents edges depths queue current n : ℕ)
    (records : List ℕ) (start : ℕ × (ℕ → ℕ))
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hchild : ∀ q ∈ records, immutable q ≠ parent T r current →
      immutable q < n ∧ immutable q ∈ T.V ∧ immutable q ≠ r ∧
      parent T r (immutable q) = current ∧ parentEdge T r (immutable q) = immutable (q+1))
    (hn : ((records.filter fun q => immutable q != parent T r current).map immutable).Nodup) :
    let out := records.foldl (scanTreeQueueModelStep immutable parents edges depths queue current
      (parent T r current) (depth T r current)) start
    TreeMetadataAt out.2 parents edges depths T r
      ((records.filter fun q => immutable q != parent T r current).map immutable) := by
  intro out x hx
  obtain ⟨ptr,hp,hx⟩ := List.mem_map.mp hx
  obtain ⟨hp,hne⟩ := List.mem_filter.mp hp
  have hne' : immutable ptr ≠ parent T r current := by simpa using hne
  obtain ⟨before,after,hr⟩ := List.append_of_mem hp
  subst x
  obtain ⟨hxB,hxV,hxr,hpar,hedge⟩ := hchild ptr hp hne'
  have hdepth := depth_parent hT hxV hxr
  rw [hpar] at hdepth
  have hafter (a : ℕ) (ha : a ∈ [parents+immutable ptr,edges+immutable ptr,depths+immutable ptr])
      (q : ℕ) (hq : q ∈ after) (hqne : immutable q ≠ parent T r current) :
      a ≠ parents+immutable q ∧ a ≠ edges+immutable q ∧ a ≠ depths+immutable q := by
    have hq' : q ∈ records := by rw [hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    have hqB := (hchild q hq' hqne).1
    have hdiff : immutable ptr ≠ immutable q := by
      have hn' := hn
      rw [hr] at hn'
      simp only [List.filter_append,List.map_append] at hn'
      have hh := (List.nodup_append.mp hn').2.1
      have ht : ((ptr::after).filter fun q => immutable q != parent T r current) =
          ptr :: (after.filter fun q => immutable q != parent T r current) := by simp [hne']
      rw [ht,List.map_cons,List.nodup_cons] at hh
      intro he
      exact hh.1 (List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨hq,by simpa using hqne⟩,he.symm⟩)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩
  obtain ⟨hp',he',hd'⟩ := scanTreeQueueModel_childFields immutable parents edges depths queue current
    (parent T r current) (depth T r current) ptr before after start hne'
    ⟨by omega,by omega,by omega⟩ ⟨by omega,by omega,by omega⟩ hafter
  dsimp [out]
  rw [hr]
  exact ⟨hp'.trans hpar.symm,fun _ => he'.trans hedge.symm,hd'.trans hdepth⟩

/-- At a queue visit the metadata invariant extends to all children.
The queue invariant supplies freshness because the current vertex has
yet to be processed. -/
theorem scanTreeQueueModel_metadata_step {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (immutable : ℕ → ℕ)
    (parents edges depths queue current n : ℕ) (done todo records : List ℕ)
    (start : ℕ × (ℕ → ℕ))
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hV : ∀ x ∈ T.V, x < n)
    (hq : ∀ x, x ∈ done++current::todo ↔
      x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done))
    (hn : (done++current::todo).Nodup)
    (hchild : ∀ q ∈ records, immutable q ≠ parent T r current →
      immutable q ∈ T.V ∧ immutable q ≠ r ∧
      parent T r (immutable q) = current ∧ parentEdge T r (immutable q) = immutable (q+1))
    (hcNodup : ((records.filter fun q => immutable q != parent T r current).map immutable).Nodup)
    (hmeta : TreeMetadataAt start.2 parents edges depths T r (done++current::todo)) :
    let out := records.foldl (scanTreeQueueModelStep immutable parents edges depths queue current
      (parent T r current) (depth T r current)) start
    TreeMetadataAt out.2 parents edges depths T r
      ((done++current::todo) ++ (records.filter fun q => immutable q != parent T r current).map immutable) := by
  intro out
  have hc : current ∉ done := by
    intro h
    exact (List.nodup_append.mp hn).2.2 _ h _ (by simp) rfl
  have hfresh (q : ℕ) (hqr : q ∈ records) (hqne : immutable q ≠ parent T r current) :
      immutable q < n ∧ immutable q ∉ done++current::todo := by
    obtain ⟨hv,hr,hpar,_⟩ := hchild q hqr hqne
    refine ⟨hV _ hv,?_⟩
    exact treeTraversal_child_fresh {x | x ∈ done++current::todo} {x | x ∈ done}
      hr hpar hc (fun x hx => ((hq x).1 hx).2)
  have hold := scanTreeQueueModel_metadata_preserve immutable parents edges depths queue current
    (parent T r current) (depth T r current) n records (done++current::todo) start
    hP hE hD (fun x hx => hV _ ((hq x).1 hx).1) hfresh hmeta
  have hnew := scanTreeQueueModel_metadata_children hT immutable parents edges depths queue
    current n records start hP hE hD (fun q hq hne => ⟨(hfresh q hq hne).1,hchild q hq hne⟩)
    hcNodup
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hold x hx
  · exact hnew x hx


open WordRAM

/-- The queue stores the processed prefix followed by the pending
vertices, with correct rooted metadata for all discovered vertices. -/
def RootedQueueAt (st : State) (T : MGraph) (r : ℕ) (immutable : ℕ → ℕ)
    (adj parents edges depths queue floor : ℕ) (done todo : List ℕ) : Prop :=
  st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
  st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = done.length ∧
  st.regs 7 = (done++todo).length ∧ ListAt st.mem queue (done++todo) ∧
  (∀ a ≥ floor, st.mem a = immutable a) ∧
  (done++todo).Nodup ∧ TreeQueueParentOrder T r (done++todo) ∧
  (∀ x, x ∈ done++todo ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done)) ∧
  TreeMetadataAt st.mem parents edges depths T r (done++todo) ∧
  ∀ a < parents, st.mem a = immutable a

/-- One rooted queue visit advances the processed prefix, appends all
children, and maintains the parent, edge, and depth tables. -/
theorem rootedQueueVisit_triple {w : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (immutable : ℕ → ℕ)
    (adj parents edges depths queue floor n current : ℕ) (done todo records : List ℕ)
    (hw : 2 < 2^w) (hV : ∀ x ∈ T.V, x < n) (hn : T.V.card ≤ n)
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hQ : queue+n < floor) (hA : floor ≤ adj) (ha : adj+n < 2^w)
    (hrecord : ∀ q ∈ records, 0 < q ∧ floor ≤ q ∧ q+2 < 2^w)
    (hbound : ∀ q ∈ records, immutable q < n)
    (hchain : TreeRecordsAt immutable (immutable (adj+current)) records)
    (hchild : ∀ q ∈ records, immutable q ≠ parent T r current →
      immutable q ∈ T.V ∧ immutable q ≠ r ∧
      parent T r (immutable q) = current ∧ parentEdge T r (immutable q) = immutable (q+1))
    (hcomplete : ∀ x, x ∈ (records.filter (fun q => immutable q != parent T r current)).map immutable ↔
      x ∈ T.V ∧ x ≠ r ∧ parent T r x = current)
    (hdup : ((records.filter fun q => immutable q != parent T r current).map immutable).Nodup) :
    let children := (records.filter fun q => immutable q != parent T r current).map immutable
    Triple w p (fun st => RootedQueueAt st T r immutable adj parents edges depths queue floor
        done (current::todo)) scanTreeQueueVertex
      (normalPost fun st => RootedQueueAt st T r immutable adj parents edges depths queue floor
        (done++[current]) (todo++children)) (fun _ => 57*records.length+31) := by
  intro children st ω ⟨h0,h1,h2,h3,h4,h6,h7,hlist,hframe,hnd,ho,hq,hmeta,hprefix⟩
  have hcv := ((hq current).1 (by simp)).1
  have hcn := hV _ hcv
  obtain ⟨hpar,_,hdepth⟩ := hmeta current (by simp)
  obtain ⟨hnd',hq'⟩ := treeTraversal_queue_step done todo children hnd hq hcomplete hdup
  have ho' := treeQueueParentOrder_step done todo children ho
    (fun x hx => ((hcomplete x).1 hx).2.2)
  have hjoin : (done++[current]) ++ (todo++children) = (done++current::todo)++children := by
    simp [List.append_assoc]
  have hcapa : ((done++current::todo)++children).length ≤ n := by
    have hs : (((done++current::todo)++children).toFinset) ⊆ T.V := by
      intro x hx
      exact ((hq' x).1 (by rw [hjoin]; exact List.mem_toFinset.mp hx)).1
    have hc := (Finset.card_le_card hs).trans hn
    rwa [List.toFinset_card_of_nodup (by rwa [← hjoin])] at hc
  have hlimit : (done++current::todo).length +
      (records.filter fun q => immutable q != parent T r current).length ≤ n := by
    simpa only [children,List.length_append,List.length_map] using hcapa
  have hd : depth T r current < n := (depth_lt_card_vertices hT hcv).trans_le hn
  have hcursor : done.length+1 ≤ n := by
    simp only [List.length_append,List.length_cons] at hcapa
    omega
  have hmid := scanTreeQueueVertex_append (p := p) st.mem immutable adj parents edges depths queue
    current (immutable (adj+current)) (parent T r current) (depth T r current) floor n
    done todo records hw (by omega) (by omega) (by omega) (by omega) hlist
    (hframe _ (by omega)) hpar hdepth (by omega) (by omega) hrecord
    (fun q hq => by have hb := hbound q hq; exact ⟨by omega,by omega,by omega⟩)
    hQ (by omega) hchain hlimit hframe
  obtain ⟨o,out,c,hr,hpost,hcost⟩ := hmid st ω ⟨rfl,h0,h1,h2,h3,h4,h6,h7⟩
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨ho0,ho1,ho2,ho3,ho4,ho6,ho7,hl,hf,he⟩ := hpost
    refine ⟨.normal,out,c,hr,⟨ho0,ho1,ho2,ho3,ho4,ho6,?_,?_,hf,hnd',?_,hq',?_,?_⟩,hcost⟩
    · rwa [hjoin]
    · rwa [hjoin]
    · rwa [hjoin]
    · have hm := scanTreeQueueModel_metadata_step hT immutable parents edges depths queue
        current n done todo records ((done++current::todo).length,st.mem)
        hP hE hD hV hq hnd hchild hdup hmeta
      have hm' : out.mem = _ := congrArg Prod.snd he
      rw [hjoin,hm']
      exact hm
    · intro a ha
      have hm : out.mem = _ := congrArg Prod.snd he
      rw [hm]
      exact (scanTreeQueueModel_prefix immutable parents edges depths queue current
        (parent T r current) (depth T r current) records _ (by omega) (by omega)
        (by omega) a ha).trans (hprefix a ha)

/-- The compact adjacency layout supplies every premise of a rooted
queue visit. The retained edge indices are distinct and cover the tree. -/
theorem rootedQueueVisit_adjacency {w : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ)
    (adj parents edges depths queue floor records n k current : ℕ) (done todo : List ℕ)
    (edge : ℕ → ℕ) (hw : 2 < 2^w) (hV : ∀ x ∈ T.V, x < n) (hn : T.V.card ≤ n)
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hQ : queue+n < floor) (hA : floor ≤ adj) (ha : adj+n ≤ records)
    (hroom : records+6*k < 2^w)
    (hzero : ∀ x < n, mem (adj+x) = 0)
    (hends : ∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i))
    (hcover : ∀ e, e ∈ T.E ↔ ∃ i < k, edge i = e)
    (hinj : ∀ i < k, ∀ j < k, edge i = edge j → i = j)
    (hc : current < n) :
    let u := T.tail ∘ edge
    let v := T.head ∘ edge
    let immutable := originalTreeAdjacencyMemory mem adj records u v edge k
    let incidences := treeIncidenceList records u v current k
    let children := (incidences.filter fun q => immutable q != parent T r current).map immutable
    Triple w p (fun st => RootedQueueAt st T r immutable adj parents edges depths queue floor
        done (current::todo)) scanTreeQueueVertex
      (normalPost fun st => RootedQueueAt st T r immutable adj parents edges depths queue floor
        (done++[current]) (todo++children)) (fun _ => 57*incidences.length+31) := by
  intro u v immutable incidences children
  have hchild := treeIncidenceList_child_fields (current := current) hT mem adj records n k edge
    ha hends (fun i hi => (hcover (edge i)).2 ⟨i,hi,rfl⟩)
  refine rootedQueueVisit_triple hT immutable adj parents edges depths queue floor n current
    done todo incidences hw hV hn hP hE hD hQ hA (by omega) ?_ ?_ ?_ hchild ?_ ?_
  · intro ptr hp
    have ⟨h₁,h₂⟩ := treeIncidenceList_bounds hp
    exact ⟨by omega,by omega,by omega⟩
  · intro ptr hp
    obtain ⟨i,hi,hcase⟩ := (mem_treeIncidenceList (fun i hi => (hends i hi).2.2)).1 hp
    obtain ⟨h0,_,h3,_⟩ := originalTreeAdjacencyMemory_fields mem adj records n u v edge ha k
      (fun i hi => ⟨(hends i hi).1,(hends i hi).2.1⟩) i hi
    rcases hcase with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · change immutable (records+6*i) = v i at h0
      exact h0.symm ▸ (hends i hi).2.1
    · change immutable (records+6*i+3) = u i at h3
      exact h3.symm ▸ (hends i hi).1
  · exact originalTreeAdjacencyMemory_recordsAt mem adj records n u v edge ha hzero k hends current hc
  · intro x
    exact mem_treeIncidenceList_children (child := x) hT mem adj records n k edge ha hends hcover
  · exact treeIncidenceList_children_nodup mem adj records n k current (parent T r current)
      u v edge ha hends hinj (parentEdge T r) (fun q hq hne => (hchild q hq hne).2.2.2)

/-- The machine starts the rooted queue invariant with the root as the
only pending vertex and with the root's parent and depth initialized. -/
theorem initializeTreeQueue_rooted {w : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ)
    (pos adj parents edges depths queue floor n : ℕ)
    (hw : 2 < 2^w) (hr : r < n)
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hQ : queue+n < floor) (hf : floor < 2^w)
    (hz : mem (depths+r) = 0) :
    Triple w p (fun st => st = startState [adj,parents,edges,depths,queue,r] mem pos)
      initializeTreeQueue
      (normalPost fun st => RootedQueueAt st T r mem adj parents edges depths queue floor [] [r])
      (fun _ => 15) := by
  refine (initializeTreeQueue_triple (p := p) mem adj parents edges depths queue r
    (by omega) (by omega) (by omega) (by omega)).conseq
    (fun st h => by subst st; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩) ?_ (fun _ _ => le_rfl)
  intro o st h
  cases o with
  | returned => exact h
  | normal =>
    obtain ⟨hqueue,hparent,h0,h1,h2,h3,h4,h6,h7,hframe⟩ := h
    refine ⟨h0,h1,h2,h3,h4,h6,h7,?_,?_,by simp,?_,?_,?_,?_⟩
    · intro i hi
      have he : i = 0 := by simp at hi; omega
      subst i
      exact hqueue
    · intro a ha
      exact hframe a (by omega) (by omega)
    · intro i hi hne
      have he : i = 0 := by simp at hi; omega
      subst i
      exact False.elim (hne rfl)
    · intro x
      simp only [List.nil_append,List.mem_singleton,List.not_mem_nil,or_false]
      exact ⟨fun h => ⟨h.symm ▸ hT.2,h⟩,And.right⟩
    · exact treeMetadataAt_root hT st.mem parents edges depths hparent
        ((hframe _ (by omega) (by omega)).trans hz)
    · intro a ha
      exact hframe a (by omega) (by omega)

open scoped BigOperators in
/-- Starting with the root, the machine visits each compact tree vertex,
writes its metadata, and returns a parent-first queue. The cost is
linear in the vertices and selected tree edges. -/
theorem traverseTreeQueue_triple {w : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ)
    (pos adj parents edges depths queue floor records n k : ℕ) (edge : ℕ → ℕ)
    (hw : 2 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < n)
    (hP : parents+n ≤ edges) (hE : edges+n ≤ depths) (hD : depths+n ≤ queue)
    (hQ : queue+n < floor) (hA : floor ≤ adj) (ha : adj+n ≤ records)
    (hroom : records+6*k < 2^w) (hz : mem (depths+r) = 0)
    (hzero : ∀ x < n, mem (adj+x) = 0)
    (hends : ∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i))
    (hcover : ∀ e, e ∈ T.E ↔ ∃ i < k, edge i = e)
    (hinj : ∀ i < k, ∀ j < k, edge i = edge j → i = j) :
    let immutable := originalTreeAdjacencyMemory mem adj records (T.tail ∘ edge) (T.head ∘ edge) edge k
    Triple w p (fun st => st = startState [adj,parents,edges,depths,queue,r] immutable pos)
      traverseTreeQueue (normalPost fun st => ∃ done,
        RootedQueueAt st T r immutable adj parents edges depths queue floor done [] ∧
        (∀ x, x ∈ done ↔ x ∈ T.V))
      (fun _ => 114*k+35*n+20) := by
  intro immutable
  let degree := fun x => (treeIncidenceList records (T.tail ∘ edge) (T.head ∘ edge) x k).length
  let remaining := fun (a : List ℕ × List ℕ) => Finset.range n \ a.1.toFinset
  let budget := fun a => (∑ x ∈ remaining a, (57*degree x+35))+4
  let Inv := fun (a : List ℕ × List ℕ) st =>
    RootedQueueAt st T r immutable adj parents edges depths queue floor a.1 a.2
  let Q := normalPost fun st => ∃ done, Inv (done,[]) st ∧ (∀ x, x ∈ done ↔ x ∈ T.V)
  have hcard : T.V.card = n := by
    have hs : T.V = Finset.range n := Finset.ext fun x => (hV x).trans Finset.mem_range.symm
    simp [hs]
  have hloop := Triple.loop_inv (w := w) (p := p) (e := .bin .lt (.reg 6) (.reg 7))
    (body := scanTreeQueueVertex) (Inv := Inv) (Q := Q)
    (fun a => (remaining a).card) budget
    (condVal := fun st => if st.regs 6 < st.regs 7 then 1 else 0)
    (fun a st _ => by
      have hw1 : 1 < 2^w := by omega
      by_cases hlt : st.regs 6 < st.regs 7 <;> simp [Expr.eval,BinOp.eval,hw1,hlt])
    (fun a st hs hex => by
      obtain ⟨done,todo⟩ := a
      have hsKeep := hs
      obtain ⟨_,_,_,_,_,h6,h7,_,_,_,_,hq,_⟩ := hs
      have hempty : todo = [] := by
        apply List.length_eq_zero_iff.mp
        by_contra h
        have hlt : st.regs 6 < st.regs 7 := by rw [h6,h7,List.length_append]; exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero h)
        simp [hlt] at hex
      subst todo
      have hq' : ∀ x, x ∈ done ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done) := by
        simpa using hq
      refine ⟨⟨done,hsKeep,treeTraversal_queue_finished hT done hq'⟩,?_⟩
      change 4 ≤ _+4
      omega)
    (fun a st hs hgo => by
      obtain ⟨done,todo⟩ := a
      cases todo with
      | nil =>
        obtain ⟨_,_,_,_,_,h6,h7,_,_,_,_,_,_⟩ := hs
        simp [h6,h7] at hgo
      | cons current todo =>
        have hsKeep := hs
        obtain ⟨_,_,_,_,_,_,_,_,_,hnd,_,hq,_⟩ := hs
        have hc := (hV current).1 ((hq current).1 (by simp)).1
        have hcur : current ∈ remaining (done,current::todo) := by
          have hn : current ∉ done := fun h => (List.nodup_append.mp hnd).2.2 _ h _ (by simp) rfl
          simp [remaining,hc,hn]
        let children := ((treeIncidenceList records (T.tail ∘ edge) (T.head ∘ edge) current k).filter
          fun q => immutable q != parent T r current).map immutable
        let next := (done++[current],todo++children)
        have herase : remaining next = (remaining (done,current::todo)).erase current := by
          ext x
          simp [remaining,next, List.toFinset_append, Finset.mem_sdiff]
          tauto
        have hsize : (remaining next).card < (remaining (done,current::todo)).card := by
          rw [herase]
          exact Finset.card_erase_lt_of_mem hcur
        have hbudget : 3+(57*degree current+31)+budget next+1 ≤ budget (done,current::todo) := by
          dsimp [budget]
          rw [herase,← Finset.sum_erase_add _ _ hcur]
          omega
        refine ⟨57*degree current+31,?_⟩
        refine (rootedQueueVisit_adjacency (p := p) hT mem adj parents edges depths queue floor
          records n k current done todo edge hw (fun x => (hV x).1) hcard.le
          hP hE hD hQ hA ha hroom hzero hends hcover hinj hc).conseq
          (fun s he => he.symm ▸ hsKeep) ?_ (fun _ _ => le_rfl)
        intro o out hout
        cases o with
        | returned => exact False.elim hout
        | normal => exact ⟨next,hout,hsize,hbudget⟩)
    ([],[r])
  have hbudget : budget ([],[r]) = 114*k+35*n+4 := by
    have hsum := treeIncidenceList_sum_length records n k (T.tail ∘ edge) (T.head ∘ edge) hends
    simp only [budget,remaining,List.toFinset_nil,Finset.sdiff_empty,Finset.sum_add_distrib,
      ← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    change 57*(∑ x ∈ Finset.range n, degree x) + n*35 + 4 = _
    have hv : (∑ x ∈ Finset.range n, degree x) = 2*k := hsum
    rw [hv]
    omega
  have hz' : immutable (depths+r) = 0 := by
    have hr := (hV r).1 hT.2
    change originalTreeAdjacencyMemory mem adj records _ _ edge k (depths+r) = 0
    rw [originalTreeAdjacencyMemory_prefix mem adj records _ _ edge (by omega) k _ (by omega)]
    exact hz
  refine Triple.seq_normal
    (initializeTreeQueue_rooted hT immutable pos adj parents edges depths queue floor n hw
      ((hV r).1 hT.2) hP hE hD hQ (by omega) hz') hloop ?_
  intro _ _ _ _
  rw [hbudget]
  omega
/-- The completed machine queue exposes the nonroot order at the word
after the root and supplies its exact parent, edge, and depth entries. -/
theorem rootedQueueAt_distanceOrder {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {st : State} {immutable : ℕ → ℕ} {adj parents edges depths queue floor : ℕ} {done : List ℕ}
    (hq : RootedQueueAt st T r immutable adj parents edges depths queue floor done [])
    (hcover : ∀ x, x ∈ done ↔ x ∈ T.V) :
    ∃ children : List ℕ, children.Nodup ∧ ListAt st.mem (queue+1) children ∧
      (∀ x, x ∈ children ↔ x ∈ T.V ∧ x ≠ r) ∧ TreeMetadataAt st.mem parents edges depths T r done ∧
      ∀ i, ∀ hi : i < children.length,
        parent T r children[i] = r ∨
          ∃ j, ∃ hj : j < children.length, j < i ∧ children[j] = parent T r children[i] := by
  obtain ⟨_,_,_,_,_,_,_,hl,_,hn,ho,_,hm,_⟩ := hq
  simp only [List.append_nil] at hl hn ho hm
  obtain ⟨children,he,hn',hc,ho'⟩ := treeQueueParentOrder_split_root hT done hn ho hcover
  rw [he, listAt_cons] at hl
  exact ⟨children,hn',hl.2,hc,hm,ho'⟩


/-- A callable traversal returns the number of queued vertices. -/
def traverseTreeQueueBody : Stmt :=
  traverseTreeQueue ;; .ret (.reg 7)

/-- A compact tree's incidence lists supply the traversal. Its output
contains the complete queue and all rooted metadata. -/
def traverseTreeQueueContract (w : ℕ) (T : MGraph) (r : ℕ) : Contract where
  pre args immutable := ∃ (adj parents edges depths queue floor records n k : ℕ) (edge mem : ℕ → ℕ),
    args = [adj,parents,edges,depths,queue,r] ∧
    immutable = originalTreeAdjacencyMemory mem adj records (T.tail ∘ edge) (T.head ∘ edge) edge k ∧
    2 < 2^w ∧ (∀ x, x ∈ T.V ↔ x < n) ∧
    parents+n ≤ edges ∧ edges+n ≤ depths ∧ depths+n ≤ queue ∧ queue+n < floor ∧
    floor ≤ adj ∧ adj+n ≤ records ∧ records+6*k < 2^w ∧ mem (depths+r) = 0 ∧
    (∀ x < n, mem (adj+x) = 0) ∧
    (∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i)) ∧
    (∀ e, e ∈ T.E ↔ ∃ i < k, edge i = e) ∧
    (∀ i < k, ∀ j < k, edge i = edge j → i = j)
  post args immutable ret out :=
    ∃ st floor done, st.mem = out ∧
      RootedQueueAt st T r immutable (args.getD 0 0) (args.getD 1 0)
        (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) floor done [] ∧
      (∀ x, x ∈ done ↔ x ∈ T.V) ∧ ret = done.length ∧
      ∀ a ≥ args.getD 0 0, out a = immutable a
  cost _ _ := 114*T.E.card+35*T.V.card+23

/-- The traversal call scans each tree edge twice and each vertex once. -/
theorem traverseTreeQueue_meetsContract {w entry : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (he : p.procs[entry]? = some traverseTreeQueueBody) :
    MeetsContract w p entry (traverseTreeQueueContract w T r) := by
  apply meetsContract_of_runs he
  intro args immutable pos ω _ hpre
  obtain ⟨adj,parents,edges,depths,queue,floor,records,n,k,edge,mem,rfl,rfl,hw,hV,hP,hE,hD,
    hQ,hA,ha,hroom,hz,hzero,hends,hcover,hinj⟩ := hpre
  have hcardV : T.V.card = n := by
    have equ : T.V = Finset.range n := Finset.ext fun x => (hV x).trans Finset.mem_range.symm
    simp [equ]
  have hcardE : T.E.card = k := by
    have equ : T.E = (Finset.range k).image edge := by
      ext x
      simpa [Finset.mem_image] using hcover x
    rw [equ,Finset.card_image_of_injOn,Finset.card_range]
    intro i hi j hj
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := traverseTreeQueue_triple (p := p) hT mem pos adj parents
    edges depths queue floor records n k edge hw hV hP hE hD hQ hA ha hroom hz hzero hends hcover
    hinj _ ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨done,hq,hc⟩ := hpost
    have hret : mid.regs 7 = done.length := by simpa using hq.2.2.2.2.2.2.1
    have hrun : Runs w p ω (.ret (.reg 7)) mid (.returned (mid.regs 7)) mid 2 :=
      runs_ret_iff.mpr ⟨mid.regs 7,rfl,rfl,rfl,rfl⟩
    refine ⟨.returned (mid.regs 7),mid,c+3,
      runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hr,hrun,by omega⟩),
      ⟨mid,floor,done,rfl,hq,hc,hret,fun a ha' =>
        hq.2.2.2.2.2.2.2.2.1 a (hA.trans ha')⟩,?_⟩
    change c ≤ 114*k+35*n+20 at hcost
    change c+3 ≤ 114*T.E.card+35*T.V.card+23
    omega
end MinCostFlow.LastLevelProgram
