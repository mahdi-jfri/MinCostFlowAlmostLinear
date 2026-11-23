module

public import MinCostFlow.DynSpanner.Program.DynSpannerBuildProjDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
import MinCostFlow.DynSpanner.Walks

/-!
# Building the projected graph `J`: loop invariant

`BPCtx` collects the data and the precondition of `dsBuildProjContract`, and `BPInv c i st` is
the invariant of the loop of `dsBuildProjStmt` after `i` edges: the fixed registers, the heap
pointer `projHeapAt … i`, the graph `J` built from the first `i` edges, the walks of these edges
in the heap, and that every other address outside the heap, outside `J` and outside the table
entries of these edges still holds its initial value.

The model facts used by the loop step are proved here: the projected ends are vertices
(`prefixWalk_fst_mem_V`), the walk `projWalk e` is at most `2 · |embLt e| + 1` long, the heap
pointer stays inside the heap area (`projHeapAt_add_le`), and the graph built from the first
`i + 1` edges is the one built from the first `i` edges with `e` added (`buildProjGraph_take_succ`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Model facts -/

/-- The end of the prefix walk is a vertex: the walk stays in `G`. -/
lemma prefixWalk_fst_mem_V {G : MGraph} (hV : G.IsValid) (S : Finset ℕ) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, G.IsWalk a b P → a ∈ G.V →
      (prefixWalk G a P S).1 ∈ G.V
  | _, _, [], .nil _, ha => by unfold prefixWalk; split_ifs <;> exact ha
  | a, _, x :: P, .cons hx hsrc hrest, ha => by
    unfold prefixWalk
    split_ifs
    · exact ha
    · have hdst : G.dst x ∈ G.V := by
        rcases x with ⟨e, d⟩
        cases d <;> simp [MGraph.dst, (hV e hx).1, (hV e hx).2]
      exact prefixWalk_fst_mem_V hV S hrest hdst

lemma projWalk_length_le (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) :
    (projWalk G G embLt S e).length ≤ 2 * (embLt e).length + 1 := by
  have h1 := prefixWalk_snd_length_le G S (G.tail e) (embLt e)
  have h2 := prefixWalk_snd_length_le G S (G.head e) (walkRev (embLt e))
  rw [walkRev_length] at h2
  simp only [projWalk, List.length_append, walkRev_length, List.length_cons, List.length_nil]
  omega

lemma projOutLen_le (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) :
    projOutLen G embLt S e ≤ 4 * (embLt e).length + 5 := by
  have := projWalk_length_le G embLt S e
  simp only [projOutLen]; omega

private lemma sum_take_le {f g : ℕ → ℕ} (hfg : ∀ e, f e ≤ g e) :
    ∀ (l : List ℕ) (i : ℕ), ((l.take i).map f).sum ≤ ((l.take i).map g).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, i + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hfg x) (sum_take_le hfg l i)

private lemma sum_take_add_getElem (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (hi : i < l.length),
      ((l.take i).map f).sum + f l[i] = ((l.take (i + 1)).map f).sum
  | [], _, hi => by simp at hi
  | x :: l, 0, _ => by simp
  | x :: l, i + 1, hi => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    have := sum_take_add_getElem f l i (by simpa using hi)
    omega

private lemma sum_take_le_sum (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ), ((l.take i).map f).sum ≤ (l.map f).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, i + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_le_sum f l i) _

/-- The heap pointer after `i + 1` edges. -/
lemma projHeapAt_succ (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) (hi : i < es.length) :
    projHeapAt G embLt S es heap (i + 1) =
      projHeapAt G embLt S es heap i + projOutLen G embLt S es[i] := by
  simp only [projHeapAt]
  rw [← sum_take_add_getElem _ es i hi]
  omega

/-- The output and the scratch area of edge `i` fit in the heap area. -/
lemma projHeapAt_add_le (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) (hi : i < es.length) :
    projHeapAt G embLt S es heap i + (14 * (embLt es[i]).length + 15) ≤
      heap + projHeapNeed embLt es := by
  have h1 : ((es.take i).map (projOutLen G embLt S)).sum ≤
      ((es.take i).map fun e => 14 * (embLt e).length + 15).sum :=
    sum_take_le (fun e => by have := projOutLen_le G embLt S e; omega) es i
  have h2 := sum_take_add_getElem (fun e => 14 * (embLt e).length + 15) es i hi
  have h3 := sum_take_le_sum (fun e => 14 * (embLt e).length + 15) es (i + 1)
  simp only [projHeapAt, projHeapNeed]
  omega

lemma projHeapAt_mono (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) (hi : i < es.length) :
    projHeapAt G embLt S es heap i ≤ projHeapAt G embLt S es heap (i + 1) := by
  rw [projHeapAt_succ G embLt S es heap i hi]; omega

lemma heap_le_projHeapAt (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) : heap ≤ projHeapAt G embLt S es heap i := by
  simp only [projHeapAt]; omega

/-- The graph of the first `i + 1` edges is the graph of the first `i` edges with the edge
`es[i] = (â, b̂)` and its two ends added. -/
lemma buildProjGraph_take_succ (G H : MGraph) (embLt : Embedding) (S : Finset ℕ)
    (es : List ℕ) (i : ℕ) (hi : i < es.length) (hnd : es.Nodup) :
    let e := es[i]
    let J := buildProjGraph G H embLt S (es.take i).toFinset
    let J₁ : MGraph := { J with V := insert (proj G H embLt S e).1 J.V }
    let J₂ : MGraph := { J₁ with V := insert (proj G H embLt S e).2 J₁.V }
    e ∉ J₂.E ∧
    (J₂.applyUpdate (.insert e (proj G H embLt S e).1 (proj G H embLt S e).2)).V =
      (buildProjGraph G H embLt S (es.take (i + 1)).toFinset).V ∧
    (J₂.applyUpdate (.insert e (proj G H embLt S e).1 (proj G H embLt S e).2)).E =
      (buildProjGraph G H embLt S (es.take (i + 1)).toFinset).E ∧
    ∀ e' ∈ (J₂.applyUpdate (.insert e (proj G H embLt S e).1 (proj G H embLt S e).2)).E,
      (J₂.applyUpdate (.insert e (proj G H embLt S e).1 (proj G H embLt S e).2)).tail e' =
        (buildProjGraph G H embLt S (es.take (i + 1)).toFinset).tail e' ∧
      (J₂.applyUpdate (.insert e (proj G H embLt S e).1 (proj G H embLt S e).2)).head e' =
        (buildProjGraph G H embLt S (es.take (i + 1)).toFinset).head e'
  := by
  intro e J J₁ J₂
  have htake : es.take (i + 1) = es.take i ++ [es[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hnot : e ∉ (es.take i).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have hnd' : (es.take (i + 1)).Nodup := hnd.sublist (List.take_sublist _ _)
    rw [htake] at hnd'
    exact (List.nodup_append.mp hnd').2.2 _ h _ (List.mem_singleton_self _) rfl
  refine ⟨hnot, ?_, ?_, ?_⟩
  · simp only [MGraph.applyUpdate, J₂, J₁, J, buildProjGraph, htake, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.union_singleton,
      Finset.biUnion_insert]
    ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  · simp only [MGraph.applyUpdate, J₂, J₁, J, buildProjGraph, htake, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.union_singleton]
    rfl
  · intro e' _
    simp only [MGraph.applyUpdate, J₂, J₁, J, buildProjGraph]
    by_cases he : e' = e
    · subst he; simp
    · simp [Function.update_of_ne he]

lemma buildProjGraph_take_zero (G H : MGraph) (embLt : Embedding) (S : Finset ℕ)
    (es : List ℕ) :
    (buildProjGraph G H embLt S (es.take 0).toFinset).V = emptyMGraph.V ∧
    (buildProjGraph G H embLt S (es.take 0).toFinset).E = emptyMGraph.E := by
  simp [buildProjGraph, emptyMGraph]

/-! ## Context and invariant -/

/-- The data and the precondition of `dsBuildProjContract`, unpacked. -/
structure BPCtx where
  w : ℕ
  vCap : ℕ
  eCap : ℕ
  G : MGraph
  embLt : Embedding
  S : Finset ℕ
  es : List ℕ
  gPtr : ℕ
  jPtr : ℕ
  sBitPtr : ℕ
  esPtr : ℕ
  wpPtr : ℕ
  embTab : ℕ
  heap : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hgB : gPtr + dynGraphSize vCap eCap < 2 ^ w
  hjB : jPtr + dynGraphSize vCap eCap < 2 ^ w
  hsB : sBitPtr + vCap < 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hwpB : wpPtr + es.length < 2 ^ w
  htB : embTab + eCap < 2 ^ w
  hhB : heap + projHeapNeed embLt es < 2 ^ w
  dHG : IvlDisj heap (projHeapNeed embLt es) gPtr (dynGraphSize vCap eCap)
  dHJ : IvlDisj heap (projHeapNeed embLt es) jPtr (dynGraphSize vCap eCap)
  dHS : IvlDisj heap (projHeapNeed embLt es) sBitPtr vCap
  dHE : IvlDisj heap (projHeapNeed embLt es) esPtr es.length
  dHW : IvlDisj heap (projHeapNeed embLt es) wpPtr es.length
  dHT : IvlDisj heap (projHeapNeed embLt es) embTab eCap
  dJG : IvlDisj jPtr (dynGraphSize vCap eCap) gPtr (dynGraphSize vCap eCap)
  dJS : IvlDisj jPtr (dynGraphSize vCap eCap) sBitPtr vCap
  dJE : IvlDisj jPtr (dynGraphSize vCap eCap) esPtr es.length
  dJW : IvlDisj jPtr (dynGraphSize vCap eCap) wpPtr es.length
  dJT : IvlDisj jPtr (dynGraphSize vCap eCap) embTab eCap
  dTG : IvlDisj embTab eCap gPtr (dynGraphSize vCap eCap)
  dTS : IvlDisj embTab eCap sBitPtr vCap
  dTE : IvlDisj embTab eCap esPtr es.length
  dTW : IvlDisj embTab eCap wpPtr es.length
  hwalk : ∀ k (hk : k < es.length),
    MWalkAt mem0 (mem0 (wpPtr + k)) (embLt es[k]) ∧
    mem0 (wpPtr + k) + (2 * (embLt es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (projHeapNeed embLt es) (mem0 (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) (mem0 (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
    IvlDisj embTab eCap (mem0 (wpPtr + k)) (2 * (embLt es[k]).length + 1)
  hG : DynGraphAt mem0 gPtr vCap eCap G
  hGv : G.IsValid
  hVc : ∀ v ∈ G.V, v < vCap
  hEc : ∀ e ∈ G.E, e < eCap
  hJ0 : DynGraphAt mem0 jPtr vCap eCap emptyMGraph
  hes : ListAt mem0 esPtr es
  hnd : es.Nodup
  hesG : ∀ e ∈ es, e ∈ G.E
  hPw : ∀ e ∈ es, PrefixWalksValid G S eCap (G.tail e) (G.head e) (embLt e)
  hsBit : ∀ v < vCap, mem0 (sBitPtr + v) = if v ∈ S then 1 else 0

/-- Invariant of the loop of `dsBuildProjStmt` after `i` edges. -/
def BPInv (c : BPCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.gPtr ∧ st.regs 1 = c.jPtr ∧ st.regs 2 = c.sBitPtr ∧ st.regs 3 = c.esPtr ∧
  st.regs 4 = c.es.length ∧ st.regs 5 = c.wpPtr ∧ st.regs 6 = c.embTab ∧
  st.regs 7 = projHeapAt c.G c.embLt c.S c.es c.heap i ∧ st.regs 8 = i ∧
  DynGraphAt st.mem c.jPtr c.vCap c.eCap
    (buildProjGraph c.G c.G c.embLt c.S (c.es.take i).toFinset) ∧
  (∀ k (hk : k < c.es.length), k < i →
    c.heap ≤ st.mem (c.embTab + c.es[k]) ∧
    st.mem (c.embTab + c.es[k]) + (2 * (projWalk c.G c.G c.embLt c.S c.es[k]).length + 1) ≤
      projHeapAt c.G c.embLt c.S c.es c.heap i ∧
    MWalkAt st.mem (st.mem (c.embTab + c.es[k])) (projWalk c.G c.G c.embLt c.S c.es[k])) ∧
  ∀ addr, (addr < c.heap ∨ c.heap + projHeapNeed c.embLt c.es ≤ addr) →
    (addr < c.jPtr ∨ c.jPtr + dynGraphSize c.vCap c.eCap ≤ addr) →
    (∀ k (hk : k < c.es.length), k < i → addr ≠ c.embTab + c.es[k]) →
    st.mem addr = c.mem0 addr

/-- An address outside the heap, outside `J` and outside the table keeps its initial value. -/
lemma BPInv.read {c : BPCtx} {i : ℕ} {st : State} (h : BPInv c i st) {addr : ℕ}
    (hH : addr < c.heap ∨ c.heap + projHeapNeed c.embLt c.es ≤ addr)
    (hJ : addr < c.jPtr ∨ c.jPtr + dynGraphSize c.vCap c.eCap ≤ addr)
    (hT : addr < c.embTab ∨ c.embTab + c.eCap ≤ addr) :
    st.mem addr = c.mem0 addr := by
  refine h.2.2.2.2.2.2.2.2.2.2.2 addr hH hJ fun k hk _ => ?_
  have := c.hEc _ (c.hesG _ (List.getElem_mem hk))
  omega

lemma BPCtx.es_lt (c : BPCtx) {k : ℕ} (hk : k < c.es.length) : c.es[k] < c.eCap :=
  c.hEc _ (c.hesG _ (List.getElem_mem hk))

lemma BPCtx.eCap_le (c : BPCtx) : c.eCap ≤ dynGraphSize c.vCap c.eCap := by
  simp only [dynGraphSize]; omega

lemma BPCtx.vCap_le (c : BPCtx) : c.vCap ≤ dynGraphSize c.vCap c.eCap := by
  simp only [dynGraphSize]; omega

end

end MinCostFlow.DynSpanner.Program
