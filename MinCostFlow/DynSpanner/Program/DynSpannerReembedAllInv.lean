module

public import MinCostFlow.DynSpanner.Program.DynSpannerReembedAllDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers

/-!
# Re-embedding all affected edges: loop invariant

`RACtx` collects the data and the precondition of `dsReembedAllContract`, and `RAInv c i st` is
the invariant of the loop of `dsReembedAllStmt` after `i` edges: the fixed registers, the heap
pointer `reembHeapAt … i`, the new walks of these edges in the heap, and that every other address
outside the heap and outside the table entries of these edges still holds its initial value.

The model facts used by the loop step are proved here: the walk `reembedWalk e` has at most
`2 · |embLt e| + |embMid e|` edges, and the heap pointer stays inside the heap area
(`reembHeapAt_add_le`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Model facts -/

lemma reembedWalk_length_le (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (e : ℕ) :
    (reembedWalk G G embLt embMid S e).length ≤ 2 * (embLt e).length + (embMid e).length := by
  have h1 := prefixWalk_snd_length_le G S (G.tail e) (embLt e)
  have h2 := prefixWalk_snd_length_le G S (G.head e) (walkRev (embLt e))
  rw [walkRev_length] at h2
  rw [← reembedEdgeWalk_eq_reembedWalk]
  simp only [reembedEdgeWalk, List.length_append, walkRev_length]
  omega

lemma reembOutLen_le (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (e : ℕ) :
    reembOutLen G embLt embMid S e ≤ 4 * (embLt e).length + 2 * (embMid e).length + 1 := by
  have := reembedWalk_length_le G embLt embMid S e
  simp only [reembOutLen]; omega

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
lemma reembHeapAt_succ (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) (hi : i < es.length) :
    reembHeapAt G embLt embMid S es heap (i + 1) =
      reembHeapAt G embLt embMid S es heap i + reembOutLen G embLt embMid S es[i] := by
  simp only [reembHeapAt]
  rw [← sum_take_add_getElem _ es i hi]
  omega

/-- The output and the scratch area of edge `i` fit in the heap area. -/
lemma reembHeapAt_add_le (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) (hi : i < es.length) :
    reembHeapAt G embLt embMid S es heap i +
        (14 * (embLt es[i]).length + 4 * (embMid es[i]).length + 15) ≤
      heap + reembHeapNeed embLt embMid es := by
  have h1 : ((es.take i).map (reembOutLen G embLt embMid S)).sum ≤
      ((es.take i).map fun e => 14 * (embLt e).length + 4 * (embMid e).length + 15).sum :=
    sum_take_le (fun e => by have := reembOutLen_le G embLt embMid S e; omega) es i
  have h2 := sum_take_add_getElem
    (fun e => 14 * (embLt e).length + 4 * (embMid e).length + 15) es i hi
  have h3 := sum_take_le_sum
    (fun e => 14 * (embLt e).length + 4 * (embMid e).length + 15) es (i + 1)
  simp only [reembHeapAt, reembHeapNeed]
  omega

lemma heap_le_reembHeapAt (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) : heap ≤ reembHeapAt G embLt embMid S es heap i := by
  simp only [reembHeapAt]; omega

/-! ## Context and invariant -/

/-- The data and the precondition of `dsReembedAllContract`, unpacked. -/
structure RACtx where
  w : ℕ
  vCap : ℕ
  eCap : ℕ
  G : MGraph
  embLt : Embedding
  embMid : Embedding
  S : Finset ℕ
  es : List ℕ
  gPtr : ℕ
  sBitPtr : ℕ
  esPtr : ℕ
  wpPtr : ℕ
  mpPtr : ℕ
  piTab : ℕ
  heap : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hgB : gPtr + dynGraphSize vCap eCap < 2 ^ w
  hsB : sBitPtr + vCap < 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hwpB : wpPtr + es.length < 2 ^ w
  hmpB : mpPtr + es.length < 2 ^ w
  htB : piTab + eCap < 2 ^ w
  hhB : heap + reembHeapNeed embLt embMid es < 2 ^ w
  dHG : IvlDisj heap (reembHeapNeed embLt embMid es) gPtr (dynGraphSize vCap eCap)
  dHS : IvlDisj heap (reembHeapNeed embLt embMid es) sBitPtr vCap
  dHE : IvlDisj heap (reembHeapNeed embLt embMid es) esPtr es.length
  dHW : IvlDisj heap (reembHeapNeed embLt embMid es) wpPtr es.length
  dHM : IvlDisj heap (reembHeapNeed embLt embMid es) mpPtr es.length
  dHT : IvlDisj heap (reembHeapNeed embLt embMid es) piTab eCap
  dTG : IvlDisj piTab eCap gPtr (dynGraphSize vCap eCap)
  dTS : IvlDisj piTab eCap sBitPtr vCap
  dTE : IvlDisj piTab eCap esPtr es.length
  dTW : IvlDisj piTab eCap wpPtr es.length
  dTM : IvlDisj piTab eCap mpPtr es.length
  hwalk : ∀ k (hk : k < es.length),
    MWalkAt mem0 (mem0 (wpPtr + k)) (embLt es[k]) ∧
    mem0 (wpPtr + k) + (2 * (embLt es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) (mem0 (wpPtr + k))
      (2 * (embLt es[k]).length + 1) ∧
    IvlDisj piTab eCap (mem0 (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
    MWalkAt mem0 (mem0 (mpPtr + k)) (embMid es[k]) ∧
    mem0 (mpPtr + k) + (2 * (embMid es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) (mem0 (mpPtr + k))
      (2 * (embMid es[k]).length + 1) ∧
    IvlDisj piTab eCap (mem0 (mpPtr + k)) (2 * (embMid es[k]).length + 1)
  hG : DynGraphAt mem0 gPtr vCap eCap G
  hGv : G.IsValid
  hVc : ∀ v ∈ G.V, v < vCap
  hEc : ∀ e ∈ G.E, e < eCap
  hes : ListAt mem0 esPtr es
  hnd : es.Nodup
  hesG : ∀ e ∈ es, e ∈ G.E
  hPw : ∀ e ∈ es, PrefixWalksValid G S eCap (G.tail e) (G.head e) (embLt e)
  hMe : ∀ e ∈ es, ∀ x ∈ embMid e, x.1 < eCap
  hsBit : ∀ v < vCap, mem0 (sBitPtr + v) = if v ∈ S then 1 else 0

/-- Invariant of the loop of `dsReembedAllStmt` after `i` edges. -/
def RAInv (c : RACtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.gPtr ∧ st.regs 1 = c.sBitPtr ∧ st.regs 2 = c.esPtr ∧ st.regs 3 = c.es.length ∧
  st.regs 4 = c.wpPtr ∧ st.regs 5 = c.mpPtr ∧ st.regs 6 = c.piTab ∧
  st.regs 7 = reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i ∧ st.regs 8 = i ∧
  (∀ k (hk : k < c.es.length), k < i →
    c.heap ≤ st.mem (c.piTab + c.es[k]) ∧
    st.mem (c.piTab + c.es[k]) + reembOutLen c.G c.embLt c.embMid c.S c.es[k] ≤
      reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i ∧
    MWalkAt st.mem (st.mem (c.piTab + c.es[k]))
      (reembedWalk c.G c.G c.embLt c.embMid c.S c.es[k])) ∧
  ∀ addr, (addr < c.heap ∨ c.heap + reembHeapNeed c.embLt c.embMid c.es ≤ addr) →
    (∀ k (hk : k < c.es.length), k < i → addr ≠ c.piTab + c.es[k]) →
    st.mem addr = c.mem0 addr

lemma RACtx.es_lt (c : RACtx) {k : ℕ} (hk : k < c.es.length) : c.es[k] < c.eCap :=
  c.hEc _ (c.hesG _ (List.getElem_mem hk))

/-- An address outside the heap and outside the table keeps its initial value. -/
lemma RAInv.read {c : RACtx} {i : ℕ} {st : State} (h : RAInv c i st) {addr : ℕ}
    (hH : addr < c.heap ∨ c.heap + reembHeapNeed c.embLt c.embMid c.es ≤ addr)
    (hT : addr < c.piTab ∨ c.piTab + c.eCap ≤ addr) :
    st.mem addr = c.mem0 addr := by
  refine h.2.2.2.2.2.2.2.2.2.2 addr hH fun k hk _ => ?_
  have := c.es_lt hk
  omega

lemma RACtx.eCap_le (c : RACtx) : c.eCap ≤ dynGraphSize c.vCap c.eCap := by
  simp only [dynGraphSize]; omega

lemma RACtx.vCap_le (c : RACtx) : c.vCap ≤ dynGraphSize c.vCap c.eCap := by
  simp only [dynGraphSize]; omega

end

end MinCostFlow.DynSpanner.Program
