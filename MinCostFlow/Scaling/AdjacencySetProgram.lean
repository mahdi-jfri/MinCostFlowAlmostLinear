module

public import MinCostFlow.Scaling.AdjacencyLayout
public import MinCostFlow.Scaling.WordPairStoreProgram

/-!
# Installing a represented outgoing-list tail

A cycle walk removes the first unused outgoing edge and installs its
already represented tail. The shared pair store writes the tail pointer
and length, preserving every immutable node and every other adjacency
head. No new cells are allocated and the cost is fourteen steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The input pointer represents the replacement list below the old heap.
Only one existing outgoing pointer/length pair changes. -/
def adjacencySetContract (w heads lo bound : ℕ) {n m : ℕ}
    (out : Fin n → List (Fin m)) (v : Fin n) (es : List (Fin m)) : Contract where
  pre args mem := ∃ ptr,args=[ptr,es.length,heads+2*v.val] ∧ AdjacencyAt mem heads lo bound out ∧
    IndexListAt mem lo bound ptr es ∧ heads+2*n≤lo ∧ heads+2*n<2^w
  post _ mem ret mem' := ret=heads+2*v.val+2 ∧
    AdjacencyAt mem' heads lo bound (Function.update out v es) ∧
    ∀ x,x<heads+2*v.val ∨ heads+2*v.val+2≤x → mem' x=mem x
  cost _ _ := 14

/-- The existing pair-store body installs exactly the represented list,
with a frame on all other cells and no change to immutable nodes. -/
theorem adjacencySet_meetsContract {w b heads lo bound n m : ℕ} {p : Program}
    (hp : p.HasAt b wordPairModule) (out : Fin n → List (Fin m)) (v : Fin n) (es : List (Fin m)) :
    MeetsContract w p b (adjacencySetContract w heads lo bound out v es) := by
  intro args mem pos ω hwords hpre
  obtain ⟨ptr,rfl,hat,hlist,hheadsEnd,hspace⟩ := hpre
  have hv := v.isLt
  have hcellEnd : heads+2*v.val+2≤heads+2*n := by omega
  obtain ⟨body,hbody,o,st,cost,hrun,hpost,hcost⟩ :=
    wordPairStore_meetsContract hp [ptr,es.length,heads+2*v.val] mem pos ω hwords
      ⟨ptr,es.length,heads+2*v.val,rfl,hcellEnd.trans_lt hspace⟩
  obtain ⟨hret,hstored,hframe⟩ := hpost
  change o.value=heads+2*v.val+2 at hret
  change ListAt st.mem (heads+2*v.val) [ptr,es.length] at hstored
  change (∀ x,x<heads+2*v.val ∨ heads+2*v.val+2≤x → st.mem x=mem x) at hframe
  have hnodeFrame : ∀ x,lo≤x → x<bound → st.mem x=mem x := by
    intro x hx _
    exact hframe x (Or.inr (by omega))
  have htable := hat.update v es ptr hheadsEnd le_rfl hstored (hlist.of_agree hnodeFrame)
    hnodeFrame (by intro x _ hx0 hx1; apply hframe; omega)
  exact ⟨body,hbody,o,st,cost,hrun,⟨hret,htable,hframe⟩,hcost⟩

/-- Arbitrary replacement lists have joint pointer, table, and word bounds
when installed into an initially empty outgoing table. -/
theorem exists_adjacencySet_pre {n m : ℕ} (v : Fin n) (es : List (Fin m)) :
    ∃ w mem ptr lo bound,(∀ x ∈ [ptr,es.length,2*v.val],x<2^w) ∧
      (adjacencySetContract w 0 lo bound (fun _ : Fin n => ([] : List (Fin m))) v es).pre
        [ptr,es.length,2*v.val] mem := by
  let lo := 2*n+1
  obtain ⟨mem,bound,ptr,hbound,hpositive,hlist,hprefix,hzero⟩ := exists_indexListAt_above lo es
  let w := bound+es.length+2*n+20
  have hw : bound+es.length+2*n+20<2^w := Nat.lt_two_pow_self
  have hp := hlist.pointer_le
  have hv := v.isLt
  have htable : AdjacencyAt mem 0 lo bound (fun _ : Fin n => ([] : List (Fin m))) := by
    intro u
    refine ⟨0,?_,.nil⟩
    intro i hi
    have hi' : i=0 ∨ i=1 := by change i<2 at hi; omega
    rcases hi' with rfl | rfl <;> rw [hprefix _ (by dsimp only [lo]; have hu := u.isLt; omega)] <;> rfl
  refine ⟨w,mem,ptr,lo,bound,?_,ptr,by simp only [Nat.zero_add],htable,hlist,by dsimp only [lo]; omega,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
