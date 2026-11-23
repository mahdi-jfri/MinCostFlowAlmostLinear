module

public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Adjacency records for the rooted-tree traversal

Each directed incidence records the other endpoint, its edge name,
and the previous record at the vertex. Inserting an incidence takes
constant time and changes only that record and the vertex's head.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Registers zero through three hold the head-cell address, the new
record address, the neighbor, and the edge name. -/
def pushTreeIncidence : Stmt :=
  .store (.reg 1) (.reg 2) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 3) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.load (.reg 0)) ;;
  .store (.reg 0) (.reg 1)

/-- Prepend an incidence and preserve all cells outside the new record
and the head being updated. -/
theorem pushTreeIncidence_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (head node neighbor edge : ℕ)
    (hw : 2 < 2^w) (hh : head < node) (hn : node+2 < 2^w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = head ∧ st.regs 1 = node ∧
      st.regs 2 = neighbor ∧ st.regs 3 = edge)
      pushTreeIncidence (normalPost fun st =>
        st.mem head = node ∧ st.mem node = neighbor ∧ st.mem (node+1) = edge ∧
        st.mem (node+2) = mem head ∧
        ∀ a, a ≠ head → a < node ∨ node+3 ≤ a → st.mem a = mem a)
      (fun _ => 23) := by
  intro st ω ⟨hm,h0,h1,h2,h3⟩
  have hhead : head < 2^w := by omega
  have hnode : node < 2^w := by omega
  have hn1 : node+1 < 2^w := by omega
  have hne : head ≠ node := Nat.ne_of_lt hh
  have hne1 : head ≠ node+1 := by omega
  have hne2 : head ≠ node+2 := by omega
  unfold pushTreeIncidence
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost, Expr.size, hm,hne,hne1,Ne.symm hne,Ne.symm hne1,Ne.symm hne2]
  · intro a ha ha'
    have hn0 : a ≠ node := by rcases ha' <;> omega
    have hn1' : a ≠ node+1 := by rcases ha' <;> omega
    have hn2 : a ≠ node+2 := by rcases ha' <;> omega
    simp [ha,hn0,hn1',hn2]

/-- A procedure wrapper for inserting a directed incidence. -/
def pushTreeIncidenceBody : Stmt := pushTreeIncidence ;; .ret (.const 0)

/-- The directed incidence procedure changes precisely the indicated cells. -/
def pushTreeIncidenceContract (w : ℕ) : Contract where
  pre args _ := ∃ head node neighbor edge, args = [head,node,neighbor,edge] ∧
    2 < 2^w ∧ head < node ∧ node+2 < 2^w
  post args mem _ out :=
    let head := args.getD 0 0
    let node := args.getD 1 0
    out head = node ∧ out node = args.getD 2 0 ∧ out (node+1) = args.getD 3 0 ∧
    out (node+2) = mem head ∧
    ∀ a, a ≠ head → a < node ∨ node+3 ≤ a → out a = mem a
  cost _ _ := 26

/-- The incidence insertion is callable from the packed tree edge pass. -/
theorem pushTreeIncidence_meetsContract {w entry : ℕ} {p : Program}
    (he : p.procs[entry]? = some pushTreeIncidenceBody) :
    MeetsContract w p entry (pushTreeIncidenceContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨head,node,neighbor,edge,rfl,hw,hh,hn⟩ := hpre
  let st := startState [head,node,neighbor,edge] mem pos
  obtain ⟨o,out,c,hr,hpost,hcost⟩ :=
    pushTreeIncidence_triple (p := p) mem head node neighbor edge hw hh hn st ω (by
      simp [st,startState])
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    have hret : Runs w p ω (.ret (.const 0)) out (.returned 0) out 2 :=
      runs_ret_iff.mpr ⟨0,by eval_expr,rfl,rfl,rfl⟩
    refine ⟨.returned 0,out,c+3,?_,hpost,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨out,c,2,hr,hret,by omega⟩)
    · change c ≤ 23 at hcost
      change c+3 ≤ 26
      omega

/-- Arguments are `[headU, headV, firstRecord, u, v, edge]`.
The two records occupy six consecutive cells. -/
def pushTreeEdgeBody (push : ℕ) : Stmt :=
  .call 6 push [.reg 0,.reg 2,.reg 4,.reg 5] ;;
  .call 6 push [.reg 1,.bin .add (.reg 2) (.const 3),.reg 3,.reg 5] ;;
  .ret (.const 0)

/-- Both incidences of an edge are inserted, with each retaining its
endpoint's previous head as the next entry. -/
theorem pushTreeEdge_runs {w push : ℕ} {p : Program}
    (hp : MeetsContract w p push (pushTreeIncidenceContract w))
    (a b node u v edge pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hab : a ≠ b) (ha : a < node) (hb : b < node) (hn : node+5 < 2^w)
    (hu : u < 2^w) (hv : v < 2^w) (he : edge < 2^w) :
    ∃ o out c, Runs w p ω (pushTreeEdgeBody push) (startState [a,b,node,u,v,edge] mem pos) o out c ∧
      (out.mem a = node ∧ out.mem b = node+3 ∧
        out.mem node = v ∧ out.mem (node+1) = edge ∧ out.mem (node+2) = mem a ∧
        out.mem (node+3) = u ∧ out.mem (node+4) = edge ∧ out.mem (node+5) = mem b ∧
        ∀ x, x ≠ a → x ≠ b → x < node ∨ node+6 ≤ x → out.mem x = mem x) ∧ c ≤ 70 := by
  have hw : 2 < 2^w := by omega
  apply runs_start_le
  unfold pushTreeEdgeBody
  refine runs_seq_call_le hp (vs := [a,node,v,edge]) (by eval_expr) ?_
    ⟨a,node,v,edge,rfl,hw,ha,by omega⟩ ?_
  · wram_words
  · intro _ mid _ hm
    change mid a = node ∧ mid node = v ∧ mid (node+1) = edge ∧ mid (node+2) = mem a ∧
      (∀ x, x ≠ a → x < node ∨ node+3 ≤ x → mid x = mem x) at hm
    obtain ⟨hMa,hMn,hM1,hM2,hMf⟩ := hm
    refine runs_seq_call_le hp (vs := [b,node+3,u,edge]) (by eval_expr) ?_
      ⟨b,node+3,u,edge,rfl,hw,by omega,by omega⟩ ?_
    · wram_words
    · intro _ out _ ho
      change out b = node+3 ∧ out (node+3) = u ∧ out (node+3+1) = edge ∧
        out (node+3+2) = mid b ∧
        (∀ x, x ≠ b → x < node+3 ∨ node+3+3 ≤ x → out x = mid x) at ho
      obtain ⟨hOb,hO3,hO4,hO5,hOf⟩ := ho
      refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · refine ⟨(hOf a hab (Or.inl (by omega))).trans hMa,hOb,
          (hOf node (by omega) (Or.inl (by omega))).trans hMn,
          (hOf _ (by omega) (Or.inl (by omega))).trans hM1,
          (hOf _ (by omega) (Or.inl (by omega))).trans hM2,
          hO3,hO4,hO5.trans (hMf b hab.symm (Or.inl hb)),?_⟩
        intro x hxA hxB hx
        exact (hOf x hxB (by rcases hx <;> omega)).trans (hMf x hxA (by rcases hx <;> omega))
      · simp [pushTreeIncidenceContract,argsSize,Expr.size]

/-- The two new head values, their records, and the untouched cells. -/
def treeEdgeInsertionPost (a b node u v edge : ℕ) (mem out : ℕ → ℕ) : Prop :=
  out a = node ∧ out b = node+3 ∧
  out node = v ∧ out (node+1) = edge ∧ out (node+2) = mem a ∧
  out (node+3) = u ∧ out (node+4) = edge ∧ out (node+5) = mem b ∧
  ∀ x, x ≠ a → x ≠ b → x < node ∨ node+6 ≤ x → out x = mem x

/-- Callable interface for inserting both records of a tree edge. -/
def pushTreeEdgeContract (w : ℕ) : Contract where
  pre args _ := ∃ a b node u v e, args = [a,b,node,u,v,e] ∧
    a ≠ b ∧ a < node ∧ b < node ∧ node+5 < 2^w
  post args mem _ out := treeEdgeInsertionPost (args.getD 0 0) (args.getD 1 0)
    (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) mem out
  cost _ _ := 70

/-- The pair of incidence calls implements the tree-edge insertion. -/
theorem pushTreeEdge_meetsContract {w entry push : ℕ} {p : Program}
    (he : p.procs[entry]? = some (pushTreeEdgeBody push))
    (hp : MeetsContract w p push (pushTreeIncidenceContract w)) :
    MeetsContract w p entry (pushTreeEdgeContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hw hpre
  obtain ⟨a,b,node,u,v,e,rfl,hab,ha,hb,hn⟩ := hpre
  exact pushTreeEdge_runs hp a b node u v e pos mem ω hab ha hb hn
    (hw u (by simp)) (hw v (by simp)) (hw e (by simp))

/-- Read one selected original edge and its endpoints from the LSST
output and the compact input arrays. Register six is the selected index. -/
def readSelectedTreeEdge : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
  .assign 9 (.load (.bin .add (.reg 2) (.reg 7)))

/-- The three lookups recover the edge and both endpoints in 17 steps. -/
theorem readSelectedTreeEdge_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (selected tails heads adj records count i e u v : ℕ)
    (hs : selected+i < 2^w) (ht : tails+e < 2^w) (hh : heads+e < 2^w)
    (he : mem (selected+i) = e) (hu : mem (tails+e) = u)
    (hv : mem (heads+e) = v) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = selected ∧ st.regs 1 = tails ∧
      st.regs 2 = heads ∧ st.regs 3 = adj ∧ st.regs 4 = records ∧
      st.regs 5 = count ∧ st.regs 6 = i)
      readSelectedTreeEdge (normalPost fun st =>
        st.mem = mem ∧ st.regs 0 = selected ∧ st.regs 1 = tails ∧ st.regs 2 = heads ∧
        st.regs 3 = adj ∧ st.regs 4 = records ∧ st.regs 5 = count ∧
        st.regs 6 = i ∧ st.regs 7 = e ∧ st.regs 8 = u ∧ st.regs 9 = v)
      (fun _ => 17) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h5,h6⟩
  have he' : st.mem (selected+i) = e := hm ▸ he
  have hu' : st.mem (tails+e) = u := hm ▸ hu
  have hv' : st.mem (heads+e) = v := hm ▸ hv
  unfold readSelectedTreeEdge
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,h2,h3,h4,h5,h6,he,hu,hv]

/-- Read a selected edge and insert both of its incidences. -/
def originalTreeAdjacencyStep (insert : ℕ) : Stmt :=
  readSelectedTreeEdge ;;
    .call 10 insert
      [.bin .add (.reg 3) (.reg 8), .bin .add (.reg 3) (.reg 9),
       .bin .add (.reg 4) (.bin .mul (.reg 6) (.const 6)),
       .reg 8,.reg 9,.reg 7]

/-- Build original-edge incidences. Registers three and four are the
vertex-head and record bases, and register five is the edge count. -/
def originalTreeAdjacency (insert : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 5) (originalTreeAdjacencyStep insert)

/-- One iteration reads the packed edge and updates exactly its two heads
and its six record cells. The input base and index registers are preserved. -/
theorem originalTreeAdjacencyStep_triple {w insert : ℕ} {p : Program}
    (hp : MeetsContract w p insert (pushTreeEdgeContract w)) (mem : ℕ → ℕ)
    (selected tails heads adj records count i e u v : ℕ)
    (hs : selected+i < 2^w) (ht : tails+e < 2^w) (hh : heads+e < 2^w)
    (he : mem (selected+i) = e) (hu : mem (tails+e) = u) (hv : mem (heads+e) = v)
    (hne : u ≠ v) (ha : adj+u < records) (hb : adj+v < records)
    (hr : records+6*i+5 < 2^w) (hw : 6 < 2^w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = selected ∧ st.regs 1 = tails ∧
        st.regs 2 = heads ∧ st.regs 3 = adj ∧ st.regs 4 = records ∧ st.regs 5 = count ∧
        st.regs 6 = i)
      (originalTreeAdjacencyStep insert) (normalPost fun st =>
        treeEdgeInsertionPost (adj+u) (adj+v) (records+6*i) u v e mem st.mem ∧
        st.regs 0 = selected ∧ st.regs 1 = tails ∧ st.regs 2 = heads ∧ st.regs 3 = adj ∧
        st.regs 4 = records ∧ st.regs 5 = count ∧ st.regs 6 = i)
      (fun _ => 103) := by
  intro st ω hpre
  obtain ⟨o,mid,c,hrun,hpost,hcost⟩ :=
    readSelectedTreeEdge_triple (p := p) mem selected tails heads adj records count i e u v
      hs ht hh he hu hv st ω hpre
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨hm,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := hpost
    let node := records+6*i
    have hnode : node < 2^w := by dsimp [node]; omega
    have hmul : i*6 < 2^w := by rw [Nat.mul_comm]; omega
    have hargs : evalArgs w mid
        [.bin .add (.reg 3) (.reg 8), .bin .add (.reg 3) (.reg 9),
         .bin .add (.reg 4) (.bin .mul (.reg 6) (.const 6)),.reg 8,.reg 9,.reg 7] =
        some [adj+u,adj+v,node,u,v,e] := by
      have haW : adj+u < 2^w := by omega
      have hbW : adj+v < 2^w := by omega
      have hnodeW : records+i*6 < 2^w := by rw [Nat.mul_comm]; exact hnode
      simp [node,evalArgs,Expr.eval,BinOp.eval,h3,h4,h6,h7,h8,h9,
        haW,hbW,hw,hmul,Nat.mul_comm 6 i,hnodeW]
    have hwords : ∀ x ∈ [adj+u,adj+v,node,u,v,e], x < 2^w := by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    obtain ⟨out,t,ret,hcall,hp',_,hregs,htime⟩ :=
      runs_call_of_meetsContract (r := 10) hp hargs hwords
        ⟨adj+u,adj+v,node,u,v,e,rfl,by omega,by dsimp [node]; omega,
          by dsimp [node]; omega,hr⟩ ω
    refine ⟨.normal,out,c+t+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,t,hrun,hcall,rfl⟩),?_,?_⟩
    · refine ⟨?_,(hregs 0 (by decide)).trans h0,(hregs 1 (by decide)).trans h1,
        (hregs 2 (by decide)).trans h2,(hregs 3 (by decide)).trans h3,
        (hregs 4 (by decide)).trans h4,(hregs 5 (by decide)).trans h5,
        (hregs 6 (by decide)).trans h6⟩
      rw [← hm]
      exact hp'
    · change c ≤ 17 at hcost
      change t ≤ 85 at htime
      change c+t+1 ≤ 103
      omega

/-- The memory update for a pair of incidence records. -/
def insertTreeEdgeMemory (mem : ℕ → ℕ) (a b node u v e : ℕ) : ℕ → ℕ :=
  fun x =>
    if x = a then node else if x = b then node+3 else
    if x = node then v else if x = node+1 then e else if x = node+2 then mem a else
    if x = node+3 then u else if x = node+4 then e else if x = node+5 then mem b else mem x

private theorem treeEdgeInsertion_eq {a b node u v e : ℕ} {mem out : ℕ → ℕ}
    (h : treeEdgeInsertionPost a b node u v e mem out) :
    out = insertTreeEdgeMemory mem a b node u v e := by
  obtain ⟨ha,hb,h0,h1,h2,h3,h4,h5,hf⟩ := h
  funext x
  unfold insertTreeEdgeMemory
  split
  · rename_i hx; subst x; exact ha
  split
  · rename_i hx; subst x; exact hb
  split
  · rename_i hx; subst x; exact h0
  split
  · rename_i hx; subst x; exact h1
  split
  · rename_i hx; subst x; exact h2
  split
  · rename_i hx; subst x; exact h3
  split
  · rename_i hx; subst x; exact h4
  split
  · rename_i hx; subst x; exact h5
  exact hf _ (by assumption) (by assumption) (by omega)

/-- The model for the first `k` insertions, using the selected-edge order. -/
def originalTreeAdjacencyMemory (mem : ℕ → ℕ) (adj records : ℕ) (u v edge : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0 => mem
  | k+1 => insertTreeEdgeMemory (originalTreeAdjacencyMemory mem adj records u v edge k)
      (adj+u k) (adj+v k) (records+6*k) (u k) (v k) (edge k)

/-- Adjacency construction preserves memory below the head array. -/
theorem originalTreeAdjacencyMemory_prefix (mem : ℕ → ℕ) (adj records : ℕ)
    (u v e : ℕ → ℕ) (hadj : adj ≤ records) (k x : ℕ) (hx : x < adj) :
    originalTreeAdjacencyMemory mem adj records u v e k x = mem x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [originalTreeAdjacencyMemory]
    unfold insertTreeEdgeMemory
    repeat
      first | rw [ite_eq_right (by omega)] | exact ih

/-- The adjacency pass preserves memory after its reserved incidence records. -/
theorem originalTreeAdjacencyMemory_suffix (mem : ℕ → ℕ) (adj records n : ℕ)
    (u v e : ℕ → ℕ) (ha : adj + n ≤ records) (k : ℕ)
    (hends : ∀ i < k, u i < n ∧ v i < n)
    (x : ℕ) (hx : records + 6 * k ≤ x) :
    originalTreeAdjacencyMemory mem adj records u v e k x = mem x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨hu, hv⟩ := hends k (Nat.lt_succ_self _)
    rw [originalTreeAdjacencyMemory]
    unfold insertTreeEdgeMemory
    have hrec : records + 6 * k + 6 ≤ x := by omega
    repeat
      first | rw [ite_eq_right (by omega)]
    exact ih (fun i hi => hends i (hi.trans (Nat.lt_succ_self _))) (by omega)

/-- Build the adjacency records for all selected original edges in a
single linear pass. The input arrays lie below the adjacency heads. -/
theorem originalTreeAdjacency_triple {w insert : ℕ} {p : Program}
    (hp : MeetsContract w p insert (pushTreeEdgeContract w)) (mem : ℕ → ℕ)
    (pos selected tails heads adj records count n m : ℕ) (u v edge : ℕ → ℕ)
    (hw : 6 < 2^w) (hc : count < 2^w)
    (hs : selected+count ≤ adj) (ht : tails+m ≤ adj) (hh : heads+m ≤ adj)
    (ha : adj+n ≤ records) (hr : records+6*count < 2^w)
    (hinputs : ∀ i < count, edge i < m ∧ u i < n ∧ v i < n ∧ u i ≠ v i ∧
      mem (selected+i) = edge i ∧ mem (tails+edge i) = u i ∧ mem (heads+edge i) = v i) :
    Triple w p (fun st => st = startState [selected,tails,heads,adj,records,count] mem pos)
      (originalTreeAdjacency insert)
      (normalPost fun st => st.mem = originalTreeAdjacencyMemory mem adj records u v edge count)
      (fun _ => 112*count+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = selected ∧ st.regs 1 = tails ∧ st.regs 2 = heads ∧ st.regs 3 = adj ∧
    st.regs 4 = records ∧ st.regs 5 = count ∧ st.regs 6 = i ∧
    st.mem = originalTreeAdjacencyMemory mem adj records u v edge i
  have loop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 5)
    (body := originalTreeAdjacencyStep insert) (Inv := Inv)
    (P := fun st => st = startState [selected,tails,heads,adj,records,count] mem pos)
    103 0 count (Nat.zero_le _) (by omega) (fun _ => hc)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,originalTreeAdjacencyMemory]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hreg : st.regs 5 = count := h.2.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,hm⟩
      obtain ⟨he,hu,hv,hne,hsM,htM,hhM⟩ := hinputs i hi
      have hframe (x : ℕ) (hx : x < adj) : st.mem x = mem x := by
        rw [hm]
        exact originalTreeAdjacencyMemory_prefix mem adj records u v edge (by omega) i x hx
      obtain ⟨o,out,c,hrun,hpost,hcost⟩ :=
        originalTreeAdjacencyStep_triple hp st.mem selected tails heads adj records count i _ _ _
          (by omega) (by omega) (by omega)
          ((hframe _ (by omega)).trans hsM) ((hframe _ (by omega)).trans htM)
          ((hframe _ (by omega)).trans hhM) hne (by omega) (by omega) (by omega) hw
          st ω ⟨rfl,h0,h1,h2,h3,h4,h5,h6⟩
      cases o with
      | returned => exact False.elim hpost
      | normal =>
        obtain ⟨hmem,ho0,ho1,ho2,ho3,ho4,ho5,ho6⟩ := hpost
        refine ⟨.normal,out,c,hrun,⟨?_,ho6⟩,hcost⟩
        refine ⟨ho0,ho1,ho2,ho3,ho4,ho5,by simp,?_⟩
        change out.mem = originalTreeAdjacencyMemory mem adj records u v edge (i+1)
        rw [originalTreeAdjacencyMemory,← hm]
        exact treeEdgeInsertion_eq hmem)
  refine loop.conseq (fun _ h => h) ?_ (by intro _ _; simp [Expr.size,Nat.mul_comm])
  intro o st h
  cases o with
  | returned => exact h
  | normal => exact h.2.2.2.2.2.2.2

/-- A nonzero record pointer identifies an oriented incidence of the
given vertex within the first `k` selected edges. -/
def treeIncidenceFor (records : ℕ) (u v : ℕ → ℕ) (k vertex ptr : ℕ) : Prop :=
  ∃ i < k, (u i = vertex ∧ ptr = records+6*i) ∨
    (v i = vertex ∧ ptr = records+6*i+3)

private theorem treeIncidenceFor_mono {records k l vertex ptr : ℕ} {u v : ℕ → ℕ}
    (hk : k ≤ l) (h : treeIncidenceFor records u v k vertex ptr) :
    treeIncidenceFor records u v l vertex ptr := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi.trans_le hk,h⟩

/-- In the completed adjacency lists, each head references an incidence
of its vertex or zero. Links inside a record point to an incidence of
the same vertex from a strictly earlier insertion, or to zero. -/
theorem originalTreeAdjacencyMemory_links (mem : ℕ → ℕ) (adj records n : ℕ)
    (u v e : ℕ → ℕ) (ha : adj+n ≤ records)
    (hzero : ∀ x < n, mem (adj+x) = 0)
    (k : ℕ) (hv : ∀ i < k, u i < n ∧ v i < n ∧ u i ≠ v i) :
    let out := originalTreeAdjacencyMemory mem adj records u v e k
    (∀ x < n, out (adj+x) = 0 ∨ treeIncidenceFor records u v k x (out (adj+x))) ∧
    (∀ i < k,
      (out (records+6*i+2) = 0 ∨
        treeIncidenceFor records u v i (u i) (out (records+6*i+2))) ∧
      (out (records+6*i+5) = 0 ∨
        treeIncidenceFor records u v i (v i) (out (records+6*i+5)))) := by
  induction k with
  | zero => exact ⟨fun x hx => Or.inl (hzero x hx),fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ k ih =>
    let prev := originalTreeAdjacencyMemory mem adj records u v e k
    let node := records+6*k
    obtain ⟨hu,hv',hne⟩ := hv k (by omega)
    obtain ⟨hheads,hlinks⟩ := ih (fun i hi => hv i (by omega))
    change (∀ x < n, _ ) ∧ _
    simp only [originalTreeAdjacencyMemory]
    constructor
    · intro x hx
      by_cases hxu : x = u k
      · subst x
        rw [show insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
            (adj+u k) = node by simp [insertTreeEdgeMemory]]
        exact Or.inr ⟨k,by omega,Or.inl ⟨rfl,rfl⟩⟩
      by_cases hxv : x = v k
      · subst x
        rw [show insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
            (adj+v k) = node+3 by simp [insertTreeEdgeMemory,hxu]]
        exact Or.inr ⟨k,by omega,Or.inr ⟨rfl,rfl⟩⟩
      have hsame : insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
          (adj+x) = prev (adj+x) := by
        unfold insertTreeEdgeMemory node
        repeat
          first | rw [ite_eq_right (by omega)] | rfl
      rw [hsame]
      exact (hheads x hx).imp id (treeIncidenceFor_mono (Nat.le_succ _))
    · intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with hieq | hi'
      · subst i
        have h2 : insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
            (node+2) = prev (adj+u k) := by
          unfold insertTreeEdgeMemory node
          repeat
            first | rw [ite_eq_right (by omega)] | rw [ite_eq_left (by omega)] | rfl
        have h5 : insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
            (node+5) = prev (adj+v k) := by
          unfold insertTreeEdgeMemory node
          repeat
            first | rw [ite_eq_right (by omega)] | rw [ite_eq_left (by omega)] | rfl
        dsimp [node,prev] at h2 h5
        rw [h2,h5]
        exact ⟨hheads (u k) hu,hheads (v k) hv'⟩
      · obtain ⟨hui,hvi,_⟩ := hv i hi
        have hsame (j : ℕ) (hj : j ≤ 5) :
            insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
              (records+6*i+j) = prev (records+6*i+j) := by
          unfold insertTreeEdgeMemory node
          repeat
            first | rw [ite_eq_right (by omega)] | rfl
        rw [hsame 2 (by decide),hsame 5 (by decide)]
        exact hlinks i hi'

/-- Each record stores the endpoint opposite its owner and the original
edge index, and subsequent insertions preserve both fields. -/
theorem originalTreeAdjacencyMemory_fields (mem : ℕ → ℕ) (adj records n : ℕ)
    (u v e : ℕ → ℕ) (ha : adj+n ≤ records) (k : ℕ)
    (hv : ∀ i < k, u i < n ∧ v i < n) :
    let out := originalTreeAdjacencyMemory mem adj records u v e k
    ∀ i < k, out (records+6*i) = v i ∧ out (records+6*i+1) = e i ∧
      out (records+6*i+3) = u i ∧ out (records+6*i+4) = e i := by
  induction k with
  | zero => exact fun i hi => (Nat.not_lt_zero i hi).elim
  | succ k ih =>
    obtain ⟨hu,hv'⟩ := hv k (by omega)
    have hu' : adj+u k < records := by omega
    have hv'' : adj+v k < records := by omega
    simp only [originalTreeAdjacencyMemory]
    intro i hi
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with hik | hik
    · subst i
      unfold insertTreeEdgeMemory
      repeat
        first
        | constructor
        | rw [ite_eq_right (by omega)]
        | rw [ite_eq_left (by omega)]
        | rfl
    · have hsame (j : ℕ) (hj : j ≤ 4) :
          insertTreeEdgeMemory (originalTreeAdjacencyMemory mem adj records u v e k)
            (adj+u k) (adj+v k) (records+6*k) (u k) (v k) (e k) (records+6*i+j) =
          originalTreeAdjacencyMemory mem adj records u v e k (records+6*i+j) := by
        unfold insertTreeEdgeMemory
        repeat
          first | rw [ite_eq_right (by omega)] | rfl
      rw [← Nat.add_zero (records+6*i),hsame 0 (by decide),hsame 1 (by decide),
        hsame 3 (by decide),hsame 4 (by decide),Nat.add_zero]
      exact ih (fun j hj => hv j (by omega)) i hik

/-- The record addresses for a vertex, in reverse insertion order. -/
def treeIncidenceList (records : ℕ) (u v : ℕ → ℕ) (vertex : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 =>
    let rest := treeIncidenceList records u v vertex k
    if vertex = u k then (records+6*k) :: rest
    else if vertex = v k then (records+6*k+3) :: rest else rest

/-- A list of record addresses is realized by the pointer and the next
fields in memory, with zero marking the end. -/
def TreeRecordsAt (mem : ℕ → ℕ) : ℕ → List ℕ → Prop
  | ptr, [] => ptr = 0
  | ptr, record::rest => ptr = record ∧ TreeRecordsAt mem (mem (record+2)) rest

private theorem TreeRecordsAt.congr {mem out : ℕ → ℕ} {ptr : ℕ} {l : List ℕ}
    (h : TreeRecordsAt mem ptr l) (he : ∀ a ∈ l, out (a+2) = mem (a+2)) :
    TreeRecordsAt out ptr l := by
  induction l generalizing ptr with
  | nil => exact h
  | cons a l ih =>
    obtain ⟨hp,ht⟩ := h
    refine ⟨hp,?_⟩
    rw [he a (by simp)]
    exact ih ht (fun x hx => he x (List.mem_cons_of_mem _ hx))

/-- Every incidence address lies inside the allocated record region. -/
theorem treeIncidenceList_bounds {records vertex k a : ℕ} {u v : ℕ → ℕ}
    (ha : a ∈ treeIncidenceList records u v vertex k) :
    records ≤ a ∧ a+2 < records+6*k := by
  induction k with
  | zero => simp [treeIncidenceList] at ha
  | succ k ih =>
    rw [treeIncidenceList] at ha
    split at ha
    · rcases List.mem_cons.mp ha with rfl | h
      · omega
      · obtain ⟨_,_⟩ := ih h
        omega
    · split at ha
      · rcases List.mem_cons.mp ha with rfl | h
        · omega
        · obtain ⟨_,_⟩ := ih h
          omega
      · obtain ⟨_,_⟩ := ih ha
        omega

/-- Starting from zeroed heads, following next pointers reads the entire
reverse insertion list of each vertex. -/
theorem originalTreeAdjacencyMemory_recordsAt (mem : ℕ → ℕ) (adj records n : ℕ)
    (u v e : ℕ → ℕ) (ha : adj+n ≤ records) (hzero : ∀ x < n, mem (adj+x) = 0)
    (k : ℕ) (hv : ∀ i < k, u i < n ∧ v i < n ∧ u i ≠ v i) :
    ∀ x < n, let out := originalTreeAdjacencyMemory mem adj records u v e k
      TreeRecordsAt out (out (adj+x)) (treeIncidenceList records u v x k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    intro x hx
    obtain ⟨hu,hv',hne⟩ := hv k (by omega)
    let prev := originalTreeAdjacencyMemory mem adj records u v e k
    let node := records+6*k
    let out := insertTreeEdgeMemory prev (adj+u k) (adj+v k) node (u k) (v k) (e k)
    have hprev : TreeRecordsAt prev (prev (adj+x)) (treeIncidenceList records u v x k) :=
      ih (fun i hi => hv i (by omega)) x hx
    have hold : TreeRecordsAt out (prev (adj+x)) (treeIncidenceList records u v x k) :=
      hprev.congr fun a h => by
        obtain ⟨_,_⟩ := treeIncidenceList_bounds h
        unfold out insertTreeEdgeMemory node
        repeat
          first | rw [ite_eq_right (by omega)] | rfl
    change TreeRecordsAt out (out (adj+x)) (treeIncidenceList records u v x (k+1))
    rw [treeIncidenceList]
    by_cases hxu : x = u k
    · rw [ite_eq_left hxu]
      have hhead : out (adj+x) = node := by simp [out,insertTreeEdgeMemory,hxu]
      have hlink : out (node+2) = prev (adj+x) := by
        unfold out insertTreeEdgeMemory node
        rw [hxu]
        repeat
          first | rw [ite_eq_right (by omega)] | rw [ite_eq_left (by omega)] | rfl
      exact ⟨hhead,hlink ▸ hold⟩
    · rw [ite_eq_right hxu]
      by_cases hxv : x = v k
      · rw [ite_eq_left hxv]
        have hhead : out (adj+x) = node+3 := by simp [out,insertTreeEdgeMemory,hxv,Ne.symm hne]
        have hlink : out (node+3+2) = prev (adj+x) := by
          unfold out insertTreeEdgeMemory node
          rw [hxv]
          repeat
            first | rw [ite_eq_right (by omega)] | rw [ite_eq_left (by omega)] | rfl
        exact ⟨hhead,hlink ▸ hold⟩
      · rw [ite_eq_right hxv]
        have hhead : out (adj+x) = prev (adj+x) := by
          unfold out insertTreeEdgeMemory node
          repeat
            first | rw [ite_eq_right (by omega)] | rfl
        rwa [hhead]

end MinCostFlow.LastLevelProgram
