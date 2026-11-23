module

public import MinCostFlow.LastLevelProgram.TraversalAdjacency
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Recording a newly discovered tree vertex

Write the parent, incoming edge and depth into indexed tables, and
append the child to the parent-first discovery order.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Arguments are the four destinations, the parent, incoming edge,
parent depth, and child. -/
def recordTreeChild : Stmt :=
  .store (.reg 0) (.reg 4) ;;
  .store (.reg 1) (.reg 5) ;;
  .store (.reg 2) (.bin .add (.reg 6) (.const 1)) ;;
  .store (.reg 3) (.reg 7)

/-- A discovery writes the four metadata cells in 17 instructions and
preserves every other cell when the destinations are distinct. -/
theorem recordTreeChild_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (pa ea da oa parent edge depth child : ℕ)
    (haddr : ∀ a ∈ [pa,ea,da,oa], a < 2^w)
    (hdepth : depth+1 < 2^w)
    (hne : pa ≠ ea ∧ pa ≠ da ∧ pa ≠ oa ∧ ea ≠ da ∧ ea ≠ oa ∧ da ≠ oa) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = pa ∧ st.regs 1 = ea ∧
        st.regs 2 = da ∧ st.regs 3 = oa ∧ st.regs 4 = parent ∧ st.regs 5 = edge ∧
        st.regs 6 = depth ∧ st.regs 7 = child)
      recordTreeChild (normalPost fun st =>
        st.mem pa = parent ∧ st.mem ea = edge ∧ st.mem da = depth+1 ∧
        st.mem oa = child ∧
        ∀ a, a ≠ pa → a ≠ ea → a ≠ da → a ≠ oa → st.mem a = mem a)
      (fun _ => 17) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hpa := haddr pa (by simp)
  have hea := haddr ea (by simp)
  have hda := haddr da (by simp)
  have hoa := haddr oa (by simp)
  have hword : 1 < 2^w := by omega
  obtain ⟨he1,he2,he3,he4,he5,he6⟩ := hne
  unfold recordTreeChild
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,he1,he2,he3,he4,he5,he6]
  intro a hp he hd ho
  simp [hp,he,hd,ho]

/-- Inspect an incidence. Register zero is its record address, and
register one is the current vertex's parent. Read the neighbor, edge
index and next pointer into registers two through four. Register five
indicates whether the neighbor is the parent. -/
def inspectTreeIncidence : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 5 (.bin .eq (.reg 2) (.reg 1))

/-- Inspecting an incidence leaves the record and parent in place and
distinguishes the parent from the children of the current vertex. -/
theorem inspectTreeIncidence_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (ptr parent child edge next : ℕ)
    (hw : 2 < 2^w) (hptr : ptr+2 < 2^w)
    (hc : mem ptr = child) (he : mem (ptr+1) = edge) (hn : mem (ptr+2) = next) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = ptr ∧ st.regs 1 = parent)
      inspectTreeIncidence (normalPost fun st =>
        st.mem = mem ∧ st.regs 0 = ptr ∧ st.regs 1 = parent ∧
        st.regs 2 = child ∧ st.regs 3 = edge ∧ st.regs 4 = next ∧
        st.regs 5 = if child = parent then 1 else 0)
      (fun _ => 20) := by
  intro st ω ⟨hm,h0,h1⟩
  have hptr' : ptr+1 < 2^w := by omega
  have hc' : st.mem ptr = child := hm ▸ hc
  have he' : st.mem (ptr+1) = edge := hm ▸ he
  have hn' : st.mem (ptr+2) = next := hm ▸ hn
  unfold inspectTreeIncidence
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,hc,he,hn]

/-- Start the queue with the root, make it its own parent, and
initialize the queue cursors. The depth array starts at zero. -/
def initializeTreeQueue : Stmt :=
  .store (.reg 4) (.reg 5) ;;
  .store (.bin .add (.reg 1) (.reg 5)) (.reg 5) ;;
  .assign 6 (.const 0) ;;
  .assign 7 (.const 1)

/-- Inspect one record in the current vertex's adjacency list. Append
the neighbor to the queue and record its metadata if it is a child. -/
def scanTreeQueueRecord : Stmt :=
  .assign 12 (.load (.reg 9)) ;;
  .cond (.bin .eq (.reg 12) (.reg 10)) .nop
    (.store (.bin .add (.reg 1) (.reg 12)) (.reg 8) ;;
     .store (.bin .add (.reg 2) (.reg 12)) (.load (.bin .add (.reg 9) (.const 1))) ;;
     .store (.bin .add (.reg 3) (.reg 12)) (.bin .add (.reg 11) (.const 1)) ;;
     .store (.bin .add (.reg 4) (.reg 7)) (.reg 12) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1))) ;;
  .assign 9 (.load (.bin .add (.reg 9) (.const 2)))

/-- Read the next vertex and its adjacency head, parent, and depth. -/
def readTreeQueueVertex : Stmt :=
  .assign 8 (.load (.bin .add (.reg 4) (.reg 6))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 3) (.reg 8)))

/-- Dequeue a vertex, read its parent and depth, then scan its incidences. -/
def scanTreeQueueVertex : Stmt :=
  readTreeQueueVertex ;;
  .loop (.reg 9) scanTreeQueueRecord ;;
  .assign 6 (.bin .add (.reg 6) (.const 1))

/-- Traverse the rooted tree in discovery order. Input registers are
the adjacency heads, parents, parent edges, depths, queue, and root. -/
def traverseTreeQueue : Stmt :=
  initializeTreeQueue ;; .loop (.bin .lt (.reg 6) (.reg 7)) scanTreeQueueVertex

/-- Initialization puts the root first and preserves every other cell. -/
theorem initializeTreeQueue_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (adj parents edges depths queue root : ℕ) (hw : 1 < 2^w) (_hq : queue < 2^w)
    (hp : parents+root < 2^w) (hne : parents+root ≠ queue) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = adj ∧ st.regs 1 = parents ∧
        st.regs 2 = edges ∧ st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 5 = root)
      initializeTreeQueue (normalPost fun st =>
        st.mem queue = root ∧ st.mem (parents+root) = root ∧
        st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
        st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = 0 ∧ st.regs 7 = 1 ∧
        ∀ a, a ≠ queue → a ≠ parents+root → st.mem a = mem a)
      (fun _ => 15) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h5⟩
  unfold initializeTreeQueue
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,h2,h3,h4,Ne.symm hne]
  intro a ha hb
  simp [ha,hb]

/-- The queue read leaves the memory and the queue cursors in place. -/
theorem readTreeQueueVertex_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (adj parents edges depths queue cursor tail current ptr parent depth : ℕ)
    (hq : queue+cursor < 2^w) (ha : adj+current < 2^w)
    (hp : parents+current < 2^w) (hd : depths+current < 2^w)
    (hc : mem (queue+cursor) = current) (hptr : mem (adj+current) = ptr)
    (hpar : mem (parents+current) = parent) (hdepth : mem (depths+current) = depth) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = adj ∧ st.regs 1 = parents ∧
        st.regs 2 = edges ∧ st.regs 3 = depths ∧ st.regs 4 = queue ∧
        st.regs 6 = cursor ∧ st.regs 7 = tail)
      readTreeQueueVertex (normalPost fun st =>
        st.mem = mem ∧ st.regs 0 = adj ∧ st.regs 1 = parents ∧
        st.regs 2 = edges ∧ st.regs 3 = depths ∧ st.regs 4 = queue ∧
        st.regs 6 = cursor ∧ st.regs 7 = tail ∧ st.regs 8 = current ∧
        st.regs 9 = ptr ∧ st.regs 10 = parent ∧ st.regs 11 = depth)
      (fun _ => 23) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h6,h7⟩
  have hc' : st.mem (queue+cursor) = current := hm ▸ hc
  have ht' : st.mem (adj+current) = ptr := hm ▸ hptr
  have hp' : st.mem (parents+current) = parent := hm ▸ hpar
  have hd' : st.mem (depths+current) = depth := hm ▸ hdepth
  unfold readTreeQueueVertex
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,h2,h3,h4,h6,h7,hc,hptr,hpar,hdepth]

/-- One adjacency scan follows the next pointer and appends a queue
entry exactly when the neighbor differs from the current parent. -/
theorem scanTreeQueueRecord_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (parents edges depths queue tail current ptr parent depth child edge next adj cursor : ℕ)
    (hw : 2 < 2^w) (hptr : ptr+2 < 2^w)
    (hc : mem ptr = child) (he : mem (ptr+1) = edge) (hn : mem (ptr+2) = next)
    (hroom : ∀ a ∈ [parents+child,edges+child,depths+child,queue+tail,depth+1,tail+1], a < 2^w)
    (hsep : ∀ a ∈ [parents+child,edges+child,depths+child,queue+tail],
      a ≠ ptr+1 ∧ a ≠ ptr+2) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
        st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 7 = tail ∧ st.regs 8 = current ∧
        st.regs 9 = ptr ∧ st.regs 10 = parent ∧ st.regs 11 = depth ∧
        st.regs 0 = adj ∧ st.regs 6 = cursor)
      scanTreeQueueRecord (normalPost fun st => st.regs 9 = next ∧
        st.regs 7 = (if child = parent then tail else tail+1) ∧
        st.mem = (if child = parent then mem else
          Function.update (Function.update (Function.update (Function.update mem
            (parents+child) current) (edges+child) edge) (depths+child) (depth+1))
            (queue+tail) child) ∧
        st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧ st.regs 3 = depths ∧
        st.regs 4 = queue ∧ st.regs 6 = cursor ∧ st.regs 8 = current ∧
        st.regs 10 = parent ∧ st.regs 11 = depth)
      (fun _ => 55) := by
  intro st ω ⟨hm,h1,h2,h3,h4,h7,h8,h9,h10,h11,h0,h6⟩
  have hc' : st.mem ptr = child := hm ▸ hc
  have he' : st.mem (ptr+1) = edge := hm ▸ he
  have hn' : st.mem (ptr+2) = next := hm ▸ hn
  have hptr' : ptr+1 < 2^w := by omega
  have hpa := hroom (parents+child) (by simp)
  have hea := hroom (edges+child) (by simp)
  have hda := hroom (depths+child) (by simp)
  have hqa := hroom (queue+tail) (by simp)
  have hd := hroom (depth+1) (by simp)
  have ht := hroom (tail+1) (by simp)
  obtain ⟨hp1,hp2⟩ := hsep (parents+child) (by simp)
  have he2 := (hsep (edges+child) (by simp)).2
  have hd2 := (hsep (depths+child) (by simp)).2
  have hq2 := (hsep (queue+tail) (by simp)).2
  unfold scanTreeQueueRecord
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,h2,h3,h4,h6,h7,h8,h9,h10,h11,hc,he,hn,
    Ne.symm hp1,Ne.symm hp2,Ne.symm he2,Ne.symm hd2,Ne.symm hq2] <;> simp_all

/-- The queue tail and memory after processing one record. -/
def scanTreeQueueModelStep (records : ℕ → ℕ)
    (parents edges depths queue current parent depth : ℕ)
    (state : ℕ × (ℕ → ℕ)) (ptr : ℕ) : ℕ × (ℕ → ℕ) :=
  let child := records ptr
  if child = parent then state else
    (state.1+1, Function.update (Function.update (Function.update (Function.update state.2
      (parents+child) current) (edges+child) (records (ptr+1))) (depths+child) (depth+1))
      (queue+state.1) child)

/-- A scan advances the queue tail once for each nonparent incidence. -/
theorem scanTreeQueueModel_tail (mem : ℕ → ℕ)
    (parents edges depths queue current parent depth : ℕ)
    (records : List ℕ) (start : ℕ × (ℕ → ℕ)) :
    (records.foldl (scanTreeQueueModelStep mem parents edges depths queue current parent depth)
      start).1 = start.1 + (records.filter fun ptr => mem ptr != parent).length := by
  induction records generalizing start with
  | nil => simp
  | cons ptr rest ih =>
    rw [List.foldl_cons, ih]
    by_cases he : mem ptr = parent
    · simp [scanTreeQueueModelStep,he]
    · simp [scanTreeQueueModelStep,he]
      omega

/-- Scan one linked list using immutable incidence records. The scan takes
at most 57 steps per record and writes only below the record region. -/
theorem scanTreeQueueList_triple {w : ℕ} {p : Program}
    (mem initial : ℕ → ℕ) (parents edges depths queue current parent depth adj cursor floor limit start : ℕ)
    (records : List ℕ) (hw : 2 < 2^w) (hd : depth+1 < 2^w)
    (hrecord : ∀ ptr ∈ records, 0 < ptr ∧ floor ≤ ptr ∧ ptr+2 < 2^w)
    (hwrite : ∀ ptr ∈ records, parents+mem ptr < floor ∧ edges+mem ptr < floor ∧
      depths+mem ptr < floor)
    (hqueue : queue+limit < floor) (hfW : floor < 2^w) :
    let step := scanTreeQueueModelStep mem parents edges depths queue current parent depth
    Triple w p (fun st => st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
        st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = cursor ∧
        st.regs 8 = current ∧ st.regs 10 = parent ∧ st.regs 11 = depth ∧
        st.regs 7 + (records.filter fun ptr => mem ptr != parent).length ≤ limit ∧ TreeRecordsAt mem (st.regs 9) records ∧
        (∀ a ≥ floor, st.mem a = mem a) ∧ st.regs 7 = start ∧ st.mem = initial)
      (.loop (.reg 9) scanTreeQueueRecord)
      (normalPost fun st => st.regs 9 = 0 ∧ st.regs 7 ≤ limit ∧
        st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧ st.regs 3 = depths ∧
        st.regs 4 = queue ∧ st.regs 6 = cursor ∧ st.regs 8 = current ∧
        st.regs 10 = parent ∧ st.regs 11 = depth ∧ (∀ a ≥ floor, st.mem a = mem a) ∧
        (st.regs 7,st.mem) = records.foldl step (start,initial))
      (fun _ => 57*records.length+2) := by
  intro step
  let Inv := fun xs (st : State) =>
    st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
    st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = cursor ∧
    st.regs 8 = current ∧ st.regs 10 = parent ∧ st.regs 11 = depth ∧
    st.regs 7 + (xs.filter fun ptr => mem ptr != parent).length ≤ limit ∧ TreeRecordsAt mem (st.regs 9) xs ∧
    (∀ a ≥ floor, st.mem a = mem a) ∧
    (∀ ptr ∈ xs, ptr ∈ records) ∧
    xs.foldl step (st.regs 7,st.mem) = records.foldl step (start,initial)
  have loop := Triple.loop_list (p := p) (e := .reg 9) (body := scanTreeQueueRecord)
    (Inv := Inv) (Q := normalPost fun st => st.regs 9 = 0 ∧ st.regs 7 ≤ limit ∧
      st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧ st.regs 3 = depths ∧
      st.regs 4 = queue ∧ st.regs 6 = cursor ∧ st.regs 8 = current ∧
      st.regs 10 = parent ∧ st.regs 11 = depth ∧ (∀ a ≥ floor, st.mem a = mem a) ∧
        (st.regs 7,st.mem) = records.foldl step (start,initial))
    (fun _ => 55)
    (fun st ⟨h0,h1,h2,h3,h4,h6,h8,h10,h11,ht,hz,hf,_,hmodel⟩ =>
      ⟨by simp [Expr.eval,show st.regs 9 = 0 from hz],
        hz,by simpa using ht,h0,h1,h2,h3,h4,h6,h8,h10,h11,hf,hmodel⟩)
    (fun ptr xs st ⟨h0,h1,h2,h3,h4,h6,h8,h10,h11,ht,hchain,hf,hmem,hmodel⟩ => by
      obtain ⟨hp,hnext⟩ := hchain
      have hin := hmem ptr (by simp)
      obtain ⟨hpos,hfloor,hptr⟩ := hrecord ptr hin
      obtain ⟨hpB,heB,hdB⟩ := hwrite ptr hin
      let tail := st.regs 7
      let child := mem ptr
      have ht' : (if child = parent then tail else tail+1) +
          (xs.filter fun ptr => mem ptr != parent).length ≤ limit := by
        by_cases he : child = parent
        · simpa [List.filter_cons,child,show mem ptr = parent from he,tail] using ht
        · simpa [List.filter_cons,child,show mem ptr ≠ parent from he,tail,
            Nat.add_assoc,Nat.add_comm 1] using ht
      have htailLimit : tail ≤ limit := by
        change tail + _ ≤ limit at ht
        omega
      have hqB : queue+tail < floor := by omega
      have htW : tail+1 < 2^w := (show tail+1 ≤ floor by omega).trans_lt hfW
      refine ⟨ptr,by simp [Expr.eval,hp],Nat.ne_of_gt hpos,?_⟩
      have hstep := scanTreeQueueRecord_triple (p := p) st.mem parents edges depths queue tail
        current ptr parent depth child (mem (ptr+1)) (mem (ptr+2)) adj cursor hw hptr
        (hf ptr hfloor) (hf _ (by omega)) (hf _ (by omega))
        (by
          intro a ha
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          dsimp [child] at ha
          rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
        (by
          intro a ha
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          dsimp [child] at ha
          rcases ha with rfl|rfl|rfl|rfl <;> omega)
      refine hstep.conseq ?_ ?_ (fun _ _ => le_rfl)
      · intro s hs
        subst s
        exact ⟨rfl,h1,h2,h3,h4,rfl,h8,hp,h10,h11,h0,h6⟩
      · intro o out hpost
        cases o with
        | returned => exact False.elim hpost
        | normal =>
          obtain ⟨hn,htail,hm,ho0,ho1,ho2,ho3,ho4,ho6,ho8,ho10,ho11⟩ := hpost
          refine ⟨ho0,ho1,ho2,ho3,ho4,ho6,ho8,ho10,ho11,?_,hn ▸ hnext,?_,?_,?_⟩
          · rw [htail]
            exact ht'
          · intro a ha
            rw [hm]
            split
            · exact hf _ ha
            · dsimp [child]
              have h1' : a ≠ parents+mem ptr := by omega
              have h2' : a ≠ edges+mem ptr := by omega
              have h3' : a ≠ depths+mem ptr := by omega
              have h4' : a ≠ queue+tail := by omega
              simpa [h1',h2',h3',h4'] using hf _ ha
          · intro a ha
            exact hmem a (List.mem_cons_of_mem _ ha)
          · rw [← hmodel, List.foldl_cons]
            congr 1
            rw [htail,hm]
            by_cases h : child = parent <;> simp [step,scanTreeQueueModelStep,child,h,tail])
    records
  refine loop.conseq (fun _ h => ?_) (fun _ _ h => h) ?_
  · obtain ⟨h0,h1,h2,h3,h4,h6,h8,h10,h11,ht,hc,hf,hs,hm⟩ := h
    exact ⟨h0,h1,h2,h3,h4,h6,h8,h10,h11,ht,hc,hf,fun _ h => h,by rw [hs,hm]⟩
  · intro _ _
    simp [Expr.size,List.sum_replicate]
    omega


/-- Visit a queued vertex, scan its adjacency list, and advance the read
cursor. The postcondition gives the exact resulting queue tail and memory. -/
theorem scanTreeQueueVertex_triple {w : ℕ} {p : Program}
    (mem immutable : ℕ → ℕ)
    (adj parents edges depths queue cursor tail current ptr parent depth floor limit : ℕ)
    (records : List ℕ) (hw : 2 < 2^w)
    (hq : queue+cursor < 2^w) (ha : adj+current < 2^w)
    (hp : parents+current < 2^w) (hd : depths+current < 2^w)
    (hc : mem (queue+cursor) = current) (hptr : mem (adj+current) = ptr)
    (hpar : mem (parents+current) = parent) (hdepth : mem (depths+current) = depth)
    (hnext : cursor+1 < 2^w) (hdnext : depth+1 < 2^w)
    (hrecord : ∀ q ∈ records, 0 < q ∧ floor ≤ q ∧ q+2 < 2^w)
    (hwrite : ∀ q ∈ records, parents+immutable q < floor ∧ edges+immutable q < floor ∧
      depths+immutable q < floor)
    (hqueue : queue+limit < floor) (hfW : floor < 2^w)
    (hchain : TreeRecordsAt immutable ptr records)
    (hlimit : tail+(records.filter fun ptr => immutable ptr != parent).length ≤ limit) (hframe : ∀ a ≥ floor, mem a = immutable a) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = adj ∧ st.regs 1 = parents ∧
        st.regs 2 = edges ∧ st.regs 3 = depths ∧ st.regs 4 = queue ∧
        st.regs 6 = cursor ∧ st.regs 7 = tail)
      scanTreeQueueVertex (normalPost fun st =>
        st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
        st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = cursor+1 ∧
        st.regs 7 ≤ limit ∧ (∀ a ≥ floor, st.mem a = immutable a) ∧
        (st.regs 7,st.mem) = records.foldl
          (scanTreeQueueModelStep immutable parents edges depths queue current parent depth)
          (tail,mem))
      (fun _ => 57*records.length+31) := by
  refine Triple.seq_normal (T₂ := fun _ => 57*records.length+7)
    (readTreeQueueVertex_triple mem adj parents edges depths queue cursor tail current ptr parent depth
      hq ha hp hd hc hptr hpar hdepth) ?_ (fun _ _ _ _ => ?_)
  · refine Triple.seq_normal (T₂ := fun _ => 4)
      ((scanTreeQueueList_triple (p := p) immutable mem parents edges depths queue current parent depth
        adj cursor floor limit tail records hw hdnext hrecord hwrite hqueue hfW).conseq
        ?_ (fun _ _ h => h) (fun _ _ => le_rfl)) ?_ (fun _ _ _ _ => ?_)
    · intro st ⟨hm,h0,h1,h2,h3,h4,h6,h7,h8,h9,h10,h11⟩
      exact ⟨h0,h1,h2,h3,h4,h6,h8,h10,h11,by rwa [h7],by rwa [h9],
        by rwa [hm],h7,hm⟩
    · intro st ω ⟨_,ht,h0,h1,h2,h3,h4,h6,_,_,_,hf,hm⟩
      let out := { st with regs := Function.update st.regs 6 (cursor+1) }
      have hrun : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1))) st .normal out 4 :=
        runs_assign_iff.mpr ⟨cursor+1,by eval_expr,rfl,rfl,rfl⟩
      exact ⟨.normal,out,4,hrun,⟨h0,h1,h2,h3,h4,by simp [out],ht,hf,hm⟩,le_rfl⟩
    · exact le_rfl
  · omega


/-- The scan preserves the queue prefix and appends precisely the
nonparent neighbors, in the order of the incidence records. -/
theorem scanTreeQueueModel_append (mem : ℕ → ℕ)
    (parents edges depths queue current parent depth : ℕ)
    (records : List ℕ) (start : ℕ × (ℕ → ℕ))
    (hmeta : ∀ ptr ∈ records, parents+mem ptr < queue ∧ edges+mem ptr < queue ∧
      depths+mem ptr < queue) :
    let out := records.foldl
      (scanTreeQueueModelStep mem parents edges depths queue current parent depth) start
    (∀ j < start.1, out.2 (queue+j) = start.2 (queue+j)) ∧
    ListAt out.2 (queue+start.1) ((records.filter fun ptr => mem ptr != parent).map mem) := by
  induction records generalizing start with
  | nil => exact ⟨fun _ _ => rfl,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | cons ptr rest ih =>
    have hm := hmeta ptr (by simp)
    have hrest : ∀ q ∈ rest, parents+mem q < queue ∧ edges+mem q < queue ∧
        depths+mem q < queue := fun q h => hmeta q (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    by_cases he : mem ptr = parent
    · simpa [scanTreeQueueModelStep,he] using ih start hrest
    · let child := mem ptr
      let updated := Function.update (Function.update (Function.update (Function.update start.2
        (parents+child) current) (edges+child) (mem (ptr+1))) (depths+child) (depth+1))
        (queue+start.1) child
      let more := rest.filter (fun q => mem q != parent)
      let out := rest.foldl
        (scanTreeQueueModelStep mem parents edges depths queue current parent depth) (start.1+1,updated)
      obtain ⟨hold,hnew⟩ := ih (start.1+1,updated) hrest
      have hp (j : ℕ) (hj : j < start.1) : updated (queue+j) = start.2 (queue+j) := by
        obtain ⟨ha,hb,hc⟩ := hm
        have hpa : queue+j ≠ parents+child := by dsimp [child]; omega
        have hea : queue+j ≠ edges+child := by dsimp [child]; omega
        have hda : queue+j ≠ depths+child := by dsimp [child]; omega
        have hqa : queue+j ≠ queue+start.1 := by omega
        unfold updated
        rw [Function.update_of_ne hqa,Function.update_of_ne hda,
          Function.update_of_ne hea,Function.update_of_ne hpa]
      have hcell : out.2 (queue+start.1) = child := by
        rw [hold _ (Nat.lt_succ_self _)]
        simp [updated]
      simp [scanTreeQueueModelStep,he]
      change (∀ j < start.1, out.2 (queue+j) = start.2 (queue+j)) ∧
        ListAt out.2 (queue+start.1) (child::more.map mem)
      refine ⟨fun j hj => (hold j (hj.trans (Nat.lt_succ_self _))).trans (hp j hj),?_⟩
      intro j hj
      cases j with
      | zero => simpa using hcell
      | succ j =>
        have hj' : j < (more.map mem).length := by simpa using hj
        have hh := hnew j hj'
        change out.2 (queue+(start.1+1)+j) = _ at hh
        simpa [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 j] using hh

/-- A scan preserves cells outside its queue append range and the metadata
cells of the children that it discovers. -/
theorem scanTreeQueueModel_frame (mem : ℕ → ℕ)
    (parents edges depths queue current parent depth : ℕ)
    (records : List ℕ) (start : ℕ × (ℕ → ℕ)) (a : ℕ)
    (hqueue : a < queue+start.1 ∨
      queue+start.1+(records.filter fun ptr => mem ptr != parent).length ≤ a)
    (hmeta : ∀ ptr ∈ records, mem ptr ≠ parent →
      a ≠ parents+mem ptr ∧ a ≠ edges+mem ptr ∧ a ≠ depths+mem ptr) :
    (records.foldl (scanTreeQueueModelStep mem parents edges depths queue current parent depth)
      start).2 a = start.2 a := by
  induction records generalizing start with
  | nil => rfl
  | cons ptr rest ih =>
    have hrest : ∀ ptr ∈ rest, mem ptr ≠ parent →
        a ≠ parents+mem ptr ∧ a ≠ edges+mem ptr ∧ a ≠ depths+mem ptr :=
      fun q h => hmeta q (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    by_cases he : mem ptr = parent
    · simp [scanTreeQueueModelStep,he]
      exact ih start (by simpa [he] using hqueue) hrest
    · let next := scanTreeQueueModelStep mem parents edges depths queue current parent depth start ptr
      have ht : next.1 = start.1+1 := by simp [next,scanTreeQueueModelStep,he]
      have hq : a < queue+next.1 ∨
          queue+next.1+(rest.filter fun ptr => mem ptr != parent).length ≤ a := by
        rw [ht]
        simpa [he,Nat.add_assoc,Nat.add_comm 1] using
          (show a < queue+start.1+1 ∨
             queue+start.1+((ptr::rest).filter fun ptr => mem ptr != parent).length ≤ a by
            rcases hqueue with h | h
            · exact Or.inl (by omega)
            · exact Or.inr h)
      change (rest.foldl _ next).2 a = _
      rw [ih next hq hrest]
      obtain ⟨ha,hb,hc⟩ := hmeta ptr (by simp) he
      have hd : a ≠ queue+start.1 := by
        simp [he] at hqueue
        rcases hqueue <;> omega
      dsimp [next,scanTreeQueueModelStep]
      rw [ite_eq_right he]
      exact (Function.update_of_ne hd _ _).trans
        ((Function.update_of_ne hc _ _).trans
          ((Function.update_of_ne hb _ _).trans (Function.update_of_ne ha _ _)))

/-- Once a child is appended, its metadata survives the remaining scan
when no later discovery writes any of its three cells. -/
theorem scanTreeQueueModel_childFields (mem : ℕ → ℕ)
    (parents edges depths queue current parent depth ptr : ℕ)
    (before after : List ℕ) (start : ℕ × (ℕ → ℕ))
    (hne : mem ptr ≠ parent)
    (hsep : parents+mem ptr ≠ edges+mem ptr ∧ parents+mem ptr ≠ depths+mem ptr ∧
      edges+mem ptr ≠ depths+mem ptr)
    (hqueue : parents+mem ptr < queue ∧ edges+mem ptr < queue ∧ depths+mem ptr < queue)
    (hafter : ∀ a ∈ [parents+mem ptr,edges+mem ptr,depths+mem ptr],
      ∀ q ∈ after, mem q ≠ parent →
        a ≠ parents+mem q ∧ a ≠ edges+mem q ∧ a ≠ depths+mem q) :
    let out := (before ++ ptr::after).foldl
      (scanTreeQueueModelStep mem parents edges depths queue current parent depth) start
    out.2 (parents+mem ptr) = current ∧ out.2 (edges+mem ptr) = mem (ptr+1) ∧
      out.2 (depths+mem ptr) = depth+1 := by
  let step := scanTreeQueueModelStep mem parents edges depths queue current parent depth
  let mid := before.foldl step start
  let next := step mid ptr
  let a := parents+mem ptr
  let b := edges+mem ptr
  let c := depths+mem ptr
  have preserve (d : ℕ) (hd : d ∈ [a,b,c]) (hq : d < queue) :
      (after.foldl step next).2 d = next.2 d :=
    scanTreeQueueModel_frame mem parents edges depths queue current parent depth after next d
      (Or.inl (hq.trans_le (Nat.le_add_right _ _))) (hafter d hd)
  simp only [List.foldl_append,List.foldl_cons]
  change (after.foldl step next).2 a = current ∧
    (after.foldl step next).2 b = mem (ptr+1) ∧ (after.foldl step next).2 c = depth+1
  rw [preserve a (by simp) hqueue.1,preserve b (by simp) hqueue.2.1,
    preserve c (by simp) hqueue.2.2]
  have ha : a ≠ queue+mid.1 := by change parents+mem ptr ≠ _; omega
  have hb : b ≠ queue+mid.1 := by change edges+mem ptr ≠ _; omega
  have hc : c ≠ queue+mid.1 := by change depths+mem ptr ≠ _; omega
  change a ≠ b ∧ a ≠ c ∧ b ≠ c at hsep
  obtain ⟨hab,hac,hbc⟩ := hsep
  have he : next.2 = Function.update (Function.update (Function.update (Function.update
      mid.2 a current) b (mem (ptr+1))) c (depth+1)) (queue+mid.1) (mem ptr) := by
    simp [next,step,scanTreeQueueModelStep,hne,a,b,c]
  rw [he,Function.update_of_ne ha,Function.update_of_ne hb,Function.update_of_ne hc,
    Function.update_of_ne hac,Function.update_of_ne hbc,Function.update_of_ne hab]
  simp

/-- The outer loop consumes a list of vertex visits. The cost charges
each visited adjacency list separately, so the total is linear in the
number of vertices and records scanned. -/
theorem traverseTreeQueueLoop_triple {w : ℕ} {p : Program}
    (degrees : List ℕ) (Inv : List ℕ → State → Prop) (hw : 1 < 2^w)
    (hdone : ∀ st, Inv [] st → st.regs 7 ≤ st.regs 6)
    (hvisit : ∀ d ds st, Inv (d::ds) st → st.regs 6 < st.regs 7 ∧
      Triple w p (fun s => s = st) scanTreeQueueVertex (normalPost (Inv ds))
        (fun _ => 57*d+31)) :
    Triple w p (Inv degrees) (.loop (.bin .lt (.reg 6) (.reg 7)) scanTreeQueueVertex)
      (normalPost (Inv []))
      (fun _ => 57*degrees.sum + 35*degrees.length + 4) := by
  have hloop := Triple.loop_list (w := w) (p := p) (e := .bin .lt (.reg 6) (.reg 7))
    (body := scanTreeQueueVertex) (Inv := Inv) (Q := normalPost (Inv []))
    (fun d => 57*d+31)
    (fun st hs => by
      have hnot := Nat.not_lt.mpr (hdone st hs)
      exact ⟨by simp [Expr.eval,BinOp.eval,hnot],hs⟩)
    (fun d ds st hs => by
      obtain ⟨hlt,ht⟩ := hvisit d ds st hs
      refine ⟨1,by simp [Expr.eval,BinOp.eval,hlt,hw],by decide,?_⟩
      exact ht.conseq (fun _ h => h) (fun o _ h => by cases o <;> exact h) (fun _ _ => le_rfl))
    degrees
  have hsum (ds : List ℕ) : (ds.map fun d => 57*d+31).sum = 57*ds.sum+31*ds.length := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
      omega
  exact hloop.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => by
    simp only [hsum,Expr.size]
    omega)
/-- A machine visit moves the current vertex past the read cursor and
extends the in-memory queue by exactly its nonparent neighbors. -/
theorem scanTreeQueueVertex_append {w : ℕ} {p : Program}
    (mem immutable : ℕ → ℕ) (adj parents edges depths queue current ptr parent depth floor limit : ℕ)
    (done todo records : List ℕ) (hw : 2 < 2^w)
    (hq : queue+done.length < 2^w) (ha : adj+current < 2^w)
    (hp : parents+current < 2^w) (hd : depths+current < 2^w)
    (hlist : ListAt mem queue (done++current::todo))
    (hptr : mem (adj+current) = ptr)
    (hpar : mem (parents+current) = parent) (hdepth : mem (depths+current) = depth)
    (hnext : done.length+1 < 2^w) (hdnext : depth+1 < 2^w)
    (hrecord : ∀ q ∈ records, 0 < q ∧ floor ≤ q ∧ q+2 < 2^w)
    (hmeta : ∀ q ∈ records, parents+immutable q < queue ∧ edges+immutable q < queue ∧
      depths+immutable q < queue)
    (hqueue : queue+limit < floor) (hfW : floor < 2^w)
    (hchain : TreeRecordsAt immutable ptr records)
    (hlimit : (done++current::todo).length +
      (records.filter fun ptr => immutable ptr != parent).length ≤ limit)
    (hframe : ∀ a ≥ floor, mem a = immutable a) :
    let old := done++current::todo
    let children := (records.filter fun ptr => immutable ptr != parent).map immutable
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = adj ∧ st.regs 1 = parents ∧
        st.regs 2 = edges ∧ st.regs 3 = depths ∧ st.regs 4 = queue ∧
        st.regs 6 = done.length ∧ st.regs 7 = old.length)
      scanTreeQueueVertex (normalPost fun st =>
        st.regs 0 = adj ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧
        st.regs 3 = depths ∧ st.regs 4 = queue ∧ st.regs 6 = (done++[current]).length ∧
        st.regs 7 = (old++children).length ∧ ListAt st.mem queue (old++children) ∧
        (∀ a ≥ floor, st.mem a = immutable a) ∧
        (st.regs 7,st.mem) = records.foldl
          (scanTreeQueueModelStep immutable parents edges depths queue current parent depth)
          (old.length,mem))
      (fun _ => 57*records.length+31) := by
  intro old children
  have hc : mem (queue+done.length) = current := by
    have hh := (listAt_append.mp hlist).2 0 (by simp)
    simpa using hh
  have hwrite (q : ℕ) (hq : q ∈ records) :
      parents+immutable q < floor ∧ edges+immutable q < floor ∧ depths+immutable q < floor := by
    obtain ⟨h₁,h₂,h₃⟩ := hmeta q hq
    exact ⟨by omega,by omega,by omega⟩
  refine (scanTreeQueueVertex_triple (p := p) mem immutable adj parents edges depths queue
    done.length old.length current ptr parent depth floor limit records hw hq ha hp hd hc hptr
    hpar hdepth hnext hdnext hrecord hwrite hqueue hfW hchain hlimit hframe).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o out h
  cases o with
  | returned => exact h
  | normal =>
    obtain ⟨h0,h1,h2,h3,h4,h6,_,hf,hm⟩ := h
    have h7 := (congrArg Prod.fst hm).trans
      (scanTreeQueueModel_tail immutable parents edges depths queue current parent depth
        records (old.length,mem))
    have ⟨hkeep,happend⟩ := scanTreeQueueModel_append immutable parents edges depths queue
      current parent depth records (old.length,mem) hmeta
    have he := congrArg Prod.snd hm
    change out.mem = _ at he
    refine ⟨h0,h1,h2,h3,h4,by simpa using h6,?_,?_,hf,hm⟩
    · simpa [children, List.length_append] using h7
    · apply listAt_append.mpr
      refine ⟨?_,?_⟩
      · intro j hj
        rw [he,hkeep j hj]
        exact hlist j hj
      · rw [he]
        exact happend

/-- The queue scan preserves every cell before the parent table when
the remaining traversal arrays are above it. -/
theorem scanTreeQueueModel_prefix (mem : ℕ → ℕ)
    (parents edges depths queue current parent depth : ℕ)
    (records : List ℕ) (start : ℕ × (ℕ → ℕ))
    (he : parents ≤ edges) (hd : parents ≤ depths) (hq : parents ≤ queue)
    (a : ℕ) (ha : a < parents) :
    (records.foldl (scanTreeQueueModelStep mem parents edges depths queue current parent depth)
      start).2 a = start.2 a := by
  apply scanTreeQueueModel_frame
  · exact Or.inl (ha.trans_le (hq.trans (Nat.le_add_right _ _)))
  · intro ptr _ _
    exact ⟨by omega,by omega,by omega⟩

end MinCostFlow.LastLevelProgram
