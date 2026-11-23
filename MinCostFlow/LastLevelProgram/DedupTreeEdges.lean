module

public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Removing repeated selected edge indices

Use a zero-initialized mark array indexed by the compact edge
indices. Append an edge to the output only on its first occurrence.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Read the selected edge, then mark and append it if it is new.
Registers zero, one, and two are the source, marks, and output bases.
Register four is the output count, and register five the input index. -/
def dedupTreeEdgeStep : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
  .cond (.load (.bin .add (.reg 1) (.reg 6))) .nop
    (.store (.bin .add (.reg 1) (.reg 6)) (.const 1) ;;
     .store (.bin .add (.reg 2) (.reg 4)) (.reg 6) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

/-- Register three is the number of selected indices. -/
def dedupTreeEdges : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 3) dedupTreeEdgeStep

/-- One scan step implements the first-occurrence rule in constant time. -/
theorem dedupTreeEdgeStep_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (source marks dest count size i edge : ℕ)
    (hword : 1 < 2^w) (hsrc : source+i < 2^w) (hmark : marks+edge < 2^w)
    (hdest : dest+size < 2^w) (hsize : size+1 < 2^w)
    (hread : mem (source+i) = edge) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = source ∧ st.regs 1 = marks ∧
        st.regs 2 = dest ∧ st.regs 3 = count ∧ st.regs 4 = size ∧ st.regs 5 = i)
      dedupTreeEdgeStep (normalPost fun st =>
        st.regs 0 = source ∧ st.regs 1 = marks ∧ st.regs 2 = dest ∧
        st.regs 3 = count ∧ st.regs 5 = i ∧
        st.regs 4 = (if mem (marks+edge) = 0 then size+1 else size) ∧
        st.mem = (if mem (marks+edge) = 0 then
          Function.update (Function.update mem (marks+edge) 1) (dest+size) edge else mem))
      (fun _ => 31) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h5⟩
  have hread' : st.mem (source+i) = edge := hm ▸ hread
  have hmark' : st.mem (marks+edge) = mem (marks+edge) := congrFun hm _
  unfold dedupTreeEdgeStep
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  wram_run
  all_goals simp [normalPost,Expr.size,hm,h0,h1,h2,h3,h4,h5,hread] <;> simp_all


/-- The scan with an empty output and zero marks produces a duplicate-free
list with the same selected edge set. The source array is preserved. -/
theorem dedupTreeEdges_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (pos source marks dest m count : ℕ) (edge : ℕ → ℕ)
    (hw : 1 < 2^w) (hc : count+1 < 2^w)
    (hs : source+count ≤ marks) (hm : marks+m ≤ dest) (hd : dest+count < 2^w)
    (hread : ∀ i < count, mem (source+i) = edge i ∧ edge i < m)
    (hz : ∀ e < m, mem (marks+e) = 0) :
    Triple w p (fun st => st = startState [source,marks,dest,count] mem pos)
      dedupTreeEdges (normalPost fun st =>
        (∀ a, a < marks ∨ dest + count ≤ a → st.mem a = mem a) ∧
        ∃ kept : List ℕ, st.regs 4 = kept.length ∧ kept.length ≤ count ∧ kept.Nodup ∧
          ListAt st.mem dest kept ∧ ∀ e, e ∈ kept ↔ ∃ j < count, edge j = e)
      (fun _ => 40*count+10) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = source ∧ st.regs 1 = marks ∧ st.regs 2 = dest ∧
    st.regs 3 = count ∧ st.regs 5 = i ∧ (∀ a, a < marks ∨ dest + count ≤ a → st.mem a = mem a) ∧
    ∃ kept : List ℕ, st.regs 4 = kept.length ∧ kept.length ≤ i ∧ kept.Nodup ∧
      ListAt st.mem dest kept ∧ (∀ e, e ∈ kept ↔ ∃ j < i, edge j = e) ∧
      ∀ e < m, st.mem (marks+e) ≠ 0 ↔ e ∈ kept
  let mid := { startState [source,marks,dest,count] mem pos with
    regs := Function.update (startState [source,marks,dest,count] mem pos).regs 4 0 }
  have loop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := dedupTreeEdgeStep) (Inv := Inv) (P := fun st => st = mid)
    31 0 count (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr,?_⟩
      refine ⟨rfl,rfl,rfl,rfl,by simp,(fun _ _ => rfl),[],rfl,by simp,by simp,?_,?_,?_⟩
      · intro i hi; exact (Nat.not_lt_zero _ hi).elim
      · simp
      · intro e he; change (mem (marks+e) ≠ 0 ↔ e ∈ ([] : List ℕ)); simp [hz e he])
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hh : st.regs 3 = count := h.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h5,hframe,kept,h4,hsize,hnodup,hlist,hmem,hmarks⟩
      obtain ⟨hsrc,he⟩ := hread i hi
      let size := kept.length
      have hsz : size ≤ i := hsize
      obtain ⟨o,out,c,hr,hpost,hcost⟩ := dedupTreeEdgeStep_triple (p := p)
        st.mem source marks dest count size i (edge i) hw (by omega) (by omega)
        (by omega) (by omega) ((hframe _ (Or.inl (by omega))).trans hsrc) st ω
        ⟨rfl,h0,h1,h2,h3,h4,h5⟩
      cases o with
      | returned => exact False.elim hpost
      | normal =>
        obtain ⟨ho0,ho1,ho2,ho3,ho5,ho4,hoM⟩ := hpost
        refine ⟨.normal,out,c,hr,⟨?_,ho5⟩,hcost⟩
        refine ⟨ho0,ho1,ho2,ho3,by simp,?_,?_⟩
        · intro a ha
          rw [hoM]
          split
          · rw [Function.update_of_ne (by omega : a ≠ dest+size),
              Function.update_of_ne (by omega : a ≠ marks+edge i)]
            exact hframe a ha
          · exact hframe a ha
        · by_cases hnew : st.mem (marks+edge i) = 0
          · have hnot : edge i ∉ kept := fun h => (hmarks _ he).2 h hnew
            rw [ite_eq_left hnew] at ho4 hoM
            refine ⟨kept ++ [edge i],by simpa using ho4,by simpa using Nat.succ_le_succ hsize,
              ?_,?_,?_,?_⟩
            · simp [List.nodup_append,hnodup]
              intro a ha heq
              exact hnot (heq ▸ ha)
            · intro j hj
              by_cases hj' : j < size
              · have heq : (kept ++ [edge i])[j] = kept[j]'hj' := List.getElem_append_left hj'
                rw [hoM,Function.update_of_ne (by omega : dest+j ≠ dest+size),
                  Function.update_of_ne (by omega : dest+j ≠ marks+edge i),heq]
                exact hlist j hj'
              · have hj0 : j = size := by
                  simp only [List.length_append,List.length_singleton] at hj
                  omega
                subst j
                rw [hoM,Function.update_self]
                simp [size]
            · intro e
              simp only [List.mem_append,List.mem_singleton,hmem]
              constructor
              · rintro (⟨j,hj,hjE⟩ | rfl)
                · exact ⟨j,by omega,hjE⟩
                · exact ⟨i,by omega,rfl⟩
              · rintro ⟨j,hj,hjE⟩
                by_cases hji : j = i
                · exact Or.inr (hji ▸ hjE).symm
                · exact Or.inl ⟨j,by omega,hjE⟩
            · intro e hE
              rw [hoM,Function.update_of_ne (by omega : marks+e ≠ dest+size)]
              by_cases heq : e = edge i
              · subst e
                simp
              · rw [Function.update_of_ne (by omega : marks+e ≠ marks+edge i)]
                simp [hmarks e hE,heq]
          · have hseen := (hmarks _ he).1 hnew
            rw [ite_eq_right hnew] at ho4 hoM
            refine ⟨kept,ho4,hsize.trans (Nat.le_succ _),hnodup,?_,?_,?_⟩
            · rwa [hoM]
            · intro e
              constructor
              · intro hh
                obtain ⟨j,hj,hjE⟩ := (hmem e).1 hh
                exact ⟨j,by omega,hjE⟩
              · rintro ⟨j,hj,hjE⟩
                by_cases hji : j = i
                · subst j
                  rwa [← hjE]
                · exact (hmem e).2 ⟨j,by omega,hjE⟩
            · intro e hE
              rw [hoM]
              exact hmarks e hE)
  refine Triple.seq_normal (R := fun st => st = mid) (T₁ := fun _ => 2) ?_
    (loop.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)) ?_
  · intro st ω hst
    subst st
    exact ⟨.normal,mid,2,runs_assign_iff.mpr ⟨0,by eval_expr,rfl,rfl,rfl⟩,rfl,le_rfl⟩
  · intro o st hh
    cases o with
    | returned => exact hh
    | normal =>
      obtain ⟨_,_,_,_,_,hf,kept,hs,hcount,hn,hl,hm,_⟩ := hh
      exact ⟨hf,kept,hs,hcount,hn,hl,hm⟩
  · intro _ _ _ _
    simp [Expr.size,Nat.mul_comm]
    omega
end MinCostFlow.LastLevelProgram
