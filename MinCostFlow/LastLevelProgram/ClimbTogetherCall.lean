module

public import MinCostFlow.LastLevelProgram.ClimbTogether
import WordRAM.Tactic

/-!
# One simultaneous climb on an ancestor table

Read both ancestors in the given row and replace both vertices if
the two ancestors differ.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Address of a vertex in the selected ancestor row. -/
def climbTogetherAddress (vertex : ℕ) : Expr :=
  .bin .add (.bin .add (.reg 0) (.bin .mul (.reg 5) (.reg 1))) (.reg vertex)

/-- Registers zero and one give the table base and width. Register five
selects the row, and registers three and four hold the vertices. -/
def climbTogetherBody : Stmt :=
  .assign 6 (.load (climbTogetherAddress 3)) ;;
  .assign 7 (.load (climbTogetherAddress 4)) ;;
  .cond (.bin .eq (.reg 6) (.reg 7)) .nop
    (.assign 3 (.reg 6) ;; .assign 4 (.reg 7))

/-- One descending jump costs at most 29 steps and leaves memory and the
table arguments intact. -/
theorem climbTogetherBody_triple {w : ℕ} {p : Program}
    (base n i u v limit index : ℕ) (parent mem : ℕ → ℕ)
    (hword : 1 < 2^w) (hu : u < n) (hv : v < n)
    (hroom : base+(i+1)*n < 2^w)
    (hparent : ∀ x < n, parent x < n) :
    Triple w p (fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 5 = i ∧
      st.regs 3 = u ∧ st.regs 4 = v ∧ st.regs 2 = limit ∧ st.regs 8 = index ∧
      st.mem = mem ∧
      ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x)
      climbTogetherBody
      (fun o out => o = .normal ∧
        (out.regs 3,out.regs 4) = climbTogetherStep parent i (u,v) ∧ out.mem = mem ∧
        out.regs 0 = base ∧ out.regs 1 = n ∧ out.regs 5 = i ∧
        out.regs 2 = limit ∧ out.regs 8 = index)
      (fun _ => 29) := by
  intro st ω ⟨h0,h1,h5,h3,h4,h2,h8,hmemory,htable⟩
  let a := ancestorJump parent i u
  let b := ancestorJump parent i v
  have na := ancestorJump_lt hparent i hu
  have nb := ancestorJump_lt hparent i hv
  rw [Nat.succ_mul] at hroom
  have ha : base+i*n+u < 2^w := by omega
  have hb : base+i*n+v < 2^w := by omega
  have hmul : i*n < 2^w := by omega
  have hsum : base+i*n < 2^w := by omega
  have hma : st.mem (base+i*n+u) = a := hmemory ▸ htable u hu
  have hmb : st.mem (base+i*n+v) = b := hmemory ▸ htable v hv
  let sa := { st with regs := Function.update st.regs 6 a }
  let sb := { sa with regs := Function.update sa.regs 7 b }
  have hreadA : Runs w p ω (.assign 6 (.load (climbTogetherAddress 3))) st .normal sa 9 :=
    runs_assign_iff.mpr ⟨a,by unfold climbTogetherAddress; eval_expr,rfl,rfl,rfl⟩
  have hreadB : Runs w p ω (.assign 7 (.load (climbTogetherAddress 4))) sa .normal sb 9 := by
    have hn0 : sa.regs 0 = base := h0
    have hn1 : sa.regs 1 = n := h1
    have hn4 : sa.regs 4 = v := h4
    have hn5 : sa.regs 5 = i := h5
    have hm : sa.mem (base+i*n+v) = b := hmb
    exact runs_assign_iff.mpr ⟨b,by unfold climbTogetherAddress; eval_expr,rfl,rfl,rfl⟩
  have hr6 : sb.regs 6 = a := by simp [sb,sa]
  have hr7 : sb.regs 7 = b := by simp [sb]
  let condition := Expr.bin .eq (.reg 6) (.reg 7)
  let move := Stmt.assign 3 (.reg 6) ;; .assign 4 (.reg 7)
  have heval : condition.eval w sb = some (if a = b then 1 else 0) := by
    dsimp [condition]
    eval_expr
  have hex : ∃ out c, Runs w p ω (.cond condition .nop move) sb .normal out c ∧
      (out.regs 3,out.regs 4) = climbTogetherStep parent i (u,v) ∧ out.mem = mem ∧
      out.regs 0 = base ∧ out.regs 1 = n ∧ out.regs 5 = i ∧
      out.regs 2 = limit ∧ out.regs 8 = index ∧ c ≤ 9 := by
    by_cases hab : a = b
    · refine ⟨sb,5,?_,?_,hmemory,h0,h1,h5,h2,h8,by decide⟩
      · exact runs_cond_iff.mpr ⟨1,1,by simpa [hab] using heval,
          by simpa using (runs_nop_iff.mpr ⟨rfl,rfl,rfl⟩ :
            Runs w p ω .nop sb .normal sb 1),rfl⟩
      · simp [sb,sa,h3,h4,climbTogetherStep,show ancestorJump parent i u =
          ancestorJump parent i v from hab]
    · let s := { sb with regs := Function.update sb.regs 3 a }
      let out := { s with regs := Function.update s.regs 4 b }
      have hs : Runs w p ω (.assign 3 (.reg 6)) sb .normal s 2 :=
        runs_assign_iff.mpr ⟨a,by simp [Expr.eval,hr6],rfl,rfl,rfl⟩
      have ht : Runs w p ω (.assign 4 (.reg 7)) s .normal out 2 :=
        runs_assign_iff.mpr ⟨b,by simp [Expr.eval,s,hr7],rfl,rfl,rfl⟩
      refine ⟨out,9,?_,?_,hmemory,h0,h1,h5,h2,h8,le_rfl⟩
      · refine runs_cond_iff.mpr ⟨0,5,by simpa [hab] using heval,?_,rfl⟩
        simpa [move] using (runs_seq_iff.mpr (Or.inr ⟨s,2,2,hs,ht,rfl⟩) :
          Runs w p ω (.assign 3 (.reg 6) ;; .assign 4 (.reg 7)) sb .normal out 5)
      · simp [out,s,climbTogetherStep,show ancestorJump parent i u ≠
          ancestorJump parent i v from hab,a,b]
  obtain ⟨out,c,hr,hmodel,hmem,ho0,ho1,ho5,ho2,ho8,hc⟩ := hex
  refine ⟨.normal,out,9+(9+c+1)+1,?_,⟨rfl,hmodel,hmem,ho0,ho1,ho5,ho2,ho8⟩,by change 9+(9+c+1)+1 ≤ 29; omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨sa,9,9+c+1,hreadA,
    runs_seq_iff.mpr (Or.inr ⟨sb,9,c,hreadB,hr,rfl⟩),rfl⟩)

/-- Visit all rows from the highest to the lowest. Input registers are
`[base, width, row count, first vertex, second vertex]`. -/
def climbTogetherLoop : Stmt :=
  forRange 8 (.const 0) (.reg 2)
    (.assign 5 (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 8)) ;;
      climbTogetherBody)

/-- The descending pass realizes the pure simultaneous climb with one
constant-cost step per ancestor row. -/
theorem climbTogetherLoop_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v : ℕ) (parent : ℕ → ℕ)
    (hword : 1 < 2^w) (hcount : count < 2^w) (hu : u < n) (hv : v < n)
    (hroom : base+count*n < 2^w) (hparent : ∀ x < n, parent x < n)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x) :
    Triple w p (fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = u ∧ st.regs 4 = v ∧ st.mem = mem)
      climbTogetherLoop (normalPost fun st => st.mem = mem ∧ st.regs 0 = base ∧
        st.regs 3 < n ∧ (st.regs 3,st.regs 4) = climbTogether parent count (u,v))
      (fun _ => 45*count+7) := by
  let Inv := fun j (st : State) =>
    st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧ st.regs 8 = j ∧
    st.regs 3 < n ∧ st.regs 4 < n ∧ st.mem = mem ∧
    climbTogether parent (count-j) (st.regs 3,st.regs 4) = climbTogether parent count (u,v)
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 2)
    (body := .assign 5 (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 8)) ;;
      climbTogetherBody) (Inv := Inv)
    (P := fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
      st.regs 3 = u ∧ st.regs 4 = v ∧ st.mem = mem)
    36 0 count (Nat.zero_le _) (by omega) (fun _ => hcount)
    (fun st ⟨h0,h1,h2,h3,h4,hm⟩ => by
      exact ⟨by eval_expr, by simp [Inv,h0,h1,h2,h3,h4,hm,hu,hv]⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 2 = count := h.2.2.1
      eval_expr)
    (fun j _ hj => by
      intro st ω ⟨h0,h1,h2,h8,hx,hy,hm,hremain⟩
      let i := count-1-j
      let mid := { st with regs := Function.update st.regs 5 i }
      have hi : i < count := by dsimp [i]; omega
      have hfirst : Runs w p ω
          (.assign 5 (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 8))) st .normal mid 6 := by
        have hb : count-1 < 2^w := by omega
        have hbi : i < 2^w := hi.trans hcount
        refine runs_assign_iff.mpr ⟨i,?_,rfl,rfl,rfl⟩
        change _ = some (count-1-j)
        eval_expr
      have hroom' : base+(i+1)*n < 2^w :=
        (Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega : i+1 ≤ count)) base).trans_lt hroom
      obtain ⟨o,out,c,hr,⟨rfl,hpair,hmem,ho0,ho1,_,ho2,ho8⟩,hc⟩ :=
        climbTogetherBody_triple (p := p) base n i (st.regs 3) (st.regs 4) count j
          parent mem hword hx hy hroom' hparent mid ω
          ⟨h0,h1,by simp [mid],rfl,rfl,h2,h8,hm,htable i hi⟩
      refine ⟨.normal,out,6+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,6,c,hfirst,hr,rfl⟩),
        ⟨?_,ho8⟩,?_⟩
      · have hsize : (out.regs 3 < n) ∧ (out.regs 4 < n) := by
          change (out.regs 3,out.regs 4).1 < n ∧ (out.regs 3,out.regs 4).2 < n
          rw [hpair]
          simp only [climbTogetherStep]
          split
          · exact ⟨hx,hy⟩
          · exact ⟨ancestorJump_lt hparent i hx,ancestorJump_lt hparent i hy⟩
        have he : count-j = i+1 := by dsimp [i]; omega
        have he' : count-(j+1) = i := by dsimp [i]; omega
        have hnext := hremain
        rw [he,climbTogether,← hpair] at hnext
        simp [Inv,ho0,ho1,ho2,hmem,hsize,he',hnext]
      · change 6+c+1 ≤ 36
        change c ≤ 29 at hc
        omega)
  refine loop.conseq (fun _ h => h) ?_ (by intro _ _; simp [Expr.size,Nat.mul_comm])
  intro o st h
  cases o with
  | returned => exact False.elim h
  | normal =>
    rcases h with ⟨h0,_,_,_,hx,_,hm,he⟩
    exact ⟨hm,h0,hx,by simpa [climbTogether] using he⟩

/-- From equal-depth vertices, return the common vertex directly if they
agree. Otherwise climb to the last distinct pair and read its parent. -/
def alignedAncestor : Stmt :=
  .cond (.bin .eq (.reg 3) (.reg 4)) (.ret (.reg 3))
    (climbTogetherLoop ;; .ret (.load (.bin .add (.reg 0) (.reg 3))))

/-- The equal-depth query returns the first meeting of the two parent walks,
preserves memory, and takes at most `45 * count + 17` steps. -/
theorem alignedAncestor_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v : ℕ) (parent : ℕ → ℕ)
    (hword : 1 < 2^w) (hcount : count < 2^w) (hrows : 0 < count)
    (hu : u < n) (hv : v < n)
    (hroom : base+count*n < 2^w) (hparent : ∀ x < n, parent x < n)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x)
    (hroot : (parent^[2^count]) u = (parent^[2^count]) v) :
    let d := Nat.find (show ∃ k, (parent^[k]) u = (parent^[k]) v from ⟨2^count,hroot⟩)
    Triple w p (fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = u ∧ st.regs 4 = v ∧ st.mem = mem)
      alignedAncestor (fun o st => o = .returned ((parent^[d]) u) ∧ st.mem = mem)
      (fun _ => 45*count+17) := by
  classical
  intro d st ω hs
  obtain ⟨h0,h1,h2,h3,h4,hm⟩ := hs
  have hnle : n ≤ count*n := by
    simpa using Nat.mul_le_mul_right n (show 1 ≤ count by omega)
  have heval : (Expr.bin .eq (.reg 3) (.reg 4)).eval w st =
      some (if u = v then 1 else 0) := by eval_expr
  by_cases hsame : u = v
  · have hd : d = 0 := Nat.eq_zero_of_le_zero
      (Nat.find_min' _ (show (parent^[0]) u = (parent^[0]) v from hsame))
    have hr : Runs w p ω (.ret (.reg 3)) st (.returned u) st 2 :=
      runs_ret_iff.mpr ⟨u,by simp [Expr.eval,h3],rfl,rfl,rfl⟩
    refine ⟨.returned u,st,6,?_,⟨by simp [hd],hm⟩,?_⟩
    · exact runs_cond_iff.mpr ⟨1,2,by simpa [hsame] using heval,by simpa using hr,rfl⟩
    · change 6 ≤ 45*count+17
      omega
  · obtain ⟨o,mid,c,hr,hpost,hcost⟩ :=
      climbTogetherLoop_triple (p := p) mem base n count u v parent
        hword hcount hu hv hroom hparent htable st ω ⟨h0,h1,h2,h3,h4,hm⟩
    cases o with
    | returned => exact False.elim hpost
    | normal =>
      obtain ⟨hmem,hbase,hx,hpair⟩ := hpost
      let x := mid.regs 3
      have ha : base+x < 2^w := by dsimp [x]; omega
      have hcell : mid.mem (base+x) = parent x := by
        rw [hmem]
        simpa [ancestorJump] using htable 0 hrows x hx
      have hy : parent x = (parent^[d]) u := by
        have he : x = (climbTogether parent count (u,v)).1 := congrArg Prod.fst hpair
        rw [he]
        exact climbTogether_parent parent count u v hsame hroot
      have hret : Runs w p ω (.ret (.load (.bin .add (.reg 0) (.reg 3))))
          mid (.returned (parent x)) mid 5 := by
        have hx3 : mid.regs 3 = x := rfl
        exact runs_ret_iff.mpr ⟨parent x,by eval_expr,rfl,rfl,rfl⟩
      refine ⟨.returned (parent x),mid,c+10,?_,⟨by rw [hy],hmem⟩,?_⟩
      · exact runs_cond_iff.mpr ⟨0,c+5+1,by simpa [hsame] using heval,
          by simpa using runs_seq_iff.mpr (Or.inr ⟨mid,c,5,hr,hret,rfl⟩),by simp [Expr.size]; omega⟩
      · change c+10 ≤ 45*count+17
        change c ≤ 45*count+7 at hcost
        omega

end MinCostFlow.LastLevelProgram
