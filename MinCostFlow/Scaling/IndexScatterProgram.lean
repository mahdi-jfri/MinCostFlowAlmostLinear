module

public import MinCostFlow.Scaling.IndexListLayout
public import MinCostFlow.Scaling.Scatter
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Scattering a constant along a stored edge list

Cycle extraction returns immutable index nodes. Traverse those nodes in
order and write the selected bottleneck amount into each edge's unsigned
flow slot. Repeated indices have the same ordered overwrite semantics as
the model's scatter. Only the destination array changes.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[list,value,table]`. -/
def indexScatterBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.const 0))
    (.assign 3 (.load (.reg 0)) ;;
     .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .store (.bin .add (.reg 2) (.reg 3)) (.reg 1) ;;
     .call 5 self [.reg 4,.reg 1,.reg 2] ;;
     .ret (.const 0))

/-- One recursive procedure suffices for constant scatter. -/
def indexScatterModule (b : ℕ) : List Stmt := [indexScatterBody b]

/-- Source nodes lie before the destination array. -/
def indexScatterContract (w lo bound : ℕ) {n : ℕ} (s : Fin n → ℕ)
    (es : List (Fin n)) (value : ℕ) : Contract where
  pre args mem := ∃ ptr table,args=[ptr,value,table] ∧ IndexListAt mem lo bound ptr es ∧
    ListAt mem table (List.ofFn s) ∧ bound≤table ∧ table+n<2^w ∧ 1<2^w
  post args mem ret mem' := ret=0 ∧
    ListAt mem' (args.getD 2 0) (List.ofFn (Scatter.write s (es.map (fun e => (e,value))))) ∧
    ∀ x,x<args.getD 2 0 ∨ args.getD 2 0+n≤x → mem' x=mem x
  cost _ _ := 60*es.length+20

/-- The scatter loop has no random instruction. -/
theorem indexScatterModule_noRand (b : ℕ) : ∀ body ∈ indexScatterModule b,body.NoRand := by
  intro body hb
  have he : body=indexScatterBody b := by simpa only [indexScatterModule,List.mem_singleton] using hb
  subst body
  simp only [indexScatterBody,Stmt.NoRand,and_self]

private theorem unsigned_table_store {n : ℕ} {mem : ℕ → ℕ} {table value : ℕ}
    {s : Fin n → ℕ} (hat : ListAt mem table (List.ofFn s)) (e : Fin n) :
    ListAt (Function.update mem (table+e.val) value) table (List.ofFn (Function.update s e value)) := by
  intro i hi
  have hi' : i<n := by simpa only [List.length_ofFn] using hi
  rw [List.getElem_ofFn]
  by_cases heq : (⟨i,hi'⟩ : Fin n)=e
  · have hv := congrArg Fin.val heq
    simp only at hv
    subst i
    simp only [Function.update_self]
  · have hv : i≠e.val := fun hv => heq (Fin.ext hv)
    rw [Function.update_of_ne (by omega),Function.update_of_ne heq]
    have h := hat i (by simpa only [List.length_ofFn] using hi')
    change mem (table+i)=(List.ofFn s)[i]'(by simpa only [List.length_ofFn] using hi') at h
    rw [List.getElem_ofFn] at h
    exact h

/-- Every stored index list computes exactly the ordered scatter, with a
linear cost and a complete frame outside the unsigned destination. -/
theorem indexScatter_meetsContract {w b lo bound n : ℕ} {p : Program}
    (hp : p.HasAt b (indexScatterModule b)) (s : Fin n → ℕ) (es : List (Fin n)) (value : ℕ) :
    MeetsContract w p b (indexScatterContract w lo bound s es value) := by
  induction es generalizing s with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨ptr,table,rfl,hlist,htable,hbound,hspace,hw⟩ := hpre
    have hpzero := indexListAt_nil_iff.mp hlist
    subst ptr
    apply runs_start_le
    unfold indexScatterBody
    wram_step
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · exact ⟨rfl,htable,fun _ _ => rfl⟩
    · simp only [indexScatterContract,List.length_nil,Nat.mul_zero,Nat.zero_add,
        Expr.size_bin,Expr.size_reg,Expr.size_const]
      decide
  | cons e es ih =>
    have hkR := ih (Function.update s e value)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨ptr,table,rfl,hlist,htable,hbound,hspace,hw⟩ := hpre
    obtain ⟨hpositive,_,hend,heCell,tail,htailCell,htail⟩ := indexListAt_cons_iff.mp hlist
    have hptr : ptr<2^w := by omega
    have hptr1 : ptr+1<2^w := by omega
    have htableWord : table<2^w := by omega
    have heWord : e.val<2^w := by have he := e.isLt; omega
    have hcell : table+e.val<2^w := by have he := e.isLt; omega
    have htailWord : tail<2^w := by have h := htail.pointer_le; omega
    have hvalue : value<2^w := hwords _ (by simp)
    let memS := Function.update mem (table+e.val) value
    have hframeS : ∀ x,x<table ∨ table+n≤x → memS x=mem x := by
      intro x hx
      exact Function.update_of_ne (by have he := e.isLt; rcases hx with hx | hx <;> omega) _ _
    have htailS : IndexListAt memS lo bound tail es := htail.of_agree
      (fun x _ hx => hframeS x (Or.inl (by omega)))
    have htableS := unsigned_table_store (value := value) htable e
    apply runs_start_le
    unfold indexScatterBody
    wram_step
    refine runs_seq_assign_le (v := e.val) (by eval_expr) ?_
    refine runs_seq_assign_le (v := tail) (by eval_expr) ?_
    refine runs_seq_store_le (x := table+e.val) (v := value) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_call_le hkR (vs := [tail,value,table]) (by eval_expr) (by wram_words)
      ⟨tail,table,rfl,htailS,htableS,hbound,hspace,hw⟩ ?_
    intro ret memR posR hpostR
    obtain ⟨hret,htableR,hframeR⟩ := hpostR
    change (∀ x,x<table ∨ table+n≤x → memR x=memS x) at hframeR
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · refine ⟨rfl,htableR,?_⟩
      intro x hx
      exact (hframeR x hx).trans (hframeS x hx)
    · simp only [indexScatterContract,List.length_cons,argsSize_cons,argsSize_nil,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

/-- Every index list and constant value have joint layout and word
premises with a zero-initialized destination after the list nodes. -/
theorem exists_indexScatter_pre {n : ℕ} (es : List (Fin n)) (value : ℕ) :
    ∃ w mem bound ptr,(∀ x ∈ [ptr,value,bound],x<2^w) ∧
      (indexScatterContract w 1 bound (fun _ : Fin n => 0) es value).pre [ptr,value,bound] mem := by
  obtain ⟨mem,bound,ptr,hpositive,hlist,hzero⟩ := exists_indexListAt es
  let w := bound+n+value+3
  have hw : bound+n+value+3<2^w := Nat.lt_two_pow_self
  have hptr := hlist.pointer_le
  refine ⟨w,mem,bound,ptr,?_,ptr,bound,rfl,hlist,?_,le_rfl,by omega,by omega⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro i hi
    change mem (bound+i)=(List.ofFn (fun _ : Fin n => (0 : ℕ)))[i]
    rw [hzero _ (by omega),List.getElem_ofFn]

end MinCostFlow.Scaling.Machine
