module

public import WordRAM.Contract
import WordRAM.Tactic

/-!
# Reading a maximum from fixed-width input records

The whole scaling program reads the cost and capacity bounds from the
magnitude fields of the original input. A recursive scan reads one field
per record and returns its maximum. The source memory stays unchanged.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,stride]` select one word from each record. -/
def stridedMaxBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (.load (.reg 0)) ;;
     .call 4 self [.bin .add (.reg 0) (.reg 2),.bin .sub (.reg 1) (.const 1),.reg 2] ;;
     .cond (.bin .lt (.reg 3) (.reg 4)) (.ret (.reg 4)) (.ret (.reg 3)))

/-- The scan uses one recursive procedure. -/
def stridedMaxModule (b : ℕ) : List Stmt := [stridedMaxBody b]

/-- The selected words and every computed source address fit in memory. -/
def stridedMaxContract (w : ℕ) (xs : List ℕ) : Contract where
  pre args mem := ∃ src stride,args=[src,xs.length,stride] ∧
    (∀ i : Fin xs.length,mem (src+stride*i.val)=xs[i.val]) ∧
    src+stride*xs.length<2^w ∧ xs.foldr max 0<2^w ∧ 2<2^w
  post _ mem ret mem' := mem'=mem ∧ ret=xs.foldr max 0
  cost _ _ := 50*xs.length+20

/-- The maximum scan is deterministic. -/
theorem stridedMaxModule_noRand (b : ℕ) : ∀ body∈stridedMaxModule b,body.NoRand := by
  intro body hb
  have he : body=stridedMaxBody b := by simpa only [stridedMaxModule,List.mem_singleton] using hb
  subst body
  simp only [stridedMaxBody,Stmt.NoRand,and_self]

/-- Scanning a field computes its exact maximum, in linear time and with
unchanged memory. -/
theorem stridedMax_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (stridedMaxModule b)) (xs : List ℕ) :
    MeetsContract w p b (stridedMaxContract w xs) := by
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨src,stride,rfl,_,_,_,h2⟩ := hpre
    apply runs_start_le
    unfold stridedMaxBody
    wram_step
    · refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,rfl⟩ ?_
      simp only [stridedMaxContract,List.length_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
      omega
    · simp at hcond
  | cons x xs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨src,stride,rfl,hat,hend,hmax,h2⟩ := hpre
    have hhead : mem src=x := by simpa using hat ⟨0,by simp⟩
    have htail : ∀ i : Fin xs.length,mem (src+stride+stride*i.val)=xs[i.val] := by
      intro i
      have h := hat ⟨i.val+1,by simp⟩
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have hend' : src+stride+stride*xs.length<2^w := by
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hend
    have hsrc : src<2^w := by omega
    have hnext : src+stride<2^w := by omega
    have hx : x<2^w := (Nat.le_max_left x (xs.foldr max 0)).trans_lt hmax
    have ht : xs.foldr max 0<2^w := (Nat.le_max_right x (xs.foldr max 0)).trans_lt hmax
    have hcount : (x::xs).length<2^w := hwords _ (by simp)
    have hlen : xs.length<2^w := by simp only [List.length_cons] at hcount; omega
    have hstride : stride<2^w := hwords stride (by simp)
    apply runs_start_le
    unfold stridedMaxBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := x) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [src+stride,xs.length,stride]) ?_ (by wram_words) ?_ ?_
      · have he : (x::xs).length-1=xs.length := rfl
        rw [←he]; eval_expr
      · exact ⟨src+stride,stride,rfl,htail,hend',ht,h2⟩
      · intro ret memR posR hpost
        obtain ⟨hmem,hr⟩ := hpost
        change memR=mem at hmem
        change ret=xs.foldr max 0 at hr
        have hret : ret<2^w := by omega
        wram_step
        · refine runs_ret_le (v := ret) (by eval_expr) ⟨hmem,?_⟩ ?_
          · change ret=max x (xs.foldr max 0)
            rw [←hr,Nat.max_eq_right (by omega)]
          · simp only [stridedMaxContract,List.length_cons,argsSize_cons,argsSize_nil,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega
        · refine runs_ret_le (v := x) (by eval_expr) ⟨hmem,?_⟩ ?_
          · change x=max x (xs.foldr max 0)
            rw [←hr,Nat.max_eq_left (by omega)]
          · simp only [stridedMaxContract,List.length_cons,argsSize_cons,argsSize_nil,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega

end MinCostFlow.Scaling.Machine
