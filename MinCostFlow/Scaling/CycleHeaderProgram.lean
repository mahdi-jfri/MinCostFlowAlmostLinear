module

public import MinCostFlow.Scaling.WordFiveStoreProgram
public import MinCostFlow.Scaling.WordPairStoreProgram
import WordRAM.Tactic

/-!
# Writing a cycle-traversal header

The traversal changes nine header words at a time while its vertex tables
and immutable nodes remain in place. Compose the shared five-word writer
with two pair stores. Their exact frames preserve every cell outside the
header and their costs give a constant bound.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Nine supplied header words followed by their destination address. -/
def cycleHeaderBody (five pair : ℕ) : Stmt :=
  .call 10 five [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 9] ;;
  .call 11 pair [.reg 5,.reg 6,.reg 10] ;;
  .call 12 pair [.reg 7,.reg 8,.reg 11] ;;
  .ret (.reg 12)

/-- The header entry and its shared in-place stores. -/
def cycleHeaderModule (b : ℕ) : List Stmt := [cycleHeaderBody (b+1) (b+2),wordFiveBody,wordPairBody]

/-- Only the nine header cells may change. -/
def cycleHeaderContract (w : ℕ) : Contract where
  pre args _ := ∃ a b c d e f g h i dst,args=[a,b,c,d,e,f,g,h,i,dst] ∧ dst+9<2^w
  post args mem ret mem' := ret=heapArg args+9 ∧
    ListAt mem' (heapArg args) (args.take 9) ∧
    (∀ x,x<heapArg args ∨ heapArg args+9≤x → mem' x=mem x) ∧
    ∀ i<9,mem' (heapArg args+i)<2^w
  cost _ _ := 140

/-- Header writing has no random instruction. -/
theorem cycleHeaderModule_noRand (b : ℕ) : ∀ body ∈ cycleHeaderModule b,body.NoRand := by
  simp only [cycleHeaderModule,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨by simp only [cycleHeaderBody,Stmt.NoRand,and_self],wordFiveBody_noRand,wordPairBody_noRand⟩

/-- The machine stores exactly the supplied nine-word header, preserves
all other memory, and takes at most 140 steps. -/
theorem cycleHeader_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleHeaderModule b)) : MeetsContract w p b (cycleHeaderContract w) := by
  have hfive : p.HasAt (b+1) wordFiveModule := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [wordFiveModule,cycleHeaderModule,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_zero] using
      hp 1 (by change 1<3; decide)
  have hpair : p.HasAt (b+2) wordPairModule := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [wordPairModule,cycleHeaderModule,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_zero] using
      hp 2 (by change 2<3; decide)
  have hkF := wordFiveStore_meetsContract (w := w) hfive
  have hkP := wordPairStore_meetsContract (w := w) hpair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,c,d,e,f,g,h,i,j,dst,rfl,hspace⟩ := hpre
  have ha : a<2^w := hwords _ (by simp)
  have hc : c<2^w := hwords _ (by simp)
  have hd : d<2^w := hwords _ (by simp)
  have he : e<2^w := hwords _ (by simp)
  have hf : f<2^w := hwords _ (by simp)
  have hg : g<2^w := hwords _ (by simp)
  have hh : h<2^w := hwords _ (by simp)
  have hi : i<2^w := hwords _ (by simp)
  have hj : j<2^w := hwords _ (by simp)
  have hdst : dst<2^w := by omega
  have hdst5 : dst+5<2^w := by omega
  have hdst7 : dst+7<2^w := by omega
  apply runs_start_le
  unfold cycleHeaderBody
  refine runs_seq_call_le hkF (vs := [a,c,d,e,f,dst]) (by eval_expr) (by wram_words)
    ⟨a,c,d,e,f,dst,rfl,hdst5⟩ ?_
  intro firstEnd memF posF hpostF
  obtain ⟨hfirstEnd,hfirst,hframeF⟩ := hpostF
  change firstEnd=dst+5 at hfirstEnd
  change ListAt memF dst [a,c,d,e,f] at hfirst
  change (∀ x,x<dst ∨ dst+5≤x → memF x=mem x) at hframeF
  have hfirstWord : firstEnd<2^w := by omega
  refine runs_seq_call_le hkP (vs := [g,h,firstEnd]) (by eval_expr) (by wram_words)
    ⟨g,h,firstEnd,rfl,by omega⟩ ?_
  intro secondEnd memP posP hpostP
  obtain ⟨hsecondEnd,hsecond,hframeP⟩ := hpostP
  change secondEnd=firstEnd+2 at hsecondEnd
  change ListAt memP firstEnd [g,h] at hsecond
  change (∀ x,x<firstEnd ∨ firstEnd+2≤x → memP x=memF x) at hframeP
  have hsecondWord : secondEnd<2^w := by omega
  have hfirstP := hfirst.of_agree_below (h₀ := firstEnd) (by change dst+5≤firstEnd; omega)
    (fun x hx => hframeP x (Or.inl hx))
  refine runs_seq_call_le hkP (vs := [i,j,secondEnd]) (by eval_expr) (by wram_words)
    ⟨i,j,secondEnd,rfl,by omega⟩ ?_
  intro ret memR posR hpostR
  obtain ⟨hret,hthird,hframeR⟩ := hpostR
  change ret=secondEnd+2 at hret
  change ListAt memR secondEnd [i,j] at hthird
  change (∀ x,x<secondEnd ∨ secondEnd+2≤x → memR x=memP x) at hframeR
  have hr : ret<2^w := by omega
  have hfirstR := hfirstP.of_agree_below (h₀ := secondEnd) (by change dst+5≤secondEnd; omega)
    (fun x hx => hframeR x (Or.inl hx))
  have hsecondR := hsecond.of_agree_below (h₀ := secondEnd) (by change firstEnd+2≤secondEnd; omega)
    (fun x hx => hframeR x (Or.inl hx))
  have harray : ListAt memR dst [a,c,d,e,f,g,h,i,j] := by
    have hlast : ListAt memR (dst+5) ([g,h]++[i,j]) := by
      apply listAt_append.mpr
      refine ⟨?_,?_⟩
      · simpa only [hfirstEnd] using hsecondR
      · have heq : dst+5+[g,h].length=secondEnd := by change dst+5+2=secondEnd; omega
        rw [heq]; exact hthird
    exact listAt_append.mpr ⟨hfirstR,hlast⟩
  refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
  · change ret=dst+9 ∧ ListAt memR dst [a,c,d,e,f,g,h,i,j] ∧
      (∀ x,x<dst ∨ dst+9≤x → memR x=mem x) ∧ ∀ k<9,memR (dst+k)<2^w
    refine ⟨by omega,harray,?_,?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact (hframeR x (Or.inl (by omega))).trans
          ((hframeP x (Or.inl (by omega))).trans (hframeF x (Or.inl hx)))
      · exact (hframeR x (Or.inr (by omega))).trans
          ((hframeP x (Or.inr (by omega))).trans (hframeF x (Or.inr (by omega))))
    · intro k hk
      have hcell := harray k (by change k<9; exact hk)
      rw [hcell]
      have hm := List.getElem_mem (l := [a,c,d,e,f,g,h,i,j]) (by change k<9; exact hk)
      exact hwords _ (List.mem_append_left [dst] hm)
  · simp only [cycleHeaderContract,wordFiveStoreContract,wordPairStoreContract,
      argsSize_cons,argsSize_nil,Expr.size_reg]
    omega

/-- Every nine-word header has a simultaneous fitting argument and
destination instance. -/
theorem exists_cycleHeader_pre (a b c d e f g h i : ℕ) :
    ∃ w,(∀ x ∈ [a,b,c,d,e,f,g,h,i,0],x<2^w) ∧
      (cycleHeaderContract w).pre [a,b,c,d,e,f,g,h,i,0] (fun _ => 0) := by
  let w := a+b+c+d+e+f+g+h+i+20
  have hw : a+b+c+d+e+f+g+h+i+20<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,a,b,c,d,e,f,g,h,i,0,rfl,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
