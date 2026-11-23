module

public import MinCostFlow.Scaling.DoublePotentialSumProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.InputLayout
import WordRAM.Tactic

/-!
# Updating every cost-potential coordinate

Scan the old potential and extracted dual tables together. Each pair
produces its canonical doubled sum in two fresh consecutive words. The
result is a contiguous signed table, so the cost-state header can point
to it directly. The scan has linear cost and no scratch beyond its output.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[oldPotentials,dualLabels,count,heap]`. -/
def potentialUpdateScanBody (self update : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.call 4 update [.load (.reg 0),.load (.bin .add (.reg 0) (.const 1)),
       .load (.reg 1),.load (.bin .add (.reg 1) (.const 1)),.reg 3] ;;
     .call 5 self [.bin .add (.reg 0) (.const 2),.bin .add (.reg 1) (.const 2),
       .bin .sub (.reg 2) (.const 1),.reg 4] ;;
     .ret (.reg 5))

/-- The scan entry and its constant-cost coordinate updater. -/
def potentialUpdateScanModule (b : ℕ) : List Stmt :=
  potentialUpdateScanBody b (b+1) :: doublePotentialSumModule (b+1)

/-- Both signed source arrays lie below the output heap. Every doubled
sum of magnitudes fits, and each result occupies two fresh words. -/
def potentialUpdateScanContract (w : ℕ) (xs : List (ℤ × ℤ)) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ a b heap,args=[a,b,xs.length,heap] ∧
      ListAt mem a ((xs.map Prod.fst).flatMap encodeInt) ∧
      ListAt mem b ((xs.map Prod.snd).flatMap encodeInt) ∧
      a+2*xs.length≤heap ∧ b+2*xs.length≤heap ∧
      (∀ x∈xs,2*(x.1.natAbs+x.2.natAbs)<2^w) ∧ 2<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      ((xs.map (fun x => 2*(x.1+x.2))).flatMap encodeInt))
    (fun _ _ => 300*xs.length+20) (fun _ _ => 2*xs.length)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2*xs.length }

/-- The scan and every coordinate update are deterministic. -/
theorem potentialUpdateScanModule_noRand (b : ℕ) : ∀ body ∈ potentialUpdateScanModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [potentialUpdateScanBody,Stmt.NoRand,and_self]
  · exact doublePotentialSumModule_noRand _ body hb

/-- The full scan computes every exact potential update, in a contiguous
signed array, with linear cost, exact allocation, and preserved sources. -/
theorem potentialUpdateScan_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (potentialUpdateScanModule b)) (xs : List (ℤ × ℤ)) :
    MeetsContract w p b (potentialUpdateScanContract w xs) := by
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,bp,heap,rfl,_,_,_,_,_,h2⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0<2^w at hs
    have hh : heap<2^w := by omega
    apply runs_start_le
    unfold potentialUpdateScanBody
    wram_step
    · refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change (heap≤heap ∧ heap≤heap+0 ∧ (∀ x<heap,mem x=mem x) ∧ ZeroFrom mem heap ∧
          ListAt mem heap []) ∧ heap=heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [potentialUpdateScanContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega
    · simp at hcond
  | cons x xs ih =>
    have hk := doublePotentialSum_meetsContract (w := w) (hasAt_tail hp) x.1 x.2
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,bp,heap,rfl,hleft,hright,haEnd,hbEnd,hvalues,h2⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+2*(x::xs).length<2^w at hs
    simp only [List.length_cons] at haEnd hbEnd hs
    obtain ⟨hheadA,htailA⟩ := listAt_append.mp hleft
    obtain ⟨hheadB,htailB⟩ := listAt_append.mp hright
    change ListAt mem a (encodeInt x.1) at hheadA
    change ListAt mem bp (encodeInt x.2) at hheadB
    change ListAt mem (a+2) ((xs.map Prod.fst).flatMap encodeInt) at htailA
    change ListAt mem (bp+2) ((xs.map Prod.snd).flatMap encodeInt) at htailB
    have hxs : mem a=if x.1<0 then 1 else 0 := by
      simpa only [encodeInt,Nat.add_zero,List.getElem_cons_zero] using hheadA 0 (by change 0<2; decide)
    have hxm : mem (a+1)=x.1.natAbs := by
      simpa only [encodeInt,List.getElem_cons_succ,List.getElem_cons_zero] using hheadA 1 (by change 1<2; decide)
    have hys : mem bp=if x.2<0 then 1 else 0 := by
      simpa only [encodeInt,Nat.add_zero,List.getElem_cons_zero] using hheadB 0 (by change 0<2; decide)
    have hym : mem (bp+1)=x.2.natAbs := by
      simpa only [encodeInt,List.getElem_cons_succ,List.getElem_cons_zero] using hheadB 1 (by change 1<2; decide)
    have hbudget := hvalues x List.mem_cons_self
    have hx : x.1.natAbs<2^w := by omega
    have hy : x.2.natAbs<2^w := by omega
    have hsx : (if x.1<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
    have hsy : (if x.2<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
    have ha1 : a+1<2^w := by omega
    have hb1 : bp+1<2^w := by omega
    have ha2 : a+2<2^w := by omega
    have hb2 : bp+2<2^w := by omega
    have hh : heap<2^w := by omega
    have hcount : (x::xs).length<2^w := hwords _ (by simp)
    have htcount : xs.length<2^w := by simp only [List.length_cons] at hcount; omega
    apply runs_start_le
    unfold potentialUpdateScanBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hk
        (vs := [if x.1<0 then 1 else 0,x.1.natAbs,if x.2<0 then 1 else 0,x.2.natAbs,heap])
        (by eval_expr) (by wram_words) ⟨⟨heap,rfl,hbudget⟩,hz,by change heap+2<2^w; omega⟩ ?_
      intro nextHeap memH posH hpostH
      obtain ⟨⟨_,_,hframeH,hzH,hheadH⟩,hretH⟩ := hpostH
      change nextHeap=heap+2 at hretH
      change (∀ z<heap,memH z=mem z) at hframeH
      change ZeroFrom memH nextHeap at hzH
      change ListAt memH heap (encodeInt (2*(x.1+x.2))) at hheadH
      have hnextWord : nextHeap<2^w := by omega
      have htailAH := htailA.of_agree_below (h₀ := heap)
        (by rw [integers_encode_length,List.length_map]; omega) hframeH
      have htailBH := htailB.of_agree_below (h₀ := heap)
        (by rw [integers_encode_length,List.length_map]; omega) hframeH
      refine runs_seq_call_le ih (vs := [a+2,bp+2,xs.length,nextHeap]) ?_ (by wram_words)
        ⟨⟨a+2,bp+2,nextHeap,rfl,htailAH,htailBH,by omega,by omega,
          (fun z hz' => hvalues z (List.mem_cons_of_mem x hz')),h2⟩,hzH,by change nextHeap+2*xs.length<2^w; omega⟩ ?_
      · have heq : (x::xs).length-1=xs.length := rfl
        rw [←heq]
        eval_expr
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hresultR⟩,hretR⟩ := hpostR
        change ret=nextHeap+2*xs.length at hretR
        change (∀ z<nextHeap,memR z=memH z) at hframeR
        change ZeroFrom memR ret at hzR
        change ListAt memR nextHeap ((xs.map (fun z => 2*(z.1+z.2))).flatMap encodeInt) at hresultR
        have hheadR := hheadH.of_agree_below (h₀ := nextHeap) (by change heap+2≤nextHeap; omega) hframeR
        refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+2*(x::xs).length ∧ (∀ z<heap,memR z=mem z) ∧
            ZeroFrom memR ret ∧ ListAt memR heap
              (((x::xs).map (fun z => 2*(z.1+z.2))).flatMap encodeInt)) ∧ ret=heap+2*(x::xs).length
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
            by simp only [List.length_cons]; omega⟩
          · intro z hz'
            exact (hframeR z (by omega)).trans (hframeH z hz')
          · apply listAt_append.mpr
            exact ⟨hheadR,by simpa only [hretH,encodeInt_length,List.flatMap_def] using hresultR⟩
        · simp only [potentialUpdateScanContract,doublePotentialSumContract,heapContract,List.length_cons,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

end MinCostFlow.Scaling.Machine
