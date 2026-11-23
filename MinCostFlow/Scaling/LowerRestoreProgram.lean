module

public import MinCostFlow.Scaling.SignedAddProgram
public import MinCostFlow.Scaling.InputLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Restoring lower capacities after residual optimization

The last step of the general-flow reduction in Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, Appendix C, adds each original lower capacity back to
the optimized shifted flow. Scan the original eight-word edge records and
the unsigned shifted flow together. The signed addition procedure writes
exactly the canonical pair for each restored integer coordinate.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[edgeRecords,shiftedFlow,count,heap]`. -/
def lowerRestoreBody (self add : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.call 4 add [.load (.bin .add (.reg 0) (.const 2)),
       .load (.bin .add (.reg 0) (.const 3)),.const 0,.load (.reg 1),.reg 3] ;;
     .call 5 self [.bin .add (.reg 0) (.const 8),.bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1),.reg 4] ;;
     .ret (.reg 5))

/-- The scan and the existing signed addition module. -/
def lowerRestoreModule (b : ℕ) : List Stmt := lowerRestoreBody b (b+1) :: signedAddModule (b+1)

/-- Both complete sources precede the fresh result, and each addition's
sum of input magnitudes fits one word. -/
def lowerRestoreContract (w : ℕ) (xs : List (Edge × ℕ)) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ edges flow heap,args=[edges,flow,xs.length,heap] ∧
      ListAt mem edges ((xs.map Prod.fst).flatMap Edge.encode) ∧
      ListAt mem flow (xs.map Prod.snd) ∧ edges+8*xs.length≤heap ∧ flow+xs.length≤heap ∧
      (∀ x∈xs,x.1.lower.natAbs+x.2<2^w) ∧ 8<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      ((xs.map (fun x => x.1.lower+(x.2 : ℤ))).flatMap encodeInt))
    (fun _ _ => 200*xs.length+20) (fun _ _ => 2*xs.length)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2*xs.length }

/-- Lower-capacity restoration contains no random instruction. -/
theorem lowerRestoreModule_noRand (b : ℕ) : ∀ body∈lowerRestoreModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [lowerRestoreBody,Stmt.NoRand,and_self]
  · exact signedAddModule_noRand _ body hb

/-- The scan restores every original lower capacity with exact signed
output, two fresh cells per edge, full frames, and linear cost. -/
theorem lowerRestore_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (lowerRestoreModule b)) (xs : List (Edge × ℕ)) :
    MeetsContract w p b (lowerRestoreContract w xs) := by
  have hadd := hasAt_tail hp
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨edges,flow,heap,rfl,_,_,_,_,_,h8⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0<2^w at hs
    have hh : heap<2^w := by omega
    apply runs_start_le
    unfold lowerRestoreBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap≤heap ∧ heap≤heap+0 ∧ (∀ x<heap,mem x=mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap=heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [lowerRestoreContract,heapContract,List.length_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega
    · simp at hcond
  | cons x xs ih =>
    have hk := signedAdd_meetsContract (w := w) hadd x.1.lower (x.2 : ℤ)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨edges,flow,heap,rfl,hedges,hflow,hend,hfend,hvalues,h8⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+2*(x::xs).length<2^w at hs
    obtain ⟨hhead,htail⟩ := listAt_append.mp hedges
    change ListAt mem edges x.1.encode at hhead
    change ListAt mem (edges+8) ((xs.map Prod.fst).flatMap Edge.encode) at htail
    obtain ⟨hflowHead,hflowTail⟩ := listAt_cons.mp hflow
    have hsign : mem (edges+2)=(if x.1.lower<0 then 1 else 0) := hhead 2 (by change 2<8; omega)
    have hmag : mem (edges+3)=x.1.lower.natAbs := hhead 3 (by change 3<8; omega)
    have hbudget := hvalues x List.mem_cons_self
    have hxword : x.2<2^w := by omega
    have hlword : x.1.lower.natAbs<2^w := by omega
    have hsword : (if x.1.lower<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
    have he2 : edges+2<2^w := by simp only [List.length_cons] at hend hs; omega
    have he3 : edges+3<2^w := by simp only [List.length_cons] at hend hs; omega
    have he8 : edges+8<2^w := by simp only [List.length_cons] at hend hs; omega
    have hf1 : flow+1<2^w := by simp only [List.length_cons] at hfend hs; omega
    have hh : heap<2^w := by omega
    have hh2 : heap+2<2^w := by simp only [List.length_cons] at hs; omega
    have hlen : xs.length<2^w := by simp only [List.length_cons] at hs; omega
    have hflowWord : flow<2^w := by omega
    apply runs_start_le
    unfold lowerRestoreBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hk
        (vs := [if x.1.lower<0 then 1 else 0,x.1.lower.natAbs,0,x.2,heap]) ?_
        (by wram_words) ?_ ?_
      · have he : (if (x.2 : ℤ)<0 then 1 else 0 : ℕ)=0 := by simp
        eval_expr
      · refine ⟨⟨heap,?_,?_⟩,hz,hh2⟩
        · have hn : ¬(x.2 : ℤ)<0 := by omega
          simp only [hn,↓reduceIte,Int.natAbs_natCast]
        · simpa only [Int.natAbs_natCast] using hbudget
      · intro next memA posA hpostA
        obtain ⟨⟨_,_,hframeA,hzA,hpairA⟩,hnext⟩ := hpostA
        change next=heap+2 at hnext
        change (∀ y<heap,memA y=mem y) at hframeA
        change ZeroFrom memA next at hzA
        change ListAt memA heap (encodeInt (x.1.lower+(x.2 : ℤ))) at hpairA
        have hnword : next<2^w := by omega
        have htailA := htail.of_agree_below (h₀ := heap)
          (by rw [edges_encode_length,List.length_map]; simp only [List.length_cons] at hend; omega) hframeA
        have hflowA := hflowTail.of_agree_below (h₀ := heap)
          (by rw [List.length_map]; simp only [List.length_cons] at hfend; omega) hframeA
        refine runs_seq_call_le ih (vs := [edges+8,flow+1,xs.length,next]) ?_ (by wram_words) ?_ ?_
        · have he : (x::xs).length-1=xs.length := rfl
          rw [←he]; eval_expr
        · refine ⟨⟨edges+8,flow+1,next,rfl,htailA,hflowA,?_,?_,
            fun y hy => hvalues y (List.mem_cons_of_mem _ hy),h8⟩,hzA,?_⟩
          · simp only [List.length_cons] at hend; omega
          · simp only [List.length_cons] at hfend; omega
          · change next+2*xs.length<2^w
            simp only [List.length_cons] at hs; omega
        · intro out memR posR hpostR
          obtain ⟨⟨_,_,hframeR,hzR,houtput⟩,hout⟩ := hpostR
          change out=next+2*xs.length at hout
          change (∀ y<next,memR y=memA y) at hframeR
          change ZeroFrom memR out at hzR
          change ListAt memR next ((xs.map (fun y => y.1.lower+(y.2 : ℤ))).flatMap encodeInt) at houtput
          have how : out<2^w := by simp only [List.length_cons] at hs; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap≤out ∧ out≤heap+2*(x::xs).length ∧ (∀ y<heap,memR y=mem y) ∧
              ZeroFrom memR out ∧ ListAt memR heap
                (encodeInt (x.1.lower+(x.2 : ℤ))++(xs.map (fun y => y.1.lower+(y.2 : ℤ))).flatMap encodeInt)) ∧
              out=heap+2*(x::xs).length
            refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
              by simp only [List.length_cons]; omega⟩
            · intro y hy
              exact (hframeR y (by omega)).trans (hframeA y hy)
            · apply listAt_append.mpr
              refine ⟨hpairA.of_agree_below (h₀ := next) ?_ hframeR,?_⟩
              · change heap+2≤next; omega
              · simpa only [encodeInt,List.length_cons,List.length_nil,Nat.reduceAdd,hnext] using houtput
          · simp only [lowerRestoreContract,signedAddContract,heapContract,List.length_cons,argsSize_cons,argsSize_nil,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega

/-- Every list of original edges and nonnegative shifted coordinates has
simultaneous restoration premises in canonical source memory at some
finite width. -/
theorem exists_lowerRestore_pre (xs : List (Edge × ℕ)) :
    ∃ w mem,(∀ x∈[0,8*xs.length,xs.length,9*xs.length],x<2^w) ∧
      (lowerRestoreContract w xs).pre [0,8*xs.length,xs.length,9*xs.length] mem := by
  let edges := (xs.map Prod.fst).flatMap Edge.encode
  let flows := xs.map Prod.snd
  let input := edges++flows
  let mem := initMem input
  let M := (xs.map (fun x => x.1.lower.natAbs+x.2)).foldr max 0
  let w := M+11*xs.length+9
  have hw : M+11*xs.length+9<2^w := Nat.lt_two_pow_self
  have he : edges.length=8*xs.length := by rw [edges_encode_length,List.length_map]
  have hf : flows.length=xs.length := List.length_map ..
  have hi : input.length=9*xs.length := by simp only [input,List.length_append,he,hf]; omega
  have hat := listAt_append.mp (listAt_initMem input)
  refine ⟨w,mem,?_,⟨0,8*xs.length,9*xs.length,rfl,hat.1,?_,by omega,by omega,?_,by omega⟩,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · simpa only [he,Nat.zero_add] using hat.2
  · intro x hx
    have hm : x.1.lower.natAbs+x.2≤M := Link.elem_le_foldr_max (List.mem_map.mpr ⟨x,hx,rfl⟩)
    omega
  · change ZeroFrom mem (9*xs.length)
    simpa only [hi] using zeroFrom_initMem input
  · change 9*xs.length+2*xs.length<2^w
    omega

end MinCostFlow.Scaling.Machine
