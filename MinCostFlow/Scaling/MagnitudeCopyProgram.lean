module

public import MinCostFlow.Scaling.SignedTableLayout
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Copying signed magnitudes into unsigned flow arrays

The general-flow reduction uses canonical signed pairs at its outer
interface. Its residual and objective procedures use unsigned flows.
For a nonnegative flow, copying the magnitude word gives its exact value.
The loop here copies those words to a fresh contiguous array, preserving
the signed source and counting every load, store, and recursive call.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[signedSource,count,heap]`. -/
def magnitudeCopyBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.store (.reg 2) (.load (.bin .add (.reg 0) (.const 1))) ;;
     .call 3 self [.bin .add (.reg 0) (.const 2),
       .bin .sub (.reg 1) (.const 1),.bin .add (.reg 2) (.const 1)] ;;
     .ret (.reg 3))

/-- One recursive scan copies all magnitude words. -/
def magnitudeCopyModule (b : ℕ) : List Stmt := [magnitudeCopyBody b]

/-- The complete signed source precedes the fresh unsigned output. -/
def magnitudeCopyContract (w : ℕ) (zs : List ℤ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ src heap,args=[src,zs.length,heap] ∧
      ListAt mem src (zs.flatMap encodeInt) ∧ src+2*zs.length≤heap ∧
      (∀ z∈zs,z.natAbs<2^w) ∧ 2<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (zs.map Int.natAbs))
    (fun _ _ => 50*zs.length+20) (fun _ _ => zs.length)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+zs.length }

/-- Magnitude copying contains no random instruction. -/
theorem magnitudeCopyModule_noRand (b : ℕ) : ∀ body∈magnitudeCopyModule b,body.NoRand := by
  intro body hb
  have he : body=magnitudeCopyBody b := by simpa only [magnitudeCopyModule,List.mem_singleton] using hb
  subst body
  simp only [magnitudeCopyBody,Stmt.NoRand,and_self]

/-- Every magnitude is copied exactly, with one fresh output cell per
coordinate, full memory frames, and linear cost. -/
theorem magnitudeCopy_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (magnitudeCopyModule b)) (zs : List ℤ) :
    MeetsContract w p b (magnitudeCopyContract w zs) := by
  induction zs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src,heap,rfl,_,_,_,h2⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0<2^w at hs
    have hh : heap<2^w := by omega
    apply runs_start_le
    unfold magnitudeCopyBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap≤heap ∧ heap≤heap+0 ∧ (∀ x<heap,mem x=mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap=heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [magnitudeCopyContract,heapContract,List.length_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega
    · simp at hcond
  | cons z zs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src,heap,rfl,hat,hend,hvalues,h2⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(z::zs).length<2^w at hs
    obtain ⟨hpair,htail⟩ := listAt_append.mp hat
    change ListAt mem src (encodeInt z) at hpair
    change ListAt mem (src+2) (zs.flatMap encodeInt) at htail
    have hmag : mem (src+1)=z.natAbs := hpair 1 (by change 1<2; omega)
    have hzword := hvalues z List.mem_cons_self
    have hsrc1 : src+1<2^w := by simp only [List.length_cons] at hend hs; omega
    have hsrc2 : src+2<2^w := by simp only [List.length_cons] at hend hs; omega
    have hh : heap<2^w := by omega
    have hh1 : heap+1<2^w := by simp only [List.length_cons] at hs; omega
    have hlen : (z::zs).length<2^w := hwords _ (by simp)
    have hlenTail : zs.length<2^w := by simp only [List.length_cons] at hlen; omega
    let memS := Function.update mem heap z.natAbs
    have hframeS : ∀ x<heap,memS x=mem x := by
      intro x hx
      exact Function.update_of_ne (by omega : x≠heap) _ _
    have htailS := htail.of_agree_below (h₀ := heap)
      (by rw [integers_encode_length]; simp only [List.length_cons] at hend; omega) hframeS
    have hzS : ZeroFrom memS (heap+1) := by
      intro x hx
      change Function.update mem heap z.natAbs x=0
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact hz x (by omega)
    apply runs_start_le
    unfold magnitudeCopyBody
    wram_step
    · simp at hcond
    · refine runs_seq_store_le (x := heap) (v := z.natAbs) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [src+2,zs.length,heap+1]) ?_ (by wram_words) ?_ ?_
      · have he : (z::zs).length-1=zs.length := rfl
        rw [←he]; eval_expr
      · refine ⟨⟨src+2,heap+1,rfl,htailS,?_,fun y hy => hvalues y (List.mem_cons_of_mem _ hy),h2⟩,hzS,?_⟩
        · simp only [List.length_cons] at hend; omega
        · change heap+1+zs.length<2^w
          simp only [List.length_cons] at hs; omega
      · intro out memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,houtput⟩,hout⟩ := hpostR
        change out=heap+1+zs.length at hout
        change (∀ x<heap+1,memR x=memS x) at hframeR
        change ListAt memR (heap+1) (zs.map Int.natAbs) at houtput
        change ZeroFrom memR out at hzR
        have how : out<2^w := by simp only [List.length_cons] at hs; omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap≤out ∧ out≤heap+(z::zs).length ∧ (∀ x<heap,memR x=mem x) ∧
            ZeroFrom memR out ∧ ListAt memR heap (z.natAbs::zs.map Int.natAbs)) ∧ out=heap+(z::zs).length
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
            by simp only [List.length_cons]; omega⟩
          · intro x hx
            exact (hframeR x (by omega)).trans (hframeS x hx)
          · apply listAt_cons.mpr
            refine ⟨?_,houtput⟩
            exact (hframeR heap (by omega)).trans (Function.update_self _ _ _)
        · simp only [magnitudeCopyContract,heapContract,List.length_cons,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

/-- Every signed vector realizes the full copying precondition at a
finite width, with its canonical pairs as the source. -/
theorem exists_magnitudeCopy_pre (zs : List ℤ) :
    ∃ w,(∀ x∈[0,zs.length,2*zs.length],x<2^w) ∧
      (magnitudeCopyContract w zs).pre [0,zs.length,2*zs.length] (initMem (zs.flatMap encodeInt)) := by
  let M := (zs.map Int.natAbs).foldr max 0
  let w := M+3*zs.length+3
  have hw : M+3*zs.length+3<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,⟨0,2*zs.length,rfl,listAt_initMem _,by omega,?_,by omega⟩,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro z hz
    have hm : z.natAbs≤M := Link.elem_le_foldr_max (List.mem_map.mpr ⟨z,hz,rfl⟩)
    omega
  · change ZeroFrom (initMem (zs.flatMap encodeInt)) (2*zs.length)
    simpa only [integers_encode_length] using zeroFrom_initMem (zs.flatMap encodeInt)
  · change 2*zs.length+zs.length<2^w
    omega

end MinCostFlow.Scaling.Machine
