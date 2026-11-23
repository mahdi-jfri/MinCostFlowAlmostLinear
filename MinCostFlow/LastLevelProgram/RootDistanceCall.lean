module

public import MinCostFlow.Num.AddCarry
public import WordRAM.CopyWords
public import MinCostFlow.LastLevelProgram.TreeDistance
import WordRAM.Tactic

/-!
# Writing a child distance

Add the parent distance and the parent-edge length in scratch memory,
then copy the sum to the child's indexed distance block.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Arguments are `[parentDistance, edgeLength, childDistance, L, heap]`. -/
def rootDistanceStepBody (add copy : ℕ) : Stmt :=
  .call 5 add [.reg 0,.reg 1,.reg 3,.const 0,.reg 4] ;;
  .call 6 copy [.reg 4,.reg 2,.reg 3] ;;
  .ret (.reg 5)

/-- The update writes the exact sum to the child's block, uses one scratch
block, and preserves the other blocks below the original cursor. -/
theorem rootDistanceStep_runs {w h add copy : ℕ} {p : Program}
    (ha : MeetsContract w p add (addCarryContract w h))
    (hc : MeetsContract w p copy (copyWordsContract w))
    (src edge dest L heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hw : 1 < 2^w) (hs : src+L ≤ heap) (he : edge+L ≤ heap)
    (hd : dest+L ≤ heap) (hroom : heap+L < 2^w)
    (hsrc : Valid mem src h L) (hedge : Valid mem edge h L)
    (hz : ZeroFrom mem heap) (hfit : Fits h L (intVal mem src h L + intVal mem edge h L)) :
    ∃ o out c, Runs w p ω (rootDistanceStepBody add copy)
      (startState [src,edge,dest,L,heap] mem pos) o out c ∧
      (o.value = heap+L ∧ Valid out.mem dest h L ∧
        intVal out.mem dest h L = intVal mem src h L + intVal mem edge h L ∧
        (∀ a < heap, a < dest ∨ dest+L ≤ a → out.mem a = mem a) ∧
        ZeroFrom out.mem o.value) ∧ c ≤ 55*L+34 := by
  apply runs_start_le
  unfold rootDistanceStepBody
  refine runs_seq_call_le ha (vs := [src,edge,L,0,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨src,edge,L,0,heap,rfl,hs,he,by decide,hsrc,hedge⟩,hz,hroom⟩
  · intro ret mid midPos hpost
    obtain ⟨hr,_,_,hframe,hzero,hdigits⟩ := hpost
    change ret = heap+L at hr
    change ∀ a < heap, mid a = mem a at hframe
    change ZeroFrom mid ret at hzero
    change ListAt mid heap (digits h L (unsignedVal mem src h L + unsignedVal mem edge h L + 0)) at hdigits
    obtain ⟨hvalid,hvalue⟩ := addCarry_value hdigits
    rw [Nat.cast_zero,add_zero,wrap_of_fits hfit] at hvalue
    refine runs_seq_call_le hc (vs := [heap,dest,L]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨heap,dest,L,rfl,hw,hroom.le,hd.trans (by omega),Or.inl hd⟩
    · intro result out outPos hcopy
      obtain ⟨_,_,_,heq,_,hwrite,hpres⟩ := hcopy
      cases heq
      have hret : ret < 2^w := hr ▸ hroom
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · refine ⟨hr,fun i hi => (hwrite i hi).trans_lt (hvalid i hi),
          (intVal_congr hwrite).trans hvalue,?_,?_⟩
        · intro a ha hp
          exact (hpres a hp).trans (hframe a ha)
        · intro a ha
          change ret ≤ a at ha
          exact (hpres a (Or.inr (by omega))).trans (hzero a ha)
      · simp [addCarryContract,heapContract,copyWordsContract,argsSize,Expr.size]
        omega

/-- A child-distance update returns the next scratch pointer. It writes
one indexed block and preserves the other input blocks. -/
def rootDistanceStepContract (w h : ℕ) : Contract where
  pre args mem := ∃ src edge dest L heap,
    args = [src,edge,dest,L,heap] ∧ 1 < 2^w ∧
    src+L ≤ heap ∧ edge+L ≤ heap ∧ dest+L ≤ heap ∧ heap+L < 2^w ∧
    Valid mem src h L ∧ Valid mem edge h L ∧ ZeroFrom mem heap ∧
    Fits h L (intVal mem src h L + intVal mem edge h L)
  post args mem ret out :=
    let src := args.getD 0 0
    let edge := args.getD 1 0
    let dest := args.getD 2 0
    let L := args.getD 3 0
    let heap := args.getD 4 0
    ret = heap+L ∧ Valid out dest h L ∧
    intVal out dest h L = intVal mem src h L + intVal mem edge h L ∧
    (∀ a < heap, a < dest ∨ dest+L ≤ a → out a = mem a) ∧ ZeroFrom out ret
  cost args _ := 55*args.getD 3 0+34

/-- The traversal can call the child-distance update using indexed block
addresses. Its cost is linear in the number of limbs. -/
theorem rootDistanceStep_meetsContract {w h entry add copy : ℕ} {p : Program}
    (he : p.procs[entry]? = some (rootDistanceStepBody add copy))
    (ha : MeetsContract w p add (addCarryContract w h))
    (hc : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (rootDistanceStepContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,edge,dest,L,heap,rfl,hw,hs,hEdge,hd,hroom,hsrc,hedge,hz,hfit⟩ := hpre
  exact rootDistanceStep_runs ha hc src edge dest L heap pos mem ω
    hw hs hEdge hd hroom hsrc hedge hz hfit

open LSF in
/-- Decode the updated child block using the common length scale. -/
theorem rootDistanceStep_eq_model {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) (ℓ : ℕ → ℝ)
    {mem out : ℕ → ℕ} {src edge dest h L P : ℕ}
    (hsrc : fixVal mem src h L P = walkLength ℓ (T.forestPath (parent T r u) r))
    (hedge : fixVal mem edge h L P = ℓ (parentEdge T r u))
    (hval : intVal out dest h L = intVal mem src h L + intVal mem edge h L) :
    fixVal out dest h L P = walkLength ℓ (T.forestPath u r) := by
  rw [rootDistance_parent_step hT hu hne ℓ, ← hsrc, ← hedge]
  simp only [fixVal,hval,Int.cast_add,add_div]
  rw [add_comm]

end MinCostFlow.LastLevelProgram
