module

public import MinCostFlow.IPM.Machine.RoundFlowTable
public import MinCostFlow.IPM.Machine.RoundFlowArithmetic
import WordRAM.Tactic

/-!
# Updating the new edge in the working table

Compute the exact directed adjustment and copy the result back to
the edge's table block. The only write below the input heap is that
one coordinate.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On [coordinate,delta,L,backward,heap], adjust one table cell. -/
def roundStoreCoordinateBody (arithmetic copy : ℕ) : Stmt :=
  .call 5 arithmetic [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;;
  .call 6 copy [.bin .sub (.reg 5) (.reg 2),.reg 0,.reg 2] ;;
  .ret (.reg 5)

/-- The update changes one coordinate and preserves the rest of the
allocated prefix. The multiplication by scale is already represented
in its signed numerator. -/
def roundStoreCoordinateContract (w h P : ℕ) (q δ : ℚ) (backward : Bool) : Contract where
  pre := (roundFlowArithmeticContract w h P q δ backward).pre
  post args mem out final :=
    let a := args.getD 0 0
    let L := args.getD 2 0
    let heap := heapArg args
    out=heap+(if backward then 2*L else L) ∧ ZeroFrom final out ∧
      RatAt final a h L P (if backward then q-δ else q+δ) ∧
      ∀ z<heap,z<a ∨ a+L≤z → final z=mem z
  cost args _ := 91*args.getD 2 0+100

/-- Exact arithmetic and coordinate copy are deterministic. -/
theorem roundStoreCoordinate_noRand (arithmetic copy : ℕ) :
    (roundStoreCoordinateBody arithmetic copy).NoRand := by
  simp [roundStoreCoordinateBody,Stmt.NoRand]

/-- The table write follows the arithmetic direction exactly. -/
theorem roundStoreCoordinate_meetsContract {w h P entry arithmetic copy : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (roundStoreCoordinateBody arithmetic copy))
    (hArith : ∀ q δ backward,MeetsContract w p arithmetic
      (roundFlowArithmeticContract w h P q δ backward))
    (hCopy : MeetsContract w p copy (copyWordsContract w)) (hOne : 1<2^w)
    (q δ : ℚ) (backward : Bool) :
    MeetsContract w p entry (roundStoreCoordinateContract w h P q δ backward) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hw hpre
  have hp : (roundFlowArithmeticContract w h P q δ backward).pre args mem := hpre
  obtain ⟨⟨a,d,L,heap,rfl,ha,hd,hq,hδ,hFit⟩,hz,hSpace⟩ := hp
  change heap+(if backward then 2*L else L)<2^w at hSpace
  apply runs_start_le
  unfold roundStoreCoordinateBody
  refine runs_seq_call_le (hArith q δ backward) (vs:=[a,d,L,backward.toNat,heap]) rfl hw hpre ?_
  intro v mem₁ pos₁ hout
  obtain ⟨⟨hLo,hHi,hFrame,hFresh,_⟩,hEq,hValue⟩ := hout
  change v=heap+(if backward then 2*L else L) at hEq
  have hExtent : L≤(if backward then 2*L else L) := by cases backward <;> simp; omega
  have hSrc : heap≤v-L := by omega
  have hEnd : v-L+L=v := by omega
  have hV : v<2^w := hEq ▸ hSpace
  have hVL : v-L<2^w := by omega
  have hA : a<2^w := hw _ (by simp)
  have hL : L<2^w := hw _ (by simp)
  refine runs_seq_call_le hCopy (vs:=[v-L,a,L]) (by eval_expr) (by wram_words)
    ⟨v-L,a,L,rfl,hOne,by omega,by omega,Or.inl (ha.trans hSrc)⟩ ?_
  intro c mem₂ pos₂ hout'
  obtain ⟨hStored,hKeep⟩ := round_copy_rat hValue hout'
  refine runs_ret_le (v:=v) rfl ?_ ?_
  · change v=heap+(if backward then 2*L else L) ∧ ZeroFrom mem₂ v ∧
      RatAt mem₂ a h L P (if backward then q-δ else q+δ) ∧
      ∀ z<heap,z<a ∨ a+L≤z → mem₂ z=mem z
    refine ⟨hEq,?_,hStored,?_⟩
    · intro z hz'
      exact (hKeep z (Or.inr (ha.trans (hLo.trans hz')))).trans (hFresh z hz')
    · intro z hz' hsep
      exact (hKeep z hsep).trans (hFrame z hz')
  · change 0+5+(74*L+60)+2+5+(17*L+10)+2+2≤91*L+100
    omega

end MinCostFlow.IPM.Machine
