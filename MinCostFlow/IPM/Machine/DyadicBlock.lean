module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Num.IPM.AlphaStorageFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact dyadic blocks for the normalization

A dyadic normalization has one nonzero numerator bit at the selected
fixed-point precision. Fresh-zero memory lets the machine store it with
one limb write, using the same representation proof as the numerical
barrier exponent. The full output block is allocated and framed.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[exponent,L,P,heap]`. Four-bit limbs are fixed. -/
def dyadicBlockBody : Stmt :=
  .store (.bin .add (.reg 3)
    (.bin .div (.bin .sub (.reg 2) (.reg 0)) (.const 4)))
    (.bin .shiftLeft (.const 1)
      (.bin .mod (.bin .sub (.reg 2) (.reg 0)) (.const 4))) ;;
  .ret (.bin .add (.reg 3) (.reg 1))

/-- One exact dyadic-block entry. -/
def dyadicBlockModule : List Stmt := [dyadicBlockBody]

/-- The numerator bit must lie within the signed block. -/
def dyadicBlockContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ k L P heap,args=[k,L,P,heap] ∧ k ≤ P ∧ P+2 ≤ 4*L)
    (fun args _ mem' => ScalarAt mem' (heapArg args) 4 (args.getD 1 0) (args.getD 2 0)
      (1/(2:ℝ)^(args.getD 0 0)))
    (fun _ _ => 80) (fun args _ => args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+args.getD 1 0}

/-- Storing one dyadic block contains no random instruction. -/
theorem dyadicBlock_noRand : dyadicBlockBody.NoRand := by
  simp [dyadicBlockBody,Stmt.NoRand]

/-- One word store represents the exact dyadic value, with cost at most
 eighty and allocation equal to its limb count. -/
theorem dyadicBlock_meetsContract {w b : ℕ} {p : Program} (hw : 16 < 2^w)
    (hp : p.HasAt b dyadicBlockModule) : MeetsContract w p b (dyadicBlockContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨k,L,P,heap,rfl,hk,hwidth⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+L < 2^w at hspace
  have hkw : k < 2^w := hwords _ (by simp)
  have hLw : L < 2^w := hwords _ (by simp)
  have hPw : P < 2^w := hwords _ (by simp)
  have hhw : heap < 2^w := hwords _ (by simp)
  have hj : (P-k)/4 < L := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by omega)
  have hmod : (P-k)%4 < 4 := Nat.mod_lt _ (by decide)
  have hbit : 2^((P-k)%4) < 16 := by
    exact Nat.pow_lt_pow_right (by decide) hmod
  have hslot : heap+(P-k)/4 < 2^w := by omega
  apply runs_start_le
  unfold dyadicBlockBody
  wram_step
  refine runs_ret_le (v:=heap+L) (by eval_expr) ?_ ?_
  · simp only [Nat.shiftLeft_eq,one_mul]
    let outMem := Function.update mem (heap+(P-k)/4) (2^((P-k)%4))
    change (heap ≤ heap+L ∧ heap+L ≤ heap+L ∧ (∀ x < heap,outMem x=mem x) ∧
      ZeroFrom outMem (heap+L) ∧ ScalarAt outMem heap 4 L P (1/(2:ℝ)^k)) ∧ heap+L=heap+L
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      exact Function.update_of_ne (by omega : x ≠ heap+(P-k)/4) _ _
    · intro x hx
      change heap+L ≤ x at hx
      dsimp only [outMem]
      rw [Function.update_of_ne (by omega : x ≠ heap+(P-k)/4)]
      exact hzero x (by omega)
    · exact Num.IPM.alphaBlock_spec (by decide : 0 < 4) hk hwidth (by
        intro i hi
        dsimp only [outMem]
        by_cases he : i=(P-k)/4
        · subst i
          simp
        · rw [Function.update_of_ne (by omega : heap+i ≠ heap+(P-k)/4),hzero (heap+i) (by omega)]
          simp [he])
  · simp only [dyadicBlockContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
