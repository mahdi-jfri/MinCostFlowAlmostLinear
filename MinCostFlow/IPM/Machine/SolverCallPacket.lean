module

public import MinCostFlow.IPM.Machine.SolverDriver
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Evaluating the prepared search packet

The driver takes the three loop and radius words from a short record.
It combines them with the two array reservations and the fixed graph
and coefficient addresses without copying the tables.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Interpret all expressions of the final packet in the current
register state. Each access is to a field of the prepared records. -/
theorem solverStartSearchArgs_eval {w : ℕ} (I : Instance) (F : MinRatioFormat w)
    (L E g params source origHeap heap dest m limit radius wa ra : ℕ)
    (st : State)
    (hRegs : st.regs 0=g ∧ st.regs 1=params ∧ st.regs 2=source ∧ st.regs 3=origHeap ∧
      st.regs 6=I.n ∧ st.regs 7=m ∧ st.regs 8=dest ∧ st.regs 9=I.m ∧ st.regs 11=L ∧
      st.regs 12=F.fmt.precision ∧ st.regs 13=E ∧ st.regs 15=wa ∧
      st.regs 18=ra ∧ st.regs 19=heap ∧ st.regs 20=solverCoefficientBase I origHeap ∧
      st.regs 21=I.m*L ∧ st.regs 22=solverGuardBase I L origHeap)
    (hL : F.limbs=L)
    (hA₀ : st.mem (wa+0)=Num.IPM.lengthArraySpace I.m L F.fmt.precision E)
    (hA₁ : st.mem (wa+1)=Num.IPM.gradientArraySpace I.m L F.fmt.precision E)
    (hB₀ : st.mem (ra+0)=limit) (hB₁ : st.mem (ra+1)=radius)
    (hB₂ : st.mem (ra+2)=targetSearchRounds radius)
    (hRecords : max (wa+1) (ra+2)<2^w)
    (hW : heap<2^w) (hNine : 9<2^w)
    (hSpace : solverGuardBase I L origHeap+5*L≤heap)
    (hParams : params+7<2^w) :
    let old := solverEpochLayout I L E g (params+7) origHeap
    let quarter := old.slackMin+2*L
    evalArgs w st solverStartSearchArgs=some
      (targetOffsetPacket old F I 0 quarter source heap limit radius++
        [targetSearchRounds radius,I.n,m,dest]) := by
  dsimp only
  obtain ⟨r0,r1,r2,r3,r6,r7,r8,r9,r11,r12,r13,r15,r18,r19,r20,r21,r22⟩ := hRegs
  let c := solverCoefficientBase I origHeap
  let s := solverGuardBase I L origHeap
  have hs : s=c+9*(I.m*L)+L := by
    change c+(9*I.m+1)*L=c+9*(I.m*L)+L
    ring
  change s+5*L≤heap at hSpace
  have h₀ : 0<2^w := Nat.two_pow_pos _
  have h₁ : 1<2^w := by omega
  have h₂ : 2<2^w := by omega
  have h₃ : 3<2^w := by omega
  have h₄ : 4<2^w := by omega
  have h₅ : 5<2^w := by omega
  have h₇ : 7<2^w := by omega
  have ha : wa+0<2^w := by have := le_max_left (wa+1) (ra+2); omega
  have hb : wa+1<2^w := (le_max_left _ _).trans_lt hRecords
  have hr₀ : ra+0<2^w := by have := le_max_right (wa+1) (ra+2); omega
  have hr₁ : ra+1<2^w := by have := le_max_right (wa+1) (ra+2); omega
  have hr₂ : ra+2<2^w := (le_max_right _ _).trans_lt hRecords
  have c1 : c+I.m*L<2^w := by omega
  have c5 : c+5*(I.m*L)<2^w := by omega
  have c9 : c+9*(I.m*L)<2^w := by omega
  have m5 : 5*(I.m*L)<2^w := by omega
  have m9 : 9*(I.m*L)<2^w := by omega
  have sl1 : s+L<2^w := by omega
  have sl2 : s+2*L<2^w := by omega
  have sl3 : s+3*L<2^w := by omega
  have sl4 : s+4*L<2^w := by omega
  have l2 : 2*L<2^w := by omega
  have l3 : 3*L<2^w := by omega
  have l4 : 4*L<2^w := by omega
  have reg (j a : ℕ) (h : st.regs j=a) : Expr.eval w st (.reg j)=some a := congrArg some h
  have loadReg (j x k a : ℕ) (h : st.regs j=x) (hk : k<2^w) (hf : x+k<2^w)
      (ha : st.mem (x+k)=a) :
      Expr.eval w st (.load (.bin .add (.reg j) (.const k)))=some a :=
    Expr.eval_load_of_eq (Expr.eval_add (reg j x h) (Expr.eval_const hk) hf) ha
  simp only [solverStartSearchArgs,targetOffsetPacket,targetEpochPacket,solverEpochLayout,
    List.cons_append,hL]
  refine evalArgs_cons (reg _ _ r9) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r20) (reg _ _ r21) c1) ?_
  refine evalArgs_cons (reg _ _ r20) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r20) (Expr.eval_mul (Expr.eval_const h₅) (reg _ _ r21) m5) c5) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r1) (Expr.eval_const h₇) hParams) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r20) (Expr.eval_mul (Expr.eval_const hNine) (reg _ _ r21) m9) c9) ?_
  refine evalArgs_cons (Expr.eval_const h₀) ?_
  refine evalArgs_cons (reg _ _ r22) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r22) (reg _ _ r11) sl1) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r22) (Expr.eval_mul (Expr.eval_const h₂) (reg _ _ r11) l2) sl2) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r22) (Expr.eval_mul (Expr.eval_const h₃) (reg _ _ r11) l3) sl3) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r22) (reg _ _ r11) sl1) ?_
  refine evalArgs_cons (reg _ _ r22) ?_
  refine evalArgs_cons (Expr.eval_add (reg _ _ r22) (Expr.eval_mul (Expr.eval_const h₄) (reg _ _ r11) l4) sl4) ?_
  refine evalArgs_cons (reg _ _ r0) ?_
  refine evalArgs_cons (reg _ _ r11) ?_
  refine evalArgs_cons (reg _ _ r12) ?_
  refine evalArgs_cons (reg _ _ r13) ?_
  refine evalArgs_cons (loadReg 15 wa 0 _ r15 h₀ ha hA₀) ?_
  refine evalArgs_cons (loadReg 15 wa 1 _ r15 h₁ hb hA₁) ?_
  refine evalArgs_cons (reg _ _ r2) ?_
  refine evalArgs_cons (reg _ _ r19) ?_
  refine evalArgs_cons (reg _ _ r3) ?_
  refine evalArgs_cons (loadReg 18 ra 0 _ r18 h₀ hr₀ hB₀) ?_
  refine evalArgs_cons (loadReg 18 ra 1 _ r18 h₁ hr₁ hB₁) ?_
  refine evalArgs_cons (loadReg 18 ra 2 _ r18 h₂ hr₂ hB₂) ?_
  refine evalArgs_cons (reg _ _ r6) ?_
  refine evalArgs_cons (reg _ _ r7) ?_
  exact evalArgs_cons (reg _ _ r8) rfl

private theorem evalArgs_snoc_reg_pkt {w : ℕ} {st : State} {es : List Expr} {vs : List ℕ} {r v : ℕ}
    (h1 : evalArgs w st es = some vs) (hr : st.regs r = v) :
    evalArgs w st (es ++ [.reg r]) = some (vs ++ [v]) := by
  induction es generalizing vs with
  | nil => cases h1; exact evalArgs_cons (congrArg some hr) rfl
  | cons a es ih =>
    cases ha : a.eval w st with
    | none => simp [evalArgs, ha] at h1
    | some x =>
      cases hrest : evalArgs w st es with
      | none => simp [evalArgs, ha, hrest] at h1
      | some ys =>
        have hvs : x :: ys = vs := by simpa [evalArgs, ha, hrest] using h1
        subst hvs
        simp only [List.cons_append,evalArgs,ha,ih hrest]

/-- `V`-passing search packet evaluation appending `.reg 4` (`V`). -/
theorem solverStartSearchArgsWithV_eval {w : ℕ} (I : Instance) (F : MinRatioFormat w)
    (L E g params source origHeap heap dest m limit radius wa ra V : ℕ)
    (st : State)
    (hRegs : st.regs 0=g ∧ st.regs 1=params ∧ st.regs 2=source ∧ st.regs 3=origHeap ∧ st.regs 4=V ∧
      st.regs 6=I.n ∧ st.regs 7=m ∧ st.regs 8=dest ∧ st.regs 9=I.m ∧ st.regs 11=L ∧
      st.regs 12=F.fmt.precision ∧ st.regs 13=E ∧ st.regs 15=wa ∧
      st.regs 18=ra ∧ st.regs 19=heap ∧ st.regs 20=solverCoefficientBase I origHeap ∧
      st.regs 21=I.m*L ∧ st.regs 22=solverGuardBase I L origHeap)
    (hL : F.limbs=L)
    (hA₀ : st.mem (wa+0)=Num.IPM.lengthArraySpace I.m L F.fmt.precision E)
    (hA₁ : st.mem (wa+1)=Num.IPM.gradientArraySpace I.m L F.fmt.precision E)
    (hB₀ : st.mem (ra+0)=limit) (hB₁ : st.mem (ra+1)=radius)
    (hB₂ : st.mem (ra+2)=targetSearchRounds radius)
    (hRecords : max (wa+1) (ra+2)<2^w)
    (hW : heap<2^w) (hNine : 9<2^w)
    (hSpace : solverGuardBase I L origHeap+5*L≤heap)
    (hParams : params+7<2^w) :
    let old := solverEpochLayout I L E g (params+7) origHeap
    let quarter := old.slackMin+2*L
    evalArgs w st solverStartSearchArgsWithV=some
      (targetOffsetPacket old F I 0 quarter source heap limit radius++
        [targetSearchRounds radius,I.n,m,dest,V]) := by
  have hBase := solverStartSearchArgs_eval I F L E g params source origHeap heap dest m limit radius wa ra st
    ⟨hRegs.1,hRegs.2.1,hRegs.2.2.1,hRegs.2.2.2.1,hRegs.2.2.2.2.2⟩
    hL hA₀ hA₁ hB₀ hB₁ hB₂ hRecords hW hNine hSpace hParams
  dsimp only at hBase ⊢
  simpa [solverStartSearchArgsWithV,List.append_assoc] using
    evalArgs_snoc_reg_pkt hBase hRegs.2.2.2.2.1

end MinCostFlow.IPM.Machine
