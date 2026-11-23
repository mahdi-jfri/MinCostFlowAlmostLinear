module

public import MinCostFlow.LastLevelProgram.StoreWord
public import MinCostFlow.LastLevelProgram.ScaleBlock
import MinCostFlow.LastLevelProgram.StretchEncoding
import WordRAM.Tactic

/-!
# Preparing the scaled denominator

The integer update scale is a word. Write it as signed limbs, then
multiply by the grid denominator using the verified left shift.
This prepares the common divisor for all edges of a last-level round.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Arguments are `[scale, L, precision, heap]`. The result occupies
the second block allocated by the procedure. -/
def denominatorBody (store shift : ℕ) : Stmt :=
  .call 4 store [.reg 3,.reg 1,.reg 0] ;;
  .call 5 shift [.reg 3,.reg 1,.reg 2,.reg 4] ;;
  .ret (.reg 5)

/-- Run the setup for the common divisor in linear limb time. -/
theorem denominator_runs {w h store shift : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hs : MeetsContract w p store (storeWordContract w h))
    (hp : p.HasAt shift (shiftLeftModule shift h))
    (scale L P heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hscale : scale < 2 ^ w) (hprec : P < 2 ^ w)
    (hfit : Fits h L (scale : ℤ)) (hscaled : Fits h L ((scale : ℤ) * (2 : ℤ)^P))
    (hz : ZeroFrom mem heap) (hroom : heap + 2 * L < 2 ^ w) :
    ∃ o st c, Runs w p ω (denominatorBody store shift)
      (startState [scale,L,P,heap] mem pos) o st c ∧
      (o.value = heap + 2 * L ∧ Valid st.mem (heap + L) h L ∧
        intVal st.mem (heap + L) h L = (scale : ℤ) * (2 : ℤ)^P ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem o.value) ∧ c ≤ 56 * L + 62 := by
  apply runs_start_le
  unfold denominatorBody
  refine runs_seq_call_le hs (vs := [heap,L,scale]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨heap,L,scale,rfl,hfit,hz,by omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁,hframe₁,hzero₁,hvalid₁,hval₁⟩ := hpost
    change r₁ = heap + L at hr₁
    change ∀ a < heap, m₁ a = mem a at hframe₁
    change Valid m₁ heap h L at hvalid₁
    change intVal m₁ heap h L = (scale : ℤ) at hval₁
    refine runs_seq_call_le (shiftLeft_meetsContract hh hw hp) (vs := [heap,L,P,r₁])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨heap,L,P,r₁,rfl,hr₁.ge,hvalid₁⟩,hzero₁,by change r₁ + L < 2^w; omega⟩
    · intro r₂ m₂ pos₂ hpost₂
      obtain ⟨hr₂,_,_,hframe₂,hzero₂,hvalid₂,hval₂⟩ := hpost₂
      change r₂ = r₁ + L at hr₂
      change ∀ a < r₁, m₂ a = m₁ a at hframe₂
      change Valid m₂ r₁ h L at hvalid₂
      change intVal m₂ r₁ h L = wrap h L (intVal m₁ heap h L * (2 : ℤ)^P) at hval₂
      rw [hval₁, wrap_of_fits hscaled] at hval₂
      refine runs_ret_le (v := r₂) (by eval_expr) ?_ ?_
      · exact ⟨by change r₂ = _; omega,hr₁ ▸ hvalid₂,hr₁ ▸ hval₂,
          fun a ha => (hframe₂ a (by omega)).trans (hframe₁ a ha),hzero₂⟩
      · simp [storeWordContract, shiftLeftContract, heapContract, argsSize, Expr.size]
        omega

/-- A denominator call receives the scale, limb count, precision, and
fresh allocation cursor as runtime words. -/
def denominatorContract (w h : ℕ) : Contract where
  pre args mem := ∃ scale L P heap,
    args = [scale,L,P,heap] ∧ Fits h L (scale : ℤ) ∧
      Fits h L ((scale : ℤ)*(2 : ℤ)^P) ∧ ZeroFrom mem heap ∧ heap+2*L < 2^w
  post args mem ret out := ∃ scale L P heap,
    args = [scale,L,P,heap] ∧ ret = heap+2*L ∧ Valid out (heap+L) h L ∧
      intVal out (heap+L) h L = (scale : ℤ)*(2 : ℤ)^P ∧
      (∀ a < heap, out a = mem a) ∧ ZeroFrom out ret
  cost args _ := 56*args.getD 1 0+62

/-- Install denominator preparation as an ordinary procedure. -/
theorem denominator_meetsContract {w h entry store shift : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (he : p.procs[entry]? = some (denominatorBody store shift))
    (hs : MeetsContract w p store (storeWordContract w h))
    (hp : p.HasAt shift (shiftLeftModule shift h)) :
    MeetsContract w p entry (denominatorContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨scale,L,P,heap,rfl,hfit,hscaled,hz,hroom⟩ := hpre
  obtain ⟨o,out,c,hr,hpost,hcost⟩ := denominator_runs hh hw hs hp scale L P heap pos mem ω
    (hwords _ (by simp)) (hwords _ (by simp)) hfit hscaled hz hroom
  exact ⟨o,out,c,hr,⟨scale,L,P,heap,rfl,hpost⟩,hcost⟩

/-- Prepare the unit used by the branch scatter. The limb count and
stretch-grid precision are runtime words. -/
def stagedStretchUnitArgs : List Expr :=
  [.const 1,.reg 55,.reg 23,.reg 16]

/-- At the stretch-grid precision, the scaled unit numerator decodes to
one. The caller can use this block for loops and named denominators. -/
theorem stagedStretchUnit_runs {w h entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P heap : ℕ)
    (hcall : MeetsContract w p entry (denominatorContract w h))
    (hL : st.regs 55 = L) (hP : st.regs 23 = P) (hheap : st.regs 16 = heap)
    (hw : 1 < 2^w) (hPword : P < 2^w)
    (hfit : Fits h L 1) (hscaled : Fits h L ((2 : ℤ)^P))
    (hz : ZeroFrom st.mem heap) (hroom : heap+2*L < 2^w) :
    ∃ out cost, Runs w p ω (.call 67 entry stagedStretchUnitArgs) st .normal out cost ∧
      out.regs 67 = heap+2*L ∧ Valid out.mem (heap+L) h L ∧
      fixVal out.mem (heap+L) h L P = 1 ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap+2*L) ∧
      (∀ r, r ≠ 67 → out.regs r = st.regs r) ∧ cost ≤ 56*L+67 := by
  have hargs : evalArgs w st stagedStretchUnitArgs = some [1,L,P,heap] := by
    simp [stagedStretchUnitArgs,evalArgs,Expr.eval,hL,hP,hheap,hw]
  have hwords : ∀ a ∈ [1,L,P,heap], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre : (denominatorContract w h).pre [1,L,P,heap] st.mem :=
    ⟨1,L,P,heap,rfl,by simpa using hfit,by simpa using hscaled,hz,hroom⟩
  obtain ⟨out,cost,ret,hrun,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 67) hcall hargs hwords hpre ω
  obtain ⟨scale,l,q,addr,heq,hr,hvalid,hvalue,hframe,hzero⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
  change cost ≤ 4+(56*L+62)+1 at hcost
  refine ⟨out,cost,hrun,hret.trans hr,hvalid,?_,hframe,hr ▸ hzero,hregs,by omega⟩
  rw [fixVal,hvalue]
  push_cast
  simp

/-- Publish the unit pointer while retaining the returned allocation end. -/
def stagedStretchUnitBody (entry : ℕ) : Stmt :=
  .seq (.call 67 entry stagedStretchUnitArgs)
    (.assign 60 (.bin .sub (.reg 67) (.reg 55)))

/-- The unit is available to the named scatter, and the next allocation
can start immediately after it. -/
theorem stagedStretchUnitBody_runs {w h entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P heap : ℕ)
    (hcall : MeetsContract w p entry (denominatorContract w h))
    (hL : st.regs 55 = L) (hP : st.regs 23 = P) (hheap : st.regs 16 = heap)
    (hw : 1 < 2^w) (hPword : P < 2^w)
    {B : ℝ} (hB : 1 ≤ B) (hwidth : 2 * (2 : ℝ)^P * B < capacity h L)
    (hz : ZeroFrom st.mem heap) (hroom : heap+2*L < 2^w) :
    ∃ out cost, Runs w p ω (stagedStretchUnitBody entry) st .normal out cost ∧
      out.regs 60 = heap+L ∧ out.regs 67 = heap+2*L ∧
      Valid out.mem (heap+L) h L ∧ fixVal out.mem (heap+L) h L P = 1 ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap+2*L) ∧
      (∀ r, r ≠ 60 → r ≠ 67 → out.regs r = st.regs r) ∧ cost ≤ 56*L+72 := by
  obtain ⟨hfit,hscaled⟩ := stretchUnit_fits_of_capacity hB hwidth
  obtain ⟨mid,c,hr,he,hv,hunit,hframe,hzero,hregs,hcost⟩ :=
    stagedStretchUnit_runs (ω := ω) st L P heap hcall hL hP hheap hw hPword hfit hscaled hz hroom
  let out := {mid with regs := Function.update mid.regs 60 (heap+L)}
  have hL' := (hregs 55 (by decide)).trans hL
  have hptr : heap+2*L-L = heap+L := by omega
  have ha : Runs w p ω (.assign 60 (.bin .sub (.reg 67) (.reg 55))) mid .normal out 4 := by
    apply runs_assign_iff.mpr
    refine ⟨heap+L,?_,rfl,rfl,rfl⟩
    have hf : heap+L < 2^w := by omega
    simp [Expr.eval,BinOp.eval,he,hL',hptr,hf]
  refine ⟨out,c+4+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,4,hr,ha,rfl⟩),
    by simp [out],by simpa [out, Function.update] using he,
    hv,hunit,hframe,hzero,?_,by omega⟩
  intro r hr60 hr67
  simpa [out,Function.update,hr60] using hregs r hr67

/-- Allocate the shared unit immediately after the numeric pass. Reuse
its cursor register for the start of the branch records. -/
def stagedAfterRoundUnitBody (entry : ℕ) : Stmt :=
  .seq (stagedStretchUnitBody entry) (.assign 16 (.reg 67))

/-- The branch record buffer starts in fresh memory after the unit,
and the compact numeric outputs below the original cursor survive. -/
theorem stagedAfterRoundUnit_runs {w h entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P heap : ℕ)
    (hcall : MeetsContract w p entry (denominatorContract w h))
    (hL : st.regs 55 = L) (hP : st.regs 23 = P) (hheap : st.regs 16 = heap)
    (hw : 1 < 2^w) (hPword : P < 2^w)
    {B : ℝ} (hB : 1 ≤ B) (hwidth : 2 * (2 : ℝ)^P * B < capacity h L)
    (hz : ZeroFrom st.mem heap) (hroom : heap+2*L < 2^w) :
    ∃ out cost, Runs w p ω (stagedAfterRoundUnitBody entry) st .normal out cost ∧
      out.regs 60 = heap+L ∧ out.regs 16 = heap+2*L ∧
      Valid out.mem (heap+L) h L ∧ fixVal out.mem (heap+L) h L P = 1 ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap+2*L) ∧
      (∀ r, r ≠ 16 → r ≠ 60 → r ≠ 67 → out.regs r = st.regs r) ∧ cost ≤ 56*L+75 := by
  obtain ⟨mid,c,hu,hptr,he,hv,hval,hframe,hzero,hregs,hcost⟩ :=
    stagedStretchUnitBody_runs (ω := ω) st L P heap hcall hL hP hheap hw hPword hB hwidth hz hroom
  let out := {mid with regs := Function.update mid.regs 16 (heap+2*L)}
  have ha : Runs w p ω (.assign 16 (.reg 67)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨heap+2*L,by simp [Expr.eval,he],rfl,rfl,rfl⟩
  refine ⟨out,c+2+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hu,ha,rfl⟩),
    by simpa [out,Function.update] using hptr,by simp [out],hv,hval,hframe,hzero,?_,by omega⟩
  intro r hr16 hr60 hr67
  simpa [out,Function.update,hr16] using hregs r hr60 hr67

end MinCostFlow.LastLevelProgram
