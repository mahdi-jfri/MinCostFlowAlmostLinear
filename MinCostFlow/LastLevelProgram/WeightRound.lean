module

public import MinCostFlow.LastLevelProgram.NarrowWeight
import WordRAM.Tactic

/-!
# Updating the weights of a complete last-level round

The multiplicative update in Lemma 5.5 (page 18) is independent at
each edge once the tree stretches are known. This pass calls the
verified arithmetic on all edges and leaves their results at a
fixed stride in fresh memory.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- The final block in the allocation for edge `i`. -/
def roundWeightAddr (heap L i : ℕ) : ℕ :=
  heap + (i + 1) * narrowWeightSpace L - L

/-- Registers contain weight base, stretch base, shared denominator,
limb count, edge count, heap cursor, weight stride, and stretch stride (register eight). -/
def weightRoundArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.reg 7) (.reg 6)),
   .bin .add (.reg 1) (.bin .mul (.reg 7) (.reg 8)), .reg 2, .reg 3, .reg 5]

/-- Update all compact edge weights. The old weights may be strided. -/
def weightRoundLoop (update : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 4) (.call 5 update weightRoundArgs)

/-- The signed numerator written for one edge. -/
def roundWeightValue (mem : ℕ → ℕ) (a b d h L : ℕ) : ℤ :=
  let A := intVal mem a h L
  A + A * intVal mem b h L / intVal mem d h L

private theorem preserve_block {mem out : ℕ → ℕ} {a h L heap : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, out x = mem x) :
    (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
  have he (i : ℕ) (hi : i < L) := hf (a + i) (by omega)
  exact ⟨fun hv i hi => (he i hi).trans_lt (hv i hi), intVal_congr he⟩

/-- One pass updates all edges within the per-edge cost and scratch
budget. It preserves the original arrays and leaves a zero heap tail. -/
theorem weightRoundLoop_triple {w h update : ℕ} {p : Program}
    (hu : MeetsContract w p update (narrowWeightContract w h))
    (mem : ℕ → ℕ) (pos weights stretches denom L m heap stride stretchStride : ℕ)
    (hw : 1 < 2^w) (hm : m < 2^w)
    (ha : ∀ i < m, weights+i*stride+L ≤ heap) (hb : ∀ i < m, stretches+i*stretchStride+L ≤ heap)
    (hd : denom + L ≤ heap) (hvd : Valid mem denom h L)
    (hpos : 0 < intVal mem denom h L) (hz : ZeroFrom mem heap)
    (hroom : heap + m * narrowWeightSpace L < 2^w)
    (hinputs : ∀ i < m, Valid mem (weights + i * stride) h L ∧
      Valid mem (stretches + i * stretchStride) h L ∧
      Fits h L (roundWeightValue mem (weights + i * stride) (stretches + i * stretchStride) denom h L)) :
    Triple w p (fun st => st = startState [weights,stretches,denom,L,m,heap,stride,0,stretchStride] mem pos)
      (weightRoundLoop update)
      (normalPost fun st =>
        st.regs 5 = heap + m * narrowWeightSpace L ∧ ZeroFrom st.mem (st.regs 5) ∧
        (∀ x < heap, st.mem x = mem x) ∧
        ∀ i < m, Valid st.mem (roundWeightAddr heap L i) h L ∧
          intVal st.mem (roundWeightAddr heap L i) h L =
            roundWeightValue mem (weights + i * stride) (stretches + i * stretchStride) denom h L)
      (fun _ => (narrowWeightCost L + 30) * m + 7) := by
  let S := narrowWeightSpace L
  have hLS : L ≤ S := by
    change L ≤ widenWeightSpace L + L
    exact Nat.le_add_left _ _
  let Inv := fun i (st : State) =>
    st.regs 0 = weights ∧ st.regs 1 = stretches ∧ st.regs 2 = denom ∧ st.regs 3 = L ∧
    st.regs 4 = m ∧ st.regs 5 = heap + i * S ∧ st.regs 6 = stride ∧ st.regs 7 = i ∧ st.regs 8 = stretchStride ∧
    ZeroFrom st.mem (st.regs 5) ∧ (∀ x < heap, st.mem x = mem x) ∧
    ∀ j < i, Valid st.mem (roundWeightAddr heap L j) h L ∧
      intVal st.mem (roundWeightAddr heap L j) h L =
        roundWeightValue mem (weights + j * stride) (stretches + j * stretchStride) denom h L
  have loop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 4)
    (body := .call 5 update weightRoundArgs) (Inv := Inv)
    (P := fun st => st = startState [weights,stretches,denom,L,m,heap,stride,0,stretchStride] mem pos)
    (narrowWeightCost L + 21) 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      dsimp [Inv]
      simp [startState, hz])
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 4 = m := h.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,hzero,hframe,hdone⟩
      let a := weights + i * stride
      let b := stretches + i * stretchStride
      let cur := heap + i * S
      have ha' : a + L ≤ heap := ha i hi
      have hb' : b + L ≤ heap := hb i hi
      have hcur : cur + S < 2^w := by
        have hh := Nat.mul_le_mul_right S hi
        rw [Nat.succ_mul] at hh
        change heap + m * S < 2^w at hroom
        dsimp [cur]
        omega
      have haWord : a < 2^w := by dsimp [cur] at hcur; omega
      have hbWord : b < 2^w := by dsimp [cur] at hcur; omega
      have hdenWord : denom < 2^w := by dsimp [cur] at hcur; omega
      have hLWord : L < 2^w := by omega
      have hcurWord : cur < 2^w := by omega
      have hprodA : i * stride < 2^w := by dsimp [a] at haWord; omega
      have hprodB : i * stretchStride < 2^w := by dsimp [b] at hbWord; omega
      have haBlock := preserve_block (h := h) ha' hframe
      have hbBlock := preserve_block (h := h) hb' hframe
      have hdBlock := preserve_block (h := h) hd hframe
      obtain ⟨hva,hvb,hfit⟩ := hinputs i hi
      have hfit' : Fits h L (roundWeightValue st.mem a b denom h L) := by
        simpa only [roundWeightValue, haBlock.2, hbBlock.2, hdBlock.2] using hfit
      have hargs : evalArgs w st weightRoundArgs = some [a,b,denom,L,cur] := by
        simp [weightRoundArgs, evalArgs, Expr.eval, h0,h1,h2,h3,h5,h6,h7,h8,
          hprodA,hprodB, show weights + i * stride < 2^w from haWord,
          show stretches + i * stretchStride < 2^w from hbWord, a,b,cur]
      have hwords : ∀ x ∈ [a,b,denom,L,cur], x < 2^w := by
        simp [haWord,hbWord,hdenWord,hLWord,hcurWord]
      have hpre : (narrowWeightContract w h).pre [a,b,denom,L,cur] st.mem := by
        refine ⟨⟨_,_,_,_,_,rfl,by dsimp [cur]; omega,by dsimp [cur]; omega,
          by dsimp [cur]; omega,haBlock.1 hva,hbBlock.1 hvb,hdBlock.1 hvd,
          by rwa [hdBlock.2],hfit'⟩,?_,hcur⟩
        rwa [h5] at hzero
      obtain ⟨out,c,ret,hrun,hpost,hreg,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 5) hu hargs hwords hpre ω
      obtain ⟨hret,⟨_,_,hframe',hzero',_⟩,hv,hvalue⟩ := hpost
      change ret = cur + S at hret
      change ∀ x < cur, out.mem x = st.mem x at hframe'
      change Valid out.mem (ret - L) h L at hv
      change intVal out.mem (ret - L) h L = roundWeightValue st.mem a b denom h L at hvalue
      have hnew : ret = heap + (i + 1) * S := by
        rw [Nat.succ_mul]
        dsimp [cur] at hret
        omega
      have hindex : out.regs 7 = i := (hregs 7 (by decide)).trans h7
      refine ⟨.normal,out,c,hrun,⟨?_,hindex⟩,?_⟩
      · refine ⟨(hregs 0 (by decide)).trans h0, (hregs 1 (by decide)).trans h1,
          (hregs 2 (by decide)).trans h2, (hregs 3 (by decide)).trans h3,
          (hregs 4 (by decide)).trans h4, hreg.trans hnew,
          (hregs 6 (by decide)).trans h6, by simp, (hregs 8 (by decide)).trans h8, ?_, ?_, ?_⟩
        · change ZeroFrom out.mem (Function.update out.regs 7 (i+1) 5)
          simpa [Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),hreg] using hzero'
        · exact fun x hx => (hframe' x (by dsimp [cur]; omega)).trans (hframe x hx)
        · intro j hj
          by_cases heq : j = i
          · subst j
            change Valid out.mem (roundWeightAddr heap L i) h L ∧ _
            rw [roundWeightAddr]
            change Valid out.mem (heap + (i + 1) * S - L) h L ∧
              intVal out.mem (heap + (i + 1) * S - L) h L = _
            rw [← hnew]
            exact ⟨hv, by simpa only [roundWeightValue, haBlock.2, hbBlock.2, hdBlock.2] using hvalue⟩
          · have hj' : j < i := by omega
            have hjS : (j + 1) * S ≤ i * S := Nat.mul_le_mul_right S hj'
            have hjL : L ≤ (j + 1) * S := hLS.trans (Nat.le_mul_of_pos_left _ (by omega))
            have hprev : roundWeightAddr heap L j + L ≤ cur := by
              unfold roundWeightAddr
              change heap + (j + 1) * S - L + L ≤ cur
              dsimp [cur]
              omega
            have hcopy := preserve_block (h := h) hprev hframe'
            exact ⟨hcopy.1 (hdone j hj').1, hcopy.2.trans (hdone j hj').2⟩
      · change c ≤ argsSize weightRoundArgs + narrowWeightCost L + 1 at hcost
        simp [weightRoundArgs, argsSize, Expr.size] at hcost
        change c ≤ narrowWeightCost L + 21
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal =>
      obtain ⟨_,_,_,_,_,hret,_,_,_,hzero,hframe,hdone⟩ := h
      exact ⟨hret,hzero,hframe,hdone⟩
  · intro _ _
    simp [Expr.size_reg, Expr.size_const, Nat.mul_comm, Nat.add_assoc]

/-- The array pass implements one model weight update at each edge
when its input blocks and the scaled denominator are in place. -/
theorem roundWeightValue_decoded {mem : ℕ → ℕ} {a b d h L P : ℕ} {scale : ℤ}
    (hs : 0 < scale) (hd : intVal mem d h L = scale * (2 : ℤ)^P) :
    (roundWeightValue mem a b d h L : ℝ) / (2 : ℝ)^P =
      updateWeight P (scale : ℝ) (fixVal mem a h L P) (fixVal mem b h L P) := by
  rw [fixVal, fixVal, updateWeight_integer P _ _ _ hs, roundWeightValue, hd]


/-- Return the heap pointer after updating all edge weights. -/
def weightRoundBody (update : ℕ) : Stmt :=
  weightRoundLoop update ;; .ret (.reg 5)

/-- Callable interface for one strided weight update pass. -/
def weightRoundContract (w h : ℕ) : Contract where
  pre args mem := ∃ weights stretches denom L m heap stride stretchStride,
    args = [weights,stretches,denom,L,m,heap,stride,0,stretchStride] ∧
    1 < 2^w ∧ denom+L ≤ heap ∧ Valid mem denom h L ∧
    0 < intVal mem denom h L ∧ ZeroFrom mem heap ∧ heap+m*narrowWeightSpace L < 2^w ∧
    ∀ i < m, weights+i*stride+L ≤ heap ∧ stretches+i*stretchStride+L ≤ heap ∧
      Valid mem (weights+i*stride) h L ∧ Valid mem (stretches+i*stretchStride) h L ∧
      Fits h L (roundWeightValue mem (weights+i*stride) (stretches+i*stretchStride) denom h L)
  post args mem ret out :=
    let weights := args.getD 0 0
    let stretches := args.getD 1 0
    let denom := args.getD 2 0
    let L := args.getD 3 0
    let m := args.getD 4 0
    let heap := args.getD 5 0
    let stride := args.getD 6 0
    let stretchStride := args.getD 8 0
    ret = heap+m*narrowWeightSpace L ∧ ZeroFrom out ret ∧
    (∀ a < heap, out a = mem a) ∧
    ∀ i < m, Valid out (roundWeightAddr heap L i) h L ∧
      intVal out (roundWeightAddr heap L i) h L =
        roundWeightValue mem (weights+i*stride) (stretches+i*stretchStride) denom h L
  cost args _ := (narrowWeightCost (args.getD 3 0)+30)*args.getD 4 0+10

/-- The strided weight pass implements the callable round contract. -/
theorem weightRound_meetsContract {w h entry update : ℕ} {p : Program}
    (he : p.procs[entry]? = some (weightRoundBody update))
    (hu : MeetsContract w p update (narrowWeightContract w h)) :
    MeetsContract w p entry (weightRoundContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨weights,stretches,denom,L,m,heap,stride,stretchStride,rfl,hw,
    hd,hvd,hpos,hz,hroom,hinputs⟩ := hpre
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := weightRoundLoop_triple hu mem pos weights stretches
    denom L m heap stride stretchStride hw (hwords m (by simp))
    (fun i hi => (hinputs i hi).1) (fun i hi => (hinputs i hi).2.1)
    hd hvd hpos hz hroom (fun i hi => (hinputs i hi).2.2) _ ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    have hrun : Runs w p ω (.ret (.reg 5)) mid (.returned (mid.regs 5)) mid 2 :=
      runs_ret_iff.mpr ⟨mid.regs 5,rfl,rfl,rfl,rfl⟩
    refine ⟨.returned (mid.regs 5),mid,c+3,
      runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hr,hrun,by omega⟩),hpost,?_⟩
    change c ≤ (narrowWeightCost L+30)*m+7 at hcost
    change c+3 ≤ (narrowWeightCost L+30)*m+10
    omega
end MinCostFlow.LastLevelProgram
