module

public import MinCostFlow.LastLevelProgram.ScaleBlock
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Entry
import MinCostFlow.Num.EqualityFacts
public import MinCostFlow.Num.Encoding

/-!
# Packing weights at the common LSST precision

Between last-level rounds, the local-grid weights can be stored
at a stride. Gather those blocks and shift each integer numerator
to the common precision in one pass.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- Registers contain source, stride, limb count, edge count, shift,
and heap cursor. Each shift appends one block to the compact array. -/
def packPrecisionArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.reg 6) (.reg 1)), .reg 2, .reg 4, .reg 5]

/-- Pack and shift the blocks in increasing compact edge order. -/
def packPrecisionLoop (shift : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 3) (.call 5 shift packPrecisionArgs)

private theorem block_agrees {m₁ m₂ : ℕ → ℕ} {a h L heap : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, m₂ x = m₁ x) :
    (Valid m₁ a h L → Valid m₂ a h L) ∧ intVal m₂ a h L = intVal m₁ a h L := by
  have he (i : ℕ) (hi : i < L) := hf (a+i) (by omega)
  exact ⟨fun hv i hi => (he i hi).trans_lt (hv i hi), intVal_congr he⟩

/-- Gather a strided table into a compact table and preserve its decoded
values at the refined precision. The shifted numerators must fit. -/
theorem packPrecisionLoop_triple {w h shift : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hp : p.HasAt shift (shiftLeftModule shift h))
    (mem : ℕ → ℕ) (pos src stride L m P Q heap : ℕ)
    (hword : 1 < 2^w) (hm : m < 2^w)
    (hbits : Q-P < 2^w) (hPQ : P ≤ Q)
    (hsrc : ∀ i < m, src+i*stride+L ≤ heap) (hz : ZeroFrom mem heap)
    (hroom : heap + m*L < 2^w)
    (hinput : ∀ i < m, Valid mem (src + i*stride) h L ∧
      Fits h L (intVal mem (src + i*stride) h L * (2 : ℤ)^(Q-P))) :
    Triple w p (fun st => st = startState [src,stride,L,m,Q-P,heap] mem pos)
      (packPrecisionLoop shift)
      (normalPost fun st =>
        st.regs 5 = heap + m*L ∧ ZeroFrom st.mem (st.regs 5) ∧
        (∀ x < heap, st.mem x = mem x) ∧
        ∀ i < m, Valid st.mem (heap + i*L) h L ∧
          fixVal st.mem (heap + i*L) h L Q = fixVal mem (src + i*stride) h L P)
      (fun _ => (35*L+60)*m+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = stride ∧ st.regs 2 = L ∧
    st.regs 3 = m ∧ st.regs 4 = Q-P ∧ st.regs 5 = heap+i*L ∧ st.regs 6 = i ∧
    ZeroFrom st.mem (st.regs 5) ∧ (∀ x < heap, st.mem x = mem x) ∧
    ∀ j < i, Valid st.mem (heap+j*L) h L ∧
      fixVal st.mem (heap+j*L) h L Q = fixVal mem (src+j*stride) h L P
  have loop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 3)
    (body := .call 5 shift packPrecisionArgs) (Inv := Inv)
    (P := fun st => st = startState [src,stride,L,m,Q-P,heap] mem pos)
    (35*L+51) 0 m (Nat.zero_le _) hword (fun _ => hm)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,hz]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 3 = m := h.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,hzero,hframe,hdone⟩
      let a := src+i*stride
      let cur := heap+i*L
      have ha : a + L ≤ heap := hsrc i (by omega)
      have hcur : cur + L < 2^w := by
        have he := Nat.mul_le_mul_right L hi
        rw [Nat.succ_mul] at he
        dsimp [cur]
        omega
      have haWord : a < 2^w := by dsimp [cur] at hcur; omega
      have heWord : i*stride < 2^w := by dsimp [a] at haWord; omega
      have hL : L < 2^w := by omega
      have hargs : evalArgs w st packPrecisionArgs = some [a,L,Q-P,cur] := by
        simp [packPrecisionArgs, evalArgs, Expr.eval, h0,h1,h2,h4,h5,h6,
          heWord, show src+i*stride < 2^w from haWord,a,cur]
      have hwords : ∀ x ∈ [a,L,Q-P,cur], x < 2^w := by
        simp [haWord,hL,hbits, show cur < 2^w by omega]
      have hblock := block_agrees (h := h) ha hframe
      obtain ⟨out,c,ret,hrun,hpost,hreg,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 5) (shiftLeft_meetsContract hh hw hp) hargs hwords
          ⟨⟨a,L,Q-P,cur,rfl,by dsimp [cur]; omega,hblock.1 (hinput i hi).1⟩,
            by rwa [h5] at hzero,hcur⟩ ω
      obtain ⟨hret,_,_,hf,hz',hv,hval⟩ := hpost
      change ret = cur + L at hret
      change ∀ x < cur, out.mem x = st.mem x at hf
      change Valid out.mem cur h L at hv
      change intVal out.mem cur h L =
        wrap h L (intVal st.mem a h L * (2 : ℤ)^(Q-P)) at hval
      rw [hblock.2, wrap_of_fits (hinput i hi).2] at hval
      have hnext : ret = heap + (i+1)*L := by
        rw [Nat.succ_mul]
        dsimp [cur] at hret
        omega
      have hindex : out.regs 6 = i := (hregs 6 (by decide)).trans h6
      refine ⟨.normal,out,c,hrun,⟨?_,hindex⟩,?_⟩
      · refine ⟨(hregs 0 (by decide)).trans h0,(hregs 1 (by decide)).trans h1,
          (hregs 2 (by decide)).trans h2,(hregs 3 (by decide)).trans h3,
          (hregs 4 (by decide)).trans h4,hreg.trans hnext,by simp,?_,?_,?_⟩
        · change ZeroFrom out.mem (Function.update out.regs 6 (i+1) 5)
          simpa [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6),hreg] using hz'
        · exact fun x hx => (hf x (by dsimp [cur]; omega)).trans (hframe x hx)
        · intro j hj
          by_cases heq : j = i
          · subst j
            exact ⟨hv, fixVal_of_shift hPQ hval⟩
          · have hj' : j < i := by omega
            have hfit := Nat.mul_le_mul_right L hj'
            rw [Nat.succ_mul] at hfit
            have hcopy := block_agrees (h := h) (show heap+j*L+L ≤ cur by dsimp [cur]; omega) hf
            exact ⟨hcopy.1 (hdone j hj').1, by rw [fixVal,hcopy.2]; exact (hdone j hj').2⟩
      · change c ≤ argsSize packPrecisionArgs + (35*L+35) + 1 at hcost
        simp [packPrecisionArgs,argsSize,Expr.size] at hcost
        change c ≤ 35*L+51
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal =>
      obtain ⟨_,_,_,_,_,hret,_,hzero,hframe,hdone⟩ := h
      exact ⟨hret,hzero,hframe,hdone⟩
  · intro _ _
    simp [Expr.size_reg,Expr.size_const,Nat.mul_comm,Nat.add_assoc]

/-- The same fit bound used for the canonical query gives fit for each
shift from local weight storage. -/
theorem packPrecision_fits {mem : ℕ → ℕ} {src h L P Q : ℕ}
    {x B : ℝ} (hPQ : P ≤ Q) (heq : fixVal mem src h L P = x)
    (hx : 0 < x) (hB : x ≤ B) (hwidth : 2 * (2 : ℝ)^Q * B < capacity h L) :
    Fits h L (intVal mem src h L * (2 : ℤ)^(Q-P)) := by
  have hgrid : ∃ a : ℤ, x = (a : ℝ) / (2 : ℝ)^Q :=
    queryGrid_mono hPQ ⟨intVal mem src h L, heq.symm⟩
  have hfit := (queryNumerator_fits hx hB hwidth hgrid).2
  rwa [← heq, queryNumerator_of_shift hPQ] at hfit

private theorem limbs_eq_of_intVal_eq {mem out : ℕ → ℕ} {a b h L : ℕ}
    (ha : Valid mem a h L) (hb : Valid out b h L)
    (hv : intVal mem a h L = intVal out b h L) :
    ∀ i < L, mem (a+i) = out (b+i) := by
  induction L generalizing a b with
  | zero => intro i hi; omega
  | succ L ih =>
    obtain ⟨hh,ht⟩ := (intVal_eq_succ_iff ha hb).1 hv
    intro i hi
    cases i with
    | zero => simpa using hh
    | succ i =>
      have he := ih (valid_succ.mp ha).2 (valid_succ.mp hb).2 ht i (by omega)
      simpa only [Nat.add_assoc,Nat.add_comm 1] using he

/-- A valid block that decodes to a fitting integer is its canonical
limb encoding. -/
theorem listAt_encodeLimbs_of_intVal {mem : ℕ → ℕ} {a h L : ℕ} {n : ℤ}
    (hv : Valid mem a h L) (hn : Fits h L n) (he : intVal mem a h L = n) :
    ListAt mem a (encodeLimbs h L n) := by
  let enc := encodeLimbs h L n
  have hinit := listAt_initMem enc
  have hvalid : Valid (initMem enc) 0 h L := valid_encodeLimbs hinit
  have hval : intVal (initMem enc) 0 h L = n := intVal_encodeLimbs hinit hn
  intro i hi
  have hi' : i < L := by simpa using hi
  exact (limbs_eq_of_intVal_eq hv hvalid (he.trans hval.symm) i hi').trans (hinit i hi)

/-- A packed weight block that decodes at the guest precision contains
exactly the integer numerator expected by the canonical query. -/
theorem packPrecision_guestEncoding {mem out : ℕ → ℕ} {a b L P Q : ℕ}
    (hv : Valid out b 1 L)
    (he : fixVal out b 1 L Q = fixVal mem a 1 L P)
    (hfit : Fits 1 L (queryNumerator Q (fixVal mem a 1 L P))) :
    ListAt out b (encodeLimbs 1 L (queryNumerator Q (fixVal mem a 1 L P))) := by
  have h := queryNumerator_grid Q (intVal out b 1 L)
  change queryNumerator Q (fixVal out b 1 L Q) = intVal out b 1 L at h
  rw [he] at h
  exact listAt_encodeLimbs_of_intVal hv hfit h.symm

/-- Pack the strided weights at the guest precision and return their end. -/
def packGuestWeightsBody (shift : ℕ) : Stmt :=
  .seq (packPrecisionLoop shift) (.ret (.reg 5))

/-- The guest weight packer writes canonical bit blocks and leaves the
allocation prefix and fresh suffix available to the relocated call. -/
noncomputable def packGuestWeightsContract (w P Q : ℕ) : Contract where
  pre args mem := ∃ src stride L m heap,
    args = [src,stride,L,m,Q-P,heap] ∧
    1 < 2^w ∧ m < 2^w ∧ L ≤ stride ∧ Q-P < 2^w ∧ P ≤ Q ∧
    src+m*stride ≤ heap ∧ ZeroFrom mem heap ∧ heap+m*L < 2^w ∧
    ∀ i < m, Valid mem (src+i*stride) 1 L ∧
      Fits 1 L (queryNumerator Q (fixVal mem (src+i*stride) 1 L P))
  post args mem ret out := ∃ src stride L m heap,
    args = [src,stride,L,m,Q-P,heap] ∧ ret = heap+m*L ∧ ZeroFrom out ret ∧
    (∀ x < heap, out x = mem x) ∧
    ∀ i < m, ListAt out (heap+i*L)
      (encodeLimbs 1 L (queryNumerator Q (fixVal mem (src+i*stride) 1 L P)))
  cost args _ := (35*args.getD 2 0+60)*args.getD 3 0+10

/-- Link the guest weight packer at the two runtime arithmetic precisions. -/
theorem packGuestWeights_meetsContract {w entry shift P Q : ℕ} {p : Program}
    (he : p.procs[entry]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (shiftLeftModule shift 1)) (hw : 4 ≤ w) :
    MeetsContract w p entry (packGuestWeightsContract w P Q) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,stride,L,m,heap,rfl,hword,hm,hstride,hbits,hPQ,hsrc,hz,hroom,hinput⟩ := hpre
  have hfit (i : ℕ) (hi : i < m) :
      Valid mem (src+i*stride) 1 L ∧
        Fits 1 L (intVal mem (src+i*stride) 1 L * (2 : ℤ)^(Q-P)) := by
    obtain ⟨hv,hf⟩ := hinput i hi
    rw [queryNumerator_of_shift hPQ] at hf
    exact ⟨hv,hf⟩
  apply runs_start_le
  unfold packGuestWeightsBody
  refine runs_seq_triple_le (packPrecisionLoop_triple (by decide) hw hp mem pos
    src stride L m P Q heap hword hm hbits hPQ (fun i hi => by
      have hb := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hb
      omega) hz hroom hfit) rfl ?_
  intro st ⟨hret,hzero,hframe,hdone⟩
  refine runs_ret_le (v := heap+m*L) (by eval_expr)
    ⟨src,stride,L,m,heap,rfl,rfl,hret ▸ hzero,hframe,?_⟩ ?_
  · intro i hi
    obtain ⟨hv,heq⟩ := hdone i hi
    exact packPrecision_guestEncoding hv heq (hinput i hi).2
  · change 0+((35*L+60)*m+7)+1+2 ≤ (35*L+60)*m+10
    omega

/-- Gather strided host-format weights into a compact array at the same
precision, with a zero shift in the shared packing body. -/
def packHostWeightsContract (w h P : ℕ) : Contract where
  pre args mem := ∃ src stride L m heap,
    args = [src,stride,L,m,0,heap] ∧
    1 < 2^w ∧ m < 2^w ∧ L ≤ stride ∧ (∀ i < m, src+i*stride+L ≤ heap) ∧
    ZeroFrom mem heap ∧ heap+m*L < 2^w ∧
    ∀ i < m, Valid mem (src+i*stride) h L
  post args mem ret out := ∃ src stride L m heap,
    args = [src,stride,L,m,0,heap] ∧ ret = heap+m*L ∧ ZeroFrom out ret ∧
    (∀ a < heap, out a = mem a) ∧
    ∀ i < m, Valid out (heap+i*L) h L ∧
      fixVal out (heap+i*L) h L P = fixVal mem (src+i*stride) h L P
  cost args _ := (35*args.getD 2 0+60)*args.getD 3 0+10

/-- The same packing loop can preserve the host weight precision.
Every valid source numerator fits because the shift is zero. -/
theorem packHostWeights_meetsContract {w h P entry shift : ℕ} {p : Program}
    (he : p.procs[entry]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w) :
    MeetsContract w p entry (packHostWeightsContract w h P) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,stride,L,m,heap,rfl,hword,hm,hstride,hsrc,hz,hroom,hinput⟩ := hpre
  have hfit (i : ℕ) (hi : i < m) :
      Valid mem (src+i*stride) h L ∧
        Fits h L (intVal mem (src+i*stride) h L * (2 : ℤ)^(P-P)) := by
    have hv := hinput i hi
    exact ⟨hv,by simpa only [Nat.sub_self,pow_zero,mul_one] using intVal_fits hv⟩
  have ht := packPrecisionLoop_triple hh hw hp mem pos src stride L m P P heap
    hword hm (by simp) le_rfl hsrc hz hroom hfit
  rw [Nat.sub_self] at ht
  apply runs_start_le
  unfold packGuestWeightsBody
  refine runs_seq_triple_le ht rfl ?_
  intro st ⟨hret,hzero,hframe,hpacked⟩
  refine runs_ret_le (v := heap+m*L) (by eval_expr)
    ⟨src,stride,L,m,heap,rfl,rfl,hret ▸ hzero,hframe,hpacked⟩ ?_
  change 0+((35*L+60)*m+7)+1+2 ≤ (35*L+60)*m+10
  omega

end MinCostFlow.LastLevelProgram
