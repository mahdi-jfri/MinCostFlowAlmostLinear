module

public import MinCostFlow.LastLevelProgram.FormatBit
public import MinCostFlow.LastLevelProgram.IndexGraph
import WordRAM.Tactic

/-!
# Packing converted length blocks

The tree query of Definition 5.8 (pages 19–20) reads the live lengths
in compact edge order. The packing pass converts each named source
block to the common precision and the one-bit format of Theorem 2.2.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Registers hold the source, destination, names, source width, caller
precision, guest precision, guest width, edge count, and loop index. -/
def packGuestLengthsArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.load (.bin .add (.reg 2) (.reg 8))) (.reg 3)),
    .reg 3,.reg 4,.reg 5, .bin .add (.reg 1) (.bin .mul (.reg 8) (.reg 6)), .reg 6]

/-- Convert live lengths into consecutive guest blocks. -/
def packGuestLengthsLoop (convert : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 7) (.call 9 convert packGuestLengthsArgs)

/-- The packing loop writes canonical guest encodings and frames the
input tables. It charges one conversion per live edge. -/
theorem packGuestLengthsLoop_triple {w convert : ℕ} {p : Program}
    (hp : MeetsContract w p convert (guestLengthBlockContract w))
    (mem : ℕ → ℕ) (pos src dst names L P Q N cap : ℕ) (G : MGraph)
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P+N < 2^w) (hQ : Q < 2^w)
    (hm : G.m < 2^w) (hsrc : src+cap*L ≤ dst) (hname : names+G.m ≤ dst)
    (hroom : dst+G.m*N < 2^w)
    (hnames : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hvalid : ∀ e ∈ G.E, Valid mem (src+e*L) 4 L ∧ 0 ≤ intVal mem (src+e*L) 4 L ∧
      Fits 1 N (queryNumerator Q (fixVal mem (src+e*L) 4 L P))) :
    let enc := fun e => encodeLimbs 1 N (queryNumerator Q (fixVal mem (src+e*L) 4 L P))
    Triple w p (fun st => st = startState [src,dst,names,L,P,Q,N,G.m] mem pos)
      (packGuestLengthsLoop convert)
      (normalPost fun st =>
        (∀ i < G.m, ListAt st.mem (dst+i*N) (enc (edgeName G i))) ∧
        ∀ a, a < dst ∨ dst+G.m*N ≤ a → st.mem a = mem a)
      (fun _ => (80*N+37)*G.m+7) := by
  intro enc
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = names ∧ st.regs 3 = L ∧
    st.regs 4 = P ∧ st.regs 5 = Q ∧ st.regs 6 = N ∧ st.regs 7 = G.m ∧ st.regs 8 = i ∧
    (∀ j < i, ListAt st.mem (dst+j*N) (enc (edgeName G j))) ∧
    ∀ a, a < dst ∨ dst+i*N ≤ a → st.mem a = mem a
  have loop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := .call 9 convert packGuestLengthsArgs) (Inv := Inv)
    (P := fun st => st = startState [src,dst,names,L,P,Q,N,G.m] mem pos)
    (80*N+28) 0 G.m (Nat.zero_le _) (by omega) (fun _ => hm)
    (fun st h => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by have hr := h.2.2.2.2.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,hdone,hframe⟩ => by
      let e := edgeName G i
      let a := src+e*L
      let b := dst+i*N
      have he : e ∈ G.E := edgeName_mem hi
      have hs := Nat.mul_le_mul_right L (hcap e he)
      have hb := Nat.mul_le_mul_right N hi
      rw [Nat.succ_mul] at hs hb
      have ha : a+L ≤ dst := by dsimp [a]; omega
      have hbr : b+N < 2^w := by dsimp [b]; omega
      have hmAt : Expr.MemAt st (names+i) e :=
        (hframe _ (Or.inl (by omega))).trans (hnames i hi)
      have hargs : evalArgs w st packGuestLengthsArgs = some [a,L,P,Q,b,N] := by
        have hnm : names+i < 2^w := by omega
        have hsrcWord : a < 2^w := by omega
        have hdstWord : b < 2^w := by omega
        have hp₁ : e*L < 2^w := by dsimp [a] at hsrcWord; omega
        have hp₂ : i*N < 2^w := by dsimp [b] at hdstWord; omega
        dsimp [packGuestLengthsArgs,a,b]
        eval_expr
      obtain ⟨hv,hn,hfit⟩ := hvalid e he
      have hread : ∀ k < L, st.mem (a+k) = mem (a+k) :=
        fun k hk => hframe _ (Or.inl (by omega))
      have hnum : intVal st.mem a 4 L = intVal mem a 4 L := intVal_congr hread
      have hv' : Valid st.mem a 4 L := fun k hk => (hread k hk).trans_lt (hv k hk)
      obtain ⟨out,cost,ret,hr,hpost,_,hf,hcost⟩ :=
        runs_call_of_meetsContract (r := 9) hp hargs
          (by
            intro x hx
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
          ⟨a,L,P,Q,b,N,rfl,hw,hP,hQ,hL,ha.trans (Nat.le_add_right ..),hbr,
            hv',hnum.symm ▸ hn,by simpa only [fixVal,hnum] using hfit⟩ ω
      obtain ⟨a',L',P',Q',b',N',heq,_,henc,hother⟩ := hpost
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      refine ⟨.normal,out,cost,hr,⟨⟨(hf 0 (by decide)).trans h0,(hf 1 (by decide)).trans h1,
        (hf 2 (by decide)).trans h2,(hf 3 (by decide)).trans h3,(hf 4 (by decide)).trans h4,
        (hf 5 (by decide)).trans h5,(hf 6 (by decide)).trans h6,(hf 7 (by decide)).trans h7,
        by simp,?_,?_⟩,(hf 8 (by decide)).trans h8⟩,?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [enc,fixVal,hnum] using henc
        · have hj' : j < i := by omega
          intro k hk
          have hk' : k < N := by simpa [enc] using hk
          have hmul := Nat.mul_le_mul_right N hj'
          rw [Nat.succ_mul] at hmul
          change out.mem (dst+j*N+k) = _
          exact (hother _ (Or.inl (by dsimp [b]; omega))).trans (hdone j hj' k hk)
      · intro x hx
        have hb' : dst+(i+1)*N = b+N := by simp [b,Nat.succ_mul,Nat.add_assoc]
        rw [hb'] at hx
        change out.mem x = _
        exact (hother x (hx.imp_left (by dsimp [b]; omega))).trans
          (hframe x (hx.imp_right (by dsimp [b]; omega)))
      · apply hcost.trans
        change 17+(80*N+10)+1 ≤ 80*N+28
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.2.2.2.2.2.2.2.2.2
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm G.m]

/-- Pack the lengths and return zero, leaving all other words unchanged. -/
def packGuestLengthsBody (convert : ℕ) : Stmt :=
  .seq (packGuestLengthsLoop convert) (.ret (.const 0))

/-- The callable packer converts the live lengths to the selected guest format. -/
def packGuestLengthsContract (w cap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ src dst names L P Q N,
    args = [src,dst,names,L,P,Q,N,G.m] ∧
    16 ≤ 2^w ∧ 4*L < 2^w ∧ P+N < 2^w ∧ Q < 2^w ∧ G.m < 2^w ∧
    src+cap*L ≤ dst ∧ names+G.m ≤ dst ∧ dst+G.m*N < 2^w ∧
    (∀ i < G.m, mem (names+i) = edgeName G i) ∧
    (∀ e ∈ G.E, e < cap) ∧
    ∀ e ∈ G.E, Valid mem (src+e*L) 4 L ∧ 0 ≤ intVal mem (src+e*L) 4 L ∧
      Fits 1 N (queryNumerator Q (fixVal mem (src+e*L) 4 L P))
  post args mem ret out := ∃ src dst names L P Q N,
    args = [src,dst,names,L,P,Q,N,G.m] ∧ ret = 0 ∧
    (∀ i < G.m, ListAt out (dst+i*N)
      (encodeLimbs 1 N (queryNumerator Q (fixVal mem (src+edgeName G i*L) 4 L P)))) ∧
    ∀ a, a < dst ∨ dst+G.m*N ≤ a → out a = mem a
  cost args _ := (80*args.getD 6 0+37)*G.m+10

/-- The installed packer returns the compact length arrays with an
explicit bound on the conversion work. -/
theorem packGuestLengths_meetsContract {w entry convert cap : ℕ} {p : Program}
    (G : MGraph)
    (he : p.procs[entry]? = some (packGuestLengthsBody convert))
    (hp : MeetsContract w p convert (guestLengthBlockContract w)) :
    MeetsContract w p entry (packGuestLengthsContract w cap G) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,names,L,P,Q,N,rfl,hw,hL,hP,hQ,hm,hsrc,hnames,hroom,
    hnamesAt,hcap,hvalid⟩ := hpre
  apply runs_start_le
  unfold packGuestLengthsBody
  refine runs_seq_triple_le (packGuestLengthsLoop_triple hp mem pos src dst names L P Q N cap G
    hw hL hP hQ hm hsrc hnames hroom hnamesAt hcap hvalid) rfl ?_
  intro out ⟨henc,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨src,dst,names,L,P,Q,N,rfl,rfl,henc,hframe⟩ ?_
  change 0+((80*N+37)*G.m+7)+1+2 ≤ (80*N+37)*G.m+10
  omega

/-- The converter reads host weights using the runtime source stride. -/
def packGuestStridedArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.reg 8) (.reg 2)),
    .reg 3,.reg 4,.reg 5, .bin .add (.reg 1) (.bin .mul (.reg 8) (.reg 6)), .reg 6]

/-- Convert strided host weights into consecutive guest blocks. -/
def packGuestStridedLoop (convert : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 7) (.call 9 convert packGuestStridedArgs)

/-- The strided packing loop writes canonical guest encodings and frames the
input tables. It charges one conversion per live edge. -/
theorem packGuestStridedLoop_triple {w convert : ℕ} {p : Program}
    (hp : MeetsContract w p convert (guestLengthBlockContract w))
    (mem : ℕ → ℕ) (pos src dst stride L P Q N m : ℕ)
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P+N < 2^w) (hQ : Q < 2^w)
    (hm : m < 2^w) (hstride : L ≤ stride) (hsrc : ∀ i < m, src+i*stride+L ≤ dst)
    (hroom : dst+m*N < 2^w)
    (hvalid : ∀ i < m, Valid mem (src+i*stride) 4 L ∧ 0 ≤ intVal mem (src+i*stride) 4 L ∧
      Fits 1 N (queryNumerator Q (fixVal mem (src+i*stride) 4 L P))) :
    let enc := fun e => encodeLimbs 1 N (queryNumerator Q (fixVal mem (src+e*stride) 4 L P))
    Triple w p (fun st => st = startState [src,dst,stride,L,P,Q,N,m] mem pos)
      (packGuestStridedLoop convert)
      (normalPost fun st =>
        (∀ i < m, ListAt st.mem (dst+i*N) (enc i)) ∧
        ∀ a, a < dst ∨ dst+m*N ≤ a → st.mem a = mem a)
      (fun _ => (80*N+37)*m+7) := by
  intro enc
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = stride ∧ st.regs 3 = L ∧
    st.regs 4 = P ∧ st.regs 5 = Q ∧ st.regs 6 = N ∧ st.regs 7 = m ∧ st.regs 8 = i ∧
    (∀ j < i, ListAt st.mem (dst+j*N) (enc j)) ∧
    ∀ a, a < dst ∨ dst+i*N ≤ a → st.mem a = mem a
  have loop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := .call 9 convert packGuestStridedArgs) (Inv := Inv)
    (P := fun st => st = startState [src,dst,stride,L,P,Q,N,m] mem pos)
    (80*N+28) 0 m (Nat.zero_le _) (by omega) (fun _ => hm)
    (fun st h => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by have hr := h.2.2.2.2.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,hdone,hframe⟩ => by
      let a := src+i*stride
      let b := dst+i*N
      have hs := Nat.mul_le_mul_right stride hi
      have hb := Nat.mul_le_mul_right N hi
      rw [Nat.succ_mul] at hs hb
      have ha : a+L ≤ dst := hsrc i hi
      have hbr : b+N < 2^w := by dsimp [b]; omega
      have hargs : evalArgs w st packGuestStridedArgs = some [a,L,P,Q,b,N] := by
        have hsrcWord : a < 2^w := by omega
        have hdstWord : b < 2^w := by omega
        have hp₁ : i*stride < 2^w := by dsimp [a] at hsrcWord; omega
        have hp₂ : i*N < 2^w := by dsimp [b] at hdstWord; omega
        dsimp [packGuestStridedArgs,a,b]
        eval_expr
      obtain ⟨hv,hn,hfit⟩ := hvalid i hi
      have hread : ∀ k < L, st.mem (a+k) = mem (a+k) :=
        fun k hk => hframe _ (Or.inl (by omega))
      have hnum : intVal st.mem a 4 L = intVal mem a 4 L := intVal_congr hread
      have hv' : Valid st.mem a 4 L := fun k hk => (hread k hk).trans_lt (hv k hk)
      obtain ⟨out,cost,ret,hr,hpost,_,hf,hcost⟩ :=
        runs_call_of_meetsContract (r := 9) hp hargs
          (by
            intro x hx
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
          ⟨a,L,P,Q,b,N,rfl,hw,hP,hQ,hL,ha.trans (Nat.le_add_right ..),hbr,
            hv',hnum.symm ▸ hn,by simpa only [fixVal,hnum] using hfit⟩ ω
      obtain ⟨a',L',P',Q',b',N',heq,_,henc,hother⟩ := hpost
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      refine ⟨.normal,out,cost,hr,⟨⟨(hf 0 (by decide)).trans h0,(hf 1 (by decide)).trans h1,
        (hf 2 (by decide)).trans h2,(hf 3 (by decide)).trans h3,(hf 4 (by decide)).trans h4,
        (hf 5 (by decide)).trans h5,(hf 6 (by decide)).trans h6,(hf 7 (by decide)).trans h7,
        by simp,?_,?_⟩,(hf 8 (by decide)).trans h8⟩,?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [enc,fixVal,hnum] using henc
        · have hj' : j < i := by omega
          intro k hk
          have hk' : k < N := by simpa [enc] using hk
          have hmul := Nat.mul_le_mul_right N hj'
          rw [Nat.succ_mul] at hmul
          change out.mem (dst+j*N+k) = _
          exact (hother _ (Or.inl (by dsimp [b]; omega))).trans (hdone j hj' k hk)
      · intro x hx
        have hb' : dst+(i+1)*N = b+N := by simp [b,Nat.succ_mul,Nat.add_assoc]
        rw [hb'] at hx
        change out.mem x = _
        exact (hother x (hx.imp_left (by dsimp [b]; omega))).trans
          (hframe x (hx.imp_right (by dsimp [b]; omega)))
      · apply hcost.trans
        change 14+(80*N+10)+1 ≤ 80*N+28
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.2.2.2.2.2.2.2.2.2
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm m]

/-- Return after converting the strided host weights. -/
def packGuestStridedBody (convert : ℕ) : Stmt :=
  .seq (packGuestStridedLoop convert) (.ret (.const 0))

/-- The runtime arguments determine the input stride and both formats. -/
def packGuestStridedContract (w : ℕ) : Contract where
  pre args mem := ∃ src dst stride L P Q N m,
    args = [src,dst,stride,L,P,Q,N,m] ∧
    16 ≤ 2^w ∧ 4*L < 2^w ∧ P+N < 2^w ∧ Q < 2^w ∧ m < 2^w ∧
    L ≤ stride ∧ (∀ i < m, src+i*stride+L ≤ dst) ∧ dst+m*N < 2^w ∧
    ∀ i < m, Valid mem (src+i*stride) 4 L ∧ 0 ≤ intVal mem (src+i*stride) 4 L ∧
      Fits 1 N (queryNumerator Q (fixVal mem (src+i*stride) 4 L P))
  post args mem ret out := ∃ src dst stride L P Q N m,
    args = [src,dst,stride,L,P,Q,N,m] ∧ ret = 0 ∧
    (∀ i < m, ListAt out (dst+i*N)
      (encodeLimbs 1 N (queryNumerator Q (fixVal mem (src+i*stride) 4 L P)))) ∧
    ∀ a, a < dst ∨ dst+m*N ≤ a → out a = mem a
  cost args _ := (80*args.getD 6 0+37)*args.getD 7 0+10

/-- The strided converter meets its call interface for every runtime
choice of the host and guest formats. -/
theorem packGuestStrided_meetsContract {w entry convert : ℕ} {p : Program}
    (he : p.procs[entry]? = some (packGuestStridedBody convert))
    (hp : MeetsContract w p convert (guestLengthBlockContract w)) :
    MeetsContract w p entry (packGuestStridedContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,stride,L,P,Q,N,m,rfl,hw,hL,hP,hQ,hm,hstride,hsrc,hroom,hvalid⟩ := hpre
  apply runs_start_le
  unfold packGuestStridedBody
  refine runs_seq_triple_le (packGuestStridedLoop_triple hp mem pos src dst stride L P Q N m
    hw hL hP hQ hm hstride hsrc hroom hvalid) rfl ?_
  intro out ⟨henc,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨src,dst,stride,L,P,Q,N,m,rfl,rfl,henc,hframe⟩ ?_
  change 0+((80*N+37)*m+7)+1+2 ≤ (80*N+37)*m+10
  omega

end MinCostFlow.LastLevelProgram
