module

public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.Num.Representation
public import MinCostFlow.Num.SignExtend
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Packing the lengths and weights for Theorem 2.2

The last-level rebuild puts the numeric blocks in compact edge order.
One call to the shared copy procedure moves each block, preserving
its signed fixed-point value and the source tables.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- The input block base, output block base, and block width for one copy.
Registers zero through four hold the source, destination, edge-name array,
block width, and count. Register five is the compact edge index. -/
def packValueArgs : List Expr :=
  [.bin .add (.reg 0)
    (.bin .mul (.load (.bin .add (.reg 2) (.reg 5))) (.reg 3)),
    .bin .add (.reg 1) (.bin .mul (.reg 5) (.reg 3)), .reg 3]

/-- Copy an edge-name-indexed table into compact edge order. -/
def packValuesLoop (copy : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 4) (.call 6 copy packValueArgs)

/-- The widening call reads the length at the original edge name
and writes it at the compact index using a distinct scratch width. -/
def packWideValueArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.load (.bin .add (.reg 2) (.reg 5))) (.reg 3)),
    .reg 3, .reg 7, .bin .add (.reg 1) (.bin .mul (.reg 5) (.reg 7))]

/-- Widen a caller-format length table into the numeric scratch region.
Arguments are the source, destination, names, caller width, edge count,
a loop index slot, a return slot, and the scratch width. -/
def packWideValuesBody (extend : ℕ) : Stmt :=
  .seq (forRange 5 (.const 0) (.reg 4) (.call 6 extend packWideValueArgs)) (.ret (.const 0))

/-- The widening call uses the caller width for source addressing and
the scratch width for destination addressing. -/
theorem packWideValueArgs_eval {w : ℕ} (st : State)
    (src dst names L K i e : ℕ)
    (h0 : st.regs 0 = src) (h1 : st.regs 1 = dst) (h2 : st.regs 2 = names)
    (h3 : st.regs 3 = L) (h5 : st.regs 5 = i) (h7 : st.regs 7 = K)
    (hname : st.mem (names+i) = e) (hnames : names+i < 2^w)
    (ha : src+e*L < 2^w) (hb : dst+i*K < 2^w) :
    evalArgs w st packWideValueArgs = some [src+e*L,L,K,dst+i*K] := by
  unfold packWideValueArgs
  eval_expr

/-- A strided weight table already uses compact edge indices. Widening
reads each source at its stride and writes a dense scratch array. -/
def packWideWeightArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.reg 5) (.reg 2)),
    .reg 3, .reg 7, .bin .add (.reg 1) (.bin .mul (.reg 5) (.reg 7))]

/-- Widen the live weights into the scratch format used by the update. -/
def packWideWeightsBody (extend : ℕ) : Stmt :=
  .seq (forRange 5 (.const 0) (.reg 4) (.call 6 extend packWideWeightArgs)) (.ret (.const 0))

/-- The output stride is the scratch width and the source stride is
the distance between live weight blocks. -/
theorem packWideWeightArgs_eval {w : ℕ} (st : State)
    (src dst stride L K i : ℕ)
    (h0 : st.regs 0 = src) (h1 : st.regs 1 = dst) (h2 : st.regs 2 = stride)
    (h3 : st.regs 3 = L) (h5 : st.regs 5 = i) (h7 : st.regs 7 = K)
    (ha : src+i*stride < 2^w) (hb : dst+i*K < 2^w) :
    evalArgs w st packWideWeightArgs = some [src+i*stride,L,K,dst+i*K] := by
  unfold packWideWeightArgs
  eval_expr

/-- Each widened block retains the exact signed numerator of the
corresponding representative, and the region after the table is fresh. -/
private theorem packWideTableLoop_triple {w h extend : ℕ} {p : Program}
    (he : MeetsContract w p extend (Num.signExtendContract w h))
    (mem : ℕ → ℕ) (pos src dst names L K count : ℕ) (source : ℕ → ℕ) (callArgs : List Expr)
    (hw : 1 < 2^w) (hwidth : L ≤ K) (hK : K < 2^w)
    (hm : count < 2^w) (hroom : dst+count*K < 2^w)
    (hsrc : ∀ i < count, source i+L ≤ dst ∧ Num.Valid mem (source i) h L)
    (hargsSize : argsSize callArgs ≤ 38)
    (heval : ∀ st i, i < count → st.regs 0 = src → st.regs 1 = dst → st.regs 2 = names →
      st.regs 3 = L → st.regs 5 = i → st.regs 7 = K →
      (∀ a < dst, st.mem a = mem a) → dst+i*K < 2^w →
      evalArgs w st callArgs = some [source i,L,K,dst+i*K])
    (hz : ZeroFrom mem dst) :
    Triple w p (fun st => st = startState [src,dst,names,L,count,0,0,K] mem pos)
      (forRange 5 (.const 0) (.reg 4) (.call 6 extend callArgs))
      (normalPost fun st =>
        (∀ i < count, Num.Valid st.mem (dst+i*K) h K ∧
          Num.intVal st.mem (dst+i*K) h K = Num.intVal mem (source i) h L) ∧
        (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dst+count*K))
      (fun _ => (30*K+90)*count+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = names ∧ st.regs 3 = L ∧
      st.regs 4 = count ∧ st.regs 5 = i ∧ st.regs 7 = K ∧
      (∀ j < i, Num.Valid st.mem (dst+j*K) h K ∧
        Num.intVal st.mem (dst+j*K) h K = Num.intVal mem (source j) h L) ∧
      (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dst+i*K)
  have loop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 4)
    (body := .call 6 extend callArgs) (Inv := Inv)
    (P := fun st => st = startState [src,dst,names,L,count,0,0,K] mem pos)
    (30*K+81) 0 count (Nat.zero_le _) hw (fun _ => hm)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr,?_⟩
      simp [Inv,startState,hz])
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have hr := hi.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h7,hpacked,hframe,hzero⟩
      let a := source i
      let b := dst+i*K
      obtain ⟨ha,hvalid⟩ := hsrc i hi
      have hmul : (i+1)*K ≤ count*K := Nat.mul_le_mul_right K hi
      rw [Nat.add_mul,Nat.one_mul] at hmul
      have hb : b+K < 2^w := by dsimp [b]; omega
      have hargs := heval st i hi h0 h1 h2 h3 h5 h7 hframe (by omega)
      have hv (k : ℕ) (hk : k < L) : st.mem (a+k) = mem (a+k) := hframe _ (by omega)
      have hwords : ∀ x ∈ [a,L,K,b], x < 2^w := by
        have ha' : a < 2^w := by omega
        have hb' : b < 2^w := by omega
        simp [ha',hb',hwidth.trans_lt hK,hK]
      obtain ⟨out,c,ret,hr,hpost,hreg,hkeep,hcost⟩ := runs_call_of_meetsContract (r := 6)
        he hargs hwords ⟨⟨a,L,K,b,rfl,hwidth,by dsimp [b]; omega,
          fun k hk => (hv k hk).trans_lt (hvalid k hk)⟩,hzero,hb⟩ ω
      obtain ⟨hret,_,_,hbelow,hfresh,hnew,hval⟩ := hpost
      change ret = b+K at hret
      change (∀ x < b, out.mem x = st.mem x) at hbelow
      change ZeroFrom out.mem ret at hfresh
      change Num.Valid out.mem b h K at hnew
      change Num.intVal out.mem b h K = Num.intVal st.mem a h L at hval
      refine ⟨.normal,out,c,hr,⟨⟨(hkeep _ (by decide)).trans h0,(hkeep _ (by decide)).trans h1,
        (hkeep _ (by decide)).trans h2,(hkeep _ (by decide)).trans h3,(hkeep _ (by decide)).trans h4,
        by simp,by simpa using (hkeep 7 (by decide)).trans h7,?_,?_,?_⟩,
        (hkeep _ (by decide)).trans h5⟩,?_⟩
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
        · have hsep := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hj')
          rw [Nat.succ_mul] at hsep
          have hcell (k : ℕ) (hk : k < K) : out.mem (dst+j*K+k) = st.mem (dst+j*K+k) :=
            hbelow _ (by dsimp [b]; omega)
          obtain ⟨hvalid,hvalue⟩ := hpacked j hj'
          exact ⟨fun k hk => (hcell k hk).trans_lt (hvalid k hk),
            (Num.intVal_congr hcell).trans hvalue⟩
        · exact ⟨hnew,hval.trans (Num.intVal_congr hv)⟩
      · intro x hx
        exact (hbelow x (hx.trans_le (Nat.le_add_right _ _))).trans (hframe x hx)
      · simpa [hret,b,Nat.add_mul,Nat.add_assoc] using hfresh
      · change c ≤ 30*K+81
        change c ≤ argsSize callArgs+(30*K+42)+1 at hcost
        omega)
  refine loop.conseq (fun _ hs => hs) ?_ ?_
  · intro o _ hs
    cases o with
    | normal => exact hs.2.2.2.2.2.2.2
    | returned _ => exact hs
  · intro _ _
    simp [Expr.size, Nat.mul_comm]

/-- Each widened block retains the exact signed numerator of the
corresponding representative, and the region after the table is fresh. -/
theorem packWideValuesLoop_triple {w h extend : ℕ} {p : Program}
    (he : MeetsContract w p extend (Num.signExtendContract w h))
    (mem : ℕ → ℕ) (pos src dst names L K : ℕ) (H : MGraph)
    (hw : 1 < 2^w) (hwidth : L ≤ K) (hK : K < 2^w)
    (hm : H.m < 2^w) (hroom : dst+H.m*K < 2^w)
    (hsrc : ∀ e ∈ H.E, src+e*L+L ≤ dst ∧ Num.Valid mem (src+e*L) h L)
    (hnames : names+H.m ≤ dst) (hat : ∀ i < H.m, mem (names+i) = edgeName H i)
    (hz : ZeroFrom mem dst) :
    Triple w p (fun st => st = startState [src,dst,names,L,H.m,0,0,K] mem pos)
      (forRange 5 (.const 0) (.reg 4) (.call 6 extend packWideValueArgs))
      (normalPost fun st =>
        (∀ i < H.m, Num.Valid st.mem (dst+i*K) h K ∧
          Num.intVal st.mem (dst+i*K) h K = Num.intVal mem (src+edgeName H i*L) h L) ∧
        (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dst+H.m*K))
      (fun _ => (30*K+90)*H.m+7) := by
  apply packWideTableLoop_triple he mem pos src dst names L K H.m
    (fun i => src+edgeName H i*L) packWideValueArgs hw hwidth hK hm hroom
    (fun i hi => hsrc _ (edgeName_mem hi)) (by decide) _ hz
  intro st i hi h0 h1 h2 h3 h5 h7 hframe hb
  have ha := (hsrc _ (edgeName_mem hi)).1
  have hname := (hframe (names+i) (by omega)).trans (hat i hi)
  exact packWideValueArgs_eval st src dst names L K i _ h0 h1 h2 h3 h5 h7 hname
    (by omega) (by omega) hb

/-- The widened numeric table preserves the signed caller numerators. -/
def packWideValuesContract (w h : ℕ) (H : MGraph) : Contract where
  pre args mem := ∃ src dst names L K,
    args = [src,dst,names,L,H.m,0,0,K] ∧ 1 < 2^w ∧ L ≤ K ∧ K < 2^w ∧
    H.m < 2^w ∧ dst+H.m*K < 2^w ∧
    (∀ e ∈ H.E, src+e*L+L ≤ dst ∧ Num.Valid mem (src+e*L) h L) ∧
    names+H.m ≤ dst ∧ (∀ i < H.m, mem (names+i) = edgeName H i) ∧ ZeroFrom mem dst
  post args mem ret out := ∃ src dst names L K,
    args = [src,dst,names,L,H.m,0,0,K] ∧ ret = 0 ∧
    (∀ i < H.m, Num.Valid out (dst+i*K) h K ∧
      Num.intVal out (dst+i*K) h K = Num.intVal mem (src+edgeName H i*L) h L) ∧
    (∀ a < dst, out a = mem a) ∧ ZeroFrom out (dst+H.m*K)
  cost args _ := (30*args.getD 7 0+90)*H.m+10

/-- Install the widening packer over the signed-extension procedure. -/
theorem packWideValues_meetsContract {w h entry extend : ℕ} {p : Program} (H : MGraph)
    (hp : p.procs[entry]? = some (packWideValuesBody extend))
    (he : MeetsContract w p extend (Num.signExtendContract w h)) :
    MeetsContract w p entry (packWideValuesContract w h H) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,names,L,K,rfl,hw,hwidth,hK,hm,hroom,hsrc,hnames,hat,hz⟩ := hpre
  apply runs_start_le
  unfold packWideValuesBody
  refine runs_seq_triple_le
    (packWideValuesLoop_triple he mem pos src dst names L K H hw hwidth hK hm hroom
      hsrc hnames hat hz) rfl ?_
  intro out ⟨hvals,hframe,hfresh⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨src,dst,names,L,K,rfl,rfl,hvals,hframe,hfresh⟩ ?_
  change 0+((30*K+90)*H.m+7)+1+2 ≤ (30*K+90)*H.m+10
  omega

/-- The widened weight table preserves every compact weight numerator. -/
def packWideWeightsContract (w h : ℕ) : Contract where
  pre args mem := ∃ src dst stride L m K,
    args = [src,dst,stride,L,m,0,0,K] ∧ 1 < 2^w ∧ L ≤ K ∧ K < 2^w ∧
    m < 2^w ∧ dst+m*K < 2^w ∧
    (∀ i < m, src+i*stride+L ≤ dst ∧ Num.Valid mem (src+i*stride) h L) ∧ ZeroFrom mem dst
  post args mem ret out := ∃ src dst stride L m K,
    args = [src,dst,stride,L,m,0,0,K] ∧ ret = 0 ∧
    (∀ i < m, Num.Valid out (dst+i*K) h K ∧
      Num.intVal out (dst+i*K) h K = Num.intVal mem (src+i*stride) h L) ∧
    (∀ a < dst, out a = mem a) ∧ ZeroFrom out (dst+m*K)
  cost args _ := (30*args.getD 7 0+90)*args.getD 4 0+10

/-- Install the strided weight packer using the same loop proof as the length packer. -/
theorem packWideWeights_meetsContract {w h entry extend : ℕ} {p : Program}
    (hp : p.procs[entry]? = some (packWideWeightsBody extend))
    (he : MeetsContract w p extend (Num.signExtendContract w h)) :
    MeetsContract w p entry (packWideWeightsContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,stride,L,m,K,rfl,hw,hwidth,hK,hm,hroom,hsrc,hz⟩ := hpre
  have heval (st : State) (i : ℕ) (hi : i < m) (h0 : st.regs 0 = src) (h1 : st.regs 1 = dst)
      (h2 : st.regs 2 = stride) (h3 : st.regs 3 = L) (h5 : st.regs 5 = i) (h7 : st.regs 7 = K)
      (_ : ∀ a < dst, st.mem a = mem a) (hb : dst+i*K < 2^w) :
      evalArgs w st packWideWeightArgs = some [src+i*stride,L,K,dst+i*K] := by
    have ha := (hsrc i hi).1
    exact packWideWeightArgs_eval st src dst stride L K i h0 h1 h2 h3 h5 h7 (by omega) hb
  apply runs_start_le
  unfold packWideWeightsBody
  refine runs_seq_triple_le
    (packWideTableLoop_triple he mem pos src dst stride L K m (fun i => src+i*stride)
      packWideWeightArgs hw hwidth hK hm hroom hsrc (by decide) heval hz) rfl ?_
  intro out ⟨hvals,hframe,hfresh⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨src,dst,stride,L,m,K,rfl,rfl,hvals,hframe,hfresh⟩ ?_
  change 0+((30*K+90)*m+7)+1+2 ≤ (30*K+90)*m+10
  omega

/-- Pack one numeric table in linear time in the number of words.
The source is indexed by edge names and both source tables lie below
the destination. -/
theorem packValuesLoop_triple {w copy : ℕ} {p : Program} (hp : p.HasAt copy [copyWords])
    (mem : ℕ → ℕ) (pos src dst names L cap : ℕ) (H : MGraph)
    (hword : 1 < 2 ^ w) (hL : L < 2 ^ w) (hm : H.m < 2 ^ w)
    (hsrc : src ≤ dst ∧ ∀ e ∈ H.E, src+e*L+L ≤ dst) (hnames : names + H.m ≤ dst)
    (hroom : dst + H.m * L < 2 ^ w)
    (hnamesAt : ∀ i < H.m, mem (names + i) = edgeName H i)
    (hcap : ∀ e ∈ H.E, e < cap) :
    Triple w p (fun st => st = startState [src,dst,names,L,H.m] mem pos)
      (packValuesLoop copy)
      (normalPost fun st =>
        (∀ i < H.m, ∀ k < L, st.mem (dst + i * L + k) =
          mem (src + edgeName H i * L + k)) ∧
        (∀ a, a < dst ∨ dst + H.m * L ≤ a → st.mem a = mem a))
      (fun _ => (17 * L + 41) * H.m + 7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = names ∧ st.regs 3 = L ∧
    st.regs 4 = H.m ∧ st.regs 5 = i ∧
    (∀ j < i, ∀ k < L, st.mem (dst + j * L + k) = mem (src + edgeName H j * L + k)) ∧
    (∀ a, a < dst ∨ dst + i * L ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 4)
    (body := .call 6 copy packValueArgs) (Inv := Inv)
    (P := fun st => st = startState [src,dst,names,L,H.m] mem pos)
    (17 * L + 32) 0 H.m (Nat.zero_le _) hword (fun _ => hm)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      dsimp [Inv]
      simp [startState])
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 4 = H.m := h.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,hdone,hframe⟩
      let e := edgeName H i
      let a := src + e * L
      let b := dst + i * L
      have he : e < cap := hcap e (edgeName_mem hi)
      have hmul₂ : i * L + L ≤ H.m * L := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right L hi
      have ha : a + L ≤ dst := hsrc.2 e (edgeName_mem hi)
      have hb : b + L < 2 ^ w := by dsimp [b]; omega
      have haWord : a < 2 ^ w := by omega
      have hbWord : b < 2 ^ w := by omega
      have hname : st.mem (names + i) = e :=
        (hframe _ (Or.inl (by omega))).trans (hnamesAt i hi)
      have hnameWord : names + i < 2 ^ w := by omega
      have hprod₁ : e * L < 2 ^ w := by dsimp [a] at haWord; omega
      have hprod₂ : i * L < 2 ^ w := by dsimp [b] at hbWord; omega
      have hargs : evalArgs w st packValueArgs = some [a,b,L] := by
        simp [packValueArgs, evalArgs, Expr.eval, h0,h1,h2,h3,h5,hname,
          hnameWord,hprod₁,hprod₂, show src + e * L < 2 ^ w from haWord,
          show dst + i * L < 2 ^ w from hbWord, a, b]
      have hwords : ∀ x ∈ [a,b,L], x < 2 ^ w := by
        simp [haWord,hbWord,hL]
      obtain ⟨body,hbody,o,after,c,hrun,hpost,hcost⟩ :=
        copyWords_meetsContract hp [a,b,L] st.mem st.pos ω hwords
          ⟨a,b,L,rfl,hword,by omega,hb.le,Or.inr (by dsimp [b]; omega)⟩
      obtain ⟨a',b',L',hab,hzero,hcopied,hother⟩ := hpost
      simp only [List.cons.injEq, and_true] at hab
      obtain ⟨rfl,rfl,rfl⟩ := hab
      let out := { after with regs := Function.update st.regs 6 o.value }
      refine ⟨.normal,out,_,runs_call_iff.mpr
        ⟨_,body,o,after,c,hargs,hbody,hrun,rfl,rfl,rfl⟩,?_,?_⟩
      · refine ⟨⟨h0,h1,h2,h3,h4,by simp [out],?_,?_⟩,h5⟩
        · intro j hj k hk
          change after.mem _ = _
          by_cases heq : j = i
          · subst j
            exact (hcopied k hk).trans (hframe _ (Or.inl (by omega)))
          · have hj' : j < i := by omega
            have hlt : dst + j * L + k < b := by
              have hx : (j + 1) * L ≤ i * L := Nat.mul_le_mul_right L hj'
              rw [Nat.add_mul, one_mul] at hx
              dsimp [b]
              omega
            exact (hother _ (Or.inl hlt)).trans (hdone j hj' k hk)
        · intro x hx
          change after.mem x = _
          have hs' : dst + (i + 1) * L = b + L := by simp [b,Nat.add_mul,Nat.add_assoc]
          rw [hs'] at hx
          have hbefore : dst ≤ b := Nat.le_add_right _ _
          have hprev : x < dst ∨ dst + i * L ≤ x := hx.elim Or.inl (fun h => Or.inr (by omega))
          exact (hother x (hx.imp_left (fun h => lt_of_lt_of_le h hbefore))).trans (hframe x hprev)
      · change c ≤ 17 * L + 10 at hcost
        simp [packValueArgs, Expr.size]
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o _ h
    cases o with
    | normal => exact h.2.2.2.2.2.2
    | returned _ => exact h
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- A packed block supplies the fixed-point value of the original edge. -/
theorem packedValue_eq {mem out : ℕ → ℕ} {src dst h L P : ℕ} {H : MGraph}
    {i : ℕ} (hcopy : ∀ k < L,
      out (dst + i * L + k) = mem (src + edgeName H i * L + k))
    (hvalid : Num.Valid mem (src + edgeName H i * L) h L) :
    Num.Valid out (dst + i * L) h L ∧
      Num.fixVal out (dst + i * L) h L P = Num.fixVal mem (src + edgeName H i * L) h L P := by
  refine ⟨fun k hk => (hcopy k hk).trans_lt (hvalid k hk), ?_⟩
  rw [Num.fixVal, Num.fixVal, Num.intVal_congr hcopy]

/-- Pack a host-format block array into the caller’s destination. -/
def packValuesBody (copy : ℕ) : Stmt :=
  .seq (packValuesLoop copy)
    (.ret (.const 0))

/-- The host numeric pass uses a compact copy of the edge-name-indexed
length blocks. Copying preserves their caller format and precision. -/
def packValuesContract (w cap : ℕ) (H : MGraph) : Contract where
  pre args mem := ∃ src dst names L,
    args = [src,dst,names,L,H.m] ∧ 1 < 2^w ∧ L < 2^w ∧ H.m < 2^w ∧
      (src ≤ dst ∧ ∀ e ∈ H.E, src+e*L+L ≤ dst) ∧ names+H.m ≤ dst ∧ dst+H.m*L < 2^w ∧
      (∀ i < H.m, mem (names+i) = edgeName H i) ∧ ∀ e ∈ H.E, e < cap
  post args mem ret out := ∃ src dst names L,
    args = [src,dst,names,L,H.m] ∧ ret = 0 ∧
      (∀ i < H.m, ∀ k < L, out (dst+i*L+k) = mem (src+edgeName H i*L+k)) ∧
      ∀ a, a < dst ∨ dst+H.m*L ≤ a → out a = mem a
  cost args _ := (17*args.getD 3 0+41)*H.m+10

/-- Install the host-format packer over the verified word-copy procedure. -/
theorem packValues_meetsContract {w entry copy cap : ℕ} {p : Program} (H : MGraph)
    (he : p.procs[entry]? = some (packValuesBody copy))
    (hp : p.HasAt copy [copyWords]) :
    MeetsContract w p entry (packValuesContract w cap H) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,names,L,rfl,hw,hL,hm,hsrc,hnames,hroom,hat,hcap⟩ := hpre
  apply runs_start_le
  unfold packValuesBody
  refine runs_seq_triple_le
    (packValuesLoop_triple hp mem pos src dst names L cap H hw hL hm hsrc hnames hroom hat hcap)
    rfl ?_
  intro out ⟨hcopy,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨src,dst,names,L,rfl,rfl,hcopy,hframe⟩ ?_
  change 0+((17*L+41)*H.m+7)+1+2 ≤ (17*L+41)*H.m+10
  omega

/-- The compact length table preserves each source numerator. A fresh
allocation remains zero after the final packed block. -/
theorem packedLengths_of_packValues {w cap h : ℕ} {H : MGraph}
    (src dst names L ret : ℕ) (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (hpost : (packValuesContract w cap H).post [src,dst,names,L,H.m] mem ret out)
    (hsrc : ∀ e ∈ H.E, Num.Valid mem (src+e*L) h L ∧
      Num.intVal mem (src+e*L) h L = len e)
    (hz : ZeroFrom mem dst) :
    (∀ i < H.m, Num.Valid out (dst+i*L) h L ∧
      Num.intVal out (dst+i*L) h L = len (edgeName H i)) ∧
      (∀ a < dst, out a = mem a) ∧ ZeroFrom out (dst+H.m*L) := by
  obtain ⟨s,d,n,l,he,_,hcopy,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  refine ⟨?_,fun a ha => hframe a (.inl ha),?_⟩
  · intro i hi
    have he := edgeName_mem (G := H) hi
    obtain ⟨hv,hlen⟩ := hsrc _ he
    exact ⟨fun k hk => (hcopy i hi k hk).trans_lt (hv k hk),
      (Num.intVal_congr (hcopy i hi)).trans hlen⟩
  · intro a ha
    exact (hframe a (.inr ha)).trans (hz a ((Nat.le_add_right _ _).trans ha))

end MinCostFlow.LastLevelProgram
