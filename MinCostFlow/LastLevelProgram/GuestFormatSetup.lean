module

public import MinCostFlow.LastLevelProgram.BlockWidth
public import MinCostFlow.LastLevelProgram.LimbValuation
public import MinCostFlow.LastLevelProgram.ScaleWord
public import MinCostFlow.LastLevelProgram.PackGuestLengths
public import MinCostFlow.LastLevelProgram.QueryMemory
public import MinCostFlow.LastLevelProgram.RepresentativeGraph
import WordRAM.Tactic
import Mathlib.Data.Nat.Size

/-!
# Setting the guest format at runtime

For Definition 5.8 (pages 19–20), compute the common exact precision,
then the width of the weight bound, then the largest guest width over
the live lengths. Store the precision and return the signed width.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Input registers hold names, lengths, caller width and precision,
edge count, weight grid, and the output precision cell. -/
def guestFormatSetupBody (precision weight width : ℕ) : Stmt :=
  .seq (.call 7 precision ((List.range 6).map Expr.reg))
  (.seq (.call 8 weight [.reg 4,.reg 7])
  (.seq (.call 9 width [.reg 0,.reg 1,.reg 2,.reg 3,.reg 7,.reg 8,.reg 4])
  (.seq (.store (.reg 6) (.reg 7)) (.ret (.reg 9)))))

/-- Format setup links the three read-only procedures and writes just
the destination precision cell. -/
theorem guestFormatSetup_runs {w precision weight width : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos names lengths L P m grid dst : ℕ) (name : ℕ → ℕ) (E : Finset ℕ)
    (hp : MeetsContract w p precision (queryPrecisionContract w names lengths L P m grid name E))
    (hb : MeetsContract w p weight (weightBoundWidthContract w)) :
    let len := fun e => if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := graphQueryPrecision grid len
    let B := (2*m*2^Q).size
    let W := max B ((Finset.range m).sup fun i =>
      (queryNumerator Q (Num.fixVal mem (lengths+name i*L) 4 L P)).natAbs.size)+1
    MeetsContract w p width (guestWidthContract w names lengths L P Q B m name) →
    (∀ a ∈ [names,lengths,L,P,m,grid,dst], a < 2^w) →
    (queryPrecisionContract w names lengths L P m grid name E).pre
      [names,lengths,L,P,m,grid] mem →
    (weightBoundWidthContract w).pre [m,Q] mem →
    (guestWidthContract w names lengths L P Q B m name).pre
      [names,lengths,L,P,Q,B,m] mem →
    Q < 2^w → B < 2^w →
    ∃ o out cost, Runs w p ω (guestFormatSetupBody precision weight width)
      (startState [names,lengths,L,P,m,grid,dst] mem pos) o out cost ∧
      (o.value = W ∧ out.mem = Function.update mem dst Q) ∧
      cost ≤ (98*L+92)*m+40*(2*m).size+110 := by
  intro len Q B W hf hwords hpre hweight hwidth hQ hB
  have hdst := hwords dst (by simp)
  apply runs_start_le
  unfold guestFormatSetupBody
  refine runs_seq_call_le hp (vs := [names,lengths,L,P,m,grid]) rfl
    (fun a ha => hwords a (List.mem_append_left [dst] ha)) hpre ?_
  intro q mid pos₁ hpost
  obtain ⟨hmem,hq⟩ := hpost
  change mid = mem at hmem
  change q = Q at hq
  subst q; subst mid
  refine runs_seq_call_le hb (vs := [m,Q]) rfl ?_ hweight ?_
  · intro a ha
    rcases (show a = m ∨ a = Q by simpa using ha) with rfl | rfl
    · exact hwords _ (by simp)
    · exact hQ
  · intro bits mid pos₂ hpost₂
    obtain ⟨n,R,he,hbits,hmem⟩ := hpost₂
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl⟩ := he
    change bits = B at hbits
    change mid = mem at hmem
    subst bits; subst mid
    refine runs_seq_call_le hf (vs := [names,lengths,L,P,Q,B,m]) rfl ?_ hwidth ?_
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hQ | exact hB | exact hwords _ (by simp)
    · intro ret out pos₃ hpost₃
      obtain ⟨hmem,hret⟩ := hpost₃
      change out = mem at hmem
      change ret = W at hret
      refine runs_seq_store_le (x := dst) (v := Q) (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := ret) (by eval_expr) ⟨hret,?_⟩ ?_
      · rw [hmem]
      · have hlen : argsSize ((List.range 6).map Expr.reg) = 6 := by decide
        simp only [hlen, weightBoundWidthContract, queryPrecisionContract, guestWidthContract,
          argsSize, Expr.size, List.getD_cons_zero, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
        omega

/-- With compact names covering the live edges, the format setup stores
and returns the exact pair selected by the graph-derived model. -/
theorem guestFormatSetup_model_runs {w precision weight width : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos names lengths L P dst : ℕ) (G : MGraph) (C : ℝ)
    (name : ℕ → ℕ) (hn : ∀ e, e ∈ G.E ↔ ∃ i < G.m, name i = e)
    (grid : ℕ) (hgrid : grid = weightPrecision C G)
    (hp : MeetsContract w p precision (queryPrecisionContract w names lengths L P G.m grid name G.E))
    (hb : MeetsContract w p weight (weightBoundWidthContract w)) :
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let B := (2*G.m*2^Q).size
    let args := [names,lengths,L,P,G.m,grid,dst]
    MeetsContract w p width (guestWidthContract w names lengths L P Q B G.m name) →
    (∀ a ∈ args, a < 2^w) →
    (queryPrecisionContract w names lengths L P G.m grid name G.E).pre
      [names,lengths,L,P,G.m,grid] mem →
    (weightBoundWidthContract w).pre [G.m,Q] mem →
    (guestWidthContract w names lengths L P Q B G.m name).pre
      [names,lengths,L,P,Q,B,G.m] mem →
    Q < 2^w → B < 2^w →
    ∃ o out cost, Runs w p ω (guestFormatSetupBody precision weight width)
      (startState args mem pos) o out cost ∧
      (o.value = roundQueryLimbs C G len ∧ out.mem = Function.update mem dst Q) ∧
      cost ≤ (98*L+92)*G.m+40*(2*G.m).size+110 := by
  subst grid
  intro len Q B args hf hwords hpre hweight hwidth hQ hB
  obtain ⟨o,out,cost,hrun,⟨hret,hmem⟩,hcost⟩ := guestFormatSetup_runs (ω := ω)
    mem pos names lengths L P G.m (weightPrecision C G) dst name G.E hp hb hf hwords
      hpre hweight hwidth hQ hB
  have hlen (i : ℕ) (hi : i ∈ Finset.range G.m) :
      len (name i) = Num.fixVal mem (lengths+name i*L) 4 L P := by
    change (if name i ∈ G.E then _ else _) = _
    rw [ite_eq_left ((hn _).2 ⟨i,Finset.mem_range.mp hi,rfl⟩)]
  have heq : roundQueryLimbs C G len = max B ((Finset.range G.m).sup fun i =>
    (queryNumerator Q (Num.fixVal mem (lengths+name i*L) 4 L P)).natAbs.size)+1 := by
    change graphQueryLimbs G Q (2*G.m*2^Q) len = _
    rw [graphQueryLimbs_of_widthScan len name hn]
    congr 2
    apply Finset.sup_congr rfl
    intro i hi
    rw [hlen i hi]
  exact ⟨o,out,cost,hrun,⟨hret.trans heq.symm,hmem⟩,hcost⟩

/-- The setup's scan and word bounds follow from one layout premise
and room for the caller precision, weight grid, and their derived sizes. -/
theorem guestFormatSetup_preconditions {w names lengths L P m grid : ℕ}
    (mem : ℕ → ℕ) (name : ℕ → ℕ) (E : Finset ℕ)
    (hw : 16 ≤ 2^w) (hP : P ≤ 4*L) (hm : 0 < m) (hmFit : 2*m+2 < 2^w)
    (hnames : names+m < 2^w) (hlen : lengths < 2^w)
    (hroom : 4*L + max P grid + (2*m).size + 2 < 2^w)
    (hname : ∀ e, e ∈ E ↔ ∃ i < m, name i = e)
    (hblocks : ∀ i < m, mem (names+i) = name i ∧ lengths+name i*L+L < 2^w ∧
      Num.Valid mem (lengths+name i*L) 4 L ∧ 0 < Num.intVal mem (lengths+name i*L) 4 L) :
    let len := fun e => if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := graphQueryPrecision grid len
    let B := (2*m*2^Q).size
    (queryPrecisionContract w names lengths L P m grid name E).pre [names,lengths,L,P,m,grid] mem ∧
    (weightBoundWidthContract w).pre [m,Q] mem ∧
    (guestWidthContract w names lengths L P Q B m name).pre [names,lengths,L,P,Q,B,m] mem ∧
    Q < 2^w ∧ B < 2^w := by
  intro len Q B
  have hgrid : OnQueryGrid P len := by
    intro e
    by_cases he : e ∈ E
    · exact ⟨Num.intVal mem (lengths+e*L) 4 L, by simp [len,he,Num.fixVal]⟩
    · exact ⟨0,by simp [len,he]⟩
  have hQ : Q ≤ max P grid := by
    have hlenGrid := lengthQueryPrecision_le hgrid
    change max grid (lengthQueryPrecision len) ≤ _
    omega
  have hB : B = (2*m).size+Q := by
    change (2*m*2^Q).size = _
    rw [← Nat.shiftLeft_eq, Nat.size_shiftLeft (by omega : 2*m ≠ 0)]
  refine ⟨?_,⟨m,Q,rfl,hm,hmFit,by omega⟩,
    ⟨rfl,hw,by omega,by omega,by omega,hnames,hblocks⟩,by omega,by omega⟩
  refine ⟨rfl,⟨rfl,hw,by omega,hP,hnames,hlen,?_⟩,hname,?_⟩
  · intro i hi
    obtain ⟨hn,ha,hv,_⟩ := hblocks i hi
    exact ⟨hn,ha,hv⟩
  · intro e he
    obtain ⟨i,hi,rfl⟩ := (hname e).1 he
    obtain ⟨_,_,hv,hpos⟩ := hblocks i hi
    exact ⟨hv,hpos.le⟩

/-- The guest format setup takes caller format words and stores one
canonical precision word. The return value is the canonical limb count. -/
noncomputable def guestFormatSetupContract (w names lengths L P dst : ℕ) (G : MGraph)
    (C : ℝ) (name : ℕ → ℕ) : Contract where
  pre args mem := args = [names,lengths,L,P,G.m,weightPrecision C G,dst] ∧
    16 ≤ 2^w ∧ P ≤ 4*L ∧ 0 < G.m ∧ 2*G.m+2 < 2^w ∧
    names+G.m < 2^w ∧ lengths < 2^w ∧
    4*L + max P (weightPrecision C G) + (2*G.m).size+2 < 2^w ∧
    (∀ e, e ∈ G.E ↔ ∃ i < G.m, name i = e) ∧
    ∀ i < G.m, mem (names+i) = name i ∧ lengths+name i*L+L < 2^w ∧
      Num.Valid mem (lengths+name i*L) 4 L ∧ 0 < Num.intVal mem (lengths+name i*L) 4 L
  post _ mem ret out :=
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    ret = roundQueryLimbs C G len ∧
      out = Function.update mem dst (roundQueryPrecision C G len)
  cost _ _ := (98*L+92)*G.m+40*(2*G.m).size+110

/-- Install the format setup for all represented length vectors. The
width reader is linked once and accepts every computed pair of words. -/
theorem guestFormatSetup_meetsContract {w entry precision weight width names lengths L P dst : ℕ}
    {p : Program} (G : MGraph) (C : ℝ) (name : ℕ → ℕ)
    (he : p.procs[entry]? = some (guestFormatSetupBody precision weight width))
    (hp : MeetsContract w p precision
      (queryPrecisionContract w names lengths L P G.m (weightPrecision C G) name G.E))
    (hb : MeetsContract w p weight (weightBoundWidthContract w))
    (hf : ∀ Q initial, MeetsContract w p width
      (guestWidthContract w names lengths L P Q initial G.m name)) :
    MeetsContract w p entry (guestFormatSetupContract w names lengths L P dst G C name) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hw,hP,hm,hmFit,hnames,hlen,hroom,hname,hblocks⟩ := hpre
  obtain ⟨hprec,hweight,hwidth,hQ,hB⟩ :=
    guestFormatSetup_preconditions mem name G.E hw hP hm hmFit hnames hlen hroom hname hblocks
  exact guestFormatSetup_model_runs (ω := ω) mem pos names lengths L P dst G C name hname
    (weightPrecision C G) rfl hp hb (hf _ _) hwords hprec hweight hwidth hQ hB

/-- Select the format and pass its returned width and stored precision
to the compact length packer. The last input is the guest length base. -/
def setupAndPackGuestBody (setup pack : ℕ) : Stmt :=
  .seq (.call 8 setup ((List.range 7).map Expr.reg))
    (.seq (.call 9 pack [.reg 1,.reg 7,.reg 0,.reg 2,.reg 3,.load (.reg 6),.reg 8,.reg 4])
      (.ret (.reg 8)))

/-- Format setup and packing preserve the original lengths and write
only the precision cell and the compact guest length array. -/
theorem setupAndPackGuest_runs {w setup pack cap : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos names lengths L P dst guest : ℕ)
    (G : MGraph) (C : ℝ) (name : ℕ → ℕ)
    (hs : MeetsContract w p setup (guestFormatSetupContract w names lengths L P dst G C name))
    (hp : MeetsContract w p pack (packGuestLengthsContract w cap G)) :
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let N := roundQueryLimbs C G len
    let sa := [names,lengths,L,P,G.m,weightPrecision C G,dst]
    let pa := [lengths,guest,names,L,P,Q,N,G.m]
    (∀ x ∈ sa ++ [guest], x < 2^w) →
    (guestFormatSetupContract w names lengths L P dst G C name).pre sa mem →
    (packGuestLengthsContract w cap G).pre pa (Function.update mem dst Q) →
    Q < 2^w → N < 2^w → dst < guest →
    (∀ e ∈ G.E, dst < lengths+e*L ∨ lengths+e*L+L ≤ dst) →
    ∃ o out cost, Runs w p ω (setupAndPackGuestBody setup pack)
      (startState (sa ++ [guest]) mem pos) o out cost ∧
      (o.value = N ∧ out.mem dst = Q ∧
        (∀ i < G.m, ListAt out.mem (guest+i*N)
          (Num.encodeLimbs 1 N (queryNumerator Q (len (edgeName G i))))) ∧
        ∀ b, b ≠ dst → (b < guest ∨ guest+G.m*N ≤ b) → out.mem b = mem b) ∧
      cost ≤ ((98*L+92)+(80*N+37))*G.m+40*(2*G.m).size+145 := by
  intro len Q N sa pa hwords hstart hpack hQ hN hdst hsrc
  apply runs_start_le
  unfold setupAndPackGuestBody
  refine runs_seq_call_le hs (vs := sa) rfl
    (fun a ha => hwords a (List.mem_append_left [guest] ha)) hstart ?_
  intro ret mid pos₁ hpost
  obtain ⟨hn,hm⟩ := hpost
  change ret = N at hn
  change mid = Function.update mem dst Q at hm
  subst ret
  have hmid : mid dst = Q := by rw [hm,Function.update_self]
  have hmAt : Expr.MemAt (State.mk mid
      (Function.update (startState (sa ++ [guest]) mem pos).regs 8 N) pos₁) dst Q := hmid
  have hdstFit : dst < 2^w := hwords _ (by simp [sa])
  refine runs_seq_call_le hp (vs := pa) (by eval_expr) ?_ (hm.symm ▸ hpack) ?_
  · intro a ha
    simp only [pa,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hQ | exact hN | exact hwords _ (by simp [sa])
  · intro result out pos₂ ho
    obtain ⟨s,g,n,l,f,q,b,he,_,henc,hframe⟩ := ho
    simp only [pa,List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    refine runs_ret_le (v := N) (by eval_expr)
      ⟨rfl,(hframe _ (Or.inl hdst)).trans hmid,?_,?_⟩ ?_
    · intro i hi
      have he := edgeName_mem hi
      have hv : Num.intVal mid (lengths+edgeName G i*L) 4 L =
          Num.intVal mem (lengths+edgeName G i*L) 4 L := by
        apply Num.intVal_congr
        intro j hj
        rw [hm,Function.update_of_ne (by have h := hsrc _ he; omega)]
      have hl : len (edgeName G i) = Num.fixVal mem (lengths+edgeName G i*L) 4 L P := by
        exact ite_eq_left he
      simpa only [hl,Num.fixVal,hv] using henc i hi
    · intro b hne hb
      exact (hframe b hb).trans (hm.symm ▸ Function.update_of_ne hne ..)
    · have hlen : argsSize ((List.range 7).map Expr.reg) = 7 := by decide
      simp only [hlen, guestFormatSetupContract,packGuestLengthsContract,argsSize,Expr.size,
        pa,List.getD_cons_succ,List.getD_cons_zero,Nat.zero_add,Nat.add_mul,Nat.mul_assoc]
      omega

/-- The canonical width fits the loaded lengths. A precision cell
outside the live input tables preserves the packing premises. -/
theorem packGuestLengths_pre_of_format {w cap names lengths L P dst guest : ℕ}
    {G : MGraph} {C : ℝ} {mem : ℕ → ℕ}
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hm : G.m < 2^w)
    (hs : lengths+cap*L ≤ guest) (hn : names+G.m ≤ guest)
    (haddr : dst < names ∨ names+G.m ≤ dst)
    (hsrc : ∀ e ∈ G.E, dst < lengths+e*L ∨ lengths+e*L+L ≤ dst)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hname : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hblocks : ∀ e ∈ G.E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 ≤ Num.intVal mem (lengths+e*L) 4 L) :
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let N := roundQueryLimbs C G len
    P+N < 2^w → Q < 2^w → guest+G.m*N < 2^w →
    (packGuestLengthsContract w cap G).pre
      [lengths,guest,names,L,P,Q,N,G.m] (Function.update mem dst Q) := by
  intro len Q N hPN hQ hroom
  refine ⟨lengths,guest,names,L,P,Q,N,rfl,hw,hL,hPN,hQ,hm,hs,hn,hroom,?_,hcap,?_⟩
  · intro i hi
    exact (Function.update_of_ne (by omega) ..).trans (hname i hi)
  · intro e he
    obtain ⟨hv,hpos⟩ := hblocks e he
    have hread (i : ℕ) (hi : i < L) : Function.update mem dst Q (lengths+e*L+i) =
        mem (lengths+e*L+i) :=
      Function.update_of_ne (by have h := hsrc e he; omega) ..
    have hval := Num.intVal_congr (h := 4) hread
    have hlen : len e = Num.fixVal mem (lengths+e*L) 4 L P := ite_eq_left he
    have hnonneg : 0 ≤ queryNumerator Q (len e) := by
      rw [hlen,← rescaleUnsigned_eq_queryNumerator hv hpos]
      exact Int.natCast_nonneg _
    have hfit : Num.Fits 1 N (queryNumerator Q (len e)) :=
      graphQueryLimbs_length he hnonneg
    exact ⟨fun i hi => (hread i hi).trans_lt (hv i hi),hval.symm ▸ hpos,
      by simpa only [hlen,Num.fixVal,hval] using hfit⟩

/-- The query initializer computes both format words and writes the
converted compact lengths into a reserved guest interval. -/
noncomputable def setupAndPackGuestContract (w cap names lengths L P dst guest : ℕ)
    (G : MGraph) (C : ℝ) (name : ℕ → ℕ) : Contract where
  pre args mem :=
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let N := roundQueryLimbs C G len
    args = [names,lengths,L,P,G.m,weightPrecision C G,dst,guest] ∧
    (guestFormatSetupContract w names lengths L P dst G C name).pre
      [names,lengths,L,P,G.m,weightPrecision C G,dst] mem ∧
    Q < 2^w ∧ N < 2^w ∧ P+N < 2^w ∧ dst < guest ∧
    lengths+cap*L ≤ guest ∧ names+G.m ≤ guest ∧ guest+G.m*N < 2^w ∧
    (dst < names ∨ names+G.m ≤ dst) ∧
    (∀ i < G.m, name i = edgeName G i) ∧
    (∀ e ∈ G.E, e < cap) ∧
    ∀ e ∈ G.E, dst < lengths+e*L ∨ lengths+e*L+L ≤ dst
  post _ mem ret out :=
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let N := roundQueryLimbs C G len
    ret = N ∧ out dst = Q ∧
    (∀ i < G.m, ListAt out (guest+i*N)
      (Num.encodeLimbs 1 N (queryNumerator Q (len (edgeName G i))))) ∧
    ∀ b, b ≠ dst → (b < guest ∨ guest+G.m*N ≤ b) → out b = mem b
  cost _ mem :=
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    ((98*L+92)+(80*roundQueryLimbs C G len+37))*G.m+40*(2*G.m).size+145

/-- The installed query initializer packs the lengths at the model's
chosen precision and width. -/
theorem setupAndPackGuest_meetsContract {w entry setup pack cap names lengths L P dst guest : ℕ}
    {p : Program} (G : MGraph) (C : ℝ) (name : ℕ → ℕ)
    (he : p.procs[entry]? = some (setupAndPackGuestBody setup pack))
    (hs : MeetsContract w p setup (guestFormatSetupContract w names lengths L P dst G C name))
    (hp : MeetsContract w p pack (packGuestLengthsContract w cap G)) :
    MeetsContract w p entry (setupAndPackGuestContract w cap names lengths L P dst guest G C name) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hstart,hQ,hN,hPN,hdst,hs',hn,hroom,haddr,hnames,hcap,hsrc⟩ := hpre
  have hstartCopy := hstart
  obtain ⟨_,hw,hP,hm,hmFit,_,_,hscalar,hname,hblocks⟩ := hstartCopy
  have hnamesAt (i : ℕ) (hi : i < G.m) : mem (names+i) = edgeName G i :=
    (hblocks i hi).1.trans (hnames i hi)
  have hvalid (e : ℕ) (he' : e ∈ G.E) : Num.Valid mem (lengths+e*L) 4 L ∧
      0 ≤ Num.intVal mem (lengths+e*L) 4 L := by
    obtain ⟨i,hi,rfl⟩ := (hname e).1 he'
    obtain ⟨_,_,hv,hpos⟩ := hblocks i hi
    exact ⟨hv,hpos.le⟩
  have hpack := packGuestLengths_pre_of_format (C := C) hw (by omega) (by omega)
    hs' hn haddr hsrc hcap hnamesAt hvalid hPN hQ hroom
  exact setupAndPackGuest_runs (ω := ω) mem pos names lengths L P dst guest G C name
    hs hp hwords hstart hpack hQ hN hdst hsrc

/-- The packed lengths and the other three compact arrays yield exactly
the canonical guest memory when viewed from the relocated input base. -/
theorem queryMemory_of_setupAndPackGuest {w cap names lengths L P dst base : ℕ}
    {G : MGraph} {C : ℝ} {name : ℕ → ℕ} {mem out : ℕ → ℕ} {ret : ℕ}
    (wt : ℕ → ℤ)
    (hp : (setupAndPackGuestContract w cap names lengths L P dst
      (base+queryLengths G) G C name).post [] mem ret out) :
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C G len
    let N := roundQueryLimbs C G len
    (∀ i < G.m, out (base+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, out (base+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt out (base+queryWeights G N+i*N)
      (Num.encodeLimbs 1 N (wt (edgeName G i)))) →
    ZeroFrom out (base+queryOriginals G N) →
    (fun a => out (base+a)) = queryMemory G N (queryNumerator Q ∘ len) wt := by
  intro len Q N ht hh hw hz
  have hN : 0 < N := Nat.succ_pos _
  obtain ⟨_,_,hpack,_⟩ := hp
  refine queryMemory_eq_of_arrays G hN (queryNumerator Q ∘ len) wt _ ht hh ?_ ?_ ?_
  · intro i hi j hj
    have h := hpack i hi j hj
    change out (base+(queryLengths G+i*N+j)) = _
    simpa only [Nat.add_assoc, N, Q, len, Function.comp_apply] using h
  · intro i hi j hj
    have h := hw i hi j hj
    change out (base+(queryWeights G N+i*N+j)) = _
    simpa only [Nat.add_assoc] using h
  · intro a ha
    exact hz (base+a) (Nat.add_le_add_left ha _)

/-- Bound the guest limb count by the caller width, the precision grid
and the bit count of the number of edges. -/
theorem roundQueryLimbs_le_of_callerBlocks (C : ℝ) (G : MGraph)
    (mem : ℕ → ℕ) (lengths L P : ℕ) (hP : P ≤ 4*L) (hm : 0 < G.m)
    (hblocks : ∀ e ∈ G.E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 < Num.intVal mem (lengths+e*L) 4 L) :
    let len := fun e => if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    roundQueryLimbs C G len ≤ max (2*G.m).size (4*L) + max (4*L) (weightPrecision C G)+1 := by
  intro len
  let Q := roundQueryPrecision C G len
  have hgrid : OnQueryGrid P len := by
    intro e
    by_cases he : e ∈ G.E
    · exact ⟨Num.intVal mem (lengths+e*L) 4 L,by simp [len,he,Num.fixVal]⟩
    · exact ⟨0,by simp [len,he]⟩
  have hQ : Q ≤ max (4*L) (weightPrecision C G) := by
    change max (weightPrecision C G) (lengthQueryPrecision len) ≤ _
    exact max_le (le_max_right ..) ((lengthQueryPrecision_le hgrid).trans (hP.trans (le_max_left ..)))
  have hb : (2*G.m*2^Q).size = (2*G.m).size+Q := by
    rw [← Nat.shiftLeft_eq,Nat.size_shiftLeft (by omega : 2*G.m ≠ 0)]
  have hl : (G.E.sup fun e => (queryNumerator Q (len e)).natAbs.size) ≤ 4*L+Q := by
    apply Finset.sup_le_iff.mpr
    intro e he
    obtain ⟨hv,hpos⟩ := hblocks e he
    change (queryNumerator Q (if e ∈ G.E then Num.fixVal mem (lengths+e*L) 4 L P else 0)).natAbs.size ≤ _
    rw [ite_eq_left he,queryNumerator_size_of_positiveBlock hv hpos]
    have hn : (Num.unsignedVal mem (lengths+e*L) 4 L).size ≤ 4*L :=
      Nat.size_le.mpr (by simpa only [Num.capacity,Num.base,pow_mul] using Num.unsignedVal_lt hv)
    omega
  change graphQueryLimbs G Q (2*G.m*2^Q) len ≤ _
  rw [graphQueryLimbs_eq_maxSize,hb]
  apply Nat.succ_le_succ
  exact max_le (Nat.add_le_add (le_max_left ..) hQ)
    (hl.trans (Nat.add_le_add (le_max_right ..) hQ))

/-- Upper bound on representative guest width, in terms of the caller
limb count, the original edge count and the fixed LSST constant. -/
def representativeGuestWidthBound (D L m : ℕ) : ℕ :=
  max (2*m).size (4*L) + max (4*L) ((1024*D).size+3*(m+1).size) + 1

/-- Positive caller blocks on the original graph bound the width used
by the representative graph query. -/
theorem representativeRoundQueryLimbs_le (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ)
    (mem : ℕ → ℕ) (lengths L P : ℕ) (hG : G.IsValid) (hP : P ≤ 4*L)
    (hm : 0 < (representativeGraph G ℓ).m)
    (hblocks : ∀ e ∈ G.E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 < Num.intVal mem (lengths+e*L) 4 L) :
    let H := representativeGraph G ℓ
    let len := fun e => if e ∈ H.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    roundQueryLimbs C H len ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m := by
  intro H len
  have hsub := (representativeGraph_subgraph hG ℓ).2.1
  have hm' : H.m ≤ G.m := Finset.card_le_card hsub
  have hgrid : weightPrecision C H ≤ (1024*(⌈max 1 C⌉₊ : ℕ)).size+3*(G.m+1).size :=
    (representativeGraph_weightPrecision_le C G ℓ).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3
        (Nat.size_le_size (Nat.succ_le_succ hm'))) _)
  apply (roundQueryLimbs_le_of_callerBlocks C H mem lengths L P hP hm
    (fun e he => hblocks e (hsub he))).trans
  unfold representativeGuestWidthBound
  exact Nat.succ_le_succ (Nat.add_le_add
    (max_le_max_right _ (Nat.size_le_size (Nat.mul_le_mul_left 2 hm')))
    (max_le_max_left _ hgrid))

/-- Caller-size factor for selecting the guest format and packing lengths. -/
def representativeGuestSetupMultiplier (D L m : ℕ) : ℕ :=
  98*L + 80*representativeGuestWidthBound D L m + 40*(2*m).size + 274

/-- Charge the guest setup for the representative graph to the original
live edge count and the caller limb width. -/
theorem representativeGuestSetupCost_le (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ)
    (mem : ℕ → ℕ) (lengths L P : ℕ) (hG : G.IsValid) (hP : P ≤ 4*L)
    (hm : 0 < (representativeGraph G ℓ).m)
    (hblocks : ∀ e ∈ G.E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 < Num.intVal mem (lengths+e*L) 4 L) :
    let H := representativeGraph G ℓ
    let len := fun e => if e ∈ H.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    ((98*L+92)+(80*roundQueryLimbs C H len+37))*H.m+40*(2*H.m).size+145 ≤
      representativeGuestSetupMultiplier ⌈max 1 C⌉₊ L G.m * (G.m+1) := by
  intro H len
  let B := representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m
  let A := 98*L+80*B+129
  let T := 40*(2*G.m).size+145
  have hm' : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hwidth : roundQueryLimbs C H len ≤ B :=
    representativeRoundQueryLimbs_le C G ℓ mem lengths L P hG hP hm hblocks
  have hmain : ((98*L+92)+(80*roundQueryLimbs C H len+37))*H.m ≤ A*G.m :=
    Nat.mul_le_mul (by dsimp only [A]; omega) hm'
  have hadd : 40*(2*H.m).size+145 ≤ T :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 40 (Nat.size_le_size (Nat.mul_le_mul_left 2 hm'))) _
  refine (Nat.add_le_add hmain hadd).trans ?_
  have heq : representativeGuestSetupMultiplier ⌈max 1 C⌉₊ L G.m = A+T := by
    dsimp only [representativeGuestSetupMultiplier,A,T,B]
    omega
  rw [heq, Nat.mul_add (A+T) G.m 1, Nat.mul_one]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) (Nat.le_add_left _ _)

end MinCostFlow.LastLevelProgram
