module

public import MinCostFlow.LastLevelProgram.SelectedRound
public import MinCostFlow.LastLevelProgram.CollectionHeader
import WordRAM.Tactic

/-!
# Repeating the last-level round

Definition 5.8 (pages 19–20) collects the trees from successive weight
updates. The loop passes its current allocation pointer and round
index to the round procedure and advances to the returned pointer.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Register zero is the current allocation pointer, register one is
the round count, and register two is the round index. -/
def lastLevelRoundsBody (entry : ℕ) (args : List Expr) : Stmt :=
  forRange 2 (.const 0) (.reg 1) (.call 0 entry args)

/-- The loop and its call instruction use no random bits. -/
theorem lastLevelRoundsBody_noRand (entry : ℕ) (args : List Expr) :
    (lastLevelRoundsBody entry args).NoRand := by
  simp [lastLevelRoundsBody, forRange, forUp, Stmt.NoRand]

/-- Execute every last-level round in order. The invariant may track
both the current weights and the already written branches. -/
theorem lastLevelRounds_triple {w entry : ℕ} {p : Program} {args : List Expr}
    (rounds budget : ℕ) (Inv : ℕ → State → Prop)
    (hw : 1 < 2^w) (hn : rounds < 2^w)
    (hinit : ∀ st, Inv 0 st → Inv 0 { st with regs := Function.update st.regs 2 0 })
    (hbound : ∀ i st, Inv i st → st.regs 1 = rounds)
    (hstep : ∀ i < rounds, ∀ st, Inv i st → st.regs 2 = i →
      ∃ (C : Contract) (vs : List ℕ), MeetsContract w p entry C ∧
        evalArgs w st args = some vs ∧ (∀ a ∈ vs, a < 2^w) ∧ C.pre vs st.mem ∧
        C.cost vs st.mem ≤ budget ∧
        ∀ ret mem pos, C.post vs st.mem ret mem →
          Inv (i+1) {mem := mem, regs := Function.update (Function.update st.regs 0 ret) 2 (i+1), pos := pos}) :
    Triple w p (fun st => Inv 0 st) (lastLevelRoundsBody entry args)
      (normalPost (Inv rounds)) (fun _ => (argsSize args + budget + 10) * rounds + 7) := by
  let J := fun i (st : State) => Inv i st ∧ st.regs 2 = i
  have loop := Triple.forRange_const (p := p) (r := 2) (lo := .const 0) (hi := .reg 1)
    (body := .call 0 entry args) (Inv := J) (P := fun st => Inv 0 st)
    (argsSize args + budget + 1) 0 rounds (Nat.zero_le _) hw (fun _ => hn)
    (fun st h => ⟨by eval_expr, hinit st h, by simp⟩)
    (fun _ _ _ _ h => h.2)
    (fun i st _ _ h => by
      have hreg := hbound i st h.1
      eval_expr)
    (fun i _ hi st ω ⟨hinv, hidx⟩ => by
      obtain ⟨C, vs, hc, ha, hw', hp, hcost, hpost⟩ := hstep i hi st hinv hidx
      obtain ⟨out, cost, ret, hr, hresult, hret, hf, hcost'⟩ :=
        runs_call_of_meetsContract (r := 0) hc ha hw' hp ω
      have hregs : out.regs = Function.update st.regs 0 ret := by
        funext r
        by_cases he : r = 0
        · simpa [he] using hret
        · simpa [Function.update_of_ne he] using hf r he
      have hidx' : out.regs 2 = i := (hf 2 (by decide)).trans hidx
      refine ⟨.normal, out, cost, hr, ⟨⟨?_, by simp⟩, hidx'⟩, by change cost ≤ argsSize args + budget + 1; omega⟩
      have hnext := hpost ret out.mem out.pos hresult
      change Inv (i+1) { mem := out.mem, regs := Function.update out.regs 2 (i+1), pos := out.pos }
      rw [hregs]
      exact hnext)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.1
  · intro st _
    simp only [Nat.sub_zero, Expr.size]
    rw [Nat.mul_comm rounds]

/-- Repeat the last-level round with the collection prefix as part of the
invariant. Each round must return fresh memory beyond the branch it adds. -/
theorem collectionRounds_triple {w entry : ℕ} {p : Program} {args : List Expr}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (collection rounds budget vCap eCap h L P : ℕ)
    (Inv : ℕ → State → Prop)
    (hw : 1 < 2^w) (hn : rounds < 2^w)
    (hinit : ∀ st, Inv 0 st → Inv 0 {st with regs := Function.update st.regs 2 0})
    (hbound : ∀ i st, Inv i st → st.regs 1 = rounds)
    (hstep : ∀ i < rounds, ∀ st, Inv i st → st.regs 2 = i →
      ∃ (C : Contract) (vs : List ℕ), MeetsContract w p entry C ∧
        evalArgs w st args = some vs ∧ (∀ a ∈ vs, a < 2^w) ∧ C.pre vs st.mem ∧
        C.cost vs st.mem ≤ budget ∧
        ∀ ret mem pos, C.post vs st.mem ret mem →
          Inv (i+1) ⟨mem, Function.update (Function.update st.regs 0 ret) 2 (i+1), pos⟩ ∧
          st.regs 0 ≤ ret ∧
          (∀ a < st.regs 0, a ≠ collection+1+i → mem a = st.mem a) ∧
          (let base := mem (collection+1+i)
           BranchWithin mem base (collection+1+rounds) ret vCap eCap L E ∧
             MinRatio.LSFAt mem base vCap eCap h L P E (branches i))) :
    Triple w p (fun st => Inv 0 st ∧ collection+1+rounds ≤ st.regs 0 ∧
      st.mem collection = rounds) (lastLevelRoundsBody entry args)
      (normalPost fun st => Inv rounds st ∧ collection+1+rounds ≤ st.regs 0 ∧
        CollectionPrefix st.mem collection rounds rounds (st.regs 0) vCap eCap h L P E branches)
      (fun _ => (argsSize args + budget + 10) * rounds + 7) := by
  let J := fun i (st : State) => Inv i st ∧ collection+1+rounds ≤ st.regs 0 ∧
    CollectionPrefix st.mem collection rounds i (st.regs 0) vCap eCap h L P E branches
  have loop := lastLevelRounds_triple (p := p) (entry := entry) (args := args)
    rounds budget J hw hn
    (fun st hs => ⟨hinit st hs.1, by simpa using hs.2⟩)
    (fun i st hs => hbound i st hs.1)
    (fun i hi st hs hidx => by
      obtain ⟨C,vs,hc,ha,hwords,hpre,hcost,hpost⟩ := hstep i hi st hs.1 hidx
      refine ⟨C,vs,hc,ha,hwords,hpre,hcost,?_⟩
      intro ret mem pos hm
      obtain ⟨hI,hle,hframe,hnew⟩ := hpost ret mem pos hm
      refine ⟨hI, ?_, ?_⟩
      · simpa using hs.2.1.trans hle
      · simpa using collectionPrefix_succ hs.2.2 hi hle hs.2.1 hframe hnew)
  refine loop.conseq (fun st hs => ⟨hs.1,hs.2.1,?_,hs.2.2,?_⟩) (fun _ _ hs => hs)
    (fun _ _ => le_rfl)
  · exact Nat.zero_le _
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)

/-- A completed loop can publish at the original handle once its invariant
supplies the caller frame and the final cursor bounds. -/
theorem collectionRounds_publish_triple {w entry copy src dst count bound vCap eCap h L P cost : ℕ}
    {p : Program} {args : List Expr} {E : Finset ℕ} {branches : ℕ → LSF}
    (mem : ℕ → ℕ) (Initial Final : State → Prop)
    (hloop : Triple w p Initial (lastLevelRoundsBody entry args)
      (normalPost fun st => Final st ∧ src+1+count ≤ st.regs 0 ∧
        CollectionPrefix st.mem src count count (st.regs 0) vCap eCap h L P E branches)
      (fun _ => cost))
    (hfinal : ∀ st, Final st →
      st.regs 3 = src ∧ st.regs 151 = dst ∧ st.regs 1 = count ∧
      st.regs 0 ≤ bound ∧ st.regs 0 < 2^w ∧ ZeroFrom st.mem (st.regs 0) ∧
      (∀ a < dst, st.mem a = mem a))
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hw : 1 < 2^w) (hsep : dst+1+count ≤ src) :
    Triple w p Initial
      (.seq (lastLevelRoundsBody entry args) (publishRuntimeCollection copy))
      (fun o out => ∃ limit, o = .returned limit ∧ dst+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem dst count count limit vCap eCap h L P E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < dst, out.mem a = mem a))
      (fun _ => cost+(17*(count+1)+19)+1) := by
  have hpublish := publishRuntimeCollection_triple (w := w) (copy := copy)
    (bound := bound) (vCap := vCap) (eCap := eCap) (h := h) (L := L) (P := P)
    (E := E) (branches := branches) mem hc hw hsep
  apply Triple.seq_normal_const hloop
  apply hpublish.conseq
  · intro st ⟨hst,hspan,hprefix⟩
    obtain ⟨hsrc,hdst,hcount,hbound,hfit,hzero,hframe⟩ := hfinal st hst
    exact ⟨hsrc,hdst,hcount,hspan,hbound,hfit,hprefix,hzero,hframe⟩
  · exact fun _ _ hs => hs
  · exact fun _ _ => le_rfl

/-- Reserve the collection table, run the rounds, and return its base.
The caller places the round count in register one and the base in register three. -/
def rebuildCollectionBody (init round : ℕ) (args : List Expr) : Stmt :=
  .seq (.call 0 init [.reg 3,.reg 1])
    (.seq (lastLevelRoundsBody round args) (.ret (.reg 3)))

/-- The initializer and round loop return the collection at its original
base, with a constant cost in addition to the loop. -/
theorem rebuildCollection_runs {w init round : ℕ} {p : Program} {ω : ℕ → Bool}
    {args : List Expr} {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (base count vCap eCap h L P budget : ℕ)
    (Inv : State → Prop)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hb : st.regs 3 = base) (hn : st.regs 1 = count)
    (hfit : base+1+count < 2^w) (hz : ZeroFrom st.mem base)
    (hInv : ∀ ret mem pos, (initCollectionContract w).post [base,count] st.mem ret mem →
      Inv ⟨mem,Function.update st.regs 0 ret,pos⟩)
    (hloop : Triple w p Inv (lastLevelRoundsBody round args)
      (normalPost fun out => out.regs 3 = base ∧
        MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches))
      (fun _ => budget)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionBody init round args) st o out cost ∧
      (o.value = base ∧
        MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches)) ∧
      cost ≤ budget+17 := by
  have hbfit : base < 2^w := by omega
  have hnfit : count < 2^w := by omega
  apply runs_start_le
  unfold rebuildCollectionBody
  refine runs_seq_call_le hi (vs := [base,count]) (by eval_expr) ?_
    ⟨base,count,rfl,hfit,hz⟩ ?_
  · intro a ha
    rcases (show a = base ∨ a = count by simpa using ha) with rfl | rfl
    · exact hbfit
    · exact hnfit
  · intro ret mem pos hpost
    refine runs_seq_triple_le hloop (hInv ret mem pos hpost) ?_
    intro out ⟨hreg,hlayout⟩
    refine runs_ret_le (v := base) (by eval_expr) ⟨rfl,hlayout⟩ ?_
    change 0+2+10+2+budget+1+2 ≤ budget+17
    omega

/-- Reserve the header, build initial weights, run the rounds, and then
execute the final publication step. -/
def rebuildCollectionThen (init weights round : ℕ)
    (weightArgs roundArgs : List Expr) (finish : Stmt) : Stmt :=
  .seq (.call 0 init [.reg 3,.reg 1])
    (.seq (.call 0 weights weightArgs)
      (.seq (lastLevelRoundsBody round roundArgs) finish))

/-- Rebuild and return the staged collection header. -/
def rebuildPreparedCollectionBody (init weights round : ℕ)
    (weightArgs roundArgs : List Expr) : Stmt :=
  rebuildCollectionThen init weights round weightArgs roundArgs (.ret (.reg 3))

/-- The initialization and rounds pass their final state to publication. -/
theorem rebuildCollectionThen_runs {w init weights round : ℕ}
    {p : Program} {ω : ℕ → Bool} {weightArgs roundArgs : List Expr}
    (st : State) (base count setupBudget loopBudget finishBudget : ℕ)
    (finish : Stmt) (Ready : State → Prop) (Post : Outcome → State → Prop)
    (Inv : State → Prop) (W : Contract)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hw : MeetsContract w p weights W)
    (hb : st.regs 3 = base) (hn : st.regs 1 = count)
    (hfit : base+1+count < 2^w) (hz : ZeroFrom st.mem base)
    (hsetup : ∀ ret mem pos, (initCollectionContract w).post [base,count] st.mem ret mem →
      ∃ vs, evalArgs w ⟨mem,Function.update st.regs 0 ret,pos⟩ weightArgs = some vs ∧
        (∀ a ∈ vs, a < 2^w) ∧ W.pre vs mem ∧ W.cost vs mem ≤ setupBudget ∧
        ∀ next out pos', W.post vs mem next out →
          Inv ⟨out,Function.update st.regs 0 next,pos'⟩)
    (hloop : Triple w p Inv (lastLevelRoundsBody round roundArgs)
      (normalPost Ready) (fun _ => loopBudget))
    (hfinish : Triple w p Ready finish Post (fun _ => finishBudget)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round weightArgs roundArgs finish)
      st o out cost ∧ Post o out ∧
      cost ≤ argsSize weightArgs+setupBudget+loopBudget+finishBudget+17 := by
  have hbfit : base < 2^w := by omega
  have hnfit : count < 2^w := by omega
  apply runs_start_le
  unfold rebuildCollectionThen
  refine runs_seq_call_le hi (vs := [base,count]) (by eval_expr) ?_
    ⟨base,count,rfl,hfit,hz⟩ ?_
  · intro a ha
    rcases (show a = base ∨ a = count by simpa using ha) with rfl | rfl
    · exact hbfit
    · exact hnfit
  · intro ret mem pos hpost
    obtain ⟨vs,he,hwords,hpre,hcost,hInv⟩ := hsetup ret mem pos hpost
    refine runs_seq_call_le hw he hwords hpre ?_
    intro next out pos' hp
    have hInv' := hInv next out pos' hp
    have hInv'' : Inv ⟨out,Function.update (Function.update st.regs 0 ret) 0 next,pos'⟩ := by
      simpa using hInv'
    refine runs_seq_triple_le hloop hInv'' ?_
    intro final hReady
    obtain ⟨o,finished,c,hr,hpost,hc⟩ := hfinish.runs ω hReady
    refine ⟨o,finished,c,hr,hpost,?_⟩
    change 0+2+10+2+argsSize weightArgs+W.cost vs mem+2+loopBudget+1+c ≤ _
    omega

/-- The collection controller returns the original header. The
weight setup contributes its own bounded cost before the round loop. -/
theorem rebuildPreparedCollection_runs {w init weights round : ℕ}
    {p : Program} {ω : ℕ → Bool} {weightArgs roundArgs : List Expr}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (base count vCap eCap h L P setupBudget loopBudget : ℕ)
    (Inv : State → Prop) (W : Contract)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hw : MeetsContract w p weights W)
    (hb : st.regs 3 = base) (hn : st.regs 1 = count)
    (hfit : base+1+count < 2^w) (hz : ZeroFrom st.mem base)
    (hsetup : ∀ ret mem pos, (initCollectionContract w).post [base,count] st.mem ret mem →
      ∃ vs, evalArgs w ⟨mem,Function.update st.regs 0 ret,pos⟩ weightArgs = some vs ∧
        (∀ a ∈ vs, a < 2^w) ∧ W.pre vs mem ∧ W.cost vs mem ≤ setupBudget ∧
        ∀ next out pos', W.post vs mem next out →
          Inv ⟨out,Function.update st.regs 0 next,pos'⟩)
    (hloop : Triple w p Inv (lastLevelRoundsBody round roundArgs)
      (normalPost fun out => out.regs 3 = base ∧
        MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches))
      (fun _ => loopBudget)) :
    ∃ o out cost, Runs w p ω (rebuildPreparedCollectionBody init weights round weightArgs roundArgs)
      st o out cost ∧
      (o.value = base ∧ MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches)) ∧
      cost ≤ argsSize weightArgs+setupBudget+loopBudget+19 := by
  unfold rebuildPreparedCollectionBody
  have hfinish : Triple w p (fun out => out.regs 3 = base ∧
      MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches))
      (.ret (.reg 3))
      (fun o out => o.value = base ∧
        MinRatio.LSFCollectionAt out.mem base vCap eCap h L P E (count,branches))
      (fun _ => 2) := by
    intro out ω' ⟨hreg,hlayout⟩
    exact ⟨.returned base,out,2,runs_ret_iff.mpr
      ⟨base,congrArg some hreg,rfl,rfl,rfl⟩,⟨rfl,hlayout⟩,le_rfl⟩
  simpa only [Nat.add_assoc] using rebuildCollectionThen_runs (ω := ω) st base count
    setupBudget loopBudget 2 (.ret (.reg 3)) _ _ Inv W hi hw hb hn hfit hz hsetup hloop hfinish

end MinCostFlow.LastLevelProgram
