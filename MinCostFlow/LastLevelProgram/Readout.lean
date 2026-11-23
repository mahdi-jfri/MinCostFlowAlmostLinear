module

public import MinCostFlow.MinRatio.LastLevelContract
public import MinCostFlow.LastLevelProgram.CollectionHeader
import WordRAM.Tactic

/-!
# Readout of the last-level collection

The collection of Definition 5.8 (pages 19–20) has a table of branch
pointers. Readout follows one pointer and copies its four-word header
into fresh memory.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM MinRatio

/-- The collection owns the interval from its handle to the end of its
allocation. Its branches are immutable and carry zero potential. -/
def lastLevelRepresentation (vCap eCap h L P : ℕ) (E : Finset ℕ) :
    DSRep (ℕ × (ℕ → LSF)) where
  τ := ℕ
  rep b s limit mem :=
    b+1+s.1 ≤ limit ∧ CollectionPrefix mem b s.1 s.1 limit vCap eCap h L P E s.2
  phi _ _ _ := 0
  foot b limit a := b ≤ a ∧ a < limit

/-- A full prefix at the caller handle supplies both the representation
and the runtime initializer's model postcondition. -/
theorem lastLevelRuntime_initPost_of_prefix {w L vCap eCap multiplier Q graph lengths handle limit : ℕ}
    (fmt : Num.Format w) (tool : Chain.LastLevelTool) (G : MGraph)
    (allocation : ℕ → List ℕ → ℕ) (input out : ℕ → ℕ)
    (hbits : fmt.limbBits = 4) :
    let args := [graph,lengths,L,fmt.precision,handle]
    let s := tool.build G (readEdgeValues input lengths 4 L fmt.precision G.E)
    handle+1+s.1 ≤ limit →
    CollectionPrefix out handle s.1 s.1 limit vCap eCap 4 L fmt.precision G.E s.2 →
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep handle s limit out ∧
    (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation).initPost
      args input s out := by
  intro args s hlimit hprefix
  refine ⟨⟨hlimit,hbits.symm ▸ hprefix⟩,?_,?_⟩
  · simp only [args,s,hbits]
    rfl
  · simpa only [hbits,show heapArg args = handle from rfl] using hprefix.complete

/-- The allocated interval determines the collection representation. -/
theorem lastLevelRepresentation_local (vCap eCap h L P : ℕ) (E : Finset ℕ) :
    (lastLevelRepresentation vCap eCap h L P E).Local := by
  intro b s limit mem out hmem
  refine ⟨?_, rfl⟩
  rintro ⟨hbound, hprefix⟩
  exact ⟨hbound,hprefix.of_agree hbound (fun a hlo hhi => (hmem a ⟨hlo,hhi⟩).symm)⟩

/-- Read operation zero, with arguments `[handle, branch, heap]`. -/
def readoutBody : Stmt :=
  .assign 3 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 1))) ;;
  .assign 4 (.load (.reg 3)) ;;
  .store (.reg 2) (.reg 4) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 4) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 4) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.const 3))) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 4) ;;
  .ret (.bin .add (.reg 2) (.const 4))

/-- The readout uses no random bits. -/
theorem readoutBody_noRand : readoutBody.NoRand := by simp [readoutBody, Stmt.NoRand]

/-- Copy the four pointers of the requested branch without moving its payload. -/
theorem readout_runs {w : ℕ} (p : Program) (ω : ℕ → Bool) (b j h pos : ℕ)
    (mem : ℕ → ℕ) (htable : b + 1 + j < h)
    (hsrc : mem (b + 1 + j) + 3 < h) (hroom : h + 4 < 2 ^ w)
    (_hp₀ : mem (mem (b + 1 + j)) < 2 ^ w)
    (_hp₁ : mem (mem (b + 1 + j) + 1) < 2 ^ w)
    (_hp₂ : mem (mem (b + 1 + j) + 2) < 2 ^ w)
    (_hp₃ : mem (mem (b + 1 + j) + 3) < 2 ^ w) :
    ∃ o st c, Runs w p ω readoutBody (startState [b, j, h] mem pos) o st c ∧
      (o.value = h + 4 ∧
      st.mem = Function.update (Function.update (Function.update (Function.update mem
        h (mem (mem (b + 1 + j)))) (h + 1) (mem (mem (b + 1 + j) + 1)))
        (h + 2) (mem (mem (b + 1 + j) + 2))) (h + 3) (mem (mem (b + 1 + j) + 3))) ∧
      c ≤ 64 := by
  apply runs_start_le
  unfold readoutBody
  wram_run
  · simp only [show mem (b + 1 + j) + 1 ≠ h by omega,
      show mem (b + 1 + j) + 2 ≠ h by omega,
      show mem (b + 1 + j) + 3 ≠ h by omega, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  · wram_cost

/-- Operation zero preserves the collection and writes a branch header in
the four freshly allocated cells. -/
theorem readout_rep_runs {w vCap eCap bits L P : ℕ} {E : Finset ℕ}
    (p : Program) (ω : ℕ → Bool) (b j heap limit pos : ℕ)
    (mem : ℕ → ℕ) (s : ℕ × (ℕ → LSF))
    (hrep : (lastLevelRepresentation vCap eCap bits L P E).rep b s limit mem)
    (hj : j < s.1) (hlimit : limit ≤ heap)
    (hz : ZeroFrom mem heap) (hroom : heap+4 < 2^w) :
    ∃ out cost, Runs w p ω readoutBody (startState [b,j,heap] mem pos)
        (.returned (heap+4)) out cost ∧
      (lastLevelRepresentation vCap eCap bits L P E).rep b s limit out.mem ∧
      LSFAt out.mem heap vCap eCap bits L P E (s.2 j) ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (heap+4) ∧ cost ≤ 64 := by
  have hslot : b+1+j < heap := by have := hrep.1; omega
  obtain ⟨hspan,hbranch⟩ := hrep.2.2.2 j hj
  let base := mem (b+1+j)
  change BranchWithin mem base (b+1+s.1) limit vCap eCap L E at hspan
  obtain ⟨_,hB,_,hT,_,hF,_,hR,_,hS,_,_,hN,hD⟩ := hspan
  obtain ⟨o,out,c,hr,⟨ho,hm⟩,hcost⟩ := readout_runs (w := w) p ω b j heap pos mem hslot
    (by change base+3 < heap; omega) hroom (by change mem base < 2^w; omega)
    (by change mem (base+1) < 2^w; omega) (by change mem (base+2) < 2^w; omega)
    (by change mem (base+3) < 2^w; omega)
  cases o with
  | normal => simp [Outcome.value] at ho
  | returned v =>
    change v = heap+4 at ho
    subst v
    have hframe a (ha : a < heap ∨ heap+4 ≤ a) : out.mem a = mem a := by
      rw [hm]
      simp only [Function.update_of_ne (show a ≠ heap+3 by omega),
        Function.update_of_ne (show a ≠ heap+2 by omega),
        Function.update_of_ne (show a ≠ heap+1 by omega),
        Function.update_of_ne (show a ≠ heap by omega)]
    have hbelow a (ha : a < heap) := hframe a (Or.inl ha)
    have hb : LSFAt out.mem base vCap eCap bits L P E (s.2 j) :=
      lsfAt_of_agree_below hbranch (hB.trans hlimit) (hT.trans hlimit) (hF.trans hlimit)
        (hR.trans hlimit) (hS.trans hlimit) (fun e he => (hN e he).trans hlimit)
        (fun e he => (hD e he).trans hlimit) hbelow
    refine ⟨out,c,hr,⟨hrep.1,hrep.2.of_agree hrep.1
      (fun a _ ha => hbelow a (ha.trans_le hlimit))⟩,?_,hbelow,
      fun a ha => (hframe a (Or.inr ha)).trans (hz a (by omega)),hcost⟩
    unfold LSFAt at hb ⊢
    rw [hbelow base (by omega), hbelow (base+1) (by omega), hbelow (base+2) (by omega),
      hbelow (base+3) (by omega)] at hb
    have hp (i : ℕ) (hi : i < 4) : out.mem (heap+i) = mem (base+i) := by
      rw [hm]
      interval_cases i <;> simp [base, Function.update_of_ne]
    rw [show out.mem heap = mem base from hp 0 (by decide), hp 1 (by decide),
      hp 2 (by decide), hp 3 (by decide)]
    exact hb

/-- An initializer that publishes a complete collection can be linked
with the common operation-zero procedure. -/
theorem lastLevelRuntime_implements_of_init {w vCap eCap L multiplier Q init op : ℕ}
    {p : Program} (fmt : Num.Format w) (tool : Chain.LastLevelTool) (G : MGraph)
    (allocation : ℕ → List ℕ → ℕ) (body : Stmt)
    (hbody : p.procs[init]? = some body) (hop : p.procs[op]? = some readoutBody)
    (hinit :
      let D := lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation
      ∀ args mem pos ω, (∀ a ∈ args, a < 2^w) → D.initPre args mem →
        ZeroFrom mem (heapArg args) → heapArg args + D.initSpace args mem < 2^w →
        ∃ limit out cost s, Runs w p ω body (startState args mem pos) (.returned limit) out cost ∧
          (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep
            (heapArg args) s limit out.mem ∧ D.initPost args mem s out.mem ∧
          limit ≤ heapArg args + D.initSpace args mem ∧ ZeroFrom out.mem limit ∧
          (∀ a < heapArg args, out.mem a = mem a) ∧ cost ≤ D.initCost args mem) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation) := by
  refine ⟨lastLevelRepresentation_local _ _ _ _ _ _, ?_, ?_⟩
  · intro args mem pos ω hwords hpre hz hroom
    obtain ⟨limit,out,c,s,hr,hrep,hpost,hupper,hzero,hframe,hcost⟩ :=
      hinit args mem pos ω hwords hpre hz hroom
    have hbase := hrep.1
    exact ⟨body,hbody,.returned limit,out,c,hr,s,limit,hrep,hpost,
      ⟨by change heapArg args ≤ limit; omega,hupper,hzero,fun a ha _ => hframe a ha,
        fun a ha => Or.inr ha⟩,hcost⟩
  · intro i b s limit args mem pos ω _ hhead hrep hpre hfoot hz hroom
    change ℕ at limit
    obtain ⟨rfl,handle,j,heap,rfl,hj⟩ := hpre
    have hh : handle = b := Option.some.inj hhead
    subst handle
    have hbase := hrep.1
    have hlimit : limit ≤ heap := by
      have hl : b ≤ limit-1 := by omega
      have hu : limit-1 < limit := by omega
      have h := hfoot (limit-1) ⟨hl,hu⟩
      change limit-1 < heap at h
      omega
    obtain ⟨out,c,hr,hrep',hbranch,hframe,hzero,hcost⟩ :=
      readout_rep_runs p ω b j heap limit pos mem s hrep hj hlimit hz hroom
    exact ⟨readoutBody,hop,.returned (heap+4),out,c,hr,s,limit,hrep',
      ⟨rfl,rfl,hbranch⟩,⟨by simp [heapArg,Outcome.value],le_rfl,hzero,
        fun a ha _ => hframe a ha,fun _ ha => Or.inl ha⟩,hcost⟩

/-- Link an initializer that publishes a full collection to the
operation-zero readout at the runtime contract's entry points. -/
theorem lastLevelRuntime_implements_of_prefix {w vCap eCap L multiplier Q init op : ℕ}
    {p : Program} (fmt : Num.Format w) (tool : Chain.LastLevelTool) (G : MGraph)
    (allocation : ℕ → List ℕ → ℕ) (body : Stmt)
    (hbody : p.procs[init]? = some body) (hop : p.procs[op]? = some readoutBody)
    (hinit :
      let D := lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation
      ∀ graph lengths heap mem pos ω,
        let args := [graph,lengths,L,fmt.precision,heap]
        let s := tool.build G (readEdgeValues mem lengths 4 L fmt.precision G.E)
        (∀ a ∈ args, a < 2^w) → D.initPre args mem →
        ZeroFrom mem heap → heap+D.initSpace args mem < 2^w →
        ∃ limit out cost, Runs w p ω body (startState args mem pos) (.returned limit) out cost ∧
          heap+1+s.1 ≤ limit ∧
          CollectionPrefix out.mem heap s.1 s.1 limit vCap eCap 4 L fmt.precision G.E s.2 ∧
          limit ≤ heap+D.initSpace args mem ∧ ZeroFrom out.mem limit ∧
          (∀ a < heap, out.mem a = mem a) ∧ cost ≤ D.initCost args mem) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation) := by
  apply lastLevelRuntime_implements_of_init fmt tool G allocation body hbody hop
  intro D args mem pos ω hwords hpre hz hroom
  have hinput := hpre
  obtain ⟨graph,lengths,heap,rfl,hbits,_⟩ := hinput
  obtain ⟨limit,out,cost,hr,hlimit,hprefix,hupper,hzero,hframe,hcost⟩ :=
    hinit graph lengths heap mem pos ω hwords hpre hz hroom
  obtain ⟨hrep,hpost⟩ := lastLevelRuntime_initPost_of_prefix (Q := Q) (multiplier := multiplier)
    (graph := graph) fmt tool G allocation mem out.mem hbits hlimit hprefix
  exact ⟨limit,out,cost,_,hr,hrep,hpost,hupper,hzero,hframe,hcost⟩

end MinCostFlow.LastLevelProgram
