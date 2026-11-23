module

public import MinCostFlow.LastLevelProgram.StagedOutputLayout
public import MinCostFlow.LastLevelProgram.PackPrecision
import MinCostFlow.Num.ShiftFacts
import WordRAM.Link
import Mathlib.Tactic

/-!
# Widening the staged numeric inputs

Definition 5.8 (pages 19–20) uses root distances computed in scratch
blocks wide enough to hold intermediate values.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Pass the caller width and the scratch width separately to the
widening packers. Registers 18 and 26 hold the two scratch table bases. -/
def stagedWideLengthArgs : List Expr :=
  [.reg 27,.reg 18,.reg 28,.reg 19,.reg 1,.const 0,.const 0,.reg 24]

/-- The live weights use their compact edge order and source stride. -/
def stagedWideWeightArgs : List Expr :=
  [.reg 31,.reg 26,.reg 32,.reg 19,.reg 1,.const 0,.const 0,.reg 24]

/-- Both widening calls use the scratch width installed by the layout
and leave the caller's source width unchanged. -/
theorem stagedWidePackArgs_eval {w : ℕ} (st : State)
    (src lengths names weights old stride L K m : ℕ)
    (h27 : st.regs 27 = src) (h18 : st.regs 18 = lengths) (h28 : st.regs 28 = names)
    (h31 : st.regs 31 = weights) (h26 : st.regs 26 = old) (h32 : st.regs 32 = stride)
    (h19 : st.regs 19 = L) (h24 : st.regs 24 = K) (h1 : st.regs 1 = m) :
    evalArgs w st stagedWideLengthArgs = some [src,lengths,names,L,m,0,0,K] ∧
    evalArgs w st stagedWideWeightArgs = some [weights,old,stride,L,m,0,0,K] := by
  simp [stagedWideLengthArgs,stagedWideWeightArgs,evalArgs,Expr.eval,
    h27,h18,h28,h31,h26,h32,h19,h24,h1]

/-- The two widened tables are built consecutively in fresh scratch
and preserve the caller's original signed numerators. -/
theorem stagedWidePack_runs {w h packLengths packWeights : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (src lengths names weights stride L K : ℕ)
    (hl : MeetsContract w p packLengths (packWideValuesContract w h G))
    (hw : MeetsContract w p packWeights (packWideWeightsContract w h))
    (hlen : evalArgs w st stagedWideLengthArgs = some [src,lengths,names,L,G.m,0,0,K])
    (hweights : evalArgs w st stagedWideWeightArgs =
      some [weights,lengths+G.m*K,stride,L,G.m,0,0,K])
    (hlWords : ∀ x ∈ [src,lengths,names,L,G.m,0,0,K], x < 2^w)
    (hwWords : ∀ x ∈ [weights,lengths+G.m*K,stride,L,G.m,0,0,K], x < 2^w)
    (hlPre : (packWideValuesContract w h G).pre [src,lengths,names,L,G.m,0,0,K] st.mem)
    (hsource : ∀ i < G.m, weights+i*stride+L ≤ lengths ∧ Num.Valid st.mem (weights+i*stride) h L)
    (hroom : lengths+G.m*K+G.m*K < 2^w) :
    ∃ out cost, Runs w p ω
        (.seq (.call 29 packLengths stagedWideLengthArgs) (.call 33 packWeights stagedWideWeightArgs))
        st .normal out cost ∧
      (∀ i < G.m,
        (Num.Valid out.mem (lengths+i*K) h K ∧ Num.intVal out.mem (lengths+i*K) h K =
          Num.intVal st.mem (src+edgeName G i*L) h L) ∧
        (Num.Valid out.mem (lengths+G.m*K+i*K) h K ∧
          Num.intVal out.mem (lengths+G.m*K+i*K) h K =
          Num.intVal st.mem (weights+i*stride) h L)) ∧
      (∀ a < lengths, out.mem a = st.mem a) ∧ ZeroFrom out.mem (lengths+G.m*K+G.m*K) ∧
      (∀ r, r ≠ 29 → r ≠ 33 → out.regs r = st.regs r) ∧
      cost ≤ 2*((30*K+90)*G.m+20)+1 := by
  have hlPreCopy := hlPre
  obtain ⟨s,d,n,l,k,ha,hsmall,hLK,hK,hm,_,_,_,_,_⟩ := hlPreCopy
  simp only [List.cons.injEq,and_true,true_and] at ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := ha
  obtain ⟨mid,cl,rl,hrl,hpl,_,hrKeep,hcl⟩ :=
    runs_call_of_meetsContract (r := 29) hl hlen hlWords hlPre ω
  obtain ⟨s,d,n,l,k,ha,_,hvals,hframe,hz⟩ := hpl
  simp only [List.cons.injEq,and_true,true_and] at ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := ha
  have hargs : evalArgs w mid stagedWideWeightArgs =
      some [weights,lengths+G.m*K,stride,L,G.m,0,0,K] := by
    simpa only [stagedWideWeightArgs,evalArgs,Expr.eval,hrKeep 31 (by decide),
      hrKeep 26 (by decide),hrKeep 32 (by decide),hrKeep 19 (by decide),
      hrKeep 1 (by decide),hrKeep 24 (by decide)] using hweights
  have hsrc i (hi : i < G.m) (k : ℕ) (hk : k < L) :
      mid.mem (weights+i*stride+k) = st.mem (weights+i*stride+k) := by
    have he := (hsource i hi).1
    exact hframe _ (by omega)
  obtain ⟨out,cw,rwgt,hrw,hpw,_,hkeep, hcw⟩ :=
    runs_call_of_meetsContract (r := 33) hw hargs hwWords
      ⟨weights,lengths+G.m*K,stride,L,G.m,K,rfl,hsmall,hLK,hK,hm,hroom,
        fun i hi => ⟨(hsource i hi).1.trans (Nat.le_add_right _ _),
          fun k hk => (hsrc i hi k hk).trans_lt ((hsource i hi).2 k hk)⟩,hz⟩ ω
  obtain ⟨s,d,t,l,m,k,ha,_,hnew,hframe',hz'⟩ := hpw
  simp only [List.cons.injEq,and_true,true_and] at ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ha
  refine ⟨out,cl+cw+1,runs_seq_iff.mpr (Or.inr ⟨mid,cl,cw,hrl,hrw,rfl⟩),?_,
    fun a ha => (hframe' _ (ha.trans_le (Nat.le_add_right _ _))).trans (hframe _ ha),hz',
    fun r h29 h33 => (hkeep r h33).trans (hrKeep r h29),?_⟩
  · intro i hi
    have hidx := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hidx
    have hf k (hk : k < K) : out.mem (lengths+i*K+k) = mid.mem (lengths+i*K+k) :=
      hframe' _ (by omega)
    exact ⟨⟨fun k hk => (hf k hk).trans_lt ((hvals i hi).1 k hk),
      (Num.intVal_congr hf).trans (hvals i hi).2⟩,
      (hnew i hi).1,(hnew i hi).2.trans (Num.intVal_congr (hsrc i hi))⟩
  · change cl ≤ argsSize stagedWideLengthArgs+((30*K+90)*G.m+10)+1 at hcl
    change cw ≤ argsSize stagedWideWeightArgs+((30*K+90)*G.m+10)+1 at hcw
    have ha : argsSize stagedWideLengthArgs = 8 := by decide
    have hb : argsSize stagedWideWeightArgs = 8 := by decide
    omega

/-- The denominator is written after the widened arrays using their
scratch width and the model precision. -/
def stagedWideDenominatorArgs : List Expr :=
  [.reg 35, .reg 24, .reg 23, .bin .sub (.reg 25) (.reg 24)]

/-- Evaluate the denominator arguments after installing the numeric scratch layout. -/
theorem stagedWideDenominatorArgs_eval {w : ℕ} (st : State) (scale K P dst : ℕ)
    (h35 : st.regs 35 = scale) (h24 : st.regs 24 = K) (h23 : st.regs 23 = P)
    (h25 : st.regs 25 = dst+K) (hd : dst < 2^w) :
    evalArgs w st stagedWideDenominatorArgs = some [scale,K,P,dst] := by
  simp [stagedWideDenominatorArgs,evalArgs,Expr.eval,h35,h24,h23,h25,hd]

/-- Prepare the scaled denominator at the scratch width. The initial
scale word occupies the preceding block. -/
theorem stagedWideDenominator_runs {w h prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (scale K P dst : ℕ)
    (hprepare : MeetsContract w p prepare (denominatorContract w h))
    (h35 : st.regs 35 = scale) (h24 : st.regs 24 = K) (h23 : st.regs 23 = P)
    (h25 : st.regs 25 = dst+K)
    (hwords : ∀ x ∈ [scale,K,P,dst], x < 2^w)
    (hfit : Num.Fits h K (scale : ℤ))
    (hscaled : Num.Fits h K ((scale : ℤ)*(2 : ℤ)^P))
    (hzero : ZeroFrom st.mem dst) (hroom : dst+2*K < 2^w) :
    ∃ out cost, Runs w p ω (.call 34 prepare stagedWideDenominatorArgs) st .normal out cost ∧
      out.regs 34 = dst+2*K ∧ Num.Valid out.mem (dst+K) h K ∧
      Num.intVal out.mem (dst+K) h K = (scale : ℤ)*(2 : ℤ)^P ∧
      (∀ a < dst, out.mem a = st.mem a) ∧ ZeroFrom out.mem (dst+2*K) ∧
      (∀ r, r ≠ 34 → out.regs r = st.regs r) ∧ cost ≤ 56*K+70 := by
  obtain ⟨out,cost,ret,hr,hpost,hret,hkeep,hcost⟩ := runs_call_of_meetsContract (r := 34)
    hprepare (stagedWideDenominatorArgs_eval st scale K P dst h35 h24 h23 h25 (hwords dst (by simp)))
    hwords ⟨scale,K,P,dst,rfl,hfit,hscaled,hzero,hroom⟩ ω
  obtain ⟨s,k,q,b,heq,hcursor,hvalid,hval,hframe,hfresh⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
  refine ⟨out,cost,hr,hret.trans hcursor,hvalid,hval,hframe,hcursor ▸ hfresh,hkeep,?_⟩
  change cost ≤ argsSize stagedWideDenominatorArgs+(56*K+62)+1 at hcost
  have ha : argsSize stagedWideDenominatorArgs = 6 := by decide
  omega

/-- Pack both numeric arrays and write the scaled denominator. -/
def stagedWideInputsBody (packLengths packWeights prepare : ℕ) : Stmt :=
  .seq (.seq (.call 29 packLengths stagedWideLengthArgs) (.call 33 packWeights stagedWideWeightArgs))
    (.call 34 prepare stagedWideDenominatorArgs)

/-- The denominator write preserves both widened tables and the prefix. -/
theorem stagedWideInputs_runs {w h packLengths packWeights prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st packed : State) (lengths m K scale P packCost : ℕ) (len wt : ℕ → ℤ)
    (hpack : Runs w p ω
      (.seq (.call 29 packLengths stagedWideLengthArgs) (.call 33 packWeights stagedWideWeightArgs))
      st .normal packed packCost)
    (hprepare : MeetsContract w p prepare (denominatorContract w h))
    (h35 : packed.regs 35 = scale) (h24 : packed.regs 24 = K) (h23 : packed.regs 23 = P)
    (h25 : packed.regs 25 = lengths+m*K+m*K+K)
    (hwords : ∀ x ∈ [scale,K,P,lengths+m*K+m*K], x < 2^w)
    (hfit : Num.Fits h K (scale : ℤ))
    (hscaled : Num.Fits h K ((scale : ℤ)*(2 : ℤ)^P))
    (hzero : ZeroFrom packed.mem (lengths+m*K+m*K))
    (hroom : lengths+m*K+m*K+2*K < 2^w)
    (hframe : ∀ a < lengths, packed.mem a = st.mem a)
    (hpacked : ∀ i < m,
      (Num.Valid packed.mem (lengths+i*K) h K ∧ Num.intVal packed.mem (lengths+i*K) h K = len i) ∧
      (Num.Valid packed.mem (lengths+m*K+i*K) h K ∧
        Num.intVal packed.mem (lengths+m*K+i*K) h K = wt i)) :
    let dst := lengths+m*K+m*K
    ∃ out cost, Runs w p ω (stagedWideInputsBody packLengths packWeights prepare) st .normal out cost ∧
      (∀ i < m,
        (Num.Valid out.mem (lengths+i*K) h K ∧ Num.intVal out.mem (lengths+i*K) h K = len i) ∧
        (Num.Valid out.mem (lengths+m*K+i*K) h K ∧ Num.intVal out.mem (lengths+m*K+i*K) h K = wt i)) ∧
      Num.Valid out.mem (dst+K) h K ∧ Num.intVal out.mem (dst+K) h K = (scale : ℤ)*(2 : ℤ)^P ∧
      ZeroFrom out.mem (dst+2*K) ∧ (∀ a < lengths, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 34 → out.regs r = packed.regs r) ∧ cost ≤ packCost+56*K+71 := by
  intro dst
  obtain ⟨out,c,hr,_,hv,he,hbefore,hfresh,hkeep,hc⟩ :=
    stagedWideDenominator_runs (ω := ω) packed scale K P dst hprepare h35 h24 h23 h25
      hwords hfit hscaled hzero hroom
  refine ⟨out,packCost+c+1,runs_seq_iff.mpr (Or.inr ⟨packed,packCost,c,hpack,hr,rfl⟩),
    ?_,hv,he,hfresh,fun a ha => (hbefore _ (ha.trans_le (by dsimp [dst]; omega))).trans (hframe _ ha),
    hkeep,by omega⟩
  intro i hi
  have hend := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hend
  have hl k (hk : k < K) : out.mem (lengths+i*K+k) = packed.mem (lengths+i*K+k) :=
    hbefore _ (by dsimp [dst]; omega)
  have hw k (hk : k < K) : out.mem (lengths+m*K+i*K+k) = packed.mem (lengths+m*K+i*K+k) :=
    hbefore _ (by dsimp [dst]; omega)
  obtain ⟨⟨hlv,hle⟩,hwv,hwe⟩ := hpacked i hi
  exact ⟨⟨fun k hk => (hl k hk).trans_lt (hlv k hk),(Num.intVal_congr hl).trans hle⟩,
    fun k hk => (hw k hk).trans_lt (hwv k hk),(Num.intVal_congr hw).trans hwe⟩

/-- A state with both scratch table addresses installed can prepare
the widened model inputs and the denominator in one run. -/
theorem stagedWideInputs_of_registers
    {w h packLengths packWeights prepare extend store shift : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (src lengths names weights stride L K scale P : ℕ)
    (hlBody : p.procs[packLengths]? = some (packWideValuesBody extend))
    (hwBody : p.procs[packWeights]? = some (packWideWeightsBody extend))
    (hdBody : p.procs[prepare]? = some (denominatorBody store shift))
    (hextend : p.HasAt extend (Num.signExtendModule extend h))
    (hstore : p.procs[store]? = some (storeWordBody h))
    (hshift : p.HasAt shift (Num.shiftLeftModule shift h))
    (hh : 0 < h) (hbits : 2*h+2 ≤ w)
    (h27 : st.regs 27 = src) (h18 : st.regs 18 = lengths) (h28 : st.regs 28 = names)
    (h31 : st.regs 31 = weights) (h26 : st.regs 26 = lengths+G.m*K) (h32 : st.regs 32 = stride)
    (h19 : st.regs 19 = L) (h24 : st.regs 24 = K) (h1 : st.regs 1 = G.m)
    (h35 : st.regs 35 = scale) (h23 : st.regs 23 = P)
    (h25 : st.regs 25 = lengths+G.m*K+G.m*K+K)
    (hwords : ∀ r ∈ ([27,18,28,31,26,32,19,24,1,35,23] : List ℕ), st.regs r < 2^w)
    (hlPre : (packWideValuesContract w h G).pre [src,lengths,names,L,G.m,0,0,K] st.mem)
    (hsource : ∀ i < G.m, weights+i*stride+L ≤ lengths ∧ Num.Valid st.mem (weights+i*stride) h L)
    (hfit : Num.Fits h K (scale : ℤ))
    (hscaled : Num.Fits h K ((scale : ℤ)*(2 : ℤ)^P))
    (hroom : lengths+G.m*K+G.m*K+2*K < 2^w) :
    let dst := lengths+G.m*K+G.m*K
    ∃ out cost, Runs w p ω (stagedWideInputsBody packLengths packWeights prepare) st .normal out cost ∧
      (∀ i < G.m,
        (Num.Valid out.mem (lengths+i*K) h K ∧ Num.intVal out.mem (lengths+i*K) h K =
          Num.intVal st.mem (src+edgeName G i*L) h L) ∧
        (Num.Valid out.mem (lengths+G.m*K+i*K) h K ∧ Num.intVal out.mem (lengths+G.m*K+i*K) h K =
          Num.intVal st.mem (weights+i*stride) h L)) ∧
      Num.Valid out.mem (dst+K) h K ∧ Num.intVal out.mem (dst+K) h K = (scale : ℤ)*(2 : ℤ)^P ∧
      ZeroFrom out.mem (dst+2*K) ∧ (∀ a < lengths, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 29 → r ≠ 33 → r ≠ 34 → out.regs r = st.regs r) ∧
      cost ≤ 2*((30*K+90)*G.m+20)+56*K+72 := by
  intro dst
  have hwSmall : 1 < 2^w :=
    (by decide : 1 < 2^1).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : Num.base h < 2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hext := Num.signExtend_meetsContract hh hwSmall hb hextend
  have hl := packWideValues_meetsContract G hlBody hext
  have hw := packWideWeights_meetsContract hwBody hext
  have hd := denominator_meetsContract hh hbits hdBody (storeWord_meetsContract hwSmall hb hstore) hshift
  have fit (r : ℕ) (hr : r ∈ ([27,18,28,31,26,32,19,24,1,35,23] : List ℕ)) := hwords r hr
  obtain ⟨hla,hwa⟩ := stagedWidePackArgs_eval (w := w) st src lengths names weights
    (lengths+G.m*K) stride L K G.m h27 h18 h28 h31 h26 h32 h19 h24 h1
  have hwl : ∀ x ∈ [src,lengths,names,L,G.m,0,0,K], x < 2^w := by
    simp [← h27,← h18,← h28,← h19,← h1,← h24,fit 27 (by decide),fit 18 (by decide),fit 28 (by decide),fit 19 (by decide),fit 1 (by decide),fit 24 (by decide)]
  have hww : ∀ x ∈ [weights,lengths+G.m*K,stride,L,G.m,0,0,K], x < 2^w := by
    have hmEnd : lengths+G.m*K < 2^w := by omega
    have he : lengths+st.regs 1*st.regs 24 < 2^w := by rwa [h1,h24]
    simp [← h31,← h32,← h19,← h1,← h24,fit 31 (by decide),fit 32 (by decide),fit 19 (by decide),fit 1 (by decide),fit 24 (by decide),he]
  obtain ⟨packed,cp,hp,hvalues,hframe,hfresh,hkeep,hcp⟩ :=
    stagedWidePack_runs (ω := ω) st G src lengths names weights stride L K hl hw
      hla hwa hwl hww hlPre hsource (by omega)
  have hwd : ∀ x ∈ [scale,K,P,dst], x < 2^w := by
    have hdst : dst < 2^w := by dsimp [dst]; omega
    simp [← h35,← h24,← h23,fit 35 (by decide),fit 24 (by decide),fit 23 (by decide),hdst]
  obtain ⟨out,c,hr,hval,hv,he,hz,hf,hregs,hc⟩ :=
    stagedWideInputs_runs (ω := ω) st packed lengths G.m K scale P cp
      (fun i => Num.intVal st.mem (src+edgeName G i*L) h L)
      (fun i => Num.intVal st.mem (weights+i*stride) h L) hp hd
      ((hkeep 35 (by decide) (by decide)).trans h35)
      ((hkeep 24 (by decide) (by decide)).trans h24)
      ((hkeep 23 (by decide) (by decide)).trans h23)
      ((hkeep 25 (by decide) (by decide)).trans h25) hwd hfit hscaled hfresh hroom hframe hvalues
  exact ⟨out,c,hr,hval,hv,he,hz,hf,fun r h29 h33 h34 => (hregs r h34).trans (hkeep r h29 h33),by omega⟩

/-- Install the scratch layout, copy the endpoints, and prepare the widened arrays. -/
def prepareWideStagedNumericBody (copy packLengths packWeights prepare : ℕ) : Stmt :=
  .seq installWideStagedNumericLayout
    (.seq (.call 30 copy stagedNumericEndpointArgs)
      (stagedWideInputsBody packLengths packWeights prepare))

/-- Copying the endpoints preserves both all earlier allocations and
the fresh region where the widened numeric tables will be written. -/
theorem stagedWideEndpoints_runs {w copy : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (staging tails : ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hs : st.regs 5 = staging) (hd : st.regs 21 = tails) (hm : st.regs 1 = G.m)
    (hw : 1 < 2^w) (hsep : staging+2*G.m ≤ tails) (hroom : tails+2*G.m < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hz : ZeroFrom st.mem tails) :
    ∃ out cost, Runs w p ω (.call 30 copy stagedNumericEndpointArgs) st .normal out cost ∧
      ListAt out.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (tails+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ a < tails, out.mem a = st.mem a) ∧ ZeroFrom out.mem (tails+2*G.m) ∧
      (∀ r, r ≠ 30 → out.regs r = st.regs r) ∧ cost ≤ 34*G.m+16 := by
  obtain ⟨out,c,hr,htail,hhead,hframe,hkeep,hcost⟩ :=
    stagedNumericEndpoints_runs (ω := ω) (result := 30) st G staging tails hc hs hd hm
      hw hsep hroom ht hh
  exact ⟨out,c,hr,htail,hhead,fun a ha => hframe a (Or.inl ha),
    fun a ha => (hframe a (Or.inr ha)).trans (hz a (ha.trans' (Nat.le_add_right _ _))),hkeep,hcost⟩

/-- The scratch arrays are prepared above the copied endpoints. Their
prefix frame carries both endpoint arrays to the numeric call. -/
theorem prepareWideStagedNumeric_of_layout
    {w copy packLengths packWeights prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st laid : State) (G : MGraph) (staging tails layoutCost inputBudget : ℕ)
    (Post : State → Prop)
    (hlayout : Runs w p ω installWideStagedNumericLayout st .normal laid layoutCost)
    (hmem : laid.mem = st.mem)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h5 : laid.regs 5 = staging) (h21 : laid.regs 21 = tails) (h1 : laid.regs 1 = G.m)
    (hw : 1 < 2^w) (hsep : staging+2*G.m ≤ tails) (hroom : tails+2*G.m < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hz : ZeroFrom st.mem tails)
    (hinputs : ∀ endpoints, ZeroFrom endpoints.mem (tails+2*G.m) →
      (∀ a < tails, endpoints.mem a = st.mem a) →
      (∀ r, r ≠ 30 → endpoints.regs r = laid.regs r) →
      ∃ out cost, Runs w p ω (stagedWideInputsBody packLengths packWeights prepare)
        endpoints .normal out cost ∧ Post out ∧
        (∀ a < tails+2*G.m, out.mem a = endpoints.mem a) ∧ cost ≤ inputBudget) :
    ∃ out cost, Runs w p ω (prepareWideStagedNumericBody copy packLengths packWeights prepare)
      st .normal out cost ∧ Post out ∧
      ListAt out.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (tails+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ a < tails, out.mem a = st.mem a) ∧ cost ≤ layoutCost+34*G.m+inputBudget+18 := by
  obtain ⟨endpoints,ce,he,htail,hhead,hframe,hfresh,hkeep,hcost⟩ :=
    stagedWideEndpoints_runs (ω := ω) laid G staging tails hcopy h5 h21 h1 hw hsep hroom
      (hmem.symm ▸ ht) (hmem.symm ▸ hh) (hmem.symm ▸ hz)
  have hprefix (a : ℕ) (ha : a < tails) : endpoints.mem a = st.mem a :=
    (hframe a ha).trans (congrFun hmem a)
  obtain ⟨out,ci,hi,hpost,hout,hci⟩ := hinputs endpoints hfresh hprefix hkeep
  have htail' : ListAt out.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) := by
    intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hout _ (by omega)).trans (htail i hi)
  have hhead' : ListAt out.mem (tails+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) := by
    intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hout _ (by omega)).trans (hhead i hi)
  have hseq := runs_seq_iff.mpr (Or.inr ⟨endpoints,ce,ci,he,hi,rfl⟩)
  exact ⟨out,layoutCost+(ce+ci+1)+1,runs_seq_iff.mpr (Or.inr ⟨laid,layoutCost,_,hlayout,hseq,rfl⟩),
    hpost,htail',hhead',fun a ha => (hout _ (by omega)).trans (hprefix a ha),by omega⟩

set_option maxHeartbeats 800000 in
/-- Prepare the widened numeric inputs directly from the selected round state. -/
theorem prepareWideStagedNumeric_runs
    {w h copy packLengths packWeights prepare extend store shift : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph)
    (staging cursor levels src names weights stride L P scale : ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hl : p.procs[packLengths]? = some (packWideValuesBody extend))
    (hwg : p.procs[packWeights]? = some (packWideWeightsBody extend))
    (hd : p.procs[prepare]? = some (denominatorBody store shift))
    (hx : p.HasAt extend (Num.signExtendModule extend h))
    (hstore : p.procs[store]? = some (storeWordBody h))
    (hshift : p.HasAt shift (Num.shiftLeftModule shift h))
    (hbits : 2*h+2 ≤ w) (hh : 0 < h) (hw : 7 < 2^w) (hn : 0 < G.n)
    (h0 : st.regs 0 = G.n) (h1 : st.regs 1 = G.m) (h5 : st.regs 5 = staging)
    (h12 : st.regs 12 = cursor) (h14 : st.regs 14 = levels) (h19 : st.regs 19 = L)
    (h23 : st.regs 23 = P) (h27 : st.regs 27 = src) (h28 : st.regs 28 = names)
    (h31 : st.regs 31 = weights) (h32 : st.regs 32 = stride) (h35 : st.regs 35 = scale)
    (hwords : ∀ r, st.regs r < 2^w) (hprec : P+levels+7 < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hhead : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) :
    let K := L+(P+levels+7)/4
    let tails := cursor+1+G.m+G.n+stagedTraversalReserve G.n levels+G.n+6*G.n
    let lengths := tails+2*G.m
    let old := lengths+G.m*K
    let dst := old+G.m*K
    let dist := dst+2*K
    let heap := dist+G.n*K
    K < 2^w → heap < 2^w → staging+2*G.m ≤ tails → ZeroFrom st.mem tails →
    names+G.m ≤ tails → (∀ i < G.m, st.mem (names+i) = edgeName G i) →
    (∀ e ∈ G.E, src+e*L+L ≤ tails ∧ Num.Valid st.mem (src+e*L) h L) →
    (∀ i < G.m, weights+i*stride+L ≤ tails ∧ Num.Valid st.mem (weights+i*stride) h L) →
    Num.Fits h K (scale : ℤ) → Num.Fits h K ((scale : ℤ)*(2 : ℤ)^P) →
    ∃ out cost, Runs w p ω (prepareWideStagedNumericBody copy packLengths packWeights prepare)
      st .normal out cost ∧
      (∀ i < G.m,
        (Num.Valid out.mem (lengths+i*K) h K ∧ Num.intVal out.mem (lengths+i*K) h K =
          Num.intVal st.mem (src+edgeName G i*L) h L) ∧
        (Num.Valid out.mem (old+i*K) h K ∧ Num.intVal out.mem (old+i*K) h K =
          Num.intVal st.mem (weights+i*stride) h L)) ∧
      Num.Valid out.mem (dst+K) h K ∧ Num.intVal out.mem (dst+K) h K = (scale : ℤ)*(2 : ℤ)^P ∧
      ZeroFrom out.mem dist ∧
      out.regs 21 = tails ∧ out.regs 22 = tails+G.m ∧ out.regs 18 = lengths ∧
      out.regs 26 = old ∧ out.regs 25 = dst+K ∧ out.regs 17 = dist ∧
      out.regs 20 = heap ∧ out.regs 24 = K ∧
      (∀ r, r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34] : List ℕ) → out.regs r = st.regs r) ∧
      ListAt out.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (tails+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ a < tails, out.mem a = st.mem a) ∧
      cost ≤ stagedScratchWidthExpr.size+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
          [.reg 64])+37+34*G.m+(2*((30*K+90)*G.m+20)+56*K+72) := by
  intro K tails lengths old dst dist heap hK hheap hsep hz hnEnd hnames hlen hwt hfit hscaled
  have hheap' : (tails+G.m+G.m+G.m*K+G.m*K+K+K)+G.n*K < 2^w := by
    dsimp only [heap,dist,dst,old,lengths] at hheap
    omega
  obtain ⟨laid,cl,hr,hm,h21,h22,h18,h26,h25,h17,h20,h24,hkeep,hcl⟩ :=
    installWideStagedNumericLayout_runs (p := p) (ω := ω) st G.n G.m levels cursor L P
      h0 h1 h14 h12 h19 h23 hn hw hprec hK hheap'
  change laid.regs 18 = tails+G.m+G.m at h18
  change laid.regs 26 = tails+G.m+G.m+G.m*K at h26
  change laid.regs 25 = tails+G.m+G.m+G.m*K+G.m*K+K at h25
  change laid.regs 17 = tails+G.m+G.m+G.m*K+G.m*K+K+K at h17
  change laid.regs 20 = tails+G.m+G.m+G.m*K+G.m*K+K+K+G.n*K at h20
  have h18' : laid.regs 18 = lengths := by dsimp [lengths]; omega
  have h26' : laid.regs 26 = old := by dsimp [old,lengths]; omega
  have h25' : laid.regs 25 = dst+K := by dsimp [dst,old,lengths]; omega
  have h17' : laid.regs 17 = dist := by dsimp [dist,dst,old,lengths]; omega
  have h20' : laid.regs 20 = heap := by dsimp [heap,dist,dst,old,lengths]; omega
  obtain ⟨endpoints,ce,he,htail,hheads,hprefix,hfresh,hkeepE,hce⟩ :=
    stagedWideEndpoints_runs (ω := ω) laid G staging tails hc ((hkeep 5 (by decide)).trans h5)
      h21 ((hkeep 1 (by decide)).trans h1) ((by decide : 1 < 7).trans hw)
      hsep (by dsimp [heap,dist,dst,old,lengths] at hheap; omega)
      (hm.symm ▸ ht) (hm.symm ▸ hhead) (hm.symm ▸ hz)
  have hprefixInput (a : ℕ) (ha : a < tails) := (hprefix a ha).trans (congrFun hm a)
  have regs (r : ℕ) (hr : r ≠ 30) (hs : r ∉ ([64,21,22,18,26,25,17,20,24] : List ℕ)) :=
    (hkeepE r hr).trans (hkeep r hs)
  have hwordsE (r : ℕ) (hr : r ∈ ([27,18,28,31,26,32,19,24,1,35,23] : List ℕ)) :
      endpoints.regs r < 2^w := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [regs _ (by decide) (by decide)]; exact hwords _)
      | (rw [(hkeepE _ (by decide)).trans h18']; dsimp [heap,dist,dst,old] at hheap; omega)
      | (rw [(hkeepE _ (by decide)).trans h26']; dsimp [heap,dist,dst] at hheap; omega)
      | (rw [(hkeepE _ (by decide)).trans h24]; exact hK)
  have hsrcE e (he : e ∈ G.E) k (hk : k < L) :
      endpoints.mem (src+e*L+k) = st.mem (src+e*L+k) := by
    have hb := (hlen e he).1
    exact hprefixInput _ (by omega)
  have hwtE i (hi : i < G.m) k (hk : k < L) :
      endpoints.mem (weights+i*stride+k) = st.mem (weights+i*stride+k) := by
    have hb := (hwt i hi).1
    exact hprefixInput _ (by omega)
  have hLk : L ≤ K := Nat.le_add_right _ _
  have hroom : dst+2*K < 2^w := by dsimp [heap,dist] at hheap; omega
  obtain ⟨out,ci,hi,hval,hv,hden,hz',hf,hkeepI,hci⟩ :=
    stagedWideInputs_of_registers (ω := ω) endpoints G src lengths names weights stride L K scale P
      hl hwg hd hx hstore hshift hh hbits
      ((regs 27 (by decide) (by decide)).trans h27) ((hkeepE 18 (by decide)).trans h18')
      ((regs 28 (by decide) (by decide)).trans h28) ((regs 31 (by decide) (by decide)).trans h31)
      ((hkeepE 26 (by decide)).trans h26') ((regs 32 (by decide) (by decide)).trans h32)
      ((regs 19 (by decide) (by decide)).trans h19) ((hkeepE 24 (by decide)).trans h24)
      ((regs 1 (by decide) (by decide)).trans h1)
      ((regs 35 (by decide) (by decide)).trans h35) ((regs 23 (by decide) (by decide)).trans h23)
      ((hkeepE 25 (by decide)).trans h25') hwordsE
      ⟨src,lengths,names,L,K,rfl,((by decide : 1 < 7).trans hw),hLk,hK,h1 ▸ hwords 1,
        by dsimp [dst,old] at hroom; omega,
        fun e he => ⟨(hlen e he).1.trans (Nat.le_add_right _ _),
          fun k hk => (hsrcE e he k hk).trans_lt ((hlen e he).2 k hk)⟩,
        hnEnd.trans (Nat.le_add_right _ _),fun i hi => (hprefixInput _ (by omega)).trans (hnames i hi),
        hfresh⟩
      (fun i hi => ⟨(hwt i hi).1.trans (Nat.le_add_right _ _),
        fun k hk => (hwtE i hi k hk).trans_lt ((hwt i hi).2 k hk)⟩) hfit hscaled hroom
  have keep (r : ℕ) (h29 : r ≠ 29) (h30 : r ≠ 30) (h33 : r ≠ 33) (h34 : r ≠ 34) :=
    (hkeepI r h29 h33 h34).trans (hkeepE r h30)
  refine ⟨out,cl+(ce+ci+1)+1,runs_seq_iff.mpr (Or.inr ⟨laid,cl,_,hr,
    runs_seq_iff.mpr (Or.inr ⟨endpoints,ce,ci,he,hi,rfl⟩),rfl⟩),?_,hv,hden,hz',
    (keep 21 (by decide) (by decide) (by decide) (by decide)).trans h21,
    (keep 22 (by decide) (by decide) (by decide) (by decide)).trans h22,
    (keep 18 (by decide) (by decide) (by decide) (by decide)).trans h18',
    (keep 26 (by decide) (by decide) (by decide) (by decide)).trans h26',
    (keep 25 (by decide) (by decide) (by decide) (by decide)).trans h25',
    (keep 17 (by decide) (by decide) (by decide) (by decide)).trans h17',
    (keep 20 (by decide) (by decide) (by decide) (by decide)).trans h20',
    (keep 24 (by decide) (by decide) (by decide) (by decide)).trans h24,?_,?_,?_,?_,by omega⟩
  · intro i hi
    obtain ⟨⟨hlv,hle⟩,hwv,hwe⟩ := hval i hi
    exact ⟨⟨hlv,hle.trans (Num.intVal_congr (hsrcE _ (edgeName_mem hi)))⟩,
      hwv,hwe.trans (Num.intVal_congr (hwtE i hi))⟩
  · intro r hr
    exact (keep r (fun he => hr (by simp [he])) (fun he => hr (by simp [he]))
      (fun he => hr (by simp [he])) (fun he => hr (by simp [he]))).trans
        (hkeep r (fun he => hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at he ⊢; tauto)))
  · intro i hi
    have hidx : i < G.m := by simpa using hi
    exact (hf _ (by dsimp [lengths]; omega)).trans (htail i hi)
  · intro i hi
    have hidx : i < G.m := by simpa using hi
    exact (hf _ (by dsimp [lengths]; omega)).trans (hheads i hi)
  · intro a ha
    exact (hf a (ha.trans_le (Nat.le_add_right _ _))).trans (hprefixInput a ha)

/-- Run the stretch and weight pass on the widened numeric inputs. -/
def prepareAndRunWideStagedNumericBody (copy packLengths packWeights prepare adjacency numeric : ℕ) : Stmt :=
  .seq (prepareWideStagedNumericBody copy packLengths packWeights prepare)
    (stagedNumericBodyFrom adjacency numeric 24)

/-- Widened preparation and the numeric pass preserve the selected
tree and every caller word below the staged input boundary. -/
theorem prepareAndRunWideStagedNumeric_of_runs
    {w copy packLengths packWeights prepare adjacency numeric : ℕ}
    {p : Program} {ω : ℕ → Bool} {G T : MGraph}
    (st ready : State) (input : ℕ → ℕ) (base dest count tails adj records prepCost budget : ℕ)
    (Post : State → Prop)
    (hprep : Runs w p ω (prepareWideStagedNumericBody copy packLengths packWeights prepare)
      st .normal ready prepCost)
    (htree : selectedTreeAt G T base dest count input st.mem)
    (hbase : base ≤ dest) (hdest : dest+G.n ≤ adj) (hadj : adj ≤ records) (hrecords : records ≤ tails)
    (hframe : ∀ a < tails, ready.mem a = st.mem a)
    (hnumeric : retainedStagedTreeAt G T base dest count input ready.mem →
      (∀ a, dest+G.n ≤ a → a < records → ready.mem a = 0) →
      ∃ out cost, Runs w p ω (stagedNumericBodyFrom adjacency numeric 24) ready .normal out cost ∧
        Post out ∧ (∀ a < dest+G.n, out.mem a = ready.mem a) ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω
      (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric)
      st .normal out cost ∧ Post out ∧
      retainedStagedTreeAt G T base dest count input out.mem ∧ cost ≤ prepCost+budget+1 := by
  have hbaseAdj : base ≤ adj := hbase.trans ((Nat.le_add_right _ _).trans hdest)
  have hadjTails := hadj.trans hrecords
  have ht := retainedStagedTreeAt_of_frame htree (hbaseAdj.trans hadjTails) (hdest.trans hadjTails) hframe
  have hz : ZeroFrom st.mem (dest+G.n) := by
    obtain ⟨_,_,_,_,_,_,_,hz⟩ := htree
    exact hz
  obtain ⟨out,cr,hr,hpost,hpres,hcr⟩ := hnumeric ht
    (fun a ha hb => (hframe _ (hb.trans_le hrecords)).trans (hz a ha))
  exact ⟨out,prepCost+cr+1,runs_seq_iff.mpr (Or.inr ⟨ready,prepCost,cr,hprep,hr,rfl⟩),
    hpost,retainedStagedTreeAt_congr ht (hbase.trans (Nat.le_add_right _ _)) le_rfl hpres,by omega⟩

/-- The caller-width prefix of a widened output represents the same
fixed-point value whenever its signed numerator fits the caller. -/
theorem stagedWideOutput_prefix {mem : ℕ → ℕ} {addr h L K P : ℕ} {value : ℝ}
    (hLK : L ≤ K) (hv : Num.Valid mem addr h K)
    (he : Num.fixVal mem addr h K P = value)
    (hfit : Num.Fits h L (Num.intVal mem addr h K)) :
    Num.Valid mem addr h L ∧ Num.fixVal mem addr h L P = value := by
  refine ⟨fun i hi => hv i (hi.trans_le hLK),?_⟩
  unfold Num.fixVal at he ⊢
  rwa [Num.intVal_prefix_wrap hv hLK,Num.wrap_of_fits hfit]

/-- A nonnegative stretch or weight below the caller's capacity bound
can be read at caller width without a second conversion pass. -/
theorem stagedWideOutput_prefix_of_capacity {mem : ℕ → ℕ} {addr h L K P : ℕ}
    {value bound : ℝ} (hLK : L ≤ K) (hv : Num.Valid mem addr h K)
    (he : Num.fixVal mem addr h K P = value) (hpos : 0 ≤ value) (hbound : value ≤ bound)
    (hwidth : 2*(2 : ℝ)^P*bound < Num.capacity h L) :
    Num.Valid mem addr h L ∧ Num.fixVal mem addr h L P = value := by
  apply stagedWideOutput_prefix hLK hv he
  have hp : (0 : ℝ) < (2 : ℝ)^P := by positivity
  have hi : (Num.intVal mem addr h K : ℝ) = value*(2 : ℝ)^P := by
    exact (div_eq_iff hp.ne').mp he
  have hzero : (0 : ℝ) ≤ (Num.intVal mem addr h K : ℝ) := by
    rw [hi]
    exact mul_nonneg hpos hp.le
  have hc : 2*(Num.intVal mem addr h K : ℝ) < Num.capacity h L := by
    calc
      _ = 2*(2 : ℝ)^P*value := by rw [hi]; ring
      _ ≤ 2*(2 : ℝ)^P*bound := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ < _ := hwidth
  have hiNonneg : 0 ≤ Num.intVal mem addr h K := by exact_mod_cast hzero
  refine ⟨?_,by exact_mod_cast hc⟩
  have hcap : (0 : ℤ) ≤ (Num.capacity h L : ℤ) := Int.natCast_nonneg _
  omega

/-- Use the shared zero-shift packer to gather a widened output table
at caller width, preserving the decoded values and the allocated prefix. -/
theorem stagedWideOutput_pack_runs {w h P entry shift src L K m heap boundCost : ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    {value : ℕ → ℝ} {bound : ℝ}
    (he : p.procs[entry]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hargs : ∀ a ∈ [src,K,L,m,0,heap], a < 2^w)
    (hword : 1 < 2^w) (hLK : L ≤ K) (hsrc : ∀ i < m, src+i*K+L ≤ heap)
    (hz : ZeroFrom mem heap) (hroom : heap+m*L < 2^w)
    (hinput : ∀ i < m, Num.Valid mem (src+i*K) h K ∧
      Num.fixVal mem (src+i*K) h K P = value i ∧ 0 ≤ value i ∧ value i ≤ bound)
    (hwidth : 2*(2 : ℝ)^P*bound < Num.capacity h L)
    (hcost : (35*L+60)*m+10 ≤ boundCost) :
    ∃ out cost ret,
      Runs w p ω (packGuestWeightsBody shift) (startState [src,K,L,m,0,heap] mem pos)
        ret out cost ∧ ret.value = heap+m*L ∧
      ZeroFrom out.mem (heap+m*L) ∧ (∀ a < heap, out.mem a = mem a) ∧
      (∀ i < m, Num.Valid out.mem (heap+i*L) h L ∧
        Num.fixVal out.mem (heap+i*L) h L P = value i) ∧ cost ≤ boundCost := by
  have hprefix (i : ℕ) (hi : i < m) :=
    stagedWideOutput_prefix_of_capacity hLK (hinput i hi).1 (hinput i hi).2.1
      (hinput i hi).2.2.1 (hinput i hi).2.2.2 hwidth
  obtain ⟨body,hbody,ret,out,c,hr,hpost,hc⟩ :=
    packHostWeights_meetsContract (P := P) he hp hh hw [src,K,L,m,0,heap] mem pos ω hargs
      ⟨src,K,L,m,heap,rfl,hword,hargs m (by simp),hLK,hsrc,hz,hroom,
        fun i hi => (hprefix i hi).1⟩
  obtain ⟨src',K',L',m',heap',hparams,hret,hzero,hframe,hpacked⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at hparams
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hparams
  rw [he] at hbody
  cases Option.some.inj hbody
  exact ⟨out,c,ret,hr,hret,hret ▸ hzero,hframe,fun i hi =>
    ⟨(hpacked i hi).1,(hpacked i hi).2.trans (hprefix i hi).2⟩,
    (show c ≤ (35*L+60)*m+10 from hc).trans hcost⟩

/-- Call the output packer with either widened table's source and stride.
The return register advances the heap cursor and all other registers survive. -/
theorem stagedWideOutput_packCall_runs {w h P entry shift src L K m heap r : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {args : List Expr}
    {value : ℕ → ℝ} {bound : ℝ}
    (he : p.procs[entry]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (heval : evalArgs w st args = some [src,K,L,m,0,heap])
    (hargs : ∀ a ∈ [src,K,L,m,0,heap], a < 2^w)
    (hword : 1 < 2^w) (hLK : L ≤ K) (hsrc : ∀ i < m, src+i*K+L ≤ heap)
    (hz : ZeroFrom st.mem heap) (hroom : heap+m*L < 2^w)
    (hinput : ∀ i < m, Num.Valid st.mem (src+i*K) h K ∧
      Num.fixVal st.mem (src+i*K) h K P = value i ∧ 0 ≤ value i ∧ value i ≤ bound)
    (hwidth : 2*(2 : ℝ)^P*bound < Num.capacity h L) :
    ∃ out cost, Runs w p ω (.call r entry args) st .normal out cost ∧
      out.regs r = heap+m*L ∧ (∀ j, j ≠ r → out.regs j = st.regs j) ∧
      ZeroFrom out.mem (heap+m*L) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (heap+i*L) h L ∧
        Num.fixVal out.mem (heap+i*L) h L P = value i) ∧
      cost ≤ (35*L+60)*m+10+argsSize args+1 := by
  have hprefix (i : ℕ) (hi : i < m) :=
    stagedWideOutput_prefix_of_capacity hLK (hinput i hi).1 (hinput i hi).2.1
      (hinput i hi).2.2.1 (hinput i hi).2.2.2 hwidth
  obtain ⟨out,cost,ret,hr,hpost,hreg,hkeep,hcost⟩ :=
    runs_call_of_meetsContract (r := r) (packHostWeights_meetsContract (P := P) he hp hh hw)
      heval hargs ⟨src,K,L,m,heap,rfl,hword,hargs m (by simp),hLK,hsrc,hz,hroom,
        fun i hi => (hprefix i hi).1⟩ ω
  obtain ⟨src',K',L',m',heap',hparams,hret,hzero,hframe,hpacked⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at hparams
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hparams
  refine ⟨out,cost,hr,hreg.trans hret,hkeep,hret ▸ hzero,hframe,?_,?_⟩
  · exact fun i hi => ⟨(hpacked i hi).1,(hpacked i hi).2.trans (hprefix i hi).2⟩
  · simpa [packHostWeightsContract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcost

/-- Append the compact stretches, then the compact updated weights. Register
37 receives the start of the compact weights and 16 receives the new heap end. -/
def packStagedWideOutputs (pack : ℕ) : Stmt :=
  .seq (.call 37 pack [.reg 36,.reg 37,.reg 19,.reg 1,.const 0,.reg 16])
    (.call 16 pack [.reg 38,.reg 39,.reg 19,.reg 1,.const 0,.reg 37])

/-- Both output tables fit at caller width. Packing them preserves all
previous allocations and leaves fresh memory after the compact weights. -/
theorem packStagedWideOutputs_runs {w h P pack shift m L heap stretch weight sStride wStride : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {sval wval : ℕ → ℝ}
    (he : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hregs : st.regs 1 = m ∧ st.regs 19 = L ∧ st.regs 16 = heap ∧
      st.regs 36 = stretch ∧ st.regs 37 = sStride ∧ st.regs 38 = weight ∧ st.regs 39 = wStride)
    (hsmall : ∀ a ∈ [m,L,stretch,sStride,weight,wStride], a < 2^w)
    (hword : 1 < 2^w) (hsL : L ≤ sStride) (hwL : L ≤ wStride)
    (hsEnd : ∀ i < m, stretch+i*sStride+L ≤ heap)
    (hwEnd : ∀ i < m, weight+i*wStride+L ≤ heap)
    (hz : ZeroFrom st.mem heap) (hroom : heap+m*L+m*L < 2^w)
    (hs : ∀ i < m, Num.Valid st.mem (stretch+i*sStride) h L ∧
      Num.fixVal st.mem (stretch+i*sStride) h L P = sval i)
    (hwgt : ∀ i < m, Num.Valid st.mem (weight+i*wStride) h L ∧
      Num.fixVal st.mem (weight+i*wStride) h L P = wval i) :
    ∃ out cost, Runs w p ω (packStagedWideOutputs pack) st .normal out cost ∧
      out.regs 37 = heap+m*L ∧ out.regs 16 = heap+m*L+m*L ∧
      (∀ r, r ≠ 37 → r ≠ 16 → out.regs r = st.regs r) ∧
      ZeroFrom out.mem (heap+m*L+m*L) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (heap+i*L) h L ∧
        Num.fixVal out.mem (heap+i*L) h L P = sval i) ∧
      (∀ i < m, Num.Valid out.mem (heap+m*L+i*L) h L ∧
        Num.fixVal out.mem (heap+m*L+i*L) h L P = wval i) ∧
      cost ≤ 2*((35*L+60)*m+17)+1 := by
  obtain ⟨hm,hL,hheap,hstretch,hss,hweight,hws⟩ := hregs
  have hmid : heap+m*L < 2^w := by omega
  have hheapWord : heap < 2^w := by omega
  have hzero : 0 < 2^w := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp] at hsmall
  obtain ⟨hmWord,hLWord,hsWord,hssWord,hwWord,hwsWord⟩ := hsmall
  let sargs : List Expr := [.reg 36,.reg 37,.reg 19,.reg 1,.const 0,.reg 16]
  let wargs : List Expr := [.reg 38,.reg 39,.reg 19,.reg 1,.const 0,.reg 37]
  have seval : evalArgs w st sargs = some [stretch,sStride,L,m,0,heap] := by
    simp [sargs,evalArgs,Expr.eval,hstretch,hss,hL,hm,hheap,hzero]
  have hc := packHostWeights_meetsContract (P := P) he hp hh hw
  obtain ⟨mid,cs,rs,hsRun,hsPost,hsRet,hsKeep,hsCost⟩ :=
    runs_call_of_meetsContract (r := 37) hc seval
      (by simp [hsWord,hssWord,hLWord,hmWord,hzero,hheapWord])
      ⟨stretch,sStride,L,m,heap,rfl,hword,hmWord,hsL,hsEnd,hz,hmid,fun i hi => (hs i hi).1⟩ ω
  obtain ⟨a,b,c,d,e,hsParams,hsEndRet,hsZero,hsFrame,hsPacked⟩ := hsPost
  simp only [List.cons.injEq,and_true,true_and] at hsParams
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hsParams
  have hsCursor := hsRet.trans hsEndRet
  have weval : evalArgs w mid wargs = some [weight,wStride,L,m,0,heap+m*L] := by
    simp [wargs,evalArgs,Expr.eval,(hsKeep 38 (by decide)).trans hweight,
      (hsKeep 39 (by decide)).trans hws,(hsKeep 19 (by decide)).trans hL,
      (hsKeep 1 (by decide)).trans hm,hsCursor,hzero]
  have hwAgree (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < L) :
      mid.mem (weight+i*wStride+j) = st.mem (weight+i*wStride+j) := by
    have := hwEnd i hi
    exact hsFrame _ (by omega)
  obtain ⟨out,cw,rw',hwRun,hwPost,hwRet,hwKeep,hwCost⟩ :=
    runs_call_of_meetsContract (r := 16) hc weval
      (by simp [hwWord,hwsWord,hLWord,hmWord,hzero,hmid])
      ⟨weight,wStride,L,m,heap+m*L,rfl,hword,hmWord,hwL,
        fun i hi => (hwEnd i hi).trans (Nat.le_add_right _ _),hsEndRet ▸ hsZero,hroom,
        fun i hi j hj => (hwAgree i hi j hj).trans_lt ((hwgt i hi).1 j hj)⟩ ω
  obtain ⟨a,b,c,d,e,hwParams,hwEndRet,hwZero,hwFrame,hwPacked⟩ := hwPost
  simp only [List.cons.injEq,and_true,true_and] at hwParams
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hwParams
  refine ⟨out,cs+cw+1,runs_seq_iff.mpr (Or.inr ⟨mid,cs,cw,hsRun,hwRun,rfl⟩),
    (hwKeep 37 (by decide)).trans hsCursor,hwRet.trans hwEndRet,
    fun r h37 h16 => (hwKeep r h16).trans (hsKeep r h37),hwEndRet ▸ hwZero,
    fun a ha => (hwFrame a (by omega)).trans (hsFrame a ha),?_,?_,?_⟩
  · intro i hi
    have heq (j : ℕ) (hj : j < L) : out.mem (heap+i*L+j) = mid.mem (heap+i*L+j) := by
      have hle := Nat.mul_le_mul_right L hi
      rw [Nat.succ_mul] at hle
      exact hwFrame _ (by omega)
    refine ⟨fun j hj => (heq j hj).trans_lt ((hsPacked i hi).1 j hj),?_⟩
    calc
      _ = Num.fixVal mid.mem (heap+i*L) h L P := by
        unfold Num.fixVal
        rw [Num.intVal_congr heq]
      _ = _ := (hsPacked i hi).2.trans (hs i hi).2
  · intro i hi
    refine ⟨(hwPacked i hi).1,(hwPacked i hi).2.trans ?_⟩
    calc
      _ = Num.fixVal st.mem (weight+i*wStride) h L P := by
        unfold Num.fixVal
        rw [Num.intVal_congr (hwAgree i hi)]
      _ = _ := (hwgt i hi).2
  · simp [packHostWeightsContract,sargs,wargs,argsSize,Expr.size] at hsCost hwCost
    omega

/-- Install the compact table bases and their common caller-width stride.
Both bases are recovered from the allocation end and the table size. -/
def packedStagedOutputArgs : List Expr :=
  let size := Expr.bin .mul (.reg 1) (.reg 19)
  [.bin .sub (.reg 16) (.bin .add size size), .reg 19,
    .bin .sub (.reg 16) size, .reg 19]

/-- Reset the publisher's output pointers after packing both tables. -/
def installPackedStagedOutputLayout : Stmt :=
  stagedAddressAssignments [36,37,38,39] packedStagedOutputArgs

/-- Installing compact output addresses preserves the packed tables and
all registers outside the publisher's four table descriptors. -/
theorem installPackedStagedOutputLayout_runs {w m L heap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (hm : st.regs 1 = m) (hL : st.regs 19 = L)
    (hend : st.regs 16 = heap+m*L+m*L)
    (hfit : heap+m*L+m*L < 2^w) :
    ∃ out cost, Runs w p ω installPackedStagedOutputLayout st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 36 = heap ∧ out.regs 37 = L ∧
      out.regs 38 = heap+m*L ∧ out.regs 39 = L ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize packedStagedOutputArgs+9 := by
  let rs : List ℕ := [36,37,38,39]
  have ha (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid packedStagedOutputArgs = some [heap,L,heap+m*L,L] := by
    have hprod : m*L < 2^w := by omega
    have hdouble : m*L+m*L < 2^w := by omega
    have hbase : heap < 2^w := by omega
    have hnext : heap+m*L < 2^w := by omega
    have hsub : heap+m*L+m*L-(m*L+m*L) = heap := by omega
    simp [packedStagedOutputArgs,evalArgs,Expr.eval,BinOp.eval,
      (hf 1 (by decide)).trans hm,(hf 19 (by decide)).trans hL,
      (hf 16 (by decide)).trans hend,hprod,hdouble,hbase,hnext,hsub]
  obtain ⟨out,cost,hr,hmem,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs packedStagedOutputArgs
      [heap,L,heap+m*L,L] rfl ha
  refine ⟨out,cost,hr,hmem,?_,?_,?_,?_,?_,hcost⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h36 h37 h38 h39
  simp [h36,h37,h38,h39]

/-- Pack the two output tables and expose their bases to branch publication. -/
def preparePackedStagedOutputs (pack : ℕ) : Stmt :=
  .seq (packStagedWideOutputs pack) installPackedStagedOutputLayout

/-- Branch publication receives two compact caller-width tables, with the
same values as the incoming prefixes and fresh memory above them. -/
theorem preparePackedStagedOutputs_runs {w h P pack shift m L heap stretch weight sStride wStride : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {sval wval : ℕ → ℝ}
    (he : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hregs : st.regs 1 = m ∧ st.regs 19 = L ∧ st.regs 16 = heap ∧
      st.regs 36 = stretch ∧ st.regs 37 = sStride ∧ st.regs 38 = weight ∧ st.regs 39 = wStride)
    (hsmall : ∀ a ∈ [m,L,stretch,sStride,weight,wStride], a < 2^w)
    (hword : 1 < 2^w) (hsL : L ≤ sStride) (hwL : L ≤ wStride)
    (hsEnd : ∀ i < m, stretch+i*sStride+L ≤ heap)
    (hwEnd : ∀ i < m, weight+i*wStride+L ≤ heap)
    (hz : ZeroFrom st.mem heap) (hroom : heap+m*L+m*L < 2^w)
    (hs : ∀ i < m, Num.Valid st.mem (stretch+i*sStride) h L ∧
      Num.fixVal st.mem (stretch+i*sStride) h L P = sval i)
    (hwgt : ∀ i < m, Num.Valid st.mem (weight+i*wStride) h L ∧
      Num.fixVal st.mem (weight+i*wStride) h L P = wval i) :
    ∃ out cost, Runs w p ω (preparePackedStagedOutputs pack) st .normal out cost ∧
      out.regs 16 = heap+m*L+m*L ∧ out.regs 36 = heap ∧ out.regs 37 = L ∧
      out.regs 38 = heap+m*L ∧ out.regs 39 = L ∧
      (∀ r, r ≠ 16 → r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      ZeroFrom out.mem (heap+m*L+m*L) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (heap+i*L) h L ∧
        Num.fixVal out.mem (heap+i*L) h L P = sval i) ∧
      (∀ i < m, Num.Valid out.mem (heap+m*L+i*L) h L ∧
        Num.fixVal out.mem (heap+m*L+i*L) h L P = wval i) ∧
      cost ≤ 2*((35*L+60)*m+17)+argsSize packedStagedOutputArgs+11 := by
  obtain ⟨mid,cp,hpack,_,hend,hkeep,hzero,hframe,hstretch,hweight,hcp⟩ :=
    packStagedWideOutputs_runs (ω := ω) he hp hh hw hregs hsmall hword hsL hwL
      hsEnd hwEnd hz hroom hs hwgt
  obtain ⟨out,cl,hlayout,hmem,h36,h37,h38,h39,hout,hcl⟩ :=
    installPackedStagedOutputLayout_runs (ω := ω) mid
      ((hkeep 1 (by decide) (by decide)).trans hregs.1)
      ((hkeep 19 (by decide) (by decide)).trans hregs.2.1) hend hroom
  refine ⟨out,cp+cl+1,runs_seq_iff.mpr (Or.inr ⟨mid,cp,cl,hpack,hlayout,rfl⟩),
    (hout 16 (by decide)).trans hend,h36,h37,h38,h39,?_,?_,?_,?_,?_,by omega⟩
  · intro r h16 hrs
    exact (hout r hrs).trans (hkeep r (fun h => hrs (by simp [h])) h16)
  all_goals rw [hmem]
  all_goals assumption

/-- Locate the widened results and prepare their compact publication layout. -/
def publishableWideOutputs (pack : ℕ) : Stmt :=
  .seq installWideStagedOutputLayout (preparePackedStagedOutputs pack)

/-- Rounded stretches and updated weights that fit the caller's format
retain their values through the output-address and packing passes. -/
theorem publishableWideOutputs_runs {w h P pack shift n m L K heap : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {sval wval : ℕ → ℝ} {sBound wBound : ℝ}
    (he : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hL : st.regs 19 = L)
    (hK : st.regs 24 = K) (hheap : st.regs 20 = heap)
    (hnWord : n < 2^w) (hmWord : m < 2^w) (hLWord : L < 2^w)
    (hmPos : 0 < m) (hKPos : 0 < K) (hword : 1 < 2^w) (hLK : L ≤ K) :
    let start := heap+(n-1)*K
    let afterStretch := start+m*edgeStretchSpace K
    let stop := afterStretch+m*narrowWeightSpace K
    st.regs 16 = stop → ZeroFrom st.mem stop → stop+m*L+m*L < 2^w →
    (∀ i < m, Num.Valid st.mem (roundStretchAddr start K i) h K ∧
      Num.fixVal st.mem (roundStretchAddr start K i) h K P = sval i ∧
      0 ≤ sval i ∧ sval i ≤ sBound) →
    (∀ i < m, Num.Valid st.mem (roundWeightAddr afterStretch K i) h K ∧
      Num.fixVal st.mem (roundWeightAddr afterStretch K i) h K P = wval i ∧
      0 ≤ wval i ∧ wval i ≤ wBound) →
    2*(2 : ℝ)^P*sBound < Num.capacity h L →
    2*(2 : ℝ)^P*wBound < Num.capacity h L →
    ∃ out cost, Runs w p ω (publishableWideOutputs pack) st .normal out cost ∧
      out.regs 16 = stop+m*L+m*L ∧ out.regs 36 = stop ∧ out.regs 37 = L ∧
      out.regs 38 = stop+m*L ∧ out.regs 39 = L ∧
      (∀ r, r ≠ 16 → r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      ZeroFrom out.mem (stop+m*L+m*L) ∧ (∀ a < stop, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (stop+i*L) h L ∧
        Num.fixVal out.mem (stop+i*L) h L P = sval i) ∧
      (∀ i < m, Num.Valid out.mem (stop+m*L+i*L) h L ∧
        Num.fixVal out.mem (stop+m*L+i*L) h L P = wval i) ∧
      cost ≤ 2*((35*L+60)*m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro start afterStretch stop hend hz hroom hs hwgt hsFit hwFit
  have hstop : stop < 2^w := by omega
  obtain ⟨mid,cl,hl,hmem,h36,h37,h38,h39,hkeep,hcl⟩ :=
    installWideStagedOutputLayout_runs (ω := ω) st n m K heap hn hm hK hheap
      hnWord hmPos hKPos hword hstop
  have hsK : K ≤ edgeStretchSpace K := by unfold edgeStretchSpace; omega
  have hwK : K ≤ narrowWeightSpace K := by unfold narrowWeightSpace; omega
  have hsLe := Nat.le_mul_of_pos_left (edgeStretchSpace K) hmPos
  have hwLe := Nat.le_mul_of_pos_left (narrowWeightSpace K) hmPos
  have hsmall : ∀ a ∈ [m,L,start+edgeStretchSpace K-K,edgeStretchSpace K,
      afterStretch+narrowWeightSpace K-K,narrowWeightSpace K], a < 2^w := by
    dsimp only [stop,afterStretch] at hstop
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
    dsimp only [afterStretch]
    exact ⟨hmWord,hLWord,by omega,by omega,by omega,by omega⟩
  have hsEnd (i : ℕ) (hi : i < m) :=
    (stagedNumericOutput_blockEnds start m K i hi).1
  have hwEnd (i : ℕ) (hi : i < m) :=
    (stagedNumericOutput_blockEnds start m K i hi).2
  obtain ⟨out,cp,hr,hend',h36',h37',h38',h39',hkeep',hz',hframe,hs',hw',hcp⟩ :=
    preparePackedStagedOutputs_runs (ω := ω) he hp hh hw
      ⟨(hkeep 1 (by decide)).trans hm,(hkeep 19 (by decide)).trans hL,
        (hkeep 16 (by decide)).trans hend,h36,h37,h38,h39⟩
      hsmall hword (hLK.trans hsK) (hLK.trans hwK)
      (fun i hi => by
        rw [← stagedStretchAddr_eq]
        exact ((Nat.add_le_add_left hLK _).trans (hsEnd i hi)).trans (Nat.le_add_right _ _))
      (fun i hi => by
        rw [← stagedWeightAddr_eq]
        exact (Nat.add_le_add_left hLK _).trans (hwEnd i hi))
      (hmem.symm ▸ hz) hroom
      (fun i hi => by
        rw [hmem,← stagedStretchAddr_eq]
        exact stagedWideOutput_prefix_of_capacity hLK (hs i hi).1 (hs i hi).2.1
          (hs i hi).2.2.1 (hs i hi).2.2.2 hsFit)
      (fun i hi => by
        rw [hmem,← stagedWeightAddr_eq]
        exact stagedWideOutput_prefix_of_capacity hLK (hwgt i hi).1 (hwgt i hi).2.1
          (hwgt i hi).2.2.1 (hwgt i hi).2.2.2 hwFit)
  exact ⟨out,cl+cp+1,runs_seq_iff.mpr (Or.inr ⟨mid,cl,cp,hl,hr,rfl⟩),
    hend',h36',h37',h38',h39',fun r h16 hrs => (hkeep' r h16 hrs).trans (hkeep r hrs),
    hz',fun a ha => (hframe a ha).trans (congrFun hmem a),hs',hw',by omega⟩

/-- Read the numeric contract's output as the two compact arrays consumed
by branch publication and the next multiplicative-weights round. -/
theorem publishableWideOutputs_of_numericPost
    {w h Q pack shift : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue n levels dist lengths K heap tails heads P old stride denom j L : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) (args : List ℕ) (mem : ℕ → ℕ)
    (he : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hn : st.regs 0 = n) (hm : st.regs 1 = G.m) (hL : st.regs 19 = L)
    (hK : st.regs 24 = K) (hheap : st.regs 20 = heap)
    (hnWord : n < 2^w) (hmWord : G.m < 2^w) (hLWord : L < 2^w)
    (hmPos : 0 < G.m) (hKPos : 0 < K) (hword : 1 < 2^w) (hLK : L ≤ K)
    (hmEq : H.m = G.m)
    (hpost : (stretchWeightRoundContract w h Q G T H 0 len adj parents edges depths queue n
      levels dist lengths K heap tails heads P old stride denom j scale query).post args mem
      (st.regs 16) st.mem)
    (sBound wBound : ℝ)
    (hs : ∀ i < H.m, let s := query (weights P (scale : ℝ) query j) (edgeName H i)
      0 ≤ s ∧ s ≤ sBound)
    (hwt : ∀ i < H.m, let v := weights P (scale : ℝ) query (j+1) (edgeName H i)
      0 ≤ v ∧ v ≤ wBound)
    (hsFit : 2*(2 : ℝ)^P*sBound < Num.capacity h L)
    (hwFit : 2*(2 : ℝ)^P*wBound < Num.capacity h L) :
    let stop := heap+(n-1)*K+G.m*edgeStretchSpace K+G.m*narrowWeightSpace K
    stop+G.m*L+G.m*L < 2^w →
    ∃ out cost, Runs w p ω (publishableWideOutputs pack) st .normal out cost ∧
      out.regs 16 = stop+G.m*L+G.m*L ∧ out.regs 36 = stop ∧ out.regs 37 = L ∧
      out.regs 38 = stop+G.m*L ∧ out.regs 39 = L ∧
      (∀ r, r ≠ 16 → r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      ZeroFrom out.mem (stop+G.m*L+G.m*L) ∧ (∀ a < stop, out.mem a = st.mem a) ∧
      (∀ i < H.m, Num.Valid out.mem (stop+i*L) h L ∧
        Num.fixVal out.mem (stop+i*L) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
      (∀ i < H.m, Num.Valid out.mem (stop+G.m*L+i*L) h L ∧
        Num.fixVal out.mem (stop+G.m*L+i*L) h L P =
          weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
      cost ≤ 2*((35*L+60)*G.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro stop hroom
  obtain ⟨hend,hzero,_,hblocks,_⟩ := hpost
  rw [hmEq] at hend
  obtain ⟨out,cost,hr,h16,h36,h37,h38,h39,hkeep,hz,hframe,hstretch,hweight,hcost⟩ :=
    publishableWideOutputs_runs (ω := ω) he hp hh hw hn hm hL hK hheap hnWord hmWord
      hLWord hmPos hKPos hword hLK hend (hend ▸ hzero) hroom
      (fun i hi => by
        have hi' : i < H.m := hmEq ▸ hi
        exact ⟨(hblocks i hi').2.1,(hblocks i hi').2.2,hs i hi'⟩)
      (fun i hi => by
        have hi' : i < H.m := hmEq ▸ hi
        exact ⟨(hblocks i hi').1.1,(hblocks i hi').1.2,hwt i hi'⟩)
      hsFit hwFit
  exact ⟨out,cost,hr,h16,h36,h37,h38,h39,hkeep,hz,hframe,
    fun i hi => hstretch i (hmEq ▸ hi),fun i hi => hweight i (hmEq ▸ hi),hcost⟩

end MinCostFlow.LastLevelProgram
