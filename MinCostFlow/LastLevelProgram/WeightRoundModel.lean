module

public import MinCostFlow.LastLevelProgram.WeightRound
public import MinCostFlow.LastLevelProgram.QueryFit
public import MinCostFlow.LastLevelProgram.TreeStretchRound

/-!
# The model invariant across a machine weight pass

The rounded potential bounds the next weight vector before the
machine writes it back into storage. This supplies the fit premise
for the pass and identifies its output with the next model round.
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM
open scoped BigOperators

/-- A full compact pass advances the model round. Its output fit follows
from the model's next-round invariant and the storage width. -/
theorem weightRound_model_triple {w h update : ℕ} {p : Program}
    (hu : MeetsContract w p update (narrowWeightContract w h))
    (mem : ℕ → ℕ) (pos old stretches denom L heap stride stretchStride : ℕ) (H : MGraph)
    (P j : ℕ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hw : 1 < 2^w) (hm : H.m < 2^w)
    (ha : ∀ i < H.m, old+i*stride+L ≤ heap) (hb : ∀ i < H.m, stretches+i*stretchStride+L ≤ heap)
    (hd : denom + L ≤ heap) (hvd : Valid mem denom h L)
    (hscale : 0 < scale) (hdenom : intVal mem denom h L = scale * (2 : ℤ)^P)
    (hz : ZeroFrom mem heap) (hroom : heap + H.m * narrowWeightSpace L < 2^w)
    (hwidth : 2 * (2 : ℝ)^P * (2 * (H.m : ℝ)) < capacity h L)
    (hone : ∀ e ∈ H.E, 1 ≤ weights P (scale : ℝ) query (j + 1) e)
    (hsum : ∑ e ∈ H.E, weights P (scale : ℝ) query (j + 1) e ≤ 2 * H.m)
    (hinputs : ∀ i < H.m,
      (Valid mem (old + i * stride) h L ∧
        fixVal mem (old + i * stride) h L P = weights P (scale : ℝ) query j (edgeName H i)) ∧
      (Valid mem (stretches + i * stretchStride) h L ∧
        fixVal mem (stretches + i * stretchStride) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i))) :
    Triple w p (fun st => st = startState [old,stretches,denom,L,H.m,heap,stride,0,stretchStride] mem pos)
      (weightRoundLoop update)
      (normalPost fun st =>
        st.regs 5 = heap + H.m * narrowWeightSpace L ∧ ZeroFrom st.mem (st.regs 5) ∧
        (∀ x < heap, st.mem x = mem x) ∧
        ∀ i < H.m, Valid st.mem (roundWeightAddr heap L i) h L ∧
          fixVal st.mem (roundWeightAddr heap L i) h L P =
            weights P (scale : ℝ) query (j + 1) (edgeName H i))
      (fun _ => (narrowWeightCost L + 30) * H.m + 7) := by
  have hpos : 0 < intVal mem denom h L := by
    rw [hdenom]
    exact mul_pos hscale (pow_pos (by decide) _)
  have hvalue (i : ℕ) (hi : i < H.m) :
      (roundWeightValue mem (old + i * stride) (stretches + i * stretchStride) denom h L : ℝ) /
        (2 : ℝ)^P = weights P (scale : ℝ) query (j + 1) (edgeName H i) := by
    obtain ⟨⟨_, ha'⟩, ⟨_, hb'⟩⟩ := hinputs i hi
    rw [roundWeightValue_decoded hscale hdenom, ha', hb']
    rfl
  have hfits (i : ℕ) (hi : i < H.m) :
      Fits h L (roundWeightValue mem (old + i * stride) (stretches + i * stretchStride) denom h L) := by
    have he := edgeName_mem (G := H) hi
    have hbound := (Finset.single_le_sum (fun e he => zero_le_one.trans (hone e he)) he).trans hsum
    have hgrid : ∃ a : ℤ, weights P (scale : ℝ) query (j + 1) (edgeName H i) =
        (a : ℝ) / (2 : ℝ)^P := ⟨_, (hvalue i hi).symm⟩
    have h := (queryNumerator_fits (zero_lt_one.trans_le (hone _ he)) hbound hwidth hgrid).2
    rwa [← hvalue i hi, queryNumerator_grid] at h
  refine (weightRoundLoop_triple hu mem pos old stretches denom L H.m heap stride stretchStride
    hw hm ha hb hd hvd hpos hz hroom
    (fun i hi => ⟨(hinputs i hi).1.1, (hinputs i hi).2.1, hfits i hi⟩)).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st hpost
  cases o with
  | returned _ => exact hpost
  | normal =>
    obtain ⟨hcur,hzero,hframe,hweights⟩ := hpost
    refine ⟨hcur,hzero,hframe,fun i hi => ⟨(hweights i hi).1, ?_⟩⟩
    rw [fixVal, (hweights i hi).2]
    exact hvalue i hi


/-- The stretch round preserves the old weights and denominator and
supplies the strided stretches for the next weight update. The model's
next-round weight bound discharges the signed fit checks. -/
theorem weightRound_pre_of_treeStretch {w h Q : ℕ} {G T H : MGraph} {r : ℕ}
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (adj base edges db queue n levels dist lengths L heap tails heads P ret old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hpost : (treeStretchRoundContract w h Q G T r len).post
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem ret out)
    (hm : G.m = H.m) (hw : 1 < 2^w) (hscale : 0 < scale)
    (hold : ∀ i < H.m, adj ≤ old+i*stride ∧ old+i*stride+L ≤ dist)
    (hd : adj ≤ denom ∧ denom+L ≤ dist) (hdist : dist ≤ heap)
    (hden : Valid mem denom h L ∧ intVal mem denom h L = scale*(2 : ℤ)^P)
    (hroom : ret+H.m*narrowWeightSpace L < 2^w)
    (hwidth : 2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity h L)
    (hone : ∀ e ∈ H.E, 1 ≤ weights P (scale : ℝ) query (j+1) e)
    (hsum : ∑ e ∈ H.E, weights P (scale : ℝ) query (j+1) e ≤ 2*H.m)
    (hweights : ∀ i < H.m, Valid mem (old+i*stride) h L ∧
      fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i))
    (hstretches : ∀ i < H.m,
      roundStretch P (treeStretch G T (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
        query (weights P (scale : ℝ) query j) (edgeName H i)) :
    let first := roundStretchAddr (heap+(n-1)*L) L 0
    (weightRoundContract w h).pre [old,first,denom,L,H.m,ret,stride,0,edgeStretchSpace L] out ∧
    intVal out denom h L = scale*(2 : ℤ)^P ∧
    ∀ i < H.m,
      fixVal out (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i) ∧
      fixVal out (first+i*edgeStretchSpace L) h L P =
        query (weights P (scale : ℝ) query j) (edgeName H i) := by
  intro first
  let start := heap+(n-1)*L
  obtain ⟨hret,hz,hframe,hstretch,_⟩ := hpost
  change ret = start+G.m*edgeStretchSpace L at hret
  change ∀ a, adj ≤ a → a < dist → out a = mem a at hframe
  have hdret : dist ≤ ret := by dsimp [start] at hret; omega
  have hc (a : ℕ) (ha : adj ≤ a) (hb : a+L ≤ dist) :
      (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
    have he (i : ℕ) (hi : i < L) := hframe (a+i) (by omega) (by omega)
    exact ⟨fun hv i hi => (he i hi).trans_lt (hv i hi),intVal_congr he⟩
  obtain ⟨hdvalid,hdeq⟩ := hc denom hd.1 hd.2
  have hde : intVal out denom h L = scale*(2 : ℤ)^P := hdeq.trans hden.2
  have hpos : 0 < intVal out denom h L := hde ▸ mul_pos hscale (pow_pos (by decide) _)
  have haddresses (i : ℕ) : first+i*edgeStretchSpace L = roundStretchAddr start L i :=
    roundStretchAddr_stride start L i
  have hDecoded (i : ℕ) (hi : i < H.m) :
      fixVal out (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i) ∧
      fixVal out (first+i*edgeStretchSpace L) h L P =
        query (weights P (scale : ℝ) query j) (edgeName H i) := by
    have hi' : i < G.m := by rwa [hm]
    obtain ⟨_,hoe⟩ := hc (old+i*stride) (hold i hi).1 (hold i hi).2
    constructor
    · unfold fixVal
      rw [hoe]
      exact (hweights i hi).2
    · rw [haddresses i]
      exact (hstretch i hi').2.trans (hstretches i hi)
  refine ⟨⟨old,first,denom,L,H.m,ret,stride,edgeStretchSpace L,rfl,hw,hd.2.trans hdret,
    hdvalid hden.1,hpos,hz,hroom,?_⟩,hde,hDecoded⟩
  intro i hi
  have hi' : i < G.m := by rwa [hm]
  have hb : first+i*edgeStretchSpace L+L ≤ ret := by
    rw [haddresses i,hret]
    exact roundStretchAddr_end_le start L G.m i hi'
  obtain ⟨hvalid,_⟩ := hstretch i hi'
  obtain ⟨ho,hs⟩ := hDecoded i hi
  have how := (hc (old+i*stride) (hold i hi).1 (hold i hi).2).1
  refine ⟨(hold i hi).2.trans hdret,hb,how (hweights i hi).1,by rwa [haddresses i],?_⟩
  have he := edgeName_mem (G := H) hi
  have hbound := (Finset.single_le_sum (fun e he => zero_le_one.trans (hone e he)) he).trans hsum
  have hval' : (roundWeightValue out (old+i*stride) (first+i*edgeStretchSpace L) denom h L : ℝ) /
      (2 : ℝ)^P = weights P (scale : ℝ) query (j+1) (edgeName H i) := by
    rw [roundWeightValue_decoded hscale hde,ho,hs]
    rfl
  have hgrid : ∃ a : ℤ, weights P (scale : ℝ) query (j+1) (edgeName H i) =
      (a : ℝ) / (2 : ℝ)^P := ⟨_,hval'.symm⟩
  have hf := (queryNumerator_fits (zero_lt_one.trans_le (hone _ he)) hbound hwidth hgrid).2
  rwa [← hval',queryNumerator_grid] at hf

/-- Decode the callable weight update at the same fixed-point scale.
The old weights and stretches identify its output with the next
multiplicative-weights vector. -/
theorem weightRound_post_model {w h : ℕ} {H : MGraph} (mem out : ℕ → ℕ)
    (old stretches denom L heap stride stretchStride P j ret : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hscale : 0 < scale) (hdenom : intVal mem denom h L = scale*(2 : ℤ)^P)
    (hold : ∀ i < H.m, fixVal mem (old+i*stride) h L P =
      weights P (scale : ℝ) query j (edgeName H i))
    (hst : ∀ i < H.m, fixVal mem (stretches+i*stretchStride) h L P =
      query (weights P (scale : ℝ) query j) (edgeName H i))
    (hpost : (weightRoundContract w h).post
      [old,stretches,denom,L,H.m,heap,stride,0,stretchStride] mem ret out) :
    ret = heap+H.m*narrowWeightSpace L ∧ ZeroFrom out ret ∧
    (∀ a < heap, out a = mem a) ∧
    ∀ i < H.m, Valid out (roundWeightAddr heap L i) h L ∧
      fixVal out (roundWeightAddr heap L i) h L P =
        weights P (scale : ℝ) query (j+1) (edgeName H i) := by
  obtain ⟨hret,hz,hframe,hvals⟩ := hpost
  refine ⟨hret,hz,hframe,?_⟩
  intro i hi
  obtain ⟨hv,hnum⟩ := hvals i hi
  change intVal out (roundWeightAddr heap L i) h L =
    roundWeightValue mem (old+i*stride) (stretches+i*stretchStride) denom h L at hnum
  refine ⟨hv,?_⟩
  rw [fixVal,hnum,roundWeightValue_decoded hscale hdenom,hold i hi,hst i hi]
  rfl
end MinCostFlow.LastLevelProgram
