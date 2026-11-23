module

public import MinCostFlow.LastLevelProgram.WeightRoundModel
public import MinCostFlow.LastLevelProgram.NameTreeStretch
public import MinCostFlow.LastLevelProgram.FixedPoint
import WordRAM.Tactic

/-!
# One stretch computation and multiplicative update

The last-level loop of Definition 5.8 (pages 19–20) uses a rounded
stretch vector to update the weights. The stretch result blocks
already have the stride needed by the weight update.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF
open scoped BigOperators

/-- The first sixteen arguments match the tree stretch call. Append
the old weight base, weight stride, denominator address and stretch stride. -/
def stretchWeightRoundBody (stretch weights : ℕ) : Stmt :=
  .call 20 stretch [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15] ;;
  .assign 21 (.bin .sub
    (.bin .add (.bin .add (.reg 11) (.bin .mul (.bin .sub (.reg 6) (.const 1)) (.reg 10)))
      (.reg 19)) (.reg 10)) ;;
  .call 22 weights [.reg 16,.reg 21,.reg 18,.reg 10,.reg 15,.reg 20,.reg 17,.const 0,.reg 19] ;;
  .ret (.reg 22)


/-- One combined call produces exactly the next model weights and
retains the rounded stretches from this round. -/
theorem stretchWeightRound_runs {w h Q stretch update : ℕ} {p : Program} {G T H : MGraph}
    {r : ℕ} (len : ℕ → ℤ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (ht : MeetsContract w p stretch (treeStretchRoundContract w h Q G T r len))
    (hu : MeetsContract w p update (weightRoundContract w h))
    (pos adj base edges db queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hwords : ∀ a ∈ [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
      old,stride,denom,edgeStretchSpace L], a < 2^w)
    (hpre : (treeStretchRoundContract w h Q G T r len).pre
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem)
    (hm : G.m = H.m) (hw : 1 < 2^w) (hscale : 0 < scale)
    (hold : ∀ i < H.m, adj ≤ old+i*stride ∧ old+i*stride+L ≤ dist)
    (hd : adj ≤ denom ∧ denom+L ≤ dist) (hdist : dist ≤ heap)
    (hden : Valid mem denom h L ∧ intVal mem denom h L = scale*(2 : ℤ)^P)
    (hRoom : heap+(n-1)*L+G.m*edgeStretchSpace L+H.m*narrowWeightSpace L < 2^w)
    (hFirst : heap+(n-1)*L+edgeStretchSpace L < 2^w)
    (hwidth : 2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity h L)
    (hone : ∀ e ∈ H.E, 1 ≤ weights P (scale : ℝ) query (j+1) e)
    (hsum : ∑ e ∈ H.E, weights P (scale : ℝ) query (j+1) e ≤ 2*H.m)
    (hweights : ∀ i < H.m, Valid mem (old+i*stride) h L ∧
      fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i))
    (hstretches : ∀ i < H.m,
      roundStretch P (treeStretch G T (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
        query (weights P (scale : ℝ) query j) (edgeName H i)) :
    let start := heap+(n-1)*L
    let afterStretch := start+G.m*edgeStretchSpace L
    ∃ o out c, Runs w p ω (stretchWeightRoundBody stretch update)
      (startState [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
        old,stride,denom,edgeStretchSpace L] mem pos) o out c ∧
      (o.value = afterStretch+H.m*narrowWeightSpace L ∧ ZeroFrom out.mem o.value ∧
        (∀ a, adj ≤ a → a < dist → out.mem a = mem a) ∧
        (∀ i < H.m,
          (Valid out.mem (roundWeightAddr afterStretch L i) h L ∧
            fixVal out.mem (roundWeightAddr afterStretch L i) h L P =
              weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
          (Valid out.mem (roundStretchAddr start L i) h L ∧
            fixVal out.mem (roundStretchAddr start L i) h L P =
              query (weights P (scale : ℝ) query j) (edgeName H i))) ∧
        ∀ a < base, out.mem a = mem a) ∧
      c ≤ (treeStretchRoundContract w h Q G T r len).cost
        [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem +
        (narrowWeightCost L+30)*H.m+60 := by
  intro start afterStretch
  let first := roundStretchAddr start L 0
  have hS : L ≤ edgeStretchSpace L := by unfold edgeStretchSpace stretchFromLengthSpace; omega
  have hFirst' : start+edgeStretchSpace L < 2^w := hFirst
  have hStart : start < 2^w := by omega
  have hFirstW : first < 2^w := by
    have he : first = start+edgeStretchSpace L-L := by simp [first,roundStretchAddr]
    omega
  have hprod : (n-1)*L < 2^w := by dsimp [start] at hStart; omega
  have hroom : afterStretch+H.m*narrowWeightSpace L < 2^w := hRoom
  have hAfterW : afterStretch < 2^w := by omega
  -- Argument words used by the two linked calls.
  have hw0 := hwords adj (by simp)
  have hw1 := hwords base (by simp)
  have hw2 := hwords edges (by simp)
  have hw3 := hwords db (by simp)
  have hw4 := hwords queue (by simp)
  have hw5 := hwords r (by simp)
  have hw6 := hwords n (by simp)
  have hw7 := hwords levels (by simp)
  have hw8 := hwords dist (by simp)
  have hw9 := hwords lengths (by simp)
  have hw10 := hwords L (by simp)
  have hw11 := hwords heap (by simp)
  have hw12 := hwords tails (by simp)
  have hw13 := hwords heads (by simp)
  have hw14 := hwords P (by simp)
  have hw15 := hwords G.m (by simp)
  have hw16 := hwords old (by simp)
  have hw17 := hwords stride (by simp)
  have hw18 := hwords denom (by simp)
  have hwS := hwords (edgeStretchSpace L) (by simp)
  have hbHeap : base ≤ heap := by
    obtain ⟨a,b,e,d,q,k,lv,di,le,lim,hp,ta,he,pr,B,heq,_,_,_,_,hb,_⟩ := hpre
    have hb' : base = b := congrArg (fun xs : List ℕ => xs.getD 1 0) heq
    have hp' : heap = hp := congrArg (fun xs : List ℕ => xs.getD 11 0) heq
    rw [hb',hp']
    exact (Nat.le_add_right _ _).trans hb
  have hnsub : n-1 < 2^w := by omega
  apply runs_start_le
  unfold stretchWeightRoundBody
  refine runs_seq_call_le ht (vs := [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,
    tails,heads,P,G.m]) (by eval_expr) ?_ hpre ?_
  · wram_words
  · intro cursor mid pos' hs
    have hcur : cursor = afterStretch := hs.1
    subst cursor
    obtain ⟨hnext,hden',hvals⟩ := weightRound_pre_of_treeStretch len mem mid adj base edges db queue
      n levels dist lengths L heap tails heads P afterStretch old stride denom j scale query
      hs hm hw hscale hold hd hdist hden hroom hwidth hone hsum hweights hstretches
    refine runs_seq_assign_le (v := first) ?_ ?_
    · have he : start+edgeStretchSpace L-L = first := by simp [first,roundStretchAddr]
      rw [← he]
      change _ = some (heap+(n-1)*L+edgeStretchSpace L-L)
      eval_expr
    · have hweightArgs := hnext
      rw [← hm] at hweightArgs
      refine runs_seq_call_le hu (vs := [old,first,denom,L,G.m,afterStretch,stride,0,edgeStretchSpace L])
        (by eval_expr) ?_ hweightArgs ?_
      · wram_words
      · intro ret out _ hf
        have hf' : (weightRoundContract w h).post
            [old,first,denom,L,H.m,afterStretch,stride,0,edgeStretchSpace L] mid ret out := by
          rwa [← hm]
        obtain ⟨hret,hz,hframe,hout⟩ := weightRound_post_model mid out old first denom L
          afterStretch stride (edgeStretchSpace L) P j ret scale query hscale hden'
          (fun i hi => (hvals i hi).1) (fun i hi => (hvals i hi).2) hf'
        have hretW : ret < 2^w := hret ▸ hroom
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · refine ⟨hret,hz,?_,?_,?_⟩
          · intro a ha hb
            have hl : a < afterStretch := by dsimp [afterStretch,start]; omega
            exact (hframe a hl).trans (hs.2.2.1 a ha hb)
          · intro i hi
            have hi' : i < G.m := by rwa [hm]
            have hb : roundStretchAddr start L i+L ≤ afterStretch :=
              roundStretchAddr_end_le start L G.m i hi'
            have hsame (b : ℕ) (hb' : b < L) :
                out (roundStretchAddr start L i+b) = mid (roundStretchAddr start L i+b) :=
              hframe _ (by omega)
            have hst := hs.2.2.2.1 i hi'
            refine ⟨hout i hi,fun b hb' => (hsame b hb').trans_lt (hst.1 b hb'),?_⟩
            unfold fixVal
            rw [intVal_congr hsame]
            exact hst.2.trans (hstretches i hi)
          · intro a ha
            have hl : a < afterStretch := by dsimp [afterStretch,start]; omega
            exact (hframe a hl).trans (hs.2.2.2.2 a ha)
        · simp [weightRoundContract,argsSize,Expr.size,hm,startState]
          omega

/-- When the compact tree is the oracle's returned tree, its rounded
edge stretches are the fixed-point query's values at the named edges. -/
theorem compactRoundStretch_eq_query {H T : MGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (P : ℕ)
    (hH : H.IsValid)
    (hT : LSF.IsLSST (indexedGraph H).toMGraph (safeLen H ℓ ∘ edgeName H) (v ∘ edgeName H) gamma T)
    (horacle : oracle H (safeLen H ℓ) v = restoreTreeNames H T)
    (i : ℕ) (hi : i < H.m) :
    roundStretch P (treeStretch (indexedGraph H).toMGraph T (safeLen H ℓ ∘ edgeName H) i) =
      stretchQuery oracle H ℓ P v (edgeName H i) := by
  rw [stretchQuery,horacle,restoreTreeNames_treeStretch hH hT i hi]

/-- Encoded compact lengths may be decoded before identifying the
stretch round with the named fixed-point model. -/
theorem encodedRoundStretch_eq_query {H T : MGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (Q P : ℕ) (len : ℕ → ℤ)
    (hH : H.IsValid)
    (hT : LSF.IsLSST (indexedGraph H).toMGraph (safeLen H ℓ ∘ edgeName H) (v ∘ edgeName H) gamma T)
    (horacle : oracle H (safeLen H ℓ) v = restoreTreeNames H T)
    (hLen : ∀ i, (len i : ℝ)/(2 : ℝ)^Q = (safeLen H ℓ ∘ edgeName H) i)
    (i : ℕ) (hi : i < H.m) :
    roundStretch P (treeStretch (indexedGraph H).toMGraph T (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
      stretchQuery oracle H ℓ P v (edgeName H i) := by
  rw [funext hLen]
  exact compactRoundStretch_eq_query oracle P hH hT horacle i hi
/-- Callable stretch and weight-update pass for one fixed-point round. -/
def stretchWeightRoundContract (w h Q : ℕ) (G T H : MGraph) (r : ℕ) (len : ℕ → ℤ)
    (adj base edges db queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) : Contract where
  pre args mem :=
    args = [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
      old,stride,denom,edgeStretchSpace L] ∧
    (treeStretchRoundContract w h Q G T r len).pre
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem ∧
    (∀ i < H.m, adj ≤ old+i*stride ∧ old+i*stride+L ≤ dist) ∧
    (adj ≤ denom ∧ denom+L ≤ dist) ∧
    (Valid mem denom h L ∧ intVal mem denom h L = scale*(2 : ℤ)^P) ∧
    ∀ i < H.m, Valid mem (old+i*stride) h L ∧
      fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i)
  post _ mem ret out :=
    let start := heap+(n-1)*L
    let afterStretch := start+G.m*edgeStretchSpace L
    ret = afterStretch+H.m*narrowWeightSpace L ∧ ZeroFrom out ret ∧
    (∀ a, adj ≤ a → a < dist → out a = mem a) ∧
    (∀ i < H.m,
      (Valid out (roundWeightAddr afterStretch L i) h L ∧
        fixVal out (roundWeightAddr afterStretch L i) h L P =
          weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
      (Valid out (roundStretchAddr start L i) h L ∧
        fixVal out (roundStretchAddr start L i) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i))) ∧
    ∀ a < base, out a = mem a
  cost _ mem :=
    (treeStretchRoundContract w h Q G T r len).cost
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem +
      (narrowWeightCost L+30)*H.m+60

/-- Install the combined pass as an ordinary machine procedure. -/
theorem stretchWeightRound_meetsContract {w h Q entry stretch update : ℕ}
    {p : Program} {G T H : MGraph} {r : ℕ}
    (len : ℕ → ℤ) (hp : p.procs[entry]? = some (stretchWeightRoundBody stretch update))
    (ht : MeetsContract w p stretch (treeStretchRoundContract w h Q G T r len))
    (hu : MeetsContract w p update (weightRoundContract w h))
    (adj base edges db queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hm : G.m = H.m) (hw : 1 < 2^w) (hscale : 0 < scale) (hdist : dist ≤ heap)
    (hRoom : heap+(n-1)*L+G.m*edgeStretchSpace L+H.m*narrowWeightSpace L < 2^w)
    (hFirst : heap+(n-1)*L+edgeStretchSpace L < 2^w)
    (hwidth : 2*(2 : ℝ)^P*(2*(H.m : ℝ)) < capacity h L)
    (hone : ∀ e ∈ H.E, 1 ≤ weights P (scale : ℝ) query (j+1) e)
    (hsum : ∑ e ∈ H.E, weights P (scale : ℝ) query (j+1) e ≤ 2*H.m)
    (hstretches : ∀ i < H.m,
      roundStretch P (treeStretch G T (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
        query (weights P (scale : ℝ) query j) (edgeName H i)) :
    MeetsContract w p entry
      (stretchWeightRoundContract w h Q G T H r len adj base edges db queue n levels dist
        lengths L heap tails heads P old stride denom j scale query) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, htree, hold, hd, hden, hweights⟩ := hpre
  exact stretchWeightRound_runs len mem ω ht hu pos adj base edges db queue n levels dist lengths
    L heap tails heads P old stride denom j scale query hwords htree hm hw hscale hold hd hdist
    hden hRoom hFirst hwidth hone hsum hweights hstretches

end MinCostFlow.LastLevelProgram
