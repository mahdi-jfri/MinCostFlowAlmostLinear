module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCParts

/-!
# The post of the first step without the cost: the goal and its parts (`AssemblyFirstStepNCDefs`)

The field `hPost` of `AsmFsPieces` comes from two parts (`asmFirstStep_hPost_of`): the cost
goal `AsmFsCostGoal` and the post without the cost. This file states the second one as a
proposition, `AsmFsNCGoal`, and three smaller goals from which `AssemblyFirstStepNC` proves it:

* `AsmFsSideGoal`: the bundle side after the step (`asmFsSideAfter`) holds the new state of the
  model in the final memory;
* `AsmFsEmbGoal`: the embedding table after Phase 4 has every core edge of the new state in its
  domain, with the embedding of the new state on it;
* `AsmFsSpaceGoal`: the end of Phase 4 is at most `h` plus the space of the step.

Each goal is stated for every call whose premises hold (`AsmFsPre`) and every state after Phase 4
with its witnesses (`AsmFsQ₄At`). The final memory is the memory after Phase 4 with the place of
the split lists at `h + 1` (what the driver writes).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The post of the first step without the cost**, the premise `hNC` of
`asmFirstStep_hPost_of`: for every call and every state after Phase 4, and the tour state
`xTour` of Phase 4 at the caps of the branch, `AsmFsPostNCAt` holds for the final memory, the
bundle side `asmFsSideAfter` and some embedding table, abstract tour, split lists and `T₀`. -/
def AsmFsNCGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (ysMul : ℕ) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    ∀ xTour : (TRc A.x.vCap A.x.eCap).τ, HEq xTour tx' →
    ∃ (yEmb : EmbConc) (sTour : OutTourAbs) (Ys' : List (List End)) (T₀' : List ℕ),
      AsmFsPostNCAt TRc scProgB5 impl P L capExp limbMul w Ψ ysMul space A o₄.value
        (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) yEmb sTour xTour
        (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x')
        Ys' T₀'

/-- **The bundle side after the step** (conjunct 6 of the post): `asmFsSideAfter` holds the new
state of the model `⟨info.state, ord', vCap, eCap⟩` at the handle of the side, in the final
memory. -/
def AsmFsSideGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    (asmBrSideRep scProgB5 impl w depth L capExp limbMul Ψ).rep A.x.restH
      ⟨(stepBundleTree (fun _ => canonicalSparsify impl) A.tr A.U A.ord
        (applyOrdEdits A.ord A.ed)).state, applyOrdEdits A.ord A.ed, A.x.vCap, A.x.eCap⟩
      (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x')
      (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂))

/-- **The embedding model** (conjuncts 2 and 3 of the post): the view of the embedding table
after Phase 4 has every edge of the new core graph in its domain, and there it is the embedding
of the new state. -/
def AsmFsEmbGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    let info := stepBundleTree (fun _ => canonicalSparsify impl) A.tr A.U A.ord
      (applyOrdEdits A.ord A.ed)
    (coreGraph info.state.cs.G info.state.cs.lsf).E ⊆ yE.view.dom ∧
    ∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E, yE.view.emb e = info.state.emb e

/-- **The space of the step** (conjunct 25 of the post): the end of Phase 4 is at most `h` plus
the space of the step at the size of the input. -/
def AsmFsSpaceGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    o₄.value ≤ A.h + space (A.M + A.N + A.k + A.x.vCap + A.x.eCap + L + depth + A.words +
      A.editWords)

end

end MinCostFlow.SparseCore.Program
