module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuild
public import MinCostFlow.SparseCore.Program.AssemblyBranchInitBound
public import MinCostFlow.SparseCore.Program.AssemblyFirstCharge
public import MinCostFlow.SparseCore.CompLSFBridge

/-!
# The first phase of the init of a branch (`AssemblyFirstInit`)

The program `asmFirstInitStmt` (`AssemblyFirstInitBuild.lean`) calls the build of the branch and
then exports `G` and the output graph `S₀`. This file proves that it meets the interface
`AsmBrCoreInitAt` of the first phase, given the build (`AsmFirstInitBuildAt`) and scfirst's export
procedure `asmFirstExportDynGraphStmt` (`asmBrCoreInitAt_of_build`).

The two exports cost little and need little space:
* the export of a graph `G` with `n` vertices and `m` edges takes `4 + n + 3 m` cells and at most
  `200 (n + m + 1)` steps (`asmFirstExportDynGraph_runs`);
* the output graph `S₀` has at most the vertices and the edges of `G` (`scur_size_le_of_facts`);
* the machine cost of the model is at least `3 m + 2` (`initMachCost_ge`), and `n ≤ m + 1`.
So the multiplier grows by `500`, and the space by `10 (x + 2)` (`asmFirstInitSpace`).

The exports write only cells at or after the end of the build, and the two stores write only the
two spare words of the record. The parts of the branch lie in the cells of the build and away from
the record, so they keep their memory form and their potentials (the parts are local).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The multiplier of the first phase, from the multiplier `bm` of the build: `500` more for the
two exports and the steps of the program. -/
def asmFirstInitMul (bm : ℕ) : ℕ := bm + 500

/-- The space of the first phase: the space `s` of the build, plus `10 (x + 2)` for the two
exports. -/
def asmFirstInitSpace (s : PolyBound) : PolyBound := ⟨s.coeff + 10, max s.deg 1⟩

/-- The space of the first phase is at least the space of the build plus `10 (x + 2)`. -/
theorem asmFirstInitSpace_ge (s : PolyBound) (x : ℕ) :
    s.eval x + 10 * (x + 2) ≤ (asmFirstInitSpace s).eval x := by
  show s.coeff * (x + 2) ^ s.deg + 10 * (x + 2) ≤ (s.coeff + 10) * (x + 2) ^ max s.deg 1
  have h1 : (x + 2) ^ s.deg ≤ (x + 2) ^ max s.deg 1 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : x + 2 ≤ (x + 2) ^ max s.deg 1 := by
    calc x + 2 = (x + 2) ^ 1 := (pow_one _).symm
      _ ≤ (x + 2) ^ max s.deg 1 := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h3 := Nat.mul_le_mul_left s.coeff h1
  have h4 := Nat.mul_le_mul_left 10 h2
  rw [Nat.add_mul]
  omega

/-- **The output graph is no larger than the graph**, on the model: its vertices are the roots of
the forest, which are vertices of the graph, and its edges are edges of the graph. -/
theorem scur_size_le_of_facts {depth : ℕ} {impl : SparsifyImpl} {vCap eCap : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} (hF : AsmBrModelFacts impl vCap eCap tr ord) :
    tr.S_cur.n ≤ tr.cs.G.n ∧ tr.S_cur.m ≤ tr.cs.G.m := by
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, hScur, -⟩ := hF
  have hRS := compLSF_RF_isRSF hI
  refine ⟨?_, ?_⟩
  · unfold MGraph.n
    rw [hScur.2.1]
    exact Finset.card_le_card hRS.2.2.1
  · exact Finset.card_le_card fun e he => (Finset.mem_sdiff.mp (hScur.2.2.2.1.2.1 he)).1

/-- **The first phase of the init of a branch meets its interface.** Given the build `B`, the
locality of the tour family and of the bundle tables, the program `asmFirstInitStmt fB fExp` at
`f` and scfirst's export procedure at `fExp`, the procedure `f` meets `AsmBrCoreInitAt` with
multiplier `asmFirstInitMul B.mul` and space `asmFirstInitSpace B.space`. -/
noncomputable def asmBrCoreInitAt_of_build {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit} {impl : SparsifyImpl}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fB fExp f : ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (B : AsmFirstInitBuildAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p fB)
    (hpf : p.procs[f]? = some (asmFirstInitStmt fB fExp))
    (hpE : p.procs[fExp]? = some asmFirstExportDynGraphStmt) :
    AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p f where
  mul := asmFirstInitMul B.mul
  space := asmFirstInitSpace B.space
  runs := by
    intro cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf mem
      pos ω X tr₀ hk hj hGv hGne hM hN hnm hPL hcap hword hCF hcfs hlen hdg hgraph hord hordh hcw hrot
      hexp hexph hcfft hargs hz hsp hF
    have hsp' : h + (asmFirstInitSpace B.space).eval (M + N + k + vCap + eCap + L + depth) <
        2 ^ w := hsp
    have hsp2 := asmFirstInitSpace_ge B.space (M + N + k + vCap + eCap + L + depth)
    have hspB : h + B.space.eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w := by omega
    obtain ⟨bodyB, hfB, oB, stB, cB, x, hrunB, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hxv, hxe,
        hxt, hxl, hemb, hdom, hembEq, hout, htour, hmarks, hX, hv5, he5, hslot, hin, hdisj,
        hsize, hoB, hzB, hlowB, hcB⟩ :=
      B.runs cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf
        mem pos ω hk hj hGv hGne hM hN hnm hPL hcap hword hCF hcfs hlen hdg hgraph hord hordh hcw hrot
        hexp hexph hcfft hargs hz hspB hF
    have hS := scur_size_le_of_facts hF
    have hSn : tr₀.S_cur.n ≤ G.n := hS.1
    have hSm : tr₀.S_cur.m ≤ G.m := hS.2
    have hw16 : 16 ≤ 2 ^ w := by omega
    -- the first export: `G` at the end of the build
    have hdgB : DynGraphAt stB.mem graph vCap eCap G :=
      hdg.of_agree fun a _ ha2 => hlowB a (by omega)
    obtain ⟨oE, stE, cE, hrunE, hoE, hexpG, hzE, hlowE, -, hcE⟩ :=
      asmFirstExportDynGraph_runs (p := p) (ω := ω) (pos := stB.pos) hw16 hdgB (by omega) hzB
        (by omega)
    -- the output graph lies in the cells of the build
    have hout' := hout
    obtain ⟨hO1, -, hO3⟩ := hout
    rw [hxv, hxe] at hO3
    have hfoot3 : ∀ a, (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a → h ≤ a ∧ a < oB.value :=
      hin 3 (by decide) (by decide)
    have hOh := hfoot3 x.outH (Or.inl rfl)
    have hgOut : x.gOut + dynGraphSize vCap eCap ≤ oB.value := by
      have := hfoot3 (x.gOut + dynGraphSize x.vCap x.eCap - 1)
        (Or.inr ⟨by unfold dynGraphSize; omega, by unfold dynGraphSize; omega⟩)
      rw [hxv, hxe] at this
      unfold dynGraphSize at this ⊢
      omega
    have haddr : stE.mem (stE.mem (h + ASM_BR_OUT)) = x.gOut := by
      have e1 : stE.mem (h + ASM_BR_OUT) = x.outH := by
        rw [hlowE _ (by simp only [ASM_BR_OUT, ASM_BR_SIZE] at *; omega), hw2]
      rw [e1, hlowE _ hOh.2, hO1]
    -- the second export: `S₀` at the end of the first export
    have hdgE : DynGraphAt stE.mem x.gOut vCap eCap tr₀.S_cur :=
      hO3.of_agree fun a _ ha2 => hlowE a (by omega)
    obtain ⟨oF, stF, cF, hrunF, hoF, hexpS, hzF, hlowF, -, hcF⟩ :=
      asmFirstExportDynGraph_runs (p := p) (ω := ω) (pos := stE.pos) hw16 hdgE (by omega) hzE
        (by omega)
    -- the run of the program
    obtain ⟨st', c, hrun, hmem', hc⟩ :=
      asmFirstInitStmt_runs (hh := by omega) (hfB := hfB) (hfE := hpE) (hrunB := hrunB)
        (hrunE := hrunE) (hrunF := by rw [haddr]; exact hrunF)
    have hGx : h + ASM_BR_GEXP < h + ASM_BR_SIZE := by simp only [ASM_BR_GEXP, ASM_BR_SIZE]; omega
    have hSx : h + ASM_BR_SEXP < h + ASM_BR_SIZE := by simp only [ASM_BR_SEXP, ASM_BR_SIZE]; omega
    have hGS : h + ASM_BR_GEXP ≠ h + ASM_BR_SEXP := by simp only [ASM_BR_GEXP, ASM_BR_SEXP]; omega
    have hm_other : ∀ a, a ≠ h + ASM_BR_GEXP → a ≠ h + ASM_BR_SEXP → st'.mem a = stF.mem a := by
      intro a h1 h2
      rw [hmem', Function.update_of_ne h2, Function.update_of_ne h1]
    have hmG : st'.mem (h + ASM_BR_GEXP) = oB.value := by
      rw [hmem', Function.update_of_ne hGS, Function.update_self]
    have hmS : st'.mem (h + ASM_BR_SEXP) = oE.value := by
      rw [hmem', Function.update_self]
    have hag : ∀ a, a < oB.value → a ≠ h + ASM_BR_GEXP → a ≠ h + ASM_BR_SEXP →
        st'.mem a = stB.mem a := by
      intro a ha h1 h2
      rw [hm_other a h1 h2, hlowF a (by omega), hlowE a ha]
    have hrec : ∀ i, i < ASM_BR_SIZE → i ≠ ASM_BR_GEXP → i ≠ ASM_BR_SEXP →
        st'.mem (h + i) = stB.mem (h + i) := by
      intro i hi h1 h2
      exact hag _ (by omega) (by omega) (by omega)
    -- the parts other than the record keep their cells
    have hpart : ∀ i < 6, i ≠ 0 → i ≠ 1 → ∀ a, asmBrPart X h x i a → stB.mem a = st'.mem a := by
      intro i hi hi0 hi1 a ha
      have hr := hin i hi hi1 a ha
      have hn0 : ¬ asmBrPart X h x 0 a := fun h0 => hdisj i hi 0 (by decide) hi1 (by decide)
        hi0 a ha h0
      have hn0' : ¬ (h ≤ a ∧ a < h + ASM_BR_SIZE) := hn0
      exact (hag a hr.2 (by omega) (by omega)).symm
    have hEm := embRep_local x.eCap x.embH x.yEmb.view x.yEmb stB.mem st'.mem
      (fun c hc => hpart 2 (by decide) (by decide) (by decide) c hc)
    have hOut := outGraphRep_local x.vCap x.eCap x.outH tr₀.S_cur x.gOut stB.mem st'.mem
      (fun c hc => hpart 3 (by decide) (by decide) (by decide) c hc)
    have hTour := asmBrTourView_keep hTR ⟨tr₀, ord, vCap, eCap⟩ (s := x.sTour)
      (fun c hc => hpart 4 (by decide) (by decide) (by decide) c hc)
    have hRest := asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ x.restH
      ⟨tr₀, ord, vCap, eCap⟩ x.xRest stB.mem st'.mem
      (fun c hc => hpart 5 (by decide) (by decide) (by decide) c hc)
    -- the bounds on the ends of the calls
    have hoBw : oB.value < 2 ^ w := by omega
    have hoEw : oE.value < 2 ^ w := by omega
    -- the cost
    have hmc : (3 * G.m + 2) * bundleLogFactor M N ≤ tr₀.machCost :=
      initMachCost_ge lsfInit (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl)
        (dsAmortConst impl) k M N G ℓ₀ ord j
    have hlog := one_le_bundleLogFactor M N
    have hmc' : 3 * G.m + 2 ≤ tr₀.machCost :=
      le_trans (Nat.le_mul_of_pos_right _ (by omega)) hmc
    have hmul : (B.mul + 500) * tr₀.machCost = B.mul * tr₀.machCost + 500 * tr₀.machCost :=
      Nat.add_mul _ _ _
    have hval : (Outcome.returned oF.value).value = oF.value := rfl
    refine ⟨asmFirstInitStmt fB fExp, hpf, .returned oF.value, st', c, x, hrun,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hxv, hxe, hxt, hxl, hEm.1 hemb, hdom, hembEq, hOut.1 hout',
      hTour.1 htour, hmarks, hRest.1 hX, hv5, he5, hslot, fun i hi hi1 a ha =>
        ⟨(hin i hi hi1 a ha).1, by have := (hin i hi hi1 a ha).2; rw [hval]; omega⟩, hdisj,
      ?_, ?_, by rw [hmG]; exact hoBw, by rw [hmS]; exact hoEw, by rw [hval]; omega, ?_, ?_, ?_, ?_⟩
    · rw [hrec ASM_BR_EMB (by decide) (by decide) (by decide)]; exact hw1
    · rw [hrec ASM_BR_OUT (by decide) (by decide) (by decide)]; exact hw2
    · rw [hrec ASM_BR_TOUR (by decide) (by decide) (by decide)]; exact hw3
    · rw [hrec ASM_BR_REST (by decide) (by decide) (by decide)]; exact hw4
    · rw [hrec ASM_BR_VCAP (by decide) (by decide) (by decide)]; exact hw5
    · rw [hrec ASM_BR_ECAP (by decide) (by decide) (by decide)]; exact hw6
    · rw [hrec ASM_BR_TCAP (by decide) (by decide) (by decide)]; exact hw7
    · rw [hrec ASM_BR_LW (by decide) (by decide) (by decide)]; exact hw8
    · -- the export of `G`
      rw [hval, hmG]
      refine exportAt_mono (exportAt_congr (fun a ha1 ha2 => ?_) hexpG) (by omega)
      rw [hm_other a (by omega) (by omega), hlowF a ha2]
    · -- the export of `S₀`
      rw [hval, hmS]
      refine exportAt_congr (fun a ha1 _ => ?_) hexpS
      exact hm_other a (by omega) (by omega)
    · -- the space
      show oF.value ≤ h + (asmFirstInitSpace B.space).eval (M + N + k + vCap + eCap + L + depth)
      omega
    · -- the cells after the second export are zero
      intro a ha
      rw [hval] at ha
      rw [hm_other a (by omega) (by omega)]
      exact hzF a ha
    · -- memory below `h`
      intro a ha
      rw [hag a (by omega) (by omega) (by omega)]
      exact hlowB a ha
    · -- the cost
      show c + _ + _ ≤ asmFirstInitMul B.mul * tr₀.machCost
      unfold asmFirstInitMul
      have hcB' : cB + (TR x.vCap x.eCap).phi x.tourH x.xTour stB.mem +
          X.phi x.restH x.xRest stB.mem ≤ B.mul * tr₀.machCost := hcB
      have e1 : (TR x.vCap x.eCap).phi x.tourH x.xTour st'.mem =
          (TR x.vCap x.eCap).phi x.tourH x.xTour stB.mem := hTour.2.symm
      have e2 : X.phi x.restH x.xRest st'.mem = X.phi x.restH x.xRest stB.mem := hRest.2.symm
      have goal' : c + (TR x.vCap x.eCap).phi x.tourH x.xTour st'.mem +
          X.phi x.restH x.xRest st'.mem ≤ B.mul * tr₀.machCost + 500 * tr₀.machCost := by
        rw [e1, e2]
        omega
      rw [hmul]
      exact goal'

end MinCostFlow.SparseCore.Program
