module

public import MinCostFlow.SparseCore.Program.AssemblyBranchInitBound

/-!
# The init of a branch (`AssemblyBranchInit`)

The init of the sparse-core tool builds every branch `j < k` by `initBundleTreeWithParams`
(`AsmBranchAt.init_runs`, `AssemblyTopIface.lean`). The program of the init (`asmBrInitStmt`)
makes two calls: the first phase (`AsmBrCoreInitAt`), which builds every part of the branch but
the readout data, and the init of the readout data of P10 (`ReadBranchAt.init`). Then it stores the
handle of the readout data in the first word of the record.

This file puts the two calls together (`asmBrFull_init_runs`), in the form of the clause
`init_runs` of `AsmBranchAt`. The proof follows the cells:
* the first phase writes the record and the parts `2` to `5` in `[h, h₁)`, keeps the memory below
  `h`, and leaves exports of `G` and `S₀` in `[h, h₁)`;
* P10's init reads `T`, `F`, the roots and the stretch tables from P4's export, which lies below
  `h`, and `G`, `S₀` from the two exports of the first phase. It builds the readout data in
  `[h₁, h₂)` and keeps the memory below `h₁`. Its view meets `ReadView.Inv` by the facts of the
  model (`readView_inv_of_facts`), and P10's word condition follows from the word condition of the
  clause (`p10Word_of_wordExp`);
* the last store writes only the first word of the record, which no other part uses.
So the six parts lie apart: the readout data in `[h₁, h₂)`, the other parts in `[h, h₁)`.

The space is `asmBrInitPoly` and the cost factor `asmBrInitMul` (`AssemblyBranchInitBound.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The init of a branch, in the form of the clause `init_runs` of `AsmBranchAt`.** Let `J` be
the first phase, P10 meet `ReadBranchAt` at the caps of a branch (`AsmBrReadAt`), and the word
exponent `wordExp` be at least P10's (`asmP10WordExp`). Under the hypotheses of the clause, with
the facts of the model for the new state `tr₀`, the init runs and the branch at `h` holds
`⟨tr₀, ord, vCap, eCap⟩`. The new cells lie in `[h, o)`, at most `asmBrInitPoly J.space readMul
capExp` of them, the memory below `h` stays, and the cost with the potential is at most
`asmBrInitMul J.mul readMul capExp limbMul` times the machine cost of `tr₀`. -/
theorem asmBrFull_init_runs {w depth P L capExp limbMul wordExp : ℕ} {lsfInit : LSFInit}
    {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {CFR : DSRep CompFamilyAbs} {p : Program} {fCore f bRead readMul fRoot : ℕ}
    {readIdx : ℕ → ℕ} {Q : ℕ → RootQueryAt w p fRoot}
    (J : AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p fCore)
    (hB : AsmBrReadAt w P p bRead readIdx fRoot Q readMul)
    (hf : p.procs[f]? = some (asmBrInitStmt fCore (bRead + readIdx 4)))
    (hWE : asmP10WordExp capExp ≤ wordExp) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
    let sp := asmBrInitPoly J.space readMul capExp
    ∀ (cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords : ℕ) (G : MGraph)
      (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (cfs : CompFamilyAbs) (xcf : CFR.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      0 < k → j < k → G.IsValid → G.V.Nonempty → G.m ≤ M → G.n ≤ N → G.n ≤ G.m + 1 →
      P ≤ 4 * L → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      CFR.rep cfH cfs xcf mem → cfs j = initCompLSFWith lsfInit G ℓ₀ k j →
      BranchLengthsAt mem lengths eCap L P h G ℓ₀ →
      DynGraphAt mem graph vCap eCap G → graph + dynGraphSize vCap eCap ≤ h →
      OrdListAt mem cOrdPtr ord cWords → cOrdPtr + cWords ≤ h → cWords ≤ 1 + 6 * G.m →
      IsRotationOrder G ord →
      CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap (cfs j) → expEnd ≤ h →
      (∀ a, CFR.foot cfH xcf a → a < h) →
      (∀ a ∈ [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h],
        a < 2 ^ w) →
      ZeroFrom mem h →
      h + sp.eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w →
      let tr₀ := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
      AsmBrModelFacts impl vCap eCap tr₀ ord →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body
          (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
            mem pos)
          o st' c ∧
        R.rep h ⟨tr₀, ord, vCap, eCap⟩ x' st'.mem ∧
        R.Respects (fun _ => False) h (sp.eval (M + N + k + vCap + eCap + L + depth)) mem
          o.value h x' st'.mem ∧
        c + R.phi h x' st'.mem ≤ asmBrInitMul J.mul readMul capExp limbMul * tr₀.machCost := by
  intro R sp cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf
    mem pos ω hk hj hGval hGne hGm hGn hGnm hPL hcap hw hCF hcfs hlen hGr hgraph hOrd
    hOrdLe hcW hRot hExp hexpEnd hCFfoot hargs hz hspace tr₀ hfacts
  let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
  have hJsp : J.space.eval (M + N + k + vCap + eCap + L + depth) ≤
      sp.eval (M + N + k + vCap + eCap + L + depth) := polyBound_le_asmBrInitPoly _ _ _ _
  -- the first phase
  obtain ⟨bodyC, hbC, oC, stC, cC, x, hrunC, hwEmb, hwOut, hwTour, hwRest, hwV, hwE, hwT, hwL,
    hxv, hxe, hxt, hxl, hembC, hdomC, hembAgC, hOutC, hTourC, hmkC, hXC, hV5, hE5, hslot,
    hpartsC, hdisjC, hExpGC, hExpSC, hGexpW, hSexpW, hsizeC, hoC_hi, hzC, hbelowC, hcostC⟩ :=
    J.runs cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf
      mem pos ω hk hj hGval hGne hGm hGn hGnm hPL hcap hw hCF hcfs hlen hGr hgraph hOrd
      hOrdLe hcW hRot hExp hexpEnd hCFfoot hargs hz (lt_of_le_of_lt (Nat.add_le_add_left hJsp h) hspace) hfacts
  have hpartsC' : ∀ i < 6, i ≠ 1 → ∀ a, asmBrPart X h x i a → h ≤ a ∧ a < oC.value := hpartsC
  have hdisjC' : ∀ i < 6, ∀ i' < 6, i ≠ 1 → i' ≠ 1 → i ≠ i' → ∀ a, asmBrPart X h x i a →
      ¬ asmBrPart X h x i' a := hdisjC
  have hcostC' : cC + (TR x.vCap x.eCap).phi x.tourH x.xTour stC.mem +
      X.phi x.restH x.xRest stC.mem ≤ J.mul * tr₀.machCost := hcostC
  have hsizeC' : h + 16 ≤ oC.value := hsizeC
  have hhw : h < 2 ^ w := hargs h (by simp)
  -- P4's export of the branch, seen in the memory after the first phase
  have hExpC : CompBranchExportAt w stC.mem expPtr expEnd L capExp M N vCap eCap tr₀.cs := by
    rw [hcfs] at hExp
    exact compBranchExportAt_congr (fun a _ ha2 => (hbelowC a (by omega)).symm) hExp
  obtain ⟨h8, hexpW, -, htEx, -, hfEx, ⟨roots, hrLen, hrNd, hrFs, hrLA, -, hrHi⟩,
    hLw1, hLwHi, htCapLo, htCapHi, htE, num, den, hnd⟩ := hExpC
  have htcEq : x.tCap = stC.mem (expPtr + 7) := hxt.trans (hbelowC _ (by omega)).symm
  have hlwEq : x.L_w = stC.mem (expPtr + 6) := hxl.trans (hbelowC _ (by omega)).symm
  -- the view of P10 and its invariant
  have hInv : ReadView.Inv vCap eCap (stC.mem (expPtr + 7))
      ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ :=
    readView_inv_of_facts hfacts htCapLo htE fun e he =>
      ⟨(hnd e he).2.2.2.2.2.2.2.2.1, (hnd e he).2.2.2.2.2.2.2.2.2⟩
  have hword : (vCap + stC.mem (expPtr + 7) + 2) ^ 2 * (stC.mem (expPtr + 6) + 1) < 2 ^ w :=
    p10Word_of_wordExp hcap htCapHi hLwHi hWE hw
  have hRB := hB 0 vCap eCap (stC.mem (expPtr + 7)) (stC.mem (expPtr + 6))
    ⟨impl, 0, w, 0, 0, 0, 0⟩ 0 rfl (Nat.zero_le _) htCapLo hLw1 hword
  have hsize : readInitSize ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ ≤ 4 * vCap + 4 * eCap :=
    readInitSize_le_caps hfacts num den
  have hsp2 := asmBrInit_space_le J.space readMul (k := k) (depth := depth) htCapHi hLwHi hsize
  have hroomR : oC.value + readSpace readMul vCap (stC.mem (expPtr + 7)) (stC.mem (expPtr + 6))
      (readInitSize ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩) < 2 ^ w := by
    have : sp.eval (M + N + k + vCap + eCap + L + depth) =
        (asmBrInitPoly J.space readMul capExp).eval (M + N + k + vCap + eCap + L + depth) := rfl
    omega
  -- what P10's init reads
  have hInitAt : ReadInitAt stC.mem oC.value (stC.mem (expPtr + 6))
      (stC.mem (h + ASM_BR_GEXP)) (stC.mem expPtr) (stC.mem (expPtr + 1))
      (stC.mem (expPtr + 2)) (stC.mem (expPtr + 3)) (stC.mem (expPtr + 4))
      (stC.mem (expPtr + 5)) (stC.mem (h + ASM_BR_SEXP))
      ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ := by
    refine ⟨hExpGC, exportAt_mono htEx (by omega), exportAt_mono hfEx (by omega), hExpSC,
      ⟨roots, hrLen, hrNd, hrFs, hrLA, by omega⟩, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨-, h1, -, h2, -⟩ := hnd e he
      exact ⟨by omega, by omega⟩
    · obtain ⟨-, -, -, -, h1, h2, h3, h4, -⟩ := hnd e he
      exact ⟨h1, h2, h3, h4⟩
  have hargsR : ∀ a ∈ [stC.mem (h + ASM_BR_GEXP), stC.mem expPtr, stC.mem (expPtr + 1),
      stC.mem (expPtr + 2), stC.mem (expPtr + 3), stC.mem (expPtr + 4), stC.mem (expPtr + 5),
      stC.mem (h + ASM_BR_SEXP), oC.value], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hGexpW
    · exact hexpW _ (by omega) (by omega)
    · exact hexpW _ (by omega) (by omega)
    · exact hexpW _ (by omega) (by omega)
    · exact hexpW _ (by omega) (by omega)
    · exact hexpW _ (by omega) (by omega)
    · exact hexpW _ (by omega) (by omega)
    · exact hSexpW
    · omega
  -- P10's init
  obtain ⟨bodyR, hbR, oR, stR, cR, y, hrunR, hrepR, hoR_lo, hoR_hi, hzR, hbelowR, hfootR,
    hcostR⟩ :=
    hRB.init _ _ _ _ _ _ _ _ oC.value _ stC.mem stC.pos ω hargsR hInitAt hInv hzC hroomR
  -- the program
  obtain ⟨st', c, hrun, hmem', hc⟩ :=
    asmBrInitStmt_runs (cfH := cfH) (j := j) (graph := graph) (cOrdPtr := cOrdPtr) (k := k)
      (M := M) (N := N) (L := L) (P := P) (depth := depth) (lengths := lengths)
      (by simp only [ASM_BR_SIZE]; omega) (by omega) hbC hbR hrunC hrunR
  -- what the last store keeps
  have hF : ∀ a, a ≠ h + ASM_BR_READ → st'.mem a = stR.mem a := fun a ha => by
    rw [hmem', Function.update_of_ne ha]
  have hF0 : st'.mem (h + ASM_BR_READ) = oC.value := by rw [hmem', Function.update_self]
  have hlow : ∀ a < oC.value, a ≠ h + ASM_BR_READ → st'.mem a = stC.mem a := fun a h1 h2 =>
    (hF a h2).trans (hbelowR a h1)
  have h0part : asmBrPart X h x 0 (h + ASM_BR_READ) :=
    ⟨by simp [ASM_BR_READ], by simp [ASM_BR_READ, ASM_BR_SIZE]⟩
  have hkeepP : ∀ i < 6, i ≠ 0 → i ≠ 1 → ∀ a, asmBrPart X h x i a → st'.mem a = stC.mem a :=
    fun i hi h0 h1 a ha => hlow a (hpartsC' i hi h1 a ha).2 fun he =>
      hdisjC' i hi 0 (by decide) h1 (by decide) h0 a ha (by rw [he]; exact h0part)
  have hrecW : ∀ i, 0 < i → i < ASM_BR_SIZE → st'.mem (h + i) = stC.mem (h + i) :=
    fun i h1 h2 => hlow _ (by simp only [ASM_BR_SIZE] at h2; omega)
      (by simp only [ASM_BR_READ]; omega)
  have hfootR' : ∀ a, readFoot vCap eCap (stC.mem (expPtr + 7)) (stC.mem (expPtr + 6))
      oC.value y a → oC.value ≤ a ∧ a < oR.value := hfootR
  have hp1 : ∀ a, readFoot x.vCap x.eCap x.tCap x.L_w oC.value y a →
      oC.value ≤ a ∧ a < oR.value := by
    intro a ha
    rw [hxv, hxe, htcEq, hlwEq] at ha
    exact hfootR' a ha
  -- the branch after the init
  let x' := x.withRead oC.value y
  have hyv : y.view = ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ := hrepR.1
  have hrepF : R.rep h ⟨tr₀, ord, vCap, eCap⟩ x' st'.mem := by
    refine ⟨⟨hF0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdomC, hembAgC, ?_,
      ?_, hmkC, ?_, hfacts.2.2.1.2.1, ?_, ?_, ?_⟩, hV5.trans hxv.symm, hE5.trans hxe.symm, hxv,
      hxe, ?_, ?_, ?_, le_rfl⟩
    · exact (hrecW ASM_BR_EMB (by decide) (by decide)).trans hwEmb
    · exact (hrecW ASM_BR_OUT (by decide) (by decide)).trans hwOut
    · exact (hrecW ASM_BR_TOUR (by decide) (by decide)).trans hwTour
    · exact (hrecW ASM_BR_REST (by decide) (by decide)).trans hwRest
    · exact (hrecW ASM_BR_VCAP (by decide) (by decide)).trans hwV
    · exact (hrecW ASM_BR_ECAP (by decide) (by decide)).trans hwE
    · exact (hrecW ASM_BR_TCAP (by decide) (by decide)).trans hwT
    · exact (hrecW ASM_BR_LW (by decide) (by decide)).trans hwL
    · show y.view.G = tr₀.cs.G
      rw [hyv]
    · show y.view.lsf = tr₀.cs.lsf
      rw [hyv]
    · show y.view.S = tr₀.S_cur
      rw [hyv]
    · show y.view.Inv x.vCap x.eCap x.tCap
      rw [hyv, hxv, hxe, htcEq]
      exact hInv
    · show (readRep x.vCap x.eCap x.tCap x.L_w P).rep oC.value y.view y st'.mem
      rw [hyv, hxv, hxe, htcEq, hlwEq]
      refine ((readRep_local _ _ _ _ P) oC.value _ y stR.mem st'.mem fun a ha => ?_).1 hrepR
      have := hfootR' a ha
      exact (hF a (by simp only [ASM_BR_READ]; omega)).symm
    · exact ((embRep_local x.eCap) x.embH x.yEmb.view x.yEmb stC.mem st'.mem fun a ha =>
        (hkeepP 2 (by decide) (by decide) (by decide) a ha).symm).1 hembC
    · exact ((outGraphRep_local x.vCap x.eCap) x.outH tr₀.S_cur x.gOut stC.mem st'.mem
        fun a ha => (hkeepP 3 (by decide) (by decide) (by decide) a ha).symm).1 hOutC
    · exact (asmTourView_local (hTR x.vCap x.eCap) ord tr₀.cs.lsf.F (outCoreOrder tr₀ ord)
        x.tourH x.sTour x.xTour stC.mem st'.mem fun a ha =>
          (hkeepP 4 (by decide) (by decide) (by decide) a ha).symm).1 hTourC
    · exact ((asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ) x.restH
        ⟨tr₀, ord, vCap, eCap⟩ x.xRest stC.mem st'.mem fun a ha =>
          (hkeepP 5 (by decide) (by decide) (by decide) a ha).symm).1 hXC
    · show x.vCap + x.eCap + 2 ≤ (M + N + 2) ^ capExp
      rw [hxv, hxe]
      exact hcap.1
    · show x.L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)
      rw [hlwEq]
      exact hLwHi
    · intro i hi i' hi' hne a ha ha'
      rcases eq_or_ne i 1 with rfl | h1 <;> rcases eq_or_ne i' 1 with rfl | h1'
      · exact hne rfl
      · have e1 := hp1 a ha
        have e2 := hpartsC' i' hi' h1' a ((asmBrPart_withRead h1' a).mp ha')
        omega
      · have e1 := hp1 a ha'
        have e2 := hpartsC' i hi h1 a ((asmBrPart_withRead h1 a).mp ha)
        omega
      · exact hdisjC' i hi i' hi' h1 h1' hne a ((asmBrPart_withRead h1 a).mp ha)
          ((asmBrPart_withRead h1' a).mp ha')
    · show x.tCap ≤ 2 * (x.vCap + x.eCap + 2) ^ 2
      rw [htcEq, hxv, hxe]
      exact htCapHi
    · show x.xRest.slotCap ≤ 2 * (x.vCap + x.eCap + 2) ^ 2
      rw [hxv, hxe]
      exact hslot
    · show 1 ≤ x.L_w
      rw [hlwEq]
      exact hLw1
  -- the cost
  have hTloc := hTR x.vCap x.eCap x.tourH ⟨ord, tr₀.cs.lsf.F, x.sTour.marked⟩ x.xTour stC.mem
    st'.mem fun a ha => (hkeepP 4 (by decide) (by decide) (by decide) a ha).symm
  have hXloc := (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ) x.restH
    ⟨tr₀, ord, vCap, eCap⟩ x.xRest stC.mem st'.mem fun a ha =>
      (hkeepP 5 (by decide) (by decide) (by decide) a ha).symm
  have hphi : R.phi h x' st'.mem = readPotMul * treePot y.view.G y.view.lsf.T +
      (TR x.vCap x.eCap).phi x.tourH x.xTour stC.mem + X.phi x.restH x.xRest stC.mem := by
    show readPotMul * treePot y.view.G y.view.lsf.T +
      (TR x.vCap x.eCap).phi x.tourH x.xTour st'.mem + X.phi x.restH x.xRest st'.mem = _
    rw [← hTloc.2, ← hXloc.2]
  have hcostR' : cR + readPotMul * treePot y.view.G y.view.lsf.T ≤
      readMul * (readInitSize ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ + 1) *
        (stC.mem (expPtr + 6) + 1) := hcostR
  have hsizeF : readInitSize ⟨tr₀.cs.G, tr₀.cs.lsf, tr₀.S_cur, num, den⟩ ≤ 4 * G.n + 4 * G.m :=
    readInitSize_le_facts hfacts num den
  have hmc : (3 * G.m + 2) * bundleLogFactor M N ≤ tr₀.machCost :=
    initMachCost_ge lsfInit (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl)
      (dsAmortConst impl) k M N G ℓ₀ ord j
  have hfin := asmBrInit_cost_le (jMul := J.mul) (readMul := readMul) hcap.2 hLwHi hsizeF hGnm hmc
  refine ⟨_, hf, .returned oR.value, st', c, x', hrun, hrepF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show h ≤ oR.value
    omega
  · show oR.value ≤ h + sp.eval (M + N + k + vCap + eCap + L + depth)
    have : sp.eval (M + N + k + vCap + eCap + L + depth) =
        (asmBrInitPoly J.space readMul capExp).eval (M + N + k + vCap + eCap + L + depth) := rfl
    omega
  · intro a ha
    change oR.value ≤ a at ha
    rw [hF a (by simp only [ASM_BR_READ]; omega)]
    exact hzR a ha
  · intro a ha _
    rw [hF a (by simp only [ASM_BR_READ]; omega), hbelowR a (by omega)]
    exact hbelowC a ha
  · rintro a ⟨i, hi, ha⟩
    right
    change h ≤ a ∧ a < oR.value
    rcases eq_or_ne i 1 with rfl | h1
    · have := hp1 a ha
      omega
    · have := hpartsC' i hi h1 a ((asmBrPart_withRead h1 a).mp ha)
      omega
  · rw [hphi]
    omega

end MinCostFlow.SparseCore.Program
