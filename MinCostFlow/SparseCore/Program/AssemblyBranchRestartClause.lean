module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartPoly

/-!
# The restart of a branch in the form of the clause (`AssemblyBranchRestartClause`)

`asmBrFull_restart_runs` (`AssemblyBranchFull.lean`) proves the restart of a branch for any heap
space `sp` at least `asmBrRestartSpace`. With the polynomial bound `asmBrRestartSpace_le_poly`
(`AssemblyBranchRestartPoly.lean`) we take `sp` to be the value of `asmBrRestartPoly` at
`M + N + k + vCap + eCap + L + depth`. This gives the clause `restart_runs` of `AsmBranchAt`
(`asmBrFull_restart_runs_clause`), with the space `asmBrRestartPoly …` in place of
`S.restartSpace capExp` and the multiplier `asmBrRestartMul …` in place of `S.mul capExp limbMul`.

The edges of the core graph lie below `eCap` by the model facts of the clause. P5's restart `J`
serves every bundle cap, and the bundle side gives the cap of its table as `tr.k`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The restart of a branch, in the form of the clause `restart_runs` of `AsmBranchAt`.** The
heap space is the polynomial `asmBrRestartPoly` of P5's multiplier `J.mul`, P10's multiplier
`readMul`, the multiplier `embRefreshMul` of the refresh, the query space of the tour, the word
exponent of the sparsifier and its stretch bound `⌈γ_ℓ m⌉ ≤ Cγ · (m + 2) ^ cγ`. The cost factor is
`asmBrRestartMul`. The walk potential `Ψ` after the restart is paid by `AsmWalkPotRestartOK`. -/
theorem asmBrFull_restart_runs_clause {w depth L capExp limbMul wordExp : ℕ}
    {fmt : Num.Format w} {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ}
    (hΨ : AsmWalkPotRestartOK impl depth Ψ) {Cγ cγ : ℕ}
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {OS : OutTourSpec} {nm sm fm lm : ℕ} {p : Program}
    {TR : ℕ → ℕ → DSRep AsmTourAbs} (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hOP : AsmBrOutProj OS TR w p nm sm fm lm)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {fBun : ℕ}
    (J : AsmBrBunAt TR B5 w p fBun)
    {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {fCFInit fCFBatch : ℕ}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    {bRead readMul : ℕ} {readIdx : ℕ → ℕ} {f f8 bOut bSpan fEmb bCopy : ℕ}
    (hf : p.procs[f]? = some (asmBrRestartStmt f8 (outIdxReset bOut) fEmb))
    (hpS : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    (hpOut : OutProcsAt p bOut nm sm fm lm)
    (hp8 : p.procs[f8]? = some (restartBranchStmt fBun (bSpan + bsIdxOp0 + 0) (bRead + readIdx 3)))
    (hfE : p.procs[fEmb]? = some (embRefreshStmt bCopy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords])
    (hB : ∀ k vCap eCap tCap L_w (P' : DSParams) cap,
      P'.w = w → P'.eCap ≤ eCap → eCap ≤ tCap → 1 ≤ L_w →
      (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w →
      ReadBranchAt (readRep vCap eCap tCap L_w fmt.precision) w vCap eCap tCap L_w fmt.precision
        P' cap p bRead readIdx CF.fRoot (CF.toRootQueryAtCaps k vCap eCap) readMul)
    (hWE : asmP10WordExp capExp ≤ wordExp) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    let sp := asmBrRestartPoly J.mul readMul embRefreshMul OS.querySpace impl.cw Cγ cγ capExp
    ∀ (brH cfH j k M N vCap eCap h : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (cfs : CompFamilyAbs) (xcf : CF.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      j < k → tr.m₀ = M → tr.n₀ = N →
      16 ≤ 2 ^ w → (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      CF.rep.rep cfH cfs xcf mem → CF.vCapOf xcf = vCap → CF.eCapOf xcf = eCap → cfs j = tr.cs → k = (cfs 0).k →
      (∀ a, R.foot brH x a → a < h) → (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a, R.foot brH x a → ¬ CF.rep.foot cfH xcf a) →
      (∀ a ∈ [brH, cfH, j, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + sp.eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w →
      let tr' := restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord
      AsmBrModelFacts impl vCap eCap tr ord →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x' xcf',
        Runs w p ω body (startState [brH, cfH, j, h] mem pos) o st' c ∧
        R.rep brH ⟨tr', ord, vCap, eCap⟩ x' st'.mem ∧
        CF.rep.rep cfH cfs xcf' st'.mem ∧ CF.vCapOf xcf' = vCap ∧ CF.eCapOf xcf' = eCap ∧
        h ≤ o.value ∧ o.value ≤ h + sp.eval (M + N + k + vCap + eCap + L + depth) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot brH x a → ¬ CF.rep.foot cfH xcf a → st'.mem a = mem a) ∧
        (∀ a, R.foot brH x' a → R.foot brH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, CF.rep.foot cfH xcf' a → CF.rep.foot cfH xcf a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, R.foot brH x' a → ¬ CF.rep.foot cfH xcf' a) ∧
        c + R.phi brH x' st'.mem + CF.rep.phi cfH xcf' st'.mem ≤
          asmBrRestartMul J.mul readMul (CFS.rootCost capExp) OS.mul capExp *
              (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord + 1) +
            R.phi brH x mem + CF.rep.phi cfH xcf mem := by
  intro R sp brH cfH j k M N vCap eCap h tr ord x cfs xcf mem pos ω hj hM hN h16 hword hrep
    hrep4 hv4 he4 hcfs hk0 hfoot hf4 hd4 hargs hz hspW tr' hfacts
  have hGE : ∀ e ∈ tr.cs.G.E, e < eCap := hfacts.2.2.2.2.2.2.2.2.1
  have hsp := asmBrRestartSpace_le_poly (k := k) hγ J.space_le readMul embRefreshMul OS hrep hM hN
    hGE
  exact asmBrFull_restart_runs hΨ hTR hOP hTh J CF hf hpS hpOut hp8 hfE hcopy hB hWE brH cfH j k M N
    vCap eCap h _ tr ord x cfs xcf mem pos ω hj hM hN h16 hword hrep hrep4 hv4 he4 hcfs hk0 hfoot hf4 hd4
    hargs hz hsp hspW

end MinCostFlow.SparseCore.Program
