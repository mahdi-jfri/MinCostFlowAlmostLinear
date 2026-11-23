module

public import MinCostFlow.SparseCore.Program.AssemblyBranchValue
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
public import MinCostFlow.SparseCore.Program.AssemblyContractLayoutEmb

/-!
# Readout layout of the branch module (`AssemblyBranchReadLayout`)

The bridge of the top layer (`ScBranchModuleHyp`, `AssemblyBridge.lean`) asks for
`AsmBranchReadoutLayout` (`AssemblyContractLayout.lean`) of the branch module: the layout and
footprint guarantees of readouts `2` (`readLSF`), `3` (`readS`), and `5` (`readOrd`).

This file proves them for `asmBrFullRep` and packages them as
`asmBranchAt_value_readoutLayout` for the concrete branch value `asmBranchAt_value`
(`AssemblyBranchValue.lean`):
* `asmBrFull_readLSF_layout_runs`: readout `2`, from P10's `readRep_readLSF_layout` through
  `asmBrReadStmt_runs` and `AsmBrRepAt.frame_read`. The forest `DynGraphAt` lies inside part `1`
  of the branch footprint, and the stretch descriptor and tables lie below `h`.
* `asmBrFull_readS_layout_runs`: readout `3`, from P10's `readRep_readS_layout` through
  `asmBrReadStmt_runs` and `AsmBrRepAt.frame_read`, with capacities `x.vCap = vCap`,
  `x.eCap = eCap`, and the sparsifier `DynGraphAt` inside part `1` of the branch footprint.
* `asmBrFull_readOrd_layout_runs`: readout `5`, from `asmBrOrd_loop_runs` and
  `AsmBrRepAt.frame_tour`. Besides `OrdListAt`, it exports `st'.mem h = h + 1`,
  `st'.mem h + words ≤ o.value`, and `st'.mem (st'.mem h + j) < 2 ^ w` for every written word
  `j < words`: every vertex is below `x.vCap`, every edge key is below `2 * x.eCap`, both sit
  below `dynGraphSize x.vCap x.eCap ≤ h < 2 ^ w`, and every list length is below the word count
  `W < 2 ^ w`.
* `asmBranchAt_value_readoutLayout`: combines the three into `AsmBranchReadoutLayout` for
  `asmBranchAt_value`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Read

/-! ## Word bounds for serialized order records -/

private theorem ordRecordsWords_mem_lt {v : ℕ} {xs : List End} :
    ∀ {recs : List (ℕ × List End)}, (v, xs) ∈ recs → xs.length < ordRecordsWords recs
  | [], h => by cases h
  | (u, ys) :: rest, h => by
    simp only [ordRecordsWords, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with heq | hmem
    · rcases Prod.mk.inj heq with ⟨_, rfl⟩
      omega
    · have ih := ordRecordsWords_mem_lt hmem
      unfold ordRecordsWords at ih
      omega

private theorem asmBrRecsAt_word_lt {mem : ℕ → ℕ} {B : ℕ} :
    ∀ {a : ℕ} {recs : List (ℕ × List End)},
      AsmBrRecsAt mem a recs →
      (∀ r ∈ recs, r.1 < B ∧ r.2.length < B ∧ ∀ z ∈ r.2, endKey z < B) →
      ∀ k < ordRecordsWords recs, mem (a + k) < B
  | _, [], _, _, k, hk => by
    simp only [ordRecordsWords, List.map_nil, List.sum_nil] at hk
    omega
  | a, (v, xs) :: rest, ⟨hv, hxs, hrest⟩, hB, k, hk => by
    have hhw : ordRecordsWords ((v, xs) :: rest) = 2 + xs.length + ordRecordsWords rest := by
      simp [ordRecordsWords, Nat.add_assoc]
    rw [hhw] at hk
    obtain ⟨hvB, hlenB, hzB⟩ := hB (v, xs) List.mem_cons_self
    by_cases hk0 : k = 0
    · subst hk0
      simpa [hv] using hvB
    · by_cases hk1 : k = 1
      · subst hk1
        simpa [hxs.1] using hlenB
      · by_cases hkxs : k < 2 + xs.length
        · have hi : k - 2 < xs.length := by omega
          have heq : a + k = a + 1 + 1 + (k - 2) := by omega
          rw [heq, hxs.2 (k - 2) hi, List.getD_eq_getElem _ _ hi]
          exact hzB _ (List.getElem_mem hi)
        · have hk' : k - (2 + xs.length) < ordRecordsWords rest := by omega
          have heq : a + k = a + 2 + xs.length + (k - (2 + xs.length)) := by omega
          rw [heq]
          exact asmBrRecsAt_word_lt hrest (fun r hr => hB r (List.mem_cons_of_mem _ hr)) _ hk'

/-! ## Readouts `2`, `3`, and `5` with layout and footprint guarantees -/

section LayoutReadouts

variable {depth w : ℕ} {fmt : Num.Format w} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
  {impl : SparsifyImpl} {L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}

/-- **Readout `2` with layout and footprint bounds** for `asmBrFullRep`, matching
`AsmBranchReadoutLayout.readLSF_layout_runs`. -/
theorem asmBrFull_readLSF_layout_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRL : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRL ASM_BR_READ))
    (hRL : p.procs[fRL]? = some readLSFStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 5 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (let fBase := st'.mem (h + 1)
         let stDesc := st'.mem (h + 3)
         let Lw := st'.mem (h + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem h forestVCap forestECap fmt.limbBits Lw fmt.precision tr.cs.G.E tr.cs.lsf ∧
           fBase + dynGraphSize forestVCap forestECap ≤ h ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             R.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ h ∧
           (∀ e ∈ tr.cs.G.E, st'.mem stDesc + e * Lw + Lw ≤ h ∧
             ∀ t < Lw, R.foot brH x' (st'.mem stDesc + e * Lw + t) ∨
               (h ≤ st'.mem stDesc + e * Lw + t ∧ st'.mem stDesc + e * Lw + t < o.value)) ∧
           (∀ e ∈ tr.cs.G.E, st'.mem (stDesc + 1) + e * Lw + Lw ≤ h ∧
             ∀ t < Lw, R.foot brH x' (st'.mem (stDesc + 1) + e * Lw + t) ∨
               (h ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value)) ∧
           dynGraphSize forestVCap forestECap ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
        R.Respects (R.foot brH x) h 5 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h M N vCap eCap tr ord x mem pos ω hfmt hM hN _ hrep hfoot _ _ hz hroom
  let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
  have hX : X.Local := asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep.1
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨h0, -, -, -, -, -, -, -, -, hG, hlsf, hS, -, hR, -, -, -, -, -, -, -, -, -, hLw, -⟩ :=
    id hrepA
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hR', hout,
      ⟨hlsfAt, hfEnd, hfFoot, hstDesc, hNum, hDen⟩, ⟨hlo, hhi, hz', hfr, hnew⟩, hcost⟩ :=
    readRep_readLSF_layout (mul := 80) hRL le_rfl x.readH h x.yRead.view x.yRead mem pos ω hR
      (fun c hc => hfootA c ⟨1, by decide, hc⟩) hz hroom
  rw [hRL] at hbody₁
  cases hbody₁
  rw [← h0] at hrun₁
  obtain ⟨st', hrun, hmem⟩ := asmBrReadStmt_runs hRL
    (by have : ASM_BR_READ < ASM_BR_SIZE := by decide
        omega) hrun₁
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_read (hEnd := o₁.value) hTR hX hrepA hfootA
    hR' hfr hnew
  have hphiR : (readRep x.vCap x.eCap x.tCap x.L_w fmt.precision).phi x.readH y' st₁.mem =
      (readRep x.vCap x.eCap x.tCap x.L_w fmt.precision).phi x.readH x.yRead mem := by
    have hv : y'.view = x.yRead.view := hR'.1
    show readPotMul * treePot y'.view.G y'.view.lsf.T =
      readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T
    rw [hv]
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yRead := y' }, hrun,
    ⟨hmem ▸ hrep', hrep.2⟩, ?_,
    ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨1, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · dsimp only
    have hL4 : st'.mem (h + 4) = x.L_w := by rw [hmem]; exact hout.1
    refine ⟨x.vCap, x.tCap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hL4, ← hM, ← hN]; exact hLw
    · rw [hL4, hfmt, hmem, ← hG, ← hlsf]; exact hlsfAt
    · rw [hmem]; exact hfEnd
    · intro addr ha1 ha2
      rw [hmem] at ha1 ha2
      exact Or.inl ⟨1, by decide, hfFoot addr ha1 ha2⟩
    · rw [hmem]; exact hstDesc
    · intro e he
      obtain ⟨hEnd, hFt⟩ := hNum e (hG.symm ▸ he)
      rw [hL4, hmem]
      exact ⟨hEnd, fun t ht => Or.inl ⟨1, by decide, hFt t ht⟩⟩
    · intro e he
      obtain ⟨hEnd, hFt⟩ := hDen e (hG.symm ▸ he)
      rw [hL4, hmem]
      exact ⟨hEnd, fun t ht => Or.inl ⟨1, by decide, hFt t ht⟩⟩
    · have hvc : x.vCap = vCap := hrep.2.2.2.1
      have hec : x.eCap = eCap := hrep.2.2.2.2.1
      have htc : x.tCap ≤ 2 * (vCap + eCap + 2) ^ 2 := by
        rw [← hvc, ← hec]; exact hrep.2.2.2.2.2.1
      have hmono : ∀ a b c : ℕ, b ≤ c → dynGraphSize a b ≤ dynGraphSize a c := fun a b c h => by
        unfold dynGraphSize; omega
      rw [hvc]
      exact hmono vCap x.tCap (2 * (vCap + eCap + 2) ^ 2) htc
  · show c₁ + 9 + asmBrPhi X { x with yRead := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    rw [hphiR] at hcost
    simp only [asmBrReadoutCost]
    omega

/-- **Readout `3` with layout and footprint bounds** for `asmBrFullRep`, matching
`AsmBranchReadoutLayout.readS_layout_runs`. -/
theorem asmBrFull_readS_layout_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRS : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRS ASM_BR_READ))
    (hRS : p.procs[fRS]? = some readSStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ graphVCap graphECap,
          DynGraphAt st'.mem (st'.mem h) graphVCap graphECap tr.S_cur ∧
          graphVCap = vCap ∧ graphECap = eCap ∧
          st'.mem h + dynGraphSize graphVCap graphECap ≤ h ∧
          (∀ addr, st'.mem h ≤ addr → addr < st'.mem h + dynGraphSize graphVCap graphECap →
            R.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot brH x) h 1 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h vCap eCap tr ord x mem pos ω hrep hfoot _ _ hz hroom
  let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
  have hX : X.Local := asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep.1
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨h0, -, -, -, -, -, -, -, -, -, -, hS, -, hR, -⟩ := id hrepA
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hR', hDG, hsEnd, hsFoot,
      ⟨hlo, hhi, hz', hfr, hnew⟩, hcost⟩ :=
    readRep_readS_layout (mul := 20) hRS le_rfl x.readH h x.yRead.view x.yRead mem pos ω hR
      (fun c hc => hfootA c ⟨1, by decide, hc⟩) hz hroom
  rw [hRS] at hbody₁
  cases hbody₁
  rw [← h0] at hrun₁
  obtain ⟨st', hrun, hmem⟩ := asmBrReadStmt_runs hRS
    (by have : ASM_BR_READ < ASM_BR_SIZE := by decide
        omega) hrun₁
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_read (hEnd := o₁.value) hTR hX hrepA hfootA
    hR' hfr hnew
  have hphiR : (readRep x.vCap x.eCap x.tCap x.L_w fmt.precision).phi x.readH y' st₁.mem =
      (readRep x.vCap x.eCap x.tCap x.L_w fmt.precision).phi x.readH x.yRead mem := by
    have hv : y'.view = x.yRead.view := hR'.1
    show readPotMul * treePot y'.view.G y'.view.lsf.T =
      readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T
    rw [hv]
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yRead := y' }, hrun,
    ⟨hmem ▸ hrep', hrep.2⟩, ?_,
    ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨1, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · refine ⟨x.vCap, x.eCap, ?_, hrep.2.2.2.1, hrep.2.2.2.2.1, ?_, ?_⟩
    · rw [hmem, ← hS]; exact hDG
    · rw [hmem]; exact hsEnd
    · intro addr ha1 ha2
      rw [hmem] at ha1 ha2
      exact Or.inl ⟨1, by decide, hsFoot addr ha1 ha2⟩
  · show c₁ + 9 + asmBrPhi X { x with yRead := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    rw [hphiR] at hcost
    simp only [asmBrReadoutCost]
    omega

/-- **Readout `5` with layout and word-bound guarantees** for `asmBrFullRep`, matching
`AsmBranchReadoutLayout.readOrd_layout_runs`. -/
theorem asmBrFull_readOrd_layout_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fList mulT : ℕ} (hp : p.procs[f]? = some (asmBrReadOrdStmt fList))
    (hL : AsmBrTourListProj TR w p fList mulT) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h →
      h + (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ words, OrdListAt st'.mem (st'.mem h) (tr.outOrder ord) words ∧
          words ≤ ordWordsOn tr.S_cur.V (tr.outOrder ord) ∧
          st'.mem h = h + 1 ∧
          st'.mem h + words ≤ o.value ∧
          (∀ j < words, st'.mem (st'.mem h + j) < 2 ^ w)) ∧
        R.Respects (R.foot brH x) h (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord))
          mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤
          asmBrOrdMul mulT capExp * (ordWordsOn tr.S_cur.V (tr.outOrder ord) + 1) *
            bundleLogFactor M N + R.phi brH x mem := by
  intro R brH h M N vCap eCap tr ord x mem pos ω hM hN _ hrep hfoot _ hh hz hroom
  let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
  have hX : X.Local := asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep.1
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨-, -, h2, h3, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hT, hmarks, -, hV, hcap, -,
    hdisj⟩ := id hrepA
  obtain ⟨hOh, -, hdyn⟩ := hO
  obtain ⟨-, hVlt, hElt, hvc, -, hn, -, -, ⟨vL, hvLlen, hvLnd, hvLmem, hvLat, -⟩, -⟩ := hdyn
  have hvLmem' : ∀ v, v ∈ vL ↔ v ∈ tr.S_cur.V := hvLmem
  have hV' : tr.S_cur.V = tr.cs.RF.R := hV
  have hw : 1 < 2 ^ w := by simp only [ASM_BR_SIZE] at hrec; omega
  set out := tr.outOrder ord with hout
  set W := ordRecordsWords (vL.map fun v => (v, out v)) with hW
  have hVeq : tr.S_cur.V = vL.toFinset := by
    ext v
    rw [List.mem_toFinset, hvLmem']
  have hwords : ordWordsOn tr.S_cur.V out = 1 + W := by
    unfold ordWordsOn
    rw [hVeq, List.sum_toFinset _ hvLnd, hW]
    simp [ordRecordsWords, Function.comp_def]
  rw [hwords] at hroom ⊢
  have hvLle : vL.length ≤ x.vCap := by
    rw [← List.toFinset_card_of_nodup hvLnd]
    calc vL.toFinset.card ≤ (Finset.range x.vCap).card :=
          Finset.card_le_card fun v hv => Finset.mem_range.mpr
            (hVlt v ((hvLmem' v).mp (List.mem_toFinset.mp hv)))
      _ = x.vCap := Finset.card_range _
  have hgpart : ∀ k < dynGraphSize x.vCap x.eCap, asmBrPart X brH x 3 (x.gOut + k) :=
    fun k hk => Or.inr ⟨by omega, by omega⟩
  have hgcell : ∀ k < dynGraphSize x.vCap x.eCap, x.gOut + k < h := fun k hk =>
    hfootA _ ⟨3, by decide, hgpart k hk⟩
  have hgtour : ∀ k < dynGraphSize x.vCap x.eCap,
      ¬ (TR x.vCap x.eCap).foot x.tourH x.xTour (x.gOut + k) := fun k hk hf =>
    hdisj 3 (by decide) 4 (by decide) (by decide) _ (hgpart k hk) hf
  have hdgLe : dynGraphSize x.vCap x.eCap ≤ h := by
    have h4 : 4 ≤ dynGraphSize x.vCap x.eCap := by unfold dynGraphSize; omega
    have := hgcell (dynGraphSize x.vCap x.eCap - 1) (by omega)
    omega
  have hL' := hL ord tr.cs.lsf.F (outCoreOrder tr ord)
  have htourLt : x.tourH < h := hfootA _ ⟨4, by decide, hL'.handle_foot _ _ _ _⟩
  have H : AsmBrOrdHyp (asmBrTourView TR ⟨tr, ord, vCap, eCap⟩ x.vCap x.eCap) w h x.gOut x.vCap
      x.tourH vL out x.sTour mem x.xTour :=
    { vl := fun j hj => hvLat j hj
      vlCell := fun j hj => by
        have hk : 4 + x.vCap + j < dynGraphSize x.vCap x.eCap := by
          unfold dynGraphSize; omega
        refine ⟨?_, ?_⟩
        · have := hgcell _ hk; omega
        · have := hgtour _ hk
          rwa [show x.gOut + (4 + x.vCap + j) = x.gOut + 4 + x.vCap + j by omega] at this
      vlt := fun v hv => hVlt v ((hvLmem' v).mp hv)
      marked := asmBr_markedList_eq (tr := tr) (ord := ord) hmarks
      footLt := fun a ha => hfootA a ⟨4, by decide, ha⟩
      tourLt := by omega
      room := by omega }
  have hg2 : x.gOut + 2 < h := hgcell 2 (by unfold dynGraphSize; omega)
  have hmn : mem (x.gOut + 2) = vL.length := by rw [hvLlen]; exact hn
  set st0 := startState [brH, h] mem pos with hst0
  have r1 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const ASM_BR_OUT)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 x.outH } 5 :=
    runs_assign_iff.mpr ⟨x.outH, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := brH) (by simp [hst0, startState])) (Expr.eval_const (by
        simp only [ASM_BR_OUT, ASM_BR_SIZE] at hrec ⊢; omega)) (by
        simp only [ASM_BR_OUT, ASM_BR_SIZE] at hrec ⊢; omega)) (by simpa [hst0, startState]
        using h2), rfl, rfl, rfl⟩
  set st1 := { st0 with regs := Function.update st0.regs 2 x.outH } with hst1
  have r2 : Runs w p ω (.assign 3 (.load (.reg 2))) st1 .normal
      { st1 with regs := Function.update st1.regs 3 x.gOut } 3 :=
    runs_assign_iff.mpr ⟨x.gOut, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := x.outH) (by simp [hst1]))
      (by simpa [hst1, hst0, startState] using hOh), rfl, rfl, rfl⟩
  set st2 := { st1 with regs := Function.update st1.regs 3 x.gOut } with hst2
  have r3 : Runs w p ω (.assign 4 (.load (.reg 3))) st2 .normal
      { st2 with regs := Function.update st2.regs 4 x.vCap } 3 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := x.gOut) (by simp [hst2]))
      (by simpa [hst2, hst1, hst0, startState, dgVCapOff] using hvc), rfl, rfl, rfl⟩
  set st3 := { st2 with regs := Function.update st2.regs 4 x.vCap } with hst3
  have r4 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 3) (.const 2)))) st3 .normal
      { st3 with regs := Function.update st3.regs 5 vL.length } 5 :=
    runs_assign_iff.mpr ⟨vL.length, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := x.gOut) (by simp [hst3, hst2])) (Expr.eval_const (by omega))
      (by omega))
      (by simpa [hst3, hst2, hst1, hst0, startState] using hmn), rfl, rfl, rfl⟩
  set st4 := { st3 with regs := Function.update st3.regs 5 vL.length } with hst4
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const ASM_BR_TOUR)))) st4 .normal
      { st4 with regs := Function.update st4.regs 6 x.tourH } 5 :=
    runs_assign_iff.mpr ⟨x.tourH, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := brH) (by simp [hst4, hst3, hst2, hst1, hst0, startState]))
      (Expr.eval_const (by simp only [ASM_BR_TOUR, ASM_BR_SIZE] at hrec ⊢; omega))
      (by simp only [ASM_BR_TOUR, ASM_BR_SIZE] at hrec ⊢; omega))
      (by simpa [hst4, hst3, hst2, hst1, hst0, startState] using h3), rfl, rfl, rfl⟩
  set st5 := { st4 with regs := Function.update st4.regs 6 x.tourH } with hst5
  have h1₅ : st5.regs 1 = h := by simp [hst5, hst4, hst3, hst2, hst1, hst0, startState]
  have r6 : Runs w p ω (.store (.reg 1) (.bin .add (.reg 1) (.const 1))) st5 .normal
      { st5 with mem := Function.update st5.mem h (h + 1) } 5 :=
    runs_store_iff.mpr ⟨h, h + 1, Expr.eval_reg_of_eq h1₅, Expr.eval_add
      (Expr.eval_reg_of_eq h1₅) (Expr.eval_const hw) (by omega), rfl, rfl, rfl⟩
  set st6 := { st5 with mem := Function.update st5.mem h (h + 1) } with hst6
  have h1₆ : st6.regs 1 = h := h1₅
  have h5₆ : st6.regs 5 = vL.length := by simp [hst6, hst5, hst4]
  have r7 : Runs w p ω (.store (.bin .add (.reg 1) (.const 1)) (.reg 5)) st6 .normal
      { st6 with mem := Function.update st6.mem (h + 1) vL.length } 5 :=
    runs_store_iff.mpr ⟨h + 1, vL.length, Expr.eval_add (Expr.eval_reg_of_eq h1₆)
      (Expr.eval_const hw) (by omega), Expr.eval_reg_of_eq h5₆, rfl, rfl, rfl⟩
  set st7 := { st6 with mem := Function.update st6.mem (h + 1) vL.length } with hst7
  have r8 : Runs w p ω (.assign 7 (.bin .add (.reg 1) (.const 2))) st7 .normal
      { st7 with regs := Function.update st7.regs 7 (h + 2) } 4 :=
    runs_assign_iff.mpr ⟨h + 2, Expr.eval_add (Expr.eval_reg_of_eq h1₆)
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set st8 := { st7 with regs := Function.update st7.regs 7 (h + 2) } with hst8
  have r9 : Runs w p ω (.assign 8 (.const 0)) st8 .normal
      { st8 with regs := Function.update st8.regs 8 0 } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st9 := { st8 with regs := Function.update st8.regs 8 0 } with hst9
  have hmem9 : st9.mem = Function.update (Function.update mem h (h + 1)) (h + 1) vL.length := rfl
  have hmem9' : ∀ a < h, st9.mem a = mem a := fun a ha => by
    rw [hmem9, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hT9 := asmBrTourView_keep hTR ⟨tr, ord, vCap, eCap⟩ (s := x.sTour) fun a ha =>
    (hmem9' a (hfootA a ⟨4, by decide, ha⟩)).symm
  have hinv0 : AsmBrOrdInv (asmBrTourView TR ⟨tr, ord, vCap, eCap⟩ x.vCap x.eCap) h x.gOut x.vCap
      x.tourH vL out x.sTour mem x.xTour 0 x.xTour st9 := by
    refine ⟨Nat.zero_le _, by simp [hst9, hst8, hst7, hst6, hst5, hst4, hst3, hst2],
      by simp [hst9, hst8, hst7, hst6, hst5, hst4, hst3],
      by simp [hst9, hst8, hst7, hst6, hst5, hst4], by simp [hst9, hst8, hst7, hst6, hst5],
      by simp [hst9, hst8, ordRecordsWords],
      by simp [hst9], hT9.1 hT, fun a ha => ha, fun a ha _ => hmem9' a ha, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h7₉ : st9.regs 7 = h + 2 := by simp [hst9, hst8]
      rw [h7₉] at ha
      rw [hmem9, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz a (by omega)
    · rw [hmem9, Function.update_of_ne (by omega), Function.update_self]
    · rw [hmem9, Function.update_self]
    · simp [AsmBrRecsAt]
  obtain ⟨st10, cL, tx', hloop, hinvN, hcostL⟩ :=
    asmBrOrd_loop_runs hL' (asmTourView_local (hTR x.vCap x.eCap) _ _ _) (ω := ω) hw H hinv0
  obtain ⟨-, -, -, -, -, h7N, -, hTN, hsubN, hfrN, hzN, hmhN, hmh1N, hrecsN⟩ := hinvN
  rw [List.take_length] at h7N hrecsN
  rw [← hW] at h7N
  rw [h7N] at hzN
  have r11 : Runs w p ω (.ret (.reg 7)) st10 (.returned (h + 2 + W)) st10 2 :=
    runs_ret_iff.mpr ⟨h + 2 + W, Expr.eval_reg_of_eq h7N, rfl, rfl, rfl⟩
  obtain ⟨c, hrunAll, hc⟩ : ∃ c, Runs w p ω (asmBrReadOrdStmt fList) st0
      (.returned (h + 2 + W)) st10 c ∧ c ≤ cL + 60 :=
    ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨st4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨st5, _, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨st6, _, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨st7, _, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨st8, _, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨st9, _, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨st10, _, _, hloop, r11, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_tour (h := h) hX hrepA hfootA hTN
    (fun c hc hn => hfrN c hc hn) hsubN
  have hread : readOrdRecordsAt st10.mem (st10.mem h) = vL.map fun v => (v, out v) := by
    rw [hmhN]
    unfold readOrdRecordsAt
    rw [hmh1N, show h + 1 + 1 = h + 2 by omega]
    have := hrecsN.readOrdRecords_eq
    rwa [List.length_map] at this
  have hwordsLt : ∀ j < 1 + W, st10.mem (st10.mem h + j) < 2 ^ w := by
    rw [hmhN]
    intro j hj
    cases j with
    | zero =>
      rw [Nat.add_zero, hmh1N]
      unfold dynGraphSize at hdgLe
      omega
    | succ k =>
      have hk : k < W := by omega
      rw [show h + 1 + (k + 1) = h + 2 + k by omega]
      refine asmBrRecsAt_word_lt hrecsN (fun r hr => ?_) k hk
      rcases List.mem_map.mp hr with ⟨v, hv, rfl⟩
      have hvCap : v < x.vCap := hVlt v ((hvLmem' v).mp hv)
      have hlenLt : (out v).length < W := ordRecordsWords_mem_lt (List.mem_map.mpr ⟨v, hv, rfl⟩)
      refine ⟨?_, by dsimp only; omega, fun z hz => ?_⟩
      · unfold dynGraphSize at hdgLe; omega
      · have hzM : z ∈ x.sTour.markedList v := by
          rw [asmBr_markedList_eq hmarks v]; exact hz
        have hzMk : z ∈ x.sTour.marked := by
          unfold OutTourAbs.markedList at hzM
          exact of_decide_eq_true (List.mem_filter.mp hzM).2
        have hzE : z.1 < x.eCap := hElt z.1 ((hmarks.2 z).mp hzMk).2
        unfold endKey
        unfold dynGraphSize at hdgLe
        cases z.2 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  refine ⟨_, hp, .returned (h + 2 + W), st10, c, { x with xTour := tx' }, hrunAll,
    ⟨hrep', hrep.2⟩,
    ⟨1 + W, ⟨?_, ?_, ?_⟩, le_rfl, hmhN, by simp only [Outcome.value, hmhN]; omega, hwordsLt⟩,
    ⟨by simp only [Outcome.value]; omega, by simp only [Outcome.value]; omega,
      by simpa [Outcome.value] using hzN, fun a ha hn => hfrN a ha fun hf => hn ⟨4, by decide, hf⟩,
      fun a ha => Or.inl (hfoot' a ha)⟩, ?_⟩
  · rw [hread, List.map_map]
    simpa [Function.comp_def] using hvLnd
  · funext v
    unfold readOrd
    rw [hread, ordOfRecords_map_pair]
    split_ifs with hv
    · rfl
    · exact (outOrder_eq_nil_of_not_mem tr ord fun hR => hv ((hvLmem' v).mpr (hV' ▸ hR))).symm
  · rw [hread]
  · show c + asmBrPhi X { x with xTour := tx' } st10.mem ≤ _ + asmBrPhi X x mem
    have hphi9 : (asmTourView (TR x.vCap x.eCap) ord tr.cs.lsf.F (outCoreOrder tr ord)).phi
        x.tourH x.xTour st9.mem = (TR x.vCap x.eCap).phi x.tourH x.xTour mem := hT9.2.symm
    rw [hphi9] at hcostL
    change cL + (TR x.vCap x.eCap).phi x.tourH tx' st10.mem ≤ _ at hcostL
    have hsum := asmBrOrd_sum_le mulT x.eCap out vL
    rw [← hW] at hsum
    have hcap' : x.eCap + 2 ≤ (M + N + 2) ^ capExp := by
      have : x.vCap + x.eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp := hcap
      rw [hM, hN] at this
      omega
    have hlg : ordStoreLog x.eCap ≤ capExp * bundleLogFactor M N :=
      le_trans (ordStoreLog_le_of_cap hcap')
        (Nat.mul_le_mul_left _ (logStep_le_bundleLogFactor M N))
    have hb : 1 ≤ bundleLogFactor M N :=
      le_trans (by omega) (logStep_le_bundleLogFactor M N)
    have e1 : (29 + mulT * ordStoreLog x.eCap) * W ≤
        (29 + mulT * (capExp * bundleLogFactor M N)) * W :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlg) _)
    have e2 : (29 + mulT * (capExp * bundleLogFactor M N)) * W + 64 ≤
        asmBrOrdMul mulT capExp * (1 + W + 1) * bundleLogFactor M N := by
      unfold asmBrOrdMul
      have hWb : W ≤ W * bundleLogFactor M N := Nat.le_mul_of_pos_right W hb
      have q1 : (29 + mulT * (capExp * bundleLogFactor M N)) * W =
          29 * W + mulT * capExp * (W * bundleLogFactor M N) := by ring
      have q2 : (100 + mulT * capExp) * (1 + W + 1) * bundleLogFactor M N =
          100 * (W * bundleLogFactor M N) + 200 * bundleLogFactor M N +
            mulT * capExp * (W * bundleLogFactor M N) +
            2 * (mulT * capExp * bundleLogFactor M N) := by ring
      rw [q1, q2]
      omega
    omega

end LayoutReadouts

/-! ## `AsmBranchReadoutLayout` for `asmBranchAt_value` -/

/-- **Readout layout for `asmBranchAt_value`**: readouts `2`, `3`, and `5` of the branch value
satisfy every layout, footprint, and word-bound guarantee of `AsmBranchReadoutLayout`. -/
theorem asmBranchAt_value_readoutLayout {K : AsmBrConsts} {CFS : AsmCompFamilySpec}
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ}
    {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs} {I : AsmBrProcIdx} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    (hΨ : AsmWalkPotRestartOK impl depth Ψ)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ K.Cγ * (m + 2) ^ K.cγ)
    (hRe : ∀ tr U ord ord', brReemb tr U ord ord' =
      stepBundleTree_reembList (fun _ => canonicalSparsify impl) tr U ord ord')
    (hP : HasAsmBrProcs p bp impl CF.fRoot I)
    (X : AsmBrPieces K lsfInit depth w fmt L capExp limbMul impl p I TR B5 Ψ CF.rep) :
    AsmBranchReadoutLayout
      (asmBranchAt_value (C_lsst := C_lsst) (CF := CF) hTR hB5 hTh hΨ hγ hRe hP X) where
  readLSF_layout_runs :=
    asmBrFull_readLSF_layout_runs hTR hB5 hP.readLSF hP.readLSFBody
  readS_layout_runs :=
    asmBrFull_readS_layout_runs hTR hB5 hP.readS hP.readSBody
  readEmb_layout_runs :=
    asmBrFull_readEmb_layout_runs hTR hB5 hP.readEmb hP.readEmbBody
  readOrd_layout_runs := by
    intro brH h M N vCap eCap tr ord x mem pos ω hM hN hcap hrep hfoot hb hh hz hroom
    obtain ⟨body, hbody, o, st', c, x', h1, h2, h3, h4, hcost⟩ :=
      asmBrFull_readOrd_layout_runs (fmt := fmt) hTR hB5 hP.readOrd X.list brH h M N vCap eCap
        tr ord x mem pos ω hM hN hcap hrep hfoot hb hh hz hroom
    refine ⟨body, hbody, o, st', c, x', h1, h2, h3, h4, hcost.trans ?_⟩
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      asmBrSpec_mul_ord)) _

end MinCostFlow.SparseCore.Program
