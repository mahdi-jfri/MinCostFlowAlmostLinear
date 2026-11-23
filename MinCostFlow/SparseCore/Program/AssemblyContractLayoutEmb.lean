module

public import MinCostFlow.SparseCore.Program.AssemblyBranchValue
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout

/-!
# Embedding readout (`op 4`) layout and footprint proofs (`AssemblyContractLayoutEmb`)

Proves the layout and footprint postconditions of readout `4` (`embReadStmt`) for P10's embedding
table (`embRep_readEmb_layout`) and lifts them to the full branch representation
(`asmBrFull_readEmb_layout_runs`), supplying `AsmBranchReadoutLayout.readEmb_layout_runs`:
* `MEmbBounded st'.mem (st'.mem h) coreE (st'.mem (h + 1)) tr.emb 0 h` (the pointer table and
  every walk of `coreE` lie below `h`);
* `st'.mem (h + 1) ≤ eCap` (in fact `st'.mem (h + 1) = eCap`);
* every cell of the pointer table and of every walk lies in `R.foot brH x'` (hence in
  `R.foot brH x' ∨ (h ≤ addr ∧ addr < o.value)`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Read

/-! ## P10 readout `4` (`embReadStmt`) layout and footprint proof -/

/-- **P10 readout `4` (`embReadStmt`) satisfies every layout and footprint bound.** Proved directly
from `EmbRepAt`, `embFoot`, and `embReadStmt` (`ReadEmb.lean`, `ReadEmbOps.lean`). -/
theorem embRep_readEmb_layout {eCap w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some embReadStmt)
    {r h : ℕ} {v : EmbView} {y : EmbConc} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hr : r < 2 ^ w) (hh : h + 2 < 2 ^ w)
    (hrep : (embRep eCap).rep r v y mem)
    (hfoot : ∀ a, embFoot eCap r y a → a < h) (hz : ZeroFrom mem h) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
      Runs w p ω body (startState [r, h] mem pos) o st' c ∧
      (embRep eCap).rep r v y' st'.mem ∧
      ReadEmbOut st'.mem h eCap v ∧
      st'.mem h = r + 2 ∧
      st'.mem (h + 1) = eCap ∧
      MEmbBounded st'.mem (st'.mem h) v.dom eCap v.emb 0 h ∧
      (∀ a, st'.mem h ≤ a → a < st'.mem h + eCap → embFoot eCap r y' a) ∧
      (∀ e ∈ v.dom, ∀ a,
        st'.mem (st'.mem h + e) ≤ a →
        a < st'.mem (st'.mem h + e) + (mWalkEncode (v.emb e)).length →
        embFoot eCap r y' a) ∧
      (embRep eCap).Respects (embFoot eCap r y) h 2 mem o.value r y' st'.mem ∧
      c + (embRep eCap).phi r y' st'.mem ≤ 20 + (embRep eCap).phi r y mem := by
  obtain ⟨hv, h0, h1, hE⟩ := hrep
  have hr1 : r + 1 < h := hfoot _ (Or.inl ⟨by omega, by omega⟩)
  have htabLe : r + 2 + eCap ≤ h := by
    have := hfoot (r + 1 + eCap) (Or.inl ⟨by omega, by omega⟩)
    omega
  set m' := Function.update (Function.update mem h (r + 2)) (h + 1) eCap with hm'
  have hag : ∀ a, embFoot eCap r y a → mem a = m' a := fun a ha => by
    have := hfoot a ha
    simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
      ite_false]
  have hrep' := ((embRep_local eCap) r v y mem m' hag).1 ⟨hv, h0, h1, hE⟩
  have hrun : ∃ o st' c, Runs w p ω embReadStmt (startState [r, h] mem pos) o st' c ∧
      (o = .returned (h + 2) ∧ st'.mem = m') ∧ c ≤ 20 := by
    apply runs_start_le
    refine runs_seq_store_le (x := h) (v := r + 2)
      (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := r) (by simp [startState])) h0) ?_
    refine runs_seq_store_le (x := h + 1) (v := eCap)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := r) (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) (by
          simp only [startState, Function.update_apply, show r + 1 ≠ h by omega, ite_false]
          exact h1)) ?_
    refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) ⟨rfl, by simp [hm', startState]⟩ ?_
    simp only [Expr.size]; omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hmem⟩, hc⟩ := hrun
  have hmh : st'.mem h = r + 2 := by rw [hmem]; simp [hm']
  have hmh1 : st'.mem (h + 1) = eCap := by rw [hmem]; simp [hm']
  refine ⟨embReadStmt, hp, .returned (h + 2), st', c, y, hrun, hmem ▸ hrep', ?_, hmh, hmh1, ?_,
    ?_, ?_, ?_, ?_⟩
  · refine ⟨hmh1, fun e he => ?_⟩
    obtain ⟨hlt, _, ht, hw⟩ := hrep'.2.2.2 e he
    rw [hmh, hmem, ht]
    exact ⟨hlt, hw⟩
  · rw [hmh]
    refine ⟨Nat.zero_le _, htabLe, fun e he => ?_⟩
    obtain ⟨hlt, _, ht, hw⟩ := hrep'.2.2.2 e he
    have hptr : st'.mem (r + 2 + e) = y.ptr e := by rw [hmem]; exact ht
    have hwalkEnd : y.ptr e + (mWalkEncode (v.emb e)).length ≤ h := by
      have hlen : (mWalkEncode (v.emb e)).length = Read.walkWords (y.view.emb e) := by
        rw [hv, mWalkEncode_length, Read.walkWords]
      have hlt' := hfoot (y.ptr e + Read.walkWords (y.view.emb e) - 1)
        (Or.inr ⟨e, hv ▸ he, by simp only [Read.walkWords]; omega, by simp only [Read.walkWords]; omega⟩)
      rw [hlen]; omega
    rw [hptr]
    exact ⟨hlt, Nat.zero_le _, hwalkEnd, hmem ▸ hw⟩
  · intro a ha1 ha2
    rw [hmh] at ha1 ha2
    exact Or.inl ⟨by omega, ha2⟩
  · intro e he a ha1 ha2
    obtain ⟨_, _, ht, _⟩ := hrep'.2.2.2 e he
    have hptr : st'.mem (st'.mem h + e) = y.ptr e := by rw [hmh, hmem]; exact ht
    rw [hptr] at ha1 ha2
    have hlen : (mWalkEncode (v.emb e)).length = Read.walkWords (y.view.emb e) := by
      rw [hv, mWalkEncode_length, Read.walkWords]
    rw [hlen] at ha2
    exact Or.inr ⟨e, hv ▸ he, ha1, ha2⟩
  · refine ⟨by simp [Outcome.value], by simp [Outcome.value], ?_, ?_, fun a ha => Or.inl ha⟩
    · intro a ha
      simp only [Outcome.value] at ha
      rw [hmem]
      simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
        ite_false]
      exact hz a (by omega)
    · intro a ha _
      rw [hmem]
      simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
        ite_false]
  · simpa [embRep] using hc

/-! ## Branch-level readout `4` with layout and footprint bounds -/

/-- **Readout `4` with layout and footprint bounds** for `asmBrFullRep`, matching
`AsmBranchReadoutLayout.readEmb_layout_runs`. -/
theorem asmBrFull_readEmb_layout_runs {depth w : ℕ} {fmt : Num.Format w}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRE : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRE ASM_BR_EMB))
    (hRE : p.procs[fRE]? = some embReadStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 2 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (let embTable := st'.mem h
         let embCap := st'.mem (h + 1)
         let coreE := (coreGraph tr.cs.G tr.cs.lsf).E
         EmbeddingReadoutAt st'.mem h embCap tr.cs.G tr.cs.lsf tr.emb ∧
         MEmbBounded st'.mem embTable coreE embCap tr.emb 0 h ∧
         embCap ≤ eCap ∧
         (∀ addr, embTable ≤ addr → addr < embTable + embCap →
           R.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value)) ∧
         (∀ e ∈ coreE, ∀ addr,
           st'.mem (embTable + e) ≤ addr →
           addr < st'.mem (embTable + e) + (mWalkEncode (tr.emb e)).length →
           R.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot brH x) h 2 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h vCap eCap tr ord x mem pos ω hrep hfoot _ _ hz hroom
  let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
  have hX : X.Local := asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep.1
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨-, h1, -, -, -, -, -, -, -, -, -, -, -, -, hE, hdom, hemb, -⟩ := id hrepA
  have hembH : x.embH < 2 ^ w := lt_of_lt_of_le (hfootA x.embH ⟨2, by decide,
    Or.inl ⟨le_rfl, by omega⟩⟩) (by omega)
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hE', hout, _, hm1, hBd, hTabFt, hWalkFt,
      ⟨hlo, hhi, hz', hfr, hnew⟩, hcost⟩ :=
    embRep_readEmb_layout hRE hembH hroom hE (fun c hc => hfootA c ⟨2, by decide, hc⟩) hz
  rw [hRE] at hbody₁
  cases hbody₁
  rw [← h1] at hrun₁
  obtain ⟨st', hrun, hmem⟩ := asmBrReadStmt_runs hRE
    (by have : ASM_BR_EMB < ASM_BR_SIZE := by decide
        omega) hrun₁
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_emb (hEnd := o₁.value) hTR hX hrepA hfootA
    hE' hfr hnew
  have heCapEq : x.eCap = eCap := hrep.2.2.2.2.1
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yEmb := y' }, hrun,
    ⟨hmem ▸ hrep', hrep.2⟩, ?_,
    ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨2, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · dsimp only
    rw [hmem]
    refine ⟨hout.mEmbAt hdom hemb, ?_, by rw [hm1, heCapEq], ?_, ?_⟩
    · rw [hm1]
      refine ⟨hBd.1, hBd.2.1, fun e he => ?_⟩
      obtain ⟨heLt, hpLo, hpHi, hW⟩ := hBd.2.2 e (hdom he)
      rw [hemb e he] at hpHi hW
      exact ⟨heLt, hpLo, hpHi, hW⟩
    · intro addr ha1 ha2
      rw [hm1] at ha2
      exact Or.inl ⟨2, by decide, hTabFt addr ha1 ha2⟩
    · intro e he addr ha1 ha2
      rw [← hemb e he] at ha2
      exact Or.inl ⟨2, by decide, hWalkFt e (hdom he) addr ha1 ha2⟩
  · show c₁ + 9 + asmBrPhi X { x with yEmb := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    simp only [embRep] at hcost
    simp only [asmBrReadoutCost]
    omega

end MinCostFlow.SparseCore.Program
