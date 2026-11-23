module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRep

/-!
# Readouts `2`, `3` and `4` of a branch (`AssemblyBranchRead`)

Readouts `2` (the LSF view), `3` (the graph `S_cur`) and `4` (the embedding table) of a branch
of the sparse-core program (`AsmBranchAt`, `AssemblyTopIface.lean`) cost a constant. The branch
keeps their data in the readout data and the embedding table of piece P10 (`readRep`, `embRep`),
whose own readouts are proved (`readRep_readLSF`, `readRep_readS`, `embRead_ends`). So each
readout of the branch loads the handle of the part from its record and calls the readout of the
part (`asmBrReadStmt`).

The proofs share two steps.
* `asmBrReadStmt_runs`: the run of the dispatch is the run of the called readout, plus `9` steps.
* `AsmBrRepAt.frame_read` and `AsmBrRepAt.frame_emb`: a call that writes only the cells of one
  part and new cells, and leaves the view of the part, keeps the whole branch. The other parts
  lie below the heap pointer and outside the part, so their cells keep their values, and each
  part is local.

The main results are `asmBr_readLSF_runs`, `asmBr_readS_runs` and `asmBr_readEmb_runs`, the
clauses `readLSF_runs`, `readS_runs` and `readEmb_runs` of `AsmBranchAt` for `asmBrRep`, with
readout cost `asmBrReadoutCost`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.SparseCore.Program.Read

/-! ## The dispatch -/

/-- A readout of a branch, `[b, h]`: call procedure `f` on the handle stored at `b + off` and on
the heap pointer `h`, and return what it returns. -/
def asmBrReadStmt (f off : ℕ) : Stmt :=
  .call 2 f [.load (.bin .add (.reg 0) (.const off)), .reg 1] ;; .ret (.reg 2)

/-- The dispatch never reads random bits. -/
theorem asmBrReadStmt_noRand (f off : ℕ) : (asmBrReadStmt f off).NoRand := by
  simp [asmBrReadStmt, Stmt.NoRand]

/-- The constant cost of readouts `2`, `3` and `4` of a branch. -/
def asmBrReadoutCost : ℕ := 200

/-- **The run of the dispatch.** If the called procedure runs on `[mem (b + off), h]`, the
dispatch runs on `[b, h]`, returns the same value, ends with the same memory, and costs `9` more
steps. -/
theorem asmBrReadStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {f off b h pos : ℕ}
    {mem : ℕ → ℕ} {body : Stmt} {o₁ : Outcome} {st₁ : State} {c₁ : ℕ}
    (hf : p.procs[f]? = some body) (hoff : b + off < 2 ^ w)
    (hrun : Runs w p ω body (startState [mem (b + off), h] mem pos) o₁ st₁ c₁) :
    ∃ st', Runs w p ω (asmBrReadStmt f off) (startState [b, h] mem pos) (.returned o₁.value)
      st' (c₁ + 9) ∧ st'.mem = st₁.mem := by
  have hargs : evalArgs w (startState [b, h] mem pos)
      [.load (.bin .add (.reg 0) (.const off)), .reg 1] = some [mem (b + off), h] := by
    have hoff' : off < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hoff
    simp [evalArgs, Expr.eval, startState, hoff', hoff]
  set st₂ : State :=
    { st₁ with regs := (Function.update (startState [b, h] mem pos).regs 2 o₁.value) }
  have hcall : Runs w p ω (.call 2 f [.load (.bin .add (.reg 0) (.const off)), .reg 1])
      (startState [b, h] mem pos) .normal st₂
      (argsSize [.load (.bin .add (.reg 0) (.const off)), .reg 1] + c₁ + 1) :=
    runs_call_iff.mpr ⟨[mem (b + off), h], body, o₁, st₁, c₁, hargs, hf, hrun, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 2)) st₂ (.returned o₁.value) st₂ ((Expr.reg 2).size + 1) :=
    runs_ret_iff.mpr ⟨o₁.value, by simp [Expr.eval, st₂], rfl, rfl, rfl⟩
  refine ⟨st₂, ?_, rfl⟩
  have hseq := runs_seq_iff.mpr (Or.inr ⟨st₂, _, _, hcall, hret, rfl⟩)
  simpa [asmBrReadStmt, argsSize, Expr.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hseq

/-! ## Calls that touch one part -/

/-- Changing the readout data leaves every other part. -/
theorem asmBrPart_setRead {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x : AsmBrConc TR X.τ} {y' : ReadConc} :
    ∀ i, i ≠ 1 → asmBrPart X b { x with yRead := y' } i = asmBrPart X b x i
  | 0, _ => rfl
  | 1, h => absurd rfl h
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, _ => rfl

/-- Changing the embedding table leaves every other part. -/
theorem asmBrPart_setEmb {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x : AsmBrConc TR X.τ} {y' : EmbConc} :
    ∀ i, i ≠ 2 → asmBrPart X b { x with yEmb := y' } i = asmBrPart X b x i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, h => absurd rfl h
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, _ => rfl

/-- If part `k` changes from `x` to `x'` only by cells in `[h, hEnd)`, the other parts are the
same, and all old cells lie below `h`, then the parts of `x'` are disjoint, and every cell of `x'`
is a cell of `x` or lies in `[h, hEnd)`. -/
theorem asmBr_disjoint_of_part {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b h hEnd k : ℕ} {x x' : AsmBrConc TR X.τ} (hdisj : AsmBrDisjoint X b x)
    (hfoot : ∀ c, asmBrFoot X b x c → c < h)
    (hsame : ∀ i, i ≠ k → asmBrPart X b x' i = asmBrPart X b x i)
    (hnew : ∀ c, asmBrPart X b x' k c → asmBrPart X b x k c ∨ (h ≤ c ∧ c < hEnd)) :
    AsmBrDisjoint X b x' ∧
      ∀ c, asmBrFoot X b x' c → asmBrFoot X b x c ∨ (h ≤ c ∧ c < hEnd) := by
  have hP : ∀ i < 6, ∀ c, asmBrPart X b x' i c →
      asmBrPart X b x i c ∨ (i = k ∧ h ≤ c ∧ c < hEnd) := by
    intro i _ c hc
    by_cases hik : i = k
    · subst hik
      rcases hnew c hc with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h2⟩
    · rw [hsame i hik] at hc
      exact Or.inl hc
  refine ⟨?_, ?_⟩
  · intro i hi j hj hij c hci hcj
    rcases hP i hi c hci with hci' | ⟨rfl, hci'⟩ <;> rcases hP j hj c hcj with hcj' | ⟨rfl, hcj'⟩
    · exact hdisj i hi j hj hij c hci' hcj'
    · exact absurd (hfoot c ⟨i, hi, hci'⟩) (by omega)
    · exact absurd (hfoot c ⟨j, hj, hcj'⟩) (by omega)
    · exact hij rfl
  · rintro c ⟨i, hi, hc⟩
    rcases hP i hi c hc with hc' | ⟨_, hc'⟩
    · exact Or.inl ⟨i, hi, hc'⟩
    · exact Or.inr hc'

/-- **A call on the readout data keeps the branch.** Let the readout data hold the same view in
`mem'` with a new concrete state `y'`, let `mem'` agree with `mem` below `h` outside the old cells
of the readout data, and let the new cells of the readout data be old ones or lie in
`[h, hEnd)`. Then `mem'` holds the branch with `y'`, the cells of the branch grow only into
`[h, hEnd)`, and the potential is the same. -/
theorem AsmBrRepAt.frame_read {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {P L capExp b h hEnd : ℕ} {a : AsmBranchAbs depth} {x : AsmBrConc TR X.τ}
    {mem mem' : ℕ → ℕ} {y' : ReadConc}
    (hrep : AsmBrRepAt TR X P L capExp b a x mem)
    (hfoot : ∀ c, asmBrFoot X b x c → c < h)
    (hR' : (readRep x.vCap x.eCap x.tCap x.L_w P).rep x.readH x.yRead.view y' mem')
    (hfr : ∀ c < h, ¬ readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead c → mem' c = mem c)
    (hnew : ∀ c, readFoot x.vCap x.eCap x.tCap x.L_w x.readH y' c →
      readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead c ∨ (h ≤ c ∧ c < hEnd)) :
    AsmBrRepAt TR X P L capExp b a { x with yRead := y' } mem' ∧
      (∀ c, asmBrFoot X b { x with yRead := y' } c → asmBrFoot X b x c ∨ (h ≤ c ∧ c < hEnd)) ∧
      asmBrPhi X { x with yRead := y' } mem' = asmBrPhi X x mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hG, hlsf, hS, hinv, hR, hE, hdom, hemb, hO, hT,
    hmarks, hXr, hV, hcap, hLw, hdisj⟩ := hrep
  have hview : y'.view = x.yRead.view := hR'.1
  have hkeep : ∀ i < 6, i ≠ 1 → ∀ c, asmBrPart X b x i c → mem c = mem' c := fun i hi hi1 c hc =>
    (hfr c (hfoot c ⟨i, hi, hc⟩) (hdisj i hi 1 (by decide) hi1 c hc)).symm
  have hrec : ∀ k < ASM_BR_SIZE, mem' (b + k) = mem (b + k) := fun k hk =>
    (hkeep 0 (by decide) (by decide) _ ⟨by omega, by omega⟩).symm
  have hE' := (embRep_local x.eCap x.embH x.yEmb.view x.yEmb mem mem'
    (hkeep 2 (by decide) (by decide))).1 hE
  have hO' := (outGraphRep_local x.vCap x.eCap x.outH a.tr.S_cur x.gOut mem mem'
    (hkeep 3 (by decide) (by decide))).1 hO
  have hT' := asmBrTourView_keep hTR a (s := x.sTour) (hkeep 4 (by decide) (by decide))
  have hX' := hX x.restH a x.xRest mem mem' (hkeep 5 (by decide) (by decide))
  obtain ⟨hdisj', hfoot'⟩ := asmBr_disjoint_of_part (k := 1) (hEnd := hEnd)
    (x' := { x with yRead := y' }) hdisj hfoot asmBrPart_setRead hnew
  refine ⟨⟨(hrec _ (by decide)).trans h0, (hrec _ (by decide)).trans h1,
    (hrec _ (by decide)).trans h2, (hrec _ (by decide)).trans h3, (hrec _ (by decide)).trans h4,
    (hrec _ (by decide)).trans h5, (hrec _ (by decide)).trans h6, (hrec _ (by decide)).trans h7,
    (hrec _ (by decide)).trans h8, ?_, ?_, ?_, ?_, ?_, hE', hdom, hemb, hO', hT'.1 hT, hmarks,
    hX'.1 hXr, hV, hcap, hLw, hdisj'⟩, hfoot', ?_⟩
  · show y'.view.G = _; rw [hview]; exact hG
  · show y'.view.lsf = _; rw [hview]; exact hlsf
  · show y'.view.S = _; rw [hview]; exact hS
  · show y'.view.Inv _ _ _; rw [hview]; exact hinv
  · show (readRep x.vCap x.eCap x.tCap x.L_w P).rep x.readH y'.view y' mem'
    rw [hview]; exact hR'
  · show readPotMul * treePot y'.view.G y'.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem' + X.phi x.restH x.xRest mem' =
      readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem + X.phi x.restH x.xRest mem
    rw [hview, hT'.2, hX'.2]

/-- **A call on the embedding table keeps the branch.** As `AsmBrRepAt.frame_read`, for the
embedding table, which keeps its view. -/
theorem AsmBrRepAt.frame_emb {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {P L capExp b h hEnd : ℕ} {a : AsmBranchAbs depth} {x : AsmBrConc TR X.τ}
    {mem mem' : ℕ → ℕ} {y' : EmbConc}
    (hrep : AsmBrRepAt TR X P L capExp b a x mem)
    (hfoot : ∀ c, asmBrFoot X b x c → c < h)
    (hE' : (embRep x.eCap).rep x.embH x.yEmb.view y' mem')
    (hfr : ∀ c < h, ¬ embFoot x.eCap x.embH x.yEmb c → mem' c = mem c)
    (hnew : ∀ c, embFoot x.eCap x.embH y' c →
      embFoot x.eCap x.embH x.yEmb c ∨ (h ≤ c ∧ c < hEnd)) :
    AsmBrRepAt TR X P L capExp b a { x with yEmb := y' } mem' ∧
      (∀ c, asmBrFoot X b { x with yEmb := y' } c → asmBrFoot X b x c ∨ (h ≤ c ∧ c < hEnd)) ∧
      asmBrPhi X { x with yEmb := y' } mem' = asmBrPhi X x mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hG, hlsf, hS, hinv, hR, hE, hdom, hemb, hO, hT,
    hmarks, hXr, hV, hcap, hLw, hdisj⟩ := hrep
  have hview : y'.view = x.yEmb.view := hE'.1
  have hkeep : ∀ i < 6, i ≠ 2 → ∀ c, asmBrPart X b x i c → mem c = mem' c := fun i hi hi2 c hc =>
    (hfr c (hfoot c ⟨i, hi, hc⟩) (hdisj i hi 2 (by decide) hi2 c hc)).symm
  have hrec : ∀ k < ASM_BR_SIZE, mem' (b + k) = mem (b + k) := fun k hk =>
    (hkeep 0 (by decide) (by decide) _ ⟨by omega, by omega⟩).symm
  have hR' := (readRep_local x.vCap x.eCap x.tCap x.L_w P x.readH x.yRead.view x.yRead mem mem'
    (hkeep 1 (by decide) (by decide))).1 hR
  have hO' := (outGraphRep_local x.vCap x.eCap x.outH a.tr.S_cur x.gOut mem mem'
    (hkeep 3 (by decide) (by decide))).1 hO
  have hT' := asmBrTourView_keep hTR a (s := x.sTour) (hkeep 4 (by decide) (by decide))
  have hX' := hX x.restH a x.xRest mem mem' (hkeep 5 (by decide) (by decide))
  obtain ⟨hdisj', hfoot'⟩ := asmBr_disjoint_of_part (k := 2) (hEnd := hEnd)
    (x' := { x with yEmb := y' }) hdisj hfoot asmBrPart_setEmb hnew
  refine ⟨⟨(hrec _ (by decide)).trans h0, (hrec _ (by decide)).trans h1,
    (hrec _ (by decide)).trans h2, (hrec _ (by decide)).trans h3, (hrec _ (by decide)).trans h4,
    (hrec _ (by decide)).trans h5, (hrec _ (by decide)).trans h6, (hrec _ (by decide)).trans h7,
    (hrec _ (by decide)).trans h8, hG, hlsf, hS, hinv, hR', ?_, ?_, ?_, hO', hT'.1 hT, hmarks,
    hX'.1 hXr, hV, hcap, hLw, hdisj'⟩, hfoot', ?_⟩
  · show (embRep x.eCap).rep x.embH y'.view y' mem'
    rw [hview]; exact hE'
  · show _ ⊆ y'.view.dom; rw [hview]; exact hdom
  · show ∀ e ∈ _, y'.view.emb e = _; rw [hview]; exact hemb
  · show readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem' + X.phi x.restH x.xRest mem' =
      readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem + X.phi x.restH x.xRest mem
    rw [hT'.2, hX'.2]

/-! ## The readouts -/

section Readouts

variable {depth w : ℕ} {fmt : Num.Format w} {L capExp : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {X : DSRep (AsmBranchAbs depth)}

/-- **Readout `2` of a branch** (the clause `readLSF_runs` of `AsmBranchAt`). The dispatch calls
the LSF readout of the readout data (`readRep_readLSF`). It writes the four pointers of `LSFAt`
for `tr.cs.lsf` on the edges of `tr.cs.G`, and the limb count `L_w` at `h + 4`, which the
representation bounds by `L + (capExp + 128) · (⌊log₂ (M + N + 2)⌋ + 1)`. -/
theorem asmBr_readLSF_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {p : Program} {f fRL : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRL ASM_BR_READ))
    (hRL : p.procs[fRL]? = some readLSFStmt) :
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : (asmBrRep TR X fmt.precision L capExp).τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → tr.m₀ = M → tr.n₀ = N →
      (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, (asmBrRep TR X fmt.precision L capExp).foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 5 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.tCap = x.tCap ∧ x'.L_w = x.L_w ∧
        x'.xRest = x.xRest ∧
        (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ forestVCap forestECap,
          st'.mem (h + 4) ≤
            L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
          LSFAt st'.mem h forestVCap forestECap fmt.limbBits (st'.mem (h + 4)) fmt.precision
            tr.cs.G.E tr.cs.lsf) ∧
        (asmBrRep TR X fmt.precision L capExp).Respects
          ((asmBrRep TR X fmt.precision L capExp).foot brH x) h 5 mem o.value brH x' st'.mem ∧
        c + (asmBrRep TR X fmt.precision L capExp).phi brH x' st'.mem ≤
          asmBrReadoutCost + (asmBrRep TR X fmt.precision L capExp).phi brH x mem := by
  intro brH h M N vCap eCap tr ord x mem pos ω hfmt hM hN hrep hfoot _ _ hz hroom
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨h0, -, -, -, -, -, -, -, -, hG, hlsf, -, -, hR, -, -, -, -, -, -, -, -, -, hLw, -⟩ :=
    id hrepA
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hR', hout, hlo, hhi, hz', hfr, hnew, hcost⟩ :=
    readRep_readLSF (mul := 80) hRL le_rfl x.readH h x.yRead.view x.yRead mem pos ω hR
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
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yRead := y' }, hrun, rfl, rfl,
    rfl, rfl, rfl, hmem ▸ hrep',
    ?_, ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨1, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · obtain ⟨hL4, ⟨fV, fE, hlsfAt⟩, -⟩ := hout
    refine ⟨fV, fE, ?_, ?_⟩
    · rw [hmem, hL4, ← hM, ← hN]; exact hLw
    · rw [hmem, hL4, hfmt, ← hG, ← hlsf]; exact hlsfAt
  · show c₁ + 9 + asmBrPhi X { x with yRead := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    rw [hphiR] at hcost
    simp only [asmBrReadoutCost]
    omega

/-- **Readout `3` of a branch** (the clause `readS_runs` of `AsmBranchAt`). The dispatch calls
the readout of `S` of the readout data (`readRep_readS`). It writes a pointer to `S_cur` in
`DynGraphAt` form at `h`. -/
theorem asmBr_readS_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {p : Program} {f fRS : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRS ASM_BR_READ))
    (hRS : p.procs[fRS]? = some readSStmt) :
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : (asmBrRep TR X fmt.precision L capExp).τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, (asmBrRep TR X fmt.precision L capExp).foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.tCap = x.tCap ∧ x'.L_w = x.L_w ∧
        x'.xRest = x.xRest ∧
        (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ graphVCap graphECap, DynGraphAt st'.mem (st'.mem h) graphVCap graphECap tr.S_cur) ∧
        (asmBrRep TR X fmt.precision L capExp).Respects
          ((asmBrRep TR X fmt.precision L capExp).foot brH x) h 1 mem o.value brH x' st'.mem ∧
        c + (asmBrRep TR X fmt.precision L capExp).phi brH x' st'.mem ≤
          asmBrReadoutCost + (asmBrRep TR X fmt.precision L capExp).phi brH x mem := by
  intro brH h vCap eCap tr ord x mem pos ω hrep hfoot _ _ hz hroom
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨h0, -, -, -, -, -, -, -, -, -, -, hS, -, hR, -⟩ := id hrepA
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hR', hout, hlo, hhi, hz', hfr, hnew, hcost⟩ :=
    readRep_readS (mul := 20) hRS le_rfl x.readH h x.yRead.view x.yRead mem pos ω hR
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
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yRead := y' }, hrun, rfl, rfl,
    rfl, rfl, rfl, hmem ▸ hrep',
    ?_, ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨1, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · obtain ⟨gV, gE, hg⟩ := hout
    refine ⟨gV, gE, ?_⟩
    rw [hmem, ← hS]; exact hg
  · show c₁ + 9 + asmBrPhi X { x with yRead := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    rw [hphiR] at hcost
    simp only [asmBrReadoutCost]
    omega

/-- **Readout `4` of a branch** (the clause `readEmb_runs` of `AsmBranchAt`). The dispatch calls
the readout of the embedding table (`embRead_ends`). It writes the table pointer and `eCap` at
`h`; the table holds the walk `tr.emb e` of every edge of the core graph, which is
`EmbeddingReadoutAt` (`ReadEmbOut.mEmbAt`). -/
theorem asmBr_readEmb_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {p : Program} {f fRE : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRE ASM_BR_EMB))
    (hRE : p.procs[fRE]? = some embReadStmt) :
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : (asmBrRep TR X fmt.precision L capExp).τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, (asmBrRep TR X fmt.precision L capExp).foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 2 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.tCap = x.tCap ∧ x'.L_w = x.L_w ∧
        x'.xRest = x.xRest ∧
        (asmBrRep TR X fmt.precision L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        EmbeddingReadoutAt st'.mem h (st'.mem (h + 1)) tr.cs.G tr.cs.lsf tr.emb ∧
        (asmBrRep TR X fmt.precision L capExp).Respects
          ((asmBrRep TR X fmt.precision L capExp).foot brH x) h 2 mem o.value brH x' st'.mem ∧
        c + (asmBrRep TR X fmt.precision L capExp).phi brH x' st'.mem ≤
          asmBrReadoutCost + (asmBrRep TR X fmt.precision L capExp).phi brH x mem := by
  intro brH h vCap eCap tr ord x mem pos ω hrep hfoot hb _ hz hroom
  have hrepA : AsmBrRepAt TR X fmt.precision L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨-, h1, -, -, -, -, -, -, -, -, -, -, -, -, hE, hdom, hemb, -⟩ := id hrepA
  have hembH : x.embH < 2 ^ w := lt_of_lt_of_le (hfootA x.embH ⟨2, by decide,
    Or.inl ⟨le_rfl, by omega⟩⟩) (by omega)
  obtain ⟨body₁, hbody₁, o₁, st₁, c₁, y', hrun₁, hE', hout, hlo, hhi, hz', hfr, hnew, hcost⟩ :=
    embRead_ends hRE hembH hroom hE (fun c hc => hfootA c ⟨2, by decide, hc⟩) hz
      (pos := pos) (ω := ω)
  rw [hRE] at hbody₁
  cases hbody₁
  rw [← h1] at hrun₁
  obtain ⟨st', hrun, hmem⟩ := asmBrReadStmt_runs hRE
    (by have : ASM_BR_EMB < ASM_BR_SIZE := by decide
        omega) hrun₁
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_emb (hEnd := o₁.value) hTR hX hrepA hfootA
    hE' hfr hnew
  refine ⟨_, hp, .returned o₁.value, st', c₁ + 9, { x with yEmb := y' }, hrun, rfl, rfl,
    rfl, rfl, rfl, hmem ▸ hrep',
    ?_, ⟨hlo, hhi, hmem ▸ hz', fun c hc hn => hmem ▸ hfr c hc fun hr => hn ⟨2, by decide, hr⟩,
      hfoot'⟩, ?_⟩
  · rw [hmem]
    exact hout.mEmbAt hdom hemb
  · show c₁ + 9 + asmBrPhi X { x with yEmb := y' } st'.mem ≤ asmBrReadoutCost + asmBrPhi X x mem
    rw [hmem, hphi']
    simp only [asmBrReadoutCost]
    omega

end Readouts

end MinCostFlow.SparseCore.Program
