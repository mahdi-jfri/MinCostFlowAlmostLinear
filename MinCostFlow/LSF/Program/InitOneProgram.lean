module

public import MinCostFlow.LSF.Program.InitOneModel
public import MinCostFlow.LSF.Program.InitOneProc
public import MinCostFlow.LSF.Program.InitProgram
public import MinCostFlow.LSF.Program.InitSegA
public import MinCostFlow.LSF.Program.InitAux
public import MinCostFlow.LSF.Program.InitHeader
import Mathlib.Tactic.Linarith

/-!
# The program of `Initialize`, one-vertex path (`n₀ = 1`)

`lsfInit_one_runs` proves that when `G₀` has a single vertex (`mem (g0Ptr + dgNOff) = 1`),
`oneBody` runs and its final memory represents a valid `initLSFWith` state matching `LSFRep`,
`lsfInitPost`, `Respects`, and `c + phi + 20 ≤ lsfInitCost`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num InitDriver

@[expose] public section

/-- State header arguments on the one-vertex path (reads `r₀` from register `31`). -/
def oneLsfHdrArgs (h : ℕ) : List Expr :=
  [r rB, r rVc, r rEc, r rN, r rM, r rGP, r rTP, r rFP, r rFA, r rWP, r rNumSt, r rDenSt, r rLw,
    k h, r rPfp, r rLin, k 0, ld (r rFA), k 0, r rAux, r rEnd, r 31, r rKn, r rTM, k 0]

/-- Steps `19 … 27` of the one-vertex initialization path. -/
def oneTail (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) : List DStep :=
  [ .call I.prep [r rG0, r rVc, r rEc, r rKn, r rAux, r rGP, r rEnd, r rN, r rM,
      add (add (add (r rG0) (k 4)) (mul (k 7) (ld (add (r rG0) (k dgVCapOff)))))
        (ld (add (r rG0) (k dgECapOff))),
      add (add (r rAux) (k auxHdrSize)) (r rVc)],
    .assign (add (add (r rAux) (k auxHdrSize)) (r rVc)),
    .assign (ld (r 30)),
    .call bBlocks [r rTP, r rFP, r rFA, r rWP, r rVc, r rEc, r 31],
    .call bWstr [add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (r rEc),
      r rM, r rNumSt, r rDenSt, r rLw],
    .call bStore8 [add (r 30) (k 1), k 0, k 0, k 0, k 0, k 0, k 0, k 0, k 0],
    .call I.store20 auxHdrArgs,
    .call I.store24 (oneLsfHdrArgs h),
    .assign (add (r rEnd) (k 3)) ]

/-- All steps of the one-vertex initialization path. -/
def oneSteps (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) : List DStep :=
  segA I ++ oneTail I bBlocks bWstr bStore8 h

/-- The body of the one-vertex initialization path. -/
def oneBody (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) : Stmt :=
  dseqStmt 10 37 0 (oneSteps I bBlocks bWstr bStore8 h)

lemma oneBody_noRand (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) :
    (oneBody I bBlocks bWstr bStore8 h).NoRand :=
  dseqStmt_noRand _ _ _ _

private lemma oneLsfHdr_eval {w h P_fp kk r0 : ℕ} {regs mem : ℕ → ℕ} (V : InitVals)
    (hh : h < 2 ^ w)
    (r4 : regs 4 = P_fp) (r5 : regs 5 = kk) (r6 : regs 6 = V.L_w) (r3 : regs 3 = V.L_in)
    (r7 : regs 7 = V.vCap) (r8 : regs 8 = V.eCap) (r9 : regs 9 = V.b)
    (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0) (a12 : regs 12 = V.tM)
    (a20 : regs 20 = V.gPtr) (a21 : regs 21 = V.tPtr) (a22 : regs 22 = V.fPtr)
    (a23 : regs 23 = V.fAncPtr) (a24 : regs 24 = V.wPtr) (a25 : regs 25 = V.auxPtr)
    (a26 : regs 26 = V.numSt) (a27 : regs 27 = V.denSt) (a28 : regs 28 = V.endA)
    (a31 : regs 31 = r0) :
    evalArgsAt w regs mem (oneLsfHdrArgs h) =
      some (V.b :: lsfHdrVals V h P_fp kk (mem V.fAncPtr) r0) := by
  show evalArgs _ _ _ = _
  dsimp only [oneLsfHdrArgs, lsfHdrVals, rB, rVc, rEc, rN, rM, rGP, rTP, rFP, rFA, rWP, rNumSt,
    rDenSt, rLw, rPfp, rLin, rAux, rEnd, rKn, rTM]
  eval_expr

private lemma one_auxAt {V : InitVals} {r0 : ℕ} {S : LSFState} {mem₆ : ℕ → ℕ}
    (hn1 : V.n0 = 1) (htM0 : V.tM = 0)
    (hTV : S.T₀.V = {r0}) (hGV : S.G.V = {r0}) (hr0S : S.r₀ = r0) (horig : S.origVert = id)
    (hhdr : AuxHeader mem₆ V.auxPtr V.vCap V.n0) (hr0idx : mem₆ (V.auxPtr + auxOffR0Idx) = 0)
    (hvL : mem₆ (auxVListBase V.auxPtr V.vCap) = r0)
    (hvIdx1 : mem₆ (auxVIdxBase V.auxPtr + r0) = 1)
    (hvIdx0 : ∀ v < V.vCap, v ≠ r0 → mem₆ (auxVIdxBase V.auxPtr + v) = 0)
    (hZero8 : ∀ i < 8, mem₆ (auxVListBase V.auxPtr V.vCap + 1 + i) = 0)
    (hIsOrig : ∀ v < V.vCap, mem₆ (auxIsOrigVertBase V.auxPtr V.vCap V.n0 + v) = if v = r0 then 1 else 0)
    (hOrig : mem₆ (auxOrigVertBase V.auxPtr V.vCap V.n0 + r0) = r0)
    (hVis : ∀ v < V.vCap, mem₆ (auxVisABase V.auxPtr V.vCap V.n0 + v) = 0 ∧
      mem₆ (auxVisBBase V.auxPtr V.vCap V.n0 + v) = 0) :
    AuxAt mem₆ V.auxPtr V.vCap V.n0 V.tM S [] [r0]
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  have hlog : auxLogCap V.n0 = 2 := by rw [hn1]; decide
  have hlog1 : auxLogCap 1 = 2 := by decide
  have hz : ∀ off < 8, mem₆ (auxT0ParentBase V.auxPtr V.vCap V.n0 + off) = 0 := by
    intro off hoff
    have heq : auxT0ParentBase V.auxPtr V.vCap V.n0 = auxVListBase V.auxPtr V.vCap + 1 := by
      simp [auxT0ParentBase, hn1]
    rw [heq]; exact hZero8 off hoff
  have hbase_pti : auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 = auxT0ParentBase V.auxPtr V.vCap V.n0 + 1 := by
    simp [auxT0ParentTreeIdxBase, hn1]
  have hbase_dep : auxT0DepthBase V.auxPtr V.vCap V.n0 = auxT0ParentBase V.auxPtr V.vCap V.n0 + 2 := by
    simp [auxT0DepthBase, auxT0ParentTreeIdxBase, hn1]
  have hbase_upV : auxUpVBase V.auxPtr V.vCap V.n0 = auxT0ParentBase V.auxPtr V.vCap V.n0 + 3 := by
    simp [auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, hn1]
  have hbase_upM : auxUpMinIdxBase V.auxPtr V.vCap V.n0 = auxT0ParentBase V.auxPtr V.vCap V.n0 + 5 := by
    simp only [auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, hn1, hlog1, Nat.one_mul]
  have hbase_th : auxThParentBase V.auxPtr V.vCap V.n0 = auxT0ParentBase V.auxPtr V.vCap V.n0 + 7 := by
    simp only [auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, hn1, hlog1, Nat.one_mul]
  rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    by simp [hn1], List.nodup_singleton r0, by simp [hTV], by simp [htM0], ?_, ?_, ?_,
    by rw [hr0idx, hn1]; omega, by rw [hr0idx, hr0S]; rfl, ?_, ?_, ?_, ?_, ?_,
    by rw [hr0idx], rfl, ?_, ?_, ?_, ?_, ?_, hVis⟩
  · intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi; simpa using hvL
  · intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi; simpa using hvIdx1
  · intro v hv hnot
    exact hvIdx0 v hv (by simpa [hTV] using hnot)
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨by simpa using hz 0 (by decide), by omega⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨by rw [hbase_pti, Nat.add_zero]; exact hz 1 (by decide), fun h => by omega⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hbase_dep, Nat.add_zero]; exact hz 2 (by decide)
  · intro i hi j hj
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hlog] at hj
    refine ⟨?_, by omega, ?_, fun h => by omega⟩
    · rw [hbase_upV, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]
      exact hz (3 + j) (by omega)
    · rw [hbase_upM, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]
      exact hz (5 + j) (by omega)
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨by rw [hbase_th, Nat.add_zero]; exact hz 7 (by decide), by omega⟩
  · intro i hi hne
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    rw [hr0idx] at hne; omega
  · intro i hi j hj
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun hne => False.elim (hne rfl)⟩
  · intro i hi hne
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    rw [hr0idx] at hne; omega
  · intro v hv
    rw [hIsOrig v hv, hTV]; simp
  · intro u hu _
    rw [hGV, Finset.mem_singleton] at hu; subst hu
    simpa [horig] using hOrig

private lemma one_cost_le {Q_AN : Program} {c_AN m0 L_in L_w h : ℕ} {K_AN : ℝ}
    (hh : 1 ≤ h) :
    segACost 1 + (20 * Nat.log 2 1 + 20 * Nat.log 2 2 + 640 * 1 + 920 * m0 + 600) +
      600 + (80 * m0 + 50) + 2000 + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 22 ≤
      lsfInitCostFactor *
        Nat.ceil (((m0 + 1 + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN 1 m0 L_in L_w h) := by
  have hlg1 : Nat.log 2 1 = 0 := by decide
  have hlg2 : Nat.log 2 2 = 1 := by decide
  have hlg3 : Nat.log 2 3 = 1 := by decide
  have hsegA : segACost 1 = 640 := by unfold segACost; rw [hlg2]
  have hF1 : 1 ≤ lsfOverhead Q_AN c_AN K_AN 1 m0 L_in L_w h :=
    lsfOverhead_ge_one Q_AN c_AN K_AN 1 m0 L_in L_w h hh
  have hceil : m0 + 1 + 1 ≤
      Nat.ceil (((m0 + 1 + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN 1 m0 L_in L_w h) := by
    have hR : ((m0 + 1 + 1 : ℕ) : ℝ) ≤
        ((m0 + 1 + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN 1 m0 L_in L_w h :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hF1
    exact Nat.le_ceil _ |> fun hc => by exact_mod_cast hR.trans hc
  rw [hsegA, hlg1, hlg2, hlg3]
  unfold lsfInitCostFactor
  omega

private lemma one_endA_add_three_le_space (Q_AN : Program) (K_AN : ℝ) (c_AN h : ℕ) (V : InitVals)
    (hn1 : V.n0 = 1) :
    V.endA + 3 ≤ V.b + initSpaceV Q_AN K_AN c_AN h V := by
  have htM : V.tM = 0 := by show V.n0 - 1 = 0; omega
  have hst : lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w ≤
      lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w := by
    unfold lsfStaticSize tBlockSize dynGraphSize
    omega
  show V.b + lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w + 3 ≤
    V.b + initSpaceV Q_AN K_AN c_AN h V
  unfold initSpaceV
  omega

/-- Assemble `LSFRep`, `lsfInitPost`, `Respects`, and the potential bound on the one-vertex path
from the stage postconditions. -/
private lemma one_build_rep {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (V : InitVals) {G₀ : MGraph}
    {g0Ptr vCap0 eCap0 lenArr wtArr P_fp kk r0 : ℕ} {eL : List ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ mem₆ : ℕ → ℕ} {v₅ v₆ : ℕ}
    (hVn1 : V.n0 = 1) (hVtM0 : V.tM = 0)
    (hGn1 : G₀.n = 1) (hGm : G₀.E.card = V.m0)
    (hh : 1 ≤ h) (hLin : 1 ≤ V.L_in) (hLinw : V.L_in ≤ V.L_w) (h2Lw : 2 ≤ h * V.L_w)
    (hk : 1 ≤ kk) (hec1 : 1 ≤ V.eCap) (hm0 : V.m0 ≤ V.eCap)
    (hG₀ : G₀.IsValid) (hVne : G₀.V.Nonempty) (hr0_mem : r0 ∈ G₀.V) (hr0_lt : r0 < V.vCap)
    (hGV_eq : G₀.V = {r0}) (hElt : ∀ e ∈ G₀.E, e < V.eCap)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hℓpos : ∀ e ∈ G₀.E, 0 < memArrayReal mem lenArr G₀ h V.L_in P_fp e)
    (hvpos : ∀ e ∈ G₀.E, 0 < memArrayReal mem wtArr G₀ h V.L_in P_fp e)
    (hz : ZeroFrom mem V.b)
    (hdgG₂ : DynGraphAt mem₂ V.gPtr V.vCap V.eCap G₀)
    (hr0_at : mem₁ (auxVListBase V.auxPtr V.vCap) = r0)
    (hvIdx1 : mem₁ (auxVIdxBase V.auxPtr + r0) = 1)
    (hvIdx0 : ∀ u < V.vCap, u ∉ G₀.V → mem₁ (auxVIdxBase V.auxPtr + u) = 0)
    (hIsOrig₁ : ∀ u < V.vCap, mem₁ (auxIsOrigVertBase V.auxPtr V.vCap V.n0 + u) = if u ∈ G₀.V then 1 else 0)
    (hOrig₁ : mem₁ (auxOrigVertBase V.auxPtr V.vCap V.n0 + r0) = r0)
    (hVis₁ : ∀ u < V.vCap, mem₁ (auxVisABase V.auxPtr V.vCap V.n0 + u) = 0 ∧
      mem₁ (auxVisBBase V.auxPtr V.vCap V.n0 + u) = 0)
    (hfr₁ : ∀ a, (a < V.gPtr ∨ V.gPtr + dynGraphSize V.vCap V.eCap ≤ a) →
      (a < V.auxPtr ∨ V.auxPtr + auxSize V.vCap V.n0 ≤ a) →
      (a < V.endA ∨ V.endA + 3 ≤ a) → mem₁ a = mem a)
    (hT₂ : ∀ G T₀ : MGraph, G.V = {r0} → T₀.V = {r0} → T₀.E = ∅ →
      TBlockAt mem₂ V.tPtr V.vCap V.eCap 0 G T₀ T₀ (fun _ => 0) [])
    (hdgF₂ : ∀ F : MGraph, F.V = {r0} → F.E = ∅ →
      DynGraphAt mem₂ V.fPtr V.vCap (fECap V.eCap 1) F)
    (hFA₂ : ∀ RF : RootedForest, RF.F.V = {r0} → RF.F.E = ∅ → RF.R = {r0} →
      FAncAt mem₂ V.fAncPtr V.vCap RF [r0] (fun _ => r0) (fun _ => r0) (fun _ => 1) {r0})
    (hW₂ : ∀ F : MGraph, WBlockAt mem₂ V.wPtr 1 ∅ F)
    (hfr₂ : ∀ a, a < V.tPtr ∨ V.wPtr + wBlockSize 1 ≤ a → mem₂ a = mem₁ a)
    (heLlen : eL.length = V.m0) (heLmem : ∀ e, e ∈ eL ↔ e ∈ G₀.E)
    (heLat : ∀ i (hi : i < eL.length), mem₂ (dgEListBase V.gPtr V.vCap V.eCap + i) = eL[i])
    (hwstr₃ : ∀ i < V.m0,
      Num.Valid mem₃ (V.numSt + mem₂ (dgEListBase V.gPtr V.vCap V.eCap + i) * V.L_w) h V.L_w ∧
      Num.intVal mem₃ (V.numSt + mem₂ (dgEListBase V.gPtr V.vCap V.eCap + i) * V.L_w) h V.L_w = 6 ∧
      Num.Valid mem₃ (V.denSt + mem₂ (dgEListBase V.gPtr V.vCap V.eCap + i) * V.L_w) h V.L_w ∧
      Num.intVal mem₃ (V.denSt + mem₂ (dgEListBase V.gPtr V.vCap V.eCap + i) * V.L_w) h V.L_w = 1)
    (hfr₃ : ∀ a, a < V.numSt ∨ V.endA ≤ a → mem₃ a = mem₂ a)
    (hZero8_4 : ∀ i < 8, mem₄ (auxVListBase V.auxPtr V.vCap + 1 + i) = ([0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD i 0)
    (hfr₄ : ∀ a, a < auxVListBase V.auxPtr V.vCap + 1 ∨ auxVListBase V.auxPtr V.vCap + 1 + 8 ≤ a →
      mem₄ a = mem₃ a)
    (h₅ : (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem₄ v₅ mem₅)
    (hfr₅ : ∀ a, a < V.auxPtr ∨ V.auxPtr + 20 ≤ a → mem₅ a = mem₄ a)
    (h₆ : (storeArgsContract w 24).post (V.b :: lsfHdrVals V h P_fp kk 1 r0) mem₅ v₆ mem₆)
    (hfr₆ : ∀ a, a < V.b ∨ V.b + 24 ≤ a → mem₆ a = mem₅ a)
    (hsp_eq : lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, V.L_in, P_fp, kk, V.L_w, V.vCap, V.eCap, V.b] mem =
      initSpaceV Q_AN K_AN c_AN h V) :
    ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep V.b s' x' mem₆ ∧
      lsfInitPost K_AN h [g0Ptr, lenArr, wtArr, V.L_in, P_fp, kk, V.L_w, V.vCap, V.eCap, V.b] mem s' mem₆ ∧
      (LSFRep h).Respects (fun _ => False) V.b
        (lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, V.L_in, P_fp, kk, V.L_w, V.vCap, V.eCap, V.b] mem)
        mem (V.endA + 3) V.b x' mem₆ ∧
      (LSFRep h).phi V.b x' mem₆ ≤ 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) := by
  classical
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := V.static_le
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hwa_eq : V.wPtr + wBlockSize 1 = V.auxPtr := by rw [← hVn1]; exact e10
  have haux_orig : auxOrigVertBase V.auxPtr V.vCap 1 = auxVListBase V.auxPtr V.vCap + 9 := by
    have hlog1 : auxLogCap 1 = 2 := by decide
    simp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, hlog1]
  have haux_orig_le : auxVListBase V.auxPtr V.vCap + 9 ≤ V.auxPtr + auxSize V.vCap V.n0 := by
    rw [hVn1, ← haux_orig]
    dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]
    omega
  have hvL_eq : V.auxPtr + 20 + V.vCap = auxVListBase V.auxPtr V.vCap := s7
  have hdgG_end : V.gPtr + dynGraphSize V.vCap V.eCap ≤ V.tPtr := by
    dsimp [dynGraphSize]; omega
  have h6_eq_2 : ∀ a, V.gPtr ≤ a → a < V.auxPtr → mem₆ a = mem₂ a := fun a ha1 ha2 => by
    rw [hfr₆ a (Or.inr (by omega)), hfr₅ a (Or.inl ha2),
      hfr₄ a (Or.inl (by omega)), hfr₃ a (Or.inl (by omega))]
  have h6_eq_3_wstr : ∀ a, V.numSt ≤ a → a < V.endA → mem₆ a = mem₃ a := fun a ha1 ha2 => by
    rw [hfr₆ a (Or.inr (by omega)), hfr₅ a (Or.inr (by omega)), hfr₄ a (Or.inr (by omega))]
  have h6_eq_1_aux_lo : ∀ a, V.auxPtr + 20 ≤ a → a < auxVListBase V.auxPtr V.vCap + 1 →
      mem₆ a = mem₁ a := fun a ha1 ha2 => by
    rw [hfr₆ a (Or.inr (by omega)), hfr₅ a (Or.inr ha1), hfr₄ a (Or.inl ha2),
      hfr₃ a (Or.inl (by omega)), hfr₂ a (Or.inr (by omega))]
  have h6_eq_1_aux_hi : ∀ a, auxVListBase V.auxPtr V.vCap + 9 ≤ a → a < V.numSt →
      mem₆ a = mem₁ a := fun a ha1 ha2 => by
    rw [hfr₆ a (Or.inr (by omega)), hfr₅ a (Or.inr (by omega)),
      hfr₄ a (Or.inr ha1), hfr₃ a (Or.inl ha2), hfr₂ a (Or.inr (by omega))]
  let v := memArrayReal mem wtArr G₀ h V.L_in P_fp
  let ℓ := memArrayReal mem lenArr G₀ h V.L_in P_fp
  let S := initLSFWith G₀ ℓ v (kk : ℝ) (oneVertTree r0) r0 {r0} (fun _ => 0) ∅
    (defaultThreshNat K_AN G₀.n kk : ℝ)
  have hp := oneVert_validLSFParams (K_AN := K_AN) (ℓ := ℓ) (v := v) hG₀ hGn1 hr0_mem hk
  have hSinv : LSFStructInv S :=
    LSFInvWith.toStructInv (initLSFWith_inv hG₀ hVne hℓpos hvpos (by exact_mod_cast hk) hp)
  have hf := oneVert_initLSFWith_fields (K_AN := K_AN) (ℓ := ℓ) (v := v) hG₀ hGn1 hr0_mem hk
  rcases hf with ⟨hSG₀, hSG, hSr₀, hSπ, hSnum, hSorig, hST₀V, hST₀E, hSTcur,
    hSR0, hSRorig, hSR, hSRFR, hSRFFV, hSRFFE, hSW, hSwstr⟩
  let x : LSFConcrete :=
    { vCap := V.vCap, eCap := V.eCap, n0 := 1, m0 := V.m0, tM := 0,
      h := h, P_fp := P_fp, L_in := V.L_in, L_w := V.L_w, k_nat := kk,
      tOrigList := [], vList := [r0],
      t0Parent := fun _ => 0, t0ParentTreeIdx := fun _ => 0, t0Depth := fun _ => 0,
      thParent := fun _ => 0, upV := fun _ _ => 0, upMinIdx := fun _ _ => 0,
      rList := [r0], compId := fun _ => r0, compRoot := fun _ => r0, compSize := fun _ => 1,
      activeCids := {r0} }
  have hhdr_S : lsfHeaderAt mem₆ V.b S x :=
    init_lsfHeader h₆ rfl rfl hVn1.symm rfl hVtM0.symm rfl rfl rfl
      rfl rfl (by rw [hSR]; simp) hSnum hSr₀
  have hdgG_S : DynGraphAt mem₆ (lsfDgGPtr V.b) x.vCap x.eCap S.G := by
    rw [hSG]
    exact hdgG₂.of_agree fun a ha1 ha2 => h6_eq_2 a ha1 (by omega)
  have hT_S : TBlockAt mem₆ (lsfTBlockPtr V.b x.vCap x.eCap) x.vCap x.eCap x.tM
      S.G S.T_cur S.T₀ S.π x.tOrigList := by
    dsimp only [x]
    rw [hSTcur, hSπ]
    exact (hT₂ S.G S.T₀ (by rw [hSG]; exact hGV_eq) hST₀V hST₀E).of_agree fun a ha1 ha2 =>
      h6_eq_2 a (by omega) (by rw [← hVtM0] at ha2; omega)
  have hdgF_S : DynGraphAt mem₆ (lsfDgFPtr V.b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0)
      S.RF.F := by
    dsimp only [x]
    have hfp_eq : lsfDgFPtr V.b V.vCap V.eCap 0 = V.fPtr := by
      show lsfDgFPtr V.b V.vCap V.eCap 0 = lsfDgFPtr V.b V.vCap V.eCap V.tM; rw [hVtM0]
    rw [hfp_eq]
    exact (hdgF₂ S.RF.F hSRFFV hSRFFE).of_agree fun a ha1 ha2 =>
      h6_eq_2 a (by omega) (by rw [← hVn1] at ha2; omega)
  have hFA_S : FAncAt mem₆ (lsfFAncPtr V.b x.vCap x.eCap x.n0 x.tM) x.vCap S.RF
      x.rList x.compId x.compRoot x.compSize x.activeCids := by
    dsimp only [x]
    have hfa_eq : lsfFAncPtr V.b V.vCap V.eCap 1 0 = V.fAncPtr := by
      show lsfFAncPtr V.b V.vCap V.eCap 1 0 = lsfFAncPtr V.b V.vCap V.eCap V.n0 V.tM; rw [hVn1, hVtM0]
    rw [hfa_eq]
    exact (hFA₂ S.RF hSRFFV hSRFFE hSRFR).of_agree fun a ha1 ha2 =>
      h6_eq_2 a (by omega) (by omega)
  have hW_S : WBlockAt mem₆ (lsfWBlockPtr V.b x.vCap x.eCap x.n0 x.tM) x.n0 S.W_init
      (forestGivenRoots S.T₀ S.r₀ (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_init) S.π) := by
    dsimp only [x]
    have hw_eq : lsfWBlockPtr V.b V.vCap V.eCap 1 0 = V.wPtr := by
      show lsfWBlockPtr V.b V.vCap V.eCap 1 0 = lsfWBlockPtr V.b V.vCap V.eCap V.n0 V.tM; rw [hVn1, hVtM0]
    rw [hw_eq, hSW]
    exact (hW₂ _).of_agree fun a ha1 ha2 => h6_eq_2 a (by omega) (by omega)
  have hwstr_S : WstrAt mem₆ (lsfWstrNumPtr V.b x.vCap x.eCap x.n0 x.tM)
      (lsfWstrDenPtr V.b x.vCap x.eCap x.n0 x.tM x.L_w) x.eCap x.h x.L_w S.G S.wstr := by
    dsimp only [x]
    refine ⟨h2Lw, by omega, fun e he => ?_⟩
    rw [hSG] at he
    have he_lt := hElt e he
    obtain ⟨i, hi, he_eq⟩ := List.mem_iff_getElem.mp ((heLmem e).mpr he)
    have h3e := hwstr₃ i (by omega)
    rw [heLat i hi, he_eq] at h3e
    have heLw : e * V.L_w + V.L_w ≤ V.eCap * V.L_w := by
      have := Nat.mul_le_mul_right V.L_w he_lt
      rwa [Nat.succ_mul] at this
    have hconN : ∀ j < V.L_w, mem₆ (V.numSt + e * V.L_w + j) = mem₃ (V.numSt + e * V.L_w + j) :=
      fun j hj => h6_eq_3_wstr _ (by omega) (by omega)
    have hconD : ∀ j < V.L_w, mem₆ (V.denSt + e * V.L_w + j) = mem₃ (V.denSt + e * V.L_w + j) :=
      fun j hj => h6_eq_3_wstr _ (by omega) (by omega)
    have hVN : Num.Valid mem₆ (V.numSt + e * V.L_w) h V.L_w :=
      fun j hj => by rw [hconN j hj]; exact h3e.1 j hj
    have hVD : Num.Valid mem₆ (V.denSt + e * V.L_w) h V.L_w :=
      fun j hj => by rw [hconD j hj]; exact h3e.2.2.1 j hj
    have hIN : Num.intVal mem₆ (V.numSt + e * V.L_w) h V.L_w = 6 := by
      rw [Num.intVal_congr hconN]; exact h3e.2.1
    have hID : Num.intVal mem₆ (V.denSt + e * V.L_w) h V.L_w = 1 := by
      rw [Num.intVal_congr hconD]; exact h3e.2.2.2
    have hnum_eq : lsfWstrNumPtr V.b V.vCap V.eCap 1 0 = V.numSt := by
      show lsfWstrNumPtr V.b V.vCap V.eCap 1 0 = lsfWstrNumPtr V.b V.vCap V.eCap V.n0 V.tM
      rw [hVn1, hVtM0]
    have hden_eq : lsfWstrDenPtr V.b V.vCap V.eCap 1 0 V.L_w = V.denSt := by
      show lsfWstrDenPtr V.b V.vCap V.eCap 1 0 V.L_w = lsfWstrDenPtr V.b V.vCap V.eCap V.n0 V.tM V.L_w
      rw [hVn1, hVtM0]
    rw [hnum_eq, hden_eq]
    refine ⟨he_lt, hVN, hVD, by rw [hIN]; omega, by rw [hID], ?_⟩
    rw [hIN, hID, hSwstr e he]
    norm_num
  have hAux_S : AuxAt mem₆ (lsfAuxPtr V.b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 x.tM S
      x.tOrigList x.vList x.t0Parent x.t0ParentTreeIdx x.t0Depth x.thParent x.upV x.upMinIdx := by
    dsimp only [x]
    have haux_eq : lsfAuxPtr V.b V.vCap V.eCap 1 0 V.L_w = V.auxPtr := by
      show lsfAuxPtr V.b V.vCap V.eCap 1 0 V.L_w = lsfAuxPtr V.b V.vCap V.eCap V.n0 V.tM V.L_w
      rw [hVn1, hVtM0]
    rw [haux_eq]
    obtain ⟨hhdrA, hr0A⟩ := init_auxHeader h₅ h₆
    have haux_1 := one_auxAt hVn1 hVtM0 hST₀V (by rw [hSG]; exact hGV_eq) hSr₀ hSorig hhdrA hr0A
      ((h6_eq_1_aux_lo _ (by omega) (by omega)).trans hr0_at)
      ((h6_eq_1_aux_lo _ (by dsimp [auxVIdxBase, auxHdrSize]; omega)
        (by dsimp [auxVIdxBase, auxHdrSize]; omega)).trans hvIdx1)
      (fun u hu hne => (h6_eq_1_aux_lo _ (by dsimp [auxVIdxBase, auxHdrSize]; omega)
        (by dsimp [auxVIdxBase, auxHdrSize]; omega)).trans
        (hvIdx0 u hu (by rw [hGV_eq]; simpa using hne)))
      (fun i hi => by
        rw [hfr₆ _ (Or.inr (by omega)), hfr₅ _ (Or.inr (by omega)), hZero8_4 i hi]
        interval_cases i <;> rfl)
      (fun u hu => by
        have hle1 : auxVListBase V.auxPtr V.vCap + 9 ≤ auxIsOrigVertBase V.auxPtr V.vCap V.n0 + u := by
          rw [hVn1, ← haux_orig]; dsimp [auxIsOrigVertBase]; omega
        have hlt2 : auxIsOrigVertBase V.auxPtr V.vCap V.n0 + u < V.numSt := by
          have : auxIsOrigVertBase V.auxPtr V.vCap V.n0 + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 := by
            dsimp [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
              auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
              auxSize]; omega
          omega
        rw [h6_eq_1_aux_hi _ hle1 hlt2, hIsOrig₁ u hu, hGV_eq]; simp)
      (by
        have hle1 : auxVListBase V.auxPtr V.vCap + 9 ≤ auxOrigVertBase V.auxPtr V.vCap V.n0 + r0 := by
          rw [hVn1, ← haux_orig]; omega
        have hlt2 : auxOrigVertBase V.auxPtr V.vCap V.n0 + r0 < V.numSt := by
          have : auxOrigVertBase V.auxPtr V.vCap V.n0 + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 := by
            dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
              auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
              auxSize]; omega
          omega
        exact (h6_eq_1_aux_hi _ hle1 hlt2).trans hOrig₁)
      (fun u hu => by
        have hleA : auxVListBase V.auxPtr V.vCap + 9 ≤ auxVisABase V.auxPtr V.vCap V.n0 + u := by
          rw [hVn1, ← haux_orig]
          dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase]; omega
        have hltA : auxVisABase V.auxPtr V.vCap V.n0 + u < V.numSt := by
          have : auxVisABase V.auxPtr V.vCap V.n0 + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 := by
            dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase,
              auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
              auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
          omega
        have hleB : auxVListBase V.auxPtr V.vCap + 9 ≤ auxVisBBase V.auxPtr V.vCap V.n0 + u := by
          rw [hVn1, ← haux_orig]
          dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase]; omega
        have hltB : auxVisBBase V.auxPtr V.vCap V.n0 + u < V.numSt := by
          have : auxVisBBase V.auxPtr V.vCap V.n0 + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 := by
            dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
              auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
              auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
          omega
        rw [h6_eq_1_aux_hi _ hleA hltA, h6_eq_1_aux_hi _ hleB hltB]
        exact hVis₁ u hu)
    rwa [hVn1, hVtM0] at haux_1
  have hrep : (LSFRep h).rep V.b S x mem₆ :=
    ⟨rfl, hh, hLin, by dsimp [x]; omega, hk, rfl, hSinv, hGn1, hGm, by rw [hST₀E]; simp [x],
      by dsimp [x]; omega, hm0, by dsimp [x]; omega, by dsimp [x]; omega,
      fun u hu => by rw [hST₀V, Finset.mem_singleton] at hu; subst hu; exact hr0_lt,
      hElt, hhdr_S, hdgG_S, hT_S, hdgF_S, hFA_S, hW_S, hwstr_S, hAux_S⟩
  have hpost : lsfInitPost K_AN h [g0Ptr, lenArr, wtArr, V.L_in, P_fp, kk, V.L_w, V.vCap, V.eCap, V.b]
      mem S mem₆ := lsfInitPost_of_rep rfl hdg0 hp hrep rfl rfl rfl
  have hlow6 : ∀ a, a < V.b → mem₆ a = mem a := fun a ha => by
    rw [hfr₆ a (Or.inl ha), hfr₅ a (Or.inl (by omega)), hfr₄ a (Or.inl (by omega)),
      hfr₃ a (Or.inl (by omega)), hfr₂ a (Or.inl (by omega)),
      hfr₁ a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
  have hzero6 : ZeroFrom mem₆ (V.endA + 3) := fun a ha => by
    rw [hfr₆ a (Or.inr (by omega)), hfr₅ a (Or.inr (by omega)), hfr₄ a (Or.inr (by omega)),
      hfr₃ a (Or.inr (by omega)), hfr₂ a (Or.inr (by omega)),
      hfr₁ a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr ha)]
    exact hz a (by omega)
  have hcard : S.T_cur.V.card ≤ x.n0 := by
    rw [hSTcur, hST₀V]; simp [x]
  have hphi : (LSFRep h).phi V.b x mem₆ ≤ 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) :=
    lsfPhi_rep_le hrep hcard
  refine ⟨S, x, hSG₀, hrep, hpost, ⟨by omega, ?_, hzero6, fun a ha _ => hlow6 a ha, ?_⟩, hphi⟩
  · rw [hsp_eq]
    exact one_endA_add_three_le_space Q_AN K_AN c_AN h V hVn1
  · intro a ha
    right
    obtain ⟨ha1, ha2⟩ := ha
    have hx : x.endAddr V.b = V.endA := by
      show lsfEndAddr V.b V.vCap V.eCap 1 0 V.L_w = lsfEndAddr V.b V.vCap V.eCap V.n0 V.tM V.L_w
      rw [hVn1, hVtM0]
    exact ⟨ha1, by omega⟩

set_option maxHeartbeats 800000 in
/-- The one-vertex path of `Initialize` (`n₀ = 1`) for a fixed initial graph `G₀`, also witnessing
`s'.G₀ = G₀`, with `+ 20` cost slack to pay for the top-level branch. -/
theorem lsfInit_one_runs_for {w h : ℕ} {p : Program} {I : InitIdx} {bBlocks bWstr bStore8 : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hblocks : MeetsContract w p bBlocks (initOneBlocksContract w))
    (hwstr : MeetsContract w p bWstr (initOneWstrContract w h))
    (hs8 : MeetsContract w p bStore8 (storeArgsContract w 8))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPreFor c_AN K_AN w h G₀ args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w)
    (hn1_mem : mem (args.getD 0 0 + dgNOff) = 1) :
    ∃ o st' c, Runs w p ω (oneBody I bBlocks bWstr bStore8 h) (startState args mem pos) o st' c ∧
      ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem + 20 ≤
          lsfInitCost Q_AN c_AN K_AN h args mem := by
  classical
  obtain ⟨v₀, ℓ₀, g0Ptr, vCap0, eCap0, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b,
    rfl, hc, hh, hhw, hG₀, hVne, hdg0, hg0, hvc, hec, hec1, hlenB, hwtB, hLin, h2L, hPd, hk, hk3,
    hLinw, h2Lw, hθ, hlv, hwv⟩ := hpre
  have hb : heapArg [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] = b := rfl
  rw [hb] at hz hsp ⊢
  have hn_eq : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  have hm_eq : mem (g0Ptr + dgMOff) = G₀.E.card := hdg0.2.2.2.2.2.2.1
  simp only [List.getD_cons_zero] at hn1_mem
  have hn1 : G₀.n = 1 := hn_eq.symm.trans hn1_mem
  generalize hV : initValsOf G₀ L_in L_w vCap eCap b = V
  have hVb : V.b = b := by rw [← hV]; rfl
  have hVvc : V.vCap = vCap := by rw [← hV]; rfl
  have hVec : V.eCap = eCap := by rw [← hV]; rfl
  have hVm0 : V.m0 = G₀.E.card := by rw [← hV]; rfl
  have hVLw : V.L_w = L_w := by rw [← hV]; rfl
  have hVLin : V.L_in = L_in := by rw [← hV]; rfl
  have hVn0 : V.n0 = G₀.n := by rw [← hV]; rfl
  have hVn1 : V.n0 = 1 := hVn0.trans hn1
  have hVtM0 : V.tM = 0 := by show V.n0 - 1 = 0; omega
  have hsp_eq : lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap,
      eCap, b] mem = initSpaceV Q_AN K_AN c_AN h V := by
    rw [← hV]; exact lsfInitSpace_eq hdg0
  have hspV : V.b + initSpaceV Q_AN K_AN c_AN h V < 2 ^ w := by rw [hVb, ← hsp_eq]; exact hsp
  have hLw : L_w < 2 ^ w := hwords L_w (by simp)
  have hPw : P_fp < 2 ^ w := hwords P_fp (by simp)
  have hLin_w : L_in < 2 ^ w := hwords L_in (by simp)
  have hkk_w : kk < 2 ^ w := hwords kk (by simp)
  have hEndW : V.endA + 6 < 2 ^ w := by
    have hsp1000 : V.b + lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w + 1000 ≤
        V.b + initSpaceV Q_AN K_AN c_AN h V := by
      have hst : lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w ≤
          lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w := by
        unfold lsfStaticSize tBlockSize dynGraphSize; omega
      unfold initSpaceV; omega
    show V.b + lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w + 6 < 2 ^ w
    omega
  have hw32 : 32 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hhw_lt : h < 2 ^ w := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self.le)
  obtain ⟨hn0', hm0'⟩ := dynGraph_card_le hdg0
  have hn0 : V.n0 ≤ V.vCap := by omega
  have hm0 : V.m0 ≤ V.eCap := by omega
  have hVlt : ∀ u ∈ G₀.V, u < V.vCap := fun u hu => by
    have := lt_of_lt_of_le (hdg0.2.1 u hu) hvc; omega
  have hElt : ∀ e ∈ G₀.E, e < V.eCap := fun e he => by
    have := lt_of_lt_of_le (hdg0.2.2.1 e he) hec; omega
  have hℓpos : ∀ e ∈ G₀.E, 0 < memArrayReal mem lenArr G₀ h L_in P_fp e := fun e he => by
    rw [memArrayReal_eq he, (hlv e he).2.1]; exact (hlv e he).2.2
  have hvpos : ∀ e ∈ G₀.E, 0 < memArrayReal mem wtArr G₀ h L_in P_fp e := fun e he => by
    rw [memArrayReal_eq he, (hwv e he).2.1]; exact (hwv e he).2.2
  have h12cap : 12 < capacity h L_w := by
    have h2916 : 2916 ≤ defaultThreshNat K_AN 1 kk := by
      have hC : 9 ≤ defaultC_ceil K_AN := by
        have : 1 ≤ Nat.ceil (max K_AN 1) := Nat.one_le_ceil_iff.mpr (by positivity)
        unfold defaultC_ceil; omega
      have hD : hldDepthBound 1 = 2 := by decide
      have hlg : Nat.log 2 (1 + 2) = 1 := by decide
      have h1 : 2916 ≤ 9 * (hldDepthBound 1 + 1) ^ 2 * defaultC_ceil K_AN *
          (Nat.log 2 (1 + 2) + 1) ^ 2 * kk := by rw [hD, hlg]; nlinarith
      exact h1.trans (Nat.le_max_right _ _)
    rw [hn1] at hθ
    have hpow : 2 ^ (h * (L_w - L_in)) ≤ 2 ^ (h * L_w) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left h (Nat.sub_le _ _))
    have hcap_eq : capacity h L_w = 2 ^ (h * L_w) := by
      unfold capacity base; rw [← pow_mul]
    omega
  have h6len : (natLimbs h 6).length ≤ L_w := by
    rw [natLimbs_length_le_iff (by omega)]
    exact lt_trans (by decide : 6 < 12) h12cap
  -- Budget for oneSteps
  set prepC := 20 * Nat.log 2 1 + 20 * Nat.log 2 2 + 640 * 1 + 920 * V.m0 + 600 with hprepC_def
  set Bsum := segACost 1 + prepC + 600 + (80 * V.m0 + 50) + 2000 with hBsum_def
  set space := lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap,
    eCap, b] mem with hspace
  let Q : ℕ → (ℕ → ℕ) → Prop := fun o mem' =>
    ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep b s' x' mem' ∧
      lsfInitPost K_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem s' mem' ∧
      (LSFRep h).Respects (fun _ => False) b space mem o b x' mem' ∧
      (LSFRep h).phi b x' mem' ≤ 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1)
  have hwp : SeqWP w p 10 37 Q 0 (oneSteps I bBlocks bWstr bStore8 h)
      (startState [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem pos).regs mem
      (Bsum + 2) := by
    unfold oneSteps
    refine segA_wp (upClosed_wp 37 Q) V hlog rfl hVLw.symm hVvc.symm hVec.symm hVb.symm hdg0
      hVn0.symm hVm0.symm (by rw [hVb]; exact hg0) hm0
      hn0 (by omega) hEndW (by rw [hVn1]; omega) ?_
    intro regs₁ hlow₁ hsegA
    have hr0 : regs₁ 0 = g0Ptr := hlow₁ 0 (by omega)
    have hr3 : regs₁ 3 = V.L_in := (hlow₁ 3 (by omega)).trans hVLin.symm
    have hr4 : regs₁ 4 = P_fp := hlow₁ 4 (by omega)
    have hr5 : regs₁ 5 = kk := hlow₁ 5 (by omega)
    have hr6 : regs₁ 6 = V.L_w := (hlow₁ 6 (by omega)).trans hVLw.symm
    have hr7 : regs₁ 7 = V.vCap := (hlow₁ 7 (by omega)).trans hVvc.symm
    have hr8 : regs₁ 8 = V.eCap := (hlow₁ 8 (by omega)).trans hVec.symm
    have hr9 : regs₁ 9 = V.b := (hlow₁ 9 (by omega)).trans hVb.symm
    have ha10 : regs₁ 10 = V.n0 := hsegA 0 (by omega)
    have ha11 : regs₁ 11 = V.m0 := hsegA 1 (by omega)
    have ha12 : regs₁ 12 = V.tM := hsegA 2 (by omega)
    have ha15 : regs₁ 15 = auxLogCap V.n0 := hsegA 5 (by omega)
    have ha16 : regs₁ 16 = hldDepthBound V.n0 := hsegA 6 (by omega)
    have ha20 : regs₁ 20 = V.gPtr := hsegA 10 (by omega)
    have ha21 : regs₁ 21 = V.tPtr := hsegA 11 (by omega)
    have ha22 : regs₁ 22 = V.fPtr := hsegA 12 (by omega)
    have ha23 : regs₁ 23 = V.fAncPtr := hsegA 13 (by omega)
    have ha24 : regs₁ 24 = V.wPtr := hsegA 14 (by omega)
    have ha25 : regs₁ 25 = V.auxPtr := hsegA 15 (by omega)
    have ha26 : regs₁ 26 = V.numSt := hsegA 16 (by omega)
    have ha27 : regs₁ 27 = V.denSt := hsegA 17 (by omega)
    have ha28 : regs₁ 28 = V.endA := hsegA 18 (by omega)
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := V.static_le
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
    have hvc0_eq : mem (g0Ptr + dgVCapOff) = vCap0 := hdg0.2.2.2.1
    have hec0_eq : mem (g0Ptr + dgECapOff) = eCap0 := hdg0.2.2.2.2.1
    have hdg0_sz : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
    have hdgG_sz : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
    have hwa_eq : V.wPtr + wBlockSize 1 = V.auxPtr := by rw [← hVn1]; exact e10
    have haux_orig : auxOrigVertBase V.auxPtr V.vCap 1 = auxVListBase V.auxPtr V.vCap + 9 := by
      have hlog1 : auxLogCap 1 = 2 := by decide
      simp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, hlog1]
    have haux_orig_le : auxVListBase V.auxPtr V.vCap + 9 ≤ V.auxPtr + auxSize V.vCap V.n0 := by
      rw [hVn1, ← haux_orig]
      dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]
      omega
    have hvL_eq : V.auxPtr + 20 + V.vCap = auxVListBase V.auxPtr V.vCap := s7
    have hsegA1 : segACost V.n0 = segACost 1 := by rw [hVn1]
    have hg_le_aux : V.gPtr + dynGraphSize V.vCap V.eCap ≤ V.auxPtr := by omega
    have haux_sz_G : V.auxPtr + auxSize V.vCap G₀.n = V.numSt := by rw [← hVn0]; exact e7
    have haux_le_end : V.auxPtr + auxSize V.vCap G₀.n ≤ V.endA := by rw [haux_sz_G]; omega
    -- Step 19: prepStage
    unfold oneTail
    refine SeqWPR.call (upClosed_wp 37 Q) (prepStageContract w G₀)
      [g0Ptr, V.vCap, V.eCap, kk, V.auxPtr, V.gPtr, V.endA, V.n0, V.m0,
        dgEListBase g0Ptr vCap0 eCap0, auxVListBase V.auxPtr V.vCap]
      (prepC + 50) (hprep G₀) ?_ ?_ ?_ ?_ (by rw [hsegA1]; omega) ?_
    · show evalArgs _ _ _ = _
      dsimp only [rG0, rVc, rEc, rKn, rAux, rGP, rEnd, rN, rM, dgEListBase, auxVListBase,
        auxVIdxBase, auxHdrSize, dgVCapOff, dgECapOff]
      have hvc0_eq' : mem (g0Ptr + 0) = vCap0 := hvc0_eq
      have hec0_eq' : mem (g0Ptr + 1) = eCap0 := hec0_eq
      have hvc0_lt : g0Ptr + 0 < 2 ^ w := by omega
      have hec0_lt : g0Ptr + 1 < 2 ^ w := by omega
      have h7vc0_lt : 7 * vCap0 < 2 ^ w := by omega
      have haux20_lt : V.auxPtr + 20 < 2 ^ w := by omega
      have hvl_lt : V.auxPtr + 20 + V.vCap < 2 ^ w := by omega
      eval_expr
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        (try dsimp only [dgEListBase, auxVListBase, auxVIdxBase, auxHdrSize] at *) <;> omega
    · refine ⟨g0Ptr, V.vCap, V.eCap, kk, V.auxPtr, V.gPtr, V.endA, vCap0, eCap0, by rw [hVn0, hVm0],
        hw16, hVne, hk, hdg0, by omega, by omega, by omega, hg_le_aux, haux_le_end,
        by omega, hk3,
        fun i hi => hz _ (by omega),
        fun u hu => hz _ (by dsimp [auxVIdxBase, auxHdrSize]; omega),
        fun u hu => hz _ (by dsimp [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
          auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
          auxVListBase, auxVIdxBase, auxHdrSize]; omega),
        fun u hu => ⟨hz _ (by dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
            auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
            auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxHdrSize]; omega),
          hz _ (by dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
            auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
            auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxHdrSize]; omega)⟩⟩
    · have hlog11 : Nat.log 2 (1 + 1) = Nat.log 2 2 := rfl
      simp only [prepStageContract, argsSize, Expr.size,
        List.getD_cons_zero, List.getD_cons_succ, hVn1, hlog11, hprepC_def]
      omega
    rintro v₁ mem₁ ⟨_, _, _, _, _, _, _, _, _, vList, repList, heq₁,
      -, -, -, hdgG₁, hvLlen, hvLnd, hvLmem, hvLat, hvIdx1, hvIdx0, hIsOrig₁, hOrig₁, hVis₁,
      -, -, -, -, -, -, -, hfr₁⟩
    simp only [List.cons.injEq, and_true] at heq₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq₁
    have hvL_cons : ∃ r0, vList = [r0] := by
      cases vList with
      | nil => simp [hn1] at hvLlen
      | cons a tl =>
        cases tl with
        | nil => exact ⟨a, rfl⟩
        | cons _ _ => simp [hn1] at hvLlen
    obtain ⟨r0, rfl⟩ := hvL_cons
    have hr0_mem : r0 ∈ G₀.V := (hvLmem r0).mp List.mem_cons_self
    have hGV_eq : G₀.V = {r0} := oneVert_V_eq hn1 hr0_mem
    have hr0_lt : r0 < V.vCap := hVlt r0 hr0_mem
    have hr0_at : mem₁ (auxVListBase V.auxPtr V.vCap) = r0 := by simpa using hvLat 0 (by simp)
    -- Step 20: reg 30 := auxVListBase V.auxPtr V.vCap
    refine SeqWPR.assign (upClosed_wp 37 Q) (auxVListBase V.auxPtr V.vCap) 10
      (by show Expr.eval _ _ _ = _
          dsimp only [rAux, rVc, auxVListBase, auxVIdxBase, auxHdrSize]
          simp only [Nat.reduceAdd]
          have haux20_lt : V.auxPtr + 20 < 2 ^ w := by omega
          have hvl_lt : V.auxPtr + 20 + V.vCap < 2 ^ w := by omega
          eval_expr)
      (by decide) (by omega) ?_
    -- Step 21: reg 31 := r0
    refine SeqWPR.assign (upClosed_wp 37 Q) r0 10
      (by show Expr.eval _ _ _ = _; simp only [Nat.reduceAdd]; eval_expr)
      (by decide) (by omega) ?_
    -- Step 22: bBlocks
    have hz1_t : ∀ a, V.tPtr ≤ a → a < V.wPtr + wBlockSize 1 → mem₁ a = 0 := by
      intro a ha1 ha2
      rw [hfr₁ a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact hz a (by omega)
    refine SeqWPR.call (upClosed_wp 37 Q) (initOneBlocksContract w)
      [V.tPtr, V.fPtr, V.fAncPtr, V.wPtr, V.vCap, V.eCap, r0] 620 hblocks
      (by show evalArgs _ _ _ = _; dsimp only [rTP, rFP, rFA, rWP, rVc, rEc]; simp only [Nat.reduceAdd]; eval_expr)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
      ⟨V.tPtr, V.fPtr, V.fAncPtr, V.wPtr, V.vCap, V.eCap, r0, rfl, hw16, hr0_lt, by omega,
        by rw [← hVtM0]; exact e13.le,
        by rw [← hVn1]; exact e11.le,
        e12.le,
        by omega,
        hz1_t⟩
      (by simp only [initOneBlocksContract, argsSize, Expr.size]; omega)
      (by omega) ?_
    rintro v₂ mem₂ ⟨_, _, _, _, _, _, _, heq₂, -, hT₂, hdgF₂, hFA₂, hW₂, hfr₂⟩
    simp only [List.cons.injEq, and_true] at heq₂
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
    have hdgG₂ : DynGraphAt mem₂ V.gPtr V.vCap V.eCap G₀ :=
      hdgG₁.of_agree fun a ha1 ha2 => hfr₂ a (Or.inl (by omega))
    obtain ⟨eL, heLlen, heLnd, heLmem, heLat, -⟩ := hdgG₂.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hdgG_eList_lt : dgEListBase V.gPtr V.vCap V.eCap + V.m0 ≤ V.numSt := by
      have : dgEListBase V.gPtr V.vCap V.eCap + V.m0 ≤ V.gPtr + dynGraphSize V.vCap V.eCap := by
        dsimp [dgEListBase, dynGraphSize]; omega
      omega
    -- Step 23: bWstr
    refine SeqWPR.call (upClosed_wp 37 Q) (initOneWstrContract w h)
      [dgEListBase V.gPtr V.vCap V.eCap, V.m0, V.numSt, V.denSt, V.L_w]
      (80 * V.m0 + 70) hwstr
      (by show evalArgs _ _ _ = _
          dsimp only [rGP, rVc, rEc, rM, rNumSt, rDenSt, rLw, dgEListBase]
          simp only [Nat.reduceAdd]
          have h7vc_lt : 7 * V.vCap < 2 ^ w := by omega
          have h4_lt : V.gPtr + 4 + 7 * V.vCap + V.eCap < 2 ^ w := by omega
          eval_expr)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl) <;> (try dsimp [dgEListBase]) <;> omega)
      ⟨dgEListBase V.gPtr V.vCap V.eCap, V.m0, V.numSt, V.denSt, V.L_w, V.eCap, eL, rfl,
        hh, hhw, by omega, by omega, by rw [hVLw]; exact h6len, by rw [hVLw]; exact h12cap,
        heLlen.trans hVm0.symm, heLnd,
        fun e he => hElt e ((heLmem e).mp he), heLat,
        hdgG_eList_lt, e8, by omega,
        fun i hi => by
          rw [hfr₂ _ (Or.inr (by omega)), hfr₁ _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
          exact hz _ (by omega),
        fun i hi => by
          rw [hfr₂ _ (Or.inr (by omega)), hfr₁ _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
          exact hz _ (by omega)⟩
      (by simp only [initOneWstrContract, argsSize, Expr.size,
        List.getD_cons_zero, List.getD_cons_succ]; omega)
      (by omega) ?_
    rintro v₃ mem₃ ⟨_, _, _, _, _, heq₃, -, hwstr₃, hfr₃⟩
    simp only [List.cons.injEq, and_true] at heq₃
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₃
    have hfr₃' : ∀ a, a < V.numSt ∨ V.endA ≤ a → mem₃ a = mem₂ a :=
      fun a ha => hfr₃ a (by omega)
    -- Step 24: bStore8 (zeros [auxVListBase + 1, auxVListBase + 9))
    refine SeqWPR.call (upClosed_wp 37 Q) (storeArgsContract w 8)
      [auxVListBase V.auxPtr V.vCap + 1, 0, 0, 0, 0, 0, 0, 0, 0] 80 hs8
      (by show evalArgs _ _ _ = _; simp only [Nat.reduceAdd]; eval_expr)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
      ⟨auxVListBase V.auxPtr V.vCap + 1, [0, 0, 0, 0, 0, 0, 0, 0], rfl, rfl, by omega⟩
      (by simp only [storeArgsContract, argsSize, Expr.size]; omega)
      (by omega) ?_
    rintro v₄ mem₄ ⟨_, _, heq₄, -, hZero8_4, hfr₄⟩
    simp only [List.cons.injEq] at heq₄
    obtain ⟨rfl, rfl⟩ := heq₄
    -- Register lookup helper after step 24
    have hreg4 : ∀ k < 29,
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update regs₁ 29 v₁) 30 (auxVListBase V.auxPtr V.vCap)) 31 r0) 32 v₂) 33 v₃)
          34 v₄ k = regs₁ k := fun k hk => by
      simp (disch := omega) only [Function.update_of_ne]
    -- Step 25: I.store20 auxHdrArgs
    refine SeqWPR.call (upClosed_wp 37 Q) (storeArgsContract w 20)
      (V.auxPtr :: auxHdrVals V) 700 hs20
      (auxHdr_eval V (by omega)
        ((hreg4 7 (by decide)).trans hr7)
        ((hreg4 10 (by decide)).trans ha10)
        ((hreg4 15 (by decide)).trans ha15)
        ((hreg4 16 (by decide)).trans ha16)
        ((hreg4 25 (by decide)).trans ha25))
      (auxHdrVals_lt V (by omega) (by omega))
      ⟨V.auxPtr, auxHdrVals V, rfl, rfl, by omega⟩
      (by simp only [storeArgsContract, auxHdrArgs, argsSize, Expr.size, r, k, add, mul]; omega)
      (by omega) ?_
    rintro v₅ mem₅ h₅
    have hfr₅ : ∀ a, a < V.auxPtr ∨ V.auxPtr + 20 ≤ a → mem₅ a = mem₄ a := by
      obtain ⟨_, _, heq₅, -, -, hfr⟩ := h₅
      simp only [List.cons.injEq] at heq₅
      obtain ⟨rfl, rfl⟩ := heq₅
      exact hfr
    have hfa_one : mem₅ V.fAncPtr = 1 := by
      rw [hfr₅ _ (Or.inl (by omega)), hfr₄ _ (Or.inl (by omega)), hfr₃' _ (Or.inl (by omega))]
      have hFA := hFA₂ ⟨oneVertTree r0, {r0}⟩ rfl rfl rfl
      simpa [fOffRCount] using hFA.1
    have hreg5 : ∀ k < 29,
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update regs₁ 29 v₁) 30 (auxVListBase V.auxPtr V.vCap))
          31 r0) 32 v₂) 33 v₃) 34 v₄) 35 v₅ k = regs₁ k := fun k hk => by
      rw [Function.update_of_ne (by omega)]; exact hreg4 k hk
    -- Step 26: I.store24 (oneLsfHdrArgs h)
    refine SeqWPR.call (upClosed_wp 37 Q) (storeArgsContract w 24)
      (V.b :: lsfHdrVals V h P_fp kk (mem₅ V.fAncPtr) r0) 300 hs24
      (oneLsfHdr_eval V hhw_lt
        ((hreg5 4 (by decide)).trans hr4)
        ((hreg5 5 (by decide)).trans hr5)
        ((hreg5 6 (by decide)).trans hr6)
        ((hreg5 3 (by decide)).trans hr3)
        ((hreg5 7 (by decide)).trans hr7)
        ((hreg5 8 (by decide)).trans hr8)
        ((hreg5 9 (by decide)).trans hr9)
        ((hreg5 10 (by decide)).trans ha10)
        ((hreg5 11 (by decide)).trans ha11)
        ((hreg5 12 (by decide)).trans ha12)
        ((hreg5 20 (by decide)).trans ha20)
        ((hreg5 21 (by decide)).trans ha21)
        ((hreg5 22 (by decide)).trans ha22)
        ((hreg5 23 (by decide)).trans ha23)
        ((hreg5 24 (by decide)).trans ha24)
        ((hreg5 25 (by decide)).trans ha25)
        ((hreg5 26 (by decide)).trans ha26)
        ((hreg5 27 (by decide)).trans ha27)
        ((hreg5 28 (by decide)).trans ha28)
        (by simp (disch := omega) only [Function.update_of_ne, Function.update_self]))
      (lsfHdrVals_lt V (by omega) (by omega) (by omega) (by omega) hhw_lt hPw hkk_w
        (by rw [hfa_one]; omega) (by omega))
      ⟨V.b, lsfHdrVals V h P_fp kk (mem₅ V.fAncPtr) r0, rfl, rfl, by omega⟩
      (by simp only [storeArgsContract, oneLsfHdrArgs, argsSize, Expr.size, r, k, ld]; omega)
      (by omega) ?_
    rintro v₆ mem₆ h₆
    have hfr₆ : ∀ a, a < V.b ∨ V.b + 24 ≤ a → mem₆ a = mem₅ a := by
      obtain ⟨_, _, heq₆, -, -, hfr⟩ := h₆
      simp only [List.cons.injEq] at heq₆
      obtain ⟨rfl, rfl⟩ := heq₆
      exact hfr
    -- Step 27: assign reg 37 := V.endA + 3
    refine SeqWPR.assign (upClosed_wp 37 Q) (V.endA + 3) 10
      (by show Expr.eval _ _ _ = _; dsimp only [rEnd]; simp only [Nat.reduceAdd]; eval_expr)
      (by decide) (by omega) ?_
    -- End of sequence: invoke one_build_rep
    refine ⟨?_, by omega⟩
    rw [show (10 + 27 : ℕ) = 37 from rfl, Function.update_self]
    have h₆' : (storeArgsContract w 24).post (V.b :: lsfHdrVals V h P_fp kk 1 r0) mem₅ v₆ mem₆ := by
      rwa [hfa_one] at h₆
    have hres := one_build_rep (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN) V hVn1 hVtM0 hn1
      hVm0.symm hh (by omega) (by omega) (by rw [hVLw]; exact h2Lw) hk (by omega) hm0 hG₀ hVne
      hr0_mem hr0_lt hGV_eq hElt hdg0 (by rw [hVLin]; exact hℓpos) (by rw [hVLin]; exact hvpos)
      (by rw [hVb]; exact hz) hdgG₂ hr0_at (by simpa using hvIdx1 0 (by simp)) hvIdx0
      (by rw [hVn0]; exact hIsOrig₁) (by rw [hVn0]; exact hOrig₁ r0 hr0_mem hr0_lt)
      (by rw [hVn0]; exact hVis₁) (by rw [hVn0]; exact hfr₁)
      hT₂ hdgF₂ hFA₂ hW₂ hfr₂ (heLlen.trans hVm0.symm) heLmem heLat hwstr₃ hfr₃'
      hZero8_4 hfr₄ h₅ hfr₅ h₆' hfr₆ (by rw [hVb, hVvc, hVec, hVLw, hVLin]; exact hsp_eq)
    rw [hVb, hVvc, hVec, hVLw, hVLin] at hres
    exact hres
  obtain ⟨o, st', c, hr, ⟨s', x', hsG0, hrep, hpost, hresp, hphi⟩, hc'⟩ :=
    runs_dseqStmt (ω := ω) (oneSteps I bBlocks bWstr bStore8 h) 0
      (startState [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem pos)
      (Bsum + 2) 0 hwp
  refine ⟨o, st', c, hr, s', x', hsG0, hrep, hpost, hresp, ?_⟩
  rw [lsfInitCost_eq hdg0, hn1, ← hVm0]
  have hcost := one_cost_le (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN) (m0 := V.m0) (L_in := L_in)
    (L_w := L_w) hh
  rw [Nat.zero_add, Nat.zero_add] at hc'
  have h1 : c + (LSFRep h).phi b x' st'.mem + 20 ≤
      Bsum + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 22 := by
    have hstep := Nat.add_le_add_right (Nat.add_le_add hc' hphi) 20
    have hcomm : Bsum + 2 + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 20 =
        Bsum + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 22 := by
      have hsub (x y : ℕ) : x + 2 + y + 20 = x + y + 22 := by omega
      exact hsub _ _
    exact hcomm ▸ hstep
  have hB_eq : Bsum + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 22 =
      segACost 1 + (20 * Nat.log 2 1 + 20 * Nat.log 2 2 + 640 * 1 + 920 * V.m0 + 600) +
      600 + (80 * V.m0 + 50) + 2000 + 3000 * (1 + 1) * (Nat.log 2 (1 + 2) + 1) + 22 := by
    rw [hBsum_def, hprepC_def]
  rw [hB_eq] at h1
  exact Nat.le_trans h1 hcost

/-- The one-vertex path of `Initialize` (`n₀ = 1`) meets what `DSRep.Implements` asks of an
initialization, with `+ 20` cost slack to pay for the top-level branch. -/
theorem lsfInit_one_runs {w h : ℕ} {p : Program} {I : InitIdx} {bBlocks bWstr bStore8 : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hblocks : MeetsContract w p bBlocks (initOneBlocksContract w))
    (hwstr : MeetsContract w p bWstr (initOneWstrContract w h))
    (hs8 : MeetsContract w p bStore8 (storeArgsContract w 8))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPre c_AN K_AN w h args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w)
    (hn1_mem : mem (args.getD 0 0 + dgNOff) = 1) :
    ∃ o st' c, Runs w p ω (oneBody I bBlocks bWstr bStore8 h) (startState args mem pos) o st' c ∧
      ∃ s' x', (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem + 20 ≤
          lsfInitCost Q_AN c_AN K_AN h args mem := by
  obtain ⟨G₀, hpre'⟩ := hpre
  obtain ⟨o, st', c, hr, s', x', -, hrep, hpost, hresp, hc⟩ :=
    lsfInit_one_runs_for hlog hprep hblocks hwstr hs8 hs20 hs24 pos ω hwords hpre' hz hsp hn1_mem
  exact ⟨o, st', c, hr, s', x', hrep, hpost, hresp, hc⟩

end

end MinCostFlow.LSF.Program
