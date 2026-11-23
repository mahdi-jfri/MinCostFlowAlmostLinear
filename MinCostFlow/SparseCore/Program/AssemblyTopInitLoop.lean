module

public import MinCostFlow.SparseCore.Program.AssemblyTopIface
public import WordRAM.Logic

/-!
# Amortized `k`-branch initialization loop for the top-layer sparse-core program (`AssemblyTopInitLoop`)

Runs `CF.export_runs` followed by `BR.init_runs` on every branch `j = 0, …, k - 1`:
* saves the export base `expPtr := h_cur` in `r18`;
* calls P4's single-branch export `CF.fExport [cfH, j, h_cur]`, advancing `r14` to `expEnd`;
* stores `expEnd` (the handle of branch `j`) at `tbl + j`;
* calls `BR.init_runs [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P_fp, vCap, eCap, depth,
  lengths, expEnd]`, advancing `r14` to `hNext`.

Proved by direct induction on the remaining iteration count `rem = k - i`, telescoping `CF.rep.phi`
and summing `BR.rep.phi` while preserving pairwise disjointness of `CF`, all `k` branches, the
branch handle table, and all shared read-only inputs.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Loop statements -/

/-- Inner body of the branch-initialization loop (iteration counter `r15`, bound `r4 = k`).
Expects `r0 = graph`, `r1 = lengths`, `r3 = cOrdPtr`, `r4 = k`, `r5 = M`, `r6 = N`, `r7 = L`,
`r8 = P_fp`, `r10 = vCap`, `r11 = eCap`, `r12 = cfH`, `r13 = tbl`, `r14 = h_cur`, `r19 = depth`;
uses `r18` for `expPtr`. -/
def asmInitBranchStep (fCFExport fBrInit : ℕ) : Stmt :=
  .assign 18 (.reg 14) ;;
  .call 14 fCFExport [.reg 12, .reg 15, .reg 14] ;;
  .store (.bin .add (.reg 13) (.reg 15)) (.reg 14) ;;
  .call 14 fBrInit [.reg 12, .reg 15, .reg 0, .reg 3, .reg 18, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 10, .reg 11, .reg 19, .reg 1, .reg 14] ;;
  .assign 15 (.bin .add (.reg 15) (.const 1))

/-- Loop exporting and initializing all `k` branches `j = 0 .. k - 1`, recording handles at `tbl`. -/
def asmInitBranchesLoop (fCFExport fBrInit : ℕ) : Stmt :=
  .assign 15 (.const 0) ;;
  .loop (.bin .lt (.reg 15) (.reg 4)) (asmInitBranchStep fCFExport fBrInit)

theorem asmInitBranchesLoop_noRand (fCFExport fBrInit : ℕ) :
    (asmInitBranchesLoop fCFExport fBrInit).NoRand := by
  simp [asmInitBranchesLoop, asmInitBranchStep, Stmt.NoRand]

/-! ## Small helper for `Finset.Ico` sums -/

private theorem sum_Ico_cons {i k : ℕ} (h : i < k) (f : ℕ → ℕ) :
    (Finset.Ico i k).sum f = f i + (Finset.Ico (i + 1) k).sum f := by
  have h1 : Finset.Ico i k = insert i (Finset.Ico (i + 1) k) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [h1, Finset.sum_insert (by simp)]

/-! ## Verification of `asmInitBranchesLoop` -/

private theorem asmInitBranchesLoop_go
    {S : AsmBranchSpec} {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    {graph lengths cOrdPtr k M N vCap eCap cfH tbl cWords hStart : ℕ}
    {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {cfs : CompFamilyAbs}
    (hfmt : fmt.limbBits = 4) (hPL : fmt.precision ≤ 4 * L) (hk : 0 < k) (hGval : G.IsValid) (hGne : G.V.Nonempty)
    (hGm : G.m ≤ M) (hGn : G.n ≤ N) (hGn_le : G.n ≤ G.m + 1)
    (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hwCF : (M + N + 2) ^ CFS.wordExp capExp * (L + 1) < 2 ^ w)
    (hwBR : (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hcfs : ∀ j < k, cfs j = initCompLSFWith lsfInit G ℓ₀ k j)
    (hlen_disj_tbl : ∀ a, lengths ≤ a → a < lengths + eCap * L → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hG_le : graph + dynGraphSize vCap eCap ≤ hStart)
    (hcOrd_le : cOrdPtr + cWords ≤ hStart) (hcWords_le : cWords ≤ 1 + 6 * G.m)
    (hrot : IsRotationOrder G ord) (htbl_le : tbl + k ≤ hStart)
    (hG_disj_tbl : ∀ a, graph ≤ a → a < graph + dynGraphSize vCap eCap → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hcOrd_disj_tbl : ∀ a, cOrdPtr ≤ a → a < cOrdPtr + cWords → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hargsW : ∀ a ∈ [cfH, graph, cOrdPtr, k, M, N, L, fmt.precision, vCap, eCap, depth, tbl], a < 2 ^ w)
    (hsp : hStart + k * ((CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L) +
      (S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)) < 2 ^ w)
    (hMod : ∀ j < k, AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord)
    (hUpd : ∀ j < k, BranchUpdatesBelow impl
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) 0)
    (ω : ℕ → Bool) :
    let expSp := (CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L)
    let initSp := (S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)
    let iterSp := expSp + initSp
    let tr₀ := fun j => initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    ∀ (rem i : ℕ) (st : State) (xcf : CF.rep.τ) (brH : ℕ → ℕ) (xBR : ∀ j, j < i → BR.rep.τ)
      (hik : i + rem = k),
      st.regs 0 = graph → st.regs 1 = lengths → st.regs 3 = cOrdPtr → st.regs 4 = k →
      st.regs 5 = M →
      st.regs 6 = N → st.regs 7 = L → st.regs 8 = fmt.precision →
      st.regs 10 = vCap → st.regs 11 = eCap → st.regs 12 = cfH → st.regs 13 = tbl →
      st.regs 15 = i → st.regs 19 = depth →
      hStart ≤ st.regs 14 → st.regs 14 ≤ hStart + i * iterSp →
      ZeroFrom st.mem (st.regs 14) →
      CF.rep.rep cfH cfs xcf st.mem →
      CF.vCapOf xcf = vCap → CF.eCapOf xcf = eCap →
      (∀ a, CF.rep.foot cfH xcf a → a < st.regs 14 ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
        ¬ (graph ≤ a ∧ a < graph + dynGraphSize vCap eCap) ∧
        ¬ (cOrdPtr ≤ a ∧ a < cOrdPtr + cWords)) →
      (∀ a, CF.rep.foot cfH xcf a → ¬ (lengths ≤ a ∧ a < lengths + eCap * L)) →
      DynGraphAt st.mem graph vCap eCap G →
      OrdListAt st.mem cOrdPtr ord cWords →
      BranchLengthsAt st.mem lengths eCap L fmt.precision hStart G ℓ₀ →
      (∀ (j : ℕ) (hj : j < i), st.mem (tbl + j) = brH j ∧ brH j ≤ st.regs 14 ∧
        BR.rep.rep (brH j) ⟨tr₀ j, ord, vCap, eCap⟩ (xBR j hj) st.mem ∧
        ∀ a, BR.rep.foot (brH j) (xBR j hj) a → hStart ≤ a ∧ a < st.regs 14 ∧ ¬ CF.rep.foot cfH xcf a) →
      (∀ (j₁ : ℕ) (h₁ : j₁ < i) (j₂ : ℕ) (h₂ : j₂ < i), j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH j₁) (xBR j₁ h₁) a → ¬ BR.rep.foot (brH j₂) (xBR j₂ h₂) a) →
      ∃ (st' : State) (c : ℕ) (xcf' : CF.rep.τ) (brH' : ℕ → ℕ) (xBR' : ∀ j, j < k → BR.rep.τ),
        Runs w p ω (.loop (.bin .lt (.reg 15) (.reg 4)) (asmInitBranchStep CF.fExport bp.fInit)) st .normal st' c ∧
        (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 18 → st'.regs r = st.regs r) ∧
        st.regs 14 ≤ st'.regs 14 ∧ st'.regs 14 ≤ hStart + k * iterSp ∧
        ZeroFrom st'.mem (st'.regs 14) ∧
        CF.rep.rep cfH cfs xcf' st'.mem ∧
        CF.vCapOf xcf' = vCap ∧ CF.eCapOf xcf' = eCap ∧
        (∀ a, CF.rep.foot cfH xcf' a → CF.rep.foot cfH xcf a ∨ (st.regs 14 ≤ a ∧ a < st'.regs 14)) ∧
        (∀ a < hStart, ¬ CF.rep.foot cfH xcf a → ¬ (tbl + i ≤ a ∧ a < tbl + k) → st'.mem a = st.mem a) ∧
        (∀ (j : ℕ) (hj : j < i), brH' j = brH j ∧ xBR' j (by omega) = xBR j hj ∧
          ∀ a, BR.rep.foot (brH j) (xBR j hj) a → st'.mem a = st.mem a) ∧
        (∀ (j : ℕ) (hj : j < k), st'.mem (tbl + j) = brH' j ∧ brH' j ≤ st'.regs 14 ∧
          BR.rep.rep (brH' j) ⟨tr₀ j, ord, vCap, eCap⟩ (xBR' j hj) st'.mem ∧
          ∀ a, BR.rep.foot (brH' j) (xBR' j hj) a →
            hStart ≤ a ∧ a < st'.regs 14 ∧ ¬ CF.rep.foot cfH xcf' a) ∧
        (∀ (j₁ : ℕ) (h₁ : j₁ < k) (j₂ : ℕ) (h₂ : j₂ < k), j₁ ≠ j₂ → ∀ a,
          BR.rep.foot (brH' j₁) (xBR' j₁ h₁) a → ¬ BR.rep.foot (brH' j₂) (xBR' j₂ h₂) a) ∧
        c + CF.rep.phi cfH xcf' st'.mem +
          (Finset.Ico i k).sum (fun j => if hj : j < k then BR.rep.phi (brH' j) (xBR' j hj) st'.mem else 0) ≤
          (Finset.Ico i k).sum (fun j =>
            CFS.mul capExp limbMul * ((G.n + G.m + 1) * bundleLogFactor M N) +
            S.mul capExp limbMul * (tr₀ j).machCost) + 70 * rem + 10 +
          CF.rep.phi cfH xcf st.mem := by
  intro expSp initSp iterSp tr₀ rem
  change hStart + k * iterSp < 2 ^ w at hsp
  have h1w : 1 < 2 ^ w := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hcfW, hgW, hcOrdW, hkW, hMW, hNW, hLW, hPfpW, hvW, heW, hdepthW, htblW⟩
  induction rem with
  | zero =>
    intro i st xcf brH xBR hik r0 r1 r3 r4 r5 r6 r7 r8 r10 r11 r12 r13 r15 r19 hlo hhi hz hcf
      hvCF heCF hcfFt hcfLen hG hOrd hLen hprev hdisj
    have hi : i = k := by omega
    subst hi
    have hlt0 : (Expr.bin .lt (.reg 15) (.reg 4)).eval w st = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq r15) (Expr.eval_reg_of_eq r4) (le_refl _) h1w
    refine ⟨st, _, xcf, brH, xBR, runs_loop_iff.mpr (Or.inl ⟨hlt0, rfl, rfl, rfl⟩),
      fun _ _ _ _ => rfl, le_rfl, hhi, hz, hcf, hvCF, heCF, fun _ ha => Or.inl ha, fun _ _ _ _ => rfl,
      fun j hj => ⟨rfl, rfl, fun _ _ => rfl⟩, hprev, hdisj, ?_⟩
    simp [Expr.size]
  | succ rem ih =>
    intro i st xcf brH xBR hik r0 r1 r3 r4 r5 r6 r7 r8 r10 r11 r12 r13 r15 r19 hlo hhi hz hcf
      hvCF heCF hcfFt hcfLen hG hOrd hLen hprev hdisj
    have hilt : i < k := by omega
    set hCur := st.regs 14 with hhCur_def
    have hhCur_w : hCur < 2 ^ w := by
      have : i * iterSp ≤ k * iterSp := Nat.mul_le_mul_right _ (by omega)
      omega
    have hsp_iter : hCur + iterSp < 2 ^ w := by
      have : (i + 1) * iterSp ≤ k * iterSp := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_one_mul] at this; omega
    have hlt1 : (Expr.bin .lt (.reg 15) (.reg 4)).eval w st = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq r15) (Expr.eval_reg_of_eq r4) hilt h1w
    -- Step 1: r18 := hCur
    have ha18 : Runs w p ω (.assign 18 (.reg 14)) st .normal
        { st with regs := Function.update st.regs 18 hCur } _ :=
      runs_assign_iff.mpr ⟨hCur, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
    set st1 : State := { st with regs := Function.update st.regs 18 hCur }
    -- Step 2: call CF.export_runs on [cfH, i, hCur]
    have hcfs_i_G : (cfs i).G = G := by rw [hcfs i hilt]; rfl
    have hargs_exp : ∀ a ∈ [cfH, i, hCur], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> omega
    obtain ⟨bodyE, hbodyE, oE, stE, cE, xcf1, hrunE, hcfE, hvCF1, heCF1, hExpAt, hrespE, hcostE⟩ :=
      CF.export_runs cfH i k M N vCap eCap hCur cfs xcf st1.mem st1.pos ω
        hfmt hk hilt (by rw [hcfs 0 hk]; rfl) hkCap (hcfs_i_G ▸ hGm) (hcfs_i_G ▸ hGn) hcap hwCF hcf
        hvCF heCF (fun a ha => (hcfFt a ha).1) hargs_exp hz (by dsimp only [iterSp] at hsp_iter; omega)
    rcases hrespE with ⟨hE_lo, hE_hi, hzE, hE_fr, hE_ft⟩
    set expEnd := oE.value
    have hexpEnd_w : expEnd < 2 ^ w := by dsimp only [iterSp] at hsp_iter; omega
    have hsp_br : expEnd + initSp < 2 ^ w := by dsimp only [iterSp] at hsp_iter; omega
    have hcallE : Runs w p ω (.call 14 CF.fExport [.reg 12, .reg 15, .reg 14]) st1 .normal
        { stE with regs := Function.update st1.regs 14 expEnd }
        (argsSize [.reg 12, .reg 15, .reg 14] + cE + 1) := by
      refine (runs_call_iff (r := 14) (f := CF.fExport) (st := st1) (o := .normal)
        (st' := { stE with regs := Function.update st1.regs 14 expEnd })).mpr
        ⟨[cfH, i, hCur], bodyE, oE, stE, cE, ?_, hbodyE, hrunE, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st1, r12, r15, hhCur_def]
    set st2 : State := { stE with regs := Function.update st1.regs 14 expEnd }
    -- Step 3: store expEnd at tbl + i
    have hstore : Runs w p ω (.store (.bin .add (.reg 13) (.reg 15)) (.reg 14)) st2 .normal
        { st2 with mem := Function.update st2.mem (tbl + i) expEnd } _ :=
      runs_store_iff.mpr ⟨tbl + i, expEnd,
        Expr.eval_add (Expr.eval_reg_of_eq (v := tbl) (by simp [st2, st1, r13]))
          (Expr.eval_reg_of_eq (v := i) (by simp [st2, st1, r15])) (by omega),
        Expr.eval_reg_of_eq (by simp [st2]), rfl, rfl, rfl⟩
    set st3 : State := { st2 with mem := Function.update st2.mem (tbl + i) expEnd }
    have hmem3_ne : ∀ a, a ≠ tbl + i → st3.mem a = stE.mem a := fun a ha =>
      Function.update_of_ne ha _ _
    have hcfFt1 : ∀ a, CF.rep.foot cfH xcf1 a → a < expEnd ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
        ¬ (graph ≤ a ∧ a < graph + dynGraphSize vCap eCap) ∧
        ¬ (cOrdPtr ≤ a ∧ a < cOrdPtr + cWords) := fun a ha => by
      rcases hE_ft a ha with hold | hnew
      · have h := hcfFt a hold
        exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2⟩
      · exact ⟨hnew.2, by omega, by omega, by omega⟩
    have hcf3_loc := CF.rep_local cfH cfs xcf1 stE.mem st3.mem fun a ha =>
      (hmem3_ne a fun heq => (hcfFt1 (tbl + i) (heq ▸ ha)).2.1 ⟨by omega, by omega⟩).symm
    have hcf3 : CF.rep.rep cfH cfs xcf1 st3.mem := hcf3_loc.1 hcfE
    have hcf3_phi : CF.rep.phi cfH xcf1 st3.mem = CF.rep.phi cfH xcf1 stE.mem := hcf3_loc.2.symm
    have hExp3 : CompBranchExportAt w st3.mem hCur expEnd L capExp M N vCap eCap (cfs i) :=
      compBranchExportAt_congr (fun a ha1 ha2 => (hmem3_ne a (by omega)).symm) hExpAt
    have hG3 : DynGraphAt st3.mem graph vCap eCap G :=
      DynGraphAt.of_agree hG fun a ha1 ha2 => by
        rw [hmem3_ne a fun heq => hG_disj_tbl a ha1 ha2 ⟨by omega, by omega⟩]
        exact hE_fr a (by omega) fun hfa => (hcfFt a hfa).2.2.1 ⟨ha1, ha2⟩
    have hOrd3 : OrdListAt st3.mem cOrdPtr ord cWords :=
      ordListAt_of_agree hOrd fun a ha1 ha2 => by
        rw [hmem3_ne a fun heq => hcOrd_disj_tbl a ha1 ha2 ⟨by omega, by omega⟩]
        exact hE_fr a (by omega) fun hfa => (hcfFt a hfa).2.2.2 ⟨ha1, ha2⟩
    have hlen_le : lengths + eCap * L ≤ hStart := hLen.1
    have hLen3 : BranchLengthsAt st3.mem lengths eCap L fmt.precision hStart G ℓ₀ :=
      hLen.of_agree (fun a ha1 ha2 => by
        rw [hmem3_ne a fun heq => hlen_disj_tbl a ha1 ha2 ⟨by omega, by omega⟩]
        exact hE_fr a (by omega) fun hfa => hcfLen a hfa ⟨ha1, ha2⟩) hlen_le
    have hz3 : ZeroFrom st3.mem expEnd := fun a ha => by
      rw [hmem3_ne a (by omega)]; exact hzE a ha
    -- Step 4: call BR.init_runs at expEnd with expPtr = hCur
    have hargs_init : ∀ a ∈ [cfH, i, graph, cOrdPtr, hCur, k, M, N, L, fmt.precision, vCap, eCap,
        depth, lengths, expEnd], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> omega
    obtain ⟨bodyB, hbodyB, oB, stB, cB, xi, hrunB, hrepBi, hrespB, hcostB⟩ :=
      BR.init_runs cfH i graph lengths cOrdPtr hCur expEnd k M N vCap eCap expEnd cWords G ℓ₀ ord
        cfs xcf1 st3.mem st3.pos ω hfmt hPL hk hilt hGval hGne hGm hGn hGn_le hcap hwBR hcf3
        (hcfs i hilt) (hLen3.of_agree (fun _ _ _ => rfl) (by omega)) hG3 (by omega) hOrd3 (by omega) hcWords_le hrot
        hExp3 le_rfl
        (fun a ha => (hcfFt1 a ha).1) hargs_init hz3 hsp_br (hMod i hilt) (hUpd i hilt)
    rcases hrespB with ⟨hB_lo, hB_hi, hzB, hB_fr, hB_ft⟩
    set hNext := oB.value
    have hcallB : Runs w p ω (.call 14 bp.fInit [.reg 12, .reg 15, .reg 0, .reg 3, .reg 18,
        .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 10, .reg 11, .reg 19, .reg 1, .reg 14]) st3
        .normal { stB with regs := Function.update st3.regs 14 hNext }
        (argsSize [.reg 12, .reg 15, .reg 0, .reg 3, .reg 18, .reg 4, .reg 5, .reg 6, .reg 7,
          .reg 8, .reg 10, .reg 11, .reg 19, .reg 1, .reg 14] + cB + 1) := by
      refine (runs_call_iff (r := 14) (f := bp.fInit) (st := st3) (o := .normal)
        (st' := { stB with regs := Function.update st3.regs 14 hNext })).mpr
        ⟨[cfH, i, graph, cOrdPtr, hCur, k, M, N, L, fmt.precision, vCap, eCap, depth, lengths,
          expEnd], bodyB, oB, stB, cB, ?_, hbodyB, hrunB, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st3, st2, st1, r0, r1, r3, r4, r5, r6, r7, r8, r10, r11, r12, r15,
        r19]
    set st4 : State := { stB with regs := Function.update st3.regs 14 hNext }
    -- Step 5: increment r15
    have hinc : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) st4 .normal
        { st4 with regs := Function.update st4.regs 15 (i + 1) } _ :=
      runs_assign_iff.mpr ⟨i + 1,
        Expr.eval_add (Expr.eval_reg_of_eq (v := i) (by simp [st4, st3, st2, st1, r15]))
          (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
    set st5 : State := { st4 with regs := Function.update st4.regs 15 (i + 1) }
    have hstep_run := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha18,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hcallE,
        runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hstore,
          runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcallB, hinc, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    -- Update branch maps and establish invariant for i + 1
    set brH1 := Function.update brH i expEnd
    let xBR1 : ∀ j, j < i + 1 → BR.rep.τ := fun j hj =>
      if hji : j = i then xi else xBR j (by omega)
    have hcf5_loc := CF.rep_local cfH cfs xcf1 st3.mem st5.mem fun a ha =>
      (hB_fr a (hcfFt1 a ha).1 (fun hf => hf)).symm
    have hcf5 : CF.rep.rep cfH cfs xcf1 st5.mem := hcf5_loc.1 hcf3
    have hcf5_phi : CF.rep.phi cfH xcf1 st5.mem = CF.rep.phi cfH xcf1 stE.mem :=
      hcf5_loc.2.symm.trans hcf3_phi
    have hG5 : DynGraphAt st5.mem graph vCap eCap G :=
      DynGraphAt.of_agree hG3 fun a ha1 ha2 => hB_fr a (by omega) (fun hf => hf)
    have hOrd5 : OrdListAt st5.mem cOrdPtr ord cWords :=
      ordListAt_of_agree hOrd3 fun a ha1 ha2 => hB_fr a (by omega) (fun hf => hf)
    have hLen5 : BranchLengthsAt st5.mem lengths eCap L fmt.precision hStart G ℓ₀ :=
      hLen3.of_agree (fun a ha1 ha2 => hB_fr a (by omega) (fun hf => hf)) hlen_le
    have hcfLen1 : ∀ a, CF.rep.foot cfH xcf1 a → ¬ (lengths ≤ a ∧ a < lengths + eCap * L) :=
      fun a ha hin => by
        rcases hE_ft a ha with hold | hnew
        · exact hcfLen a hold hin
        · omega
    have hft_i : ∀ a, BR.rep.foot expEnd xi a → expEnd ≤ a ∧ a < hNext := fun a ha => by
      rcases hB_ft a ha with hf | hrg
      · exact False.elim hf
      · exact hrg
    have hprev5 : ∀ (j : ℕ) (hj : j < i + 1), st5.mem (tbl + j) = brH1 j ∧ brH1 j ≤ st5.regs 14 ∧
        BR.rep.rep (brH1 j) ⟨tr₀ j, ord, vCap, eCap⟩ (xBR1 j hj) st5.mem ∧
        ∀ a, BR.rep.foot (brH1 j) (xBR1 j hj) a → hStart ≤ a ∧ a < st5.regs 14 ∧ ¬ CF.rep.foot cfH xcf1 a := by
      intro j hj
      have hr14_5 : st5.regs 14 = hNext := by simp [st5, st4]
      by_cases hji : j = i
      · subst hji
        simp only [brH1, xBR1, Function.update_self, ↓reduceDIte, hr14_5]
        refine ⟨?_, hB_lo, hrepBi, fun a ha =>
          ⟨by have := (hft_i a ha).1; omega, (hft_i a ha).2,
            fun hfc => by have := (hcfFt1 a hfc).1; have := (hft_i a ha).1; omega⟩⟩
        change stB.mem (tbl + j) = expEnd
        rw [hB_fr (tbl + j) (by omega) (fun hf => hf)]
        simp [st3]
      · have hjlt : j < i := by omega
        obtain ⟨htj, hbrle, hrepj, hftj⟩ := hprev j hjlt
        simp only [brH1, xBR1, Function.update_of_ne hji, hji, ↓reduceDIte, hr14_5]
        refine ⟨?_, by omega, ?_, fun a ha =>
          ⟨(hftj a ha).1, by have := (hftj a ha).2.1; omega, fun hfc => by
            rcases hE_ft a hfc with hold | hnew
            · exact (hftj a ha).2.2 hold
            · have := (hftj a ha).2.1; omega⟩⟩
        · change stB.mem (tbl + j) = brH j
          rw [hB_fr (tbl + j) (by omega) (fun hf => hf), hmem3_ne (tbl + j) (by omega),
            hE_fr (tbl + j) (by omega) fun hfc => (hcfFt _ hfc).2.1 ⟨by omega, by omega⟩]
          exact htj
        · exact (BR.rep_local (brH j) ⟨tr₀ j, ord, vCap, eCap⟩ (xBR j hjlt) st.mem stB.mem fun a ha => by
            have hf := hftj a ha
            rw [hB_fr a (by omega) (fun h => h), hmem3_ne a (by omega),
              hE_fr a hf.2.1 hf.2.2]).1 hrepj
    have hdisj5 : ∀ (j₁ : ℕ) (h₁ : j₁ < i + 1) (j₂ : ℕ) (h₂ : j₂ < i + 1), j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH1 j₁) (xBR1 j₁ h₁) a → ¬ BR.rep.foot (brH1 j₂) (xBR1 j₂ h₂) a := by
      intro j₁ h₁ j₂ h₂ hne a ha1 ha2
      by_cases h1i : j₁ = i
      · subst h1i
        have h2i : j₂ ≠ j₁ := Ne.symm hne
        simp only [brH1, xBR1, Function.update_self, Function.update_of_ne h2i, h2i, ↓reduceDIte] at ha1 ha2
        have := hft_i a ha1; have := (hprev j₂ (by omega)).2.2.2 a ha2; omega
      · by_cases h2i : j₂ = i
        · subst h2i
          simp only [brH1, xBR1, Function.update_self, Function.update_of_ne h1i, h1i, ↓reduceDIte] at ha1 ha2
          have := hft_i a ha2; have := (hprev j₁ (by omega)).2.2.2 a ha1; omega
        · simp only [brH1, xBR1, Function.update_of_ne h1i, Function.update_of_ne h2i,
            h1i, h2i, ↓reduceDIte] at ha1 ha2
          exact hdisj j₁ (by omega) j₂ (by omega) hne a ha1 ha2
    -- Invoke induction hypothesis on rem
    obtain ⟨st', cRest, xcf', brH', xBR', hrunRest, hregs', hlo', hhi', hz', hcf', hvCF', heCF',
        hcfFt', hfr', hkeep', hall', hdisj', hcostRest⟩ :=
      ih (i + 1) st5 xcf1 brH1 xBR1 (by omega)
        (by simp [st5, st4, st3, st2, st1, r0]) (by simp [st5, st4, st3, st2, st1, r1])
        (by simp [st5, st4, st3, st2, st1, r3])
        (by simp [st5, st4, st3, st2, st1, r4]) (by simp [st5, st4, st3, st2, st1, r5])
        (by simp [st5, st4, st3, st2, st1, r6]) (by simp [st5, st4, st3, st2, st1, r7])
        (by simp [st5, st4, st3, st2, st1, r8]) (by simp [st5, st4, st3, st2, st1, r10])
        (by simp [st5, st4, st3, st2, st1, r11]) (by simp [st5, st4, st3, st2, st1, r12])
        (by simp [st5, st4, st3, st2, st1, r13]) (by simp [st5])
        (by simp [st5, st4, st3, st2, st1, r19])
        (by simp [st5, st4]; omega)
        (by simp [st5, st4]; rw [Nat.add_one_mul]; dsimp only [iterSp] at *; omega)
        (by simpa [st5, st4] using hzB) hcf5 hvCF1 heCF1
        (fun a ha => by
          have h := hcfFt1 a ha
          refine ⟨by simp [st5, st4]; omega, h.2.1, h.2.2.1, h.2.2.2⟩)
        hcfLen1 hG5 hOrd5 hLen5 hprev5 hdisj5
    have hfull : Runs w p ω (.loop (.bin .lt (.reg 15) (.reg 4)) (asmInitBranchStep CF.fExport bp.fInit))
        st .normal st' _ :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st5, _, _, hlt1, Nat.one_ne_zero, hstep_run, hrunRest, rfl⟩))
    have hki := hkeep' i (by omega)
    have hbr_i : brH' i = expEnd := hki.1.trans (by simp [brH1])
    have hx_i : xBR' i hilt = xi := hki.2.1.trans (by simp [xBR1])
    have hphi_i_eq : (if hj : i < k then BR.rep.phi (brH' i) (xBR' i hj) st'.mem else 0) =
        BR.rep.phi expEnd xi stB.mem := by
      simp only [hilt, ↓reduceDIte]
      rw [hbr_i, hx_i]
      exact (BR.rep_local expEnd ⟨tr₀ i, ord, vCap, eCap⟩ xi stB.mem st'.mem fun a ha =>
        (hki.2.2 a (by simpa [brH1, xBR1] using ha)).symm).2.symm
    refine ⟨st', _, xcf', brH', xBR', hfull,
      fun r hr14 hr15 hr18 => (hregs' r hr14 hr15 hr18).trans (by simp [st5, st4, st3, st2, st1, hr14, hr15, hr18]),
      by simp only [st5, st4, Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self] at hlo'; omega,
      hhi', hz', hcf', hvCF', heCF', ?_, ?_, ?_, hall', hdisj', ?_⟩
    · intro a ha
      rcases hcfFt' a ha with hold1 | hnew1
      · rcases hE_ft a hold1 with hold0 | hnew0
        · exact Or.inl hold0
        · exact Or.inr ⟨hnew0.1, by
            simp only [st5, st4, Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self] at hlo'
            omega⟩
      · simp only [st5, st4, Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self] at hnew1
        exact Or.inr ⟨by omega, hnew1.2⟩
    · intro a ha hncf hntbl
      have hncf1 : ¬ CF.rep.foot cfH xcf1 a := fun hfc => by
        rcases hE_ft a hfc with hold | hnew
        · exact hncf hold
        · omega
      rw [hfr' a ha hncf1 (by omega)]
      change stB.mem a = st.mem a
      rw [hB_fr a (by omega) (fun hf => hf), hmem3_ne a (by omega), hE_fr a (by omega) hncf]
    · intro j hj
      have hkj := hkeep' j (by omega)
      have hji : j ≠ i := by omega
      refine ⟨hkj.1.trans (by simp [brH1, hji]), hkj.2.1.trans (by simp [xBR1, hji]), fun a ha => ?_⟩
      rw [hkj.2.2 a (by simpa [brH1, xBR1, hji] using ha)]
      change stB.mem a = st.mem a
      have hftj := (hprev j hj).2.2.2 a ha
      rw [hB_fr a (by omega) (fun hf => hf), hmem3_ne a (by omega), hE_fr a hftj.2.1 hftj.2.2]
    · rw [sum_Ico_cons hilt, sum_Ico_cons hilt, hphi_i_eq]
      rw [hcf5_phi] at hcostRest
      rw [hcfs_i_G] at hcostE
      change cE + CF.rep.phi cfH xcf1 stE.mem ≤ _ + CF.rep.phi cfH xcf st.mem at hcostE
      change cB + BR.rep.phi expEnd xi stB.mem ≤ S.mul capExp limbMul * (tr₀ i).machCost at hcostB
      simp only [argsSize_cons, argsSize_nil, Expr.size, Nat.mul_succ]
      omega

/-- **Execution of `asmInitBranchesLoop`**: exports and initializes all `k` branches `j = 0 .. k - 1`,
stores their handles at `tbl .. tbl + k - 1`, keeps their footprints inside `[hStart, hEnd)` and
pairwise disjoint from each other and from `CF`, leaves memory below `hStart` outside `CF`'s
footprint and `[tbl, tbl + k)` untouched, and telescopes `CF.rep.phi`. -/
theorem asmInitBranchesLoop_runs
    {S : AsmBranchSpec} {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    {graph lengths cOrdPtr k M N vCap eCap cfH tbl cWords hStart : ℕ}
    {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {cfs : CompFamilyAbs} {xcf : CF.rep.τ}
    (st : State) (ω : ℕ → Bool)
    (hfmt : fmt.limbBits = 4) (hPL : fmt.precision ≤ 4 * L) (hk : 0 < k) (hGval : G.IsValid) (hGne : G.V.Nonempty)
    (hGm : G.m ≤ M) (hGn : G.n ≤ N) (hGn_le : G.n ≤ G.m + 1)
    (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hwCF : (M + N + 2) ^ CFS.wordExp capExp * (L + 1) < 2 ^ w)
    (hwBR : (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hcfs : ∀ j < k, cfs j = initCompLSFWith lsfInit G ℓ₀ k j)
    (hlen_disj_tbl : ∀ a, lengths ≤ a → a < lengths + eCap * L → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hG_le : graph + dynGraphSize vCap eCap ≤ hStart)
    (hcOrd_le : cOrdPtr + cWords ≤ hStart) (hcWords_le : cWords ≤ 1 + 6 * G.m)
    (hrot : IsRotationOrder G ord) (htbl_le : tbl + k ≤ hStart)
    (hcfFoot : ∀ a, CF.rep.foot cfH xcf a → a < hStart ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
      ¬ (graph ≤ a ∧ a < graph + dynGraphSize vCap eCap) ∧
      ¬ (cOrdPtr ≤ a ∧ a < cOrdPtr + cWords))
    (hG_disj_tbl : ∀ a, graph ≤ a → a < graph + dynGraphSize vCap eCap → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hcOrd_disj_tbl : ∀ a, cOrdPtr ≤ a → a < cOrdPtr + cWords → ¬ (tbl ≤ a ∧ a < tbl + k))
    (hargsW : ∀ a ∈ [cfH, graph, cOrdPtr, k, M, N, L, fmt.precision, vCap, eCap, depth, tbl], a < 2 ^ w)
    (hsp : hStart + k * ((CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L) +
      (S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)) < 2 ^ w)
    (hMod : ∀ j < k, AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord)
    (hUpd : ∀ j < k, BranchUpdatesBelow impl
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) 0)
    (r0 : st.regs 0 = graph) (r1 : st.regs 1 = lengths) (r3 : st.regs 3 = cOrdPtr)
    (r4 : st.regs 4 = k)
    (r5 : st.regs 5 = M) (r6 : st.regs 6 = N) (r7 : st.regs 7 = L)
    (r8 : st.regs 8 = fmt.precision) (r10 : st.regs 10 = vCap) (r11 : st.regs 11 = eCap)
    (r12 : st.regs 12 = cfH) (r13 : st.regs 13 = tbl) (r14 : st.regs 14 = hStart)
    (r19 : st.regs 19 = depth)
    (hz : ZeroFrom st.mem hStart) (hcf : CF.rep.rep cfH cfs xcf st.mem)
    (hvCF : CF.vCapOf xcf = vCap) (heCF : CF.eCapOf xcf = eCap)
    (hcfLen : ∀ a, CF.rep.foot cfH xcf a → ¬ (lengths ≤ a ∧ a < lengths + eCap * L))
    (hG : DynGraphAt st.mem graph vCap eCap G) (hOrd : OrdListAt st.mem cOrdPtr ord cWords)
    (hLen : BranchLengthsAt st.mem lengths eCap L fmt.precision hStart G ℓ₀) :
    let expSp := (CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L)
    let initSp := (S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)
    let tr₀ := fun j => initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    ∃ (st' : State) (c : ℕ) (xcf' : CF.rep.τ) (brH' : ℕ → ℕ) (xBR' : ℕ → BR.rep.τ),
      Runs w p ω (asmInitBranchesLoop CF.fExport bp.fInit) st .normal st' c ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 18 → st'.regs r = st.regs r) ∧
      hStart ≤ st'.regs 14 ∧ st'.regs 14 ≤ hStart + k * (expSp + initSp) ∧
      ZeroFrom st'.mem (st'.regs 14) ∧
      CF.rep.rep cfH cfs xcf' st'.mem ∧
      CF.vCapOf xcf' = vCap ∧ CF.eCapOf xcf' = eCap ∧
      (∀ a, CF.rep.foot cfH xcf' a → CF.rep.foot cfH xcf a ∨ (hStart ≤ a ∧ a < st'.regs 14)) ∧
      (∀ a < hStart, ¬ CF.rep.foot cfH xcf a → ¬ (tbl ≤ a ∧ a < tbl + k) → st'.mem a = st.mem a) ∧
      (∀ j < k, st'.mem (tbl + j) = brH' j ∧ brH' j ≤ st'.regs 14 ∧
        BR.rep.rep (brH' j) ⟨tr₀ j, ord, vCap, eCap⟩ (xBR' j) st'.mem ∧
        ∀ a, BR.rep.foot (brH' j) (xBR' j) a →
          hStart ≤ a ∧ a < st'.regs 14 ∧ ¬ CF.rep.foot cfH xcf' a) ∧
      (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH' j₁) (xBR' j₁) a → ¬ BR.rep.foot (brH' j₂) (xBR' j₂) a) ∧
      c + CF.rep.phi cfH xcf' st'.mem +
        (Finset.range k).sum (fun j => BR.rep.phi (brH' j) (xBR' j) st'.mem) ≤
        CFS.mul capExp limbMul * (k * ((G.n + G.m + 1) * bundleLogFactor M N)) +
        (Finset.range k).sum (fun j => S.mul capExp limbMul * (tr₀ j).machCost) + 70 * k + 20 +
        CF.rep.phi cfH xcf st.mem := by
  intro expSp initSp tr₀
  have h15 : Runs w p ω (.assign 15 (.const 0)) st .normal
      { st with regs := Function.update st.regs 15 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st0 : State := { st with regs := Function.update st.regs 15 0 }
  obtain ⟨st', cL, xcf', brH', xDep, hrunL, hregsL, hlo, hhi, hz', hcf', hvCF', heCF', hcfFt', hfr, _, hall,
      hdisj, hcost⟩ :=
    asmInitBranchesLoop_go BR hfmt hPL hk hGval hGne hGm hGn hGn_le hkCap hcap hwCF hwBR hw4 hcfs
      hlen_disj_tbl hG_le hcOrd_le hcWords_le hrot htbl_le hG_disj_tbl hcOrd_disj_tbl hargsW hsp
      hMod hUpd ω k 0 st0 xcf (fun _ => 0) (fun _ hj => absurd hj (Nat.not_lt_zero _))
      (Nat.zero_add k)
      (by simp [st0, r0]) (by simp [st0, r1]) (by simp [st0, r3]) (by simp [st0, r4]) (by simp [st0, r5])
      (by simp [st0, r6]) (by simp [st0, r7]) (by simp [st0, r8]) (by simp [st0, r10])
      (by simp [st0, r11]) (by simp [st0, r12]) (by simp [st0, r13]) (by simp [st0])
      (by simp [st0, r19])
      (by simp [st0, r14]) (by simp [st0, r14]) (by simpa [st0, r14] using hz) hcf hvCF heCF
      (by simpa [st0, r14] using hcfFoot) hcfLen hG hOrd hLen
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
  let xFun : ℕ → BR.rep.τ := fun j => if hj : j < k then xDep j hj else xDep 0 hk
  rw [Nat.Ico_zero_eq_range] at hcost
  have hsum_eq : (Finset.range k).sum (fun j => BR.rep.phi (brH' j) (xFun j) st'.mem) =
      (Finset.range k).sum (fun j => if hj : j < k then BR.rep.phi (brH' j) (xDep j hj) st'.mem else 0) :=
    Finset.sum_congr rfl fun j hj => by
      have hjk := Finset.mem_range.mp hj
      simp only [xFun, hjk, ↓reduceDIte]
  have hsum_split :
      (Finset.range k).sum (fun j =>
        CFS.mul capExp limbMul * ((G.n + G.m + 1) * bundleLogFactor M N) +
        S.mul capExp limbMul * (tr₀ j).machCost) =
      CFS.mul capExp limbMul * (k * ((G.n + G.m + 1) * bundleLogFactor M N)) +
      (Finset.range k).sum (fun j => S.mul capExp limbMul * (tr₀ j).machCost) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  refine ⟨st', _, xcf', brH', xFun, runs_seq_iff.mpr (Or.inr ⟨st0, _, _, h15, hrunL, rfl⟩),
    fun r hr14 hr15 hr18 => (hregsL r hr14 hr15 hr18).trans (by simp [st0, hr15]),
    by simpa [st0, r14] using hlo, hhi, hz', hcf', hvCF', heCF', by simpa [st0, r14] using hcfFt', by simpa using hfr,
    fun j hj => by simp only [xFun, hj, ↓reduceDIte]; exact hall j hj,
    fun j₁ h₁ j₂ h₂ hne a ha1 ha2 => by
      simp only [xFun, h₁, h₂, ↓reduceDIte] at ha1 ha2
      exact hdisj j₁ h₁ j₂ h₂ hne a ha1 ha2, ?_⟩
  rw [hsum_eq]
  rw [hsum_split] at hcost
  change cL + CF.rep.phi cfH xcf' st'.mem + _ ≤ _ + CF.rep.phi cfH xcf st.mem at hcost
  simp only [Expr.size]
  omega

end MinCostFlow.SparseCore.Program
