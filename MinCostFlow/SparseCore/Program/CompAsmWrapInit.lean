module

public import MinCostFlow.SparseCore.Program.CompAsmWrapOps
public import MinCostFlow.SparseCore.Program.AssemblyBridge
import MinCostFlow.LSF.Program.InitTreeLSSTOpsBase
import MinCostFlow.LSF.Program.Utils
import WordRAM.Tactic

/-!
# Verification of Wrapper `init` and Assembly of `AsmCompFamilyAt` / `ScCompFamilyHyp` (`CompAsmWrapInit`)

Verifies `compAsmInitProc` (index `0` of `compAsmProcs`, `CompAsmWrapDefs.lean`) against
`AsmCompFamilyAt.init_runs` (`AssemblyTopIface.lean`) and packages the complete deterministic
P4 implementation:
* `compAsmInit_runs`: runs `initCopyGStmt` (`gCopy`), computes `L_w` via `log2Stmt` when `1 ≤ G.m`
  (or `L_w = 1` in `O(1)` when `G.m = 0`), invokes `compInitProc` at `bComp`, stores the 2-word
  handle `[bComp, gCopy]` at `h`, and proves `compAsmRepPred`, `Respects`, and the `bundleLogFactor^3`
  init cost bound.
* `compAsmFamilyAt`: concrete `AsmCompFamilyAt` instance at `(compAsmSpec, canonicalLSFInit)`.
* `compAsmFamilyHyp`: concrete `ScCompFamilyHyp` instance with `wordExp 3 = 7 ≤ 39`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num MinCostFlow.MinRatio

/-! ## 1. Helper lemmas for `log2` and `canonLw` on-machine computation -/

private lemma log2_log2_add_two_le (n : ℕ) :
    Nat.log 2 (Nat.log 2 (n + 2) + 2) ≤ Nat.log 2 (n + 2) := by
  have h1 : 1 ≤ Nat.log 2 (n + 2) :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  by_cases hlt : Nat.log 2 (n + 2) = 1
  · rw [hlt]; decide
  · have h2 : 2 ≤ Nat.log 2 (n + 2) := by omega
    have hpow : Nat.log 2 (n + 2) + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := by
      have hind : ∀ t ≥ 2, t + 2 < 2 ^ (t + 1) := by
        intro t ht
        induction t with
        | zero => omega
        | succ k ih =>
          by_cases hk : k = 1
          · subst hk; decide
          · have := ih (by omega)
            rw [pow_succ]; omega
      exact hind _ h2
    have hlt2 := Nat.log_lt_of_lt_pow (by omega) hpow
    omega

private lemma compAsmLogLw_runs {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {w L k n0 m0 : ℕ} {st : State} {ω : ℕ → Bool}
    (hw128 : 128 < 2 ^ w)
    (hr2 : st.regs 2 = L) (hr4 : st.regs 4 = k) (hr8 : st.regs 8 = n0) (hr9 : st.regs 9 = m0)
    (hL_w : L < 2 ^ w) (hk1_w : k + 1 < 2 ^ w) (hn2_w : n0 + 2 < 2 ^ w) (_hm0_w : m0 < 2 ^ w)
    (hLw_w : canonLw K_AN L n0 k < 2 ^ w) :
    let p : Program := ⟨compAsmProcs Q_AN c_AN K_AN hQ⟩
    let rhoConstLog := Nat.log 2 (lemma55RhoConst K_AN + 1)
    let L_w := if m0 = 0 then 1 else canonLw K_AN L n0 k
    ∃ st' c,
      Runs w p ω
        (.cond (.reg 9)
          (.call 16 compAsmIdxLog [.bin .add (.reg 4) (.const 1)] ;;
           .call 17 compAsmIdxLog [.bin .add (.reg 8) (.const 2)] ;;
           .call 17 compAsmIdxLog [.bin .add (.reg 17) (.const 2)] ;;
           .assign 16 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 2) (.const rhoConstLog))
             (.reg 16)) (.bin .mul (.const 6) (.reg 17))) (.const 8)))
          (.assign 16 (.const 1)))
        st .normal st' c ∧
      st'.mem = st.mem ∧
      st'.regs 16 = L_w ∧
      (∀ r, r ≠ 16 → r ≠ 17 → st'.regs r = st.regs r) ∧
      c ≤ (if m0 = 0 then 0 else 20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (n0 + 2)) + 150 := by
  intro p rhoConstLog L_w
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw8 : 8 < 2 ^ w := by omega
  have hrho_w : rhoConstLog < 2 ^ w := by omega
  by_cases hm0 : m0 = 0
  · simp only [hm0, ↓reduceIte] at L_w ⊢
    have hcond : Expr.eval w st (.reg 9) = some 0 := by simp [Expr.eval, hr9, hm0]
    let st' : State := { st with regs := Function.update st.regs 16 1 }
    have hbr : Runs w p ω (.assign 16 (.const 1)) st .normal st' 2 :=
      runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
    exact ⟨st', 1 + 2 + 1, runs_cond_iff.mpr ⟨0, 2, hcond, by simpa using hbr, by simp [Expr.size]⟩, rfl,
      by simp [st', L_w, hm0], fun r hr16 _ => by simp [st', hr16], by omega⟩
  · simp only [hm0, ↓reduceIte] at L_w ⊢
    have hcond : Expr.eval w st (.reg 9) = some m0 := by simp [Expr.eval, hr9]
    have hLog := log2_meetsContract (w := w) hw2 (compAsmProg_getLog Q_AN c_AN K_AN hQ)
    -- Call 1: `log2 (k + 1)`
    obtain ⟨st1, c1, v1, hr1, ⟨x1, hx1, hm1, hv1⟩, h1_16, h1_ne, hc1⟩ :=
      runs_call_of_meetsContract (r := 16) hLog
        (show evalArgs w st [.bin .add (.reg 4) (.const 1)] = some [k + 1] by
          simp [evalArgs, Expr.eval, hr4, hw1, hk1_w])
        (fun a ha => by simp at ha; subst ha; exact hk1_w)
        ⟨k + 1, rfl, by omega⟩ ω
    simp only [List.cons.injEq, and_true] at hx1; subst hx1; subst hv1
    -- Call 2: `log2 (n0 + 2)`
    have h1_8 : st1.regs 8 = n0 := (h1_ne 8 (by decide)).trans hr8
    obtain ⟨st2, c2, v2, hr2', ⟨x2, hx2, hm2, hv2⟩, h2_17, h2_ne, hc2⟩ :=
      runs_call_of_meetsContract (r := 17) hLog
        (show evalArgs w st1 [.bin .add (.reg 8) (.const 2)] = some [n0 + 2] by
          simp [evalArgs, Expr.eval, h1_8, hw2, hn2_w])
        (fun a ha => by simp at ha; subst ha; exact hn2_w)
        ⟨n0 + 2, rfl, by omega⟩ ω
    simp only [List.cons.injEq, and_true] at hx2; subst hx2; subst hv2
    -- Call 3: `log2 (log2 (n0 + 2) + 2)`
    have hlogn2_w : Nat.log 2 (n0 + 2) + 2 < 2 ^ w := by
      have hlt_w : Nat.log 2 (n0 + 2) < w := Nat.log_lt_of_lt_pow (by omega) hn2_w
      have hw3 : 3 ≤ w := by
        by_contra hlt3
        have : 2 ^ w ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hw_pow : ∀ t ≥ 3, t + 1 < 2 ^ t := by
        intro t ht
        induction t with
        | zero => omega
        | succ m ih =>
          by_cases hm : m = 2
          · subst hm; decide
          · have := ih (by omega); rw [pow_succ]; omega
      have := hw_pow w hw3
      omega
    obtain ⟨st3, c3, v3, hr3', ⟨x3, hx3, hm3, hv3⟩, h3_17, h3_ne, hc3⟩ :=
      runs_call_of_meetsContract (r := 17) hLog
        (show evalArgs w st2 [.bin .add (.reg 17) (.const 2)] = some [Nat.log 2 (n0 + 2) + 2] by
          simp [evalArgs, Expr.eval, h2_17, hw2, hlogn2_w])
        (fun a ha => by simp at ha; subst ha; exact hlogn2_w)
        ⟨Nat.log 2 (n0 + 2) + 2, rfl, by omega⟩ ω
    simp only [List.cons.injEq, and_true] at hx3; subst hx3; subst hv3
    -- Final assign `r16 := L + rhoConstLog + log2(k+1) + 6 * log2(log2(n0+2)+2) + 8 = canonLw`
    have h3_2 : st3.regs 2 = L := (h3_ne 2 (by decide)).trans ((h2_ne 2 (by decide)).trans ((h1_ne 2 (by decide)).trans hr2))
    have h3_16 : st3.regs 16 = Nat.log 2 (k + 1) := (h3_ne 16 (by decide)).trans ((h2_ne 16 (by decide)).trans h1_16)
    have hLw_eq : L + rhoConstLog + Nat.log 2 (k + 1) + 6 * Nat.log 2 (Nat.log 2 (n0 + 2) + 2) + 8 = L_w := by
      dsimp only [L_w, rhoConstLog, canonLw]; simp only [hm0, ↓reduceIte]
    let st4 : State := { st3 with regs := Function.update st3.regs 16 L_w }
    have hr4' : Runs w p ω
        (.assign 16 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 2) (.const rhoConstLog))
          (.reg 16)) (.bin .mul (.const 6) (.reg 17))) (.const 8)))
        st3 .normal st4 12 := by
      have ha1 : L + rhoConstLog < 2 ^ w := by dsimp only [rhoConstLog, canonLw] at hLw_w ⊢; omega
      have ha2 : L + rhoConstLog + Nat.log 2 (k + 1) < 2 ^ w := by dsimp only [rhoConstLog, canonLw] at hLw_w ⊢; omega
      have ha3 : 6 * Nat.log 2 (Nat.log 2 (n0 + 2) + 2) < 2 ^ w := by dsimp only [rhoConstLog, canonLw] at hLw_w ⊢; omega
      have ha4 : L + rhoConstLog + Nat.log 2 (k + 1) + 6 * Nat.log 2 (Nat.log 2 (n0 + 2) + 2) < 2 ^ w := by
        dsimp only [rhoConstLog, canonLw] at hLw_w ⊢; omega
      have hLw_w' : L_w < 2 ^ w := by simpa [L_w, hm0] using hLw_w
      refine runs_assign_iff.mpr ⟨L_w, ?_, rfl, rfl, by simp [Expr.size]⟩
      rw [← hLw_eq]
      exact Expr.eval_add
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_add (by simp [Expr.eval, h3_2]) (by simp [Expr.eval, hrho_w]) ha1)
            (by simp [Expr.eval, h3_16]) ha2)
          (Expr.eval_mul (by simp [Expr.eval, hw6]) (by simp [Expr.eval, h3_17]) ha3) ha4)
        (by simp [Expr.eval, hw8]) (hLw_eq.symm ▸ hLw_w')
    have hbody := runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + (c3 + 12 + 1) + 1, hr1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3 + 12 + 1, hr2',
        runs_seq_iff.mpr (Or.inr ⟨st3, c3, 12, hr3', hr4', rfl⟩), rfl⟩), rfl⟩)
    have hcost_all : 1 + (c1 + (c2 + (c3 + 12 + 1) + 1) + 1) + 1 ≤
        20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (n0 + 2) + 150 := by
      simp only [log2Contract, argsSize, Expr.size, List.getD_cons_zero] at hc1 hc2 hc3
      have hll := log2_log2_add_two_le n0
      omega
    exact ⟨st4, 1 + (c1 + (c2 + (c3 + 12 + 1) + 1) + 1) + 1,
      runs_cond_iff.mpr ⟨m0, _, hcond, by simpa [hm0] using hbody, by simp [Expr.size]⟩,
      hm3.trans (hm2.trans hm1), by simp [st4],
      fun r hr16 hr17 => by
        simp only [st4, Function.update_of_ne hr16]
        exact (h3_ne r hr17).trans ((h2_ne r hr17).trans (h1_ne r hr16)),
      hcost_all⟩

/-! ## 2. Verification of `compAsmInitProc` (index `0`) -/

/-- Wrapper initialization (`compAsmInitProc`, index `0`) meets `AsmCompFamilyAt.init_runs`. -/
theorem compAsmInit_runs {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {w L capExp limbMul : ℕ} {fmt : Num.Format w}
    (graph lengths k M N vCap eCap h : ℕ) (G : MGraph) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool)
    (_hfmt : fmt.limbBits = 4) (hk : 0 < k) (hG_val : G.IsValid) (hV_ne : G.V.Nonempty)
    (hGm : G.m ≤ M) (hGn : G.n ≤ N)
    (hCFmt : CompInitFormatHyp L fmt.precision k G.m) (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hCap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hw : (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp * (L + 1) < 2 ^ w)
    (hdg : DynGraphAt mem graph vCap eCap G)
    (hg_le : graph + dynGraphSize vCap eCap ≤ h) (hlen_le : lengths + eCap * L ≤ h)
    (hLen : ∀ e ∈ G.E, e < eCap ∧ Num.Valid mem (lengths + e * L) 4 L ∧
      0 < readEdgeValues mem lengths 4 L fmt.precision G.E e)
    (hargs : ∀ a ∈ [graph, lengths, L, fmt.precision, k, vCap, eCap, h], a < 2 ^ w)
    (hz : ZeroFrom mem h)
    (hsp : h + ((compAsmSpec Q_AN c_AN K_AN).initSpace capExp).eval (vCap + eCap + L + k) < 2 ^ w) :
    let p : Program := ⟨compAsmProcs Q_AN c_AN K_AN hQ⟩
    let ℓ₀ := readEdgeValues mem lengths 4 L fmt.precision G.E
    let cfs₀ : CompFamilyAbs := fun j => initCompLSFWith (canonicalLSFInit Q_AN c_AN K_AN L fmt.precision) G ℓ₀ k j
    ∃ body, p.procs[0]? = some body ∧ ∃ o st' c x',
      Runs w p ω body (startState [graph, lengths, L, fmt.precision, k, vCap, eCap, h] mem pos)
        o st' c ∧
      compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision h cfs₀ x' st'.mem ∧
      x'.vCap = vCap ∧ x'.eCap = eCap ∧
      (compAsmRep Q_AN c_AN K_AN hQ L fmt.precision).Respects (fun _ => False) h
        (((compAsmSpec Q_AN c_AN K_AN).initSpace capExp).eval (vCap + eCap + L + k))
        mem o.value h x' st'.mem ∧
      c + compPhiFull x'.k x'.bComp x'.xComp st'.mem ≤
        (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
          (G.n + G.m + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3) := by
  intro p ℓ₀ cfs₀
  set W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L fmt.precision
  set eCap' := max eCap 1
  set lenArr' := if eCap = 0 then h + 2 else lengths
  set gCopy := if eCap = 0 then h + 2 + L else h + 2
  set bComp := gCopy + dynGraphSize vCap eCap
  set L_w := if G.m = 0 then 1 else canonLw K_AN L G.n k
  have hw128 : 128 < 2 ^ w := compAsm_hw128 hw
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hP_le : fmt.precision ≤ 4 * L := by have := hCFmt.2.2.1; omega
  have hGn_vCap : G.n ≤ vCap := dynGraphAt_n_le_vCap hdg
  have hGm_eCap : G.m ≤ eCap := by
    have hElt : ∀ e ∈ G.E, e < eCap := hdg.2.2.1
    have hsub : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hElt e he)
    change G.E.card ≤ eCap
    simpa using Finset.card_le_card hsub
  have hInitSp := compAsmInitSpace_le (k := k) hQ hRho hP_le hG_val hGn_vCap hGm_eCap graph lenArr' bComp
  dsimp only at hInitSp
  have hsp_poly_lt : h + (2 + L + dynGraphSize vCap eCap +
      compInitSpace W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp]) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left hInitSp h) hsp
  have hgr_w : graph < 2 ^ w := hargs graph (by simp)
  have hlen_w : lengths < 2 ^ w := hargs lengths (by simp)
  have hL_w : L < 2 ^ w := hargs L (by simp)
  have hP_w : fmt.precision < 2 ^ w := hargs fmt.precision (by simp)
  have hk_w : k < 2 ^ w := hargs k (by simp)
  have hvC_w : vCap < 2 ^ w := hargs vCap (by simp)
  have heC_w : eCap < 2 ^ w := hargs eCap (by simp)
  have hh_w : h < 2 ^ w := hargs h (by simp)
  have hg_lt_w : graph + dynGraphSize vCap eCap < 2 ^ w := lt_of_le_of_lt hg_le hh_w
  have hbComp_le : bComp ≤ h + 2 + L + dynGraphSize vCap eCap := by dsimp only [bComp, gCopy]; split_ifs <;> omega
  have hbComp_w : bComp < 2 ^ w := by omega
  have hgCopy_w : gCopy < 2 ^ w := by dsimp only [bComp] at hbComp_w; omega
  have hlenArr'_w : lenArr' < 2 ^ w := by dsimp only [lenArr']; split_ifs <;> omega
  have heCap'_w : eCap' < 2 ^ w := by dsimp only [eCap']; omega
  have hLw_lt_w : L_w < 2 ^ w := by
    have : L_w ≤ compStaticSize vCap eCap' L_w := by unfold compStaticSize; omega
    have : compStaticSize vCap eCap' L_w ≤
        compInitSpace W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] := by
      simp only [compInitSpace, List.getD_cons_zero, List.getD_cons_succ]; omega
    omega
  -- Step 1: 4 prefix assigns (`n0, m0, vListPtr, eListPtr`)
  set st0 := startState [graph, lengths, L, fmt.precision, k, vCap, eCap, h] mem pos
  have hm_n : mem (graph + dgNOff) = G.n := hdg.2.2.2.2.2.1
  have hm_m : mem (graph + dgMOff) = G.m := hdg.2.2.2.2.2.2.1
  let st1 : State := { st0 with regs := Function.update st0.regs 8 G.n }
  have hp1 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const dgNOff)))) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨G.n, Expr.eval_load_of_eq (by
      have hgn_w : graph + dgNOff < 2 ^ w := by unfold dynGraphSize at hg_lt_w; unfold dgNOff; omega
      exact Expr.eval_add (by simp [st0, startState, Expr.eval])
        (by simp [Expr.eval, dgNOff, show 2 < 2 ^ w by omega]) hgn_w) hm_n,
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs 9 G.m }
  have hp2 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const dgMOff)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨G.m, Expr.eval_load_of_eq (by
      have hgm_w : graph + dgMOff < 2 ^ w := by unfold dynGraphSize at hg_lt_w; unfold dgMOff; omega
      exact Expr.eval_add (by simp [st1, st0, startState, Expr.eval])
        (by simp [Expr.eval, dgMOff, show 3 < 2 ^ w by omega]) hgm_w) hm_m,
      rfl, rfl, by simp [Expr.size]⟩
  set vListPtr := dgVListBase graph vCap
  set eListPtr := dgEListBase graph vCap eCap
  have hvLP_w : vListPtr < 2 ^ w := by unfold dynGraphSize at hg_lt_w; unfold vListPtr dgVListBase; omega
  have heLP_w : eListPtr < 2 ^ w := by unfold dynGraphSize at hg_lt_w; unfold eListPtr dgEListBase; omega
  let st3 : State := { st2 with regs := Function.update st2.regs 10 vListPtr }
  have hp3 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 5))) st2 .normal st3 6 :=
    runs_assign_iff.mpr ⟨vListPtr, by
      have h4 : 4 < 2 ^ w := by omega
      have hgr4 : graph + 4 < 2 ^ w := by unfold dynGraphSize at hg_lt_w; omega
      exact Expr.eval_add (Expr.eval_add (by simp [st2, st1, st0, startState, Expr.eval])
        (by simp [Expr.eval, h4]) hgr4) (by simp [st2, st1, st0, startState, Expr.eval]) hvLP_w,
      rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs 11 eListPtr }
  have hp4 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
      (.bin .mul (.const 7) (.reg 5))) (.reg 6))) st3 .normal st4 10 :=
    runs_assign_iff.mpr ⟨eListPtr, by
      have h4 : 4 < 2 ^ w := by omega
      have h7 : 7 < 2 ^ w := by omega
      have hgr4 : graph + 4 < 2 ^ w := by unfold dynGraphSize at hg_lt_w; omega
      have h7v : 7 * vCap < 2 ^ w := by unfold dynGraphSize at hg_lt_w; omega
      have hgr47 : graph + 4 + 7 * vCap < 2 ^ w := by unfold dynGraphSize at hg_lt_w; omega
      exact Expr.eval_add (Expr.eval_add (Expr.eval_add (by simp [st3, st2, st1, st0, startState, Expr.eval])
        (by simp [Expr.eval, h4]) hgr4) (Expr.eval_mul (by simp [Expr.eval, h7])
        (by simp [st3, st2, st1, st0, startState, Expr.eval]) h7v) hgr47)
        (by simp [st3, st2, st1, st0, startState, Expr.eval]) heLP_w,
      rfl, rfl, by simp [Expr.size]⟩
  -- Step 2: Branch on `eCap` to set `(r12, r13, r14) = (eCap', lenArr', gCopy)`
  let st5 : State := { st4 with regs := Function.update (Function.update (Function.update st4.regs 12 eCap') 13 lenArr') 14 gCopy }
  have hp5 : ∃ c5, Runs w p ω (.cond (.reg 6)
      (.assign 12 (.reg 6) ;; .assign 13 (.reg 1) ;; .assign 14 (.bin .add (.reg 7) (.const 2)))
      (.assign 12 (.const 1) ;; .assign 13 (.bin .add (.reg 7) (.const 2)) ;;
        .assign 14 (.bin .add (.bin .add (.reg 7) (.const 2)) (.reg 2))))
      st4 .normal st5 c5 ∧ c5 ≤ 16 := by
    have hw1 : 1 < 2 ^ w := by omega
    have hw2 : 2 < 2 ^ w := by omega
    have hh2_w : h + 2 < 2 ^ w := by omega
    by_cases he0 : eCap = 0
    · have heq12 : eCap' = 1 := by dsimp [eCap']; omega
      have heq13 : lenArr' = h + 2 := by simp [lenArr', he0]
      have heq14 : gCopy = h + 2 + L := by simp [gCopy, he0]
      let sA : State := { st4 with regs := Function.update st4.regs 12 eCap' }
      let sB : State := { sA with regs := Function.update sA.regs 13 lenArr' }
      have rA : Runs w p ω (.assign 12 (.const 1)) st4 .normal sA 2 :=
        runs_assign_iff.mpr ⟨eCap', by rw [heq12]; simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
      have rB : Runs w p ω (.assign 13 (.bin .add (.reg 7) (.const 2))) sA .normal sB 4 :=
        runs_assign_iff.mpr ⟨lenArr', by rw [heq13]; simp [sA, st4, st3, st2, st1, st0, startState, Expr.eval, hw2, hh2_w],
          rfl, rfl, by simp [Expr.size]⟩
      have rC : Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 7) (.const 2)) (.reg 2))) sB .normal st5 6 :=
        runs_assign_iff.mpr ⟨gCopy, by
          rw [heq14]
          exact Expr.eval_add (Expr.eval_add (by simp [sB, sA, st4, st3, st2, st1, st0, startState, Expr.eval])
            (by simp [Expr.eval, hw2]) hh2_w) (by simp [sB, sA, st4, st3, st2, st1, st0, startState, Expr.eval]) (heq14 ▸ hgCopy_w),
          rfl, rfl, by simp [Expr.size]⟩
      have hbr := runs_seq_iff.mpr (Or.inr ⟨sA, 2, 11, rA, runs_seq_iff.mpr (Or.inr ⟨sB, 4, 6, rB, rC, rfl⟩), rfl⟩)
      exact ⟨16, runs_cond_iff.mpr ⟨0, 14, by simp [st4, st3, st2, st1, st0, startState, Expr.eval, he0],
        by simpa using hbr, by simp [Expr.size]⟩, by omega⟩
    · have heq12 : eCap' = eCap := by dsimp [eCap']; omega
      have heq13 : lenArr' = lengths := by simp [lenArr', he0]
      have heq14 : gCopy = h + 2 := by simp [gCopy, he0]
      let sA : State := { st4 with regs := Function.update st4.regs 12 eCap' }
      let sB : State := { sA with regs := Function.update sA.regs 13 lenArr' }
      have rA : Runs w p ω (.assign 12 (.reg 6)) st4 .normal sA 2 :=
        runs_assign_iff.mpr ⟨eCap', by rw [heq12]; simp [st4, st3, st2, st1, st0, startState, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have rB : Runs w p ω (.assign 13 (.reg 1)) sA .normal sB 2 :=
        runs_assign_iff.mpr ⟨lenArr', by rw [heq13]; simp [sA, st4, st3, st2, st1, st0, startState, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have rC : Runs w p ω (.assign 14 (.bin .add (.reg 7) (.const 2))) sB .normal st5 4 :=
        runs_assign_iff.mpr ⟨gCopy, by rw [heq14]; simp [sB, sA, st4, st3, st2, st1, st0, startState, Expr.eval, hw2, hh2_w],
          rfl, rfl, by simp [Expr.size]⟩
      have hbr := runs_seq_iff.mpr (Or.inr ⟨sA, 2, 7, rA, runs_seq_iff.mpr (Or.inr ⟨sB, 2, 4, rB, rC, rfl⟩), rfl⟩)
      exact ⟨12, runs_cond_iff.mpr ⟨eCap, 10, by simp [st4, st3, st2, st1, st0, startState, Expr.eval],
        by simpa [he0] using hbr, by simp [Expr.size]⟩, by omega⟩
  obtain ⟨c5, hp5_run, hc5⟩ := hp5
  -- Step 3: Call `initCopyGStmt` to populate `DynGraphAt` at `gCopy`
  obtain ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩ := hdg.2.2.2.2.2.2.2.2.1
  obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hdg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCopyG := initCopyG_meetsContract (w := w) (vCap0 := vCap) (eCap0 := eCap)
    (vCap := vCap) (eCap := eCap) (G₀ := G) (eList := eL) (vList := vL)
    (compAsmProg_getCopyG Q_AN c_AN K_AN hQ) (compAsmProg_hasDg Q_AN c_AN K_AN hQ)
  have hgCopy_ge : h + 2 ≤ gCopy := by dsimp [gCopy]; split_ifs <;> omega
  have hvLP_bd : vListPtr + G.n ≤ graph + dynGraphSize vCap eCap := by
    unfold vListPtr dgVListBase dynGraphSize; omega
  have heLP_bd : eListPtr + G.m ≤ graph + dynGraphSize vCap eCap := by
    unfold eListPtr dgEListBase dynGraphSize; omega
  have hCopyGPre : (initCopyGContract w vCap eCap vCap eCap G eL vL).pre
      [graph, gCopy, eListPtr, vListPtr, vCap, eCap, G.n, G.m] mem :=
    ⟨graph, gCopy, eListPtr, vListPtr, G.n, G.m, rfl, hw16, hG_val, rfl, rfl,
      hdg.2.1, hdg.2.2.1, hdg, hg_lt_w, Or.inl (by omega),
      heL_len, heL_nd, heL_mem, heL_at, by omega, Or.inl (by omega),
      hvL_len, hvL_nd, hvL_mem, hvL_at, by omega, Or.inl (by omega),
      hbComp_w, fun i hi => hz (gCopy + i) (by omega)⟩
  obtain ⟨st6, cCopyG, _, hp6, hCopyGPost, _, hr6_ne, hcCopyG⟩ :=
    runs_call_of_meetsContract (r := 15) hCopyG
      (show evalArgs w st5 [.reg 0, .reg 14, .reg 11, .reg 10, .reg 5, .reg 6, .reg 8, .reg 9] =
          some [graph, gCopy, eListPtr, vListPtr, vCap, eCap, G.n, G.m] by
        simp [evalArgs, Expr.eval, st5, st4, st3, st2, st1, st0, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hCopyGPre ω
  rcases hCopyGPost with ⟨_, _, _, _, _, _, hEqCG, _, hdg_copy, hCG_fr⟩
  simp only [List.cons.injEq, and_true, true_and] at hEqCG
  rcases hEqCG with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- Step 4: Compute `bComp` into `r15`
  let st7 : State := { st6 with regs := Function.update st6.regs 15 bComp }
  have hp7 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.bin .add (.bin .add (.const 4)
      (.bin .mul (.const 7) (.reg 5))) (.bin .mul (.const 9) (.reg 6))))) st6 .normal st7 12 := by
    have h4 : 4 < 2 ^ w := by omega
    have h7 : 7 < 2 ^ w := by omega
    have h9 : 9 < 2 ^ w := by omega
    have h7v : 7 * vCap < 2 ^ w := by dsimp only [bComp, dynGraphSize] at hbComp_w; omega
    have h9e : 9 * eCap < 2 ^ w := by dsimp only [bComp, dynGraphSize] at hbComp_w; omega
    have h47v : 4 + 7 * vCap < 2 ^ w := by dsimp only [bComp, dynGraphSize] at hbComp_w; omega
    have hdg_w : 4 + 7 * vCap + 9 * eCap < 2 ^ w := by dsimp only [bComp, dynGraphSize] at hbComp_w; omega
    have hr14 : st6.regs 14 = gCopy := by rw [hr6_ne 14 (by decide)]; simp [st5]
    have hr5 : st6.regs 5 = vCap := by rw [hr6_ne 5 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState]
    have hr6 : st6.regs 6 = eCap := by rw [hr6_ne 6 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState]
    refine runs_assign_iff.mpr ⟨bComp, ?_, rfl, rfl, by simp [Expr.size]⟩
    exact Expr.eval_add (by simp [Expr.eval, hr14])
      (Expr.eval_add (Expr.eval_add (by simp [Expr.eval, h4])
        (Expr.eval_mul (by simp [Expr.eval, h7]) (by simp [Expr.eval, hr5]) h7v) h47v)
        (Expr.eval_mul (by simp [Expr.eval, h9]) (by simp [Expr.eval, hr6]) h9e) hdg_w)
      hbComp_w
  -- Step 5: Compute `L_w` via `compAsmLogLw_runs`
  have hcanonLw_w : canonLw K_AN L G.n k < 2 ^ w := by
    by_cases hm0 : G.m = 0
    · have h1 := canonLw_le_linear (K_AN := K_AN) (L := L) (n := G.n) (k := k) hRho
      have h2 : L + k + 6 * G.n + 100 ≤
          ((compAsmSpec Q_AN c_AN K_AN).initSpace capExp).eval (vCap + eCap + L + k) := by
        unfold compAsmSpec compAsmInitSpacePoly compAsmInitSpaceCoeff PolyBound.eval
        set X := vCap + eCap + L + k + 2
        have hX1 : 1 ≤ X := by omega
        have hX6 : X ≤ X ^ 6 := Nat.le_self_pow (by decide) X
        have hC1 : 1 ≤ (WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) * (max c_AN 1 + 1) ^ 2 :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.pow_pos (Nat.succ_pos _))
        have h100 : 100 * X ≤ 30000000 * (WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) *
            (max c_AN 1 + 1) ^ 2 * X ^ 6 := by
          have : 100 ≤ 30000000 * ((WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) * (max c_AN 1 + 1) ^ 2) := by
            have := Nat.mul_le_mul_left 30000000 hC1; omega
          have heq : 30000000 * (WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) * (max c_AN 1 + 1) ^ 2 =
              30000000 * ((WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) * (max c_AN 1 + 1) ^ 2) := by ring
          rw [heq]; exact Nat.mul_le_mul this hX6
        have hlin : L + k + 6 * G.n + 100 ≤ 100 * X := by omega
        exact hlin.trans h100
      omega
    · simpa [L_w, hm0] using hLw_lt_w
  have hk1_w : k + 1 < 2 ^ w := by
    have : k + 1 ≤ ((compAsmSpec Q_AN c_AN K_AN).initSpace capExp).eval (vCap + eCap + L + k) := by
      unfold compAsmSpec compAsmInitSpacePoly compAsmInitSpaceCoeff PolyBound.eval
      dsimp only
      have hC1 : 1 ≤ 30000000 * (WideWord.simScale Q_AN + 1) * (⌈max K_AN 1⌉₊ + 1) * (max c_AN 1 + 1) ^ 2 :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _)) (Nat.pow_pos (Nat.succ_pos _))
      exact le_trans (by omega) (le_trans (Nat.le_self_pow (n := 6) (by decide) _) (Nat.le_mul_of_pos_left _ hC1))
    omega
  have hn2_w : G.n + 2 < 2 ^ w := by omega
  obtain ⟨st8, cLog, hp8, hmem8_eq, hr8_16, hr8_ne, hcLog⟩ :=
    compAsmLogLw_runs hQ hRho (w := w) (L := L) (k := k) (n0 := G.n) (m0 := G.m) (st := st7) (ω := ω)
      hw128
      (by simp [st7]; rw [hr6_ne 2 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [st7]; rw [hr6_ne 4 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [st7]; rw [hr6_ne 8 (by decide)]; simp [st5, st4, st3, st2, st1])
      (by simp [st7]; rw [hr6_ne 9 (by decide)]; simp [st5, st4, st3, st2])
      hL_w hk1_w hn2_w (by omega) hcanonLw_w
  -- Step 6: Call `compInitProc` at `[graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp]`
  have hmem8_ag_low : ∀ a < h, st8.mem a = mem a := fun a ha =>
    hmem8_eq ▸ hCG_fr a (Or.inl (by omega))
  have hdg_st8 : DynGraphAt st8.mem graph vCap eCap G :=
    dynGraphAt_of_agree hdg fun a ha1 ha2 => hmem8_ag_low a (by omega)
  have hz8 : ZeroFrom st8.mem bComp := fun a ha =>
    hmem8_eq ▸ (hCG_fr a (Or.inr ha)).trans (hz a (by omega))
  have hlenArr'_le : lenArr' + eCap' * L ≤ bComp := by
    dsimp only [lenArr', eCap', bComp, gCopy]
    split_ifs with he0
    · have : max eCap 1 = 1 := by omega
      rw [this]; omega
    · have : max eCap 1 = eCap := by omega
      rw [this]; omega
  have hLen_st8 : ∀ e ∈ G.E, Valid st8.mem (lenArr' + e * L) 4 L ∧
      0 < fixVal st8.mem (lenArr' + e * L) 4 L fmt.precision := by
    intro e he
    obtain ⟨helt, hval, hpos⟩ := hLen e he
    have he0 : eCap ≠ 0 := by omega
    have hlen_eq : lenArr' = lengths := by simp [lenArr', he0]
    rw [hlen_eq]
    have hag : ∀ i < L, st8.mem (lengths + e * L + i) = mem (lengths + e * L + i) := fun i hi => by
      have hmul : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L helt
      have : e * L + L = (e + 1) * L := by ring
      exact hmem8_ag_low _ (by omega)
    refine ⟨fun i hi => (hag i hi).symm ▸ hval i hi, ?_⟩
    simp only [fixVal, intVal_congr hag]
    simpa [readEdgeValues, he, fixVal] using hpos
  have hWinPre : ∀ C ∈ edgefulComps G, W.winPre w k L_w vCap eCap' (compGraph G C) := by
    intro C hC
    have hC_mem : C ∈ components G := (Finset.mem_filter.mp hC).1
    have hCm1 : 1 ≤ (compGraph G C).m := (Finset.mem_filter.mp hC).2
    have hCm_le : (compGraph G C).m ≤ G.m := compGraph_m_le
    have hGm_ne : G.m ≠ 0 := by omega
    have hLw_eq : L_w = canonLw K_AN L G.n k := by simp [L_w, hGm_ne]
    refine ⟨hCFmt.1, hCFmt.2.1, hCFmt.2.2.1, hCFmt.2.2.2.1, ?_, ?_, ?_⟩
    · have hmul : 32 * ((compGraph G C).E.card + 1) * 2 ^ fmt.precision ≤
          32 * (G.m + 1) * 2 ^ fmt.precision :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 (by change (compGraph G C).m + 1 ≤ G.m + 1; omega))
      exact lt_of_le_of_lt hmul hCFmt.2.2.2.2
    · rw [hLw_eq]; exact canonLw_mono_n K_AN L k (compGraph_n_le hC_mem)
    · exact canonWordBits_le_of_initSpace hQ hRho hP_le hG_val hGn_vCap hGm_eCap
        hdg.2.1 hdg.2.2.1 hC hsp
  have hInitPre : (compLSFDSFullWithSplits W w k G).initPre
      [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] st8.mem :=
    ⟨graph, vCap, eCap, lenArr', L_w, vCap, eCap', bComp, rfl, hk,
      by dsimp [L_w]; split_ifs <;> [omega; (unfold canonLw; omega)],
      by change 2 ≤ 4 * L_w; dsimp [L_w]; split_ifs <;> [omega; (unfold canonLw; omega)],
      by change 4 < 2 ^ w; omega, le_max_right _ _, hw16, hG_val, hV_ne, hdg_st8,
      le_rfl, le_max_left _ _, by omega, hlenArr'_le, hLen_st8, hWinPre⟩
  have hInitArgs : ∀ a ∈ [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hInitSp_lt : bComp + (compLSFDSFullWithSplits W w k G).initSpace
      [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] st8.mem < 2 ^ w := by
    change bComp + compInitSpace W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] < 2 ^ w
    omega
  obtain ⟨bodyI, hbodyI, oI, stI, cI, SI, xComp, hrI, hcompI, hpostI, hrespI, hcostI,
      hxV, hxE, hxLw⟩ :=
    compLSFProcs_init_runs (W := W) (G₀ := G) (pos := st8.pos) (ω := ω)
      (compAsmProg_hasComp Q_AN c_AN K_AN hQ L fmt.precision) hInitPre hInitArgs hz8 hInitSp_lt
  let st9 : State := { stI with regs := Function.update st8.regs 18 oI.value }
  have hp9 : Runs w p ω (.call 18 compAsmIdxCompInit
      [.reg 0, .reg 13, .reg 2, .reg 3, .reg 4, .reg 16, .reg 5, .reg 12, .reg 15])
      st8 .normal st9 (9 + cI + 1) := by
    rw [runs_call_iff]
    have hreg : ∀ r ∈ [0, 13, 2, 3, 4, 5, 12], st8.regs r = st5.regs r := fun r hr => by
      have h16 : r ≠ 16 := by simp at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have h17 : r ≠ 17 := by simp at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have h15 : r ≠ 15 := by simp at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      exact (hr8_ne r h16 h17).trans (by simp [st7, h15]; exact hr6_ne r h15)
    have hr15 : st8.regs 15 = bComp := (hr8_ne 15 (by decide) (by decide)).trans (by simp [st7])
    refine ⟨[graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp], bodyI, oI, stI, cI, ?_,
      hbodyI, hrI, rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp only [evalArgs, Expr.eval,
      hreg 0 (by simp), hreg 13 (by simp), hreg 2 (by simp), hreg 3 (by simp),
      hreg 4 (by simp), hr8_16, hreg 5 (by simp), hreg 12 (by simp), hr15]
    simp [st5, st4, st3, st2, st1, st0, startState, L_w]
  -- Step 7: Store `[bComp, gCopy]` at `[h, h + 1]` and return `oI.value`
  rcases hrespI with ⟨hloI, hhiI, hzI, hfrI, hftI⟩
  simp only [heapArg, List.getLastD_cons, List.getLastD_nil] at hloI hhiI hfrI hftI
  have hr9_7 : st9.regs 7 = h := by
    simp only [st9, Function.update_of_ne (by decide : (7 : ℕ) ≠ 18)]
    exact (hr8_ne 7 (by decide) (by decide)).trans (by simp [st7]; rw [hr6_ne 7 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
  have hr9_14 : st9.regs 14 = gCopy := by
    simp only [st9, Function.update_of_ne (by decide : (14 : ℕ) ≠ 18)]
    exact (hr8_ne 14 (by decide) (by decide)).trans (by simp [st7]; rw [hr6_ne 14 (by decide)]; simp [st5])
  have hr9_15 : st9.regs 15 = bComp := by
    simp only [st9, Function.update_of_ne (by decide : (15 : ℕ) ≠ 18)]
    exact (hr8_ne 15 (by decide) (by decide)).trans (by simp [st7])
  let st10 : State := { st9 with mem := Function.update st9.mem h bComp }
  have hp10 : Runs w p ω (.store (.reg 7) (.reg 15)) st9 .normal st10 3 :=
    runs_store_iff.mpr ⟨h, bComp, by simp [Expr.eval, hr9_7],
      by simp [Expr.eval, hr9_15], rfl, rfl, by simp [Expr.size]⟩
  let st11 : State := { st10 with mem := Function.update st10.mem (h + 1) gCopy }
  have hp11 : Runs w p ω (.store (.bin .add (.reg 7) (.const 1)) (.reg 14)) st10 .normal st11 5 :=
    runs_store_iff.mpr ⟨h + 1, gCopy,
      by simp [Expr.eval, st10, hr9_7, show 1 < 2 ^ w by omega, show h + 1 < 2 ^ w by omega],
      by simp [Expr.eval, st10, hr9_14], rfl, rfl, by simp [Expr.size]⟩
  have hp12 : Runs w p ω (.ret (.reg 18)) st11 (.returned oI.value) st11 2 :=
    runs_ret_iff.mpr ⟨oI.value, by simp [Expr.eval, st11, st10, st9], rfl, rfl, by simp [Expr.size]⟩
  have hrun : Runs w p ω (compAsmInitProc (compAsmIdxCopyG Q_AN) compAsmIdxLog compAsmIdxCompInit
      (Nat.log 2 (lemma55RhoConst K_AN + 1))) st0 (.returned oI.value) st11
      (69 + c5 + cCopyG + cLog + cI) := by
    unfold compAsmInitProc
    have t11 := runs_seq_iff.mpr (Or.inr ⟨st11, 5, 2, hp11, hp12, rfl⟩)
    have t10 := runs_seq_iff.mpr (Or.inr ⟨st10, 3, 8, hp10, t11, rfl⟩)
    have t9 := runs_seq_iff.mpr (Or.inr ⟨st9, 9 + cI + 1, 12, hp9, t10, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨st8, cLog, (9 + cI + 1) + 12 + 1, hp8, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨st7, 12, cLog + ((9 + cI + 1) + 12 + 1) + 1, hp7, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨st6, cCopyG, _, hp6, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨st5, c5, _, hp5_run, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨st4, 10, _, hp4, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨st3, 6, _, hp3, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, hp2, t3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hp1, t2, by omega⟩)
  -- Representation, `Respects`, and cost bound
  have hmem11_ge2 : ∀ a, h + 2 ≤ a → st11.mem a = stI.mem a := fun a ha => by
    simp only [st11, st10, st9, Function.update_of_ne (by omega : a ≠ h + 1),
      Function.update_of_ne (by omega : a ≠ h)]
  have hmem11_lt : ∀ a < h, st11.mem a = mem a := fun a ha => by
    have h1 : st11.mem a = stI.mem a := by
      simp only [st11, st10, st9, Function.update_of_ne (by omega : a ≠ h + 1),
        Function.update_of_ne (by omega : a ≠ h)]
    exact h1.trans ((hfrI a (by omega) False.elim).trans (hmem8_ag_low a ha))
  have hdg_final : DynGraphAt st11.mem gCopy vCap eCap (cfs₀ 0).G := by
    have hGeq : (cfs₀ 0).G = G := rfl
    rw [hGeq]
    exact dynGraphAt_of_agree hdg_copy fun a ha1 ha2 =>
      (hmem11_ge2 a (by omega)).trans ((hfrI a (by omega) False.elim).trans (by rw [hmem8_eq]))
  have hReadEq : compReadLen st8.mem lenArr' 4 L fmt.precision G = ℓ₀ := by
    funext e
    by_cases he : e ∈ G.E
    · have helt : e < eCap := (hLen e he).1
      have he0 : eCap ≠ 0 := by omega
      have hlen_eq : lenArr' = lengths := by simp [lenArr', he0]
      have hag : ∀ i < L, st8.mem (lengths + e * L + i) = mem (lengths + e * L + i) := fun i hi => by
        have hmul : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L helt
        have : e * L + L = (e + 1) * L := by ring
        exact hmem8_ag_low _ (by omega)
      simp only [compReadLen, ℓ₀, readEdgeValues, he, ↓reduceIte, hlen_eq, fixVal]
      rw [intVal_congr hag]
    · simp [compReadLen, ℓ₀, readEdgeValues, he]
  have hSI_eq : SI = (fun j : Fin k => cfs₀ j.1) := by
    have hp : SI = compLSFInitFamily W.lsfInit G (compReadLen st8.mem lenArr' 4 L fmt.precision G) k := hpostI
    rw [hp, hReadEq]; rfl
  have hcomp_final : CompLSFRepAt W k bComp (fun j : Fin k => cfs₀ j.1) xComp st11.mem :=
    (compLSFRepFull_local W k bComp (fun j : Fin k => cfs₀ j.1) xComp stI.mem st11.mem
      (fun a ha => (hmem11_ge2 a (by have := ha.1; omega)).symm)).1 (hSI_eq ▸ hcompI)
  have hphi_final : compPhiFull k bComp xComp st11.mem = compPhiFull k bComp xComp stI.mem :=
    ((compLSFRepFull_local W k bComp (fun j : Fin k => cfs₀ j.1) xComp stI.mem st11.mem
      (fun a ha => (hmem11_ge2 a (by have := ha.1; omega)).symm)).2).symm
  let x' : CompAsmMeta := ⟨k, vCap, eCap, gCopy, bComp, xComp⟩
  have hrep' : compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision h cfs₀ x' st11.mem := by
    have hG0_eq : (cfs₀ 0).G₀ = G := rfl
    have hk_eq : (cfs₀ 0).k = k := rfl
    refine ⟨by simp [st11, st10, x'],
      by simp [st11, x'], hgCopy_ge, rfl, hk, hk_eq, ?_, ?_, ?_, hdg_final, hcomp_final⟩
    · simpa [List.getD_cons_zero, List.getD_cons_succ] using hxV
    · simpa [List.getD_cons_zero, List.getD_cons_succ] using hxE
    · simpa [List.getD_cons_zero, List.getD_cons_succ, hG0_eq] using hxLw
  have hcost_bound :
      (69 + c5 + cCopyG + cLog + cI) +
        compPhiFull x'.k x'.bComp x'.xComp st11.mem ≤
      (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
        (G.n + G.m + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3) := by
    have hcCG : cCopyG ≤ 8 + (140 * G.n + 600 * G.m + 100) + 1 := by
      simpa [argsSize, Expr.size, initCopyGContract, List.getD_cons_zero, List.getD_cons_succ] using hcCopyG
    have hcost_wrap := compAsmInitCost_le hQ hRho hk hG_val hGn hGm hP_le hkCap hCap.2
      graph lenArr' L_w vCap eCap' bComp
    dsimp only [x', compAsmSpec]
    rw [hphi_final]
    change _ + compPhiFull k bComp xComp stI.mem ≤ _
    have hcostI' : cI + compPhiFull k bComp xComp stI.mem ≤
        compInitCost W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] +
          2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) := by
      simpa [compLSFDSFullWithSplits, compLSFDSFull, compLSFDS, heapArg] using hcostI
    linarith [hc5, hcCG, hcLog, hcostI', hcost_wrap]
  have hvI : (Outcome.returned oI.value).value = oI.value := rfl
  have hInitSp' : 2 + L + dynGraphSize vCap eCap +
      compInitSpace W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] ≤
      ((compAsmSpec Q_AN c_AN K_AN).initSpace capExp).eval (vCap + eCap + L + k) := hInitSp
  refine ⟨compAsmInitProc (compAsmIdxCopyG Q_AN) compAsmIdxLog compAsmIdxCompInit
      (Nat.log 2 (lemma55RhoConst K_AN + 1)), compAsmProg_get0 Q_AN c_AN K_AN hQ,
    .returned oI.value, st11,
    69 + c5 + cCopyG + cLog + cI, x',
    hrun, hrep', rfl, rfl,
    ⟨by rw [hvI]; omega, by
        rw [hvI]
        have hhi' : oI.value ≤ bComp + compInitSpace W k G [graph, lenArr', L, fmt.precision, k, L_w, vCap, eCap', bComp] := hhiI
        omega,
      fun a ha => by rw [hvI] at ha; exact (hmem11_ge2 a (by omega)).trans (hzI a ha),
      fun a ha _ => hmem11_lt a ha,
      fun a ha => by
        rw [hvI]
        have hb_eq : bComp = gCopy + dynGraphSize vCap eCap := rfl
        rcases ha with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | h3'
        · exact Or.inr ⟨h1', by omega⟩
        · dsimp only [x'] at h1' h2'
          exact Or.inr ⟨by omega, by omega⟩
        · rcases hftI a h3' with h4' | ⟨h4', h5'⟩
          · exact False.elim h4'
          · exact Or.inr ⟨by omega, h5'⟩⟩,
    hcost_bound⟩

/-! ## 3. Complete `AsmCompFamilyAt` and `ScCompFamilyHyp` assembly -/

/-- Complete `AsmCompFamilyAt` instance for `compAsmProcs` (`CompAsmWrapDefs.lean`). -/
def compAsmFamilyAt {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    (w : ℕ) (fmt : Num.Format w) (L capExp limbMul : ℕ)
    (hBatchCost : ∀ (k b batchPtr heap totalWords : ℕ) (G₀ : MGraph) (hk : 1 ≤ k)
      (S : CompLSFFamily k) (mem : ℕ → ℕ) (U : List Update),
      (∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ (S ⟨0, hk⟩)) →
      BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords →
      (S ⟨0, hk⟩).G.BatchIsValid U →
      (compLSFDSFullWithSplits (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L fmt.precision) w k G₀).cost
        0 S [b, batchPtr, heap] mem ≤
        (200000 * (mem (b + compOffLW) + 1) + 3000) * k * (totalWords + 1)) :
    AsmCompFamilyAt (compAsmSpec Q_AN c_AN K_AN)
      (canonicalLSFInit Q_AN c_AN K_AN L fmt.precision) w fmt L capExp limbMul
      ⟨(compAsmCode Q_AN c_AN K_AN hQ).procs⟩
      (compAsmCode Q_AN c_AN K_AN hQ).fInit
      (compAsmCode Q_AN c_AN K_AN hQ).fBatch where
  rep := compAsmRep Q_AN c_AN K_AN hQ L fmt.precision
  rep_local := compAsmRep_local Q_AN c_AN K_AN hQ L fmt.precision
  vCapOf x := x.vCap
  eCapOf x := x.eCap
  fRoot := (compAsmCode Q_AN c_AN K_AN hQ).fRoot
  fExport := (compAsmCode Q_AN c_AN K_AN hQ).fExport
  init_runs := compAsmInit_runs hQ hRho
  batch_runs := compAsmBatch_runs hQ hRho hBatchCost
  root_runs := compAsmRoot_runs hQ
  export_runs := compAsmExport_runs hQ hRho

/-- Complete `ScCompFamilyHyp` instance for `compAsmCode` (`wordExp 3 = 7 ≤ 39`). -/
theorem compAsmFamilyHyp {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    (hBatchCost : ∀ (w L P_fp k b batchPtr heap totalWords : ℕ) (G₀ : MGraph) (hk : 1 ≤ k)
      (S : CompLSFFamily k) (mem : ℕ → ℕ) (U : List Update),
      (∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ (S ⟨0, hk⟩)) →
      BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords →
      (S ⟨0, hk⟩).G.BatchIsValid U →
      (compLSFDSFullWithSplits (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L P_fp) w k G₀).cost
        0 S [b, batchPtr, heap] mem ≤
        (200000 * (mem (b + compOffLW) + 1) + 3000) * k * (totalWords + 1)) :
    ScCompFamilyHyp (compAsmSpec Q_AN c_AN K_AN) (canonicalLSFInit Q_AN c_AN K_AN)
      ⟨(compAsmCode Q_AN c_AN K_AN hQ).procs⟩
      (compAsmCode Q_AN c_AN K_AN hQ).fInit
      (compAsmCode Q_AN c_AN K_AN hQ).fBatch
      (compAsmCode Q_AN c_AN K_AN hQ).fExport
      (compAsmCode Q_AN c_AN K_AN hQ).fRoot where
  wordExp_le_39 := compAsmSpec_wordExp_le_39 Q_AN c_AN K_AN
  inst capExp limbMul w fmt L :=
    ⟨compAsmFamilyAt hQ hRho w fmt L capExp limbMul (hBatchCost w L fmt.precision), rfl, rfl⟩

end MinCostFlow.SparseCore.Program
