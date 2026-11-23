module

public import MinCostFlow.SparseCore.Program.CompAsmWrapCost
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# Verification of Wrapper `root`, `export`, and `batch` Operations (`CompAsmWrapOps`)

Verifies the three post-initialization wrapper procedures of `compAsmProcs` (`CompAsmWrapDefs.lean`)
against the exact contracts of `AsmCompFamilyAt` (`AssemblyTopIface.lean`):
* `compAsmRoot_runs`: `compAsmRootProc` (index `3`) forwards `[bComp, j, u, h]` to `compRootProc`
  at total cost `≤ 200`, preserving `compAsmRepPred` and `vCap`/`eCap`.
* `compAsmExport_runs`: `compAsmExportProc` (index `2`) forwards `[bComp, j, gCopy, h]` to
  `compExportBranchProc`, converting `CompExportPost` into `CompBranchExportAt` at cost
  `≤ compAsmMul * (((cfs j).G.n + (cfs j).G.m + 1) * bundleLogFactor M N)`.
* `compAsmBatch_runs`: `compAsmBatchProc` (index `1`) copies the batch above `h`, advances `gCopy`
  in-place via `dgApplyBatchStmt`, invokes `compBatchWithSplitsProc`, writes `ptrBase` at `h`,
  and establishes `CompFamilyChgAt`, `CompSplitListAt`, `Respects`, and the polylogarithmic batch
  cost bound.
-/

@[expose] public noncomputable section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## 1. Pure graph-size helpers and word-size lower bound -/

lemma compAsm_hw128 {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {M N L capExp w : ℕ}
    (hw : (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp * (L + 1) < 2 ^ w) :
    128 < 2 ^ w := by
  have h7 : 7 ≤ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp := le_max_left _ _
  have h1 : 128 ≤ (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp := by
    calc 128 = 2 ^ 7 := by decide
      _ ≤ 2 ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp := Nat.pow_le_pow_right (by decide) h7
      _ ≤ (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp :=
          Nat.pow_le_pow_left (by omega) _
  have h2 : (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp ≤
      (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp * (L + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  omega

lemma compLSFInv_G0_n_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.G₀.n ≤ cs.G.n := by
  classical
  refine Finset.card_le_card fun v hv => ?_
  rw [← components_biUnion_V cs.G₀, Finset.mem_biUnion] at hv
  obtain ⟨C, hC, hvC⟩ := hv
  have hCI := (hI.hCompLSF C hC).1
  have hvCG : v ∈ (cs.compSt C).G.V :=
    hCI.hGV_eq ▸ Finset.mem_union_left _ (hCI.hTV ▸ (hI.hCompLSF C hC).2.1.symm ▸ hvC)
  rw [← hI.hV_eq]
  exact Finset.mem_biUnion.mpr ⟨C, hC, hvCG⟩

lemma compLSFInv_T_m_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (_hI : CompLSFInv C_lsst ℓ₀ cs) : cs.T.m ≤ cs.G.m := by
  classical
  refine Finset.card_le_card fun e he => ?_
  simp only [CompLSFState.T, Finset.mem_inter, Finset.mem_sdiff] at he
  exact he.2.1

lemma compLSFInv_F_m_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.RF.F.m ≤ cs.G.m :=
  Finset.card_le_card (compLSF_RF_isRSF hI).2.2.2.2.2.1

lemma batchWithinCaps_mono {vCap eCap1 eCap2 : ℕ} {U : List Update}
    (he : eCap1 ≤ eCap2) (h : BatchWithinCaps vCap eCap1 U) :
    BatchWithinCaps vCap eCap2 U := by
  intro u hu
  have h1 := h u hu
  cases u with
  | insert e a b => exact lt_of_lt_of_le h1 he
  | delete e => trivial
  | split v v' St Sh => exact h1

lemma compLSFRep_b_lt_end {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {mem : ℕ → ℕ} (hrep : CompLSFRepAt W k b S x mem) :
    b < x.endAddr := by
  have hTE := hrep.2.2.2.2.2.2.2.2.2.1
  dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hTE
  omega

lemma dynGraphAt_n_le_vCap {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hdg : DynGraphAt mem a vCap eCap G) : G.n ≤ vCap := by
  have hVlt : ∀ v ∈ G.V, v < vCap := hdg.2.1
  have hsub : G.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (hVlt v hv)
  change G.V.card ≤ vCap
  simpa using Finset.card_le_card hsub

lemma compLSFBatch_fields (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).G₀ = cs.G₀ ∧
    (compLSFBatch cs U).k = cs.k ∧
    (compLSFBatch cs U).G = cs.G.applyBatch U := by
  induction U generalizing cs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u us ih =>
    change (compLSFBatch (compLSFStepSingle cs u) us).G₀ = cs.G₀ ∧
      (compLSFBatch (compLSFStepSingle cs u) us).k = cs.k ∧
      (compLSFBatch (compLSFStepSingle cs u) us).G = (cs.G.applyUpdate u).applyBatch us
    exact ih (compLSFStepSingle cs u)

/-! ## 2. Self-contained verification of `compCopyWordsProc` -/

lemma compAsmCopyWords_runs {w src dst len : ℕ} {p : Program} {mem : ℕ → ℕ}
    {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hdisj : src + len ≤ dst) (hdst_w : dst + len < 2 ^ w) :
    ∃ st' c,
      Runs w p ω compCopyWordsProc (startState [src, dst, len] mem pos) (.returned 0) st' c ∧
      (∀ i < len, st'.mem (dst + i) = mem (src + i)) ∧
      (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = mem a) ∧
      c ≤ 20 * len + 15 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  set st0 := startState [src, dst, len] mem pos
  let s1 : State := { st0 with regs := Function.update st0.regs 3 0 }
  have hp1 : Runs w p ω (.assign 3 (.const 0)) st0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  let loopStmt : Stmt :=
    .loop (.bin .lt (.reg 3) (.reg 2))
      (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))) ;;
       .assign 3 (.bin .add (.reg 3) (.const 1)))
  have hloop : ∀ rem i (s : State) (hi : i ≤ len), len - i = rem →
      s.regs 0 = src → s.regs 1 = dst → s.regs 2 = len → s.regs 3 = i →
      (∀ q < i, s.mem (dst + q) = mem (src + q)) →
      (∀ a, a < dst ∨ dst + i ≤ a → s.mem a = mem a) →
      ∃ st' c, Runs w p ω loopStmt s .normal st' c ∧
        (∀ q < len, st'.mem (dst + q) = mem (src + q)) ∧
        (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = mem a) ∧
        c ≤ 20 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr0 hr1 hr2 hr3 hdone hfr
      have hi_eq : i = len := by omega
      subst hi_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr3, hr2],
        rfl, rfl, by simp [Expr.size]⟩), hdone, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr0 hr1 hr2 hr3 hdone hfr
      have hi_lt : i < len := by omega
      have hs_v : s.mem (src + i) = mem (src + i) := hfr _ (Or.inl (by omega))
      let m1 := Function.update s.mem (dst + i) (mem (src + i))
      let a1 : State := { s with mem := m1 }
      let a2 : State := { a1 with regs := Function.update a1.regs 3 (i + 1) }
      have ha1 : Runs w p ω (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
          s .normal a1 8 :=
        runs_store_iff.mpr ⟨dst + i, mem (src + i),
          by simp [Expr.eval, BinOp.eval, hr1, hr3, show dst + i < 2 ^ w by omega],
          Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hr3, show src + i < 2 ^ w by omega]) hs_v,
          rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w p ω (.assign 3 (.bin .add (.reg 3) (.const 1))) a1 .normal a2 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [a1, Expr.eval, BinOp.eval, hr3, hw1, show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal a2 13 :=
        runs_seq_iff.mpr (Or.inr ⟨a1, 8, 4, ha1, ha2, rfl⟩)
      obtain ⟨st', cRest, hrest, hdone', hfr', hcRest⟩ :=
        ih (i + 1) a2 (by omega) (by omega)
          (by simp [a2, a1, hr0]) (by simp [a2, a1, hr1]) (by simp [a2, a1, hr2]) (by simp [a2])
          (fun q hq => by
            dsimp only [a2, a1, m1]
            by_cases hqi : q = i
            · subst hqi; simp
            · rw [Function.update_of_ne (by omega)]; exact hdone q (by omega))
          (fun a ha => by
            dsimp only [a2, a1, m1]; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega))
      have hfull : Runs w p ω loopStmt s .normal st' (13 + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, a2, 13, cRest,
          by simp [Expr.eval, BinOp.eval, hr3, hr2, hi_lt, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 13 + cRest + 4, hfull, hdone', hfr', by omega⟩
  obtain ⟨s2, cL, hL, hdone, hfr, hcL⟩ :=
    hloop len 0 s1 (Nat.zero_le _) (Nat.sub_zero _)
      (by simp [s1, st0, startState]) (by simp [s1, st0, startState])
      (by simp [s1, st0, startState]) (by simp [s1])
      (fun _ h => by omega) (fun _ _ => rfl)
  have hret : Runs w p ω (.ret (.const 0)) s2 (.returned 0) s2 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hfull : Runs w p ω compCopyWordsProc st0 (.returned 0) s2 (6 + cL) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, cL + 3, hp1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cL, 2, hL, hret, by omega⟩), by omega⟩)
  exact ⟨s2, 6 + cL, hfull, hdone, hfr, by omega⟩

/-! ## 3. Verification of `compAsmRootProc` (index `3`) -/

/-- Wrapper root query (`compAsmRootProc`, index `3`) meets `AsmCompFamilyAt.root_runs`. -/
theorem compAsmRoot_runs {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN) {w L P_fp capExp : ℕ}
    (cfH j u h k : ℕ) (cfs : CompFamilyAbs) (x : CompAsmMeta)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (_hcfH : cfH < 2 ^ w) (hj_w : j < 2 ^ w) (hu_w : u < 2 ^ w) (hh_w : h < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hj : j < k) (hk_eq : k = (cfs 0).k) (huV : u ∈ (cfs j).G.V)
    (hrep : compAsmRepPred Q_AN c_AN K_AN hQ L P_fp cfH cfs x mem)
    (hfoot : ∀ a, compAsmFoot cfH x a → a < h)
    (hz : ZeroFrom mem h) (hh1 : h + 1 < 2 ^ w) :
    let p : Program := ⟨compAsmProcs Q_AN c_AN K_AN hQ⟩
    ∃ body, p.procs[3]? = some body ∧ ∃ o st' c x',
      Runs w p ω body (startState [cfH, j, u, h] mem pos) o st' c ∧
      st'.mem h = (cfs j).RF.root u ∧
      compAsmRepPred Q_AN c_AN K_AN hQ L P_fp cfH cfs x' st'.mem ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧
      h ≤ o.value ∧ o.value ≤ h + 1 ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ compAsmFoot cfH x a → st'.mem a = mem a) ∧
      (∀ a, compAsmFoot cfH x' a → compAsmFoot cfH x a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + compPhiFull x'.k x'.bComp x'.xComp st'.mem ≤
        (compAsmSpec Q_AN c_AN K_AN).rootCost capExp + compPhiFull x.k x.bComp x.xComp mem := by
  intro p
  obtain ⟨hm0, hm1, hcf2, hgb, hk1, hk_x, hxV, hxE, hxLw, hdg, hcomp⟩ := hrep
  have hk_same : x.k = k := by omega
  subst hk_same
  set W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L P_fp
  set S : CompLSFFamily x.k := fun i => cfs i.1
  have hb_lt_h : x.bComp < h :=
    hfoot x.bComp (Or.inr (Or.inr ⟨le_rfl, compLSFRep_b_lt_end hcomp⟩))
  have hb_w : x.bComp < 2 ^ w := lt_trans hb_lt_h hh_w
  have huV0 : u ∈ (S ⟨0, hk1⟩).G.V := by
    obtain ⟨ℓ₀, hBr⟩ := hcomp.2.2.2.2.2.2.2.2.2.2.2.1
    rw [← (hBr ⟨j, hj⟩).2.2.1]; exact huV
  have hpre3 : (compLSFDS W w x.k (S ⟨0, hk1⟩).G₀).pre 3 S [x.bComp, j, u, h] mem :=
    ⟨hk1, x.bComp, j, u, h, rfl, hw16, hj, huV0⟩
  have hargs3 : ∀ a ∈ [x.bComp, j, u, h], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hfoot3 : ∀ a, compFoot x.bComp x.xComp a → a < h := fun a ha =>
    hfoot a (Or.inr (Or.inr ha))
  obtain ⟨body3, hbody3, o3, st3, c3, hr3, hcomp3, hpost3, hresp3, hcost3⟩ :=
    compLSFProcs_root_runs (W := W) (G₀ := (S ⟨0, hk1⟩).G₀) (pos := pos) (ω := ω)
      (compAsmProg_hasComp Q_AN c_AN K_AN hQ L P_fp) hcomp hpre3 hargs3 rfl hfoot3 hz hh1
  set st0 := startState [cfH, j, u, h] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 4 x.bComp }
  have hp1 : Runs w p ω (.assign 4 (.load (.reg 0))) st0 .normal st1 3 :=
    runs_assign_iff.mpr ⟨x.bComp,
      Expr.eval_load_of_eq (by simp [st0, startState, Expr.eval]) hm0,
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st3 with regs := Function.update st1.regs 5 o3.value }
  have hp2 : Runs w p ω (.call 5 compAsmIdxCompRoot [.reg 4, .reg 1, .reg 2, .reg 3])
      st1 .normal st2 (4 + c3 + 1) := by
    rw [runs_call_iff]
    refine ⟨[x.bComp, j, u, h], body3, o3, st3, c3, ?_, hbody3, hr3, rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, st1, st0, startState]
  have hp3 : Runs w p ω (.ret (.reg 5)) st2 (.returned o3.value) st2 2 :=
    runs_ret_iff.mpr ⟨o3.value, by simp [st2, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hrun : Runs w p ω (compAsmRootProc compAsmIdxCompRoot) st0 (.returned o3.value) st2
      (3 + (4 + c3 + 1 + 2 + 1) + 1) := by
    unfold compAsmRootProc
    have t1 := runs_seq_iff.mpr (Or.inr ⟨st2, 4 + c3 + 1, 2, hp2, hp3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 3, 4 + c3 + 1 + 2 + 1, hp1, t1, rfl⟩)
  rcases hresp3 with ⟨hlo3, hhi3, hz3, hfr3, hft3⟩
  have hbelow_b : ∀ a < x.bComp, st3.mem a = mem a := fun a ha =>
    hfr3 a (lt_trans ha hb_lt_h) (fun hf => absurd ha (not_lt.mpr hf.1))
  have hm0' : st3.mem cfH = x.bComp := (hbelow_b cfH (by omega)).trans hm0
  have hm1' : st3.mem (cfH + 1) = x.gCopy := (hbelow_b (cfH + 1) (by omega)).trans hm1
  have hdg' : DynGraphAt st3.mem x.gCopy x.vCap x.eCap (cfs 0).G :=
    dynGraphAt_of_agree hdg fun a ha1 ha2 => hbelow_b a (by omega)
  have hrep' : compAsmRepPred Q_AN c_AN K_AN hQ L P_fp cfH cfs x st3.mem :=
    ⟨hm0', hm1', hcf2, hgb, hk1, hk_x, hxV, hxE, hxLw, hdg', hcomp3⟩
  refine ⟨compAsmRootProc compAsmIdxCompRoot, compAsmProg_get3 Q_AN c_AN K_AN hQ,
    .returned o3.value, st2, 3 + (4 + c3 + 1 + 2 + 1) + 1, x, hrun, ?_, hrep', rfl, rfl,
    hlo3, hhi3, hz3, ?_, fun a ha => Or.inl ha, ?_⟩
  · simpa [heapArg, S, st2] using hpost3.2.2
  · intro a ha hnf
    exact hfr3 a ha (fun hf => hnf (Or.inr (Or.inr hf)))
  · change _ + compPhiFull x.k x.bComp x.xComp st3.mem ≤ 200 + compPhiFull x.k x.bComp x.xComp mem
    change c3 + compPhiFull x.k x.bComp x.xComp st3.mem ≤ 150 + compPhiFull x.k x.bComp x.xComp mem at hcost3
    omega

/-! ## 4. Verification of `compAsmExportProc` (index `2`) -/

/-- Wrapper single-branch export (`compAsmExportProc`, index `2`) meets `AsmCompFamilyAt.export_runs`. -/
theorem compAsmExport_runs {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {w L capExp limbMul : ℕ} {fmt : Num.Format w}
    (cfH j k M N vCap eCap h : ℕ) (cfs : CompFamilyAbs) (x : CompAsmMeta)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (_hfmt : fmt.limbBits = 4) (_hk : 0 < k) (hj : j < k) (hk_eq : k = (cfs 0).k)
    (hkCap : k ≤ (M + N + 2) ^ capExp) (_hGm : (cfs j).G.m ≤ M) (hGn : (cfs j).G.n ≤ N)
    (hCap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hw : (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp * (L + 1) < 2 ^ w)
    (hrep : compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs x mem)
    (hvCap : x.vCap = vCap) (heCap : x.eCap = eCap)
    (hfoot : ∀ a, compAsmFoot cfH x a → a < h)
    (hargs : ∀ a ∈ [cfH, j, h], a < 2 ^ w)
    (hz : ZeroFrom mem h)
    (hsp : h + ((compAsmSpec Q_AN c_AN K_AN).exportSpace capExp).eval (M + N + k + vCap + eCap + L) < 2 ^ w) :
    let p : Program := ⟨compAsmProcs Q_AN c_AN K_AN hQ⟩
    ∃ body, p.procs[2]? = some body ∧ ∃ o st' c x',
      Runs w p ω body (startState [cfH, j, h] mem pos) o st' c ∧
      compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs x' st'.mem ∧
      x'.vCap = vCap ∧ x'.eCap = eCap ∧
      CompBranchExportAt w st'.mem h o.value L capExp M N vCap eCap (cfs j) ∧
      (compAsmRep Q_AN c_AN K_AN hQ L fmt.precision).Respects (compAsmFoot cfH x) h
        (((compAsmSpec Q_AN c_AN K_AN).exportSpace capExp).eval (M + N + k + vCap + eCap + L))
        mem o.value cfH x' st'.mem ∧
      c + compPhiFull x'.k x'.bComp x'.xComp st'.mem ≤
        (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
          (((cfs j).G.n + (cfs j).G.m + 1) * bundleLogFactor M N) +
          compPhiFull x.k x.bComp x.xComp mem := by
  intro p
  obtain ⟨hm0, hm1, hcf2, hgb, hk1, hk_x, hxV, hxE, hxLw, hdg, hcomp⟩ := hrep
  have hk_same : x.k = k := by omega
  subst hk_same; subst hvCap; subst heCap
  set W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L fmt.precision
  set S : CompLSFFamily x.k := fun i => cfs i.1
  have hw128 : 128 < 2 ^ w := compAsm_hw128 hw
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hcfH_w : cfH < 2 ^ w := hargs cfH (by simp)
  have hj_w : j < 2 ^ w := hargs j (by simp)
  have hh_w : h < 2 ^ w := hargs h (by simp)
  have hb_lt_h : x.bComp < h :=
    hfoot x.bComp (Or.inr (Or.inr ⟨le_rfl, compLSFRep_b_lt_end hcomp⟩))
  have hg_lt_h : x.gCopy < h := by
    have : 4 ≤ dynGraphSize x.vCap x.eCap := by unfold dynGraphSize; omega
    omega
  have hb_w : x.bComp < 2 ^ w := lt_trans hb_lt_h hh_w
  have hg_w : x.gCopy < 2 ^ w := lt_trans hg_lt_h hh_w
  have hcfH1_w : cfH + 1 < 2 ^ w := by omega
  obtain ⟨ℓ₀, hBr⟩ := hcomp.2.2.2.2.2.2.2.2.2.2.2.1
  have hInv0 : CompLSFInv W.C_lsst ℓ₀ (cfs 0) := (hBr ⟨0, hk1⟩).1
  have hInvJ : CompLSFInv W.C_lsst ℓ₀ (cfs j) := (hBr ⟨j, hj⟩).1
  have hGj_eq0 : (cfs j).G = (cfs 0).G := (hBr ⟨j, hj⟩).2.2.1
  have hG0n_le_N : (cfs 0).G₀.n ≤ N := by
    have h1 := compLSFInv_G0_n_le hInv0
    rw [← hGj_eq0] at h1; exact h1.trans hGn
  have hG0n_le_vCap : (cfs 0).G₀.n ≤ x.vCap :=
    (compLSFInv_G0_n_le hInv0).trans (dynGraphAt_n_le_vCap hdg)
  have hLw_le_canon : x.xComp.L_w ≤ canonLw K_AN L (cfs 0).G₀.n x.k := by
    rw [hxLw]; split_ifs
    · unfold canonLw; omega
    · exact le_rfl
  have hLw_ge1 : 1 ≤ x.xComp.L_w := by rw [hxLw]; split_ifs <;> [omega; (unfold canonLw; omega)]
  have hhdr := hcomp.2.2.2.2.2.2.2.2.2.2.1
  have hsp_ex_le : compExportSpace [x.bComp, j, x.gCopy, h] mem ≤
      ((compAsmSpec Q_AN c_AN K_AN).exportSpace capExp).eval (M + N + x.k + x.vCap + x.eCap + L) := by
    simp only [compExportSpace, List.getD_cons_zero, hhdr.1, hhdr.2.1, hhdr.2.2.2.1, hxV, hxE]
    have h1 : 16 + 2 * x.vCap + 6 * max x.eCap 1 + 2 * max x.eCap 1 * x.xComp.L_w ≤
        16 + 2 * x.vCap + 6 * max x.eCap 1 + 2 * max x.eCap 1 * canonLw K_AN L (cfs 0).G₀.n x.k :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hLw_le_canon) _
    exact h1.trans (compAsmExportSpace_le hRho hG0n_le_vCap)
  have hpre6 : CompExportPre w x.k S [x.bComp, j, x.gCopy, h] mem :=
    ⟨hk1, x.bComp, j, x.gCopy, h, x.vCap, x.eCap, rfl, hw16, hj, hdg, by omega⟩
  have hargs6 : ∀ a ∈ [x.bComp, j, x.gCopy, h], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hfoot6 : ∀ a, compFoot x.bComp x.xComp a → a < h := fun a ha =>
    hfoot a (Or.inr (Or.inr ha))
  obtain ⟨body6, hbody6, o6, st6, c6, hr6, hcomp6, hpost6, hresp6, hcost6, hout6⟩ :=
    compLSFProcs_export_runs (W := W) (G₀ := (S ⟨0, hk1⟩).G₀) (pos := pos) (ω := ω)
      (compAsmProg_hasComp Q_AN c_AN K_AN hQ L fmt.precision) hcomp hpre6 hargs6 rfl hfoot6 hz
      (lt_of_le_of_lt (Nat.add_le_add_left hsp_ex_le h) hsp)
  set st0 := startState [cfH, j, h] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 3 x.bComp }
  have hp1 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal st1 3 :=
    runs_assign_iff.mpr ⟨x.bComp,
      Expr.eval_load_of_eq (by simp [st0, startState, Expr.eval]) hm0,
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs 4 x.gCopy }
  have hp2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 1)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨x.gCopy,
      Expr.eval_load_of_eq (by simp [st1, st0, startState, Expr.eval, hcfH1_w, show 1 < 2 ^ w by omega]) hm1,
      rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st6 with regs := Function.update st2.regs 5 o6.value }
  have hp3 : Runs w p ω (.call 5 compAsmIdxCompExport [.reg 3, .reg 1, .reg 4, .reg 2])
      st2 .normal st3 (4 + c6 + 1) := by
    rw [runs_call_iff]
    refine ⟨[x.bComp, j, x.gCopy, h], body6, o6, st6, c6, ?_, hbody6, hr6, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, st2, st1, st0, startState]
  have hp4 : Runs w p ω (.ret (.reg 5)) st3 (.returned o6.value) st3 2 :=
    runs_ret_iff.mpr ⟨o6.value, by simp [st3, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hrun : Runs w p ω (compAsmExportProc compAsmIdxCompExport) st0 (.returned o6.value) st3
      (3 + (5 + (4 + c6 + 1 + 2 + 1) + 1) + 1) := by
    unfold compAsmExportProc
    have t1 := runs_seq_iff.mpr (Or.inr ⟨st3, 4 + c6 + 1, 2, hp3, hp4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st2, 5, 4 + c6 + 1 + 2 + 1, hp2, t1, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 3, 5 + (4 + c6 + 1 + 2 + 1) + 1, hp1, t2, rfl⟩)
  rcases hresp6 with ⟨hlo6, hhi6, hz6, hfr6, hft6⟩
  have hbelow_b : ∀ a < x.bComp, st6.mem a = mem a := fun a ha =>
    hfr6 a (lt_trans ha hb_lt_h) (fun hf => absurd ha (not_lt.mpr hf.1))
  have hm0' : st6.mem cfH = x.bComp := (hbelow_b cfH (by omega)).trans hm0
  have hm1' : st6.mem (cfH + 1) = x.gCopy := (hbelow_b (cfH + 1) (by omega)).trans hm1
  have hdg' : DynGraphAt st6.mem x.gCopy x.vCap x.eCap (cfs 0).G :=
    dynGraphAt_of_agree hdg fun a ha1 ha2 => hbelow_b a (by omega)
  have hrep' : compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs x st6.mem :=
    ⟨hm0', hm1', hcf2, hgb, hk1, hk_x, hxV, hxE, hxLw, hdg', hcomp6⟩
  rcases hpost6 with ⟨_, hj', htD, hfD, hLw_m, heCap_m, h16_out, hout_sp, hwords_lt, hz_out,
    hT_exp, hF_exp, ⟨roots, hrLen, hrNd, hrFs, hrLA, hr16, hrHi⟩, hTE_lt, hPairs⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, heapArg, List.getLastD_cons,
    List.getLastD_nil] at htD hfD hLw_m heCap_m h16_out hout_sp hwords_lt hz_out hT_exp hF_exp hrLen hrLA hr16 hrHi hTE_lt hPairs hout6
  rw [← hout6] at h16_out hout_sp hwords_lt hz_out hT_exp hF_exp hrHi hPairs
  have hmax_w : max (2 ^ w) (2 ^ W.h) = 2 ^ w := max_eq_left (by change 2 ^ 4 ≤ 2 ^ w; omega)
  have hLw_ro : x.xComp.L_w ≤
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) :=
    hLw_le_canon.trans (canonLw_le_readout2_of_rho hRho hG0n_le_N hkCap)
  have htCap_le : max x.eCap 1 ≤ 2 * (x.vCap + x.eCap + 2) ^ 2 := by
    have : x.eCap + 1 ≤ (x.vCap + x.eCap + 2) ^ 2 :=
      le_trans (by omega) (Nat.le_self_pow (by decide) (x.vCap + x.eCap + 2))
    omega
  have hExp : CompBranchExportAt w st6.mem h o6.value L capExp M N x.vCap x.eCap (cfs j) := by
    dsimp only [CompBranchExportAt]
    refine ⟨by omega, fun a ha1 ha2 => by simpa [hmax_w] using hwords_lt a ha1 ha2,
      by omega, hT_exp, by omega, hF_exp,
      ⟨roots, hrLen, hrNd, hrFs, hrLA, by omega, hrHi⟩,
      by rw [hLw_m, hhdr.2.2.2.1]; exact hLw_ge1,
      by rw [hLw_m, hhdr.2.2.2.1]; exact hLw_ro,
      by rw [heCap_m, hhdr.2.1, hxE]; exact le_max_left _ _,
      by rw [heCap_m, hhdr.2.1, hxE]; exact htCap_le,
      by rw [heCap_m]; exact hTE_lt,
      fun e => intVal st6.mem (st6.mem (h + 4) + e * st6.mem (h + 6)) 4 (st6.mem (h + 6)),
      fun e => intVal st6.mem (st6.mem (h + 5) + e * st6.mem (h + 6)) 4 (st6.mem (h + 6)),
      fun e he => ?_⟩
    obtain ⟨hnLo, hnHi, hdLo, hdHi, hVN, hVD, hN1, hD1, hrat⟩ := hPairs e he
    have hWh4 : W.h = 4 := rfl
    rw [hLw_m]
    rw [hWh4] at hD1
    exact ⟨by omega, hnHi, by omega, hdHi, hVN, hVD, rfl, rfl, by dsimp only; omega, hrat⟩
  have hcost_ex : compExportCost x.k S [x.bComp, j, x.gCopy, h] mem + 18 ≤
      (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
        (((cfs j).G.n + (cfs j).G.m + 1) * bundleLogFactor M N) := by
    simp only [compExportCost, List.getD_cons_zero, List.getD_cons_succ, hj, ↓reduceDIte,
      hhdr.2.2.2.1, S]
    have h1 : 450 * (cfs j).G.n + 180 * (cfs j).T.m + 100 * (cfs j).RF.F.m +
        40 * (cfs j).G.m * x.xComp.L_w + 100 * (cfs j).G.m + 500 + 18 ≤
        450 * (cfs j).G.n + 180 * (cfs j).T.m + 100 * (cfs j).RF.F.m +
        40 * (cfs j).G.m * canonLw K_AN L (cfs 0).G₀.n x.k + 100 * (cfs j).G.m + 500 + 100 := by
      have := Nat.mul_le_mul_left (40 * (cfs j).G.m) hLw_le_canon
      omega
    exact h1.trans (compAsmExportCost_le hRho hG0n_le_N hkCap hCap.2
      (compLSFInv_T_m_le hInvJ) (compLSFInv_F_m_le hInvJ))
  refine ⟨compAsmExportProc compAsmIdxCompExport, compAsmProg_get2 Q_AN c_AN K_AN hQ,
    .returned o6.value, st3, 3 + (5 + (4 + c6 + 1 + 2 + 1) + 1) + 1, x, hrun, hrep', rfl, rfl, hExp,
    ⟨hlo6, le_trans hhi6 (Nat.add_le_add_left hsp_ex_le h), hz6,
      fun a ha hnf => hfr6 a ha fun hf => hnf (Or.inr (Or.inr hf)),
      fun a ha => Or.inl ha⟩, ?_⟩
  dsimp only [st3]
  omega

/-! ## 5. Verification of `compAsmBatchProc` (index `1`) -/

/-- Wrapper batch update (`compAsmBatchProc`, index `1`) meets `AsmCompFamilyAt.batch_runs`,
parameterized by P4's polylogarithmic `op 0` batch-cost bound `hBatchCost`. -/
theorem compAsmBatch_runs {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {w L capExp limbMul : ℕ} {fmt : Num.Format w}
    (hBatchCost : ∀ (k b batchPtr heap totalWords : ℕ) (G₀ : MGraph) (hk : 1 ≤ k)
      (S : CompLSFFamily k) (mem : ℕ → ℕ) (U : List Update),
      (∃ C_lsst ℓ₀, CompLSFInv C_lsst ℓ₀ (S ⟨0, hk⟩)) →
      BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords →
      (S ⟨0, hk⟩).G.BatchIsValid U →
      (compLSFDSFullWithSplits (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L fmt.precision) w k G₀).cost
        0 S [b, batchPtr, heap] mem ≤
        (200000 * (mem (b + compOffLW) + 1) + 3000) * k * (totalWords + 1))
    (cfH batch words k M N vCap eCap h : ℕ) (cfs : CompFamilyAbs) (x : CompAsmMeta)
    (U : List Update) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (_hfmt : fmt.limbBits = 4) (_hk : 0 < k) (hk_eq : k = (cfs 0).k)
    (hkCap : k ≤ (M + N + 2) ^ capExp) (hG0n : (cfs 0).G₀.n ≤ N)
    (hCap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hw : (M + N + 2) ^ (compAsmSpec Q_AN c_AN K_AN).wordExp capExp * (L + 1) < 2 ^ w)
    (hrep : compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs x mem)
    (hvCap : x.vCap = vCap) (heCap : x.eCap = eCap)
    (_hGsame : ∀ j < k, (cfs j).G = (cfs 0).G)
    (hBAt : SmallBatchAt mem batch (cfs 0).G U words)
    (hBVal : (cfs 0).G.BatchIsValid U) (hBCaps : BatchWithinCaps vCap eCap U)
    (hBWords : ∀ i < words, mem (batch + i) < 2 ^ w) (hBHeap : batch + words ≤ h)
    (hargs : ∀ a ∈ [cfH, batch, words, h], a < 2 ^ w)
    (hfoot : ∀ a, compAsmFoot cfH x a → a < h)
    (hz : ZeroFrom mem h)
    (hsp : h + ((compAsmSpec Q_AN c_AN K_AN).batchSpace capExp).eval (vCap + eCap + L + k + words) < 2 ^ w) :
    let p : Program := ⟨compAsmProcs Q_AN c_AN K_AN hQ⟩
    let cfs' : CompFamilyAbs := fun j => compLSFBatch (cfs j) U
    ∃ body, p.procs[1]? = some body ∧ ∃ o st' c x',
      Runs w p ω body (startState [cfH, batch, words, h] mem pos) o st' c ∧
      compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs' x' st'.mem ∧
      x'.vCap = vCap ∧ x'.eCap = eCap ∧
      h + 1 ≤ o.value ∧
      h ≤ st'.mem h ∧ st'.mem h ≤ o.value ∧
      CompFamilyChgAt w k st'.mem (st'.mem h) o.value cfs U ∧
      CompSplitListAt w k st'.mem (st'.mem h + k) o.value cfs U ∧
      (compAsmRep Q_AN c_AN K_AN hQ L fmt.precision).Respects (compAsmFoot cfH x) h
        (((compAsmSpec Q_AN c_AN K_AN).batchSpace capExp).eval (vCap + eCap + L + k + words))
        mem o.value cfH x' st'.mem ∧
      c + compPhiFull x'.k x'.bComp x'.xComp st'.mem ≤
        (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
          ((Finset.range k).sum (fun j => lsfBatchSize (cfs j) U) + (k + 1) * (words + 1)) *
          bundleLogFactor M N + compPhiFull x.k x.bComp x.xComp mem := by
  intro p cfs'
  obtain ⟨hm0, hm1, hcf2, hgb, hk1, hk_x, hxV, hxE, hxLw, hdg, hcomp⟩ := hrep
  have hk_same : x.k = k := by omega
  subst hk_same; subst hvCap; subst heCap
  set W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L fmt.precision
  set S : CompLSFFamily x.k := fun i => cfs i.1
  have hw128 : 128 < 2 ^ w := compAsm_hw128 hw
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hcfH_w : cfH < 2 ^ w := hargs cfH (by simp)
  have hbat_w : batch < 2 ^ w := hargs batch (by simp)
  have hwds_w : words < 2 ^ w := hargs words (by simp)
  have hh_w : h < 2 ^ w := hargs h (by simp)
  have hb_lt_h : x.bComp < h :=
    hfoot x.bComp (Or.inr (Or.inr ⟨le_rfl, compLSFRep_b_lt_end hcomp⟩))
  have hg_lt_h : x.gCopy < h := by
    have : 4 ≤ dynGraphSize x.vCap x.eCap := by unfold dynGraphSize; omega
    omega
  have hb_w : x.bComp < 2 ^ w := lt_trans hb_lt_h hh_w
  have hg_w : x.gCopy < 2 ^ w := lt_trans hg_lt_h hh_w
  have hcfH1_w : cfH + 1 < 2 ^ w := by omega
  have hU_le_w : U.length ≤ words := by
    have h1 := BatchBodyAt.two_mul_length_le hBAt.1.2.2
    have h2 := hBAt.1.1
    omega
  have hsp_le_poly :
      1 + words + (11 + 3 * U.length + words + 2 * max x.eCap 1 + 8 * x.vCap +
        x.k * (8 + 12 * x.vCap)) ≤
      ((compAsmSpec Q_AN c_AN K_AN).batchSpace capExp).eval (x.vCap + x.eCap + L + x.k + words) :=
    compAsmBatchSpace_le hU_le_w
  set bCopy := h + 1
  set h1 := bCopy + words
  have hbCopy_w : bCopy < 2 ^ w := by omega
  have hh1_w : h1 < 2 ^ w := by omega
  -- Step 1: 4 prefix assigns
  set st0 := startState [cfH, batch, words, h] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 4 x.bComp }
  have hp1 : Runs w p ω (.assign 4 (.load (.reg 0))) st0 .normal st1 3 :=
    runs_assign_iff.mpr ⟨x.bComp, Expr.eval_load_of_eq (by simp [st0, startState, Expr.eval]) hm0,
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs 5 x.gCopy }
  have hp2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 1)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨x.gCopy, Expr.eval_load_of_eq (by simp [st1, st0, startState, Expr.eval, hcfH1_w, hw1]) hm1,
      rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2 with regs := Function.update st2.regs 6 bCopy }
  have hp3 : Runs w p ω (.assign 6 (.bin .add (.reg 3) (.const 1))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨bCopy, by simp [st2, st1, st0, startState, Expr.eval, hw1, hbCopy_w, bCopy],
      rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs 7 h1 }
  have hp4 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 2))) st3 .normal st4 4 :=
    runs_assign_iff.mpr ⟨h1, by simp [st3, st2, st1, st0, startState, Expr.eval, hh1_w, h1],
      rfl, rfl, by simp [Expr.size]⟩
  -- Step 2: Copy batch from `[batch, batch + words)` to `[bCopy, h1)`
  obtain ⟨stCp, cCp, hrCp, hCp_done, hCp_fr, hcCp⟩ :=
    compAsmCopyWords_runs (w := w) (src := batch) (dst := bCopy) (len := words)
      (p := p) (mem := mem) (pos := pos) (ω := ω) hw16 (by omega) (by omega)
  let st5 : State := { stCp with regs := Function.update st4.regs 8 0 }
  have hp5 : Runs w p ω (.call 8 compAsmIdxCopy [.reg 1, .reg 6, .reg 2]) st4 .normal st5 (3 + cCp + 1) := by
    rw [runs_call_iff]
    refine ⟨[batch, bCopy, words], compCopyWordsProc, .returned 0, stCp, cCp, ?_,
      compAsmProg_getCopy Q_AN c_AN K_AN hQ, hrCp, rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, st4, st3, st2, st1, st0, startState]
  have hBAt_cp : SmallBatchAt stCp.mem bCopy (cfs 0).G U words :=
    smallBatchAt_shift hBAt hCp_done
  have hBWords_cp : ∀ i < words, stCp.mem (bCopy + i) < 2 ^ w := fun i hi => by
    rw [hCp_done i hi]; exact hBWords i hi
  have hdg_cp : DynGraphAt stCp.mem x.gCopy x.vCap x.eCap (cfs 0).G :=
    dynGraphAt_of_agree hdg fun a ha1 ha2 => hCp_fr a (Or.inl (by omega))
  -- Step 3: Update `gCopy` in-place via `dgApplyBatchStmt`
  have hDgHas := compAsmProg_hasDg Q_AN c_AN K_AN hQ
  have hDgBat := dgApplyBatch_meetsContract (w := w) (vCap := x.vCap) (eCap := x.eCap)
    (G := (cfs 0).G) (H := (cfs 0).G) (U := U) (totalWords := words)
    (dgReloc_hasAt_batch hDgHas) (dgReloc_hasAt_edge hDgHas)
    (dgReloc_hasAt_split hDgHas) (dgReloc_hasAt_ops hDgHas)
  have hDgPre : (dgApplyBatchContract w x.vCap x.eCap (cfs 0).G (cfs 0).G U words).pre
      [x.gCopy, bCopy, 1] stCp.mem :=
    ⟨x.gCopy, bCopy, 1, rfl, hw16, by omega, by omega,
      fun i hi => Or.inr (by omega), hBWords_cp, hBAt_cp.1, hBVal, hBCaps, hdg_cp, Or.inl ⟨by decide, rfl⟩⟩
  obtain ⟨st6, cDg, vDg, hp6, hDgPost, _, hr6_ne, hcDg⟩ :=
    runs_call_of_meetsContract (r := 8) hDgBat
      (show evalArgs w st5 [.reg 5, .reg 6, .const 1] = some [x.gCopy, bCopy, 1] by
        simp [evalArgs, Expr.eval, st5, st4, st3, st2, st1, st0, startState, hw1])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> assumption)
      hDgPre ω
  rcases hDgPost with ⟨_, _, _, hDg_eq, _, hdg_up, hDg_fr⟩
  simp only [List.cons.injEq, and_true] at hDg_eq
  rcases hDg_eq with ⟨rfl, rfl, rfl⟩
  have hdg_target : U.foldl (dgBatchTarget 1) (cfs 0).G = (cfs 0).G.applyBatch U := rfl
  rw [hdg_target] at hdg_up
  -- Step 4: Call `compBatchWithSplitsProc` at `[x.bComp, bCopy, h1]`
  have hmem6_ag_comp : ∀ a, compFoot x.bComp x.xComp a → st6.mem a = mem a := fun a ha => by
    have ha1 : x.bComp ≤ a := ha.1
    have hlt_h : a < h := hfoot a (Or.inr (Or.inr ha))
    exact (hDg_fr a (Or.inr (by omega))).trans (hCp_fr a (Or.inl (by omega)))
  have hcomp6 : CompLSFRepAt W x.k x.bComp S x.xComp st6.mem :=
    (compLSFRepFull_local W x.k x.bComp S x.xComp mem st6.mem
      (fun a ha => (hmem6_ag_comp a ha).symm)).1 hcomp
  have hphi6 : compPhiFull x.k x.bComp x.xComp st6.mem = compPhiFull x.k x.bComp x.xComp mem :=
    ((compLSFRepFull_local W x.k x.bComp S x.xComp mem st6.mem
      (fun a ha => (hmem6_ag_comp a ha).symm)).2).symm
  have hBAt6 : SmallBatchAt st6.mem bCopy (cfs 0).G U words :=
    smallBatchAt_shift hBAt_cp fun i hi => hDg_fr (bCopy + i) (Or.inr (by omega))
  have hBWords6 : ∀ i < words, st6.mem (bCopy + i) < 2 ^ w := fun i hi => by
    rw [hDg_fr (bCopy + i) (Or.inr (by omega))]; exact hBWords_cp i hi
  have hz6 : ZeroFrom st6.mem h1 := fun a ha =>
    (hDg_fr a (Or.inr (by omega))).trans ((hCp_fr a (Or.inr (by omega))).trans (hz a (by omega)))
  have hhdr6 := hcomp6.2.2.2.2.2.2.2.2.2.2.1
  have hfoot6 : ∀ a, compFoot x.bComp x.xComp a → a < h1 := fun a ha =>
    lt_of_lt_of_le (hfoot a (Or.inr (Or.inr ha))) (by omega)
  have hend_le_h : x.xComp.endAddr ≤ h := by
    have hb_lt := compLSFRep_b_lt_end hcomp6
    have := hfoot (x.xComp.endAddr - 1) (Or.inr (Or.inr ⟨by omega, by omega⟩))
    omega
  have hsp0_eq : (compLSFDSFullWithSplits W w x.k (S ⟨0, hk1⟩).G₀).space 0 S [x.bComp, bCopy, h1] st6.mem =
      11 + 3 * U.length + words + 2 * max x.eCap 1 + 8 * x.vCap + x.k * (8 + 12 * x.vCap) := by
    simp only [compLSFDSFullWithSplits, ↓reduceIte, compBatchSpaceFull, List.getD_cons_zero,
      List.getD_cons_succ, hhdr6.1, hhdr6.2.1, hxV, hxE, hBAt6.1.2.1, batchMemLen_eq hBAt6.1]
  have hsp0_lt : h1 + (compLSFDSFullWithSplits W w x.k (S ⟨0, hk1⟩).G₀).space 0 S [x.bComp, bCopy, h1] st6.mem < 2 ^ w := by
    rw [hsp0_eq]; omega
  have hargs0 : ∀ a ∈ [x.bComp, bCopy, h1], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  obtain ⟨body0, hbody0, o0, st0', c0, S0', xComp', hr0, hcomp0, _, hresp0, hcost0,
      hxV', hxE', hxLw', hpostAt⟩ :=
    compLSFProcs_batch_runs (W := W) (G₀ := (S ⟨0, hk1⟩).G₀) (pos := st6.pos) (ω := ω)
      (compAsmProg_hasComp Q_AN c_AN K_AN hQ L fmt.precision) hcomp6 hk1 hw16 hBAt6.1 hBVal
      (by rw [hhdr6.1, hhdr6.2.1, hxV, hxE]; exact batchWithinCaps_mono (le_max_left _ _) hBCaps)
      hBWords6 le_rfl (fun i hi => Or.inr (by rw [hhdr6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; omega))
      hargs0 hfoot6 hz6 hsp0_lt
  let st7 : State := { st0' with regs := Function.update st6.regs 8 o0.value }
  have hp7 : Runs w p ω (.call 8 compAsmIdxCompBatch [.reg 4, .reg 6, .reg 7]) st6 .normal st7 (3 + c0 + 1) := by
    rw [runs_call_iff]
    refine ⟨[x.bComp, bCopy, h1], body0, o0, st0', c0, ?_, hbody0, hr0, rfl, rfl, by simp [argsSize, Expr.size]⟩
    have hr4 : st6.regs 4 = x.bComp := by rw [hr6_ne 4 (by decide)]; simp [st5, st4, st3, st2, st1]
    have hr6 : st6.regs 6 = bCopy := by rw [hr6_ne 6 (by decide)]; simp [st5, st4, st3]
    have hr7 : st6.regs 7 = h1 := by rw [hr6_ne 7 (by decide)]; simp [st5, st4]
    simp [evalArgs, Expr.eval, hr4, hr6, hr7]
  -- Extract `CompBatchPostFullAt`
  rcases hpostAt with ⟨_, _, _, _, tw', hEq0, _, hS0'_eq, hr_le, hptr_out, hout_sp, hz0',
    ⟨chgFin, hChg⟩, hSpAt⟩
  simp only [List.cons.injEq, and_true] at hEq0
  rcases hEq0 with ⟨rfl, rfl, rfl⟩
  set ptrBase := h1 + 1 + st0'.mem h1
  have hout_w : o0.value < 2 ^ w := lt_of_le_of_lt hout_sp hsp0_lt
  have hptr_w : ptrBase < 2 ^ w := by omega
  have hr_w : st0'.mem h1 < 2 ^ w := by omega
  -- Step 5: Compute `ptrBase`, store at `h`, return `o0.value`
  let st8 : State := { st7 with regs := Function.update st7.regs 9 ptrBase }
  have hp8 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 7) (.const 1)) (.load (.reg 7))))
      st7 .normal st8 7 := by
    have hr7 : st7.regs 7 = h1 := by
      simp only [st7, Function.update_of_ne (by decide : (7 : ℕ) ≠ 8)]
      rw [hr6_ne 7 (by decide)]; simp [st5, st4]
    have hh1_1_w : h1 + 1 < 2 ^ w := by omega
    refine runs_assign_iff.mpr ⟨ptrBase, ?_, rfl, rfl, by simp [Expr.size]⟩
    exact Expr.eval_add (Expr.eval_add (by simp [Expr.eval, hr7]) (by simp [Expr.eval, hw1]) hh1_1_w)
      (Expr.eval_load_of_eq (by simp [Expr.eval, hr7]) rfl) hptr_w
  let st9 : State := { st8 with mem := Function.update st8.mem h ptrBase }
  have hp9 : Runs w p ω (.store (.reg 3) (.reg 9)) st8 .normal st9 3 := by
    have hr3 : st8.regs 3 = h := by
      simp only [st8, st7, Function.update_of_ne (by decide : (3 : ℕ) ≠ 9),
        Function.update_of_ne (by decide : (3 : ℕ) ≠ 8)]
      rw [hr6_ne 3 (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState]
    exact runs_store_iff.mpr ⟨h, ptrBase, by simp [Expr.eval, hr3],
      by simp [Expr.eval, st8], rfl, rfl, by simp [Expr.size]⟩
  have hp10 : Runs w p ω (.ret (.reg 8)) st9 (.returned o0.value) st9 2 :=
    runs_ret_iff.mpr ⟨o0.value, by simp [Expr.eval, st9, st8, st7], rfl, rfl, by simp [Expr.size]⟩
  have hrun : Runs w p ω (compAsmBatchProc compAsmIdxCopy compAsmIdxDgBatch compAsmIdxCompBatch)
      st0 (.returned o0.value) st9 (45 + cCp + cDg + c0) := by
    unfold compAsmBatchProc
    have t9 := runs_seq_iff.mpr (Or.inr ⟨st9, 3, 2, hp9, hp10, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨st8, 7, 6, hp8, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨st7, 3 + c0 + 1, 14, hp7, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨st6, cDg, 3 + c0 + 1 + 14 + 1, hp6, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨st5, 3 + cCp + 1, cDg + (3 + c0 + 1 + 14 + 1) + 1, hp5, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨st4, 4, (3 + cCp + 1) + (cDg + (3 + c0 + 1 + 14 + 1) + 1) + 1, hp4, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, hp3, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, hp2, t3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 3, _, hp1, t2, by omega⟩)
  -- Representation, `Respects`, `CompFamilyChgAt`, `CompSplitListAt`, and cost
  rcases hresp0 with ⟨hlo0, hhi0, _, hfr0, hft0⟩
  have hmem9_ne_h : ∀ a, a ≠ h → st9.mem a = st0'.mem a := fun a ha => Function.update_of_ne ha _ _
  have hbelow_b : ∀ a < x.bComp, st9.mem a = st6.mem a := fun a ha =>
    (hmem9_ne_h a (by omega)).trans (hfr0 a (by omega) fun hf => absurd ha (not_lt.mpr hf.1))
  have hbelow_g : ∀ a < x.gCopy, st9.mem a = mem a := fun a ha =>
    (hbelow_b a (by omega)).trans ((hDg_fr a (Or.inl ha)).trans (hCp_fr a (Or.inl (by omega))))
  have hm0' : st9.mem cfH = x.bComp := (hbelow_g cfH (by omega)).trans hm0
  have hm1' : st9.mem (cfH + 1) = x.gCopy := (hbelow_g (cfH + 1) (by omega)).trans hm1
  have hdg' : DynGraphAt st9.mem x.gCopy x.vCap x.eCap (cfs' 0).G := by
    rw [(compLSFBatch_fields (cfs 0) U).2.2]
    exact dynGraphAt_of_agree hdg_up fun a ha1 ha2 => hbelow_b a (by omega)
  have hcomp_ag : ∀ a, compFoot x.bComp xComp' a → st9.mem a = st0'.mem a := fun a ha => by
    rcases hft0 a ha with h1' | ⟨h1', _⟩
    · exact hmem9_ne_h a (ne_of_lt (hfoot a (Or.inr (Or.inr h1'))))
    · exact hmem9_ne_h a (by omega)
  have hS0'_fun : S0' = (fun j : Fin x.k => cfs' j.1) := by
    rw [hS0'_eq]; rfl
  have hcomp' : CompLSFRepAt W x.k x.bComp (fun j : Fin x.k => cfs' j.1) xComp' st9.mem :=
    (compLSFRepFull_local W x.k x.bComp (fun j : Fin x.k => cfs' j.1) xComp' st0'.mem st9.mem
      (fun a ha => (hcomp_ag a ha).symm)).1 (hS0'_fun ▸ hcomp0)
  have hphi' : compPhiFull x.k x.bComp xComp' st9.mem = compPhiFull x.k x.bComp xComp' st0'.mem :=
    ((compLSFRepFull_local W x.k x.bComp (fun j : Fin x.k => cfs' j.1) xComp' st0'.mem st9.mem
      (fun a ha => (hcomp_ag a ha).symm)).2).symm
  let x' : CompAsmMeta := { x with xComp := xComp' }
  have hrep' : compAsmRepPred Q_AN c_AN K_AN hQ L fmt.precision cfH cfs' x' st9.mem := by
    have hbf := compLSFBatch_fields (cfs 0) U
    exact ⟨hm0', hm1', hcf2, hgb, hk1, hbf.2.1.trans hk_x, hxV'.trans hxV, hxE'.trans hxE,
      by rw [hxLw', hxLw, hbf.1], hdg', hcomp'⟩
  have hChgAt : CompFamilyChgAt w x.k st9.mem ptrBase o0.value cfs U := by
    refine ⟨by omega, fun a ha1 ha2 => ?_,
      fun j => if hj : j < x.k then chgFin ⟨j, hj⟩ else chgFin ⟨0, hk1⟩, fun j hj => ?_⟩
    · rw [hmem9_ne_h a (by omega)]
      by_cases hlt : a < ptrBase + x.k
      · let jf : Fin x.k := ⟨a - ptrBase, by omega⟩
        have ha_eq : ptrBase + jf.1 = a := by dsimp [jf]; omega
        have hch := hChg jf
        rw [ha_eq] at hch
        omega
      · exact hSpAt.2.1 a (by omega) ha2
    · simp only [hj, ↓reduceDIte]
      obtain ⟨hAt, hEx, _, _, _, hlo_p, hhi_p⟩ := hChg ⟨j, hj⟩
      have hptr_eq : st9.mem (ptrBase + j) = st0'.mem (ptrBase + j) := hmem9_ne_h _ (by omega)
      rw [hptr_eq]
      set pJ := st0'.mem (ptrBase + j)
      have hw_def : (chgFin ⟨j, hj⟩).words =
          2 + ((chgFin ⟨j, hj⟩).roots.length + (chgFin ⟨j, hj⟩).fDel.length) := rfl
      refine ⟨⟨(hmem9_ne_h pJ (by omega)).trans hAt.1,
          listAt_of_agree hAt.2.1 fun a ha1 ha2 => hmem9_ne_h a (by omega),
          (hmem9_ne_h _ (by omega)).trans hAt.2.2.1,
          listAt_of_agree hAt.2.2.2 fun a ha1 ha2 => hmem9_ne_h a (by omega)⟩,
        by simpa [S, hS0'_fun] using hEx, by omega, hhi_p⟩
  have hSpAt9 : CompSplitListAt w x.k st9.mem (ptrBase + x.k) o0.value cfs U := by
    have h1 := compSplitListAt_congr (fun a ha1 ha2 => (hmem9_ne_h a (by omega)).symm) hSpAt
    refine ⟨h1.1, h1.2.1, fun j hj => ?_⟩
    simpa [hj, S] using h1.2.2 j hj
  -- Cost bound
  obtain ⟨ℓ₀, hBr⟩ := hcomp6.2.2.2.2.2.2.2.2.2.2.2.1
  have hc0_poly := hBatchCost x.k x.bComp bCopy h1 words (S ⟨0, hk1⟩).G₀ hk1 S st6.mem U
    ⟨W.C_lsst, ℓ₀, (hBr ⟨0, hk1⟩).1⟩ hBAt6.1 hBVal
  rw [hhdr6.2.2.2.1] at hc0_poly
  have hLw_le_canon : x.xComp.L_w ≤ canonLw K_AN L (cfs 0).G₀.n x.k := by
    rw [hxLw]; split_ifs
    · unfold canonLw; omega
    · exact le_rfl
  have hc0_le_canon : (200000 * (x.xComp.L_w + 1) + 3000) * x.k * (words + 1) ≤
      (200000 * (canonLw K_AN L (cfs 0).G₀.n x.k + 1) + 3000) * x.k * (words + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hcost_wrap := compAsmBatchCost_le (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN)
    (words := words) hRho hG0n hkCap hCap.2
  have hcDg_bd : cDg ≤ 3 + (670 * words + 30) + 1 := by
    simpa [argsSize, Expr.size, dgApplyBatchContract] using hcDg
  have hcost_tot :
      (45 + cCp + cDg + c0) +
        compPhiFull x'.k x'.bComp x'.xComp st9.mem ≤
      (compAsmSpec Q_AN c_AN K_AN).mul capExp limbMul *
        ((Finset.range x.k).sum (fun j => lsfBatchSize (cfs j) U) + (x.k + 1) * (words + 1)) *
        bundleLogFactor M N + compPhiFull x.k x.bComp x.xComp mem := by
    have hmono : compAsmMul Q_AN c_AN K_AN capExp limbMul * ((x.k + 1) * (words + 1)) * bundleLogFactor M N ≤
        compAsmMul Q_AN c_AN K_AN capExp limbMul *
          ((Finset.range x.k).sum (fun j => lsfBatchSize (cfs j) U) + (x.k + 1) * (words + 1)) *
          bundleLogFactor M N :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
    have hcost0' : c0 + compPhiFull x.k x.bComp xComp' st0'.mem ≤
        (200000 * (canonLw K_AN L (cfs 0).G₀.n x.k + 1) + 3000) * x.k * (words + 1) +
          compPhiFull x.k x.bComp x.xComp mem := by
      rw [hphi6] at hcost0
      exact le_trans hcost0 (Nat.add_le_add_right (le_trans hc0_poly hc0_le_canon) _)
    dsimp only [x', compAsmSpec]
    rw [hphi']
    linarith [hcCp, hcDg_bd, hcost0', hcost_wrap, hmono]
  have hv0 : (Outcome.returned o0.value).value = o0.value := rfl
  have hhi0' : o0.value ≤ h1 + (11 + 3 * U.length + words + 2 * max x.eCap 1 + 8 * x.vCap +
      x.k * (8 + 12 * x.vCap)) := by
    rw [← hsp0_eq]; exact hhi0
  refine ⟨compAsmBatchProc compAsmIdxCopy compAsmIdxDgBatch compAsmIdxCompBatch,
    compAsmProg_get1 Q_AN c_AN K_AN hQ, .returned o0.value, st9,
    45 + cCp + cDg + c0, x', hrun, hrep', rfl, rfl,
    by rw [hv0]; omega,
    by simp [st9]; omega,
    by rw [hv0]; simp only [st9, Function.update_self]; omega,
    by rw [hv0]; simpa [st9] using hChgAt,
    by rw [hv0]; simpa [st9] using hSpAt9,
    ⟨by rw [hv0]; omega,
      by rw [hv0]; omega,
      fun a ha => by rw [hv0] at ha; exact (hmem9_ne_h a (by omega)).trans (hz0' a ha),
      fun a ha hnf => by
        rw [hmem9_ne_h a (by omega)]
        rw [hfr0 a (by omega) fun hf => hnf (Or.inr (Or.inr hf))]
        have hnot_g : a < x.gCopy ∨ x.gCopy + dynGraphSize x.vCap x.eCap ≤ a := by
          by_contra hc; push Not at hc; exact hnf (Or.inr (Or.inl ⟨hc.1, hc.2⟩))
        exact (hDg_fr a hnot_g).trans (hCp_fr a (Or.inl (by omega))),
      fun a ha => by
        rw [hv0]
        rcases ha with h1' | h2' | h3'
        · exact Or.inl (Or.inl h1')
        · exact Or.inl (Or.inr (Or.inl h2'))
        · rcases hft0 a h3' with h4' | ⟨h4', h5'⟩
          · exact Or.inl (Or.inr (Or.inr h4'))
          · exact Or.inr ⟨by omega, h5'⟩⟩,
    hcost_tot⟩

end MinCostFlow.SparseCore.Program
