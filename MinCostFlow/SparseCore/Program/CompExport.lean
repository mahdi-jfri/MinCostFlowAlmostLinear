module

public import MinCostFlow.SparseCore.Program.CompExportContract
public import MinCostFlow.SparseCore.Program.CompExportGraphs
public import MinCostFlow.SparseCore.Program.CompExportFEdges
public import MinCostFlow.SparseCore.Program.CompExportPairs
import WordRAM.Tactic

/-!
# Branch Export Procedure (`op 6` of `compLSFDS`, `CompExport`)

Implements and verifies `compExportBranchProc` (`op 6` of `compLSFDS`): given `[b, j, gPtr, heap]`
where `gPtr` holds `DynGraphAt mem gPtr vCap0 eCap0 (S 0).G` below `heap`, exports branch `j`'s
`T`, `RF.F`, `RF.R`, and `wstrGlobal` numerator/denominator limb tables into `[heap, outEnd)` in
the exact layout consumed by both `Read.ReadInitAt` (`ReadSpec.lean`) and `CompBranchExportAt`
(`AssemblyTopIface.lean`), in strictly linear time
`≤ 350 * G.n + 180 * T.m + 100 * F.m + 40 * G.m * L_w + 100 * G.m + 500`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Helper wrapper procedures -/

/-- Copy `r2 = len` words from `r0 = src` to `r1 = dst` (`src + len ≤ dst`), returning `0`. -/
def compCopyWordsProc : Stmt :=
  .assign 3 (.const 0) ;;
  .loop (.bin .lt (.reg 3) (.reg 2))
    (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))) ;;
     .assign 3 (.bin .add (.reg 3) (.const 1))) ;;
  .ret (.const 0)

/-- Procedure wrapper for `compExpTEdgesStmt`: args `[b, j, k, tEPtr]`, returns `(S j).T.m`. -/
def compExpTEdgesProc : Stmt := compExpTEdgesStmt ;; .ret (.reg 4)

/-- Procedure wrapper for `compExpFEdgesStmt`: args `[b, j, k, fEPtr]`, returns `(S j).RF.F.m`. -/
def compExpFEdgesProc : Stmt := compExpFEdgesStmt ;; .ret (.reg 4)

/-- Procedure wrapper for `compExpRootsStmt`: args `[b, j, k, vPtr, nG, rootsPtr]`, returns `nR`. -/
def compExpRootsProc : Stmt := compExpRootsStmt ;; .ret (.reg 6)

/-- Procedure wrapper for `compExpPairsStmt`: args `[b, j, k, eListPtr, mG, numPtr, denPtr]`,
returns `0`. -/
def compExpPairsProc : Stmt := compExpPairsStmt ;; .ret (.const 0)

/-- Top-level single-branch export procedure (`op 6` of `compLSFDS`):
args `[b, j, gPtr, heap]`, writes the 8-word header
`[tD, fD, rootsPtr, nR, numPtr, denPtr, L_w, eCap]` at `[heap, heap + 8)`, `tD` at `[heap + 8, heap + 12)`,
`fD` at `[heap + 12, heap + 16)`, and all payloads in `[heap + 16, outEnd)`, returning `outEnd`. -/
def compExportBranchProc (bCopy bTEdges bFEdges bRoots bPairs : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffECap))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffLW))) ;;
  .assign 7 (.load (.bin .add (.reg 2) (.const dgVCapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 2) (.const dgECapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 2) (.const dgNOff))) ;;
  .assign 10 (.load (.bin .add (.reg 2) (.const dgMOff))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 7)) ;;
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
    (.bin .mul (.const 7) (.reg 7))) (.reg 8)) ;;
  .assign 13 (.bin .add (.reg 3) (.const 16)) ;;
  .call 14 bCopy [.reg 11, .reg 13, .reg 9] ;;
  .assign 14 (.bin .add (.reg 13) (.reg 9)) ;;
  .call 15 bTEdges [.reg 0, .reg 1, .reg 4, .reg 14] ;;
  .assign 16 (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 15))) ;;
  .call 17 bFEdges [.reg 0, .reg 1, .reg 4, .reg 16] ;;
  .assign 18 (.bin .add (.reg 16) (.bin .mul (.const 3) (.reg 17))) ;;
  .call 19 bRoots [.reg 0, .reg 1, .reg 4, .reg 13, .reg 9, .reg 18] ;;
  .assign 20 (.bin .add (.reg 18) (.reg 19)) ;;
  .assign 21 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 6))) ;;
  .call 22 bPairs [.reg 0, .reg 1, .reg 4, .reg 12, .reg 10, .reg 20, .reg 21] ;;
  .assign 22 (.bin .add (.reg 21) (.bin .mul (.reg 5) (.reg 6))) ;;
  .store (.reg 3) (.bin .add (.reg 3) (.const 8)) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.bin .add (.reg 3) (.const 12)) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 18) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 19) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.reg 20) ;;
  .store (.bin .add (.reg 3) (.const 5)) (.reg 21) ;;
  .store (.bin .add (.reg 3) (.const 6)) (.reg 6) ;;
  .store (.bin .add (.reg 3) (.const 7)) (.reg 5) ;;
  .store (.bin .add (.reg 3) (.const 8)) (.reg 9) ;;
  .store (.bin .add (.reg 3) (.const 9)) (.reg 13) ;;
  .store (.bin .add (.reg 3) (.const 10)) (.reg 15) ;;
  .store (.bin .add (.reg 3) (.const 11)) (.reg 14) ;;
  .store (.bin .add (.reg 3) (.const 12)) (.reg 9) ;;
  .store (.bin .add (.reg 3) (.const 13)) (.reg 13) ;;
  .store (.bin .add (.reg 3) (.const 14)) (.reg 17) ;;
  .store (.bin .add (.reg 3) (.const 15)) (.reg 16) ;;
  .ret (.reg 22)

lemma compCopyWordsProc_noRand : compCopyWordsProc.NoRand := by simp [compCopyWordsProc, Stmt.NoRand]
lemma compExpTEdgesProc_noRand : compExpTEdgesProc.NoRand := by
  simp [compExpTEdgesProc, compExpTEdgesStmt_noRand, Stmt.NoRand]
lemma compExpFEdgesProc_noRand : compExpFEdgesProc.NoRand := by
  simp [compExpFEdgesProc, compExpFEdgesStmt_noRand, Stmt.NoRand]
lemma compExpRootsProc_noRand : compExpRootsProc.NoRand := by
  simp [compExpRootsProc, compExpRootsStmt_noRand, Stmt.NoRand]
lemma compExpPairsProc_noRand : compExpPairsProc.NoRand := by
  simp [compExpPairsProc, compExpPairsStmt_noRand, Stmt.NoRand]
lemma compExportBranchProc_noRand (bC bT bF bR bP : ℕ) :
    (compExportBranchProc bC bT bF bR bP).NoRand := by
  simp [compExportBranchProc, Stmt.NoRand]

/-! ## 2. Verification of `compCopyWordsProc` -/

private lemma compCopyWords_runs {w src dst len : ℕ} {p : Program} {mem : ℕ → ℕ}
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

/-! ## 3. Verification of `compExportBranchProc` (`compLSFDS_op6`) -/

private lemma compExportTail_chain {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 : Stmt}
    {st1 st2 st2' st3 st3' st4 st4' st5 st5a st5b st6 st6' stF : State}
    {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℕ} {out : Outcome}
    (h1 : Runs w p ω s1 st1 .normal st2 c1)
    (h2 : Runs w p ω s2 st2 .normal st2' c2)
    (h3 : Runs w p ω s3 st2' .normal st3 c3)
    (h4 : Runs w p ω s4 st3 .normal st3' c4)
    (h5 : Runs w p ω s5 st3' .normal st4 c5)
    (h6 : Runs w p ω s6 st4 .normal st4' c6)
    (h7 : Runs w p ω s7 st4' .normal st5 c7)
    (h8 : Runs w p ω s8 st5 .normal st5a c8)
    (h9 : Runs w p ω s9 st5a .normal st5b c9)
    (h10 : Runs w p ω s10 st5b .normal st6 c10)
    (h11 : Runs w p ω s11 st6 .normal st6' c11)
    (h12 : Runs w p ω s12 st6' out stF c12) :
    Runs w p ω (.seq s1 (.seq s2 (.seq s3 (.seq s4 (.seq s5 (.seq s6
      (.seq s7 (.seq s8 (.seq s9 (.seq s10 (.seq s11 s12)))))))))))
      st1 out stF (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + 11) := by
  have h11_12 := runs_seq_iff.mpr (Or.inr ⟨st6', c11, c12, h11, h12, rfl⟩)
  have h10_12 := runs_seq_iff.mpr (Or.inr ⟨st6, c10, _, h10, h11_12, rfl⟩)
  have h9_12 := runs_seq_iff.mpr (Or.inr ⟨st5b, c9, _, h9, h10_12, rfl⟩)
  have h8_12 := runs_seq_iff.mpr (Or.inr ⟨st5a, c8, _, h8, h9_12, rfl⟩)
  have h7_12 := runs_seq_iff.mpr (Or.inr ⟨st5, c7, _, h7, h8_12, rfl⟩)
  have h6_12 := runs_seq_iff.mpr (Or.inr ⟨st4', c6, _, h6, h7_12, rfl⟩)
  have h5_12 := runs_seq_iff.mpr (Or.inr ⟨st4, c5, _, h5, h6_12, rfl⟩)
  have h4_12 := runs_seq_iff.mpr (Or.inr ⟨st3', c4, _, h4, h5_12, rfl⟩)
  have h3_12 := runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, h3, h4_12, rfl⟩)
  have h2_12 := runs_seq_iff.mpr (Or.inr ⟨st2', c2, _, h2, h3_12, rfl⟩)
  have h1_12 := runs_seq_iff.mpr (Or.inr ⟨st2, c1, _, h1, h2_12, rfl⟩)
  convert h1_12 using 1; ring

private lemma compExport_exec {w b j gPtr heap k eCap L_w vCap0 eCap0 nG mG mT mF nR pos
    bCopy bTEdges bFEdges bRoots bPairs cCp cT cF cR cP : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {stCp0 stT0 stF0 stR0 stP0 : State}
    (hpCopy : p.procs[bCopy]? = some compCopyWordsProc)
    (hpTEdges : p.procs[bTEdges]? = some compExpTEdgesProc)
    (hpFEdges : p.procs[bFEdges]? = some compExpFEdgesProc)
    (hpRoots : p.procs[bRoots]? = some compExpRootsProc)
    (hpPairs : p.procs[bPairs]? = some compExpPairsProc)
    (hw16 : 16 ≤ 2 ^ w) (h16w : 16 < 2 ^ w)
    (hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w)
    (hdg_w : gPtr + dynGraphSize vCap0 eCap0 < 2 ^ w)
    (h_k : mem (b + compOffK) = k) (h_eC : mem (b + compOffECap) = eCap)
    (h_Lw : mem (b + compOffLW) = L_w)
    (h_v0 : mem (gPtr + dgVCapOff) = vCap0) (h_e0 : mem (gPtr + dgECapOff) = eCap0)
    (h_nG : mem (gPtr + dgNOff) = nG) (h_mG : mem (gPtr + dgMOff) = mG)
    (hout_w : heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + eCap * L_w < 2 ^ w)
    (hrunCp0 : Runs w p ω compCopyWordsProc
      (startState [dgVListBase gPtr vCap0, heap + 16, nG] mem pos) (.returned 0) stCp0 cCp)
    (hrunT0 : Runs w p ω compExpTEdgesProc
      (startState [b, j, k, heap + 16 + nG] stCp0.mem stCp0.pos) (.returned mT) stT0 cT)
    (hrunF0 : Runs w p ω compExpFEdgesProc
      (startState [b, j, k, heap + 16 + nG + 3 * mT] stT0.mem stT0.pos) (.returned mF) stF0 cF)
    (hrunR0 : Runs w p ω compExpRootsProc
      (startState [b, j, k, heap + 16, nG, heap + 16 + nG + 3 * mT + 3 * mF] stF0.mem stF0.pos)
      (.returned nR) stR0 cR)
    (hrunP0 : Runs w p ω compExpPairsProc
      (startState [b, j, k, dgEListBase gPtr vCap0 eCap0, mG,
        heap + 16 + nG + 3 * mT + 3 * mF + nR,
        heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w] stR0.mem stR0.pos)
      (.returned 0) stP0 cP) :
    let vPtr := heap + 16
    let tEPtr := vPtr + nG
    let fEPtr := tEPtr + 3 * mT
    let rootsPtr := fEPtr + 3 * mF
    let numPtr := rootsPtr + nR
    let denPtr := numPtr + eCap * L_w
    let outEnd := denPtr + eCap * L_w
    ∃ stF,
      Runs w p ω (compExportBranchProc bCopy bTEdges bFEdges bRoots bPairs)
        (startState [b, j, gPtr, heap] mem pos) (.returned outEnd) stF
        (237 + cCp + cT + cF + cR + cP) ∧
      (∀ a, a < heap ∨ heap + 16 ≤ a → stF.mem a = stP0.mem a) ∧
      stF.mem heap = heap + 8 ∧ stF.mem (heap + 1) = heap + 12 ∧
      stF.mem (heap + 2) = rootsPtr ∧ stF.mem (heap + 3) = nR ∧
      stF.mem (heap + 4) = numPtr ∧ stF.mem (heap + 5) = denPtr ∧
      stF.mem (heap + 6) = L_w ∧ stF.mem (heap + 7) = eCap ∧
      stF.mem (heap + 8) = nG ∧ stF.mem (heap + 9) = vPtr ∧
      stF.mem (heap + 10) = mT ∧ stF.mem (heap + 11) = tEPtr ∧
      stF.mem (heap + 12) = nG ∧ stF.mem (heap + 13) = vPtr ∧
      stF.mem (heap + 14) = mF ∧ stF.mem (heap + 15) = fEPtr := by
  intro vPtr tEPtr fEPtr rootsPtr numPtr denPtr outEnd
  obtain ⟨st1, hst1_mem, hst1_pos, hpref, h1_0, h1_1, _h1_2, h1_3, h1_4, h1_5, h1_6, _h1_7, _h1_8,
    h1_9, h1_10, h1_11, h1_12, h1_13⟩ :=
    compExportPrefix_runs (p := p) (ω := ω) (b := b) (j := j) (gPtr := gPtr) (heap := heap)
      (k := k) (eCap := eCap) (L_w := L_w) (vCap0 := vCap0) (eCap0 := eCap0)
      (nG := nG) (mG := mG) (pos := pos) hw16 h16w hb_off hdg_w (by omega)
      h_k h_eC h_Lw h_v0 h_e0 h_nG h_mG
  let st2 : State := { st1 with regs := Function.update st1.regs 14 0, mem := stCp0.mem, pos := stCp0.pos }
  have hcallCp : Runs w p ω (.call 14 bCopy [.reg 11, .reg 13, .reg 9]) st1 .normal st2 (cCp + 4) := by
    rw [runs_call_iff]
    refine ⟨[dgVListBase gPtr vCap0, vPtr, nG], compCopyWordsProc, .returned 0, stCp0, cCp, ?_, hpCopy,
      by rw [hst1_mem, hst1_pos]; exact hrunCp0, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, h1_11, h1_13, h1_9, vPtr]
  let st2' : State := { st2 with regs := Function.update st2.regs 14 tEPtr }
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 9))) st2 .normal st2' 4 :=
    runs_assign_iff.mpr ⟨tEPtr, by
      simp [st2, Expr.eval, BinOp.eval, h1_13, h1_9, tEPtr, vPtr, show heap + 16 + nG < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2' with regs := Function.update st2'.regs 15 mT, mem := stT0.mem, pos := stT0.pos }
  have hcallT : Runs w p ω (.call 15 bTEdges [.reg 0, .reg 1, .reg 4, .reg 14]) st2' .normal st3 (cT + 5) := by
    rw [runs_call_iff]
    refine ⟨[b, j, k, tEPtr], compExpTEdgesProc, .returned mT, stT0, cT, ?_, hpTEdges, hrunT0,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, st2', st2, h1_0, h1_1, h1_4]
  let st3' : State := { st3 with regs := Function.update st3.regs 16 fEPtr }
  have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 15)))) st3 .normal st3' 6 :=
    runs_assign_iff.mpr ⟨fEPtr, by
      simp [st3, st2', Expr.eval, BinOp.eval, fEPtr, show 3 < 2 ^ w by omega,
        show 3 * mT < 2 ^ w by omega, show tEPtr + 3 * mT < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3' with regs := Function.update st3'.regs 17 mF, mem := stF0.mem, pos := stF0.pos }
  have hcallF : Runs w p ω (.call 17 bFEdges [.reg 0, .reg 1, .reg 4, .reg 16]) st3' .normal st4 (cF + 5) := by
    rw [runs_call_iff]
    refine ⟨[b, j, k, fEPtr], compExpFEdgesProc, .returned mF, stF0, cF, ?_, hpFEdges, hrunF0,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, st3', st3, st2', st2, h1_0, h1_1, h1_4]
  let st4' : State := { st4 with regs := Function.update st4.regs 18 rootsPtr }
  have ha18 : Runs w p ω (.assign 18 (.bin .add (.reg 16) (.bin .mul (.const 3) (.reg 17)))) st4 .normal st4' 6 :=
    runs_assign_iff.mpr ⟨rootsPtr, by
      simp [st4, st3', Expr.eval, BinOp.eval, rootsPtr, show 3 < 2 ^ w by omega,
        show 3 * mF < 2 ^ w by omega, show fEPtr + 3 * mF < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  let st5 : State := { st4' with regs := Function.update st4'.regs 19 nR, mem := stR0.mem, pos := stR0.pos }
  have hcallR : Runs w p ω (.call 19 bRoots [.reg 0, .reg 1, .reg 4, .reg 13, .reg 9, .reg 18]) st4' .normal st5 (cR + 7) := by
    rw [runs_call_iff]
    refine ⟨[b, j, k, vPtr, nG, rootsPtr], compExpRootsProc, .returned nR, stR0, cR, ?_, hpRoots, hrunR0,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, st4', st4, st3', st3, st2', st2, h1_0, h1_1, h1_4, h1_13, h1_9, vPtr]
  let st5a : State := { st5 with regs := Function.update st5.regs 20 numPtr }
  let st5b : State := { st5a with regs := Function.update st5a.regs 21 denPtr }
  have ha20 : Runs w p ω (.assign 20 (.bin .add (.reg 18) (.reg 19))) st5 .normal st5a 4 :=
    runs_assign_iff.mpr ⟨numPtr, by
      simp [st5, st4', Expr.eval, BinOp.eval, numPtr, show rootsPtr + nR < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha21 : Runs w p ω (.assign 21 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 6)))) st5a .normal st5b 6 :=
    runs_assign_iff.mpr ⟨denPtr, by
      simp [st5a, st5, st4', st4, st3', st3, st2', st2, h1_5, h1_6,
        Expr.eval, BinOp.eval, denPtr, show eCap * L_w < 2 ^ w by omega,
        show numPtr + eCap * L_w < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  let st6 : State := { st5b with regs := Function.update st5b.regs 22 0, mem := stP0.mem, pos := stP0.pos }
  have hcallP : Runs w p ω (.call 22 bPairs [.reg 0, .reg 1, .reg 4, .reg 12, .reg 10, .reg 20, .reg 21])
      st5b .normal st6 (cP + 8) := by
    rw [runs_call_iff]
    refine ⟨[b, j, k, dgEListBase gPtr vCap0 eCap0, mG, numPtr, denPtr], compExpPairsProc,
      .returned 0, stP0, cP, ?_, hpPairs, hrunP0, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, st5b, st5a, st5, st4', st4, st3', st3, st2', st2, h1_0, h1_1, h1_4, h1_12, h1_10]
  let st6' : State := { st6 with regs := Function.update st6.regs 22 outEnd }
  have ha22 : Runs w p ω (.assign 22 (.bin .add (.reg 21) (.bin .mul (.reg 5) (.reg 6)))) st6 .normal st6' 6 :=
    runs_assign_iff.mpr ⟨outEnd, by
      simp [st6, st5b, st5a, st5, st4', st4, st3', st3, st2', st2, h1_5, h1_6,
        Expr.eval, BinOp.eval, outEnd, show eCap * L_w < 2 ^ w by omega, show outEnd < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hst6'_regs :
      st6'.regs 3 = heap ∧ st6'.regs 5 = eCap ∧ st6'.regs 6 = L_w ∧
      st6'.regs 9 = nG ∧ st6'.regs 13 = vPtr ∧ st6'.regs 14 = tEPtr ∧
      st6'.regs 15 = mT ∧ st6'.regs 16 = fEPtr ∧ st6'.regs 17 = mF ∧
      st6'.regs 18 = rootsPtr ∧ st6'.regs 19 = nR ∧ st6'.regs 20 = numPtr ∧
      st6'.regs 21 = denPtr ∧ st6'.regs 22 = outEnd := by
    simp [st6', st6, st5b, st5a, st5, st4', st4, st3', st3, st2', st2,
      h1_3, h1_5, h1_6, h1_9, h1_13, vPtr]
  obtain ⟨stF, hstore_hdr, hm15_out, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hm12, hm13, hm14, hm15⟩ :=
    compExportStoreHdr_runs (p := p) (ω := ω) hw16 (by omega) hst6'_regs
  have hrun_tail := compExportTail_chain hcallCp ha14 hcallT ha16 hcallF ha18 hcallR ha20 ha21 hcallP ha22 hstore_hdr
  have hrun_full : Runs w p ω (compExportBranchProc bCopy bTEdges bFEdges bRoots bPairs)
      (startState [b, j, gPtr, heap] mem pos) (.returned outEnd) stF
      (237 + cCp + cT + cF + cR + cP) := by
    have h := hpref _ (.returned outEnd) stF _ hrun_tail
    unfold compExportBranchProc
    convert h using 1; omega
  exact ⟨stF, hrun_full, hm15_out, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hm12, hm13, hm14, hm15⟩

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of `op 6` (`compExportBranchProc`) for `compLSFDS`: exports branch `j`'s
`T`, `RF.F`, `RF.R`, and `wstrGlobal` limb tables into `[heap, outEnd)`, preserves `compLSFRep`
and potential unchanged, satisfies `CompExportPost` and `Respects`, and runs in strictly linear
time `≤ compExportCost`. -/
theorem compLSFDS_op6 {W : LSFWindowImpl} {w k b bCopy bTEdges bFEdges bRoots bPairs : ℕ}
    {G₀ : MGraph} {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpCopy : p.procs[bCopy]? = some compCopyWordsProc)
    (hpTEdges : p.procs[bTEdges]? = some compExpTEdgesProc)
    (hpFEdges : p.procs[bFEdges]? = some compExpFEdgesProc)
    (hpRoots : p.procs[bRoots]? = some compExpRootsProc)
    (hpPairs : p.procs[bPairs]? = some compExpPairsProc)
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDSFull W w k G₀).pre 6 S args mem)
    (hwords : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDSFull W w k G₀).space 6 S args mem < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω (compExportBranchProc bCopy bTEdges bFEdges bRoots bPairs)
        (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDSFull W w k G₀).post 6 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDSFull W w k G₀).space 6 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤
          (compLSFDSFull W w k G₀).cost 6 S args mem + compPhi b x mem ∧
        x' = x ∧
        o.value = st'.mem (heapArg args + 5) + mem (b + compOffECap) * mem (b + compOffLW) := by
  dsimp only [compLSFDSFull, ite_true] at hpre hsp ⊢
  obtain ⟨hk, b', j, gPtr, heap, vCap0, eCap0, hargs, hw16, hj, hdgG, hdg_le⟩ := hpre
  subst hargs
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  have hheap_eq : heapArg [b, j, gPtr, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  let jF : Fin k := ⟨j, hj⟩
  have hrep_orig := hrep
  obtain ⟨hk', _, _, _, hLw, _, _, _, _, hTE, hhdr, ⟨ℓ₀, hBr⟩, hm0Tot, hT,
    hCompMeta, hEFMeta, _, _, _, _, _, _, hWins, _⟩ := hrep
  have hS_G := (hBr jF).2.2.1
  have hS_G0 := (hBr jF).2.1
  have hIj := (hBr jF).1
  have hI0 := (hBr ⟨0, hk⟩).1
  have hend_heap : x.endAddr ≤ heap := by
    have hb_lt_end : b < x.endAddr := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hTE; omega
    have hlt := hdisj (x.endAddr - 1) ⟨by omega, by omega⟩
    omega
  have hmem_vCap : mem (b + compOffVCap) = x.vCap := hhdr.1
  have hmem_eCap : mem (b + compOffECap) = x.eCap := hhdr.2.1
  have hmem_k : mem (b + compOffK) = k := hhdr.2.2.1
  have hmem_Lw : mem (b + compOffLW) = x.L_w := hhdr.2.2.2.1
  have hsp_eq : compExportSpace [b, j, gPtr, heap] mem =
      16 + 2 * x.vCap + 6 * x.eCap + 2 * x.eCap * x.L_w := by
    simp only [compExportSpace, List.getD_cons_zero, hmem_vCap, hmem_eCap, hmem_Lw]
  have hsp_lt : heap + (16 + 2 * x.vCap + 6 * x.eCap + 2 * x.eCap * x.L_w) < 2 ^ w := by
    rwa [hsp_eq] at hsp
  -- Extract `DynGraphAt` components
  obtain ⟨hdgVal, hdgV, hdgE, hdg_vC, hdg_eC, hdg_n, hdg_m, _, ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩,
    _, _, _, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩, _, _⟩ := hdgG
  -- Size bounds
  have hnG_eq : (S jF).G.n = (S ⟨0, hk⟩).G.n := by rw [hS_G]
  have hmG_eq : (S jF).G.m = (S ⟨0, hk⟩).G.m := by rw [hS_G]
  have hnG_le_vC : (S jF).G.n ≤ x.vCap := by
    change (S jF).G.V.card ≤ x.vCap
    rw [hS_G]
    exact (Finset.card_le_card fun v hv => Finset.mem_range.mpr (hT.hVlt v hv)).trans (by simp)
  have hm0_le_eC : x.m0Total ≤ x.eCap := by
    rw [← hm0Tot]; change (S ⟨0, hk⟩).G₀.E.card ≤ x.eCap
    refine (Finset.card_le_card (t := Finset.range x.eCap) fun e he => Finset.mem_range.mpr ?_).trans (by simp)
    have hcomp := (components_biUnion_compEdgeSet (S ⟨0, hk⟩).G₀ hI0.hG₀_val) ▸ he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp hcomp
    obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
    have hm1 : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m := Finset.card_pos.mpr ⟨e, heC⟩
    obtain ⟨ec, _, _, hceq⟩ := (hCompMeta c).2.2.2 hm1
    obtain ⟨_, hWrep, _, heW, _, _, _⟩ := hWins ec ⟨0, hk⟩
    have heG0C : e ∈ ((S ⟨0, hk⟩).compSt (x.compOf (x.edgefulComp ec))).G₀.E := by
      rw [hceq, (hI0.hCompLSF _ hC).2.1]; exact heC
    exact heW ▸ hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heG0C
  have hTm_le_m0 : (S jF).T.m ≤ x.m0Total := by
    rw [← hm0Tot, ← hS_G0]; exact (compLSF_T_eq_edgeful hIj).2.2.2.2.1
  have hFm_le_m0 : (S jF).RF.F.m ≤ x.m0Total := by
    rw [← hm0Tot, ← hS_G0]; exact (compLSF_F_eq_edgeful hIj).2.2.2
  have hTE_lt_eCap : ∀ e ∈ (S jF).T.E, e < x.eCap := fun e he => by
    have heG : e ∈ (S jF).G.E := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1
    exact hT.hElt e (hS_G ▸ heG)
  have hne_le_n : x.numEdgeful ≤ (S jF).G.n := by
    have hef_inj : Function.Injective x.edgefulComp := fun a b hab =>
      Fin.ext (by rw [← (hEFMeta a).2, ← (hEFMeta b).2, hab])
    have h := compLSF_numEdgeful_le_n hI0 hT hef_inj
    omega
  have hdg_size_def : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  have hVL_end : dgVListBase gPtr vCap0 + vL.length ≤ heap := by
    have hvL_v0 : vL.length ≤ vCap0 := by
      rw [hvL_len]; change (S ⟨0, hk⟩).G.V.card ≤ vCap0
      exact (Finset.card_le_card (t := Finset.range vCap0) fun v hv =>
        Finset.mem_range.mpr (hdgV v hv)).trans (by simp)
    dsimp only [dgVListBase]; omega
  have hEL_end : dgEListBase gPtr vCap0 eCap0 + eL.length ≤ heap := by
    have heL_e0 : eL.length ≤ eCap0 := by
      rw [heL_len]; change (S ⟨0, hk⟩).G.E.card ≤ eCap0
      exact (Finset.card_le_card (t := Finset.range eCap0) fun e he =>
        Finset.mem_range.mpr (hdgE e he)).trans (by simp)
    dsimp only [dgEListBase]; omega
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  -- Define layout addresses
  set nG := (S jF).G.n
  set mG := (S jF).G.m
  set vListPtr := dgVListBase gPtr vCap0
  set eListPtr := dgEListBase gPtr vCap0 eCap0
  set vPtr := heap + 16
  set tEPtr := vPtr + nG
  set mT := (S jF).T.m
  set fEPtr := tEPtr + 3 * mT
  set mF := (S jF).RF.F.m
  set rootsPtr := fEPtr + 3 * mF
  set roots := vL.filter fun v => decide (v ∈ (S jF).RF.R)
  set nR := roots.length
  have hnR_le_nG : nR ≤ nG := le_trans (List.length_filter_le _ _) (by omega)
  set numPtr := rootsPtr + nR
  set denPtr := numPtr + x.eCap * x.L_w
  set outEnd := denPtr + x.eCap * x.L_w
  have hout_le_sp : outEnd ≤ heap + (16 + 2 * x.vCap + 6 * x.eCap + 2 * x.eCap * x.L_w) := by
    have h2e : 2 * x.eCap * x.L_w = x.eCap * x.L_w + x.eCap * x.L_w := by ring
    dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
  have hge16 : heap + 16 ≤ outEnd := by
    dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
  have hout_bounds : ∀ a, a < heap ∨ outEnd ≤ a →
      (a < numPtr ∨ numPtr + x.eCap * x.L_w ≤ a) ∧
      (a < denPtr ∨ denPtr + x.eCap * x.L_w ≤ a) ∧
      (a < rootsPtr ∨ rootsPtr + roots.length ≤ a) ∧
      (a < fEPtr ∨ fEPtr + 3 * (S jF).RF.F.m ≤ a) ∧
      (a < tEPtr ∨ tEPtr + 3 * (S jF).T.m ≤ a) ∧
      (a < vPtr ∨ vPtr + nG ≤ a) := fun a ha => by
    dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr, nR, mF, mT] at ha ⊢
    rcases ha with h | h <;> exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  -- Step 1..6: Run the five helper procedures sequentially
  have h16w : 16 < 2 ^ w := by
    have h16le : 16 ≤ 16 + 2 * x.vCap + 6 * x.eCap + 2 * x.eCap * x.L_w := by omega
    omega
  obtain ⟨stCp0, cCp, hrunCp0, hCp_done, hCp_fr, hcCp⟩ :=
    compCopyWords_runs (p := p) (src := vListPtr) (dst := vPtr) (len := nG) (mem := mem) (pos := pos) (ω := ω)
      hw16 (by omega) (by omega)
  have hrep2 : CompLSFRepAt W k b S x stCp0.mem :=
    (compLSFRep_local W k b S x mem stCp0.mem fun a ha =>
      (hCp_fr a (Or.inl (by have := ha.2; omega))).symm).1 hrep_orig
  have hvPtr_at2 : ListAt stCp0.mem vPtr vL := fun i hi =>
    (hCp_done i (by omega)).trans (hvL_at i hi)
  obtain ⟨stT0, cT, eT, hrunT_s, _, hrT4, heT_len, heT_nd, heT_in, heT_cov, heT_mem, hT_fr, hcT⟩ :=
    compExpTEdges_runs (W := W) (w := w) (k := k) (b := b) (tEPtr := tEPtr)
      (st := startState [b, j, k, tEPtr] stCp0.mem stCp0.pos) (ω := ω) jF hw16 hrep2 (by omega) (by omega)
      (by simp [startState]) (by simp [startState, jF]) (by simp [startState]) (by simp [startState])
  have hrunT0 : Runs w p ω compExpTEdgesProc (startState [b, j, k, tEPtr] stCp0.mem stCp0.pos)
      (.returned mT) stT0 (cT + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨stT0, cT, 2, hrunT_s,
      runs_ret_iff.mpr ⟨mT, by simp [Expr.eval, hrT4, mT], rfl, rfl, by simp [Expr.size]⟩, by omega⟩)
  have hrep3 : CompLSFRepAt W k b S x stT0.mem :=
    (compLSFRep_local W k b S x stCp0.mem stT0.mem fun a ha => (hT_fr a (Or.inl (by have := ha.2; omega))).symm).1 hrep2
  obtain ⟨stF0, cF, eF, hrunF_s, _, hrF4, heF_len, heF_nd, heF_in, heF_cov, heF_mem, hF_fr, hcF⟩ :=
    compExpFEdges_runs (W := W) (w := w) (k := k) (b := b) (fEPtr := fEPtr)
      (st := startState [b, j, k, fEPtr] stT0.mem stT0.pos) (ω := ω) jF hw16 hrep3 (by omega) (by omega)
      (by simp [startState]) (by simp [startState, jF]) (by simp [startState]) (by simp [startState])
  have hrunF0 : Runs w p ω compExpFEdgesProc (startState [b, j, k, fEPtr] stT0.mem stT0.pos)
      (.returned mF) stF0 (cF + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨stF0, cF, 2, hrunF_s,
      runs_ret_iff.mpr ⟨mF, by simp [Expr.eval, hrF4, mF], rfl, rfl, by simp [Expr.size]⟩, by omega⟩)
  have hrep4 : CompLSFRepAt W k b S x stF0.mem :=
    (compLSFRep_local W k b S x stT0.mem stF0.mem fun a ha => (hF_fr a (Or.inl (by have := ha.2; omega))).symm).1 hrep3
  have hvPtr_at4 : ListAt stF0.mem vPtr vL := fun i hi =>
    (hF_fr (vPtr + i) (Or.inl (by omega))).trans ((hT_fr (vPtr + i) (Or.inl (by omega))).trans (hvPtr_at2 i hi))
  obtain ⟨stR0, cR, hrunR_s, _, hrR6, hR_nd, hR_fs, hR_len, _, hR_at, hR_fr, hcR⟩ :=
    compExpRoots_runs (W := W) (w := w) (k := k) (b := b) (vPtr := vPtr) (rootsPtr := rootsPtr)
      (vL := vL) (st := startState [b, j, k, vPtr, nG, rootsPtr] stF0.mem stF0.pos) (ω := ω) jF hw16 hrep4
      hvL_nd (fun v => by rw [hvL_mem, hS_G]) hvPtr_at4 (by omega) (by omega) (by omega)
      (by simp [startState]) (by simp [startState, jF]) (by simp [startState])
      (by simp [startState]) (by simp [startState, hvL_len, hnG_eq, nG]) (by simp [startState])
  have hrunR0 : Runs w p ω compExpRootsProc (startState [b, j, k, vPtr, nG, rootsPtr] stF0.mem stF0.pos)
      (.returned nR) stR0 (cR + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨stR0, cR, 2, hrunR_s,
      runs_ret_iff.mpr ⟨nR, by simp [Expr.eval, hrR6, nR, roots], rfl, rfl, by simp [Expr.size]⟩, by omega⟩)
  have hrep5 : CompLSFRepAt W k b S x stR0.mem :=
    (compLSFRep_local W k b S x stF0.mem stR0.mem fun a ha => (hR_fr a (Or.inl (by have := ha.2; omega))).symm).1 hrep4
  have heL_at5 : ListAt stR0.mem eListPtr eL := fun i hi => by
    dsimp only [startState] at hR_fr hF_fr hT_fr
    rw [hR_fr _ (Or.inl (by omega)), hF_fr _ (Or.inl (by omega)),
        hT_fr _ (Or.inl (by omega)), hCp_fr _ (Or.inl (by omega))]
    exact heL_at i hi
  obtain ⟨stP0, cP, hrunP_s, _, hP_done, hP_fr, hP_frE, hcP⟩ :=
    compExpPairs_runs (W := W) (w := w) (k := k) (b := b) (eListPtr := eListPtr)
      (numPtr := numPtr) (denPtr := denPtr) (eL := eL)
      (st := startState [b, j, k, eListPtr, mG, numPtr, denPtr] stR0.mem stR0.pos) (ω := ω) jF hw16 hrep5
      (heL_len.trans hmG_eq.symm) heL_nd (fun e => by rw [heL_mem, hS_G]) heL_at5
      (fun a h1 _ => Or.inr (by omega)) (fun a h1 _ => Or.inr (by omega))
      (by omega) (by omega) (le_refl _) (by omega)
      (by simp [startState]) (by simp [startState, jF]) (by simp [startState]) (by simp [startState])
      (by simp [startState, mG]) (by simp [startState]) (by simp [startState])
  have hrunP0 : Runs w p ω compExpPairsProc (startState [b, j, k, eListPtr, mG, numPtr, denPtr] stR0.mem stR0.pos)
      (.returned 0) stP0 (cP + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨stP0, cP, 2, hrunP_s,
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩, by omega⟩)
  -- Execute full `compExportBranchProc`
  obtain ⟨stF, hrun_full, hm15_out, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hm12, hm13, hm14, hm15⟩ :=
    compExport_exec hpCopy hpTEdges hpFEdges hpRoots hpPairs hw16 h16w hb_off (by omega)
      hmem_k hmem_eCap hmem_Lw hdg_vC hdg_eC (hdg_n.trans hnG_eq.symm) (hdg_m.trans hmG_eq.symm)
      (by dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hout_le_sp; omega)
      hrunCp0 hrunT0 hrunF0 hrunR0 hrunP0
  -- Frame outside `[heap, outEnd)`
  clear hrep2 hrep3 hrep4 hrep5
  dsimp only [startState] at hT_fr hF_fr hR_fr hP_fr
  have hfr_all : ∀ a, a < heap ∨ outEnd ≤ a → stF.mem a = mem a := fun a ha => by
    obtain ⟨hP1, hP2, hR1, hF1, hT1, hC1⟩ := hout_bounds a ha
    rw [hm15_out a (ha.imp_right (le_trans hge16)), hP_fr a hP1 hP2, hR_fr a hR1, hF_fr a hF1,
        hT_fr a hT1, hCp_fr a hC1]
  have hrep_final : CompLSFRepAt W k b S x stF.mem :=
    (compLSFRep_local W k b S x mem stF.mem fun a ha => (hfr_all a (Or.inl (hdisj a ha))).symm).1 hrep_orig
  have hphi_eq : compPhi b x stF.mem = compPhi b x mem :=
    (compLSFRep_local W k b S x mem stF.mem fun a ha => (hfr_all a (Or.inl (hdisj a ha))).symm).2.symm
  have hz_final : ZeroFrom stF.mem outEnd := fun a ha => (hfr_all a (Or.inr ha)).trans (hz a (by omega))
  -- Export payloads preserved in `stF.mem`
  have hstF_ge16 : ∀ a, heap + 16 ≤ a → stF.mem a = stP0.mem a := fun a ha =>
    hm15_out a (Or.inr ha)
  have hvL_final : ListAt stF.mem vPtr vL := fun i hi => by
    have ha1 : heap + 16 ≤ vPtr + i := by dsimp only [vPtr]; omega
    have ha2 : vPtr + i < rootsPtr := by dsimp only [rootsPtr, fEPtr, tEPtr]; omega
    have ha3 : vPtr + i < numPtr := by dsimp only [numPtr]; omega
    have ha4 : vPtr + i < denPtr := by dsimp only [denPtr]; omega
    rw [hstF_ge16 _ ha1, hP_fr _ (Or.inl ha3) (Or.inl ha4), hR_fr _ (Or.inl ha2)]
    exact hvPtr_at4 i hi
  have heT_final : ∀ i (hi : i < eT.length),
      stF.mem (tEPtr + 3 * i) = eT[i].1 ∧ stF.mem (tEPtr + 3 * i + 1) = eT[i].2.1 ∧
      stF.mem (tEPtr + 3 * i + 2) = eT[i].2.2 := fun i hi => by
    have h1 : ∀ d < 3, stF.mem (tEPtr + 3 * i + d) = stT0.mem (tEPtr + 3 * i + d) := fun d hd => by
      have ha1 : heap + 16 ≤ tEPtr + 3 * i + d := by dsimp only [tEPtr, vPtr]; omega
      have ha2 : tEPtr + 3 * i + d < fEPtr := by dsimp only [fEPtr, mT]; omega
      have ha3 : tEPtr + 3 * i + d < rootsPtr := by dsimp only [rootsPtr]; omega
      have ha4 : tEPtr + 3 * i + d < numPtr := by dsimp only [numPtr]; omega
      have ha5 : tEPtr + 3 * i + d < denPtr := by dsimp only [denPtr]; omega
      rw [hstF_ge16 _ ha1, hP_fr _ (Or.inl ha4) (Or.inl ha5), hR_fr _ (Or.inl ha3), hF_fr _ (Or.inl ha2)]
    have h0 := h1 0 (by omega); simp only [Nat.add_zero] at h0
    exact ⟨h0.trans (heT_mem i hi).1, (h1 1 (by omega)).trans (heT_mem i hi).2.1,
      (h1 2 (by omega)).trans (heT_mem i hi).2.2⟩
  have heF_final : ∀ i (hi : i < eF.length),
      stF.mem (fEPtr + 3 * i) = eF[i].1 ∧ stF.mem (fEPtr + 3 * i + 1) = eF[i].2.1 ∧
      stF.mem (fEPtr + 3 * i + 2) = eF[i].2.2 := fun i hi => by
    have h1 : ∀ d < 3, stF.mem (fEPtr + 3 * i + d) = stF0.mem (fEPtr + 3 * i + d) := fun d hd => by
      have ha1 : heap + 16 ≤ fEPtr + 3 * i + d := by dsimp only [fEPtr, tEPtr, vPtr]; omega
      have ha2 : fEPtr + 3 * i + d < rootsPtr := by dsimp only [rootsPtr, mF]; omega
      have ha3 : fEPtr + 3 * i + d < numPtr := by dsimp only [numPtr]; omega
      have ha4 : fEPtr + 3 * i + d < denPtr := by dsimp only [denPtr]; omega
      rw [hstF_ge16 _ ha1, hP_fr _ (Or.inl ha3) (Or.inl ha4), hR_fr _ (Or.inl ha2)]
    have h0 := h1 0 (by omega); simp only [Nat.add_zero] at h0
    exact ⟨h0.trans (heF_mem i hi).1, (h1 1 (by omega)).trans (heF_mem i hi).2.1,
      (h1 2 (by omega)).trans (heF_mem i hi).2.2⟩
  have hR_final : ListAt stF.mem rootsPtr roots := fun i hi => by
    have ha1 : heap + 16 ≤ rootsPtr + i := by dsimp only [rootsPtr, fEPtr, tEPtr, vPtr]; omega
    have ha2 : rootsPtr + i < numPtr := by dsimp only [numPtr, nR]; omega
    have ha3 : rootsPtr + i < denPtr := by dsimp only [denPtr]; omega
    rw [hstF_ge16 _ ha1, hP_fr _ (Or.inl ha2) (Or.inl ha3)]
    exact hR_at i hi
  have hT_exp : Restart.ExportAt stF.mem (heap + 8) outEnd (S jF).T := by
    have hTV : (S jF).T.V = (S jF).G.V := rfl
    have hTn : (S jF).T.n = nG := by change (S jF).T.V.card = (S jF).G.V.card; rw [hTV]
    have hbound1 : heap + 16 + nG ≤ outEnd := by dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
    have hbound2 : heap + 16 + nG + 3 * mT ≤ outEnd := by dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
    exact exportAt_of_lists (vL := vL) (eT := eT)
      (hm8.trans hTn.symm) hm9 hm10 hm11
      (by omega) hvL_nd (fun v => by rw [hvL_mem, ← hS_G, ← hTV]) hvL_final
      heT_len heT_nd heT_in heT_cov heT_final
      (by omega) (by omega) (by omega) hbound1 hbound2
  have hF_exp : Restart.ExportAt stF.mem (heap + 12) outEnd (S jF).RF.F := by
    have hFV : (S jF).RF.F.V = (S jF).G.V := (compLSF_RF_isRSF hIj).2.1
    have hFn : (S jF).RF.F.n = nG := by change (S jF).RF.F.V.card = (S jF).G.V.card; rw [hFV]
    have hbound1 : heap + 16 + nG ≤ outEnd := by dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
    have hbound2 : heap + 16 + nG + 3 * mT + 3 * mF ≤ outEnd := by dsimp only [outEnd, denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
    exact exportAt_of_lists (vL := vL) (eT := eF)
      (hm12.trans hFn.symm) hm13 hm14 hm15
      (by omega) hvL_nd (fun v => by rw [hvL_mem, ← hS_G, ← hFV]) hvL_final
      heF_len heF_nd heF_in heF_cov heF_final
      (by omega) (by omega) (by omega) hbound1 hbound2
  -- Cost bound
  have hcost : (237 + cCp + (cT + 3) + (cF + 3) + (cR + 3) + (cP + 3)) + compPhi b x stF.mem ≤
      compExportCost k S [b, j, gPtr, heap] mem + compPhi b x mem := by
    rw [hphi_eq]
    dsimp only [compExportCost]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hj, ↓reduceDIte, hmem_Lw]
    have hmul : 35 * mG * x.L_w ≤ 40 * mG * x.L_w := Nat.mul_le_mul_right _ (by omega)
    dsimp only [jF, nG, mG, mT, mF] at hcCp hcT hcF hcR hcP hne_le_n hvL_len hnG_eq hmul ⊢
    omega
  have hnum_ge16 : heap + 16 ≤ numPtr := by dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr]; omega
  have hden_ge_num : numPtr + x.eCap * x.L_w = denPtr := rfl
  have hden_end : denPtr + x.eCap * x.L_w = outEnd := rfl
  have hR_le_out : rootsPtr + nR ≤ outEnd := by dsimp only [outEnd, denPtr, numPtr]; omega
  have hwords_lt : ∀ a, heap ≤ a → a < outEnd → stF.mem a < max (2 ^ w) (2 ^ W.h) :=
    compExport_words_lt hw0' hrep_orig.2.2.2.2.2.2.1 (lt_of_le_of_lt hout_le_sp hsp_lt)
      (by omega) (by omega) (hS_G ▸ hdgVal)
      (fun e he => (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1)
      (compLSF_RF_isRSF (hBr jF).1).2.2.2.2.2.1 (compLSF_RF_isRSF (hBr jF).1).2.1
      (compLSF_RF_isRSF (hBr jF).1).1.1 (compLSF_RF_isRSF (hBr jF).1).2.2.1
      (fun v hv => hT.hVlt v (hS_G ▸ hv)) (fun e he => hT.hElt e (hS_G ▸ he))
      (hvL_len.trans hnG_eq.symm) (fun v => by rw [hvL_mem, hS_G]) heT_len heT_in
      (fun e _ => ⟨rfl, rfl⟩) heF_len heF_in rfl hR_fs
      hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14 hm15
      hstF_ge16 hvL_final heT_final heF_final hR_final
      (fun e he => ⟨(hP_done e he).1, (hP_done e he).2.1⟩) hP_frE
      (fun a ha => hR_fr a (Or.inr ha)) (fun a ha => hF_fr a (Or.inr ha))
      (fun a ha => hT_fr a (Or.inr ha)) (fun a ha => hCp_fr a (Or.inr ha)) hz
  refine ⟨.returned outEnd, stF, 237 + cCp + (cT + 3) + (cF + 3) + (cR + 3) + (cP + 3),
    hrun_full, S, x, hrep_final, ?_, ?_, hcost, rfl, ?_⟩
  · simp only [CompExportPost, List.getD_cons_zero, List.getD_cons_succ, heapArg,
      List.getLastD_cons, List.getLastD_nil]
    refine ⟨trivial, hj, ?_⟩
    rw [hmem_Lw, hmem_eCap, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7]
    refine ⟨rfl, rfl, rfl, rfl, by omega,
      by simp only [compExportSpace, List.getD_cons_zero]; rw [hmem_vCap, hmem_eCap, hmem_Lw]; exact hout_le_sp,
      hwords_lt, hz_final, hT_exp, hF_exp,
      ⟨roots, rfl, hR_nd, hR_fs, hR_final, by omega, hR_le_out⟩,
      hTE_lt_eCap, fun e he => ?_⟩
    have helt : e < x.eCap := hT.hElt e (hS_G ▸ he)
    have he_mul : (e + 1) * x.L_w ≤ x.eCap * x.L_w := Nat.mul_le_mul_right _ helt
    have he_mul0 : e * x.L_w + x.L_w = (e + 1) * x.L_w := by ring
    have hP_e := hP_done e he
    have hNumAg : ∀ i < x.L_w, stF.mem (numPtr + e * x.L_w + i) = stP0.mem (numPtr + e * x.L_w + i) :=
      fun i _ => hstF_ge16 _ (Nat.le_trans hnum_ge16 (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    have hDenAg : ∀ i < x.L_w, stF.mem (denPtr + e * x.L_w + i) = stP0.mem (denPtr + e * x.L_w + i) :=
      fun i _ => hstF_ge16 _ (Nat.le_trans hnum_ge16 (by rw [← hden_ge_num]; omega))
    have hVN : Valid stF.mem (numPtr + e * x.L_w) W.h x.L_w := fun i hi => (hNumAg i hi).symm ▸ hP_e.1 i hi
    have hVD : Valid stF.mem (denPtr + e * x.L_w) W.h x.L_w := fun i hi => (hDenAg i hi).symm ▸ hP_e.2.1 i hi
    have hIN : intVal stF.mem (numPtr + e * x.L_w) W.h x.L_w = intVal stP0.mem (numPtr + e * x.L_w) W.h x.L_w :=
      intVal_congr hNumAg
    have hID : intVal stF.mem (denPtr + e * x.L_w) W.h x.L_w = intVal stP0.mem (denPtr + e * x.L_w) W.h x.L_w :=
      intVal_congr hDenAg
    refine ⟨Nat.le_trans hnum_ge16 (Nat.le_add_right _ _), ?_, ?_, ?_, hVN, hVD,
      hIN ▸ hP_e.2.2.1, hID ▸ hP_e.2.2.2.1, by rw [hIN, hID]; exact hP_e.2.2.2.2⟩
    · calc numPtr + (e + 1) * x.L_w ≤ numPtr + x.eCap * x.L_w := Nat.add_le_add_left he_mul _
        _ = denPtr := hden_ge_num
        _ ≤ denPtr + x.eCap * x.L_w := Nat.le_add_right _ _
    · exact Nat.le_trans hnum_ge16 (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · exact Nat.add_le_add_left he_mul denPtr
  · refine ⟨by dsimp only [Outcome.value]; omega,
      by rw [hsp_eq]; dsimp only [Outcome.value]; exact hout_le_sp,
      hz_final, fun a ha _ => hfr_all a (Or.inl ha), fun a ha => Or.inl ha⟩
  · simp only [Outcome.value, hm5, hmem_eCap, hmem_Lw]; rfl

end

end MinCostFlow.SparseCore.Program
