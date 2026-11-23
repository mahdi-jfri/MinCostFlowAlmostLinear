module

public import MinCostFlow.SparseCore.Program.CompContract

/-!
# Single-Branch Export Contract (`op 6`, `CompExportContract`)

Defines the Word-RAM contract for `op 6` (`compExportBranchProc`), which exports branch `j`'s
`T`, `RF.F`, `RF.R`, and `wstrGlobal` numerator/denominator limb tables in the exact layout
consumed by `Read.ReadInitAt` (`ReadSpec.lean`) and `CompBranchExportAt`
(`AssemblyTopIface.lean`), in strictly linear time.

Kept separate from `CompContract.lean` so modules verifying `op 0..5` do not pay extra
definitional-unfolding overhead from `op 6`'s postcondition.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- Precondition of `op 6` (single-branch export `[b, j, gPtr, heap]` for P10 init):
`j < k` and `gPtr` holds `DynGraphAt mem gPtr vCap0 eCap0 (S 0).G` below `heap`. -/
def CompExportPre (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b j gPtr heap vCap0 eCap0 : ℕ),
    args = [b, j, gPtr, heap] ∧ 16 ≤ 2 ^ w ∧ j < k ∧
    DynGraphAt mem gPtr vCap0 eCap0 (S ⟨0, hk⟩).G ∧
    gPtr + dynGraphSize vCap0 eCap0 ≤ heap

/-- Space bound of `op 6` (single-branch export): `16 + 2 * vCap + 6 * eCap + 2 * eCap * L_w`. -/
def compExportSpace (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let b := args.getD 0 0
  let vCap := mem (b + compOffVCap)
  let eCap := mem (b + compOffECap)
  let L_w := mem (b + compOffLW)
  16 + 2 * vCap + 6 * eCap + 2 * eCap * L_w

/-- Linear cost bound of `op 6` (single-branch export): strictly linear in the exported size
`G.n, T.m, F.m, G.m * L_w`, with zero dependence on `vCap` or `eCap`. -/
noncomputable def compExportCost (k : ℕ) (S : CompLSFFamily k) (args : List ℕ)
    (mem : ℕ → ℕ) : ℕ :=
  if hj : args.getD 1 0 < k then
    let cs := S ⟨args.getD 1 0, hj⟩
    let L_w := mem (args.getD 0 0 + compOffLW)
    450 * cs.G.n + 180 * cs.T.m + 100 * cs.RF.F.m + 40 * cs.G.m * L_w + 100 * cs.G.m + 500
  else 0

/-- Postcondition of `op 6` (single-branch export): writes an 8-word header
`[tD, fD, rootsPtr, nR, numPtr, denPtr, L_w, eCap]` at `[h, h + 8)` (matching `CompBranchExportAt`
and `Read.ReadInitAt`), `ExportAt` of `T` at `tD = h + 8`, `ExportAt` of `RF.F` at `fD = h + 12`,
the duplicate-free root list at `rootsPtr`, and valid positive `L_w`-limb numerator/denominator
tables for `wstrGlobal` at `numPtr`/`denPtr`, leaving `ZeroFrom mem' outEnd`. -/
def CompExportPost (W : LSFWindowImpl) (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ)
    (mem : ℕ → ℕ) (S' : CompLSFFamily k) (mem' : ℕ → ℕ) : Prop :=
  S' = S ∧ ∃ (hj : args.getD 1 0 < k),
    let b := args.getD 0 0
    let h := heapArg args
    let cs := S ⟨args.getD 1 0, hj⟩
    let L_w := mem (b + compOffLW)
    let eCap := mem (b + compOffECap)
    let tD := mem' h
    let fD := mem' (h + 1)
    let rootsPtr := mem' (h + 2)
    let nR := mem' (h + 3)
    let numPtr := mem' (h + 4)
    let denPtr := mem' (h + 5)
    let outEnd := denPtr + eCap * L_w
    tD = h + 8 ∧ fD = h + 12 ∧
    mem' (h + 6) = L_w ∧ mem' (h + 7) = eCap ∧
    h + 16 ≤ outEnd ∧ outEnd ≤ h + compExportSpace args mem ∧
    (∀ a, h ≤ a → a < outEnd → mem' a < max (2 ^ w) (2 ^ W.h)) ∧
    ZeroFrom mem' outEnd ∧
    Restart.ExportAt mem' tD outEnd cs.T ∧
    Restart.ExportAt mem' fD outEnd cs.RF.F ∧
    (∃ roots : List ℕ, roots.length = nR ∧ roots.Nodup ∧ roots.toFinset = cs.RF.R ∧
      ListAt mem' rootsPtr roots ∧ h + 16 ≤ rootsPtr ∧ rootsPtr + nR ≤ outEnd) ∧
    (∀ e ∈ cs.T.E, e < eCap) ∧
    (∀ e ∈ cs.G.E,
      h + 16 ≤ numPtr + e * L_w ∧ numPtr + (e + 1) * L_w ≤ outEnd ∧
      h + 16 ≤ denPtr + e * L_w ∧ denPtr + (e + 1) * L_w ≤ outEnd ∧
      Valid mem' (numPtr + e * L_w) W.h L_w ∧ Valid mem' (denPtr + e * L_w) W.h L_w ∧
      1 ≤ intVal mem' (numPtr + e * L_w) W.h L_w ∧
      1 ≤ intVal mem' (denPtr + e * L_w) W.h L_w ∧
      (intVal mem' (numPtr + e * L_w) W.h L_w : ℝ) /
        (intVal mem' (denPtr + e * L_w) W.h L_w : ℝ) = cs.wstrGlobal e)

/-- Full 7-operation per-component dynamic LSF data-structure specification extending `compLSFDS`
(`op 0..5`) with single-branch export (`op 6`). -/
noncomputable def compLSFDSFull (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) :
    DataStructure (CompLSFFamily k) where
  initPre := (compLSFDS W w k G₀).initPre
  initPost := (compLSFDS W w k G₀).initPost
  initCost := (compLSFDS W w k G₀).initCost
  initSpace := (compLSFDS W w k G₀).initSpace
  pre i S args mem := if i = 6 then CompExportPre w k S args mem else (compLSFDS W w k G₀).pre i S args mem
  post i S args mem S' mem' :=
    if i = 6 then CompExportPost W w k S args mem S' mem' else (compLSFDS W w k G₀).post i S args mem S' mem'
  cost i S args mem :=
    if i = 6 then compExportCost k S args mem else (compLSFDS W w k G₀).cost i S args mem
  space i S args mem :=
    if i = 6 then compExportSpace args mem else (compLSFDS W w k G₀).space i S args mem

private lemma mem_hdr16_reads (m : ℕ → ℕ) (h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    let m0 := Function.update m h v0
    let m1 := Function.update m0 (h + 1) v1
    let m2 := Function.update m1 (h + 2) v2
    let m3 := Function.update m2 (h + 3) v3
    let m4 := Function.update m3 (h + 4) v4
    let m5 := Function.update m4 (h + 5) v5
    let m6 := Function.update m5 (h + 6) v6
    let m7 := Function.update m6 (h + 7) v7
    let m8 := Function.update m7 (h + 8) v8
    let m9 := Function.update m8 (h + 9) v9
    let m10 := Function.update m9 (h + 10) v10
    let m11 := Function.update m10 (h + 11) v11
    let m12 := Function.update m11 (h + 12) v12
    let m13 := Function.update m12 (h + 13) v13
    let m14 := Function.update m13 (h + 14) v14
    let m15 := Function.update m14 (h + 15) v15
    (∀ a, a < h ∨ h + 16 ≤ a → m15 a = m a) ∧
    m15 h = v0 ∧ m15 (h + 1) = v1 ∧ m15 (h + 2) = v2 ∧ m15 (h + 3) = v3 ∧
    m15 (h + 4) = v4 ∧ m15 (h + 5) = v5 ∧ m15 (h + 6) = v6 ∧ m15 (h + 7) = v7 ∧
    m15 (h + 8) = v8 ∧ m15 (h + 9) = v9 ∧ m15 (h + 10) = v10 ∧ m15 (h + 11) = v11 ∧
    m15 (h + 12) = v12 ∧ m15 (h + 13) = v13 ∧ m15 (h + 14) = v14 ∧ m15 (h + 15) = v15 := by
  intro m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0]
    repeat rw [Function.update_of_ne (by omega)]
  all_goals
    dsimp only [m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0]
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])

/-- Stores the 16 header words of `compExportBranchProc` at `[heap .. heap + 15]` and returns
`outEnd` in 100 steps. -/
lemma compExportStoreHdr_runs {w heap eCap L_w nG vPtr tEPtr mT fEPtr mF rootsPtr nR numPtr denPtr outEnd : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hheap_w : heap + 16 < 2 ^ w)
    (hregs : st.regs 3 = heap ∧ st.regs 5 = eCap ∧ st.regs 6 = L_w ∧
      st.regs 9 = nG ∧ st.regs 13 = vPtr ∧ st.regs 14 = tEPtr ∧
      st.regs 15 = mT ∧ st.regs 16 = fEPtr ∧ st.regs 17 = mF ∧
      st.regs 18 = rootsPtr ∧ st.regs 19 = nR ∧ st.regs 20 = numPtr ∧
      st.regs 21 = denPtr ∧ st.regs 22 = outEnd) :
    ∃ stF : State,
      Runs w p ω
        (.store (.reg 3) (.bin .add (.reg 3) (.const 8)) ;;
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
         .ret (.reg 22)) st (.returned outEnd) stF 100 ∧
      (∀ a, a < heap ∨ heap + 16 ≤ a → stF.mem a = st.mem a) ∧
      stF.mem heap = heap + 8 ∧ stF.mem (heap + 1) = heap + 12 ∧
      stF.mem (heap + 2) = rootsPtr ∧ stF.mem (heap + 3) = nR ∧
      stF.mem (heap + 4) = numPtr ∧ stF.mem (heap + 5) = denPtr ∧
      stF.mem (heap + 6) = L_w ∧ stF.mem (heap + 7) = eCap ∧
      stF.mem (heap + 8) = nG ∧ stF.mem (heap + 9) = vPtr ∧
      stF.mem (heap + 10) = mT ∧ stF.mem (heap + 11) = tEPtr ∧
      stF.mem (heap + 12) = nG ∧ stF.mem (heap + 13) = vPtr ∧
      stF.mem (heap + 14) = mF ∧ stF.mem (heap + 15) = fEPtr := by
  let m0 := Function.update st.mem heap (heap + 8)
  let m1 := Function.update m0 (heap + 1) (heap + 12)
  let m2 := Function.update m1 (heap + 2) rootsPtr
  let m3 := Function.update m2 (heap + 3) nR
  let m4 := Function.update m3 (heap + 4) numPtr
  let m5 := Function.update m4 (heap + 5) denPtr
  let m6 := Function.update m5 (heap + 6) L_w
  let m7 := Function.update m6 (heap + 7) eCap
  let m8 := Function.update m7 (heap + 8) nG
  let m9 := Function.update m8 (heap + 9) vPtr
  let m10 := Function.update m9 (heap + 10) mT
  let m11 := Function.update m10 (heap + 11) tEPtr
  let m12 := Function.update m11 (heap + 12) nG
  let m13 := Function.update m12 (heap + 13) vPtr
  let m14 := Function.update m13 (heap + 14) mF
  let m15 := Function.update m14 (heap + 15) fEPtr
  let stF : State := { st with mem := m15 }
  have hstep : ∀ (off val : ℕ) (r : ℕ) (mem1 : ℕ → ℕ),
      off < 16 → st.regs r = val →
      Runs w p ω (.store (.bin .add (.reg 3) (.const off)) (.reg r))
        { st with mem := mem1 } .normal { st with mem := Function.update mem1 (heap + off) val } 5 := by
    intro off val r mem1 hoff hr
    refine runs_store_iff.mpr ⟨heap + off, val, ?_, by simp [Expr.eval, hr], rfl, rfl, by simp [Expr.size]⟩
    simp [Expr.eval, BinOp.eval, hregs.1, show off < 2 ^ w by omega, show heap + off < 2 ^ w by omega]
  have hs0 : Runs w p ω (.store (.reg 3) (.bin .add (.reg 3) (.const 8))) st .normal { st with mem := m0 } 5 :=
    runs_store_iff.mpr ⟨heap, heap + 8, by simp [Expr.eval, hregs.1],
      by simp [Expr.eval, BinOp.eval, hregs.1, show 8 < 2 ^ w by omega, show heap + 8 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.bin .add (.reg 3) (.const 12)))
      { st with mem := m0 } .normal { st with mem := m1 } 7 :=
    runs_store_iff.mpr ⟨heap + 1, heap + 12,
      by simp [Expr.eval, BinOp.eval, hregs.1, show 1 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, hregs.1, show 12 < 2 ^ w by omega, show heap + 12 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hret : Runs w p ω (.ret (.reg 22)) stF (.returned outEnd) stF 2 :=
    runs_ret_iff.mpr ⟨outEnd, by simp [stF, Expr.eval, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2], rfl, rfl, by simp [Expr.size]⟩
  have hrun : Runs w p ω _ st (.returned outEnd) stF 100 :=
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hs0,
    runs_seq_iff.mpr (Or.inr ⟨_, 7, _, hs1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 2 rootsPtr 18 m1 (by omega) hregs.2.2.2.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 3 nR 19 m2 (by omega) hregs.2.2.2.2.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 4 numPtr 20 m3 (by omega) hregs.2.2.2.2.2.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 5 denPtr 21 m4 (by omega) hregs.2.2.2.2.2.2.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 6 L_w 6 m5 (by omega) hregs.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 7 eCap 5 m6 (by omega) hregs.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 8 nG 9 m7 (by omega) hregs.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 9 vPtr 13 m8 (by omega) hregs.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 10 mT 15 m9 (by omega) hregs.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 11 tEPtr 14 m10 (by omega) hregs.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 12 nG 9 m11 (by omega) hregs.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 13 vPtr 13 m12 (by omega) hregs.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hstep 14 mF 17 m13 (by omega) hregs.2.2.2.2.2.2.2.2.1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, 2, hstep 15 fEPtr 16 m14 (by omega) hregs.2.2.2.2.2.2.2.1,
      hret, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  exact ⟨stF, hrun, mem_hdr16_reads st.mem heap (heap + 8) (heap + 12) rootsPtr nR numPtr denPtr L_w eCap
    nG vPtr mT tEPtr nG vPtr mF fEPtr⟩

/-- Executes the 10-assignment prefix of `compExportBranchProc` on `startState [b, j, gPtr, heap] mem pos`,
loading header and `DynGraphAt` fields into `regs 4..13` in 64 steps. -/
lemma compExportPrefix_runs {w b j gPtr heap k eCap L_w vCap0 eCap0 nG mG pos : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (_hw16 : 16 ≤ 2 ^ w) (h16w : 16 < 2 ^ w)
    (hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w)
    (hdg_w : gPtr + dynGraphSize vCap0 eCap0 < 2 ^ w)
    (hheap16 : heap + 16 < 2 ^ w)
    (h_k : mem (b + compOffK) = k) (h_eC : mem (b + compOffECap) = eCap)
    (h_Lw : mem (b + compOffLW) = L_w)
    (h_v0 : mem (gPtr + dgVCapOff) = vCap0) (h_e0 : mem (gPtr + dgECapOff) = eCap0)
    (h_nG : mem (gPtr + dgNOff) = nG) (h_mG : mem (gPtr + dgMOff) = mG) :
    let st0 := startState [b, j, gPtr, heap] mem pos
    let vListPtr := dgVListBase gPtr vCap0
    let eListPtr := dgEListBase gPtr vCap0 eCap0
    let vPtr := heap + 16
    ∃ st1 : State,
      st1.mem = mem ∧ st1.pos = pos ∧
      (∀ C : Stmt, ∀ o stF cC,
        Runs w p ω C st1 o stF cC →
        Runs w p ω
          (.assign 4 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
           .assign 5 (.load (.bin .add (.reg 0) (.const compOffECap))) ;;
           .assign 6 (.load (.bin .add (.reg 0) (.const compOffLW))) ;;
           .assign 7 (.load (.bin .add (.reg 2) (.const dgVCapOff))) ;;
           .assign 8 (.load (.bin .add (.reg 2) (.const dgECapOff))) ;;
           .assign 9 (.load (.bin .add (.reg 2) (.const dgNOff))) ;;
           .assign 10 (.load (.bin .add (.reg 2) (.const dgMOff))) ;;
           .assign 11 (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 7)) ;;
           .assign 12 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
             (.bin .mul (.const 7) (.reg 7))) (.reg 8)) ;;
           .assign 13 (.bin .add (.reg 3) (.const 16)) ;; C) st0 o stF (65 + cC)) ∧
      st1.regs 0 = b ∧ st1.regs 1 = j ∧ st1.regs 2 = gPtr ∧ st1.regs 3 = heap ∧
      st1.regs 4 = k ∧ st1.regs 5 = eCap ∧ st1.regs 6 = L_w ∧
      st1.regs 7 = vCap0 ∧ st1.regs 8 = eCap0 ∧ st1.regs 9 = nG ∧
      st1.regs 10 = mG ∧ st1.regs 11 = vListPtr ∧ st1.regs 12 = eListPtr ∧ st1.regs 13 = vPtr := by
  intro st0 vListPtr eListPtr vPtr
  have hdg_sz : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  let r1 := Function.update st0.regs 4 k
  let r2 := Function.update r1 5 eCap
  let r3 := Function.update r2 6 L_w
  let r4 := Function.update r3 7 vCap0
  let r5 := Function.update r4 8 eCap0
  let r6 := Function.update r5 9 nG
  let r7 := Function.update r6 10 mG
  let r8 := Function.update r7 11 vListPtr
  let r9 := Function.update r8 12 eListPtr
  let r10 := Function.update r9 13 vPtr
  let st1 : State := { st0 with regs := r10 }
  have hp1 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const compOffK))))
      st0 .normal { st0 with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      have := hb_off compOffK (by decide); simp [st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) h_k,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffECap))))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 5 :=
    runs_assign_iff.mpr ⟨eCap, Expr.eval_load_of_eq (by
      have := hb_off compOffECap (by decide); simp [r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) h_eC,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffLW))))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffLW (by decide); simp [r2, r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) h_Lw,
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 2) (.const dgVCapOff))))
      { st0 with regs := r3 } .normal { st0 with regs := r4 } 5 :=
    runs_assign_iff.mpr ⟨vCap0, Expr.eval_load_of_eq (by
      simp [r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, dgVCapOff, show (0 : ℕ) < 2 ^ w by omega,
        show gPtr < 2 ^ w by omega]) h_v0, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 2) (.const dgECapOff))))
      { st0 with regs := r4 } .normal { st0 with regs := r5 } 5 :=
    runs_assign_iff.mpr ⟨eCap0, Expr.eval_load_of_eq (by
      simp [r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, dgECapOff, show 1 < 2 ^ w by omega,
        show gPtr + 1 < 2 ^ w by omega]) h_e0, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 2) (.const dgNOff))))
      { st0 with regs := r5 } .normal { st0 with regs := r6 } 5 :=
    runs_assign_iff.mpr ⟨nG, Expr.eval_load_of_eq (by
      simp [r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, dgNOff, show 2 < 2 ^ w by omega,
        show gPtr + 2 < 2 ^ w by omega]) h_nG, rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 2) (.const dgMOff))))
      { st0 with regs := r6 } .normal { st0 with regs := r7 } 5 :=
    runs_assign_iff.mpr ⟨mG, Expr.eval_load_of_eq (by
      simp [r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, dgMOff, show 3 < 2 ^ w by omega,
        show gPtr + 3 < 2 ^ w by omega]) h_mG, rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 7)))
      { st0 with regs := r7 } .normal { st0 with regs := r8 } 6 :=
    runs_assign_iff.mpr ⟨vListPtr, by
      simp [r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, vListPtr, dgVListBase,
        show 4 < 2 ^ w by omega, show gPtr + 4 < 2 ^ w by omega, show gPtr + 4 + vCap0 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp9 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
      (.bin .mul (.const 7) (.reg 7))) (.reg 8)))
      { st0 with regs := r8 } .normal { st0 with regs := r9 } 10 :=
    runs_assign_iff.mpr ⟨eListPtr, by
      simp [r8, r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, eListPtr, dgEListBase,
        show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show gPtr + 4 < 2 ^ w by omega,
        show 7 * vCap0 < 2 ^ w by omega, show gPtr + 4 + 7 * vCap0 < 2 ^ w by omega,
        show gPtr + 4 + 7 * vCap0 + eCap0 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp10 : Runs w p ω (.assign 13 (.bin .add (.reg 3) (.const 16)))
      { st0 with regs := r9 } .normal st1 4 :=
    runs_assign_iff.mpr ⟨vPtr, by
      simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, vPtr, h16w, hheap16],
      rfl, rfl, by simp [Expr.size]⟩
  refine ⟨st1, rfl, rfl, fun C o stF cC hC => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp1,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp2,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp3,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp4,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp5,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp6,
      runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp7,
      runs_seq_iff.mpr (Or.inr ⟨_, 6, _, hp8,
      runs_seq_iff.mpr (Or.inr ⟨_, 10, _, hp9,
      runs_seq_iff.mpr (Or.inr ⟨st1, 4, cC, hp10, hC, rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  all_goals simp [st1, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState]

/-- Every word written in `[heap, outEnd)` by `compExportBranchProc` is bounded by
`max (2 ^ w) (2 ^ hBit)` (which equals `2 ^ w` when `hBit = 4` and `16 < 2 ^ w`). -/
lemma compExport_words_lt {w hBit heap nG mT mF nR vCap eCap L_w : ℕ}
    {mem stF_mem stP0_mem stR0_mem stF0_mem stT0_mem stCp0_mem : ℕ → ℕ}
    {G T F : MGraph} {R_set : Finset ℕ} {vL roots : List ℕ} {eT eF : List (ℕ × ℕ × ℕ)}
    (hw0' : 0 < 2 ^ w) (heCap1 : 1 ≤ eCap)
    (hout_lt : heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + eCap * L_w < 2 ^ w)
    (hvCap_w : vCap < 2 ^ w) (heCap_w : eCap < 2 ^ w)
    (hG_val : G.IsValid) (hT_sub : T.E ⊆ G.E) (hF_sub : F.E ⊆ G.E) (hFV : F.V = G.V)
    (hF_val : F.IsValid) (hR_sub : R_set ⊆ G.V)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hvL_len : vL.length = nG) (hvL_mem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (heT_len : eT.length = mT) (heT_in : ∀ t ∈ eT, t.1 ∈ T.E ∧ t.2.1 = T.tail t.1 ∧ t.2.2 = T.head t.1)
    (hT_th : ∀ e ∈ T.E, T.tail e = G.tail e ∧ T.head e = G.head e)
    (heF_len : eF.length = mF) (heF_in : ∀ t ∈ eF, t.1 ∈ F.E ∧ t.2.1 = F.tail t.1 ∧ t.2.2 = F.head t.1)
    (hR_len : roots.length = nR) (hR_fs : roots.toFinset = R_set)
    (hm0 : stF_mem heap = heap + 8) (hm1 : stF_mem (heap + 1) = heap + 12)
    (hm2 : stF_mem (heap + 2) = heap + 16 + nG + 3 * mT + 3 * mF) (hm3 : stF_mem (heap + 3) = nR)
    (hm4 : stF_mem (heap + 4) = heap + 16 + nG + 3 * mT + 3 * mF + nR)
    (hm5 : stF_mem (heap + 5) = heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w)
    (hm6 : stF_mem (heap + 6) = L_w) (hm7 : stF_mem (heap + 7) = eCap)
    (hm8 : stF_mem (heap + 8) = nG) (hm9 : stF_mem (heap + 9) = heap + 16)
    (hm10 : stF_mem (heap + 10) = mT) (hm11 : stF_mem (heap + 11) = heap + 16 + nG)
    (hm12 : stF_mem (heap + 12) = nG) (hm13 : stF_mem (heap + 13) = heap + 16)
    (hm14 : stF_mem (heap + 14) = mF) (hm15 : stF_mem (heap + 15) = heap + 16 + nG + 3 * mT)
    (hstF_ge16 : ∀ a, heap + 16 ≤ a → stF_mem a = stP0_mem a)
    (hvL_final : ListAt stF_mem (heap + 16) vL)
    (heT_final : ∀ i (hi : i < eT.length),
      stF_mem (heap + 16 + nG + 3 * i) = eT[i].1 ∧
      stF_mem (heap + 16 + nG + 3 * i + 1) = eT[i].2.1 ∧
      stF_mem (heap + 16 + nG + 3 * i + 2) = eT[i].2.2)
    (heF_final : ∀ i (hi : i < eF.length),
      stF_mem (heap + 16 + nG + 3 * mT + 3 * i) = eF[i].1 ∧
      stF_mem (heap + 16 + nG + 3 * mT + 3 * i + 1) = eF[i].2.1 ∧
      stF_mem (heap + 16 + nG + 3 * mT + 3 * i + 2) = eF[i].2.2)
    (hR_final : ListAt stF_mem (heap + 16 + nG + 3 * mT + 3 * mF) roots)
    (hP_done : ∀ e ∈ G.E,
      Valid stP0_mem (heap + 16 + nG + 3 * mT + 3 * mF + nR + e * L_w) hBit L_w ∧
      Valid stP0_mem (heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + e * L_w) hBit L_w)
    (hP_frE : ∀ a, (∀ e ∈ G.E,
      (a < heap + 16 + nG + 3 * mT + 3 * mF + nR + e * L_w ∨
        heap + 16 + nG + 3 * mT + 3 * mF + nR + e * L_w + L_w ≤ a) ∧
      (a < heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + e * L_w ∨
        heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + e * L_w + L_w ≤ a)) →
      stP0_mem a = stR0_mem a)
    (hR_fr : ∀ a, heap + 16 + nG + 3 * mT + 3 * mF + nR ≤ a → stR0_mem a = stF0_mem a)
    (hF_fr : ∀ a, heap + 16 + nG + 3 * mT + 3 * mF ≤ a → stF0_mem a = stT0_mem a)
    (hT_fr : ∀ a, heap + 16 + nG + 3 * mT ≤ a → stT0_mem a = stCp0_mem a)
    (hCp_fr : ∀ a, heap + 16 + nG ≤ a → stCp0_mem a = mem a)
    (hz : ZeroFrom mem heap) :
    ∀ a, heap ≤ a → a < heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + eCap * L_w →
      stF_mem a < max (2 ^ w) (2 ^ hBit) := by
  set vPtr := heap + 16
  set tEPtr := vPtr + nG
  set fEPtr := tEPtr + 3 * mT
  set rootsPtr := fEPtr + 3 * mF
  set numPtr := rootsPtr + nR
  set denPtr := numPtr + eCap * L_w
  set outEnd := denPtr + eCap * L_w
  have hLw_w : L_w < 2 ^ w :=
    lt_of_le_of_lt ((Nat.le_mul_of_pos_left L_w heCap1).trans (by dsimp only [outEnd, denPtr]; omega)) hout_lt
  have hlt_max : ∀ z, z < 2 ^ w → z < max (2 ^ w) (2 ^ hBit) := fun z hz => lt_of_lt_of_le hz (le_max_left _ _)
  intro a ha1 ha2
  by_cases h16 : a < vPtr
  · apply hlt_max
    have hc : a = heap ∨ a = heap + 1 ∨ a = heap + 2 ∨ a = heap + 3 ∨ a = heap + 4 ∨ a = heap + 5 ∨
        a = heap + 6 ∨ a = heap + 7 ∨ a = heap + 8 ∨ a = heap + 9 ∨ a = heap + 10 ∨ a = heap + 11 ∨
        a = heap + 12 ∨ a = heap + 13 ∨ a = heap + 14 ∨ a = heap + 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | (rw [hm0]; omega) | (rw [hm1]; omega) | (rw [hm2]; omega) | (rw [hm3]; omega) |
      (rw [hm4]; omega) | (rw [hm5]; omega) | (rw [hm6]; exact hLw_w) | (rw [hm7]; exact heCap_w) |
      (rw [hm8]; omega) | (rw [hm9]; omega) | (rw [hm10]; omega) | (rw [hm11]; omega) |
      (rw [hm12]; omega) | (rw [hm13]; omega) | (rw [hm14]; omega) | (rw [hm15]; omega)
  · clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14 hm15
    by_cases hV : a < tEPtr
    · have hi : a - vPtr < vL.length := by rw [hvL_len]; omega
      have heq := hvL_final (a - vPtr) hi
      rw [show heap + 16 + (a - vPtr) = a by dsimp only [vPtr]; omega] at heq
      exact hlt_max _ (by rw [heq]; exact lt_trans (hVlt _ ((hvL_mem _).mp (List.getElem_mem hi))) hvCap_w)
    · by_cases hET : a < fEPtr
      · have hi : (a - tEPtr) / 3 < eT.length := by rw [heT_len]; exact Nat.div_lt_of_lt_mul (by omega)
        have hdm : 3 * ((a - tEPtr) / 3) + (a - tEPtr) % 3 = a - tEPtr := Nat.div_add_mod (a - tEPtr) 3
        have hmod_lt : (a - tEPtr) % 3 < 3 := Nat.mod_lt _ (by decide)
        have ht := heT_final ((a - tEPtr) / 3) hi; have hmem := heT_in _ (List.getElem_mem hi)
        have hE_G : eT[(a - tEPtr) / 3].1 ∈ G.E := hT_sub hmem.1
        apply hlt_max; rcases (show (a - tEPtr) % 3 = 0 ∨ (a - tEPtr) % 3 = 1 ∨ (a - tEPtr) % 3 = 2 by omega) with hm | hm | hm
        · rw [show a = heap + 16 + nG + 3 * ((a - tEPtr) / 3) by dsimp only [tEPtr, vPtr] at hV hdm ⊢; omega, ht.1]
          exact lt_trans (hElt _ hE_G) heCap_w
        · rw [show a = heap + 16 + nG + 3 * ((a - tEPtr) / 3) + 1 by dsimp only [tEPtr, vPtr] at hV hdm ⊢; omega,
            ht.2.1, hmem.2.1, (hT_th _ hmem.1).1]
          exact lt_trans (hVlt _ (hG_val _ hE_G).1) hvCap_w
        · rw [show a = heap + 16 + nG + 3 * ((a - tEPtr) / 3) + 2 by dsimp only [tEPtr, vPtr] at hV hdm ⊢; omega,
            ht.2.2, hmem.2.2, (hT_th _ hmem.1).2]
          exact lt_trans (hVlt _ (hG_val _ hE_G).2) hvCap_w
      · by_cases hEF : a < rootsPtr
        · have hi : (a - fEPtr) / 3 < eF.length := by rw [heF_len]; exact Nat.div_lt_of_lt_mul (by omega)
          have hdm : 3 * ((a - fEPtr) / 3) + (a - fEPtr) % 3 = a - fEPtr := Nat.div_add_mod (a - fEPtr) 3
          have hmod_lt : (a - fEPtr) % 3 < 3 := Nat.mod_lt _ (by decide)
          have hf := heF_final ((a - fEPtr) / 3) hi; have hmem := heF_in _ (List.getElem_mem hi)
          have hE_G : eF[(a - fEPtr) / 3].1 ∈ G.E := hF_sub hmem.1
          apply hlt_max; rcases (show (a - fEPtr) % 3 = 0 ∨ (a - fEPtr) % 3 = 1 ∨ (a - fEPtr) % 3 = 2 by omega) with hm | hm | hm
          · rw [show a = heap + 16 + nG + 3 * mT + 3 * ((a - fEPtr) / 3) by dsimp only [fEPtr, tEPtr, vPtr] at hET hdm ⊢; omega, hf.1]
            exact lt_trans (hElt _ hE_G) heCap_w
          · rw [show a = heap + 16 + nG + 3 * mT + 3 * ((a - fEPtr) / 3) + 1 by dsimp only [fEPtr, tEPtr, vPtr] at hET hdm ⊢; omega,
              hf.2.1, hmem.2.1]
            exact lt_trans (hVlt _ (hFV ▸ (hF_val _ hmem.1).1)) hvCap_w
          · rw [show a = heap + 16 + nG + 3 * mT + 3 * ((a - fEPtr) / 3) + 2 by dsimp only [fEPtr, tEPtr, vPtr] at hET hdm ⊢; omega,
              hf.2.2, hmem.2.2]
            exact lt_trans (hVlt _ (hFV ▸ (hF_val _ hmem.1).2)) hvCap_w
        · by_cases hRt : a < numPtr
          · have hi : a - rootsPtr < roots.length := by rw [hR_len]; omega
            have heq := hR_final (a - rootsPtr) hi
            rw [show heap + 16 + nG + 3 * mT + 3 * mF + (a - rootsPtr) = a by dsimp only [rootsPtr, fEPtr, tEPtr, vPtr]; omega] at heq
            have hrv : roots[a - rootsPtr] ∈ R_set := by rw [← hR_fs]; exact List.mem_toFinset.mpr (List.getElem_mem hi)
            exact hlt_max _ (by rw [heq]; exact lt_trans (hVlt _ (hR_sub hrv)) hvCap_w)
          · by_cases hHit : ∃ e ∈ G.E,
                (numPtr + e * L_w ≤ a ∧ a < numPtr + e * L_w + L_w) ∨
                (denPtr + e * L_w ≤ a ∧ a < denPtr + e * L_w + L_w)
            · obtain ⟨e, he, hN | hD⟩ := hHit
              · have hV1 := (hP_done e he).1 (a - (numPtr + e * L_w)) (by omega)
                rw [hstF_ge16 a (by omega)]
                rw [show heap + 16 + nG + 3 * mT + 3 * mF + nR + e * L_w + (a - (numPtr + e * L_w)) = a by
                  dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hN ⊢; omega] at hV1
                exact lt_of_lt_of_le hV1 (le_max_right _ _)
              · have hV2 := (hP_done e he).2 (a - (denPtr + e * L_w)) (by omega)
                rw [hstF_ge16 a (by omega)]
                rw [show heap + 16 + nG + 3 * mT + 3 * mF + nR + eCap * L_w + e * L_w + (a - (denPtr + e * L_w)) = a by
                  dsimp only [denPtr, numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hD ⊢; omega] at hV2
                exact lt_of_lt_of_le hV2 (le_max_right _ _)
            · push Not at hHit
              rw [hstF_ge16 a (by omega),
                  hP_frE a fun e he => ⟨(le_or_gt _ _).symm.imp_right (fun h1 => (hHit e he).1 h1),
                    (le_or_gt _ _).symm.imp_right (fun h1 => (hHit e he).2 h1)⟩,
                  hR_fr a (by dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hRt; omega),
                  hF_fr a (by dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hRt; omega),
                  hT_fr a (by dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hRt; omega),
                  hCp_fr a (by dsimp only [numPtr, rootsPtr, fEPtr, tEPtr, vPtr] at hRt; omega),
                  hz a ha1]
              exact hlt_max 0 hw0'

end

end MinCostFlow.SparseCore.Program
