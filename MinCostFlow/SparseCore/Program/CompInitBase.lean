module

public import MinCostFlow.SparseCore.Program.CompContract
public import MinCostFlow.SparseCore.Program.CompInitBfs
import MinCostFlow.DynSpanner.Program.DynGraphInit
import WordRAM.Tactic

/-!
# Initialization Procedure Definitions and Invariants (`CompInitBase`)

Defines `compInitProc` (`init` of `compLSFDS`), its sub-statements (`compInitEdgefulStmt`,
`compInitIsoStmt`, `compInitLoop`), determinism (`compInitProc_noRand`), the isolated vs.
edgeful criterion (`incHead_eq_zero_iff_iso`), and the register/memory invariants shared by
`CompInitEdgeful`, `CompInitLoop`, and `CompInitProcs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Initialization procedure body -/

/-- Edgeful-component branch of `compInitLoop`: runs BFS, builds `DynGraphAt`, and calls
P3's window initializer `bWinInit`. -/
def compInitEdgefulStmt (bBfs bDgInit bWinInit : ℕ) : Stmt :=
  .call 41 bBfs
      [.reg 0, .reg 29, .reg 16, .reg 21, .reg 22, .reg 30, .reg 31, .reg 37, .reg 33,
       .bin .add (.reg 20) (.reg 33)] ;;
  .assign 42 (.load (.bin .add (.reg 20) (.reg 33))) ;;
  .store (.bin .add (.reg 17) (.reg 33)) (.const 1) ;;
  .store (.bin .add (.reg 18) (.reg 33)) (.reg 34) ;;
  .store (.bin .add (.reg 19) (.reg 33)) (.reg 41) ;;
  .call 43 bDgInit
      [.reg 32, .reg 6, .reg 7, .reg 41, .reg 30, .reg 42, .reg 31] ;;
  .assign 44 (.bin .add (.reg 28) (.bin .mul (.reg 34) (.reg 4))) ;;
  .assign 45 (.bin .add (.reg 32) (.reg 36)) ;;
  .call 32 bWinInit
      [.reg 32, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 44, .reg 45] ;;
  .assign 34 (.bin .add (.reg 34) (.const 1)) ;;
  .assign 33 (.bin .add (.reg 33) (.const 1))

/-- Isolated-component branch of `compInitLoop`: records `{v}` in `O(1)` with no window and no
initializer call. -/
def compInitIsoStmt : Stmt :=
  .store (.bin .add (.reg 29) (.reg 37)) (.const 1) ;;
  .store (.bin .add (.reg 16) (.reg 37)) (.reg 33) ;;
  .store (.bin .add (.reg 17) (.reg 33)) (.const 0) ;;
  .store (.bin .add (.reg 19) (.reg 33)) (.const 1) ;;
  .store (.bin .add (.reg 20) (.reg 33)) (.const 0) ;;
  .assign 33 (.bin .add (.reg 33) (.const 1))

/-- Outer component-discovery loop of `compInitProc`. -/
def compInitLoop (bBfs bDgInit bWinInit : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 35) (.reg 11))
    (.assign 37 (.load (.bin .add (.reg 13) (.reg 35))) ;;
     .assign 35 (.bin .add (.reg 35) (.const 1)) ;;
     .assign 38 (.load (.bin .add (.reg 29) (.reg 37))) ;;
     .cond (.reg 38)
       .nop
       (.assign 39 (.load (.bin .add (.reg 14) (.reg 37))) ;;
        .assign 40 (.load (.bin .add (.reg 15) (.reg 39))) ;;
        .cond (.reg 40)
          (compInitEdgefulStmt bBfs bDgInit bWinInit)
          compInitIsoStmt))

/-- Setup prefix of `compInitProc` (before `compInitLoop`). -/
def compInitSetupStmt (hLimb : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 10)) ;;
  .assign 14 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 10))) ;;
  .assign 15 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 10))) ;;
  .assign 16 (.bin .add (.reg 8) (.const compHdrSize)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 6)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 6)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 6)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 6)) ;;
  .assign 21 (.bin .add (.reg 20) (.reg 6)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 7)) ;;
  .assign 23 (.bin .add (.reg 22) (.reg 7)) ;;
  .assign 24 (.bin .add (.reg 23) (.reg 7)) ;;
  .assign 25 (.bin .add (.reg 24) (.reg 7)) ;;
  .assign 26 (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 4) (.reg 6)))
    (.bin .mul (.const 6) (.reg 7))) ;;
  .assign 27 (.bin .add (.reg 26) (.reg 6)) ;;
  .assign 28 (.bin .add (.reg 27) (.reg 5)) ;;
  .assign 29 (.bin .add (.reg 28) (.bin .mul (.reg 12) (.reg 4))) ;;
  .assign 30 (.bin .add (.reg 29) (.reg 6)) ;;
  .assign 31 (.bin .add (.reg 30) (.reg 11)) ;;
  .assign 36 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 6)))
    (.bin .mul (.const 9) (.reg 7))) ;;
  .store (.bin .add (.reg 8) (.const compOffVCap)) (.reg 6) ;;
  .store (.bin .add (.reg 8) (.const compOffECap)) (.reg 7) ;;
  .store (.bin .add (.reg 8) (.const compOffK)) (.reg 4) ;;
  .store (.bin .add (.reg 8) (.const compOffLW)) (.reg 5) ;;
  .store (.bin .add (.reg 8) (.const compOffHLimb)) (.const hLimb) ;;
  .store (.bin .add (.reg 8) (.const compOffLIn)) (.reg 2) ;;
  .store (.bin .add (.reg 8) (.const compOffPFp)) (.reg 3) ;;
  .store (.bin .add (.reg 8) (.const compOffVCompPtr)) (.reg 16) ;;
  .store (.bin .add (.reg 8) (.const compOffEdgefulPtr)) (.reg 17) ;;
  .store (.bin .add (.reg 8) (.const compOffEdgefulIdxPtr)) (.reg 18) ;;
  .store (.bin .add (.reg 8) (.const compOffN0Ptr)) (.reg 19) ;;
  .store (.bin .add (.reg 8) (.const compOffM0Ptr)) (.reg 20) ;;
  .store (.bin .add (.reg 8) (.const compOffEdgeC1Ptr)) (.reg 21) ;;
  .store (.bin .add (.reg 8) (.const compOffEdgeC2Ptr)) (.reg 22) ;;
  .store (.bin .add (.reg 8) (.const compOffIsCrossPtr)) (.reg 23) ;;
  .store (.bin .add (.reg 8) (.const compOffIsInsPtr)) (.reg 24) ;;
  .store (.bin .add (.reg 8) (.const compOffGhostPtr)) (.reg 25) ;;
  .store (.bin .add (.reg 8) (.const compOffTouchMarkPtr)) (.reg 26) ;;
  .store (.bin .add (.reg 8) (.const compOffOneLimbPtr)) (.reg 27) ;;
  .store (.bin .add (.reg 8) (.const compOffHandlesPtr)) (.reg 28) ;;
  .store (.bin .add (.reg 8) (.const compOffM0Total)) (.reg 12) ;;
  .store (.reg 27) (.const 1) ;;
  .assign 32 (.bin .add (.reg 31) (.bin .mul (.const 3) (.reg 12))) ;;
  .assign 33 (.const 0) ;;
  .assign 34 (.const 0) ;;
  .assign 35 (.const 0)

/-- Initialization procedure `init` for `compLSFDS`:
`args = [g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap, heap]`.
Returns `endAddr` (`r32`), leaving a valid `CompLSFRepAt` at handle `b := heap`. -/
def compInitProc (hLimb bBfs bDgInit bWinInit : ℕ) : Stmt :=
  compInitSetupStmt hLimb ;;
  compInitLoop bBfs bDgInit bWinInit ;;
  .store (.bin .add (.reg 8) (.const compOffNumComps)) (.reg 33) ;;
  .store (.bin .add (.reg 8) (.const compOffNumEdgeful)) (.reg 34) ;;
  .store (.bin .add (.reg 8) (.const compOffEndAddr)) (.reg 32) ;;
  .ret (.reg 32)

lemma compInitProc_noRand (hLimb bBfs bDgInit bWinInit : ℕ) :
    (compInitProc hLimb bBfs bDgInit bWinInit).NoRand := by
  simp [compInitProc, compInitSetupStmt, compInitLoop, compInitEdgefulStmt, compInitIsoStmt,
    Stmt.NoRand]

/-! ## 2. Component disjointness and isolated vs. edgeful criterion -/

lemma comp_disjoint_of_ne (G₀ : MGraph) {C₁ C₂ : Finset ℕ}
    (h₁ : C₁ ∈ components G₀) (h₂ : C₂ ∈ components G₀) (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨v, hv, rfl⟩
  refine compOf_disjoint_of_not_connected fun hconn => hne ?_
  exact (compOf_eq_iff hv).mpr hconn

lemma incHead_eq_zero_iff_iso {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 v : ℕ} {G₀ : MGraph}
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hv : v ∈ G₀.V) :
    mem (dgIncHeadBase g0Ptr vCap0 + mem (dgExtToIntBase g0Ptr vCap0 + v)) = 0 ↔
      compOf G₀ v = {v} ∧ (compGraph G₀ (compOf G₀ v)).m = 0 := by
  have hG₀ := hdg.1
  have hVlt := hdg.2.1
  have hElt := hdg.2.2.1
  have hE2I := hdg.2.2.2.2.2.2.2.2.2.1
  have hEnds := hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨incL, hincFull⟩ := hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  set sv := mem (dgExtToIntBase g0Ptr vCap0 + v)
  have hsv_lt : sv < vCap0 := hVlt sv (hE2I v hv).1
  obtain ⟨hDLL, _, hinc_v⟩ := hincFull sv hsv_lt
  have hhead_nil : mem (dgIncHeadBase g0Ptr vCap0 + sv) = 0 ↔ incL sv = [] := by
    rw [hDLL.2.2.1]
    cases incL sv <;> simp
  rw [hhead_nil]
  constructor
  · intro hnil
    have hno_inc : ∀ e ∈ G₀.E, G₀.tail e ≠ v ∧ G₀.head e ≠ v := by
      intro e he
      have he_lt := hElt e he
      constructor
      · intro ht
        have h2e : 2 * e ∈ incL sv := (hinc_v (2 * e)).mpr
          ⟨by omega, by simpa using he, by
            simp only [Nat.mul_mod_right, ↓reduceIte, show 2 * e / 2 = e by omega]
            rw [(hEnds e he).1, ht]⟩
        simp [hnil] at h2e
      · intro hh
        have h2e1 : 2 * e + 1 ∈ incL sv := (hinc_v (2 * e + 1)).mpr
          ⟨by omega, by rw [show (2 * e + 1) / 2 = e by omega]; exact he, by
            simp only [show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega,
              one_ne_zero, ↓reduceIte]
            rw [(hEnds e he).2, hh]⟩
        simp [hnil] at h2e1
    have hC_eq : compOf G₀ v = {v} := by
      ext u
      simp only [mem_compOf_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨_, P, hP⟩
        cases hP with
        | nil _ => rfl
        | @cons _ _ z _ hzE hsrc _ =>
          rcases z with ⟨e, dir⟩
          cases dir
          · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
            exact absurd hsrc (hno_inc e hzE).2
          · simp only [MGraph.src, ↓reduceIte] at hsrc
            exact absurd hsrc (hno_inc e hzE).1
      · rintro rfl; exact ⟨hv, connected_refl _ _⟩
    refine ⟨hC_eq, ?_⟩
    rw [hC_eq]
    change (compEdgeSet G₀ {v}).card = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [compEdgeSet, Finset.mem_filter, Finset.mem_singleton] at he
    exact (hno_inc e he.1).1 he.2
  · rintro ⟨_, hm0⟩
    by_contra hne
    rcases List.exists_cons_of_ne_nil hne with ⟨h, rest, heq⟩
    have hh_mem : h ∈ incL sv := by rw [heq]; exact List.mem_cons_self
    obtain ⟨_, heG, hslot⟩ := (hinc_v h).mp hh_mem
    set e := h / 2
    change (if h % 2 = 0 then mem (dgETailSlotBase g0Ptr vCap0 eCap0 + e)
      else mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + e)) = sv at hslot
    have heC : e ∈ compEdgeSet G₀ (compOf G₀ v) := by
      rw [compEdgeSet, Finset.mem_filter]; refine ⟨heG, ?_⟩
      by_cases hp : h % 2 = 0
      · have hs' : mem (dgETailSlotBase g0Ptr vCap0 eCap0 + e) = sv := by simpa [hp] using hslot
        have ht_eq : G₀.tail e = v := by
          have h1 := (hE2I _ (hG₀ e heG).1).2
          rw [← (hEnds e heG).1, hs'] at h1
          exact h1.symm.trans (hE2I v hv).2
        rw [ht_eq]; exact self_mem_compOf hv
      · have hs' : mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + e) = sv := by simpa [hp] using hslot
        have hh_eq : G₀.head e = v := by
          have h1 := (hE2I _ (hG₀ e heG).2).2
          rw [← (hEnds e heG).2, hs'] at h1
          exact h1.symm.trans (hE2I v hv).2
        exact mem_compOf_iff.mpr ⟨(hG₀ e heG).1,
          hh_eq ▸ connected_symm (connected_of_edge heG)⟩
    have hpos : 0 < (compGraph G₀ (compOf G₀ v)).m := Finset.card_pos.mpr ⟨e, heC⟩
    omega

/-! ## 3. Loop context, register invariant, and memory invariant -/

/-- Register invariant preserved across iterations of `compInitLoop`. -/
structure InitRegsOK (g0Ptr lenArr L_in P_fp k L_w vCap eCap b vCap0 n0 m0 : ℕ)
    (r : ℕ → ℕ) : Prop where
  r0 : r 0 = g0Ptr
  r1 : r 1 = lenArr
  r2 : r 2 = L_in
  r3 : r 3 = P_fp
  r4 : r 4 = k
  r5 : r 5 = L_w
  r6 : r 6 = vCap
  r7 : r 7 = eCap
  r8 : r 8 = b
  r10 : r 10 = vCap0
  r11 : r 11 = n0
  r12 : r 12 = m0
  r13 : r 13 = dgVListBase g0Ptr vCap0
  r14 : r 14 = dgExtToIntBase g0Ptr vCap0
  r15 : r 15 = dgIncHeadBase g0Ptr vCap0
  r16 : r 16 = compVCompBase b
  r17 : r 17 = compEdgefulBase b vCap
  r18 : r 18 = compEdgefulIdxBase b vCap
  r19 : r 19 = compN0Base b vCap
  r20 : r 20 = compM0Base b vCap
  r21 : r 21 = compEdgeC1Base b vCap
  r22 : r 22 = compEdgeC2Base b vCap eCap
  r23 : r 23 = compIsCrossBase b vCap eCap
  r24 : r 24 = compIsInsBase b vCap eCap
  r25 : r 25 = compGhostBase b vCap eCap
  r26 : r 26 = compTouchMarkBase b vCap eCap
  r27 : r 27 = compOneLimbBase b vCap eCap
  r28 : r 28 = compHandlesBase b vCap eCap L_w
  r29 : r 29 = compTablesEnd b vCap eCap L_w m0 k
  r30 : r 30 = compTablesEnd b vCap eCap L_w m0 k + vCap
  r31 : r 31 = compTablesEnd b vCap eCap L_w m0 k + vCap + n0
  r36 : r 36 = dynGraphSize vCap eCap

lemma InitRegsOK.update_mut {g0Ptr lenArr L_in P_fp k L_w vCap eCap b vCap0 n0 m0 idx val : ℕ}
    {r : ℕ → ℕ}
    (hR : InitRegsOK g0Ptr lenArr L_in P_fp k L_w vCap eCap b vCap0 n0 m0 r)
    (hidx : (32 ≤ idx ∧ idx ≤ 35) ∨ 37 ≤ idx) :
    InitRegsOK g0Ptr lenArr L_in P_fp k L_w vCap eCap b vCap0 n0 m0 (Function.update r idx val) where
  r0 := by rw [Function.update_of_ne (by omega)]; exact hR.r0
  r1 := by rw [Function.update_of_ne (by omega)]; exact hR.r1
  r2 := by rw [Function.update_of_ne (by omega)]; exact hR.r2
  r3 := by rw [Function.update_of_ne (by omega)]; exact hR.r3
  r4 := by rw [Function.update_of_ne (by omega)]; exact hR.r4
  r5 := by rw [Function.update_of_ne (by omega)]; exact hR.r5
  r6 := by rw [Function.update_of_ne (by omega)]; exact hR.r6
  r7 := by rw [Function.update_of_ne (by omega)]; exact hR.r7
  r8 := by rw [Function.update_of_ne (by omega)]; exact hR.r8
  r10 := by rw [Function.update_of_ne (by omega)]; exact hR.r10
  r11 := by rw [Function.update_of_ne (by omega)]; exact hR.r11
  r12 := by rw [Function.update_of_ne (by omega)]; exact hR.r12
  r13 := by rw [Function.update_of_ne (by omega)]; exact hR.r13
  r14 := by rw [Function.update_of_ne (by omega)]; exact hR.r14
  r15 := by rw [Function.update_of_ne (by omega)]; exact hR.r15
  r16 := by rw [Function.update_of_ne (by omega)]; exact hR.r16
  r17 := by rw [Function.update_of_ne (by omega)]; exact hR.r17
  r18 := by rw [Function.update_of_ne (by omega)]; exact hR.r18
  r19 := by rw [Function.update_of_ne (by omega)]; exact hR.r19
  r20 := by rw [Function.update_of_ne (by omega)]; exact hR.r20
  r21 := by rw [Function.update_of_ne (by omega)]; exact hR.r21
  r22 := by rw [Function.update_of_ne (by omega)]; exact hR.r22
  r23 := by rw [Function.update_of_ne (by omega)]; exact hR.r23
  r24 := by rw [Function.update_of_ne (by omega)]; exact hR.r24
  r25 := by rw [Function.update_of_ne (by omega)]; exact hR.r25
  r26 := by rw [Function.update_of_ne (by omega)]; exact hR.r26
  r27 := by rw [Function.update_of_ne (by omega)]; exact hR.r27
  r28 := by rw [Function.update_of_ne (by omega)]; exact hR.r28
  r29 := by rw [Function.update_of_ne (by omega)]; exact hR.r29
  r30 := by rw [Function.update_of_ne (by omega)]; exact hR.r30
  r31 := by rw [Function.update_of_ne (by omega)]; exact hR.r31
  r36 := by rw [Function.update_of_ne (by omega)]; exact hR.r36

/-- Static context for `compInitEdgeful_runs` and `compInitLoop_runs`. -/
structure InitCtx (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) (p : Program) (mem0 : ℕ → ℕ) where
  bBfs : ℕ
  bDgInit : ℕ
  bWin : ℕ
  g0Ptr : ℕ
  vCap0 : ℕ
  eCap0 : ℕ
  lenArr : ℕ
  L_w : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  vL : List ℕ
  hk : 1 ≤ k
  hLw : 1 ≤ L_w
  h2h : 2 ≤ W.h * L_w
  hHw : W.h < 2 ^ w
  heCap : 1 ≤ eCap
  hw16 : 16 ≤ 2 ^ w
  hG₀ : G₀.IsValid
  hV₀ : G₀.V.Nonempty
  hdg : DynGraphAt mem0 g0Ptr vCap0 eCap0 G₀
  hvL_len : vL.length = G₀.n
  hvL_nd : vL.Nodup
  hvL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V
  hvL_at : ListAt mem0 (dgVListBase g0Ptr vCap0) vL
  hvCap_le : vCap0 ≤ vCap
  heCap_le : eCap0 ≤ eCap
  hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ b
  hlen_le : lenArr + eCap * W.L_in ≤ b
  hLen : ∀ e ∈ G₀.E, Valid mem0 (lenArr + e * W.L_in) W.h W.L_in ∧
    0 < fixVal mem0 (lenArr + e * W.L_in) W.h W.L_in W.P_fp
  hWinPre : ∀ C ∈ edgefulComps G₀, W.winPre w k L_w vCap eCap (compGraph G₀ C)
  hargs : ∀ a ∈ [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b], a < 2 ^ w
  hz0 : ZeroFrom mem0 b
  hsp : b + compInitSpace W k G₀ [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, b] < 2 ^ w
  hpBfs : p.procs[bBfs]? = some compBfsCompProc
  hpDg : ∀ (G : MGraph) (vLs : List ℕ) (eLs : List (ℕ × ℕ × ℕ)),
    MeetsContract w p bDgInit (dgInitFromListsContract w vCap eCap G vLs eLs)
  hpWin : p.HasAt bWin (W.procs bWin)

/-- Effective edge-length function passed to `W.winInit_runs`, equal to `safeLen G₀ (compReadLen ...)`. -/
noncomputable def InitCtx.ell {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} (ctx : InitCtx W w k G₀ p mem0) : ℕ → ℝ :=
  safeLen G₀ (compReadLen mem0 ctx.lenArr W.h W.L_in W.P_fp G₀)

/-- Start of the dynamic per-component heap (immediately after the scratch region). -/
def InitCtx.heap0 {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program} {mem0 : ℕ → ℕ}
    (ctx : InitCtx W w k G₀ p mem0) : ℕ :=
  compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n + 3 * G₀.m

lemma InitCtx.hsp_lt {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program} {mem0 : ℕ → ℕ}
    (ctx : InitCtx W w k G₀ p mem0) :
    ctx.heap0 + (edgefulComps G₀).sum (fun C =>
      dynGraphSize ctx.vCap ctx.eCap +
        W.winSpace k ctx.L_w ctx.vCap ctx.eCap (compGraph G₀ C).n (compGraph G₀ C).m) < 2 ^ w := by
  have h := ctx.hsp
  simp only [compInitSpace, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at h
  dsimp only [InitCtx.heap0, compTablesEnd, compHandlesBase]
  omega

/-- Memory invariant preserved across iterations of `compInitLoop`. -/
def InitMemInv {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program} {mem0 : ℕ → ℕ}
    (ctx : InitCtx W w k G₀ p mem0)
    (mem : ℕ → ℕ) (curHeap : ℕ)
    (comps : List (Finset ℕ)) (efIdx : List ℕ)
    (winH : ℕ → ℕ → ℕ) (winX : ℕ → ℕ → LSFConcrete) : Prop :=
  let b := ctx.b
  let vCap := ctx.vCap
  let eCap := ctx.eCap
  let L_w := ctx.L_w
  let visBase := compTablesEnd b vCap eCap L_w G₀.m k
  (∀ a < b, mem a = mem0 a) ∧
  (mem (b + compOffVCap) = vCap ∧ mem (b + compOffECap) = eCap ∧ mem (b + compOffK) = k ∧
   mem (b + compOffLW) = L_w ∧ mem (b + compOffHLimb) = W.h ∧ mem (b + compOffLIn) = W.L_in ∧
   mem (b + compOffPFp) = W.P_fp ∧ mem (b + compOffVCompPtr) = compVCompBase b ∧
   mem (b + compOffEdgefulPtr) = compEdgefulBase b vCap ∧
   mem (b + compOffEdgefulIdxPtr) = compEdgefulIdxBase b vCap ∧
   mem (b + compOffN0Ptr) = compN0Base b vCap ∧
   mem (b + compOffM0Ptr) = compM0Base b vCap ∧
   mem (b + compOffEdgeC1Ptr) = compEdgeC1Base b vCap ∧
   mem (b + compOffEdgeC2Ptr) = compEdgeC2Base b vCap eCap ∧
   mem (b + compOffIsCrossPtr) = compIsCrossBase b vCap eCap ∧
   mem (b + compOffIsInsPtr) = compIsInsBase b vCap eCap ∧
   mem (b + compOffGhostPtr) = compGhostBase b vCap eCap ∧
   mem (b + compOffTouchMarkPtr) = compTouchMarkBase b vCap eCap ∧
   mem (b + compOffOneLimbPtr) = compOneLimbBase b vCap eCap ∧
   mem (b + compOffHandlesPtr) = compHandlesBase b vCap eCap L_w ∧
   mem (b + compOffM0Total) = G₀.m) ∧
  (∀ a, compIsCrossBase b vCap eCap ≤ a → a < compOneLimbBase b vCap eCap → mem a = 0) ∧
  (mem (compOneLimbBase b vCap eCap) = 1 ∧
   ∀ t, 1 ≤ t → t < L_w → mem (compOneLimbBase b vCap eCap + t) = 0) ∧
  comps.Nodup ∧ (∀ C ∈ comps, C ∈ components G₀) ∧
  efIdx.Nodup ∧ (∀ idx ∈ efIdx, idx < comps.length) ∧
  (∀ idx (hi : idx < comps.length),
    1 ≤ (compGraph G₀ comps[idx]).m ↔ idx ∈ efIdx) ∧
  (∀ v < vCap, mem (visBase + v) = if (∃ C ∈ comps, v ∈ C) then 1 else 0) ∧
  (∀ idx (hi : idx < comps.length),
    let C := comps[idx]
    (∀ u ∈ C, mem (compVCompBase b + u) = idx) ∧
    mem (compEdgefulBase b vCap + idx) = (if 1 ≤ (compGraph G₀ C).m then 1 else 0) ∧
    mem (compN0Base b vCap + idx) = (compGraph G₀ C).n ∧
    mem (compM0Base b vCap + idx) = (compGraph G₀ C).m ∧
    (∀ e ∈ compEdgeSet G₀ C,
      mem (compEdgeC1Base b vCap + e) = idx ∧ mem (compEdgeC2Base b vCap eCap + e) = idx)) ∧
  (∀ r (hr : r < efIdx.length),
    let idx := efIdx[r]
    ∃ (hi : idx < comps.length),
      let C := comps[idx]
      mem (compEdgefulIdxBase b vCap + idx) = r ∧
      ∀ j (hj : j < k),
        mem (compHandlesBase b vCap eCap L_w + (r * k + j)) = winH r j ∧
        (LSFRep W.h).rep (winH r j) (W.lsfInit (compGraph G₀ C) ctx.ell k j) (winX r j) mem ∧
        (winX r j).vCap = vCap ∧ (winX r j).eCap = eCap ∧ (winX r j).L_w = L_w ∧
        ctx.heap0 ≤ winH r j ∧ (winX r j).endAddr (winH r j) ≤ curHeap ∧
        ∀ a, (LSFRep W.h).foot (winH r j) (winX r j) a → ctx.heap0 ≤ a ∧ a < curHeap) ∧
  (∀ r₁ < efIdx.length, ∀ r₂ < efIdx.length, ∀ j₁ < k, ∀ j₂ < k,
    (r₁ ≠ r₂ ∨ j₁ ≠ j₂) →
    ∀ a, (LSFRep W.h).foot (winH r₁ j₁) (winX r₁ j₁) a →
      ¬ (LSFRep W.h).foot (winH r₂ j₂) (winX r₂ j₂) a) ∧
  ctx.heap0 ≤ curHeap ∧
  curHeap ≤ ctx.heap0 + (comps.toFinset.filter fun C => 1 ≤ (compGraph G₀ C).m).sum (fun C =>
    dynGraphSize vCap eCap + W.winSpace k L_w vCap eCap (compGraph G₀ C).n (compGraph G₀ C).m) ∧
  ZeroFrom mem curHeap

lemma init_numComps_le {G₀ : MGraph} {comps : List (Finset ℕ)}
    (hnd : comps.Nodup) (hsub : ∀ C ∈ comps, C ∈ components G₀) :
    comps.length ≤ G₀.n := by
  classical
  have h1 : comps.length ≤ comps.toFinset.sum Finset.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    have hge : ∀ C ∈ comps.toFinset, 1 ≤ C.card := fun C hC =>
      Finset.card_pos.mpr (compGraph_nonempty (hsub C (List.mem_toFinset.mp hC)))
    calc comps.toFinset.card = comps.toFinset.sum (fun _ => 1) := by simp
      _ ≤ comps.toFinset.sum Finset.card := Finset.sum_le_sum hge
  have hdisj : Set.PairwiseDisjoint (↑comps.toFinset : Set (Finset ℕ)) id := by
    intro C1 h1' C2 h2' hne
    dsimp only [Function.onFun, id]
    exact comp_disjoint_of_ne G₀
      (hsub C1 (List.mem_toFinset.mp h1')) (hsub C2 (List.mem_toFinset.mp h2')) hne
  have h2 : comps.toFinset.sum Finset.card = (comps.toFinset.biUnion id).card :=
    (Finset.card_biUnion hdisj).symm
  have h3 : comps.toFinset.biUnion id ⊆ G₀.V := by
    intro v hv
    rcases Finset.mem_biUnion.mp hv with ⟨C, hC, hvC⟩
    rcases Finset.mem_image.mp (hsub C (List.mem_toFinset.mp hC)) with ⟨w, _, rfl⟩
    exact (mem_compOf_iff.mp hvC).1
  exact le_trans h1 (h2 ▸ Finset.card_le_card h3)

lemma init_numEdgeful_le {G₀ : MGraph} {comps : List (Finset ℕ)} {efIdx : List ℕ}
    (hndC : comps.Nodup)
    (hndE : efIdx.Nodup) (hsubE : ∀ idx ∈ efIdx, idx < comps.length)
    (hef : ∀ idx (hi : idx < comps.length), 1 ≤ (compGraph G₀ comps[idx]).m ↔ idx ∈ efIdx) :
    efIdx.length ≤ (comps.toFinset.filter fun C => 1 ≤ (compGraph G₀ C).m).sum
      (fun C => (compGraph G₀ C).m) := by
  classical
  set efSet := comps.toFinset.filter fun C => 1 ≤ (compGraph G₀ C).m
  have hcard : efIdx.length = efSet.card := by
    have hinj : ∀ a ∈ efIdx, ∀ b ∈ efIdx,
        (if ha : a < comps.length then comps[a] else ∅) =
        (if hb : b < comps.length then comps[b] else ∅) → a = b := by
      intro a ha b hb heq
      have ha' := hsubE a ha; have hb' := hsubE b hb
      simp only [ha', hb', ↓reduceDIte] at heq
      exact hndC.getElem_inj_iff.mp heq
    have hmap_nd : (efIdx.map fun idx => if hi : idx < comps.length then comps[idx] else ∅).Nodup :=
      List.Nodup.map_on hinj hndE
    have hset_eq : (efIdx.map fun idx => if hi : idx < comps.length then comps[idx] else ∅).toFinset = efSet := by
      ext C
      simp only [List.mem_toFinset, List.mem_map, efSet, Finset.mem_filter]
      constructor
      · rintro ⟨idx, hidx, rfl⟩
        have hi := hsubE idx hidx
        simp only [hi, ↓reduceDIte]
        exact ⟨List.getElem_mem hi, (hef idx hi).mpr hidx⟩
      · rintro ⟨hC, hm⟩
        obtain ⟨idx, hi, rfl⟩ := List.getElem_of_mem hC
        exact ⟨idx, (hef idx hi).mp hm, by simp [hi]⟩
    calc efIdx.length
        = (efIdx.map fun idx => if hi : idx < comps.length then comps[idx] else ∅).length := by simp
      _ = (efIdx.map fun idx => if hi : idx < comps.length then comps[idx] else ∅).toFinset.card :=
          (List.toFinset_card_of_nodup hmap_nd).symm
      _ = efSet.card := by rw [hset_eq]
  rw [hcard]
  calc efSet.card = efSet.sum (fun _ => 1) := by simp
    _ ≤ efSet.sum (fun C => (compGraph G₀ C).m) :=
        Finset.sum_le_sum fun C hC => (Finset.mem_filter.mp hC).2

lemma init_sum_m_le {G₀ : MGraph} {S : Finset (Finset ℕ)} (hS : S ⊆ components G₀) :
    S.sum (fun C => (compGraph G₀ C).m) ≤ G₀.m := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑S : Set (Finset ℕ)) (compEdgeSet G₀) := by
    intro C1 h1 C2 h2 hne
    dsimp only [Function.onFun]
    exact compEdgeSet_pairwiseDisjoint G₀ (hS h1) (hS h2) hne
  have heq : S.sum (fun C => (compGraph G₀ C).m) = (S.biUnion (compEdgeSet G₀)).card :=
    (Finset.card_biUnion hdisj).symm
  rw [heq]
  exact Finset.card_le_card fun e he => by
    rcases Finset.mem_biUnion.mp he with ⟨C, _, heC⟩
    exact Finset.filter_subset _ _ heC

end

end MinCostFlow.SparseCore.Program
