module

public import MinCostFlow.SparseCore.Program.CompInitLoop
import WordRAM.Tactic

/-!
# Setup Prefix Verification for Per-Component LSF Init (`CompInitSetup`)

Verifies `compInitSetupStmt`, establishing `InitRegsOK` and `InitMemInv` for `comps = []` in `O(1)`
steps (`≤ 350`) without scanning `vCap` or `eCap`. Uses opaque single-step assign/store wrappers so
intermediate states never build deep nested `Function.update` terms.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- Dummy `LSFConcrete` used for unused entries `r ≥ efIdx.length`. -/
def dummyLSFConcrete : LSFConcrete where
  vCap := 0; eCap := 0; n0 := 0; m0 := 0; tM := 0
  h := 0; P_fp := 0; L_in := 0; L_w := 0; k_nat := 0
  tOrigList := []; vList := []
  t0Parent := fun _ => 0; t0ParentTreeIdx := fun _ => 0; t0Depth := fun _ => 0
  thParent := fun _ => 0; upV := fun _ _ => 0; upMinIdx := fun _ _ => 0
  rList := []; compId := fun _ => 0; compRoot := fun _ => 0
  compSize := fun _ => 0; activeCids := ∅

/-- Sequential composition of two runs with an explicit additive cost. -/
lemma runs_seq_add {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁) (h₂ : Runs w p ω s₂ st₁ o st₂ c₂) :
    Runs w p ω (s₁ ;; s₂) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

/-- Opaque single-assign continuation step: hides `Function.update` behind an existential `st₁` so
long sequences of assignments keep tiny proof terms. -/
private lemma seq_assign_opaque {w : ℕ} {p : Program} {ω : ℕ → Bool} {r v : ℕ} {e : Expr}
    {s : Stmt} {st : State} {o : Outcome} {st' : State} {c₂ : ℕ}
    (he : e.eval w st = some v)
    (hcont : ∀ st₁ : State, st₁.mem = st.mem → st₁.regs r = v →
      (∀ j, j ≠ r → st₁.regs j = st.regs j) →
      ∃ c, Runs w p ω s st₁ o st' c ∧ c ≤ c₂) :
    ∃ c, Runs w p ω (.assign r e ;; s) st o st' c ∧ c ≤ e.size + 1 + c₂ + 1 := by
  let st₁ : State := { st with regs := Function.update st.regs r v }
  have h1 : Runs w p ω (.assign r e) st .normal st₁ (e.size + 1) :=
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩
  obtain ⟨c, hc, hle⟩ := hcont st₁ rfl (Function.update_self _ _ _)
    (fun j hj => Function.update_of_ne hj _ _)
  exact ⟨(e.size + 1) + c + 1, runs_seq_add h1 hc, by omega⟩

/-- Opaque single-store continuation step: hides `Function.update` behind an existential `st₁` so
long sequences of stores keep tiny proof terms. -/
private lemma seq_store_opaque {w : ℕ} {p : Program} {ω : ℕ → Bool} {addr val : ℕ} {ea ev : Expr}
    {s : Stmt} {st : State} {o : Outcome} {st' : State} {c₂ : ℕ}
    (hea : ea.eval w st = some addr) (hev : ev.eval w st = some val)
    (hcont : ∀ st₁ : State, st₁.regs = st.regs → st₁.mem addr = val →
      (∀ a, a ≠ addr → st₁.mem a = st.mem a) →
      ∃ c, Runs w p ω s st₁ o st' c ∧ c ≤ c₂) :
    ∃ c, Runs w p ω (.store ea ev ;; s) st o st' c ∧ c ≤ ea.size + ev.size + 1 + c₂ + 1 := by
  let st₁ : State := { st with mem := Function.update st.mem addr val }
  have h1 : Runs w p ω (.store ea ev) st .normal st₁ (ea.size + ev.size + 1) :=
    runs_store_iff.mpr ⟨addr, val, hea, hev, rfl, rfl, rfl⟩
  obtain ⟨c, hc, hle⟩ := hcont st₁ rfl (Function.update_self _ _ _)
    (fun a ha => Function.update_of_ne ha _ _)
  exact ⟨(ea.size + ev.size + 1) + c + 1, runs_seq_add h1 hc, by omega⟩

/-- Recursive execution of a right-nested list of `(off, val)` header stores from register `rIdx`
at `b + off`, with zero nested `Function.update` terms. -/
private lemma run_hdr_stores {w : ℕ} {p : Program} {ω : ℕ → Bool} {b : ℕ}
    (hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w) :
    ∀ (items : List (ℕ × Expr × ℕ)) (sTail : Stmt) (st : State),
      st.regs 8 = b →
      (∀ x ∈ items, x.1 < compHdrSize ∧ x.2.1.size = 1 ∧
        ∀ m : ℕ → ℕ, x.2.1.eval w { st with mem := m } = some x.2.2) →
      (items.map Prod.fst).Nodup →
      ∃ st1 c1,
        (∀ o st2 c2, Runs w p ω sTail st1 o st2 c2 →
          Runs w p ω (items.foldr (fun x acc =>
            .store (.bin .add (.reg 8) (.const x.1)) x.2.1 ;; acc) sTail) st o st2 (c1 + c2)) ∧
        st1.regs = st.regs ∧
        (∀ x ∈ items, st1.mem (b + x.1) = x.2.2) ∧
        (∀ a, (∀ x ∈ items, a ≠ b + x.1) → st1.mem a = st.mem a) ∧
        c1 ≤ 6 * items.length := by
  intro items
  induction items with
  | nil =>
    intro sTail st _ _ _
    exact ⟨st, 0, fun _ _ _ h => by simpa using h, rfl, (fun _ h => by cases h), (fun _ _ => rfl), le_rfl⟩
  | cons hd tl ih =>
    intro sTail st hr8 hall hnd
    rcases hd with ⟨off, ev, val⟩
    have hhd := hall (off, ev, val) List.mem_cons_self
    have htl : ∀ x ∈ tl, x.1 < compHdrSize ∧ x.2.1.size = 1 ∧
        ∀ m : ℕ → ℕ, x.2.1.eval w { st with mem := m } = some x.2.2 :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hnd_tl : (tl.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    have hoff_not_tl : off ∉ tl.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hbo := hb_off off hhd.1
    let stM : State := { st with mem := Function.update st.mem (b + off) val }
    have hstep : Runs w p ω (.store (.bin .add (.reg 8) (.const off)) ev) st .normal stM 5 :=
      runs_store_iff.mpr ⟨b + off, val,
        by simp [Expr.eval, BinOp.eval, hr8, hbo.1, hbo.2],
        hhd.2.2 st.mem, rfl, rfl, by simp [Expr.size, hhd.2.1]⟩
    obtain ⟨st1, c1, hrun1, hregs1, hmem1, hfr1, hc1⟩ := ih sTail stM hr8 htl hnd_tl
    refine ⟨st1, 6 + c1, fun o st2 c2 htail => ?_, hregs1, fun x hx => ?_, fun a ha => ?_,
      by simp only [List.length_cons]; omega⟩
    · have hcomb := runs_seq_add hstep (hrun1 o st2 c2 htail)
      have hce : 5 + (c1 + c2) + 1 = 6 + c1 + c2 := by omega
      rw [hce] at hcomb
      exact hcomb
    · rcases List.mem_cons.mp hx with rfl | hx'
      · have hne_tl : ∀ y ∈ tl, b + off ≠ b + y.1 := fun y hy h =>
          hoff_not_tl (List.mem_map.mpr ⟨y, hy, by omega⟩)
        exact (hfr1 (b + off) hne_tl).trans (Function.update_self _ _ _)
      · exact hmem1 x hx'
    · have hne_hd : a ≠ b + off := ha _ List.mem_cons_self
      have hne_tl : ∀ y ∈ tl, a ≠ b + y.1 := fun y hy => ha y (List.mem_cons_of_mem _ hy)
      exact (hfr1 a hne_tl).trans (Function.update_of_ne hne_hd _ _)

/-- Tail half of `compInitSetupStmt`: 21 static header stores, `oneLimb[0] := 1`, and cursor
registers `32..35`. -/
private def compInitSetupPart2 (hLimb : ℕ) : Stmt :=
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

/-- Runs `compInitSetupPart2` using `run_hdr_stores` (zero deep `Function.update` nesting). -/
private lemma compInitSetup_part2 {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    (ctx : InitCtx W w k G₀ p mem0) {stA : State}
    (hmemA : stA.mem = mem0)
    (hRA : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m stA.regs) :
    ∃ st0 cB,
      Runs w p ω (compInitSetupPart2 W.h) stA .normal st0 cB ∧
      InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st0.regs ∧
      st0.regs 32 = ctx.heap0 ∧ st0.regs 33 = 0 ∧ st0.regs 34 = 0 ∧ st0.regs 35 = 0 ∧
      InitMemInv ctx st0.mem ctx.heap0 [] [] (fun _ _ => 0) (fun _ _ => dummyLSFConcrete) ∧
      cB ≤ 185 := by
  have hsp_lt := ctx.hsp_lt
  have hstat_lt : ctx.b + compStaticSize ctx.vCap ctx.eCap ctx.L_w < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hw3 : 3 < 2 ^ w := by have := ctx.hw16; omega
  have hheap0_w : ctx.heap0 < 2 ^ w := by omega
  have h3m_w : 3 * G₀.m < 2 ^ w := by dsimp [InitCtx.heap0] at hsp_lt; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ ctx.b + off < 2 ^ w := fun off hoff => by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt hoff ⊢; omega
  let items : List (ℕ × Expr × ℕ) :=
    [ (compOffVCap, .reg 6, ctx.vCap),
      (compOffECap, .reg 7, ctx.eCap),
      (compOffK, .reg 4, k),
      (compOffLW, .reg 5, ctx.L_w),
      (compOffHLimb, .const W.h, W.h),
      (compOffLIn, .reg 2, W.L_in),
      (compOffPFp, .reg 3, W.P_fp),
      (compOffVCompPtr, .reg 16, compVCompBase ctx.b),
      (compOffEdgefulPtr, .reg 17, compEdgefulBase ctx.b ctx.vCap),
      (compOffEdgefulIdxPtr, .reg 18, compEdgefulIdxBase ctx.b ctx.vCap),
      (compOffN0Ptr, .reg 19, compN0Base ctx.b ctx.vCap),
      (compOffM0Ptr, .reg 20, compM0Base ctx.b ctx.vCap),
      (compOffEdgeC1Ptr, .reg 21, compEdgeC1Base ctx.b ctx.vCap),
      (compOffEdgeC2Ptr, .reg 22, compEdgeC2Base ctx.b ctx.vCap ctx.eCap),
      (compOffIsCrossPtr, .reg 23, compIsCrossBase ctx.b ctx.vCap ctx.eCap),
      (compOffIsInsPtr, .reg 24, compIsInsBase ctx.b ctx.vCap ctx.eCap),
      (compOffGhostPtr, .reg 25, compGhostBase ctx.b ctx.vCap ctx.eCap),
      (compOffTouchMarkPtr, .reg 26, compTouchMarkBase ctx.b ctx.vCap ctx.eCap),
      (compOffOneLimbPtr, .reg 27, compOneLimbBase ctx.b ctx.vCap ctx.eCap),
      (compOffHandlesPtr, .reg 28, compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w),
      (compOffM0Total, .reg 12, G₀.m) ]
  let sTail : Stmt :=
    .store (.reg 27) (.const 1) ;;
    .assign 32 (.bin .add (.reg 31) (.bin .mul (.const 3) (.reg 12))) ;;
    .assign 33 (.const 0) ;;
    .assign 34 (.const 0) ;;
    .assign 35 (.const 0)
  have hall : ∀ x ∈ items, x.1 < compHdrSize ∧ x.2.1.size = 1 ∧
      ∀ m : ℕ → ℕ, x.2.1.eval w { stA with mem := m } = some x.2.2 := by
    intro x hx
    simp only [items, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r6]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r7]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r4]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r5]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, ctx.hHw]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r2]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r3]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r16]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r17]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r18]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r19]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r20]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r21]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r22]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r23]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r24]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r25]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r26]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r27]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r28]⟩
    · exact ⟨by dsimp only; decide, rfl, fun _ => by simp [Expr.eval, hRA.r12]⟩
  have hnd : (items.map Prod.fst).Nodup := by
    dsimp only [items, List.map, compOffVCap, compOffECap, compOffK, compOffLW, compOffHLimb,
      compOffLIn, compOffPFp, compOffVCompPtr, compOffEdgefulPtr, compOffEdgefulIdxPtr,
      compOffN0Ptr, compOffM0Ptr, compOffEdgeC1Ptr, compOffEdgeC2Ptr, compOffIsCrossPtr,
      compOffIsInsPtr, compOffGhostPtr, compOffTouchMarkPtr, compOffOneLimbPtr,
      compOffHandlesPtr, compOffM0Total]
    decide
  obtain ⟨st1, c1, hrun1, hregs1, hmem1, hfr1, hc1⟩ :=
    run_hdr_stores (p := p) (ω := ω) hb_off items sTail stA hRA.r8 hall hnd
  -- Tail 5 statements: `oneLimb[0] := 1` and `r32 := heap0, r33..35 := 0`
  let st2 : State := { st1 with mem := Function.update st1.mem (compOneLimbBase ctx.b ctx.vCap ctx.eCap) 1 }
  let st3 : State := { st2 with regs := Function.update st2.regs 32 ctx.heap0 }
  let st4 : State := { st3 with regs := Function.update st3.regs 33 0 }
  let st5 : State := { st4 with regs := Function.update st4.regs 34 0 }
  let st0 : State := { st5 with regs := Function.update st5.regs 35 0 }
  have h12 : Runs w p ω (.store (.reg 27) (.const 1)) st1 .normal st2 3 :=
    runs_store_iff.mpr ⟨compOneLimbBase ctx.b ctx.vCap ctx.eCap, 1,
      by simp [Expr.eval, hregs1, hRA.r27], by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
  have h23 : Runs w p ω (.assign 32 (.bin .add (.reg 31) (.bin .mul (.const 3) (.reg 12)))) st2 .normal st3 6 :=
    runs_assign_iff.mpr ⟨ctx.heap0,
      by simp [st2, Expr.eval, BinOp.eval, hregs1, hRA.r31, hRA.r12, hw3, h3m_w,
        show compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n + 3 * G₀.m < 2 ^ w from hheap0_w]; rfl,
      rfl, rfl, by simp [Expr.size]⟩
  have h34 : Runs w p ω (.assign 33 (.const 0)) st3 .normal st4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show (0 : ℕ) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have h45 : Runs w p ω (.assign 34 (.const 0)) st4 .normal st5 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show (0 : ℕ) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have h50 : Runs w p ω (.assign 35 (.const 0)) st5 .normal st0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show (0 : ℕ) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have htail : Runs w p ω sTail st1 .normal st0 19 :=
    runs_seq_add h12 (runs_seq_add h23 (runs_seq_add h34 (runs_seq_add h45 h50)))
  have hfull : Runs w p ω (compInitSetupPart2 W.h) stA .normal st0 (c1 + 19) :=
    hrun1 .normal st0 19 htail
  have hR0 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st0.regs := by
    have hR1 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st2.regs := by simpa [st2, hregs1] using hRA
    exact (((hR1.update_mut (by decide)).update_mut (by decide)).update_mut (by decide)).update_mut (by decide)
  -- Region ordering for `InitMemInv`
  have hOneEnd := compOneLimb_end_eq ctx.b ctx.vCap ctx.eCap ctx.L_w
  have hone_gt : ctx.b + compHdrSize ≤ compOneLimbBase ctx.b ctx.vCap ctx.eCap := by
    dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase,
      compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
      compVCompBase, compGhostSize, compHdrSize]; omega
  have hfr_out : ∀ a, (a < ctx.b ∨ ctx.b + compHdrSize ≤ a) →
      a ≠ compOneLimbBase ctx.b ctx.vCap ctx.eCap → st0.mem a = mem0 a := fun a ha hne1 => by
    change Function.update st1.mem (compOneLimbBase ctx.b ctx.vCap ctx.eCap) 1 a = mem0 a
    rw [Function.update_of_ne hne1]
    exact (hfr1 a fun x hx => by have := (hall x hx).1; omega).trans (by rw [hmemA])
  have hhdr_get : ∀ off val, (∃ ev, (off, ev, val) ∈ items) → st0.mem (ctx.b + off) = val := by
    intro off val ⟨ev, hx⟩
    change Function.update st1.mem (compOneLimbBase ctx.b ctx.vCap ctx.eCap) 1 (ctx.b + off) = val
    have hlt := (hall (off, ev, val) hx).1
    rw [Function.update_of_ne (by omega)]
    exact hmem1 (off, ev, val) hx
  have hInv0 : InitMemInv ctx st0.mem ctx.heap0 [] [] (fun _ _ => 0) (fun _ _ => dummyLSFConcrete) := by
    refine ⟨fun a ha => hfr_out a (Or.inl ha) (by omega), ?_, ?_, ?_, List.nodup_nil,
      fun _ h => (by cases h), List.nodup_nil, fun _ h => (by cases h), fun _ hi => (by simp at hi),
      fun v _ => (by
        simp only [List.not_mem_nil, false_and, exists_false, ↓reduceIte]
        have hge : ctx.b + compHdrSize ≤ compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + v := by
          dsimp [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
        have hne1 : compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + v ≠ compOneLimbBase ctx.b ctx.vCap ctx.eCap := by
          have := ctx.hLw; have := hOneEnd; dsimp [compTablesEnd]; omega
        exact (hfr_out _ (Or.inr hge) hne1).trans (ctx.hz0 _ (by omega))),
      fun _ hi => (by simp at hi), fun _ hi => (by simp at hi), fun _ hi => (by simp at hi),
      le_rfl, by simp, fun a ha => (by
        have hge : ctx.b + compHdrSize ≤ a := by
          dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at ha ⊢; omega
        have hne1 : a ≠ compOneLimbBase ctx.b ctx.vCap ctx.eCap := by
          have := ctx.hLw; have := hOneEnd; dsimp [InitCtx.heap0, compTablesEnd] at ha; omega
        exact (hfr_out a (Or.inr hge) hne1).trans (ctx.hz0 a (by omega)))⟩
    · exact ⟨hhdr_get _ _ ⟨.reg 6, by simp [items]⟩, hhdr_get _ _ ⟨.reg 7, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 4, by simp [items]⟩, hhdr_get _ _ ⟨.reg 5, by simp [items]⟩,
        hhdr_get _ _ ⟨.const W.h, by simp [items]⟩, hhdr_get _ _ ⟨.reg 2, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 3, by simp [items]⟩, hhdr_get _ _ ⟨.reg 16, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 17, by simp [items]⟩, hhdr_get _ _ ⟨.reg 18, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 19, by simp [items]⟩, hhdr_get _ _ ⟨.reg 20, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 21, by simp [items]⟩, hhdr_get _ _ ⟨.reg 22, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 23, by simp [items]⟩, hhdr_get _ _ ⟨.reg 24, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 25, by simp [items]⟩, hhdr_get _ _ ⟨.reg 26, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 27, by simp [items]⟩, hhdr_get _ _ ⟨.reg 28, by simp [items]⟩,
        hhdr_get _ _ ⟨.reg 12, by simp [items]⟩⟩
    · intro a ha1 ha2
      exact (hfr_out a (Or.inr (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha1 ⊢; omega)) (by omega)).trans
        (ctx.hz0 a (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha1 ⊢; omega))
    · refine ⟨Function.update_self _ _ _, fun t ht1 _ => ?_⟩
      exact (hfr_out _ (Or.inr (by omega)) (by omega)).trans (ctx.hz0 _ (by omega))
  exact ⟨st0, c1 + 19, hfull, hR0, by simp [st0, st5, st4, st3], by simp [st0, st5, st4],
    by simp [st0, st5], by simp [st0], hInv0, by simp [items] at hc1; omega⟩

/-- Runs the full `compInitSetupStmt` prefix (23 register computations + `compInitSetupPart2`),
establishing `InitRegsOK` and `InitMemInv` for `comps = []` in at most `350` steps. -/
theorem compInitSetup_runs {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (ctx : InitCtx W w k G₀ p mem0) :
    ∃ st0 c_set,
      Runs w p ω (compInitSetupStmt W.h)
        (startState [ctx.g0Ptr, ctx.lenArr, W.L_in, W.P_fp, k, ctx.L_w, ctx.vCap, ctx.eCap, ctx.b] mem0 pos)
        .normal st0 c_set ∧
      InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st0.regs ∧
      st0.regs 32 = ctx.heap0 ∧ st0.regs 33 = 0 ∧ st0.regs 34 = 0 ∧ st0.regs 35 = 0 ∧
      InitMemInv ctx st0.mem ctx.heap0 [] [] (fun _ _ => 0) (fun _ _ => dummyLSFConcrete) ∧
      c_set ≤ 350 := by
  have hsp_lt := ctx.hsp_lt
  have hstat_lt : ctx.b + compStaticSize ctx.vCap ctx.eCap ctx.L_w < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hg0_w : ctx.g0Ptr + dynGraphSize ctx.vCap0 ctx.eCap0 < 2 ^ w := by
    have := ctx.hg0_le; dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt; omega
  have hw2 : 2 < 2 ^ w := by have := ctx.hw16; omega
  have hw3 : 3 < 2 ^ w := by have := ctx.hw16; omega
  have hw4 : 4 < 2 ^ w := by have := ctx.hw16; omega
  have hw6 : 6 < 2 ^ w := by have := ctx.hw16; omega
  have hw7 : 7 < 2 ^ w := by have := ctx.hw16; omega
  have hw9 : 9 < 2 ^ w := by have := ctx.hw16; omega
  have hwHdr : compHdrSize < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt ⊢; omega
  have hg0_4 : ctx.g0Ptr + 4 < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h3v0 : 3 * ctx.vCap0 < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h6v0 : 6 * ctx.vCap0 < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have hdg_bases : dgVListBase ctx.g0Ptr ctx.vCap0 < 2 ^ w ∧
      dgExtToIntBase ctx.g0Ptr ctx.vCap0 < 2 ^ w ∧
      dgIncHeadBase ctx.g0Ptr ctx.vCap0 < 2 ^ w := by
    dsimp [dgVListBase, dgExtToIntBase, dgIncHeadBase, dynGraphSize] at hg0_w ⊢; omega
  have hst_bases :
      compVCompBase ctx.b < 2 ^ w ∧ compEdgefulBase ctx.b ctx.vCap < 2 ^ w ∧
      compEdgefulIdxBase ctx.b ctx.vCap < 2 ^ w ∧ compN0Base ctx.b ctx.vCap < 2 ^ w ∧
      compM0Base ctx.b ctx.vCap < 2 ^ w ∧ compEdgeC1Base ctx.b ctx.vCap < 2 ^ w ∧
      compEdgeC2Base ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compIsCrossBase ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compIsInsBase ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compGhostBase ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compGhostBase ctx.b ctx.vCap ctx.eCap + 4 * ctx.vCap < 2 ^ w ∧
      compTouchMarkBase ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compOneLimbBase ctx.b ctx.vCap ctx.eCap < 2 ^ w ∧
      compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w < 2 ^ w ∧
      compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k < 2 ^ w ∧
      compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap < 2 ^ w ∧
      compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n < 2 ^ w ∧
      4 * ctx.vCap < 2 ^ w ∧ 6 * ctx.eCap < 2 ^ w ∧ 7 * ctx.vCap < 2 ^ w ∧
      4 + 7 * ctx.vCap < 2 ^ w ∧ 9 * ctx.eCap < 2 ^ w ∧
      dynGraphSize ctx.vCap ctx.eCap < 2 ^ w ∧ G₀.m * k < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase, compOneLimbBase, compTouchMarkBase,
      compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
      compGhostSize, compHdrSize, dynGraphSize] at hsp_lt hstat_lt ⊢; omega
  have hOneEnd := compOneLimb_end_eq ctx.b ctx.vCap ctx.eCap ctx.L_w
  -- Build a flat register-evaluation sequence via opaque single-assign steps (no deep updates!)
  set stI := startState [ctx.g0Ptr, ctx.lenArr, W.L_in, W.P_fp, k, ctx.L_w, ctx.vCap, ctx.eCap, ctx.b] mem0 pos
  have hstep1 : ∀ (r v : ℕ) (e : Expr) (st : State), e.eval w st = some v →
      ∃ st', Runs w p ω (.assign r e) st .normal st' (e.size + 1) ∧
        st'.mem = st.mem ∧ st'.regs r = v ∧ ∀ j ≠ r, st'.regs j = st.regs j := fun r v e st he =>
    ⟨{ st with regs := Function.update st.regs r v },
     runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, rfl, Function.update_self _ _ _,
     fun j hj => Function.update_of_ne hj _ _⟩
  -- Execute all 23 assignments with opaque intermediate states `s1 .. s23`
  obtain ⟨s1, hs1, hm1, r1_10, o1⟩ := hstep1 10 ctx.vCap0 (.load (.bin .add (.reg 0) (.const dgVCapOff))) stI
    (Expr.eval_load_of_eq (by simp [stI, Expr.eval, BinOp.eval, startState, dgVCapOff, show ctx.g0Ptr < 2 ^ w by omega]) ctx.hdg.2.2.2.1)
  have r1_0 : s1.regs 0 = ctx.g0Ptr := (o1 0 (by decide)).trans rfl
  have hs1_n : s1.mem (ctx.g0Ptr + dgNOff) = G₀.n := by rw [hm1]; exact ctx.hdg.2.2.2.2.2.1
  obtain ⟨s2, hs2, hm2, r2_11, o2⟩ := hstep1 11 G₀.n (.load (.bin .add (.reg 0) (.const dgNOff))) s1
    (Expr.eval_load_of_eq
      (by simp [Expr.eval, BinOp.eval, r1_0,
        show dgNOff < 2 ^ w by dsimp [dgNOff]; omega,
        show ctx.g0Ptr + dgNOff < 2 ^ w by dsimp [dgNOff]; omega]) hs1_n)
  have r2_0 : s2.regs 0 = ctx.g0Ptr := (o2 0 (by decide)).trans r1_0
  have r2_10 : s2.regs 10 = ctx.vCap0 := (o2 10 (by decide)).trans r1_10
  have hs2_m : s2.mem (ctx.g0Ptr + dgMOff) = G₀.m := by rw [hm2, hm1]; exact ctx.hdg.2.2.2.2.2.2.1
  obtain ⟨s3, hs3, hm3, r3_12, o3⟩ := hstep1 12 G₀.m (.load (.bin .add (.reg 0) (.const dgMOff))) s2
    (Expr.eval_load_of_eq
      (by simp [Expr.eval, BinOp.eval, r2_0,
        show dgMOff < 2 ^ w by dsimp [dgMOff]; omega,
        show ctx.g0Ptr + dgMOff < 2 ^ w by dsimp [dgMOff]; omega]) hs2_m)
  have r3_0 : s3.regs 0 = ctx.g0Ptr := (o3 0 (by decide)).trans r2_0
  have r3_10 : s3.regs 10 = ctx.vCap0 := (o3 10 (by decide)).trans r2_10
  obtain ⟨s4, hs4, hm4, r4_13, o4⟩ := hstep1 13 (dgVListBase ctx.g0Ptr ctx.vCap0)
    (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 10)) s3
    (by simp [Expr.eval, BinOp.eval, r3_0, r3_10, hw4, hg0_4]; exact ite_eq_left hdg_bases.1)
  have r4_0 : s4.regs 0 = ctx.g0Ptr := (o4 0 (by decide)).trans r3_0
  have r4_10 : s4.regs 10 = ctx.vCap0 := (o4 10 (by decide)).trans r3_10
  obtain ⟨s5, hs5, hm5, r5_14, o5⟩ := hstep1 14 (dgExtToIntBase ctx.g0Ptr ctx.vCap0)
    (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 10))) s4
    (by simp [Expr.eval, BinOp.eval, r4_0, r4_10, hw3, hw4, hg0_4, h3v0]; exact ite_eq_left hdg_bases.2.1)
  have r5_0 : s5.regs 0 = ctx.g0Ptr := (o5 0 (by decide)).trans r4_0
  have r5_10 : s5.regs 10 = ctx.vCap0 := (o5 10 (by decide)).trans r4_10
  obtain ⟨s6, hs6, hm6, r6_15, o6⟩ := hstep1 15 (dgIncHeadBase ctx.g0Ptr ctx.vCap0)
    (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 10))) s5
    (by simp [Expr.eval, BinOp.eval, r5_0, r5_10, hw4, hw6, hg0_4, h6v0]; exact ite_eq_left hdg_bases.2.2)
  have hkeep_lt10 : ∀ j < 10, s6.regs j = stI.regs j := fun j hj =>
    (o6 j (by omega)).trans ((o5 j (by omega)).trans ((o4 j (by omega)).trans
      ((o3 j (by omega)).trans ((o2 j (by omega)).trans (o1 j (by omega))))))
  have hkeep_6 : s6.regs 8 = ctx.b ∧ s6.regs 6 = ctx.vCap ∧ s6.regs 7 = ctx.eCap ∧
      s6.regs 5 = ctx.L_w ∧ s6.regs 4 = k :=
    ⟨hkeep_lt10 8 (by decide), hkeep_lt10 6 (by decide), hkeep_lt10 7 (by decide),
     hkeep_lt10 5 (by decide), hkeep_lt10 4 (by decide)⟩
  obtain ⟨s7, hs7, hm7, r7_16, o7⟩ := hstep1 16 (compVCompBase ctx.b) (.bin .add (.reg 8) (.const compHdrSize)) s6
    (by simp [Expr.eval, BinOp.eval, hkeep_6.1, hwHdr]; exact ite_eq_left hst_bases.1)
  obtain ⟨s8, hs8, hm8, r8_17, o8⟩ := hstep1 17 (compEdgefulBase ctx.b ctx.vCap) (.bin .add (.reg 16) (.reg 6)) s7
    (by simp [Expr.eval, BinOp.eval, r7_16, (o7 6 (by decide)).trans hkeep_6.2.1]; exact ite_eq_left hst_bases.2.1)
  obtain ⟨s9, hs9, hm9, r9_18, o9⟩ := hstep1 18 (compEdgefulIdxBase ctx.b ctx.vCap) (.bin .add (.reg 17) (.reg 6)) s8
    (by simp [Expr.eval, BinOp.eval, r8_17, (o8 6 (by decide)).trans ((o7 6 (by decide)).trans hkeep_6.2.1)]; exact ite_eq_left hst_bases.2.2.1)
  obtain ⟨s10, hs10, hm10, r10_19, o10⟩ := hstep1 19 (compN0Base ctx.b ctx.vCap) (.bin .add (.reg 18) (.reg 6)) s9
    (by simp [Expr.eval, BinOp.eval, r9_18, (o9 6 (by decide)).trans ((o8 6 (by decide)).trans ((o7 6 (by decide)).trans hkeep_6.2.1))]; exact ite_eq_left hst_bases.2.2.2.1)
  obtain ⟨s11, hs11, hm11, r11_20, o11⟩ := hstep1 20 (compM0Base ctx.b ctx.vCap) (.bin .add (.reg 19) (.reg 6)) s10
    (by simp [Expr.eval, BinOp.eval, r10_19, (o10 6 (by decide)).trans ((o9 6 (by decide)).trans ((o8 6 (by decide)).trans ((o7 6 (by decide)).trans hkeep_6.2.1)))]; exact ite_eq_left hst_bases.2.2.2.2.1)
  obtain ⟨s12, hs12, hm12, r12_21, o12⟩ := hstep1 21 (compEdgeC1Base ctx.b ctx.vCap) (.bin .add (.reg 20) (.reg 6)) s11
    (by simp [Expr.eval, BinOp.eval, r11_20, (o11 6 (by decide)).trans ((o10 6 (by decide)).trans ((o9 6 (by decide)).trans ((o8 6 (by decide)).trans ((o7 6 (by decide)).trans hkeep_6.2.1))))]; exact ite_eq_left hst_bases.2.2.2.2.2.1)
  have hkeep_lt16 : ∀ j < 16, s12.regs j = s6.regs j := fun j hj =>
    (o12 j (by omega)).trans ((o11 j (by omega)).trans ((o10 j (by omega)).trans
      ((o9 j (by omega)).trans ((o8 j (by omega)).trans (o7 j (by omega))))))
  obtain ⟨s13, hs13, hm13, r13_22, o13⟩ := hstep1 22 (compEdgeC2Base ctx.b ctx.vCap ctx.eCap) (.bin .add (.reg 21) (.reg 7)) s12
    (by simp [Expr.eval, BinOp.eval, r12_21, (hkeep_lt16 7 (by decide)).trans hkeep_6.2.2.1]; exact ite_eq_left hst_bases.2.2.2.2.2.2.1)
  obtain ⟨s14, hs14, hm14, r14_23, o14⟩ := hstep1 23 (compIsCrossBase ctx.b ctx.vCap ctx.eCap) (.bin .add (.reg 22) (.reg 7)) s13
    (by simp [Expr.eval, BinOp.eval, r13_22, (o13 7 (by decide)).trans ((hkeep_lt16 7 (by decide)).trans hkeep_6.2.2.1)]; exact ite_eq_left hst_bases.2.2.2.2.2.2.2.1)
  obtain ⟨s15, hs15, hm15, r15_24, o15⟩ := hstep1 24 (compIsInsBase ctx.b ctx.vCap ctx.eCap) (.bin .add (.reg 23) (.reg 7)) s14
    (by simp [Expr.eval, BinOp.eval, r14_23, (o14 7 (by decide)).trans ((o13 7 (by decide)).trans ((hkeep_lt16 7 (by decide)).trans hkeep_6.2.2.1))]; exact ite_eq_left hst_bases.2.2.2.2.2.2.2.2.1)
  obtain ⟨s16, hs16, hm16, r16_25, o16⟩ := hstep1 25 (compGhostBase ctx.b ctx.vCap ctx.eCap) (.bin .add (.reg 24) (.reg 7)) s15
    (by simp [Expr.eval, BinOp.eval, r15_24, (o15 7 (by decide)).trans ((o14 7 (by decide)).trans ((o13 7 (by decide)).trans ((hkeep_lt16 7 (by decide)).trans hkeep_6.2.2.1)))]; exact ite_eq_left hst_bases.2.2.2.2.2.2.2.2.2.1)
  have hkeep_lt22 : ∀ j < 22, s16.regs j = s12.regs j := fun j hj =>
    (o16 j (by omega)).trans ((o15 j (by omega)).trans ((o14 j (by omega)).trans (o13 j (by omega))))
  have r16_6 : s16.regs 6 = ctx.vCap := (hkeep_lt22 6 (by decide)).trans ((hkeep_lt16 6 (by decide)).trans hkeep_6.2.1)
  have r16_7 : s16.regs 7 = ctx.eCap := (hkeep_lt22 7 (by decide)).trans ((hkeep_lt16 7 (by decide)).trans hkeep_6.2.2.1)
  obtain ⟨s17, hs17, hm17, r17_26, o17⟩ := hstep1 26 (compTouchMarkBase ctx.b ctx.vCap ctx.eCap)
    (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 4) (.reg 6))) (.bin .mul (.const 6) (.reg 7))) s16
    (by have hlt : compGhostBase ctx.b ctx.vCap ctx.eCap + 4 * ctx.vCap + 6 * ctx.eCap < 2 ^ w := by
          have := hst_bases.2.2.2.2.2.2.2.2.2.2.2.1
          dsimp [compTouchMarkBase, compGhostSize] at this; omega
        simp [Expr.eval, BinOp.eval, r16_25, r16_6, r16_7, hw4, hw6, hlt,
          hst_bases.2.2.2.2.2.2.2.2.2.2.1,
          hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
        dsimp [compTouchMarkBase, compGhostSize]; omega)
  obtain ⟨s18, hs18, hm18, r18_27, o18⟩ := hstep1 27 (compOneLimbBase ctx.b ctx.vCap ctx.eCap) (.bin .add (.reg 26) (.reg 6)) s17
    (by simp [Expr.eval, BinOp.eval, r17_26, (o17 6 (by decide)).trans r16_6]; exact ite_eq_left hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.1)
  obtain ⟨s19, hs19, hm19, r19_28, o19⟩ := hstep1 28 (compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w) (.bin .add (.reg 27) (.reg 5)) s18
    (by simp [Expr.eval, BinOp.eval, r18_27,
        (o18 5 (by decide)).trans ((o17 5 (by decide)).trans ((hkeep_lt22 5 (by decide)).trans ((hkeep_lt16 5 (by decide)).trans hkeep_6.2.2.2.1))),
        hOneEnd]; exact hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hkeep_lt26 : ∀ j < 26, s19.regs j = s16.regs j := fun j hj =>
    (o19 j (by omega)).trans ((o18 j (by omega)).trans (o17 j (by omega)))
  have r19_12 : s19.regs 12 = G₀.m := (hkeep_lt26 12 (by decide)).trans ((hkeep_lt22 12 (by decide)).trans
    ((hkeep_lt16 12 (by decide)).trans ((o6 12 (by decide)).trans ((o5 12 (by decide)).trans ((o4 12 (by decide)).trans r3_12)))))
  have r19_4 : s19.regs 4 = k := (hkeep_lt26 4 (by decide)).trans ((hkeep_lt22 4 (by decide)).trans ((hkeep_lt16 4 (by decide)).trans hkeep_6.2.2.2.2))
  obtain ⟨s20, hs20, hm20, r20_29, o20⟩ := hstep1 29 (compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k)
    (.bin .add (.reg 28) (.bin .mul (.reg 12) (.reg 4))) s19
    (by simp [Expr.eval, BinOp.eval, r19_28, r19_12, r19_4,
        hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
        exact ite_eq_left hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  obtain ⟨s21, hs21, hm21, r21_30, o21⟩ := hstep1 30 (compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap)
    (.bin .add (.reg 29) (.reg 6)) s20
    (by simp [Expr.eval, BinOp.eval, r20_29, (o20 6 (by decide)).trans ((hkeep_lt26 6 (by decide)).trans r16_6),
        hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
  have r21_11 : s21.regs 11 = G₀.n := (o21 11 (by decide)).trans ((o20 11 (by decide)).trans
    ((hkeep_lt26 11 (by decide)).trans ((hkeep_lt22 11 (by decide)).trans ((hkeep_lt16 11 (by decide)).trans
      ((o6 11 (by decide)).trans ((o5 11 (by decide)).trans ((o4 11 (by decide)).trans ((o3 11 (by decide)).trans r2_11))))))))
  obtain ⟨s22, hs22, hm22, r22_31, o22⟩ := hstep1 31 (compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n)
    (.bin .add (.reg 30) (.reg 11)) s21
    (by simp [Expr.eval, BinOp.eval, r21_30, r21_11, hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
  have hkeep_lt29 : ∀ j < 29, s22.regs j = s19.regs j := fun j hj =>
    (o22 j (by omega)).trans ((o21 j (by omega)).trans (o20 j (by omega)))
  obtain ⟨s23, hs23, hm23, r23_36, o23⟩ := hstep1 36 (dynGraphSize ctx.vCap ctx.eCap)
    (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 6))) (.bin .mul (.const 9) (.reg 7))) s22
    (by simp [Expr.eval, BinOp.eval,
        (hkeep_lt29 6 (by decide)).trans ((hkeep_lt26 6 (by decide)).trans r16_6),
        (hkeep_lt29 7 (by decide)).trans ((hkeep_lt26 7 (by decide)).trans r16_7),
        hw4, hw7, hw9,
        hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
        exact ite_eq_left hst_bases.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hmem23 : s23.mem = mem0 :=
    hm23.trans (hm22.trans (hm21.trans (hm20.trans (hm19.trans (hm18.trans (hm17.trans (hm16.trans
      (hm15.trans (hm14.trans (hm13.trans (hm12.trans (hm11.trans (hm10.trans (hm9.trans (hm8.trans
        (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1)))))))))))))))))))))
  have hlt10 : ∀ j < 10, s23.regs j = stI.regs j := fun j hj =>
    (o23 j (by omega)).trans ((hkeep_lt29 j (by omega)).trans ((hkeep_lt26 j (by omega)).trans
      ((hkeep_lt22 j (by omega)).trans ((hkeep_lt16 j (by omega)).trans (hkeep_lt10 j hj)))))
  have hR23 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m s23.regs :=
    { r0 := hlt10 0 (by decide), r1 := hlt10 1 (by decide), r2 := hlt10 2 (by decide),
      r3 := hlt10 3 (by decide), r4 := hlt10 4 (by decide), r5 := hlt10 5 (by decide),
      r6 := hlt10 6 (by decide), r7 := hlt10 7 (by decide), r8 := hlt10 8 (by decide),
      r10 := (o23 10 (by decide)).trans ((hkeep_lt29 10 (by decide)).trans ((hkeep_lt26 10 (by decide)).trans ((hkeep_lt22 10 (by decide)).trans ((hkeep_lt16 10 (by decide)).trans ((o6 10 (by decide)).trans r5_10))))),
      r11 := (o23 11 (by decide)).trans ((o22 11 (by decide)).trans r21_11),
      r12 := (o23 12 (by decide)).trans ((hkeep_lt29 12 (by decide)).trans r19_12),
      r13 := (o23 13 (by decide)).trans ((hkeep_lt29 13 (by decide)).trans ((hkeep_lt26 13 (by decide)).trans ((hkeep_lt22 13 (by decide)).trans ((hkeep_lt16 13 (by decide)).trans ((o6 13 (by decide)).trans ((o5 13 (by decide)).trans r4_13)))))),
      r14 := (o23 14 (by decide)).trans ((hkeep_lt29 14 (by decide)).trans ((hkeep_lt26 14 (by decide)).trans ((hkeep_lt22 14 (by decide)).trans ((hkeep_lt16 14 (by decide)).trans ((o6 14 (by decide)).trans r5_14))))),
      r15 := (o23 15 (by decide)).trans ((hkeep_lt29 15 (by decide)).trans ((hkeep_lt26 15 (by decide)).trans ((hkeep_lt22 15 (by decide)).trans ((hkeep_lt16 15 (by decide)).trans r6_15)))),
      r16 := (o23 16 (by decide)).trans ((hkeep_lt29 16 (by decide)).trans ((hkeep_lt26 16 (by decide)).trans ((hkeep_lt22 16 (by decide)).trans ((o12 16 (by decide)).trans ((o11 16 (by decide)).trans ((o10 16 (by decide)).trans ((o9 16 (by decide)).trans ((o8 16 (by decide)).trans r7_16)))))))),
      r17 := (o23 17 (by decide)).trans ((hkeep_lt29 17 (by decide)).trans ((hkeep_lt26 17 (by decide)).trans ((hkeep_lt22 17 (by decide)).trans ((o12 17 (by decide)).trans ((o11 17 (by decide)).trans ((o10 17 (by decide)).trans ((o9 17 (by decide)).trans r8_17))))))),
      r18 := (o23 18 (by decide)).trans ((hkeep_lt29 18 (by decide)).trans ((hkeep_lt26 18 (by decide)).trans ((hkeep_lt22 18 (by decide)).trans ((o12 18 (by decide)).trans ((o11 18 (by decide)).trans ((o10 18 (by decide)).trans r9_18)))))),
      r19 := (o23 19 (by decide)).trans ((hkeep_lt29 19 (by decide)).trans ((hkeep_lt26 19 (by decide)).trans ((hkeep_lt22 19 (by decide)).trans ((o12 19 (by decide)).trans ((o11 19 (by decide)).trans r10_19))))),
      r20 := (o23 20 (by decide)).trans ((hkeep_lt29 20 (by decide)).trans ((hkeep_lt26 20 (by decide)).trans ((hkeep_lt22 20 (by decide)).trans ((o12 20 (by decide)).trans r11_20)))),
      r21 := (o23 21 (by decide)).trans ((hkeep_lt29 21 (by decide)).trans ((hkeep_lt26 21 (by decide)).trans ((hkeep_lt22 21 (by decide)).trans r12_21))),
      r22 := (o23 22 (by decide)).trans ((hkeep_lt29 22 (by decide)).trans ((hkeep_lt26 22 (by decide)).trans ((o16 22 (by decide)).trans ((o15 22 (by decide)).trans ((o14 22 (by decide)).trans r13_22))))),
      r23 := (o23 23 (by decide)).trans ((hkeep_lt29 23 (by decide)).trans ((hkeep_lt26 23 (by decide)).trans ((o16 23 (by decide)).trans ((o15 23 (by decide)).trans r14_23)))),
      r24 := (o23 24 (by decide)).trans ((hkeep_lt29 24 (by decide)).trans ((hkeep_lt26 24 (by decide)).trans ((o16 24 (by decide)).trans r15_24))),
      r25 := (o23 25 (by decide)).trans ((hkeep_lt29 25 (by decide)).trans ((hkeep_lt26 25 (by decide)).trans r16_25)),
      r26 := (o23 26 (by decide)).trans ((hkeep_lt29 26 (by decide)).trans ((o19 26 (by decide)).trans ((o18 26 (by decide)).trans r17_26))),
      r27 := (o23 27 (by decide)).trans ((hkeep_lt29 27 (by decide)).trans ((o19 27 (by decide)).trans r18_27)),
      r28 := (o23 28 (by decide)).trans ((hkeep_lt29 28 (by decide)).trans r19_28),
      r29 := (o23 29 (by decide)).trans ((o22 29 (by decide)).trans ((o21 29 (by decide)).trans r20_29)),
      r30 := (o23 30 (by decide)).trans ((o22 30 (by decide)).trans r21_30),
      r31 := (o23 31 (by decide)).trans r22_31,
      r36 := r23_36 }
  obtain ⟨st0, cB, hrunB, hR0, hr32, hr33, hr34, hr35, hInv0, hcB⟩ :=
    compInitSetup_part2 (ω := ω) ctx hmem23 hR23
  have hrun_full : Runs w p ω (compInitSetupStmt W.h) stI .normal st0 _ :=
    runs_seq_add hs1 (runs_seq_add hs2 (runs_seq_add hs3 (runs_seq_add hs4 (runs_seq_add hs5
      (runs_seq_add hs6 (runs_seq_add hs7 (runs_seq_add hs8 (runs_seq_add hs9 (runs_seq_add hs10
        (runs_seq_add hs11 (runs_seq_add hs12 (runs_seq_add hs13 (runs_seq_add hs14 (runs_seq_add hs15
          (runs_seq_add hs16 (runs_seq_add hs17 (runs_seq_add hs18 (runs_seq_add hs19 (runs_seq_add hs20
            (runs_seq_add hs21 (runs_seq_add hs22 (runs_seq_add hs23 hrunB))))))))))))))))))))))
  refine ⟨st0, _, hrun_full, hR0, hr32, hr33, hr34, hr35, hInv0, ?_⟩
  simp only [Expr.size]; omega

end

end MinCostFlow.SparseCore.Program
