module

public import MinCostFlow.SparseCore.Program.TourInitStage1
public import MinCostFlow.SparseCore.Program.TourOpsLink
public import MinCostFlow.SparseCore.Program.TourOpsChangeRoot
public import MinCostFlow.SparseCore.Program.TourOpsLenOwner
import Mathlib.Tactic

/-!
# Tour Initialization (`tourInitBody`)

Completes initialization `[vCap, eCap, ordPtr, fePtr, rsPtr, heap]` of `tourContract` in three
stages:
1. `stage1Proc [vCap, eCap, ordPtr, rsPtr, heap]`: builds `TourRepAt` for the edgeless forest
   `s₀ = tourInitStage1Abs recs rs` and initializes the embedded `ordStore`, returning `hOut`.
2. `tourInitLinksLoop`: iterates over `fe = readNatList mem fePtr`, querying `rootOfExact` on
   `2 * e` and linking `e` via `tourOpLinkBody`, reaching `F = (initTourForest recs fe rs).F`.
3. `tourInitChRootsLoop`: iterates over `rs = readNatList mem rsPtr`, moving each non-isolated
   component's root to `r` via `rootOfExact` + `tourOpChangeRootBody`, reaching
   `s_final = ⟨ord, initTourForest recs fe rs, ∅⟩`.

Total cost (including final potential) is
`≤ (TOUR_INIT_BASE_MUL + mul_ord) * (1 + ordRecordsWords recs + |fe| + |rs|) * tourLog eCap`
with linear space `tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3` (independent of `heap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM bodies for Stages 2 and 3 -/

/-- Stage 2 loop: link every forest edge `e` in `fePtr` (`r7 = feLen`, `r8 = fePtr + 1`, `r9 = i`). -/
def tourInitLinksLoop (rootOfProc linkProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 9) (.reg 7))
    (.assign 10 (.load (.bin .add (.reg 8) (.reg 9))) ;;
     .assign 11 (.bin .add (.reg 10) (.reg 10)) ;;
     .call 12 rootOfProc [.reg 5, .reg 11, .reg 6] ;;
     .assign 11 (.load (.reg 6)) ;;
     .store (.reg 6) (.const 0) ;;
     .call 12 linkProc [.reg 5, .reg 10, .reg 11, .reg 6] ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)))

/-- Stage 3 loop: move each non-isolated component's root to `r ∈ rsPtr`
(`r7 = rsLen`, `r8 = rsPtr + 1`, `r9 = i`, `r10 = firstEndBase`, `r11 = keyOfNodeBase`). -/
def tourInitChRootsLoop (rootOfProc chRootProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 9) (.reg 7))
    (.assign 12 (.load (.bin .add (.reg 8) (.reg 9))) ;;
     .assign 13 (.load (.bin .add (.reg 10) (.reg 12))) ;;
     .cond (.reg 13)
       (.assign 14 (.load (.bin .add (.reg 11) (.reg 13))) ;;
        .call 15 rootOfProc [.reg 5, .reg 14, .reg 6] ;;
        .assign 14 (.load (.reg 6)) ;;
        .store (.reg 6) (.const 0) ;;
        .call 15 chRootProc [.reg 5, .reg 14, .reg 12, .reg 6])
       .nop ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)))

/-- Complete tour initialization procedure `[vCap, eCap, ordPtr, fePtr, rsPtr, heap] -> hOut`. -/
def tourInitBody (stage1Proc rootOfProc linkProc chRootProc : ℕ) : Stmt :=
  .call 6 stage1Proc [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5] ;;
  .assign 7 (.load (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 9 (.const 0) ;;
  tourInitLinksLoop rootOfProc linkProc ;;
  .assign 7 (.load (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 4) (.const 1)) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.load (.bin .add (.reg 5) (.const HDR_FIRST_END))) ;;
  .assign 11 (.load (.bin .add (.reg 5) (.const HDR_KEY_OF_NODE))) ;;
  tourInitChRootsLoop rootOfProc chRootProc ;;
  .ret (.reg 6)

theorem tourInitBody_noRand (s1P rP lP cP : ℕ) : (tourInitBody s1P rP lP cP).NoRand := by
  simp [tourInitBody, tourInitLinksLoop, tourInitChRootsLoop, Stmt.NoRand]

/-! ## Pure forest helpers for Stages 2 and 3 -/

private theorem not_connected_of_subgraph_erase {F_cur F_fin : MGraph} {e : ℕ}
    (hF : F_fin.IsForest) (he : e ∈ F_fin.E)
    (hV : F_cur.V = F_fin.V) (hE : F_cur.E ⊆ F_fin.E) (hne : e ∉ F_cur.E)
    (htail : F_cur.tail = F_fin.tail) (hhead : F_cur.head = F_fin.head) :
    ¬ F_cur.Connected (F_fin.tail e) (F_fin.head e) := by
  intro hc
  have hsub : (eraseForestEdge F_fin e).IsSubgraph F_cur :=
    ⟨by rw [hV],
     fun e' he' => Finset.mem_erase.mpr ⟨fun heq => hne (heq ▸ he'), hE he'⟩,
     fun e' _ => ⟨by simp [htail], by simp [hhead]⟩⟩
  have hc' := connected_of_subgraph hsub hc
  exact not_connected_eraseForestEdge hF (x := (e, true)) he hc'

private theorem addForestEdge_same_ends {ord : ℕ → List End} {F : MGraph} {e : ℕ}
    (htail : F.tail = fun e' => ordSrc ord (e', true))
    (hhead : F.head = fun e' => ordSrc ord (e', false)) :
    addForestEdge F e (ordSrc ord (e, true)) (ordSrc ord (e, false)) =
      { F with E := insert e F.E } := by
  cases F with
  | mk V E t h =>
    dsimp only at htail hhead
    subst htail; subst hhead
    simp only [addForestEdge, MGraph.mk.injEq, true_and]
    exact ⟨Function.update_eq_self _ _, Function.update_eq_self _ _⟩

/-! ## Stage 2: Linking all forest edges -/

private theorem tourInitLinks_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b fePtr hOut rootOfProc linkProc lsProc : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p)
    (hRoot : p.procs[rootOfProc]? = some (tourOpRootOfExactBody C.splay.loop))
    (hls : p.procs[lsProc]? = some (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join))
    (hLink : p.procs[linkProc]? = some (tourOpLinkBody lsProc C.rootTagOf C.setValNode C.rotateFront))
    (ω : ℕ → Bool) {mem0 : ℕ → ℕ} {recs : List (ℕ × List End)} {rs : List ℕ}
    {s0 : TourAbs} {x0 : TourConcrete R_ord.τ} {st0 : State}
    (hfe_le : fePtr + 1 + mem0 fePtr ≤ b)
    (hfe_nd : (readNatList mem0 fePtr).Nodup)
    (hValidFin : TourValid vCap eCap ⟨ordOfRecords recs, initTourForest recs (readNatList mem0 fePtr) rs, ∅⟩)
    (hord0 : s0.ord = ordOfRecords recs)
    (hV0 : s0.rf.F.V = (initTourForest recs (readNatList mem0 fePtr) rs).F.V)
    (hE0 : s0.rf.F.E = ∅)
    (htail0 : s0.rf.F.tail = fun e => ordSrc (ordOfRecords recs) (e, true))
    (hhead0 : s0.rf.F.head = fun e => ordSrc (ordOfRecords recs) (e, false))
    (hmk0 : s0.marked = ∅)
    (hrep0 : TourRepAt R_ord vCap eCap b s0 x0 st0.mem)
    (hfoot0 : ∀ a, tourFoot R_ord vCap eCap b x0 a → a < hOut)
    (hzero0 : ZeroFrom st0.mem hOut)
    (hpre0 : ∀ a < b, st0.mem a = mem0 a)
    (hroom : hOut + 2 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hr5 : st0.regs 5 = b) (hr6 : st0.regs 6 = hOut)
    (hr7 : st0.regs 7 = mem0 fePtr) (hr8 : st0.regs 8 = fePtr + 1) (hr9 : st0.regs 9 = 0) :
    let fe := readNatList mem0 fePtr
    ∃ (s1 : TourAbs) (x1 : TourConcrete R_ord.τ) (st1 : State) (c1 : ℕ),
      Runs w p ω (tourInitLinksLoop rootOfProc linkProc) st0 .normal st1 c1 ∧
      st1.regs 4 = st0.regs 4 ∧ st1.regs 5 = b ∧ st1.regs 6 = hOut ∧
      s1.ord = ordOfRecords recs ∧
      s1.rf.F = (initTourForest recs fe rs).F ∧
      s1.marked = ∅ ∧
      TourRepAt R_ord vCap eCap b s1 x1 st1.mem ∧
      (∀ a, tourFoot R_ord vCap eCap b x1 a → a < hOut) ∧
      ZeroFrom st1.mem hOut ∧
      (∀ a < b, st1.mem a = mem0 a) ∧
      c1 + (tourRep R_ord vCap eCap).phi b x1 st1.mem ≤
        (tourRep R_ord vCap eCap).phi b x0 st0.mem +
          mem0 fePtr * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap + 20 := by
  intro fe
  set Ffin := (initTourForest recs fe rs).F
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hloop : ∀ (rem i : ℕ) (sC : TourAbs) (xC : TourConcrete R_ord.τ) (stC : State),
      i + rem = mem0 fePtr →
      stC.regs 4 = st0.regs 4 → stC.regs 5 = b → stC.regs 6 = hOut →
      stC.regs 7 = mem0 fePtr → stC.regs 8 = fePtr + 1 → stC.regs 9 = i →
      sC.ord = ordOfRecords recs →
      sC.rf.F.V = Ffin.V →
      sC.rf.F.E = (fe.take i).toFinset →
      sC.rf.F.tail = Ffin.tail →
      sC.rf.F.head = Ffin.head →
      sC.marked = ∅ →
      TourRepAt R_ord vCap eCap b sC xC stC.mem →
      (∀ a, tourFoot R_ord vCap eCap b xC a → a < hOut) →
      ZeroFrom stC.mem hOut →
      (∀ a < b, stC.mem a = mem0 a) →
      ∃ (s1 : TourAbs) (x1 : TourConcrete R_ord.τ) (st1 : State) (c : ℕ),
        Runs w p ω (tourInitLinksLoop rootOfProc linkProc) stC .normal st1 c ∧
        st1.regs 4 = st0.regs 4 ∧ st1.regs 5 = b ∧ st1.regs 6 = hOut ∧
        s1.ord = ordOfRecords recs ∧ s1.rf.F = Ffin ∧ s1.marked = ∅ ∧
        TourRepAt R_ord vCap eCap b s1 x1 st1.mem ∧
        (∀ a, tourFoot R_ord vCap eCap b x1 a → a < hOut) ∧
        ZeroFrom st1.mem hOut ∧
        (∀ a < b, st1.mem a = mem0 a) ∧
        c + (tourRep R_ord vCap eCap).phi b x1 st1.mem ≤
          (tourRep R_ord vCap eCap).phi b xC stC.mem +
            rem * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro i sC xC stC hi hr4C hr5C hr6C hr7C _ hr9C hordC hVC hEC htailC hheadC hmkC hrepC hfootC hzC hpreC
      have hi_eq : i = mem0 fePtr := by omega
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stC = some 0 := by
        simp [Expr.eval, hr9C, hr7C, hi_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hFE_eq : sC.rf.F = Ffin := by
        have hlen : fe.length = mem0 fePtr := readList_length mem0 (fePtr + 1) (mem0 fePtr)
        have hE : sC.rf.F.E = Ffin.E := by rw [hEC, hi_eq, ← hlen, List.take_length]; rfl
        cases hF : sC.rf.F; cases hFf : Ffin; simp_all
      exact ⟨sC, xC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr4C, hr5C, hr6C, hordC, hFE_eq, hmkC, hrepC, hfootC, hzC, hpreC, by simp [Expr.size]; omega⟩
    | succ rem ih =>
      intro i sC xC stC hi hr4C hr5C hr6C hr7C hr8C hr9C hordC hVC hEC htailC hheadC hmkC hrepC hfootC hzC hpreC
      have hi_lt : i < mem0 fePtr := by omega
      have hfe_len : fe.length = mem0 fePtr := readList_length mem0 (fePtr + 1) (mem0 fePtr)
      set e := fe[i]'(by omega)
      have he_mem_fe : e ∈ fe := List.getElem_mem (by omega)
      have he_fin : e ∈ Ffin.E := List.mem_toFinset.mpr he_mem_fe
      have he_not_cur : e ∉ sC.rf.F.E := by
        rw [hEC, List.mem_toFinset]
        intro hmem
        obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
        simp only [List.length_take, lt_min_iff] at hj
        rw [List.getElem_take] at hje
        have := (List.Nodup.getElem_inj_iff hfe_nd).mp hje
        omega
      have he_ends := hValidFin.compat.forestEnd e he_fin
      have hxu : (e, true) ∈ sC.ord (Ffin.tail e) := by rw [hordC]; exact he_ends.1
      have hyv : (e, false) ∈ sC.ord (Ffin.head e) := by rw [hordC]; exact he_ends.2
      have he_lt : e < eCap := hValidFin.ordWithin.2.2 _ (e, true) he_ends.1
      have hnc : ¬ sC.rf.F.Connected (ordSrc sC.ord (e, true)) (ordSrc sC.ord (e, false)) := by
        rw [hordC]
        exact not_connected_of_subgraph_erase hValidFin.compat.forest he_fin hVC
          (by rw [hEC]; intro x hx; exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx)))
          he_not_cur htailC hheadC
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stC = some 1 := by
        simp [Expr.eval, hr9C, hr7C, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hmem_e : stC.mem (fePtr + 1 + i) = e := by
        rw [hpreC _ (by omega)]; simp [e, fe, readNatList, readList_getElem]
      set r1 := Function.update stC.regs 10 e
      set r2 := Function.update r1 11 (2 * e)
      have ha10 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 8) (rIdx := 9)
        (base := fePtr + 1) (idx := i) (val := e) (st := stC) hr8C hr9C
        (by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega) hmem_e
      have ha11 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.reg 10))) { stC with regs := r1 } .normal { stC with regs := r2 } 4 :=
        runs_assign_iff.mpr ⟨2 * e, by simp [Expr.eval, r1, BinOp.eval, (by omega : e + e < 2 ^ w)]; omega, rfl, rfl, rfl⟩
      -- Call `rootOfExact [b, 2 * e, hOut]`
      obtain ⟨oR, stR, cR, hrunR, hoR, xR, hrepR, hmemR, hzR, hfrR, hfootR, hcR⟩ :=
        tourOp_rootOf_exact_runs (keyX := 2 * e) (heap := hOut) (pos := stC.pos) hLoc C.toTourSplayCoreProcs ω
          hrepC ⟨Ffin.tail e, by simpa [tour_endOfKey_two_mul] using hxu⟩ hfootC hzC (by omega)
      have hcallR := runs_call_regs3 12 5 11 6 (st := { stC with regs := r2 }) hRoot
        (by simp [r2, r1, hr5C]) (by simp [r2]) (by simp [r2, r1, hr6C]) hrunR
      set rDrop := sC.rf.root (ordSrc sC.ord (e, true))
      have hmemR_val : stR.mem hOut = rDrop := by simpa [tour_endOfKey_two_mul, rDrop] using hmemR
      set r3 := Function.update r2 12 oR.value
      set r4 := Function.update r3 11 rDrop
      set mClr := Function.update stR.mem hOut 0
      have haDrop : Runs w p ω (.assign 11 (.load (.reg 6))) { stR with regs := r3 } .normal { stR with regs := r4 } 3 :=
        runs_assign_iff.mpr ⟨rDrop, by simp [Expr.eval, r3, r2, r1, hr6C, hmemR_val], rfl, rfl, rfl⟩
      have hstClr : Runs w p ω (.store (.reg 6) (.const 0)) { stR with regs := r4 } .normal { stR with mem := mClr, regs := r4 } 3 :=
        runs_store_iff.mpr ⟨hOut, 0, by simp [Expr.eval, r4, r3, r2, r1, hr6C], by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
      have hfootR_lt : ∀ a, tourFoot R_ord vCap eCap b xR a → a < hOut := fun a ha => hfootC a (hfootR a ha)
      have hlocClr := (tourRep_local hLoc vCap eCap) b sC xR stR.mem mClr fun a ha =>
        (Function.update_of_ne (Nat.ne_of_lt (hfootR_lt a ha)) _ _).symm
      have hzClr : ZeroFrom mClr hOut := fun a ha => by
        dsimp only [mClr]; by_cases hae : a = hOut
        · subst hae; simp
        · rw [Function.update_of_ne hae]; exact hzR a (by rw [hoR]; omega)
      -- Call `link [b, e, rDrop, hOut]`
      obtain ⟨oL, stL, cL, hrunL, hoL, xL, hrepL, hrespL, hcL⟩ :=
        tourOp_link_runs (e := e) (dropRoot := rDrop) (heap := hOut) (pos := stR.pos) hLoc C hls ω
          (hlocClr.1 hrepR) he_lt he_not_cur hxu hyv hnc (Or.inl rfl) hw (by omega) hfootR_lt hzClr hroom
      have hcallL := runs_call_regs4 12 5 10 11 6 (st := { stR with mem := mClr, regs := r4 }) hLink
        (by simp [r4, r3, r2, r1, hr5C]) (by simp [r4, r3, r2, r1]) (by simp [r4])
        (by simp [r4, r3, r2, r1, hr6C]) hrunL
      set r5 := Function.update r4 12 oL.value
      set r6 := Function.update r5 9 (i + 1)
      have haInc : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) { stL with regs := r5 } .normal { stL with regs := r6 } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r5, r4, r3, r2, r1, hr9C, BinOp.eval, (by omega : 1 < 2 ^ w),
          (by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11 (tour_runs_seq_normal hcallR
        (tour_runs_seq_normal haDrop (tour_runs_seq_normal hstClr (tour_runs_seq_normal hcallL haInc)))))
      have hL_ord : (tourLink sC e rDrop).ord = ordOfRecords recs := hordC
      have hL_F : (tourLink sC e rDrop).rf.F = { sC.rf.F with E := insert e sC.rf.F.E } := by
        simp only [tourLink, hordC]; exact addForestEdge_same_ends htailC hheadC
      have hL_E : (tourLink sC e rDrop).rf.F.E = (fe.take (i + 1)).toFinset := by
        rw [hL_F]; dsimp only; rw [hEC]
        ext x
        simp only [Finset.mem_insert, List.mem_toFinset,
          List.take_succ_eq_append_getElem (by omega : i < fe.length), List.mem_append,
          List.mem_singleton, e]
        exact or_comm
      have hL_foot : ∀ a, tourFoot R_ord vCap eCap b xL a → a < hOut := fun a ha => by
        rcases hrespL.2.2.2.2 a ha with h1 | ⟨h1, h2⟩
        · exact hfootR_lt a h1
        · omega
      have hL_zero : ZeroFrom stL.mem hOut := by simpa [hoL] using hrespL.2.2.1
      have hL_pre : ∀ a < b, stL.mem a = mem0 a := fun a ha => by
        have hlt_out : a < hOut := by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega
        have hnfR : ¬ tourFoot R_ord vCap eCap b xR a := fun hf => by
          rcases hf with ⟨h1, _⟩ | hord
          · omega
          · have := hrepR.ordFootGe a hord; simp [ordHandleOf, tourFixedSize] at this; omega
        have hnfC : ¬ tourFoot R_ord vCap eCap b xC a := fun hf => by
          rcases hf with ⟨h1, _⟩ | hord
          · omega
          · have := hrepC.ordFootGe a hord; simp [ordHandleOf, tourFixedSize] at this; omega
        rw [hrespL.2.2.2.1 a hlt_out hnfR, show mClr a = stR.mem a from Function.update_of_ne (Nat.ne_of_lt hlt_out) _ _,
          hfrR a hlt_out hnfC, hpreC a ha]
      obtain ⟨s1, x1, st1, cRest, hrunRest, hr14, hr15, hr16, h1ord, h1F, h1mk, h1rep, h1foot, h1zero, h1pre, hcRest⟩ :=
        ih (i + 1) (tourLink sC e rDrop) xL { stL with regs := r6 } (by omega)
          (by simp [r6, r5, r4, r3, r2, r1, hr4C]) (by simp [r6, r5, r4, r3, r2, r1, hr5C])
          (by simp [r6, r5, r4, r3, r2, r1, hr6C]) (by simp [r6, r5, r4, r3, r2, r1, hr7C])
          (by simp [r6, r5, r4, r3, r2, r1, hr8C]) (by simp [r6])
          hL_ord (by rw [hL_F]; exact hVC) hL_E (by rw [hL_F]; exact htailC) (by rw [hL_F]; exact hheadC)
          (by simp [tourLink, hmkC]) hrepL hL_foot hL_zero hL_pre
      refine ⟨s1, x1, st1, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunRest, rfl⟩)),
        hr14, hr15, hr16, h1ord, h1F, h1mk, h1rep, h1foot, h1zero, h1pre, ?_⟩
      rw [← hlocClr.2] at hcL
      have hmul : (rem + 1) * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap =
          rem * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap +
          (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap := by ring
      have hstep : TOUR_QUERY_MUL * tourLog eCap + TOUR_CUTLINK_MUL * tourLog eCap + 45 ≤
          (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap := by
        have : 45 ≤ 50 * tourLog eCap := by omega
        have : (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap =
            TOUR_QUERY_MUL * tourLog eCap + TOUR_CUTLINK_MUL * tourLog eCap + 50 * tourLog eCap := by ring
        omega
      dsimp only at hcRest
      clear * - hcR hcL hcRest hmul hstep; simp only [Expr.size]; omega
  exact hloop (mem0 fePtr) 0 s0 x0 st0 (by omega) rfl hr5 hr6 hr7 hr8 hr9 hord0 hV0
    (by simp [hE0]) htail0 hhead0 hmk0 hrep0 hfoot0 hzero0 hpre0

/-! ## Stage 3: Moving component roots to `rs` -/

private theorem tourInitChRoots_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b rsPtr hOut rootOfProc chRootProc : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p)
    (hRoot : p.procs[rootOfProc]? = some (tourOpRootOfExactBody C.splay.loop))
    (hCh : p.procs[chRootProc]? = some (tourOpChangeRootBody C.setValNode C.rotateFront))
    (ω : ℕ → Bool) {mem0 : ℕ → ℕ} {recs : List (ℕ × List End)} {fe : List ℕ}
    {s1 : TourAbs} {x1 : TourConcrete R_ord.τ} {st1 : State}
    (hrs_le : rsPtr + 1 + mem0 rsPtr ≤ b)
    (hrs_nd : (readNatList mem0 rsPtr).Nodup)
    (hValidFin : TourValid vCap eCap ⟨ordOfRecords recs, initTourForest recs fe (readNatList mem0 rsPtr), ∅⟩)
    (hord1 : s1.ord = ordOfRecords recs)
    (hF1 : s1.rf.F = (initTourForest recs fe (readNatList mem0 rsPtr)).F)
    (hmk1 : s1.marked = ∅)
    (hrep1 : TourRepAt R_ord vCap eCap b s1 x1 st1.mem)
    (hfoot1 : ∀ a, tourFoot R_ord vCap eCap b x1 a → a < hOut)
    (hzero1 : ZeroFrom st1.mem hOut)
    (hpre1 : ∀ a < b, st1.mem a = mem0 a)
    (hroom : hOut + 2 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hr5 : st1.regs 5 = b) (hr6 : st1.regs 6 = hOut)
    (hr7 : st1.regs 7 = mem0 rsPtr) (hr8 : st1.regs 8 = rsPtr + 1) (hr9 : st1.regs 9 = 0)
    (hr10 : st1.regs 10 = firstEndBase b) (hr11 : st1.regs 11 = keyOfNodeBase b vCap eCap) :
    let rs := readNatList mem0 rsPtr
    let sFin : TourAbs := ⟨ordOfRecords recs, initTourForest recs fe rs, ∅⟩
    ∃ (x2 : TourConcrete R_ord.τ) (st2 : State) (c2 : ℕ),
      Runs w p ω (tourInitChRootsLoop rootOfProc chRootProc) st1 .normal st2 c2 ∧
      st2.regs 6 = hOut ∧
      TourRepAt R_ord vCap eCap b sFin x2 st2.mem ∧
      (∀ a, tourFoot R_ord vCap eCap b x2 a → a < hOut) ∧
      ZeroFrom st2.mem hOut ∧
      (∀ a < b, st2.mem a = mem0 a) ∧
      c2 + (tourRep R_ord vCap eCap).phi b x2 st2.mem ≤
        (tourRep R_ord vCap eCap).phi b x1 st1.mem +
          mem0 rsPtr * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap + 20 := by
  intro rs sFin
  set Ffin := (initTourForest recs fe rs).F
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hloop : ∀ (rem i : ℕ) (sC : TourAbs) (xC : TourConcrete R_ord.τ) (stC : State),
      (hi_sum : i + rem = mem0 rsPtr) →
      stC.regs 5 = b → stC.regs 6 = hOut →
      stC.regs 7 = mem0 rsPtr → stC.regs 8 = rsPtr + 1 → stC.regs 9 = i →
      stC.regs 10 = firstEndBase b → stC.regs 11 = keyOfNodeBase b vCap eCap →
      sC.ord = ordOfRecords recs → sC.rf.F = Ffin → sC.marked = ∅ →
      (∀ j (hj : j < i), rs[j]'(by have := readList_length mem0 (rsPtr + 1) (mem0 rsPtr); dsimp only [rs, readNatList]; omega) ∈ sC.rf.R) →
      TourRepAt R_ord vCap eCap b sC xC stC.mem →
      (∀ a, tourFoot R_ord vCap eCap b xC a → a < hOut) →
      ZeroFrom stC.mem hOut →
      (∀ a < b, stC.mem a = mem0 a) →
      ∃ (x2 : TourConcrete R_ord.τ) (st2 : State) (c : ℕ),
        Runs w p ω (tourInitChRootsLoop rootOfProc chRootProc) stC .normal st2 c ∧
        st2.regs 6 = hOut ∧
        TourRepAt R_ord vCap eCap b sFin x2 st2.mem ∧
        (∀ a, tourFoot R_ord vCap eCap b x2 a → a < hOut) ∧
        ZeroFrom st2.mem hOut ∧
        (∀ a < b, st2.mem a = mem0 a) ∧
        c + (tourRep R_ord vCap eCap).phi b x2 st2.mem ≤
          (tourRep R_ord vCap eCap).phi b xC stC.mem +
            rem * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro i sC xC stC hi _ hr6C hr7C _ hr9C _ _ hordC hFC hmkC hRsIn hrepC hfootC hzC hpreC
      have hi_eq : i = mem0 rsPtr := by omega
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stC = some 0 := by
        simp [Expr.eval, hr9C, hr7C, hi_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hR_eq : sC.rf.R = rs.toFinset := by
        ext r; constructor
        · intro hrC
          have hrV : r ∈ Ffin.V := hFC ▸ hrepC.valid.roots_sub hrC
          obtain ⟨r', ⟨hr'R, hrr'⟩, _⟩ := hValidFin.unique_root r hrV
          have hr'In : r' ∈ sC.rf.R := by
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hr'R)
            have hlen : rs.length = mem0 rsPtr := readList_length mem0 (rsPtr + 1) (mem0 rsPtr)
            dsimp only [rs] at hj hlen
            exact hRsIn j (by omega)
          have hreq : r = r' := (hrepC.valid.unique_root r (hFC ▸ hrV)).unique
            ⟨hrC, connected_refl _ r⟩ ⟨hr'In, hFC ▸ hrr'⟩
          exact hreq ▸ hr'R
        · intro hr
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hr)
          have hlen : rs.length = mem0 rsPtr := readList_length mem0 (rsPtr + 1) (mem0 rsPtr)
          dsimp only [rs] at hj hlen
          exact hRsIn j (by omega)
      have hsEq : sC = sFin := by
        cases sC with | mk o rf mk =>
          cases rf with | mk F R =>
            dsimp only at hordC hFC hmkC hR_eq
            subst hordC; subst hFC; subst hmkC; subst hR_eq; rfl
      exact ⟨xC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr6C, hsEq ▸ hrepC, hfootC, hzC, hpreC, by simp [Expr.size]; omega⟩
    | succ rem ih =>
      intro i sC xC stC hi hr5C hr6C hr7C hr8C hr9C hr10C hr11C hordC hFC hmkC hRsIn hrepC hfootC hzC hpreC
      have hi_lt : i < mem0 rsPtr := by omega
      have hrs_len : rs.length = mem0 rsPtr := readList_length mem0 (rsPtr + 1) (mem0 rsPtr)
      set rNew := rs[i]'(by omega)
      have hrNew_mem : rNew ∈ rs := List.getElem_mem (by omega)
      have hrNew_Rfin : rNew ∈ (initTourForest recs fe rs).R := List.mem_toFinset.mpr hrNew_mem
      have hrNew_V : rNew ∈ Ffin.V := hValidFin.roots_sub hrNew_Rfin
      have hrNew_lt : rNew < vCap := hValidFin.verts_lt rNew hrNew_V
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stC = some 1 := by
        simp [Expr.eval, hr9C, hr7C, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hmem_r : stC.mem (rsPtr + 1 + i) = rNew := by
        rw [hpreC _ (by omega)]; simp [rNew, rs, readNatList, readList_getElem]
      set feR := stC.mem (firstEndBase b + rNew)
      set r1 := Function.update stC.regs 12 rNew
      set r2 := Function.update r1 13 feR
      have ha12 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 8) (rIdx := 9)
        (base := rsPtr + 1) (idx := i) (val := rNew) (st := stC) hr8C hr9C
        (by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega) hmem_r
      have ha13 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 10) (rIdx := 12)
        (base := firstEndBase b) (idx := rNew) (val := feR) (st := { stC with regs := r1 })
        (by simp [r1, hr10C]) (by simp [r1])
        (by have := hrepC.fixed_le_heap hfootC; simp [firstEndBase, ordHandleOf, tourFixedSize] at this ⊢; omega) rfl
      -- Branch on `feR = 0` vs `feR ≠ 0`
      have hstep : ∃ (sN : TourAbs) (xN : TourConcrete R_ord.τ) (stN : State) (cB : ℕ),
          Runs w p ω (.cond (.reg 13)
            (.assign 14 (.load (.bin .add (.reg 11) (.reg 13))) ;;
             .call 15 rootOfProc [.reg 5, .reg 14, .reg 6] ;;
             .assign 14 (.load (.reg 6)) ;;
             .store (.reg 6) (.const 0) ;;
             .call 15 chRootProc [.reg 5, .reg 14, .reg 12, .reg 6]) .nop)
            { stC with regs := r2 } .normal stN cB ∧
          (∀ k < 12, stN.regs k = stC.regs k) ∧
          sN.ord = ordOfRecords recs ∧ sN.rf.F = Ffin ∧ sN.marked = ∅ ∧
          (∀ j (hj : j < i + 1), rs[j]'(by omega) ∈ sN.rf.R) ∧
          TourRepAt R_ord vCap eCap b sN xN stN.mem ∧
          (∀ a, tourFoot R_ord vCap eCap b xN a → a < hOut) ∧
          ZeroFrom stN.mem hOut ∧
          (∀ a < b, stN.mem a = mem0 a) ∧
          cB + (tourRep R_ord vCap eCap).phi b xN stN.mem ≤
            (tourRep R_ord vCap eCap).phi b xC stC.mem +
              (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap := by
        cases ho : sC.ord rNew with
        | nil =>
          have hfe0 : feR = 0 := by simp [feR, hrepC.firstEnd_mem rNew hrNew_lt, ho]
          have hc0 : (Expr.reg 13).eval w { stC with regs := r2 } = some 0 := by simp [Expr.eval, r2, hfe0]
          have hrNew_in_RC : rNew ∈ sC.rf.R := by
            obtain ⟨r0, ⟨hr0R, hr0c⟩, _⟩ := hrepC.valid.unique_root rNew (hFC ▸ hrNew_V)
            by_cases heq : r0 = rNew
            · exact heq ▸ hr0R
            · exfalso
              obtain ⟨e', he'E, he's⟩ := exists_edge_of_connected_ne hr0c (Ne.symm heq)
              have hm := hrepC.valid.compat.mem_ord_of_forest he'E
              rw [he's, ho] at hm; simp at hm
          refine ⟨sC, xC, { stC with regs := r2 }, _,
            tour_runs_cond_false hc0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
            fun k hk => by simp [r2, r1, Function.update_of_ne (by omega : k ≠ 13), Function.update_of_ne (by omega : k ≠ 12)],
            hordC, hFC, hmkC,
            fun j hj => by
              by_cases hji : j = i
              · subst hji; exact hrNew_in_RC
              · exact hRsIn j (by omega),
            hrepC, hfootC, hzC, hpreC, ?_⟩
          have : 10 ≤ (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap := by
            have := Nat.mul_le_mul_left (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) htl; omega
          clear * - this; simp only [Expr.size]; omega
        | cons a0 as0 =>
          have hhd : (sC.ord rNew).head? = some a0 := by simp [ho]
          have ha0_mem : a0 ∈ sC.ord rNew := by simp [ho]
          have hfe_eq : feR = xC.nodeOf (endKey a0) := by simp [feR, hrepC.firstEnd_mem rNew hrNew_lt, hhd]
          have ha0_lt : endKey a0 < 2 * eCap := endKey_lt_two_mul (hrepC.valid.ordWithin.2.2 rNew a0 ha0_mem)
          have hfe_nz : feR ≠ 0 := hfe_eq ▸ (hrepC.active_end rNew hrNew_lt a0 ha0_mem).1
          have hfe_le : feR ≤ xC.numNodes := hfe_eq ▸ (hrepC.nodeOf_mem _ ha0_lt).2
          have hfe_key : xC.keyOf feR = endKey a0 := by rw [hfe_eq]; exact hrepC.nodeOf_keyOf _ ha0_lt (hfe_eq ▸ hfe_nz)
          have hm_kR : stC.mem (keyOfNodeBase b vCap eCap + feR) = endKey a0 := by
            rw [← hfe_key]; exact (hrepC.keyOf_mem feR (by omega) hfe_le).1
          have hc1 : (Expr.reg 13).eval w { stC with regs := r2 } = some feR := by simp [Expr.eval, r2]
          set r3 := Function.update r2 14 (endKey a0)
          have ha14 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 11) (rIdx := 13)
            (base := keyOfNodeBase b vCap eCap) (idx := feR) (val := endKey a0) (st := { stC with regs := r2 })
            (by simp [r2, r1, hr11C]) (by simp [r2])
            (by have := hrepC.numNodes_le; have := hrepC.fixed_le_heap hfootC; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at this ⊢; omega) hm_kR
          -- Call `rootOfExact [b, endKey a0, hOut]`
          obtain ⟨oR, stR, cR, hrunR, hoR, xR, hrepR, hmemR, hzR, hfrR, hfootR, hcR⟩ :=
            tourOp_rootOf_exact_runs (keyX := endKey a0) (heap := hOut) (pos := stC.pos) hLoc C.toTourSplayCoreProcs ω
              hrepC ⟨rNew, by simpa [endOfKey_endKey] using ha0_mem⟩ hfootC hzC (by omega)
          have hcallR := runs_call_regs3 15 5 14 6 (st := { stC with regs := r3 }) hRoot
            (by simp [r3, r2, r1, hr5C]) (by simp [r3]) (by simp [r3, r2, r1, hr6C]) hrunR
          have hsrc_eq : ordSrc sC.ord (endOfKey (endKey a0)) = rNew := by
            rw [endOfKey_endKey]; exact hrepC.valid.compat.ordSrc_eq ha0_mem
          set rOld := sC.rf.root rNew
          have hmemR_val : stR.mem hOut = rOld := by simpa [hsrc_eq, rOld] using hmemR
          set r4 := Function.update r3 15 oR.value
          set r5 := Function.update r4 14 rOld
          set mClr := Function.update stR.mem hOut 0
          have haOld : Runs w p ω (.assign 14 (.load (.reg 6))) { stR with regs := r4 } .normal { stR with regs := r5 } 3 :=
            runs_assign_iff.mpr ⟨rOld, by simp [Expr.eval, r4, r3, r2, r1, hr6C, hmemR_val], rfl, rfl, rfl⟩
          have hstClr : Runs w p ω (.store (.reg 6) (.const 0)) { stR with regs := r5 } .normal { stR with mem := mClr, regs := r5 } 3 :=
            runs_store_iff.mpr ⟨hOut, 0, by simp [Expr.eval, r5, r4, r3, r2, r1, hr6C], by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
          have hfootR_lt : ∀ a, tourFoot R_ord vCap eCap b xR a → a < hOut := fun a ha => hfootC a (hfootR a ha)
          have hlocClr := (tourRep_local hLoc vCap eCap) b sC xR stR.mem mClr fun a ha =>
            (Function.update_of_ne (Nat.ne_of_lt (hfootR_lt a ha)) _ _).symm
          have hzClr : ZeroFrom mClr hOut := fun a ha => by
            dsimp only [mClr]; by_cases hae : a = hOut
            · subst hae; simp
            · rw [Function.update_of_ne hae]; exact hzR a (by rw [hoR]; omega)
          have hrOld_spec := hrepC.valid.root_spec (hFC ▸ hrNew_V)
          -- Call `changeRoot [b, rOld, rNew, hOut]`
          obtain ⟨oCh, stCh, cCh, hrunCh, hoCh, xCh, hrepCh, hrespCh, hcCh⟩ :=
            tourOp_changeRoot_runs (oldRoot := rOld) (newRoot := rNew) (heap := hOut) (pos := stR.pos) hLoc C ω
              (hlocClr.1 hrepR) hrOld_spec.1 hrNew_lt (hFC ▸ hrNew_V) (connected_symm hrOld_spec.2) hw (by omega)
              hfootR_lt hzClr hroom
          have hcallCh := runs_call_regs4 15 5 14 12 6 (st := { stR with mem := mClr, regs := r5 }) hCh
            (by simp [r5, r4, r3, r2, r1, hr5C]) (by simp [r5]) (by simp [r5, r4, r3, r2, r1])
            (by simp [r5, r4, r3, r2, r1, hr6C]) hrunCh
          set r6 := Function.update r5 15 oCh.value
          have hCh_foot : ∀ a, tourFoot R_ord vCap eCap b xCh a → a < hOut := fun a ha => by
            rcases hrespCh.2.2.2.2 a ha with h1 | ⟨h1, h2⟩
            · exact hfootR_lt a h1
            · omega
          have hCh_zero : ZeroFrom stCh.mem hOut := by simpa [hoCh] using hrespCh.2.2.1
          have hCh_pre : ∀ a < b, stCh.mem a = mem0 a := fun a ha => by
            have hlt_out : a < hOut := by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega
            have hnfR : ¬ tourFoot R_ord vCap eCap b xR a := fun hf => by
              rcases hf with ⟨h1, _⟩ | hord; omega; have := hrepR.ordFootGe a hord; simp [ordHandleOf, tourFixedSize] at this; omega
            have hnfC : ¬ tourFoot R_ord vCap eCap b xC a := fun hf => by
              rcases hf with ⟨h1, _⟩ | hord; omega; have := hrepC.ordFootGe a hord; simp [ordHandleOf, tourFixedSize] at this; omega
            rw [hrespCh.2.2.2.1 a hlt_out hnfR, show mClr a = stR.mem a from Function.update_of_ne (Nat.ne_of_lt hlt_out) _ _,
              hfrR a hlt_out hnfC, hpreC a ha]
          refine ⟨tourChangeRoot sC rOld rNew, xCh, { stCh with regs := r6 }, _,
            tour_runs_cond_true hc1 hfe_nz (tour_runs_seq_normal ha14 (tour_runs_seq_normal hcallR
              (tour_runs_seq_normal haOld (tour_runs_seq_normal hstClr hcallCh)))),
            fun k hk => by simp [r6, r5, r4, r3, r2, r1, Function.update_of_ne (by omega : k ≠ 15),
              Function.update_of_ne (by omega : k ≠ 14), Function.update_of_ne (by omega : k ≠ 13),
              Function.update_of_ne (by omega : k ≠ 12)],
            hordC, hFC, hmkC,
            fun j hj => by
              simp only [tourChangeRoot, Finset.mem_insert, Finset.mem_erase]
              by_cases hji : j = i
              · subst hji; exact Or.inl rfl
              · right; refine ⟨?_, hRsIn j (by omega)⟩
                intro heq
                have hconn_ji : Ffin.Connected rNew (rs[j]'(by omega)) := by
                  rw [← hFC, heq]; exact hrOld_spec.2
                have hj_in : rs[j]'(by omega) ∈ (initTourForest recs fe rs).R := List.mem_toFinset.mpr (List.getElem_mem _)
                have heq_r : rNew = rs[j]'(by omega) := (hValidFin.unique_root rNew hrNew_V).unique
                  ⟨hrNew_Rfin, connected_refl _ rNew⟩ ⟨hj_in, hconn_ji⟩
                have := (List.Nodup.getElem_inj_iff hrs_nd).mp heq_r
                omega,
            hrepCh, hCh_foot, hCh_zero, hCh_pre, ?_⟩
          rw [← hlocClr.2] at hcCh
          have h45 : TOUR_QUERY_MUL * tourLog eCap + TOUR_FOREST_MUL * tourLog eCap + 40 ≤
              (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap := by
            have : 40 ≤ 45 * tourLog eCap := by omega
            have : (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap =
                TOUR_QUERY_MUL * tourLog eCap + TOUR_FOREST_MUL * tourLog eCap + 45 * tourLog eCap := by ring
            omega
          clear * - hcR hcCh h45; simp only [Expr.size]; omega
      obtain ⟨sN, xN, stN, cB, hrunB, hrN_lt, hNord, hNF, hNmk, hNrs, hNrep, hNfoot, hNzero, hNpre, hcB⟩ := hstep
      set rFin := Function.update stN.regs 9 (i + 1)
      have haInc : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) stN .normal { stN with regs := rFin } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, hrN_lt 9 (by omega), hr9C, BinOp.eval, (by omega : 1 < 2 ^ w),
          (by have := hrepC.fixed_le_heap hfootC; simp [ordHandleOf, tourFixedSize] at this; omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 (tour_runs_seq_normal hrunB haInc))
      obtain ⟨x2, st2, cRest, hrunRest, hr26, h2rep, h2foot, h2zero, h2pre, hcRest⟩ :=
        ih (i + 1) sN xN { stN with regs := rFin } (by omega)
          (by simp [rFin, hrN_lt 5 (by omega), hr5C]) (by simp [rFin, hrN_lt 6 (by omega), hr6C])
          (by simp [rFin, hrN_lt 7 (by omega), hr7C]) (by simp [rFin, hrN_lt 8 (by omega), hr8C])
          (by simp [rFin]) (by simp [rFin, hrN_lt 10 (by omega), hr10C])
          (by simp [rFin, hrN_lt 11 (by omega), hr11C])
          hNord hNF hNmk hNrs hNrep hNfoot hNzero hNpre
      refine ⟨x2, st2, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunRest, rfl⟩)),
        hr26, h2rep, h2foot, h2zero, h2pre, ?_⟩
      have hmul : (rem + 1) * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap =
          rem * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap +
          (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap := by ring
      have hstep' : (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap + 35 ≤
          (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap := by
        have : 35 ≤ 35 * tourLog eCap := by omega
        have : (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap =
            (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 45) * tourLog eCap + 35 * tourLog eCap := by ring
        omega
      dsimp only at hcRest
      clear * - hcB hcRest hmul hstep'; simp only [Expr.size]; omega
  exact hloop (mem0 rsPtr) 0 s1 x1 st1 (by omega) hr5 hr6 hr7 hr8 hr9 hr10 hr11 hord1 hF1 hmk1
    (fun _ h => by omega) hrep1 hfoot1 hzero1 hpre1

/-! ## Complete `tourInitBody` run theorem -/

/-- Base cost multiplier for `tourInitBody` (excluding the embedded `ordStore` init multiplier). -/
def TOUR_INIT_BASE_MUL : ℕ :=
  TOUR_INIT1_BASE_MUL + 2 * TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + TOUR_FOREST_MUL + 500

/-- Verified run theorem for `tourInitBody [vCap, eCap, ordPtr, fePtr, rsPtr, heap]`, meeting
`tourContract.initPost`, `tourContract.initCost`, and linear space
`tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3`. -/
theorem tourInitBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord ordPtr fePtr rsPtr b ordWords pos ordInit
      stage1Proc rootOfProc linkProc lsProc chRootProc : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hOrdInitSpace : alloc_ord 3 [vCap, eCap, ordPtr, ordHandleOf b vCap eCap] ≤ ordArenaSize vCap eCap)
    (hStage1 : p.procs[stage1Proc]? = some (tourInitStage1Body ordInit C.initNode C.join))
    (hRoot : p.procs[rootOfProc]? = some (tourOpRootOfExactBody C.splay.loop))
    (hls : p.procs[lsProc]? = some (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join))
    (hLink : p.procs[linkProc]? = some (tourOpLinkBody lsProc C.rootTagOf C.setValNode C.rotateFront))
    (hCh : p.procs[chRootProc]? = some (tourOpChangeRootBody C.setValNode C.rotateFront))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hOrdAt : OrdListAt mem ordPtr (readOrd mem ordPtr) ordWords)
    (hOrdLe : ordPtr + ordWords ≤ b)
    (hFeLe : fePtr + 1 + mem fePtr ≤ b)
    (hRsLe : rsPtr + 1 + mem rsPtr ≤ b)
    (hFeNd : (readNatList mem fePtr).Nodup)
    (hRsNd : (readNatList mem rsPtr).Nodup)
    (hValid : TourValid vCap eCap
      ⟨readOrd mem ordPtr,
        initTourForest (readOrdRecordsAt mem ordPtr) (readNatList mem fePtr) (readNatList mem rsPtr), ∅⟩)
    (hzero : ZeroFrom mem b)
    (hroom : b + (tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3) < 2 ^ w) :
    let sFin : TourAbs :=
      ⟨readOrd mem ordPtr,
        initTourForest (readOrdRecordsAt mem ordPtr) (readNatList mem fePtr) (readNatList mem rsPtr), ∅⟩
    ∃ (o : Outcome) (st' : State) (c : ℕ) (x' : TourConcrete R_ord.τ),
      Runs w p ω (tourInitBody stage1Proc rootOfProc linkProc chRootProc)
        (startState [vCap, eCap, ordPtr, fePtr, rsPtr, b] mem pos) o st' c ∧
      (tourRep R_ord vCap eCap).rep b sFin x' st'.mem ∧
      (tourRep R_ord vCap eCap).Respects (fun _ => False) b
        (tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3) mem o.value b x' st'.mem ∧
      c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
        (TOUR_INIT_BASE_MUL + mul_ord) *
          (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr) + mem fePtr + mem rsPtr) * tourLog eCap := by
  intro sFin
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hwide : 18 ≤ 2 ^ w := by simp [tourFixedSize, ordArenaSize] at hroom; omega
  have hw : vCap + 2 * eCap + 4 < 2 ^ w := by simp [tourFixedSize, ordArenaSize] at hroom; omega
  have hroom1 : b + tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3 < 2 ^ w := by omega
  set s0_st : State := startState [vCap, eCap, ordPtr, fePtr, rsPtr, b] mem pos
  -- Stage 1
  obtain ⟨hOut, st1, c1, x0, hrun1, hhOut_ge, hhOut_le, hz1, hpre1, hfoot1, hrep1, hc1⟩ :=
    tourInitStage1Body_runs (fePtr := fePtr) (pos := pos) C.toTourSplayOpsProcs hOrdImpl hOrdInitSpace ω
      hOrdAt hOrdLe hRsLe hValid hzero hroom1
  have hcall1 := runs_call_regs5 6 0 1 2 4 5 (st := s0_st) hStage1
    (by simp [s0_st, startState]) (by simp [s0_st, startState]) (by simp [s0_st, startState])
    (by simp [s0_st, startState]) (by simp [s0_st, startState]) hrun1
  set r1 := Function.update s0_st.regs 6 hOut
  set r2 := Function.update r1 7 (mem fePtr)
  set r3 := Function.update r2 8 (fePtr + 1)
  set r4 := Function.update r3 9 0
  have ha7 : Runs w p ω (.assign 7 (.load (.reg 3))) { st1 with regs := r1 } .normal { st1 with regs := r2 } 3 :=
    runs_assign_iff.mpr ⟨mem fePtr, by simp [Expr.eval, r1, s0_st, startState, hpre1 fePtr (by omega)], rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 3) (.const 1))) { st1 with regs := r2 } .normal { st1 with regs := r3 } 4 :=
    runs_assign_iff.mpr ⟨fePtr + 1, by simp [Expr.eval, r2, r1, s0_st, startState, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : fePtr + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha9 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 9) (val := 0) (st := { st1 with regs := r3 }) (by omega)
  -- Stage 2
  obtain ⟨s2, x2, st2, c2, hrun2, hr24, hr25, hr26, h2ord, h2F, h2mk, h2rep, h2foot, h2zero, h2pre, hc2⟩ :=
    tourInitLinks_runs (fePtr := fePtr) (hOut := hOut) (st0 := { st1 with regs := r4 })
      hOrdImpl.1 C hRoot hls hLink ω hFeLe hFeNd hValid rfl rfl rfl rfl rfl rfl
      hrep1 hfoot1 hz1 hpre1 (by omega) hw hwide
      (by simp [r4, r3, r2, r1, s0_st, startState]) (by simp [r4, r3, r2, r1])
      (by simp [r4, r3, r2]) (by simp [r4, r3]) (by simp [r4])
  set r5 := Function.update st2.regs 7 (mem rsPtr)
  set r6 := Function.update r5 8 (rsPtr + 1)
  set r7 := Function.update r6 9 0
  set r8 := Function.update r7 10 (firstEndBase b)
  set r9 := Function.update r8 11 (keyOfNodeBase b vCap eCap)
  have hr24_eq : st2.regs 4 = rsPtr := by rw [hr24]; simp [r4, r3, r2, r1, s0_st, startState]
  have ha7b : Runs w p ω (.assign 7 (.load (.reg 4))) st2 .normal { st2 with regs := r5 } 3 :=
    runs_assign_iff.mpr ⟨mem rsPtr, by simp [Expr.eval, hr24_eq, h2pre rsPtr (by omega)], rfl, rfl, rfl⟩
  have ha8b : Runs w p ω (.assign 8 (.bin .add (.reg 4) (.const 1))) { st2 with regs := r5 } .normal { st2 with regs := r6 } 4 :=
    runs_assign_iff.mpr ⟨rsPtr + 1, by simp [Expr.eval, r5, hr24_eq, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : rsPtr + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha9b := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 9) (val := 0) (st := { st2 with regs := r6 }) (by omega)
  have ha10b := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 5) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := { st2 with regs := r7 }) (by simp [r7, r6, r5, hr25])
    (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END, tourFixedSize, ordArenaSize] at hroom ⊢; omega) h2rep.header.2.2.2.2.1
  have ha11b := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 5) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := { st2 with regs := r8 }) (by simp [r8, r7, r6, r5, hr25])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE, tourFixedSize, ordArenaSize] at hroom ⊢; omega) h2rep.header.2.2.2.2.2.2.2.2.1
  -- Stage 3
  obtain ⟨x3, st3, c3, hrun3, hr36, h3rep, h3foot, h3zero, h3pre, hc3⟩ :=
    tourInitChRoots_runs (rsPtr := rsPtr) (hOut := hOut) (st1 := { st2 with regs := r9 })
      hOrdImpl.1 C hRoot hCh ω hRsLe hRsNd hValid h2ord h2F h2mk h2rep h2foot h2zero h2pre (by omega) hw hwide
      (by simp [r9, r8, r7, r6, r5, hr25]) (by simp [r9, r8, r7, r6, r5, hr26])
      (by simp [r9, r8, r7, r6, r5]) (by simp [r9, r8, r7, r6]) (by simp [r9, r8, r7])
      (by simp [r9, r8]) (by simp [r9])
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := st3) (r := 6) (v := hOut) hr36
  have hb_le_hOut : b ≤ hOut := by simp [ordHandleOf, tourFixedSize] at hhOut_ge; omega
  refine ⟨.returned hOut, st3, _, x3,
    tour_runs_seq_normal hcall1 (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9
      (tour_runs_seq_normal hrun2 (tour_runs_seq_normal ha7b (tour_runs_seq_normal ha8b (tour_runs_seq_normal ha9b
        (tour_runs_seq_normal ha10b (tour_runs_seq_normal ha11b (tour_runs_seq_normal hrun3 hret)))))))))),
    h3rep,
    ⟨hb_le_hOut, by simp only [Outcome.value]; omega, h3zero, fun a ha _ => h3pre a ha,
     fun a ha => Or.inr ⟨by
       rcases ha with ⟨h1, _⟩ | hord
       · exact h1
       · have := h3rep.ordFootGe a hord; simp [ordHandleOf, tourFixedSize] at this; omega,
       h3foot a ha⟩⟩, ?_⟩
  set W := ordRecordsWords (readOrdRecordsAt mem ordPtr)
  set F := mem fePtr
  set R := mem rsPtr
  have h1_le : (TOUR_INIT1_BASE_MUL + mul_ord) * (1 + W + R) * tourLog eCap ≤
      (TOUR_INIT1_BASE_MUL + mul_ord) * (1 + W + F + R) * tourLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h2_le : F * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * tourLog eCap ≤
      (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * (1 + W + F + R) * tourLog eCap := by
    have : F * (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) = (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * F := Nat.mul_comm _ _
    rw [this]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h3_le : R * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * tourLog eCap ≤
      (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * (1 + W + F + R) * tourLog eCap := by
    have : R * (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) = (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * R := Nat.mul_comm _ _
    rw [this]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h4_le : 200 ≤ 200 * (1 + W + F + R) * tourLog eCap := by
    have : 1 ≤ (1 + W + F + R) * tourLog eCap := Nat.mul_pos (by omega) htl
    calc 200 = 200 * 1 := by ring
      _ ≤ 200 * ((1 + W + F + R) * tourLog eCap) := Nat.mul_le_mul_left 200 this
      _ = 200 * (1 + W + F + R) * tourLog eCap := by ring
  have htot : (TOUR_INIT1_BASE_MUL + mul_ord) * (1 + W + F + R) * tourLog eCap +
      (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) * (1 + W + F + R) * tourLog eCap +
      (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) * (1 + W + F + R) * tourLog eCap +
      200 * (1 + W + F + R) * tourLog eCap ≤
      (TOUR_INIT_BASE_MUL + mul_ord) * (1 + W + F + R) * tourLog eCap := by
    have hcoeff : TOUR_INIT1_BASE_MUL + mul_ord + (TOUR_QUERY_MUL + TOUR_CUTLINK_MUL + 50) +
        (TOUR_QUERY_MUL + TOUR_FOREST_MUL + 80) + 200 ≤ TOUR_INIT_BASE_MUL + mul_ord := by
      unfold TOUR_INIT_BASE_MUL TOUR_INIT1_BASE_MUL TOUR_QUERY_MUL TOUR_CUTLINK_MUL TOUR_FOREST_MUL
      omega
    have hsum := Nat.mul_le_mul_right ((1 + W + F + R) * tourLog eCap) hcoeff
    linarith
  dsimp only at hc2 hc3
  clear * - hc1 hc2 hc3 h1_le h2_le h3_le h4_le htot
  omega

end MinCostFlow.SparseCore.Program
