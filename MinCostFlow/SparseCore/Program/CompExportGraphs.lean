module

public import MinCostFlow.SparseCore.Program.CompExportGraphsInner
import WordRAM.Tactic

/-!
# Branch Tree-Edge Export Loop (`CompExportGraphs`)

Implements and verifies `compExpTEdgesStmt` / `compExpTEdges_runs` for `op 6`
(`compExportBranchProc`): iterates `ec = 0 .. numEdgeful - 1` over all edgeful components and
emits every surviving original tree edge `(f, T.tail f, T.head f)` (`f ∈ (compSt C).T_cur.E` with
`f ∈ (compSt C).G.E` and `f ∉ cs.insertedGlobal`) contiguously at `tEPtr` in
`≤ 95 * (S j).G.n + 95 * x.numEdgeful + 45` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Statement definitions -/

/-- Iterate `ec = 0 .. numEdgeful - 1` and emit all triples `(f, T.tail f, T.head f)` of `(S j).T.E`
starting at `r3 = tEPtr`, accumulating `r4 = tCount` (`(S j).T.m`).
Inputs: `r0 = b`, `r1 = j`, `r2 = k`, `r3 = tEPtr`. Preserves `r0..r3`; writes `r4 = (S j).T.m`.
Uses scratch registers `5..20`. -/
def compExpTEdgesStmt : Stmt :=
  .assign 4 (.const 0) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffNumEdgeful))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const compOffECap))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr))) ;;
  .assign 10 (.const 0) ;;
  .loop (.bin .lt (.reg 10) (.reg 5))
    (.assign 11 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 10) (.reg 2)) (.reg 1)))) ;;
     .assign 12 (.load (.bin .add (.reg 11) (.const lsfOffTPtr))) ;;
     .assign 13 (.load (.bin .add (.reg 12) (.const tOffM))) ;;
     .assign 14 (.load (.bin .add (.reg 12) (.const tOffOrigIdPtr))) ;;
     .assign 11 (.load (.bin .add (.reg 11) (.const lsfOffDgGPtr))) ;;
     .assign 12 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 4) (.reg 7))) ;;
     .assign 15 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 7))) ;;
     .assign 16 (.bin .add (.reg 15) (.bin .mul (.const 3) (.reg 8))) ;;
     .assign 17 (.bin .add (.reg 16) (.reg 8)) ;;
     .assign 18 (.const 0) ;;
     compExpTEdgesInnerStmt ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

lemma compExpTEdgesStmt_noRand : compExpTEdgesStmt.NoRand := by
  simp [compExpTEdgesStmt, compExpTEdgesInnerStmt, Stmt.NoRand]

/-! ## 2. Outer-loop verification -/

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compExpTEdgesStmt`: emits all `(S j).T.m` surviving original tree-edge
triples of `(S j).T.E` contiguously at `tEPtr`, sets `reg 4 = (S j).T.m`, preserves memory
outside `[tEPtr, tEPtr + 3 * (S j).T.m)`, and runs in `≤ 95 * (S j).G.n + 95 * x.numEdgeful + 45`
steps. -/
theorem compExpTEdges_runs {W : LSFWindowImpl} {w k b tEPtr : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {st : State} {ω : ℕ → Bool} (j : Fin k)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepAt W k b S x st.mem)
    (hend_le : x.endAddr ≤ tEPtr)
    (hbuf_w : tEPtr + 3 * x.m0Total < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = j.1) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = tEPtr) :
    ∃ st' c, ∃ eT : List (ℕ × ℕ × ℕ),
      Runs w p ω compExpTEdgesStmt st .normal st' c ∧
      (∀ r < 4, st'.regs r = st.regs r) ∧
      st'.regs 4 = (S j).T.m ∧
      eT.length = (S j).T.m ∧
      (eT.map Prod.fst).Nodup ∧
      (∀ t ∈ eT, t.1 ∈ (S j).T.E ∧ t.2.1 = (S j).T.tail t.1 ∧ t.2.2 = (S j).T.head t.1) ∧
      (∀ e ∈ (S j).T.E, ∃ t ∈ eT, t.1 = e) ∧
      (∀ i (hi : i < eT.length),
        st'.mem (tEPtr + 3 * i) = eT[i].1 ∧
        st'.mem (tEPtr + 3 * i + 1) = eT[i].2.1 ∧
        st'.mem (tEPtr + 3 * i + 2) = eT[i].2.2) ∧
      (∀ a, a < tEPtr ∨ tEPtr + 3 * (S j).T.m ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 95 * (S j).G.n + 95 * x.numEdgeful + 45 := by
  obtain ⟨hk, _, _, _, _, _, _, _, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩, hm0Tot, hT,
    hCompMeta, hEfMeta, _, _, hFlags, _, _, _, hWins, _⟩ := hrep
  have hIj := (hBr j).1
  have hS_G0 := (hBr j).2.1
  have hIns_j := (hBr j).2.2.2.2.2.1
  have ⟨_, hTE_eq, hT_ends, hT_disj, hTm_le, hTsum_le⟩ := compLSF_T_eq_edgeful hIj
  have hTm_le_m0 : (S j).T.m ≤ x.m0Total := by rw [← hm0Tot, ← hS_G0]; exact hTm_le
  have hefComp_inj : Function.Injective x.edgefulComp := fun ec₁ ec₂ heq => by
    have h1 := (hEfMeta ec₁).2; have h2 := (hEfMeta ec₂).2; rw [heq] at h1; exact Fin.ext (h1.symm.trans h2)
  have hbij_ef : ∀ C, C ∈ edgefulComps (S j).G₀ ↔ ∃ ec : Fin x.numEdgeful, x.compOf (x.edgefulComp ec) = C := fun C => by
    simp only [edgefulComps, Finset.mem_filter, hS_G0]
    constructor
    · rintro ⟨hC, hpos⟩
      obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
      obtain ⟨ec, _, _, hcomp⟩ := (hCompMeta c).2.2.2 hpos
      exact ⟨ec, congrArg x.compOf hcomp⟩
    · rintro ⟨ec, rfl⟩
      exact ⟨hT.compOf_mem _, (hEfMeta ec).1⟩
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    dsimp only [compStaticSize, compHdrSize] at hStat ⊢; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  -- Per-edgeful-component emitted list
  let ecEList : Fin x.numEdgeful → List (ℕ × ℕ × ℕ) := fun ec =>
    let C := x.compOf (x.edgefulComp ec)
    let kept := (x.winConc ec j).tOrigList.filter fun f =>
      decide (f ∈ ((S j).compSt C).G.E ∧ f ∉ (S j).insertedGlobal)
    kept.map fun f => (f, ((S j).compSt C).G.tail f, ((S j).compSt C).G.head f)
  have hec_spec : ∀ ec : Fin x.numEdgeful,
      let C := x.compOf (x.edgefulComp ec)
      let stC := (S j).compSt C
      ((ecEList ec).map Prod.fst).Nodup ∧
      (∀ t ∈ ecEList ec, t.1 ∈ stC.T_cur.E ∧ t.1 ∈ stC.G.E ∧ t.1 ∉ (S j).insertedGlobal ∧
        t.2.1 = stC.G.tail t.1 ∧ t.2.2 = stC.G.head t.1) ∧
      (∀ f ∈ stC.T_cur.E, f ∈ stC.G.E → f ∉ (S j).insertedGlobal → ∃ t ∈ ecEList ec, t.1 = f) ∧
      (ecEList ec).length ≤ stC.T_cur.m := by
    intro ec C stC
    obtain ⟨_, hWrep, _, _, _, _, _⟩ := hWins ec j
    have hTcurE : stC.T_cur.E = stC.T₀.E := hWrep.2.2.2.2.2.2.1.hT_cur_E
    rcases hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with
      ⟨_, _, _, _, _, _, _, _, _, hnd, hmem0, _, _⟩
    have hmem : ∀ f, f ∈ (x.winConc ec j).tOrigList ↔ f ∈ stC.T_cur.E := fun f =>
      (hmem0 f).trans (by rw [hTcurE])
    have hmap_fst : (ecEList ec).map Prod.fst =
        (x.winConc ec j).tOrigList.filter fun f => decide (f ∈ stC.G.E ∧ f ∉ (S j).insertedGlobal) := by
      simp [ecEList, C, stC, List.map_map, Function.comp_def]
    refine ⟨by rw [hmap_fst]; exact hnd.filter _, fun t ht => ?_, fun f hf hfG hfNI => ?_, ?_⟩
    · simp only [ecEList, List.mem_map, List.mem_filter, decide_eq_true_eq] at ht
      obtain ⟨f, ⟨hfL, hfG, hfNI⟩, rfl⟩ := ht
      exact ⟨(hmem f).mp hfL, hfG, hfNI, rfl, rfl⟩
    · refine ⟨(f, stC.G.tail f, stC.G.head f), ?_, rfl⟩
      simp only [ecEList, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨f, ⟨(hmem f).mpr hf, hfG, hfNI⟩, rfl⟩
    · have hlenT : (x.winConc ec j).tOrigList.length = stC.T_cur.m := by
        rw [← List.toFinset_card_of_nodup hnd]
        have hfs : (x.winConc ec j).tOrigList.toFinset = stC.T_cur.E := by
          ext f; simp [List.mem_toFinset, hmem]
        rw [hfs]; rfl
      simpa [ecEList, C, stC, ← hlenT] using List.length_filter_le _ _
  -- Prefix (7 assigns)
  let s1 : State := { st with regs := Function.update st.regs 4 0 }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 x.numEdgeful }
  let s3 : State := { s2 with regs := Function.update s2.regs 6 (compHandlesBase b x.vCap x.eCap x.L_w) }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 x.vCap }
  let s5 : State := { s4 with regs := Function.update s4.regs 8 x.eCap }
  let s6 : State := { s5 with regs := Function.update s5.regs 9 (compIsInsBase b x.vCap x.eCap) }
  let s7 : State := { s6 with regs := Function.update s6.regs 10 0 }
  have hp1 : Runs w p ω (.assign 4 (.const 0)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffNumEdgeful)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨x.numEdgeful, Expr.eval_load_of_eq (by
      have := hb_off compOffNumEdgeful (by decide); simp [s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨compHandlesBase b x.vCap x.eCap x.L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffHandlesPtr (by decide); simp [s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffVCap (by decide); simp [s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.1, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const compOffECap)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨x.eCap, Expr.eval_load_of_eq (by
      have := hb_off compOffECap (by decide); simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨compIsInsBase b x.vCap x.eCap, Expr.eval_load_of_eq (by
      have := hb_off compOffIsInsPtr (by decide); simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 10 (.const 0)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Outer loop
  let outerLoop : Stmt :=
    .loop (.bin .lt (.reg 10) (.reg 5))
      (.assign 11 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 10) (.reg 2)) (.reg 1)))) ;;
       .assign 12 (.load (.bin .add (.reg 11) (.const lsfOffTPtr))) ;;
       .assign 13 (.load (.bin .add (.reg 12) (.const tOffM))) ;;
       .assign 14 (.load (.bin .add (.reg 12) (.const tOffOrigIdPtr))) ;;
       .assign 11 (.load (.bin .add (.reg 11) (.const lsfOffDgGPtr))) ;;
       .assign 12 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 4) (.reg 7))) ;;
       .assign 15 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 7))) ;;
       .assign 16 (.bin .add (.reg 15) (.bin .mul (.const 3) (.reg 8))) ;;
       .assign 17 (.bin .add (.reg 16) (.reg 8)) ;;
       .assign 18 (.const 0) ;;
       compExpTEdgesInnerStmt ;;
       .assign 10 (.bin .add (.reg 10) (.const 1)))
  let prefList : ℕ → List (ℕ × ℕ × ℕ) := fun n =>
    (List.finRange x.numEdgeful |>.take n).flatMap ecEList
  let fullList : List (ℕ × ℕ × ℕ) := prefList x.numEdgeful
  let sufTCur : ℕ → ℕ := fun n =>
    ((Finset.univ : Finset (Fin x.numEdgeful)).filter fun ec => n ≤ ec.1).sum fun ec =>
      ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.m
  have hnd_full : (fullList.map Prod.fst).Nodup := by
    have hflat : fullList.map Prod.fst =
        (List.finRange x.numEdgeful).flatMap (fun ec => (ecEList ec).map Prod.fst) := by
      simp [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful),
        List.map_flatMap]
    rw [hflat, List.nodup_flatMap]
    refine ⟨fun ec _ => (hec_spec ec).1, (List.nodup_finRange x.numEdgeful).imp fun {ec₁ ec₂} hne => ?_⟩
    intro e he₁ he₂
    simp only [List.mem_map] at he₁ he₂
    obtain ⟨t₁, ht₁, rfl⟩ := he₁; obtain ⟨t₂, ht₂, heq⟩ := he₂
    have hC₁ : x.compOf (x.edgefulComp ec₁) ∈ edgefulComps (S j).G₀ := (hbij_ef _).mpr ⟨ec₁, rfl⟩
    have hC₂ : x.compOf (x.edgefulComp ec₂) ∈ edgefulComps (S j).G₀ := (hbij_ef _).mpr ⟨ec₂, rfl⟩
    have hneC : x.compOf (x.edgefulComp ec₁) ≠ x.compOf (x.edgefulComp ec₂) := fun h =>
      hne (hefComp_inj (hT.hBij.1 h))
    exact Finset.disjoint_left.mp (hT_disj _ hC₁ _ hC₂ hneC) ((hec_spec ec₁).2.1 t₁ ht₁).1
      (heq ▸ ((hec_spec ec₂).2.1 t₂ ht₂).1)
  have hfull_len : fullList.length = (S j).T.m := by
    have hfs : (fullList.map Prod.fst).toFinset = (S j).T.E := by
      ext e
      simp only [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful),
        List.mem_toFinset, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and, hTE_eq,
        Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨t, ⟨ec, ht⟩, rfl⟩
        have hspec := (hec_spec ec).2.1 t ht
        exact ⟨x.compOf (x.edgefulComp ec), (hbij_ef _).mpr ⟨ec, rfl⟩, hspec.1, hspec.2.1, hspec.2.2.1⟩
      · rintro ⟨C, hC, hfT, hfG, hfNI⟩
        obtain ⟨ec, rfl⟩ := (hbij_ef C).mp hC
        obtain ⟨t, ht, rfl⟩ := (hec_spec ec).2.2.1 e hfT hfG hfNI
        exact ⟨t, ⟨ec, ht⟩, rfl⟩
    rw [← List.length_map Prod.fst, ← List.toFinset_card_of_nodup hnd_full, hfs]; rfl
  have hsub_len : ∀ n, (prefList n).length ≤ (S j).T.m := fun n => by
    rw [← hfull_len]
    have hsplit : List.finRange x.numEdgeful =
        (List.finRange x.numEdgeful).take n ++ (List.finRange x.numEdgeful).drop n :=
      (List.take_append_drop n _).symm
    have : fullList.length = (prefList n).length +
        (((List.finRange x.numEdgeful).drop n).flatMap ecEList).length := by
      conv_lhs =>
        simp only [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful)]
        rw [hsplit, List.flatMap_append, List.length_append]
    omega
  have hloop : ∀ rem n (s : State) (hn : n ≤ x.numEdgeful), x.numEdgeful - n = rem →
      (∀ r < 4, s.regs r = st.regs r) →
      s.regs 4 = (prefList n).length → s.regs 5 = x.numEdgeful →
      s.regs 6 = compHandlesBase b x.vCap x.eCap x.L_w → s.regs 7 = x.vCap →
      s.regs 8 = x.eCap → s.regs 9 = compIsInsBase b x.vCap x.eCap → s.regs 10 = n →
      (∀ q (hq : q < (prefList n).length),
        s.mem (tEPtr + 3 * q) = (prefList n)[q].1 ∧
        s.mem (tEPtr + 3 * q + 1) = (prefList n)[q].2.1 ∧
        s.mem (tEPtr + 3 * q + 2) = (prefList n)[q].2.2) →
      (∀ a, a < tEPtr ∨ tEPtr + 3 * (prefList n).length ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω outerLoop s .normal st' c ∧
        (∀ r < 4, st'.regs r = st.regs r) ∧
        st'.regs 4 = fullList.length ∧
        (∀ q (hq : q < fullList.length),
          st'.mem (tEPtr + 3 * q) = fullList[q].1 ∧
          st'.mem (tEPtr + 3 * q + 1) = fullList[q].2.1 ∧
          st'.mem (tEPtr + 3 * q + 2) = fullList[q].2.2) ∧
        (∀ a, a < tEPtr ∨ tEPtr + 3 * fullList.length ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 95 * sufTCur n + 95 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro n s hn hrem hr_lt hr4 hr5 hr6 hr7 hr8 hr9 hr10 hdone hfr
      have hn_eq : n = x.numEdgeful := by omega
      subst hn_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr10, hr5],
        rfl, rfl, by simp [Expr.size]⟩), hr_lt, hr4, hdone, hfr, by omega⟩
    | succ rem ih =>
      intro n s hn hrem hr_lt hr4 hr5 hr6 hr7 hr8 hr9 hr10 hdone hfr
      have hn_lt : n < x.numEdgeful := by omega
      let ec : Fin x.numEdgeful := ⟨n, hn_lt⟩
      obtain ⟨hSlot, hWrep, hvW, heW, _, hWlo, hWhi⟩ := hWins ec j
      set hWin := x.winHandle ec j
      set xWin := x.winConc ec j
      have hHdr := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hdgG_W := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hTBlk := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hTcurE_ec : ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E =
          ((S j).compSt (x.compOf (x.edgefulComp ec))).T₀.E := hWrep.2.2.2.2.2.2.1.hT_cur_E
      have hG0_lt_eCap : ∀ e ∈ ((S j).compSt (x.compOf (x.edgefulComp ec))).G₀.E, e < x.eCap :=
        fun e he => heW ▸ hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
      rcases hTBlk with ⟨htM_mem, _, htOrigPtr_mem, _, _, _, _, _, htLen, htNd, htMem0, htLO, _⟩
      have htMem : ∀ f, f ∈ xWin.tOrigList ↔ f ∈ ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E :=
        fun f => (htMem0 f).trans (by rw [hTcurE_ec])
      have hW_end_def : xWin.endAddr hWin = hWin + lsfStaticSize xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w := rfl
      have hW_end_le : xWin.endAddr hWin ≤ tEPtr := le_trans hWhi hend_le
      have hW_hdr_lt : hWin + lsfHdrSize ≤ tEPtr := by
        dsimp only [lsfStaticSize, lsfHdrSize] at hW_end_def hW_end_le ⊢; omega
      set tPtr := lsfTBlockPtr hWin xWin.vCap xWin.eCap
      set dgGPtr := lsfDgGPtr hWin
      set origIdPtr := tOrigIdBase tPtr xWin.vCap xWin.tM
      have hT_hdr_lt : tPtr + tBlockSize xWin.vCap xWin.eCap xWin.tM ≤ tEPtr :=
        le_trans (lsfTBlock_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w).2 hW_end_le
      have hdgG_end_le : dgGPtr + dynGraphSize xWin.vCap xWin.eCap ≤ tEPtr := by
        dsimp only [dgGPtr, lsfDgGPtr, lsfStaticSize] at hW_end_def hW_end_le ⊢; omega
      have hW_hdr16 : hWin + 16 ≤ tEPtr := by dsimp only [lsfHdrSize] at hW_hdr_lt; omega
      have hT_hdr4 : tPtr + 4 ≤ tEPtr := by
        dsimp only [tBlockSize, tHdrSize, dynGraphSize] at hT_hdr_lt; omega
      have hs_below : ∀ a < tEPtr, s.mem a = st.mem a := fun a ha => hfr a (Or.inl ha)
      have hslot_lt : compHandlesBase b x.vCap x.eCap x.L_w + (n * k + j.1) < tEPtr := by
        have h1 : (n + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        have h2 : n * k + j.1 < (n + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd] at hTE; omega
      have hnk_w : n * k < 2 ^ w := by
        have h1 : n * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        dsimp only [compTablesEnd] at hTE; omega
      have hdg_sz : dynGraphSize x.vCap x.eCap = 4 + 7 * x.vCap + 9 * x.eCap := rfl
      have hdgG_end_x : dgGPtr + dynGraphSize x.vCap x.eCap ≤ tEPtr := by rwa [hvW, heW] at hdgG_end_le
      have hr7_w : s.regs 7 = xWin.vCap := hr7.trans hvW.symm
      have hr8_w : s.regs 8 = xWin.eCap := hr8.trans heW.symm
      -- Load component pointers (10 assigns)
      let b1 : State := { s with regs := Function.update s.regs 11 hWin }
      let b2 : State := { b1 with regs := Function.update b1.regs 12 tPtr }
      let b3 : State := { b2 with regs := Function.update b2.regs 13 xWin.tM }
      let b4 : State := { b3 with regs := Function.update b3.regs 14 origIdPtr }
      let b5 : State := { b4 with regs := Function.update b4.regs 11 dgGPtr }
      let b6 : State := { b5 with regs := Function.update b5.regs 12 (dgIntToExtBase dgGPtr x.vCap) }
      let b7 : State := { b6 with regs := Function.update b6.regs 15 (dgEPresBase dgGPtr x.vCap) }
      let b8 : State := { b7 with regs := Function.update b7.regs 16 (dgETailSlotBase dgGPtr x.vCap x.eCap) }
      let b9 : State := { b8 with regs := Function.update b8.regs 17 (dgEHeadSlotBase dgGPtr x.vCap x.eCap) }
      let b10 : State := { b9 with regs := Function.update b9.regs 18 0 }
      have hb1 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 10) (.reg 2)) (.reg 1))))) s .normal b1 9 :=
        runs_assign_iff.mpr ⟨hWin, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr6, hr10, hr_lt 2 (by omega), hr2, hr_lt 1 (by omega), hr1,
            hnk_w, show n * k + j.1 < 2 ^ w by omega,
            show compHandlesBase b x.vCap x.eCap x.L_w + (n * k + j.1) < 2 ^ w by omega])
          ((hs_below _ hslot_lt).trans hSlot), rfl, rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 11) (.const lsfOffTPtr)))) b1 .normal b2 5 :=
        runs_assign_iff.mpr ⟨tPtr, Expr.eval_load_of_eq (by
          simp [b1, Expr.eval, BinOp.eval, lsfOffTPtr, show 5 < 2 ^ w by omega, show hWin + 5 < 2 ^ w by omega])
          ((hs_below _ (by dsimp only [lsfOffTPtr]; omega)).trans hHdr.2.2.2.2.2.1),
          rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 12) (.const tOffM)))) b2 .normal b3 5 :=
        runs_assign_iff.mpr ⟨xWin.tM, Expr.eval_load_of_eq (x := tPtr + tOffM) (by
          simp [b2, Expr.eval, BinOp.eval, tOffM, hw0', show tPtr < 2 ^ w by omega])
          ((hs_below _ (by dsimp only [tOffM]; omega)).trans htM_mem),
          rfl, rfl, by simp [Expr.size]⟩
      have hb4 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 12) (.const tOffOrigIdPtr)))) b3 .normal b4 5 :=
        runs_assign_iff.mpr ⟨origIdPtr, Expr.eval_load_of_eq (x := tPtr + tOffOrigIdPtr) (by
          simp [b3, b2, Expr.eval, BinOp.eval, tOffOrigIdPtr, show 2 < 2 ^ w by omega, show tPtr + 2 < 2 ^ w by omega])
          ((hs_below _ (by dsimp only [tOffOrigIdPtr]; omega)).trans htOrigPtr_mem),
          rfl, rfl, by simp [Expr.size]⟩
      have hb5 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 11) (.const lsfOffDgGPtr)))) b4 .normal b5 5 :=
        runs_assign_iff.mpr ⟨dgGPtr, Expr.eval_load_of_eq (x := hWin + lsfOffDgGPtr) (by
          simp [b4, b3, b2, b1, Expr.eval, BinOp.eval, lsfOffDgGPtr, show 4 < 2 ^ w by omega, show hWin + 4 < 2 ^ w by omega])
          ((hs_below _ (by dsimp only [lsfOffDgGPtr]; omega)).trans hHdr.2.2.2.2.1),
          rfl, rfl, by simp [Expr.size]⟩
      have hb6 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 4) (.reg 7)))) b5 .normal b6 8 :=
        runs_assign_iff.mpr ⟨dgIntToExtBase dgGPtr x.vCap, by
          simp [b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7, hw4, dgIntToExtBase,
            show dgGPtr + 4 < 2 ^ w by omega, show 4 * x.vCap < 2 ^ w by omega,
            show dgGPtr + 4 + 4 * x.vCap < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hb7 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 7)))) b6 .normal b7 8 :=
        runs_assign_iff.mpr ⟨dgEPresBase dgGPtr x.vCap, by
          simp [b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7, hw4, hw7, dgEPresBase,
            show dgGPtr + 4 < 2 ^ w by omega, show 7 * x.vCap < 2 ^ w by omega,
            show dgGPtr + 4 + 7 * x.vCap < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hb8 : Runs w p ω (.assign 16 (.bin .add (.reg 15) (.bin .mul (.const 3) (.reg 8)))) b7 .normal b8 6 :=
        runs_assign_iff.mpr ⟨dgETailSlotBase dgGPtr x.vCap x.eCap, by
          simp [b7, b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr8, hw3, dgEPresBase, dgETailSlotBase,
            show 3 * x.eCap < 2 ^ w by omega, show dgGPtr + 4 + 7 * x.vCap + 3 * x.eCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb9 : Runs w p ω (.assign 17 (.bin .add (.reg 16) (.reg 8))) b8 .normal b9 4 :=
        runs_assign_iff.mpr ⟨dgEHeadSlotBase dgGPtr x.vCap x.eCap, by
          have hadd : dgETailSlotBase dgGPtr x.vCap x.eCap + x.eCap = dgEHeadSlotBase dgGPtr x.vCap x.eCap := by
            dsimp only [dgETailSlotBase, dgEHeadSlotBase]; omega
          simp [b8, b7, b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr8, hadd,
            show dgEHeadSlotBase dgGPtr x.vCap x.eCap < 2 ^ w by dsimp only [dgEHeadSlotBase]; omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb10 : Runs w p ω (.assign 18 (.const 0)) b9 .normal b10 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      -- Run inner loop on component `ec`
      have hC_mem : x.compOf (x.edgefulComp ec) ∈ edgefulComps (S j).G₀ := (hbij_ef _).mpr ⟨ec, rfl⟩
      have hC_comp : x.compOf (x.edgefulComp ec) ∈ components (S j).G₀ := (Finset.mem_filter.mp hC_mem).1
      have htm_eq : xWin.tM = ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.m := by
        rw [← htLen, ← List.toFinset_card_of_nodup htNd]
        have hfs : xWin.tOrigList.toFinset = ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E := by
          ext f; simp [List.mem_toFinset, htMem]
        rw [hfs]; rfl
      have htm_le_m0 : xWin.tM ≤ x.m0Total := by
        rw [htm_eq]
        have hsubE := compLSF_T_cur_E_sub_compEdgeSet hIj hC_comp
        have h1 : ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E.card ≤ (S j).G₀.E.card :=
          Finset.card_le_card fun f hf => (Finset.mem_filter.mp (hsubE hf)).1
        rw [hS_G0] at h1; rw [← hm0Tot]; exact h1
      have hpref_tM_le : (prefList n).length + xWin.tM ≤ x.m0Total := by
        -- Disjointness: `prefList n` edges come from components `< n`, `T_cur` from component `n`, all in `G₀.E`
        have hsub_union : ((prefList n).map Prod.fst).toFinset ∪
            ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E ⊆ (S j).G₀.E := by
          intro e he
          rcases Finset.mem_union.mp he with h1 | h2
          · simp only [prefList, List.mem_toFinset, List.mem_map, List.mem_flatMap] at h1
            obtain ⟨t, ⟨ec', hec', ht⟩, rfl⟩ := h1
            have hC' := (Finset.mem_filter.mp ((hbij_ef _).mpr ⟨ec', rfl⟩)).1
            exact (Finset.mem_filter.mp (compLSF_T_cur_E_sub_compEdgeSet hIj hC' ((hec_spec ec').2.1 t ht).1)).1
          · exact (Finset.mem_filter.mp (compLSF_T_cur_E_sub_compEdgeSet hIj hC_comp h2)).1
        have hdisj_pn : Disjoint ((prefList n).map Prod.fst).toFinset
            ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur.E := by
          rw [Finset.disjoint_left]
          intro e h1 h2
          simp only [prefList, List.mem_toFinset, List.mem_map, List.mem_flatMap] at h1
          obtain ⟨t, ⟨ec', hec', ht⟩, rfl⟩ := h1
          have hec'_lt : ec'.1 < n := by
            have := List.mem_iff_getElem.mp hec'
            obtain ⟨idx, hidx, rfl⟩ := this
            simp only [List.length_take, List.length_finRange] at hidx
            simp [List.getElem_take, List.getElem_finRange]; omega
          have hneC : x.compOf (x.edgefulComp ec') ≠ x.compOf (x.edgefulComp ec) := fun h => by
            have hval := congrArg Fin.val (hefComp_inj (hT.hBij.1 h))
            dsimp only [ec] at hval; omega
          exact Finset.disjoint_left.mp (hT_disj _ ((hbij_ef _).mpr ⟨ec', rfl⟩) _ hC_mem hneC)
            ((hec_spec ec').2.1 t ht).1 h2
        have hnd_p : ((prefList n).map Prod.fst).Nodup := by
          have hsplit : fullList = prefList n ++ ((List.finRange x.numEdgeful).drop n).flatMap ecEList := by
            simp only [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful)]
            rw [← List.flatMap_append, List.take_append_drop]
          rw [hsplit, List.map_append] at hnd_full
          exact hnd_full.of_append_left
        have hcard := Finset.card_le_card hsub_union
        rw [Finset.card_union_of_disjoint hdisj_pn, List.toFinset_card_of_nodup hnd_p, List.length_map] at hcard
        rw [htm_eq, ← hm0Tot, ← hS_G0]; exact hcard
      have hdgG_s : DynGraphAt b10.mem dgGPtr x.vCap x.eCap ((S j).compSt (x.compOf (x.edgefulComp ec))).G := by
        have h1 : DynGraphAt st.mem dgGPtr x.vCap x.eCap ((S j).compSt (x.compOf (x.edgefulComp ec))).G := by
          rwa [hvW, heW] at hdgG_W
        exact dynGraphAt_of_agree h1 fun a ha1 ha2 => hs_below a (by omega)
      have hins_s : ∀ e < x.eCap, b10.mem (compIsInsBase b x.vCap x.eCap + e) =
          if e ∈ (S j).insertedGlobal then 1 else 0 := fun e he => by
        have hlt : compIsInsBase b x.vCap x.eCap + e < tEPtr := by
          dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
            compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
        rw [hs_below _ hlt, (hFlags e he).2, hIns_j]
      have horig_le : origIdPtr + xWin.tM ≤ tEPtr := by
        dsimp only [origIdPtr, tOrigIdBase, tDgTPtr, tBlockSize, tHdrSize] at hT_hdr_lt ⊢; omega
      have hins_le : compIsInsBase b x.vCap x.eCap + x.eCap ≤ tEPtr := by
        dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
          compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
      obtain ⟨b11, cIn, hrunIn, hb11_o, hb11_4, hb11_done, hb11_fr, hcIn⟩ :=
        compExpTEdgesInner_runs (tEPtr := tEPtr) (baseCnt := (prefList n).length)
          (vCap := x.vCap) (eCap := x.eCap) (isInsPtr := compIsInsBase b x.vCap x.eCap)
          (dgGPtr := dgGPtr) (origIdPtr := origIdPtr) (tM := xWin.tM)
          (G_c := ((S j).compSt (x.compOf (x.edgefulComp ec))).G)
          (T_c := ((S j).compSt (x.compOf (x.edgefulComp ec))).T_cur)
          (insSet := (S j).insertedGlobal) (tOrigList := xWin.tOrigList)
          (st := b10) (ω := ω) hw16 htLen htNd htMem
          (fun f hf => hG0_lt_eCap f (by
            have h1 := compLSF_T_cur_E_sub_compEdgeSet hIj hC_comp hf
            rw [(hIj.hCompLSF _ hC_comp).2.1]; exact h1))
          (fun q hq => (hs_below _ (by omega)).trans (htLO q hq))
          hdgG_s hins_s horig_le hdgG_end_x hins_le (by omega)
          (by simp [b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr_lt 3 (by omega), hr3])
          (by simp [b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr4])
          (by simp [b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr9])
          (by simp [b10, b9, b8, b7, b6]) (by simp [b10, b9, b8, b7, b6, b5, b4, b3])
          (by simp [b10, b9, b8, b7, b6, b5, b4]) (by simp [b10, b9, b8, b7])
          (by simp [b10, b9, b8]) (by simp [b10, b9]) (by simp [b10])
      let b12 : State := { b11 with regs := Function.update b11.regs 10 (n + 1) }
      have hb12 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) b11 .normal b12 4 :=
        runs_assign_iff.mpr ⟨n + 1, by
          simp [Expr.eval, BinOp.eval, hb11_o 10 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1,
            hr10, hw1, show n + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal b12 (72 + cIn) :=
        runs_seq_iff.mpr (Or.inr ⟨b1, 9, _, hb1, runs_seq_iff.mpr (Or.inr ⟨b2, 5, _, hb2,
          runs_seq_iff.mpr (Or.inr ⟨b3, 5, _, hb3, runs_seq_iff.mpr (Or.inr ⟨b4, 5, _, hb4,
          runs_seq_iff.mpr (Or.inr ⟨b5, 5, _, hb5, runs_seq_iff.mpr (Or.inr ⟨b6, 8, _, hb6,
          runs_seq_iff.mpr (Or.inr ⟨b7, 8, _, hb7, runs_seq_iff.mpr (Or.inr ⟨b8, 6, _, hb8,
          runs_seq_iff.mpr (Or.inr ⟨b9, 4, _, hb9, runs_seq_iff.mpr (Or.inr ⟨b10, 2, _, hb10,
          runs_seq_iff.mpr (Or.inr ⟨b11, cIn, 4, hrunIn, hb12, rfl⟩),
          rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
      have hnext_list : prefList (n + 1) = prefList n ++ ecEList ec := by
        simp only [prefList, List.take_succ_eq_append_getElem (by simp; omega : n < (List.finRange x.numEdgeful).length),
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getElem_finRange]
        rfl
      have hnext_len : (prefList (n + 1)).length = (prefList n).length + (ecEList ec).length := by
        simp [hnext_list]
      have hsuf_eq : sufTCur n = xWin.tM + sufTCur (n + 1) := by
        rw [htm_eq]
        dsimp only [sufTCur]
        have hpart : (Finset.univ.filter fun ec' : Fin x.numEdgeful => n ≤ ec'.1) =
            insert ec (Finset.univ.filter fun ec' : Fin x.numEdgeful => n + 1 ≤ ec'.1) := by
          ext ec'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, ec]
          constructor
          · intro h; by_cases heq : ec'.1 = n; exact Or.inl (Fin.ext heq); exact Or.inr (by omega)
          · rintro (rfl | h)
            · exact le_refl n
            · exact Nat.le_of_succ_le h
        rw [hpart, Finset.sum_insert (by simp [ec])]
      have hec_eq_in : (List.filter (fun f => decide (f ∈ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.E ∧ f ∉ (S j).insertedGlobal))
          xWin.tOrigList).map (fun f => (f, ((S j).compSt (x.compOf (x.edgefulComp ec))).G.tail f,
          ((S j).compSt (x.compOf (x.edgefulComp ec))).G.head f)) = ecEList ec := rfl
      rw [hec_eq_in] at hb11_4 hb11_fr
      obtain ⟨st', cRest, hrest, hr'_lt, hr'_4, hdone', hfr', hcRest⟩ :=
        ih (n + 1) b12 (by omega) (by omega)
          (fun r hr => by simp [b12, show r ≠ 10 by omega, hb11_o r (by omega) (by omega),
            b10, b9, b8, b7, b6, b5, b4, b3, b2, b1,
            show r ≠ 18 by omega, show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 15 by omega,
            show r ≠ 14 by omega, show r ≠ 13 by omega, show r ≠ 12 by omega, show r ≠ 11 by omega, hr_lt r hr])
          (by simp [b12, hb11_4, hnext_len])
          (by simp [b12, hb11_o 5 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr5])
          (by simp [b12, hb11_o 6 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr6])
          (by simp [b12, hb11_o 7 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr7])
          (by simp [b12, hb11_o 8 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr8])
          (by simp [b12, hb11_o 9 (by omega) (by omega), b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, hr9])
          (by simp [b12])
          (fun q hq => by
            by_cases hqp : q < (prefList n).length
            · have hget : (prefList (n + 1))[q]'hq = (prefList n)[q]'hqp := by
                simp [hnext_list, List.getElem_append_left hqp]
              rw [hget]
              have h1 := hb11_fr (tEPtr + 3 * q) (Or.inl (by omega))
              have h2 := hb11_fr (tEPtr + 3 * q + 1) (Or.inl (by omega))
              have h3 := hb11_fr (tEPtr + 3 * q + 2) (Or.inl (by omega))
              exact ⟨h1.trans (hdone q hqp).1, h2.trans (hdone q hqp).2.1, h3.trans (hdone q hqp).2.2⟩
            · have hq2 : q - (prefList n).length < (ecEList ec).length := by omega
              have hget : (prefList (n + 1))[q]'hq = (ecEList ec)[q - (prefList n).length]'hq2 := by
                simp [hnext_list, List.getElem_append_right (by omega : (prefList n).length ≤ q)]
              rw [hget]
              have hsub := hb11_done (q - (prefList n).length) hq2
              rwa [show (prefList n).length + (q - (prefList n).length) = q by omega] at hsub)
          (fun a ha => by
            rw [hnext_len] at ha
            exact (hb11_fr a (by omega)).trans (hfr a (by omega)))
      have hfull : Runs w p ω outerLoop s .normal st' (72 + cIn + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, b12, 72 + cIn, cRest,
          by simp [Expr.eval, BinOp.eval, hr10, hr5, hn_lt, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 72 + cIn + cRest + 4, hfull, hr'_lt, hr'_4, hdone', hfr', by omega⟩
  obtain ⟨st', cL, hrunL, hr'_lt, hr'_4, hdone', hfr', hcL⟩ :=
    hloop x.numEdgeful 0 s7 (Nat.zero_le _) (Nat.sub_zero _)
      (fun r hr => by simp [s7, s6, s5, s4, s3, s2, s1, show r ≠ 4 by omega, show r ≠ 5 by omega,
        show r ≠ 6 by omega, show r ≠ 7 by omega, show r ≠ 8 by omega, show r ≠ 9 by omega, show r ≠ 10 by omega])
      (by simp [s7, s6, s5, s4, s3, s2, s1, prefList]) (by simp [s7, s6, s5, s4, s3, s2])
      (by simp [s7, s6, s5, s4, s3]) (by simp [s7, s6, s5, s4]) (by simp [s7, s6, s5])
      (by simp [s7, s6]) (by simp [s7])
      (fun _ h => by simp [prefList] at h) (fun _ _ => rfl)
  have hrun : Runs w p ω compExpTEdgesStmt st .normal st' (36 + cL) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, 33 + cL, hp1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 27 + cL, hp2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, 21 + cL, hp3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, 15 + cL, hp4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, 9 + cL, hp5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, 3 + cL, hp6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 2, cL, hp7, hrunL, by omega⟩),
      by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  have hsuf0_le : sufTCur 0 ≤ (S j).G.n := by
    have hsum_eq : sufTCur 0 = (edgefulComps (S j).G₀).sum fun C => ((S j).compSt C).T_cur.m := by
      dsimp only [sufTCur]
      rw [Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
      refine Finset.sum_bij (fun ec _ => x.compOf (x.edgefulComp ec))
        (fun ec _ => (hbij_ef _).mpr ⟨ec, rfl⟩)
        (fun e1 _ e2 _ h => hefComp_inj (hT.hBij.1 h))
        (fun C hC => by obtain ⟨ec, rfl⟩ := (hbij_ef C).mp hC; exact ⟨ec, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    rw [hsum_eq]; exact hTsum_le
  refine ⟨st', 36 + cL, fullList, hrun, hr'_lt, hfull_len ▸ hr'_4, hfull_len, hnd_full, ?_, ?_, hdone',
    hfull_len ▸ hfr', by omega⟩
  · intro t ht
    simp only [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful),
      List.mem_flatMap, List.mem_finRange, true_and] at ht
    obtain ⟨ec, ht⟩ := ht
    have hC := (hbij_ef _).mpr ⟨ec, rfl⟩
    have hsp := (hec_spec ec).2.1 t ht
    have hend := hT_ends _ hC t.1 hsp.1 hsp.2.1 hsp.2.2.1
    refine ⟨?_, hend.1.trans hsp.2.2.2.1.symm |>.symm, hend.2.trans hsp.2.2.2.2.symm |>.symm⟩
    rw [hTE_eq, Finset.mem_biUnion]
    exact ⟨_, hC, Finset.mem_filter.mpr ⟨hsp.1, hsp.2.1, hsp.2.2.1⟩⟩
  · intro e he
    rw [hTE_eq, Finset.mem_biUnion] at he
    obtain ⟨C, hC, hf⟩ := he
    obtain ⟨hfT, hfG, hfNI⟩ := Finset.mem_filter.mp hf
    obtain ⟨ec, rfl⟩ := (hbij_ef C).mp hC
    obtain ⟨t, ht, rfl⟩ := (hec_spec ec).2.2.1 e hfT hfG hfNI
    refine ⟨t, ?_, rfl⟩
    simp only [fullList, prefList, List.take_of_length_le (by simp : (List.finRange x.numEdgeful).length ≤ x.numEdgeful),
      List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨ec, ht⟩

end

end MinCostFlow.SparseCore.Program
