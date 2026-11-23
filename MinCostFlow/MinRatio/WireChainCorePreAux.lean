module

public import MinCostFlow.MinRatio.WireChainCoreOps
public import MinCostFlow.MinRatio.WireChainCoreSyncLoop
public import MinCostFlow.MinRatio.WireSuffixEdits
import WordRAM.Tactic

/-!
# Auxiliary pre-chain batch dichotomy and slot-zeroing helpers (`WireChainCorePreAux`)

Provides:
1. `translateBatch_length_eq` and `refreshBatch_edge_dichotomy`: exact batch-length identity and
   surviving vs. replaced edge dichotomy under `RefreshBatch` and `FreshInv`.
2. `wireZeroSlotsStmt` and `wireZeroSlotsStmt_runs`: zeroes `slots[0..intCap)` (Branch A).
3. `wireZeroInsertedSlotsStmt` and `wireZeroInsertedSlotsStmt_runs`: zeroes `slots[ei]` for every
   `.insert ei _ _` in `U_int` without modifying any surviving tree edge's slot (Branch B).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-! ### 1. Batch length and `RefreshBatch` edge dichotomy -/

/-- `translateBatch` preserves list length on every edge-only batch. -/
theorem translateBatch_length_eq :
    ∀ (U : List Update) (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      (∀ u ∈ U, IsEdgeUpdate u) →
      (translateBatch curExt e2i i2e nf U).2.2.2.2.length = U.length
  | [], _, _, _, _, _ => rfl
  | u :: rest, curExt, e2i, i2e, nf, hE => by
    have hu := hE u List.mem_cons_self
    have hr := fun v hv => hE v (List.mem_cons_of_mem _ hv)
    cases u with
    | insert _ _ _ =>
      simp only [translateBatch, translateUpdate, List.length_cons]
      rw [translateBatch_length_eq rest _ _ _ _ hr]
    | delete _ =>
      simp only [translateBatch, translateUpdate, List.length_cons]
      rw [translateBatch_length_eq rest _ _ _ _ hr]
    | split _ _ _ _ => exact hu.elim

/-- If `x ∈ (H.applyBatch L).E` and no update in `L` inserts `x`, then `x ∈ H.E`. -/
theorem mem_applyBatch_of_no_insert :
    ∀ (L : List Update) (H : MGraph) (x : ℕ),
      x ∈ (H.applyBatch L).E → (¬ ∃ u ∈ L, u.Inserts x) → x ∈ H.E
  | [], _, _, hx, _ => by simpa [MGraph.applyBatch] using hx
  | v :: vs, H, x, hx, hno => by
    have hx' := mem_applyBatch_of_no_insert vs (H.applyUpdate v) x
      (by simpa [MGraph.applyBatch] using hx)
      (fun ⟨w, hw, hwi⟩ => hno ⟨w, List.mem_cons_of_mem _ hw, hwi⟩)
    cases v with
    | delete _ => simp only [MGraph.applyUpdate, Finset.mem_erase] at hx'; exact hx'.2
    | insert a _ _ =>
      simp only [MGraph.applyUpdate, Finset.mem_insert] at hx'
      rcases hx' with rfl | hx''
      · exact (hno ⟨.insert x _ _, List.mem_cons_self, rfl⟩).elim
      · exact hx''
    | split _ _ _ _ => simpa [MGraph.applyUpdate] using hx'

/-- Exact word count equality between `batchWords U` and `SmallBatchAt` for edge-only batches. -/
theorem smallBatchAt_batchWords_len_eq {mem : ℕ → ℕ} {a bW : ℕ} {G : MGraph} {U : List Update}
    (hSmall : SmallBatchAt mem a G U bW) (hEdge : ∀ u ∈ U, IsEdgeUpdate u) :
    (batchWords U).length = bW := by
  have haux : ∀ (L : List Update) (p wT : ℕ) (H : MGraph),
      BatchBodyAt mem p H L wT → (∀ u ∈ L, IsEdgeUpdate u) → (L.flatMap updateWords).length = wT := by
    intro L; induction L with
    | nil => intro p wT H hb _; exact hb.symm
    | cons u us ih =>
      intro p wT H hb he
      obtain ⟨len, hle, hu, hr⟩ := hb
      have huE := he u List.mem_cons_self
      have ihr := ih (p + len) (wT - len) (H.applyUpdate u) hr (fun v hv => he v (List.mem_cons_of_mem _ hv))
      cases u with
      | insert _ _ _ => obtain ⟨rfl, _⟩ := hu; simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
      | delete _ => obtain ⟨rfl, _⟩ := hu; simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
      | split _ _ _ _ => exact huE.elim
  have h1 := haux U (a + 1) (bW - 1) G hSmall.1.2.2 hEdge
  have h2 := hSmall.1.1
  simp only [batchWords, List.length_cons]; omega

/-- Under `FreshInv` and `RefreshBatch`, `tr.1 = extG`, `tr` maintains `FreshInv` on `G0'`,
and every `ei ∈ G0'.E` is either unchanged (`ei ∈ G0.E`, `ei = e2i (i2e' ei)`) or replaced
(`ei ∉ G0.E`, `ei = tr.2.1 e` with `e2i e ∈ G0.E` and `.delete (e2i e) ∈ U_int`). -/
theorem refreshBatch_edge_dichotomy {extG G0 : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    {U : List Update}
    (hFresh : FreshInv extG G0 e2i i2e nf) (hRef : RefreshBatch extG U) :
    let tr := translateBatch extG e2i i2e nf U
    let U_int := tr.2.2.2.2
    let G0' := G0.applyBatch U_int
    tr.1 = extG ∧
    FreshInv extG G0' tr.2.1 tr.2.2.1 tr.2.2.2.1 ∧
    (∀ u ∈ U_int, IsEdgeUpdate u) ∧
    (∀ e ∈ extG.E,
      (¬ ∃ u ∈ U, u.Inserts e) →
        e2i e ∈ G0'.E ∧ tr.2.1 e = e2i e ∧ tr.2.2.1 (e2i e) = e ∧
        Update.delete (e2i e) ∉ U_int ∧
        ¬ ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = e2i e) ∧
    (∀ e ∈ extG.E,
      (∃ u ∈ U, u.Inserts e) →
        e2i e ∈ G0.E ∧ Update.delete (e2i e) ∈ U_int ∧ tr.2.2.1 (e2i e) = e ∧
        tr.2.1 e ∉ G0.E ∧ nf ≤ tr.2.1 e) := by
  dsimp only
  set tr := translateBatch extG e2i i2e nf U
  set U_int := tr.2.2.2.2
  set G0' := G0.applyBatch U_int
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have := hRef.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact this
  obtain ⟨hTrExt, hFreshTr, _, _, _, _, _⟩ := translateBatch_preserves U extG G0 e2i i2e nf hFresh hRef.1
  have hTr1Eq : tr.1 = extG := hTrExt.trans hRef.2.1
  have hFreshTr' : FreshInv extG G0' tr.2.1 tr.2.2.1 tr.2.2.2.1 := by
    rw [← hTr1Eq]; exact hFreshTr
  obtain ⟨hI2EOld, hSurv, hRange, _, hInsIff⟩ := translateBatch_oldId_facts U extG G0 e2i i2e nf hFresh hRef.1 hEdgeU
  have hEdgeInt : ∀ u ∈ U_int, IsEdgeUpdate u := fun u hu => by
    have hr := hRange u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact hr
  refine ⟨hTr1Eq, hFreshTr', hEdgeInt, fun e he hNoIns => ?_, fun e he hIns => ?_⟩
  · have hNotDel : Update.delete (e2i e) ∉ U_int := (hInsIff e he (hTr1Eq.symm ▸ he)).mp hNoIns
    have heiG0 : e2i e ∈ G0.E := hFresh.hE ▸ Finset.mem_image_of_mem e2i he
    have heiG0' : e2i e ∈ G0'.E := (hSurv (e2i e) heiG0).mpr hNotDel
    have hi2eEq : tr.2.2.1 (e2i e) = e :=
      (hI2EOld (e2i e) (hFresh.hLtFresh _ heiG0)).trans (hFresh.hLeft e he)
    have he2iEq : tr.2.1 e = e2i e := by
      have hr := (hFreshTr'.hRight (e2i e) heiG0').1
      rwa [hi2eEq] at hr
    refine ⟨heiG0', he2iEq, hi2eEq, hNotDel, ?_⟩
    rintro ⟨ei_old, hOldG, hOldDel, hEq⟩
    have hOldE : tr.2.2.1 ei_old ∈ extG.E := by
      rw [hI2EOld ei_old (hFresh.hLtFresh _ hOldG)]
      exact (hFresh.hRight ei_old hOldG).2
    have hSameExt : tr.2.2.1 ei_old = e := by
      have h1 := hFreshTr'.hLeft (tr.2.2.1 ei_old) hOldE
      have h2 := hFreshTr'.hLeft e he
      rw [hEq, ← he2iEq] at h1
      exact h1.symm.trans h2
    have hOldEq : ei_old = e2i e := by
      rw [hI2EOld ei_old (hFresh.hLtFresh _ hOldG)] at hSameExt
      rw [← hSameExt]
      exact (hFresh.hRight ei_old hOldG).1.symm
    exact hNotDel (hOldEq ▸ hOldDel)
  · have heiG0 : e2i e ∈ G0.E := hFresh.hE ▸ Finset.mem_image_of_mem e2i he
    have hDel : Update.delete (e2i e) ∈ U_int := by
      by_contra hnd
      exact ((hInsIff e he (hTr1Eq.symm ▸ he)).mpr hnd) hIns
    have hi2eEq : tr.2.2.1 (e2i e) = e :=
      (hI2EOld (e2i e) (hFresh.hLtFresh _ heiG0)).trans (hFresh.hLeft e he)
    have hNewG0' : tr.2.1 e ∈ G0'.E := hFreshTr'.hE ▸ Finset.mem_image_of_mem tr.2.1 he
    have hNewNotOld : tr.2.1 e ∉ G0.E := by
      intro hMem
      have h1 := hFreshTr'.hLeft e he
      rw [hI2EOld (tr.2.1 e) (hFresh.hLtFresh _ hMem)] at h1
      have h2 := (hFresh.hRight (tr.2.1 e) hMem).1
      rw [h1] at h2
      have hNotSurv : e2i e ∉ G0'.E := fun hs => ((hSurv (e2i e) heiG0).mp hs) hDel
      exact hNotSurv (h2.symm ▸ hNewG0')
    have hGeNf : nf ≤ tr.2.1 e := by
      by_contra hlt
      push Not at hlt
      have hInsU : ∃ u ∈ U_int, u.Inserts (tr.2.1 e) := by
        by_contra hno
        have : ∀ (L : List Update) (H : MGraph) (x : ℕ),
            x ∈ (H.applyBatch L).E → (¬ ∃ u ∈ L, u.Inserts x) → x ∈ H.E := by
          intro L; induction L with
          | nil => intro H x hx _; simpa [MGraph.applyBatch] using hx
          | cons v vs ih =>
            intro H x hx hno'
            have hx' := ih (H.applyUpdate v) x (by simpa [MGraph.applyBatch] using hx)
              (fun ⟨w, hw, hwi⟩ => hno' ⟨w, List.mem_cons_of_mem _ hw, hwi⟩)
            cases v with
            | delete d =>
              simp only [MGraph.applyUpdate, Finset.mem_erase] at hx'; exact hx'.2
            | insert a _ _ =>
              simp only [MGraph.applyUpdate, Finset.mem_insert] at hx'
              rcases hx' with rfl | hx''
              · exact (hno' ⟨.insert x _ _, List.mem_cons_self, rfl⟩).elim
              · exact hx''
            | split _ _ _ _ =>
              simpa [MGraph.applyUpdate] using hx'
        exact hNewNotOld (this U_int G0 (tr.2.1 e) hNewG0' hno)
      obtain ⟨u, hu, hui⟩ := hInsU
      cases u with
      | insert a _ _ =>
        simp only [Update.Inserts] at hui; subst hui
        have := (hRange _ hu).1; omega
      | delete _ => simp [Update.Inserts] at hui
      | split _ _ _ _ => simp [Update.Inserts] at hui
    exact ⟨heiG0, hDel, hi2eEq, hNewNotOld, hGeNf⟩

/-- Every `.insert ei _ _` in `U_int` comes from an `.insert e _ _` in `U` with `tr.2.2.1 ei = e`. -/
theorem translateBatch_insert_mem_ext :
    ∀ (U : List Update) (curExt curInt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      FreshInv curExt curInt e2i i2e nf → curExt.BatchIsValid U → (∀ u ∈ U, IsEdgeUpdate u) →
      let tr := translateBatch curExt e2i i2e nf U
      ∀ ei x y, Update.insert ei x y ∈ tr.2.2.2.2 → ∃ u ∈ U, u.Inserts (tr.2.2.1 ei)
  | [], _, _, _, _, _, _, _, _, _, _, _, h => by simp [translateBatch] at h
  | u :: rest, curExt, curInt, e2i, i2e, nf, hF, hVal, hEdge, ei, x, y, hMem => by
    have huE := hEdge u List.mem_cons_self
    have hrestE := fun v hv => hEdge v (List.mem_cons_of_mem _ hv)
    obtain ⟨hF1, _, _, _, _, _, _⟩ := translateUpdate_preserves hF hVal.1
    cases u with
    | split _ _ _ _ => exact huE.elim
    | delete e0 =>
      simp only [translateBatch, translateUpdate, List.mem_cons] at hMem ⊢
      rcases hMem with hEq | hTail
      · cases hEq
      · obtain ⟨v, hv, hvi⟩ :=
          translateBatch_insert_mem_ext rest (curExt.applyUpdate (.delete e0))
            (curInt.applyUpdate (.delete (e2i e0))) e2i i2e nf hF1 hVal.2 hrestE ei x y hTail
        exact ⟨v, Or.inr hv, hvi⟩
    | insert e0 u0 v0 =>
      simp only [translateBatch, translateUpdate, List.mem_cons] at hMem ⊢
      rcases hMem with hEq | hTail
      · injection hEq with hEi _ _
        rw [hEi]
        have hI2E := (translateBatch_oldId_facts rest (curExt.applyUpdate (.insert e0 u0 v0))
          (curInt.applyUpdate (.insert nf u0 v0)) (Function.update e2i e0 nf)
          (Function.update i2e nf e0) (nf + 1) hF1 hVal.2 hrestE).1 nf (Nat.lt_succ_self nf)
        rw [hI2E, Function.update_self]
        exact ⟨.insert e0 u0 v0, Or.inl rfl, rfl⟩
      · obtain ⟨v, hv, hvi⟩ :=
          translateBatch_insert_mem_ext rest (curExt.applyUpdate (.insert e0 u0 v0))
            (curInt.applyUpdate (.insert nf u0 v0)) (Function.update e2i e0 nf)
            (Function.update i2e nf e0) (nf + 1) hF1 hVal.2 hrestE ei x y hTail
        exact ⟨v, Or.inr hv, hvi⟩

/-! ### 2. Zeroing `slots[0..intCap)` (`wireZeroSlotsStmt`, Branch A) -/

/-- Zero `slots[0..intCap)` using `reg 70 = root`. -/
@[expose] def wireZeroSlotsStmt : Stmt :=
  .assign 14 (.load (.bin .add (.reg 70) (.const 6))) ;;
  .assign 15 (.load (.bin .add (.reg 70) (.const 15))) ;;
  forRange 19 (.const 0) (.reg 15)
    (.store (.bin .add (.reg 14) (.reg 19)) (.const 0))

theorem wireZeroSlotsStmt_noRand : wireZeroSlotsStmt.NoRand := by
  simp [wireZeroSlotsStmt, forRange, forUp, Stmt.NoRand]

/-- Execute `wireZeroSlotsStmt`: zeroes `slots[0..intCap)`, preserving all other memory and
all registers `≥ 70`. -/
theorem wireZeroSlotsStmt_runs {w root slots intCap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h70 : st.regs 70 = root) (hS : st.mem (root + 6) = slots) (hI : st.mem (root + 15) = intCap)
    (hRW : root + 16 < 2 ^ w) (hSW : slots + intCap < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireZeroSlotsStmt st .normal out cost ∧
      cost ≤ 15 * intCap + 30 ∧
      (∀ j < intCap, out.mem (slots + j) = 0) ∧
      (∀ a, (a < slots ∨ slots + intCap ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r = 4 ∨ 70 ≤ r → out.regs r = st.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  let s1 := { st with regs := Function.update st.regs 14 slots }
  let s2 := { s1 with regs := Function.update s1.regs 15 intCap }
  have r1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 70) (.const 6)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, h70, show 6 < 2 ^ w by omega,
      show root + 6 < 2 ^ w by omega, hS], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 70) (.const 15)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨intCap, by simp [Expr.eval, BinOp.eval, s1, h70, show 15 < 2 ^ w by omega,
      show root + 15 < 2 ^ w by omega, hI], rfl, rfl, rfl⟩
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ intCap ∧ s.regs 19 = j ∧ s.regs 14 = slots ∧ s.regs 15 = intCap ∧
    (∀ r, r = 4 ∨ 70 ≤ r → s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (slots + k) = 0) ∧
    ∀ a, (a < slots ∨ slots + intCap ≤ a) → s.mem a = st.mem a
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 15)
    (P := fun s => s = s2) (Inv := Inv) 6 0 intCap (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        by simp [s2, s1], by simp [s2],
        fun r hr => by
          rcases hr with h4 | hr <;> simp [s2, s1, Function.update_of_ne (by omega : r ≠ 19),
            Function.update_of_ne (by omega : r ≠ 15), Function.update_of_ne (by omega : r ≠ 14)],
        fun _ hk => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.2.2.1])
    (fun j _ hj s ω' ⟨_, hjr, h14, h15, hregs, hzero, hfr⟩ => by
      let t1 := { s with mem := Function.update s.mem (slots + j) 0 }
      have rt1 : Runs w p ω' (.store (.bin .add (.reg 14) (.reg 19)) (.const 0)) s .normal t1 5 :=
        runs_store_iff.mpr ⟨slots + j, 0,
          by simp [Expr.eval, BinOp.eval, h14, hjr, show slots + j < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      refine ⟨.normal, t1, 5, rt1, ⟨⟨by omega, by simp, by simp [t1, h14], by simp [t1, h15],
        fun r hr => by rcases hr with h4 | hr <;> simp [t1, Function.update_of_ne (by omega : r ≠ 19), hregs r (by omega)],
        fun k hk => by
          by_cases hkj : k = j
          · subst hkj; simp [t1]
          · simp [t1, Function.update_of_ne (by omega : slots + k ≠ slots + j), hzero k (by omega)],
        fun a ha => by simp [t1, Function.update_of_ne (by rcases ha with h | h <;> omega : a ≠ slots + j),
          hfr a ha]⟩, by simp [t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, out, cL, rL, hOut, hcL⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hOut
  | normal =>
    obtain ⟨_, _, _, _, hregs, hzero, hfr⟩ := hOut
    simp only [Expr.size] at hcL
    exact ⟨out, 5 + (5 + cL + 1) + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, cL, r2, rL, rfl⟩), rfl⟩),
      by omega, hzero, hfr, hregs⟩

/-! ### 3. Zeroing `slots[ei]` for inserted edges in `U_int` (`wireZeroInsertedSlotsStmt`, Branch B) -/

/-- Zero `slots[ei]` for every `.insert ei _ _` in `U_int` (`reg 87`), leaving all other slots
(in particular every surviving tree edge) untouched. -/
@[expose] def wireZeroInsertedSlotsStmt : Stmt :=
  .assign 14 (.load (.bin .add (.reg 70) (.const 6))) ;;
  .assign 15 (.load (.reg 87)) ;;
  .assign 16 (.bin .add (.reg 87) (.const 1)) ;;
  forRange 19 (.const 0) (.reg 15)
    (.cond (.load (.reg 16))
      (.assign 16 (.bin .add (.reg 16) (.const 2)))
      (.store (.bin .add (.reg 14) (.load (.bin .add (.reg 16) (.const 1)))) (.const 0) ;;
       .assign 16 (.bin .add (.reg 16) (.const 4))))

theorem wireZeroInsertedSlotsStmt_noRand : wireZeroInsertedSlotsStmt.NoRand := by
  simp [wireZeroInsertedSlotsStmt, forRange, forUp, Stmt.NoRand]

/-- Execute `wireZeroInsertedSlotsStmt`: sets `slots[ei] = 0` for every `.insert ei _ _ ∈ U_int`
in `≤ 30 * U_int.length + 35` steps, preserving all other addresses and all registers `≥ 70`. -/
theorem wireZeroInsertedSlotsStmt_runs {w root uIntBuf slots intCap : ℕ}
    {U_int : List Update} {p : Program} {ω : ℕ → Bool} {st : State}
    (h70 : st.regs 70 = root) (h87 : st.regs 87 = uIntBuf)
    (hS : st.mem (root + 6) = slots)
    (hBatch : IPM.Machine.BatchAt st.mem uIntBuf U_int)
    (hEdgeOnly : ∀ u ∈ U_int, IsEdgeUpdate u)
    (hInsCap : ∀ u ∈ U_int, match u with | .insert ei _ _ => ei < intCap | _ => True)
    (hDisj : slots + intCap ≤ uIntBuf ∨ uIntBuf + (batchWords U_int).length ≤ slots)
    (hRW : root + 16 < 2 ^ w) (hSW : slots + intCap < 2 ^ w)
    (hBW : uIntBuf + (batchWords U_int).length < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireZeroInsertedSlotsStmt st .normal out cost ∧
      cost ≤ 30 * U_int.length + 35 ∧
      (∀ u ∈ U_int, match u with | .insert ei _ _ => out.mem (slots + ei) = 0 | _ => True) ∧
      (∀ a, (∀ u ∈ U_int, match u with | .insert ei _ _ => a ≠ slots + ei | _ => True) →
        out.mem a = st.mem a) ∧
      (∀ r, r = 4 ∨ 70 ≤ r → out.regs r = st.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hLen0 : st.mem uIntBuf = U_int.length := by simpa [batchWords] using hBatch 0 (by simp [batchWords])
  have hULenW : U_int.length < 2 ^ w := by
    have h2 : ∀ L : List Update, (∀ u ∈ L, IsEdgeUpdate u) → 2 * L.length ≤ (L.flatMap updateWords).length := by
      intro L hL; induction L with
      | nil => simp
      | cons u rest ih =>
        have hu := hL u List.mem_cons_self
        have hr := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        cases u with
        | insert _ _ _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | delete _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | split _ _ _ _ => exact hu.elim
    have h2' := h2 U_int hEdgeOnly
    simp only [batchWords, List.length_cons] at hBW; omega
  let s1 := { st with regs := Function.update st.regs 14 slots }
  let s2 := { s1 with regs := Function.update s1.regs 15 U_int.length }
  let s3 := { s2 with regs := Function.update s2.regs 16 (uIntBuf + 1) }
  have r1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 70) (.const 6)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, h70, show 6 < 2 ^ w by omega,
      show root + 6 < 2 ^ w by omega, hS], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 15 (.load (.reg 87))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨U_int.length, by simp [Expr.eval, s1, h87, hLen0], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 16 (.bin .add (.reg 87) (.const 1))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by simp [Expr.eval, BinOp.eval, s2, s1, h87, hw1,
      show uIntBuf + 1 < 2 ^ w by simp [batchWords] at hBW; omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    i ≤ U_int.length ∧ s.regs 19 = i ∧ s.regs 14 = slots ∧ s.regs 15 = U_int.length ∧
    s.regs 16 = uIntBuf + 1 + edgeRecOff U_int i ∧
    (∀ r, r = 4 ∨ 70 ≤ r → s.regs r = st.regs r) ∧
    (∀ j < i, ∀ hj : j < U_int.length, match U_int[j] with
      | .insert ei _ _ => s.mem (slots + ei) = 0 | _ => True) ∧
    (∀ a, (∀ j < i, ∀ hj : j < U_int.length, match U_int[j] with
      | .insert ei _ _ => a ≠ slots + ei | _ => True) → s.mem a = st.mem a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 15)
    (P := fun s => s = s3) (Inv := Inv) (fun _ => 21) 0 U_int.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        by simp [s3, s2, s1], by simp [s3, s2], by simp [s3, edgeRecOff],
        fun r hr => by
          rcases hr with h4 | hr <;> simp [s3, s2, s1, Function.update_of_ne (by omega : r ≠ 19),
            Function.update_of_ne (by omega : r ≠ 16), Function.update_of_ne (by omega : r ≠ 15),
            Function.update_of_ne (by omega : r ≠ 14)],
        fun j hj _ => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.2.2.1])
    (fun i _ hi s ω' ⟨_, hjr, h14, h15, h16, hregs, hdone, hfr⟩ => by
      have huE := hEdgeOnly U_int[i] (List.getElem_mem hi)
      have hNotSl (a : ℕ) (ha1 : uIntBuf ≤ a) (ha2 : a < uIntBuf + (batchWords U_int).length) :
          s.mem a = st.mem a :=
        hfr a (fun j _ hj => by
          have hc := hInsCap U_int[j] (List.getElem_mem hj)
          cases hUj : U_int[j] with
          | insert ei _ _ => rw [hUj] at hc; dsimp only at hc ⊢; rcases hDisj with h | h <;> omega
          | delete _ => trivial
          | split _ _ _ _ => trivial)
      cases hUi : U_int[i] with
      | split _ _ _ _ => rw [hUi] at huE; exact huE.elim
      | delete ei =>
        have hW0 := edgeBatch_rec_word hBatch hi (j := 0) (by simp [hUi, updateWords])
        have hTag : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 1 := by
          rw [hNotSl _ (by omega) (by omega)]; simpa [hUi, updateWords] using hW0.1
        have hOffN : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 2 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int i + 2 < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with regs := Function.update s.regs 16 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 16 (.bin .add (.reg 16) (.const 2))) s .normal t1 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, h16, hw2, hOffN, hNextW, ↓reduceIte, Option.some.injEq]
            omega, rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.load (.reg 16))
              (.assign 16 (.bin .add (.reg 16) (.const 2)))
              (.store (.bin .add (.reg 14) (.load (.bin .add (.reg 16) (.const 1)))) (.const 0) ;;
               .assign 16 (.bin .add (.reg 16) (.const 4)))) s .normal t1 7 :=
          runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, h16, hTag], by simpa using rt1, by simp [Expr.size]⟩
        refine ⟨.normal, t1, 7, rCond, ⟨⟨by omega, by simp, by simp [t1, h14], by simp [t1, h15],
          by simp [t1], fun r hr => by
            rcases hr with h4 | hr <;> simp [t1, Function.update_of_ne (by omega : r ≠ 19),
              Function.update_of_ne (by omega : r ≠ 16), hregs r (by omega)],
          fun j hj hjLt => by
            by_cases hji : j = i
            · subst hji; rw [hUi]; trivial
            · exact hdone j (by omega) hjLt,
          fun a ha => hfr a (fun j hj hjLt => ha j (Nat.lt_succ_of_lt hj) hjLt)⟩, by simp [t1, hjr]⟩, by dsimp only; omega⟩
      | insert ei u v =>
        have hW0 := edgeBatch_rec_word hBatch hi (j := 0) (by simp [hUi, updateWords])
        have hW1 := edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])
        have hTag : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 0 := by
          rw [hNotSl _ (by omega) (by omega)]; simpa [hUi, updateWords] using hW0.1
        have hEiMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i + 1) = ei := by
          rw [hNotSl _ (by omega) (by omega)]; simpa [hUi, updateWords] using hW1.1
        have hEiCap : ei < intCap := by
          have := hInsCap U_int[i] (List.getElem_mem hi); rwa [hUi] at this
        have hOffN : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 4 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int i + 4 < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 3) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with mem := Function.update s.mem (slots + ei) 0 }
        let t2 := { t1 with regs := Function.update t1.regs 16 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω'
            (.store (.bin .add (.reg 14) (.load (.bin .add (.reg 16) (.const 1)))) (.const 0))
            s .normal t1 8 :=
          runs_store_iff.mpr ⟨slots + ei, 0, by
            simp [Expr.eval, BinOp.eval, h14, h16, hw1, show uIntBuf + 1 + edgeRecOff U_int i + 1 < 2 ^ w by omega,
              hEiMem, show slots + ei < 2 ^ w by omega],
            by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 16 (.bin .add (.reg 16) (.const 4))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t1, h16, hw4, hOffN, hNextW, ↓reduceIte, Option.some.injEq]
            omega, rfl, rfl, rfl⟩
        have rElse : Runs w p ω'
            (.store (.bin .add (.reg 14) (.load (.bin .add (.reg 16) (.const 1)))) (.const 0) ;;
             .assign 16 (.bin .add (.reg 16) (.const 4))) s .normal t2 13 :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 8, 4, rt1, rt2, rfl⟩)
        have rCond : Runs w p ω'
            (.cond (.load (.reg 16))
              (.assign 16 (.bin .add (.reg 16) (.const 2)))
              (.store (.bin .add (.reg 14) (.load (.bin .add (.reg 16) (.const 1)))) (.const 0) ;;
               .assign 16 (.bin .add (.reg 16) (.const 4)))) s .normal t2 16 :=
          runs_cond_iff.mpr ⟨0, 13, by simp [Expr.eval, h16, hTag], by simpa using rElse, by simp [Expr.size]⟩
        refine ⟨.normal, t2, 16, rCond, ⟨⟨by omega, by simp, by simp [t2, t1, h14], by simp [t2, t1, h15],
          by simp [t2], fun r hr => by
            rcases hr with h4 | hr <;> simp [t2, t1, Function.update_of_ne (by omega : r ≠ 19),
              Function.update_of_ne (by omega : r ≠ 16), hregs r (by omega)],
          fun j hj hjLt => by
            by_cases hji : j = i
            · subst hji; rw [hUi]; simp [t2, t1]
            · have hd := hdone j (by omega) hjLt
              cases hUj : U_int[j] with
              | insert ej _ _ =>
                rw [hUj] at hd
                by_cases heq : ej = ei
                · subst heq; simp [t2, t1]
                · simp [t2, t1, Function.update_of_ne (by omega : slots + ej ≠ slots + ei), hd]
              | delete _ => trivial
              | split _ _ _ _ => trivial,
          fun a ha => by
            have hne : a ≠ slots + ei := by
              have := ha i (Nat.lt_succ_self i) hi; rwa [hUi] at this
            simp only [t2, t1, Function.update_of_ne hne]
            exact hfr a (fun j hj hjLt => ha j (Nat.lt_succ_of_lt hj) hjLt)⟩, by simp [t2, t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, out, cL, rL, hOut, hcL⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hOut
  | normal =>
    obtain ⟨_, _, _, _, _, hregs, hdone, hfr⟩ := hOut
    have hrc : rangeCost (fun _ => 21) 0 U_int.length = U_int.length * 21 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcL
    refine ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 4, cL, r3, rL, rfl⟩), rfl⟩), rfl⟩), by omega, ?_, ?_, hregs⟩
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      exact hdone j hj hj
    · intro a ha
      exact hfr a (fun j _ hj => ha U_int[j] (List.getElem_mem hj))

/-- In a valid edge-only batch on `H`, every `.insert _ a b` has endpoints `< vCap` if `H.V ⊆ [0, vCap)`. -/
theorem batchIsValid_insert_vert_lt {vCap : ℕ} :
    ∀ (L : List Update) (H : MGraph), H.BatchIsValid L → (∀ u ∈ L, IsEdgeUpdate u) →
      (∀ v ∈ H.V, v < vCap) →
      ∀ u ∈ L, match u with | .insert _ a b => a < vCap ∧ b < vCap | _ => True
  | [], _, _, _, _, _, h => nomatch h
  | u :: rest, H, ⟨hu, hrest⟩, hE, hV, w, hw => by
    have hRestV : ∀ v ∈ (H.applyUpdate u).V, v < vCap := by
      cases u with
      | insert _ _ _ | delete _ => simpa [MGraph.applyUpdate] using hV
      | split _ _ _ _ => exact (hE _ List.mem_cons_self).elim
    rcases List.mem_cons.mp hw with rfl | hw
    · cases w with
      | insert _ a b => exact ⟨hV a hu.2.1, hV b hu.2.2⟩
      | delete _ => trivial
      | split _ _ _ _ => exact (hE _ List.mem_cons_self).elim
    · exact batchIsValid_insert_vert_lt rest _ hrest (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hRestV w hw

/-- In a valid edge-only batch on `H` within edge capacity `eCap`, every `.delete ei` has `ei < eCap`. -/
theorem batchIsValid_delete_lt_ecap {vCap eCap : ℕ} :
    ∀ (L : List Update) (H : MGraph), H.BatchIsValid L → BatchWithinCaps vCap eCap L →
      (∀ u ∈ L, IsEdgeUpdate u) → (∀ e ∈ H.E, e < eCap) →
      ∀ u ∈ L, match u with | .delete ei => ei < eCap | _ => True
  | [], _, _, _, _, _, _, h => nomatch h
  | u :: rest, H, ⟨hu, hrest⟩, hCap, hE, hHE, w, hw => by
    have hRestE : ∀ e ∈ (H.applyUpdate u).E, e < eCap := by
      cases u with
      | insert ei _ _ =>
        intro e he; simp only [MGraph.applyUpdate, Finset.mem_insert] at he
        rcases he with rfl | he
        · exact hCap _ List.mem_cons_self
        · exact hHE e he
      | delete _ =>
        intro e he; simp only [MGraph.applyUpdate, Finset.mem_erase] at he; exact hHE e he.2
      | split _ _ _ _ => exact (hE _ List.mem_cons_self).elim
    rcases List.mem_cons.mp hw with rfl | hw
    · cases w with
      | delete ei => exact hHE ei hu
      | insert _ _ _ => trivial
      | split _ _ _ _ => exact (hE _ List.mem_cons_self).elim
    · exact batchIsValid_delete_lt_ecap rest _ hrest (fun x hx => hCap x (List.mem_cons_of_mem _ hx))
        (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hRestE w hw

end MinCostFlow.MinRatio
