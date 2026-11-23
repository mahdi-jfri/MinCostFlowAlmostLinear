module

public import MinCostFlow.SparseCore.Program.BundleStepEmitProcs

/-!
# Phase 3 pop-and-sort procedures (`BundleStepEmitPop`)

Verifies the first two stages of `bundleStepEmitSlotStmt`:
1. `applyBatch_deletes_eq`: deleting a list of edges via `MGraph.applyBatch` matches removing their
   `Finset` from `B.edges`.
2. `bundleStepEmitPopDels_runs`: pops and zeroes `slotDelHead[s]`/`slotDelNext` into `delArr`,
   sorts via `bMergeSort`, leaving `delSet.sort (· ≤ ·)` at `delArr`.
3. `bundleStepEmitPopCands_runs`: pops and zeroes `slotCandHead[s]`/`candNext`/`inCand` into
   `candArr`, sorts via `bMergeSort`, transitioning `BundleSlotRepCand` to clean `BundleSlotRepAt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-! ## 1. Pure batch-deletion lemma -/

lemma applyBatch_deletes_eq (B : BundleState) :
    ∀ (dels : List ℕ),
      B.graph.applyBatch (dels.map Update.delete) =
        ({ B with edges := B.edges \ dels.toFinset } : BundleState).graph
  | [] => by simp [MGraph.applyBatch]
  | e :: es => by
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, List.toFinset_cons]
    have hstep : B.graph.applyUpdate (.delete e) =
        ({ B with edges := B.edges.erase e } : BundleState).graph := rfl
    rw [hstep]
    have ih := applyBatch_deletes_eq { B with edges := B.edges.erase e } es
    simp only [MGraph.applyBatch] at ih
    rw [ih]
    have hE : B.edges.erase e \ es.toFinset = B.edges \ insert e es.toFinset := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
    simp [hE]

/-! ## 2. Step 3A: `bundleStepEmitPopDels_runs` -/

theorem bundleStepEmitPopDels_runs {w eCap s delHeadBase delNextBase hCur : ℕ}
    {pProg : Program} {bMergeSort : ℕ} {ω : ℕ → Bool}
    {dL : List ℕ} {delSet : Finset ℕ} {st₀ : State}
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (heCap_w : eCap < 2 ^ w)
    (hhead_w : delHeadBase + s < 2 ^ w) (hnext_w : delNextBase + eCap < 2 ^ w)
    (hh_w : hCur + 2 * dL.length < 2 ^ w)
    (hhead_disj_next : delHeadBase + s < delNextBase ∨ delNextBase + eCap ≤ delHeadBase + s)
    (hhead_disj_h : delHeadBase + s < hCur ∨ hCur + 2 * dL.length ≤ delHeadBase + s)
    (hnext_disj_h : delNextBase + eCap ≤ hCur ∨ hCur + 2 * dL.length ≤ delNextBase)
    (hsll : IsSinglyLinkedList st₀.mem delNextBase (delHeadBase + s) eCap dL)
    (hmem_eq : ∀ e, e ∈ dL ↔ e ∈ delSet)
    (hzero : ZeroFrom st₀.mem hCur)
    (hr2 : st₀.regs 2 = s) (hr4 : st₀.regs 4 = hCur)
    (hr13 : st₀.regs 13 = delHeadBase) (hr14 : st₀.regs 14 = delNextBase) :
    ∃ stEnd cEnd,
      Runs w pProg ω (bundleStepEmitPopDelsStmt bMergeSort) st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 15, r ≠ 4 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hCur + 2 * dL.length ∧
      stEnd.regs 16 = hCur ∧ stEnd.regs 17 = dL.length ∧
      delSet.card = dL.length ∧
      stEnd.mem (delHeadBase + s) = 0 ∧
      (∀ e ∈ dL, stEnd.mem (delNextBase + e) = 0) ∧
      ListAt stEnd.mem hCur (delSet.sort (· ≤ ·)) ∧
      ZeroFrom stEnd.mem (hCur + 2 * dL.length) ∧
      (∀ a, a ≠ delHeadBase + s → (∀ e ∈ dL, a ≠ delNextBase + e) →
        (a < hCur ∨ hCur + 2 * dL.length ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 200 * dL.length * (Nat.log 2 (dL.length + 1) + 1) + 30 * dL.length + 100 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hdL_nd : dL.Nodup := hsll.nodup
  have hdL_lt : ∀ e ∈ dL, e < eCap := hsll.mem_lt
  have hcard : delSet.card = dL.length := by
    have hset : dL.toFinset = delSet := by ext e; simp [hmem_eq]
    rw [← hset, List.toFinset_card_of_nodup hdL_nd]
  have hhead_val_w : st₀.mem (delHeadBase + s) < 2 ^ w := by
    cases dL with
    | nil => rw [hsll]; omega
    | cons x _ => rw [hsll.2.2.1]; have := hsll.1; omega
  let r16 := Function.update st₀.regs 16 hCur
  let r17 := Function.update r16 17 0
  let r18 := Function.update r17 18 (st₀.mem (delHeadBase + s))
  let mH := Function.update st₀.mem (delHeadBase + s) 0
  let stA : State := { mem := mH, regs := r18, pos := st₀.pos }
  have ha16 : Runs w pProg ω (.assign 16 (.reg 4)) st₀ .normal { st₀ with regs := r16 } 2 :=
    runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, hr4], rfl, rfl, rfl⟩
  have ha17 : Runs w pProg ω (.assign 17 (.const 0)) { st₀ with regs := r16 } .normal { st₀ with regs := r17 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha18 : Runs w pProg ω (.assign 18 (.load (.bin .add (.reg 13) (.reg 2))))
      { st₀ with regs := r17 } .normal { st₀ with regs := r18 } 5 :=
    runs_assign_iff.mpr ⟨st₀.mem (delHeadBase + s), by
      simp [Expr.eval, BinOp.eval, r17, r16, hr13, hr2, hhead_w], rfl, rfl, rfl⟩
  have hstH : Runs w pProg ω (.store (.bin .add (.reg 13) (.reg 2)) (.const 0))
      { st₀ with regs := r18 } .normal stA 5 :=
    runs_store_iff.mpr ⟨delHeadBase + s, 0,
      by simp [Expr.eval, BinOp.eval, r18, r17, r16, hr13, hr2, hhead_w],
      by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  let body : Stmt :=
    .assign 19 (.bin .sub (.reg 18) (.const 1)) ;;
    .assign 18 (.load (.bin .add (.reg 14) (.reg 19))) ;;
    .store (.bin .add (.reg 14) (.reg 19)) (.const 0) ;;
    .store (.bin .add (.reg 16) (.reg 17)) (.reg 19) ;;
    .assign 17 (.bin .add (.reg 17) (.const 1))
  have hloop : ∀ (rem pre : List ℕ) (st : State),
      pre ++ rem = dL →
      (∀ r ≤ 15, st.regs r = st₀.regs r) →
      st.regs 16 = hCur → st.regs 17 = pre.length →
      st.regs 18 = (match rem with | [] => 0 | x :: _ => x + 1) →
      (∀ x xs, rem = x :: xs → IsSinglyLinkedList st.mem delNextBase (delNextBase + x) eCap xs) →
      (∀ e ∈ pre, st.mem (delNextBase + e) = 0) →
      ListAt st.mem hCur pre →
      (∀ a, (∀ e ∈ pre, a ≠ delNextBase + e) → (a < hCur ∨ hCur + pre.length ≤ a) →
        st.mem a = mH a) →
      ∃ stP cP,
        Runs w pProg ω (.loop (.reg 18) body) st .normal stP cP ∧
        (∀ r ≤ 15, stP.regs r = st₀.regs r) ∧
        stP.regs 16 = hCur ∧ stP.regs 17 = dL.length ∧
        (∀ e ∈ dL, stP.mem (delNextBase + e) = 0) ∧
        ListAt stP.mem hCur dL ∧
        (∀ a, (∀ e ∈ dL, a ≠ delNextBase + e) → (a < hCur ∨ hCur + dL.length ≤ a) →
          stP.mem a = mH a) ∧
        cP ≤ 29 * rem.length + 2 := by
    intro rem
    induction rem with
    | nil =>
      intro pre st hcat hregs hr16 hr17 hr18 _ hpre0 hLat hfr
      simp only [List.append_nil] at hcat; subst hcat
      exact ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr18], rfl, rfl, rfl⟩),
        hregs, hr16, hr17, hpre0, hLat, hfr, by omega⟩
    | cons x xs ih =>
      intro pre st hcat hregs hr16 hr17 hr18 hxs_sll hpre0 hLat hfr
      have hx_mem : x ∈ dL := hcat ▸ List.mem_append_right _ List.mem_cons_self
      have hx_lt : x < eCap := hdL_lt x hx_mem
      have hlen_lt : pre.length < dL.length := by rw [← hcat]; simp
      have hsll_tl := hxs_sll x xs rfl
      have hnxt_eq : st.mem (delNextBase + x) = match xs with | [] => 0 | y :: _ => y + 1 := by
        cases xs with
        | nil => exact hsll_tl
        | cons y ys => exact hsll_tl.2.2.1
      have hnxt_w : st.mem (delNextBase + x) < 2 ^ w := by
        rw [hnxt_eq]; cases xs with
        | nil => dsimp only; omega
        | cons y _ => dsimp only; have := hsll_tl.1; omega
      let r19 := Function.update st.regs 19 x
      let r18' := Function.update r19 18 (st.mem (delNextBase + x))
      let m1 := Function.update st.mem (delNextBase + x) 0
      let m2 := Function.update m1 (hCur + pre.length) x
      let r17' := Function.update r18' 17 (pre.length + 1)
      let st1 : State := { mem := m2, regs := r17', pos := st.pos }
      have hs1 : Runs w pProg ω (.assign 19 (.bin .sub (.reg 18) (.const 1)))
          st .normal { st with regs := r19 } 4 :=
        runs_assign_iff.mpr ⟨x, by simp [Expr.eval, BinOp.eval, hr18, h1_w, show x < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hs2 : Runs w pProg ω (.assign 18 (.load (.bin .add (.reg 14) (.reg 19))))
          { st with regs := r19 } .normal { st with regs := r18' } 5 :=
        runs_assign_iff.mpr ⟨st.mem (delNextBase + x), by
          simp [Expr.eval, BinOp.eval, r19, hregs 14 (by decide), hr14, show delNextBase + x < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      have hs3 : Runs w pProg ω (.store (.bin .add (.reg 14) (.reg 19)) (.const 0))
          { st with regs := r18' } .normal { mem := m1, regs := r18', pos := st.pos } 5 :=
        runs_store_iff.mpr ⟨delNextBase + x, 0,
          by simp [Expr.eval, BinOp.eval, r18', r19, hregs 14 (by decide), hr14, show delNextBase + x < 2 ^ w by omega],
          by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      have hs4 : Runs w pProg ω (.store (.bin .add (.reg 16) (.reg 17)) (.reg 19))
          { mem := m1, regs := r18', pos := st.pos } .normal { mem := m2, regs := r18', pos := st.pos } 5 :=
        runs_store_iff.mpr ⟨hCur + pre.length, x,
          by simp [Expr.eval, BinOp.eval, r18', r19, hr16, hr17, show hCur + pre.length < 2 ^ w by omega],
          by simp [Expr.eval, r18', r19], rfl, rfl, rfl⟩
      have hs5 : Runs w pProg ω (.assign 17 (.bin .add (.reg 17) (.const 1)))
          { mem := m2, regs := r18', pos := st.pos } .normal st1 4 :=
        runs_assign_iff.mpr ⟨pre.length + 1, by
          simp [Expr.eval, BinOp.eval, r18', r19, hr17, h1_w, show pre.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hbody_run : Runs w pProg ω body st .normal st1 27 :=
        bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2 (bundle_runs_seq_normal hs3
          (bundle_runs_seq_normal hs4 hs5)))
      have hx_notin_xs : x ∉ xs := by
        rw [← hcat, List.nodup_append] at hdL_nd
        exact (List.nodup_cons.mp hdL_nd.2.1).1
      have hxs_next : ∀ y ys, xs = y :: ys → IsSinglyLinkedList m2 delNextBase (delNextBase + y) eCap ys := by
        intro y ys hxs_eq; subst hxs_eq
        refine hsll_tl.2.2.2.of_agree ?_ ?_
        · have hy_lt : y < eCap := hsll_tl.1
          have hyx : y ≠ x := fun h => hx_notin_xs (h ▸ List.mem_cons_self)
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by clear * - hnext_disj_h hy_lt hlen_lt; omega),
              Function.update_of_ne (by omega)]
        · intro z hz
          have hz_lt : z < eCap := hsll_tl.2.2.2.mem_lt z hz
          have hzx : z ≠ x := fun h => hx_notin_xs (h ▸ List.mem_cons_of_mem _ hz)
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by clear * - hnext_disj_h hz_lt hlen_lt; omega),
              Function.update_of_ne (by omega)]
      obtain ⟨stP, cP, hrunP, hregsP, hr16P, hr17P, hdL0P, hLatP, hfrP, hcP⟩ :=
        ih (pre ++ [x]) st1 (by simpa [List.append_assoc] using hcat)
          (fun r hr => by simp [st1, r17', r18', r19, show r ≠ 17 by omega, show r ≠ 18 by omega, show r ≠ 19 by omega, hregs r hr])
          (by simp [st1, r17', r18', r19, hr16]) (by simp [st1, r17'])
          (by dsimp only [st1, r17', r18']; rw [Function.update_of_ne (by decide), Function.update_self, hnxt_eq]; cases xs <;> rfl)
          hxs_next
          (fun e he => by
            dsimp only [st1, m2, m1]
            rcases List.mem_append.mp he with hep | hex
            · have he_lt : e < eCap := hdL_lt e (hcat ▸ List.mem_append_left _ hep)
              rw [Function.update_of_ne (by clear * - hnext_disj_h he_lt hlen_lt; omega)]
              by_cases hex' : e = x
              · subst hex'; simp
              · rw [Function.update_of_ne (by omega)]; exact hpre0 e hep
            · have heq : e = x := List.mem_singleton.mp hex; subst heq
              rw [Function.update_of_ne (by clear * - hnext_disj_h hx_lt hlen_lt; omega)]; simp)
          (fun i hi => by
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hip : i < pre.length
            · rw [List.getElem_append_left hip]
              dsimp only [st1, m2, m1]
              rw [Function.update_of_ne (by omega),
                  Function.update_of_ne (by clear * - hnext_disj_h hx_lt hip hlen_lt; omega)]
              exact hLat i hip
            · have hieq : i = pre.length := by omega
              subst hieq; rw [List.getElem_append_right (le_refl _)]; simp [st1, m2])
          (fun a ha1 ha2 => by
            dsimp only [st1, m2, m1]
            simp only [List.length_append, List.length_singleton] at ha2
            rw [Function.update_of_ne (by omega),
                Function.update_of_ne (ha1 x (List.mem_append_right _ (List.mem_singleton.mpr rfl)))]
            exact hfr a (fun e he => ha1 e (List.mem_append_left _ he)) (by omega))
      exact ⟨stP, 1 + 27 + cP + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨x + 1, st1, 27, cP, by simp [Expr.eval, hr18], by omega, hbody_run, hrunP, rfl⟩)),
        hregsP, hr16P, hr17P, hdL0P, hLatP, hfrP, by simp only [List.length_cons]; omega⟩
  have hsll_init : ∀ x xs, dL = x :: xs → IsSinglyLinkedList mH delNextBase (delNextBase + x) eCap xs := by
    intro x xs hd_eq; subst hd_eq
    refine hsll.2.2.2.of_agree
      (Function.update_of_ne (by have := hsll.1; clear * - hhead_disj_next this; omega) _ _)
      (fun z hz => Function.update_of_ne (by have := hsll.2.2.2.mem_lt z hz; clear * - hhead_disj_next this; omega) _ _)
  obtain ⟨stP, cP, hrunP, hregsP, hr16P, hr17P, hdL0P, hLatP, hfrP, hcP⟩ :=
    hloop dL [] stA rfl
      (fun r hr => by simp [stA, r18, r17, r16, show r ≠ 18 by omega, show r ≠ 17 by omega, show r ≠ 16 by omega])
      (by simp [stA, r18, r17, r16]) (by simp [stA, r18, r17])
      (by simp only [stA, r18, Function.update_self]; cases dL with | nil => exact hsll | cons x _ => exact hsll.2.2.1)
      hsll_init (fun _ h => by cases h) (fun _ h => by simp at h) (fun _ _ _ => rfl)
  -- Sort `delArr` via `bMergeSort`
  let r18s := Function.update stP.regs 18 (hCur + dL.length)
  let r4s := Function.update r18s 4 (hCur + 2 * dL.length)
  have ha18s : Runs w pProg ω (.assign 18 (.bin .add (.reg 16) (.reg 17)))
      stP .normal { stP with regs := r18s } 4 :=
    runs_assign_iff.mpr ⟨hCur + dL.length, by
      simp [Expr.eval, BinOp.eval, hr16P, hr17P, show hCur + dL.length < 2 ^ w by omega], rfl, rfl, rfl⟩
  have ha4s : Runs w pProg ω (.assign 4 (.bin .add (.reg 18) (.reg 17)))
      { stP with regs := r18s } .normal { stP with regs := r4s } 4 :=
    runs_assign_iff.mpr ⟨hCur + 2 * dL.length, by
      simp [Expr.eval, BinOp.eval, r18s, hr17P, show hCur + dL.length + dL.length = hCur + 2 * dL.length by omega,
        hh_w], rfl, rfl, rfl⟩
  obtain ⟨bodyS, hbodyS, oS, stS, cS, hrunS, hpostS, hcS⟩ :=
    hMergeSort dL [hCur, dL.length, hCur + dL.length] stP.mem stP.pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      ⟨hCur, hCur + dL.length, rfl, hw16, by omega, by omega, Or.inl (le_refl _), hLatP,
        fun e he => lt_trans (hdL_lt e he) heCap_w⟩
  rcases hpostS with ⟨aS, scS, L', hargsS, _, hpermS, hsortS, hLatS, hfrS⟩
  rcases List.cons.inj hargsS with ⟨haS_eq, hargsS1⟩
  rcases List.cons.inj hargsS1 with ⟨_, hargsS2⟩
  rcases List.cons.inj hargsS2 with ⟨hscS_eq, _⟩
  rw [← haS_eq] at hLatS hfrS; rw [← hscS_eq] at hfrS
  have hL'_eq : L' = delSet.sort (· ≤ ·) := by
    have h1 := sorted_perm_eq_toFinset_sort hdL_nd hpermS hsortS
    have hset : dL.toFinset = delSet := by ext e; simp [hmem_eq]
    rwa [hset] at h1
  rw [hL'_eq] at hLatS
  let stEnd : State := { mem := stS.mem, regs := Function.update r4s 19 oS.value, pos := stS.pos }
  have hcallS : Runs w pProg ω (.call 19 bMergeSort [.reg 16, .reg 17, .reg 18])
      { stP with regs := r4s } .normal stEnd (cS + 4) := by
    refine runs_call_iff.mpr ⟨[hCur, dL.length, hCur + dL.length], bodyS, oS, stS, cS,
      by simp [evalArgs, Expr.eval, r4s, r18s, hr16P, hr17P], hbodyS, hrunS, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have hfull := bundle_runs_seq_normal ha16 (bundle_runs_seq_normal ha17 (bundle_runs_seq_normal ha18
    (bundle_runs_seq_normal hstH (bundle_runs_seq_normal hrunP (bundle_runs_seq_normal ha18s
      (bundle_runs_seq_normal ha4s hcallS))))))
  have hfr_all : ∀ a, a ≠ delHeadBase + s → (∀ e ∈ dL, a ≠ delNextBase + e) →
      (a < hCur ∨ hCur + 2 * dL.length ≤ a) → stEnd.mem a = st₀.mem a := fun a h1 h2 h3 => by
    dsimp only [stEnd]
    rw [hfrS a (by omega) (by omega), hfrP a h2 (by omega)]
    exact Function.update_of_ne h1 _ _
  refine ⟨stEnd, _, hfull,
    fun r hr h4 => by simp [stEnd, r4s, r18s, h4, show r ≠ 19 by omega, show r ≠ 18 by omega, hregsP r hr],
    by simp [stEnd, r4s], by simp [stEnd, r4s, r18s, hr16P], by simp [stEnd, r4s, r18s, hr17P],
    hcard,
    by dsimp only [stEnd]; rw [hfrS _ (by clear * - hhead_disj_h; omega) (by clear * - hhead_disj_h; omega),
         hfrP _ (fun e he => by have := hdL_lt e he; clear * - hhead_disj_next this; omega)
           (by clear * - hhead_disj_h; omega)]; simp [mH],
    fun e he => by
      have he_lt := hdL_lt e he; dsimp only [stEnd]
      rw [hfrS _ (by clear * - hnext_disj_h he_lt; omega) (by clear * - hnext_disj_h he_lt; omega)]
      exact hdL0P e he,
    hLatS,
    fun a ha => by
      by_cases h1 : a = delHeadBase + s
      · subst h1; dsimp only [stEnd]
        rw [hfrS _ (by clear * - hhead_disj_h; omega) (by clear * - hhead_disj_h; omega),
          hfrP _ (fun e he => by have := hdL_lt e he; clear * - hhead_disj_next this; omega)
            (by clear * - hhead_disj_h; omega)]; simp [mH]
      · by_cases h2 : ∃ e ∈ dL, a = delNextBase + e
        · rcases h2 with ⟨e, he, rfl⟩
          have he_lt := hdL_lt e he; dsimp only [stEnd]
          rw [hfrS _ (by clear * - hnext_disj_h he_lt; omega) (by clear * - hnext_disj_h he_lt; omega)]
          exact hdL0P e he
        · push Not at h2
          exact (hfr_all a h1 h2 (Or.inr ha)).trans (hzero a (by omega)),
    hfr_all, ?_⟩
  dsimp only [mergeSortContract] at hcS; omega

/-! ## 3. Step 3B: `bundleStepEmitPopCands_runs` -/

theorem bundleStepEmitPopCands_runs {w eCap prevBase nextBase p bunCap s candHeadBase hCur : ℕ}
    {pProg : Program} {bMergeSort : ℕ} {ω : ℕ → Bool}
    {B : BundleState} {candSet : Finset ℕ} {st₀ : State}
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hhead_w : candHeadBase + s < 2 ^ w)
    (hh_w : hCur + 2 * candSet.card < 2 ^ w)
    (hhead_disj_blk : candHeadBase + s < p ∨ p + bundleSlotBlockSize bunCap ≤ candHeadBase + s)
    (hhead_disj_h : candHeadBase + s < hCur ∨ hCur + 2 * candSet.card ≤ candHeadBase + s)
    (hblk_disj_h : p + bundleSlotBlockSize bunCap ≤ hCur ∨ hCur + 2 * candSet.card ≤ p)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (hhead_disj_prev : candHeadBase + s < prevBase ∨ prevBase + 2 * eCap ≤ candHeadBase + s)
    (hhead_disj_next : candHeadBase + s < nextBase ∨ nextBase + 2 * eCap ≤ candHeadBase + s)
    (hh_disj_prev : hCur + 2 * candSet.card ≤ prevBase ∨ prevBase + 2 * eCap ≤ hCur)
    (hh_disj_next : hCur + 2 * candSet.card ≤ nextBase ∨ nextBase + 2 * eCap ≤ hCur)
    (hrep : BundleSlotRepCand eCap prevBase nextBase p bunCap B (candHeadBase + s) candSet st₀.mem)
    (hzero : ZeroFrom st₀.mem hCur)
    (hr2 : st₀.regs 2 = s) (hr4 : st₀.regs 4 = hCur) (hr7 : st₀.regs 7 = p)
    (hr8 : st₀.regs 8 = bunCap) (hr15 : st₀.regs 15 = candHeadBase) :
    ∃ stEnd cEnd,
      Runs w pProg ω (bundleStepEmitPopCandsStmt bMergeSort) st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 17, r ≠ 4 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hCur + 2 * candSet.card ∧
      stEnd.regs 18 = hCur ∧ stEnd.regs 19 = candSet.card ∧
      stEnd.mem (candHeadBase + s) = 0 ∧
      BundleSlotRepAt eCap prevBase nextBase p bunCap B stEnd.mem ∧
      ListAt stEnd.mem hCur (candSet.sort (· ≤ ·)) ∧
      ZeroFrom stEnd.mem (hCur + 2 * candSet.card) ∧
      (∀ a, a ≠ candHeadBase + s →
        (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (a < hCur ∨ hCur + 2 * candSet.card ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 200 * candSet.card * (Nat.log 2 (candSet.card + 1) + 1) + 52 * candSet.card + 100 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h4_w : 4 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  obtain ⟨nB, hV, hnB, hE_lt, hbo_lt, hpar0, h0, h1, h2, hdll_all, hpar_all, htail0,
    hseen0, hinCand, hcand_lt, ⟨cL, hsll, hcL_mem⟩, hcandN0⟩ := hrep
  have hcL_nd : cL.Nodup := hsll.nodup
  have hcL_lt : ∀ b ∈ cL, b < bunCap := hsll.mem_lt
  have hcard : cL.length = candSet.card := by
    have hset : cL.toFinset = candSet := by ext b; simp [hcL_mem]
    rw [← hset, List.toFinset_card_of_nodup hcL_nd]
  have hhead_val_w : st₀.mem (candHeadBase + s) < 2 ^ w := by
    cases cL with
    | nil => rw [hsll]; omega
    | cons b _ => rw [hsll.2.2.1]; have := hsll.1; unfold bundleSlotBlockSize at hp_w; omega
  let r18 := Function.update st₀.regs 18 hCur
  let r19 := Function.update r18 19 0
  let r20 := Function.update r19 20 (st₀.mem (candHeadBase + s))
  let mH := Function.update st₀.mem (candHeadBase + s) 0
  let stA : State := { mem := mH, regs := r20, pos := st₀.pos }
  have ha18 : Runs w pProg ω (.assign 18 (.reg 4)) st₀ .normal { st₀ with regs := r18 } 2 :=
    runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, hr4], rfl, rfl, rfl⟩
  have ha19 : Runs w pProg ω (.assign 19 (.const 0)) { st₀ with regs := r18 } .normal { st₀ with regs := r19 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha20 : Runs w pProg ω (.assign 20 (.load (.bin .add (.reg 15) (.reg 2))))
      { st₀ with regs := r19 } .normal { st₀ with regs := r20 } 5 :=
    runs_assign_iff.mpr ⟨st₀.mem (candHeadBase + s), by
      simp [Expr.eval, BinOp.eval, r19, r18, hr15, hr2, hhead_w], rfl, rfl, rfl⟩
  have hstH : Runs w pProg ω (.store (.bin .add (.reg 15) (.reg 2)) (.const 0))
      { st₀ with regs := r20 } .normal stA 5 :=
    runs_store_iff.mpr ⟨candHeadBase + s, 0,
      by simp [Expr.eval, BinOp.eval, r20, r19, r18, hr15, hr2, hhead_w],
      by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  let body : Stmt :=
    .assign 21 (.bin .sub (.reg 20) (.const 1)) ;;
    .assign 22 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
      (.bin .mul (.const 5) (.reg 8))) (.reg 21)) ;;
    .assign 20 (.load (.reg 22)) ;;
    .store (.reg 22) (.const 0) ;;
    .store (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
      (.bin .mul (.const 4) (.reg 8))) (.reg 21)) (.const 0) ;;
    .store (.bin .add (.reg 18) (.reg 19)) (.reg 21) ;;
    .assign 19 (.bin .add (.reg 19) (.const 1))
  have hloop : ∀ (rem pre : List ℕ) (st : State),
      pre ++ rem = cL →
      (∀ r ≤ 17, st.regs r = st₀.regs r) →
      st.regs 18 = hCur → st.regs 19 = pre.length →
      st.regs 20 = (match rem with | [] => 0 | b :: _ => b + 1) →
      (∀ b bs, rem = b :: bs → IsSinglyLinkedList st.mem (bsCandNextBase p bunCap) (bsCandNextBase p bunCap + b) bunCap bs) →
      (∀ b ∈ pre, st.mem (bsInCandBase p bunCap + b) = 0 ∧ st.mem (bsCandNextBase p bunCap + b) = 0) →
      ListAt st.mem hCur pre →
      (∀ a, (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (a < hCur ∨ hCur + pre.length ≤ a) → st.mem a = mH a) →
      (∀ b < bunCap, b ∉ pre → st.mem (bsInCandBase p bunCap + b) = mH (bsInCandBase p bunCap + b) ∧
        st.mem (bsCandNextBase p bunCap + b) = mH (bsCandNextBase p bunCap + b)) →
      ∃ stP cP,
        Runs w pProg ω (.loop (.reg 20) body) st .normal stP cP ∧
        (∀ r ≤ 17, stP.regs r = st₀.regs r) ∧
        stP.regs 18 = hCur ∧ stP.regs 19 = cL.length ∧
        (∀ b < bunCap, stP.mem (bsInCandBase p bunCap + b) = 0 ∧ stP.mem (bsCandNextBase p bunCap + b) = 0) ∧
        ListAt stP.mem hCur cL ∧
        (∀ a, (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
          (a < hCur ∨ hCur + cL.length ≤ a) → stP.mem a = mH a) ∧
        cP ≤ 48 * rem.length + 2 := by
    intro rem
    induction rem with
    | nil =>
      intro pre st hcat hregs hr18 hr19 hr20 _ hpre0 hLat hfr hrem_eq
      simp only [List.append_nil] at hcat
      refine ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr20], rfl, rfl, rfl⟩),
        hregs, hr18, hr19.trans (congrArg List.length hcat), fun b hb => ?_, hcat ▸ hLat,
        hcat ▸ hfr, by omega⟩
      by_cases hbp : b ∈ pre
      · exact hpre0 b hbp
      · have hnotS : b ∉ candSet := fun h => hbp (hcat ▸ (hcL_mem b).mpr h)
        have ⟨he1, he2⟩ := hrem_eq b hb hbp
        rw [he1, he2]; dsimp only [mH]
        rw [Function.update_of_ne (by unfold bsInCandBase; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk hb; omega),
            Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk hb; omega),
            hinCand b hb, ite_eq_right hnotS, hcandN0 b hb hnotS]; exact ⟨rfl, rfl⟩
    | cons b bs ih =>
      intro pre st hcat hregs hr18 hr19 hr20 hbs_sll hpre0 hLat hfr hrem_eq
      have hb_mem : b ∈ cL := hcat ▸ List.mem_append_right _ List.mem_cons_self
      have hb_lt : b < bunCap := hcL_lt b hb_mem
      have hlen_lt : pre.length < cL.length := by rw [← hcat]; simp
      have hsll_tl := hbs_sll b bs rfl
      have hnxt_eq : st.mem (bsCandNextBase p bunCap + b) = match bs with | [] => 0 | y :: _ => y + 1 := by
        cases bs with | nil => exact hsll_tl | cons y ys => exact hsll_tl.2.2.1
      have hnxt_w : st.mem (bsCandNextBase p bunCap + b) < 2 ^ w := by
        rw [hnxt_eq]; cases bs with
        | nil => dsimp only; omega
        | cons y _ => dsimp only; have := hsll_tl.1; unfold bundleSlotBlockSize at hp_w; omega
      let r21 := Function.update st.regs 21 b
      let r22 := Function.update r21 22 (bsCandNextBase p bunCap + b)
      let r20' := Function.update r22 20 (st.mem (bsCandNextBase p bunCap + b))
      let m1 := Function.update st.mem (bsCandNextBase p bunCap + b) 0
      let m2 := Function.update m1 (bsInCandBase p bunCap + b) 0
      let m3 := Function.update m2 (hCur + pre.length) b
      let r19' := Function.update r20' 19 (pre.length + 1)
      let st1 : State := { mem := m3, regs := r19', pos := st.pos }
      have hs1 : Runs w pProg ω (.assign 21 (.bin .sub (.reg 20) (.const 1))) st .normal { st with regs := r21 } 4 :=
        runs_assign_iff.mpr ⟨b, by simp [Expr.eval, BinOp.eval, hr20, h1_w, show b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega], rfl, rfl, rfl⟩
      have hs2 : Runs w pProg ω (.assign 22 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
          (.bin .mul (.const 5) (.reg 8))) (.reg 21)))
          { st with regs := r21 } .normal { st with regs := r22 } 10 :=
        runs_assign_iff.mpr ⟨bsCandNextBase p bunCap + b, by
          simp [Expr.eval, BinOp.eval, r21, hregs 7 (by decide), hregs 8 (by decide), hr7, hr8, h3_w, h5_w,
            bsCandNextBase, show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show 5 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show p + 3 + 5 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show p + 3 + 5 * bunCap + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w pProg ω (.assign 20 (.load (.reg 22))) { st with regs := r22 } .normal { st with regs := r20' } 3 :=
        runs_assign_iff.mpr ⟨st.mem (bsCandNextBase p bunCap + b), by
          simp [Expr.eval, r22, bsCandNextBase], rfl, rfl, rfl⟩
      have hs4 : Runs w pProg ω (.store (.reg 22) (.const 0)) { st with regs := r20' } .normal { mem := m1, regs := r20', pos := st.pos } 3 :=
        runs_store_iff.mpr ⟨bsCandNextBase p bunCap + b, 0,
          by simp [Expr.eval, r20', r22, bsCandNextBase],
          by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      have hs5 : Runs w pProg ω (.store (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
          (.bin .mul (.const 4) (.reg 8))) (.reg 21)) (.const 0))
          { mem := m1, regs := r20', pos := st.pos } .normal { mem := m2, regs := r20', pos := st.pos } 11 :=
        runs_store_iff.mpr ⟨bsInCandBase p bunCap + b, 0, by
          simp [Expr.eval, BinOp.eval, r20', r22, r21, hregs 7 (by decide), hregs 8 (by decide), hr7, hr8, h3_w, h4_w,
            bsInCandBase, show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show 4 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show p + 3 + 4 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
            show p + 3 + 4 * bunCap + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
          by simp [Expr.eval, h0_w], rfl, rfl, by simp [Expr.size]⟩
      have hs6 : Runs w pProg ω (.store (.bin .add (.reg 18) (.reg 19)) (.reg 21))
          { mem := m2, regs := r20', pos := st.pos } .normal { mem := m3, regs := r20', pos := st.pos } 5 :=
        runs_store_iff.mpr ⟨hCur + pre.length, b,
          by simp [Expr.eval, BinOp.eval, r20', r22, r21, hr18, hr19, show hCur + pre.length < 2 ^ w by omega],
          by simp [Expr.eval, r20', r22, r21], rfl, rfl, rfl⟩
      have hs7 : Runs w pProg ω (.assign 19 (.bin .add (.reg 19) (.const 1)))
          { mem := m3, regs := r20', pos := st.pos } .normal st1 4 :=
        runs_assign_iff.mpr ⟨pre.length + 1, by
          simp [Expr.eval, BinOp.eval, r20', r22, r21, hr19, h1_w, show pre.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hbody_run : Runs w pProg ω body st .normal st1 46 :=
        bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2 (bundle_runs_seq_normal hs3
          (bundle_runs_seq_normal hs4 (bundle_runs_seq_normal hs5 (bundle_runs_seq_normal hs6 hs7)))))
      have hb_notin_bs : b ∉ bs := by
        rw [← hcat, List.nodup_append] at hcL_nd; exact (List.nodup_cons.mp hcL_nd.2.1).1
      have hbs_next : ∀ y ys, bs = y :: ys →
          IsSinglyLinkedList m3 (bsCandNextBase p bunCap) (bsCandNextBase p bunCap + y) bunCap ys := by
        intro y ys hbs_eq; subst hbs_eq
        refine hsll_tl.2.2.2.of_agree ?_ ?_
        · have hy_lt := hsll_tl.1; have hyb : y ≠ b := fun h => hb_notin_bs (h ▸ List.mem_cons_self)
          dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hy_lt hlen_lt hcard; omega),
              Function.update_of_ne (by unfold bsCandNextBase bsInCandBase; omega),
              Function.update_of_ne (by omega)]
        · intro z hz; have hz_lt := hsll_tl.2.2.2.mem_lt z hz; have hzb : z ≠ b := fun h => hb_notin_bs (h ▸ List.mem_cons_of_mem _ hz)
          dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hz_lt hlen_lt hcard; omega),
              Function.update_of_ne (by unfold bsCandNextBase bsInCandBase; omega),
              Function.update_of_ne (by omega)]
      obtain ⟨stP, cP, hrunP, hregsP, hr18P, hr19P, hscr0P, hLatP, hfrP, hcP⟩ :=
        ih (pre ++ [b]) st1 (by simpa [List.append_assoc] using hcat)
          (fun r hr => by simp [st1, r19', r20', r22, r21, show r ≠ 19 by omega, show r ≠ 20 by omega, show r ≠ 22 by omega, show r ≠ 21 by omega, hregs r hr])
          (by simp [st1, r19', r20', r22, r21, hr18]) (by simp [st1, r19'])
          (by dsimp only [st1, r19', r20']; rw [Function.update_of_ne (by decide), Function.update_self, hnxt_eq]; cases bs <;> rfl)
          hbs_next
          (fun c hc => by
            dsimp only [st1, m3, m2, m1]
            rcases List.mem_append.mp hc with hcp | hcb
            · have hc_lt := hcL_lt c (hcat ▸ List.mem_append_left _ hcp)
              have hcb' : c ≠ b := by
                intro heq; subst heq; rw [← hcat, List.nodup_append] at hcL_nd
                exact hcL_nd.2.2 c hcp c List.mem_cons_self rfl
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hc_lt hlen_lt hcard; omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsInCandBase bsCandNextBase; omega)]
                exact (hpre0 c hcp).1
              · rw [Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hc_lt hlen_lt hcard; omega),
                    Function.update_of_ne (by unfold bsInCandBase bsCandNextBase; omega), Function.update_of_ne (by omega)]
                exact (hpre0 c hcp).2
            · have hceq : c = b := List.mem_singleton.mp hcb; subst hceq
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb_lt hlen_lt hcard; omega)]; simp
              · rw [Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb_lt hlen_lt hcard; omega),
                    Function.update_of_ne (by unfold bsInCandBase bsCandNextBase; omega)]; simp)
          (fun i hi => by
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hip : i < pre.length
            · rw [List.getElem_append_left hip]; dsimp only [st1, m3, m2, m1]
              rw [Function.update_of_ne (by omega),
                  Function.update_of_ne (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb_lt hip hlen_lt hcard; omega),
                  Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb_lt hip hlen_lt hcard; omega)]
              exact hLat i hip
            · have hieq : i = pre.length := by omega
              subst hieq; rw [List.getElem_append_right (le_refl _)]; simp [st1, m3])
          (fun a ha1 ha2 => by
            dsimp only [st1, m3, m2, m1]
            simp only [List.length_append, List.length_singleton] at ha2
            rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by unfold bsInCandBase; unfold bsInCandBase bundleSlotBlockSize at ha1; clear * - ha1 hb_lt; omega),
                Function.update_of_ne (by unfold bsCandNextBase; unfold bsInCandBase bundleSlotBlockSize at ha1; clear * - ha1 hb_lt; omega)]
            exact hfr a ha1 (by omega))
          (fun c hc hnc => by
            dsimp only [st1, m3, m2, m1]
            have hcp : c ∉ pre := fun h => hnc (List.mem_append_left _ h)
            have hcb : c ≠ b := fun h => hnc (List.mem_append_right _ (List.mem_singleton.mpr h))
            refine ⟨?_, ?_⟩
            · rw [Function.update_of_ne (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hc hlen_lt hcard; omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsInCandBase bsCandNextBase; omega)]
              exact (hrem_eq c hc hcp).1
            · rw [Function.update_of_ne (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hc hlen_lt hcard; omega),
                  Function.update_of_ne (by unfold bsInCandBase bsCandNextBase; omega), Function.update_of_ne (by omega)]
              exact (hrem_eq c hc hcp).2)
      exact ⟨stP, 1 + 46 + cP + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨b + 1, st1, 46, cP, by simp [Expr.eval, hr20], by omega, hbody_run, hrunP, rfl⟩)),
        hregsP, hr18P, hr19P, hscr0P, hLatP, hfrP, by simp only [List.length_cons]; omega⟩
  have hsll_init : ∀ b bs, cL = b :: bs →
      IsSinglyLinkedList mH (bsCandNextBase p bunCap) (bsCandNextBase p bunCap + b) bunCap bs := by
    intro b bs hc_eq; subst hc_eq
    refine hsll.2.2.2.of_agree
      (Function.update_of_ne (by have := hsll.1; unfold bsCandNextBase; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk this; omega) _ _)
      (fun z hz => Function.update_of_ne (by have := hsll.2.2.2.mem_lt z hz; unfold bsCandNextBase; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk this; omega) _ _)
  obtain ⟨stP, cP, hrunP, hregsP, hr18P, hr19P, hscr0P, hLatP, hfrP, hcP⟩ :=
    hloop cL [] stA rfl
      (fun r hr => by simp [stA, r20, r19, r18, show r ≠ 20 by omega, show r ≠ 19 by omega, show r ≠ 18 by omega])
      (by simp [stA, r20, r19, r18]) (by simp [stA, r20, r19])
      (by simp only [stA, r20, Function.update_self]; cases cL with | nil => exact hsll | cons b _ => exact hsll.2.2.1)
      hsll_init (fun _ h => by cases h) (fun _ h => by simp at h) (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩)
  -- Sort `candArr` via `bMergeSort`
  let r20s := Function.update stP.regs 20 (hCur + cL.length)
  let r4s := Function.update r20s 4 (hCur + 2 * cL.length)
  have ha20s : Runs w pProg ω (.assign 20 (.bin .add (.reg 18) (.reg 19)))
      stP .normal { stP with regs := r20s } 4 :=
    runs_assign_iff.mpr ⟨hCur + cL.length, by
      simp [Expr.eval, BinOp.eval, hr18P, hr19P, show hCur + cL.length < 2 ^ w by omega], rfl, rfl, rfl⟩
  have ha4s : Runs w pProg ω (.assign 4 (.bin .add (.reg 20) (.reg 19)))
      { stP with regs := r20s } .normal { stP with regs := r4s } 4 :=
    runs_assign_iff.mpr ⟨hCur + 2 * cL.length, by
      simp [Expr.eval, BinOp.eval, r20s, hr19P, show hCur + cL.length + cL.length = hCur + 2 * cL.length by omega,
        show hCur + 2 * cL.length < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨bodyS, hbodyS, oS, stS, cS, hrunS, hpostS, hcS⟩ :=
    hMergeSort cL [hCur, cL.length, hCur + cL.length] stP.mem stP.pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      ⟨hCur, hCur + cL.length, rfl, hw16, by omega, by omega, Or.inl (le_refl _), hLatP,
        fun b hb => by have := hcL_lt b hb; unfold bundleSlotBlockSize at hp_w; omega⟩
  rcases hpostS with ⟨aS, scS, L', hargsS, _, hpermS, hsortS, hLatS, hfrS⟩
  rcases List.cons.inj hargsS with ⟨haS_eq, hargsS1⟩
  rcases List.cons.inj hargsS1 with ⟨_, hargsS2⟩
  rcases List.cons.inj hargsS2 with ⟨hscS_eq, _⟩
  rw [← haS_eq] at hLatS hfrS; rw [← hscS_eq] at hfrS
  have hL'_eq : L' = candSet.sort (· ≤ ·) := by
    have h1 := sorted_perm_eq_toFinset_sort hcL_nd hpermS hsortS
    have hset : cL.toFinset = candSet := by ext b; simp [hcL_mem]
    rwa [hset] at h1
  rw [hL'_eq] at hLatS
  let stEnd : State := { mem := stS.mem, regs := Function.update r4s 21 oS.value, pos := stS.pos }
  have hcallS : Runs w pProg ω (.call 21 bMergeSort [.reg 18, .reg 19, .reg 20])
      { stP with regs := r4s } .normal stEnd (cS + 4) := by
    refine runs_call_iff.mpr ⟨[hCur, cL.length, hCur + cL.length], bodyS, oS, stS, cS,
      by simp [evalArgs, Expr.eval, r4s, r20s, hr18P, hr19P], hbodyS, hrunS, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have hfull := bundle_runs_seq_normal ha18 (bundle_runs_seq_normal ha19 (bundle_runs_seq_normal ha20
    (bundle_runs_seq_normal hstH (bundle_runs_seq_normal hrunP (bundle_runs_seq_normal ha20s
      (bundle_runs_seq_normal ha4s hcallS))))))
  have hfr_all : ∀ a, a ≠ candHeadBase + s →
      (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      (a < hCur ∨ hCur + 2 * candSet.card ≤ a) → stEnd.mem a = st₀.mem a := fun a h1 h2 h3 => by
    dsimp only [stEnd]
    rw [hfrS a (by omega) (by omega), hfrP a h2 (by omega)]
    exact Function.update_of_ne h1 _ _
  have hblk_pres : ∀ a, p ≤ a → a < bsInCandBase p bunCap → stEnd.mem a = st₀.mem a := fun a ha1 ha2 =>
    hfr_all a (by unfold bsInCandBase at ha2; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk ha1 ha2; omega)
      (Or.inl ha2)
      (by unfold bsInCandBase at ha2; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h ha1 ha2; omega)
  have hrep_clean : BundleSlotRepAt eCap prevBase nextBase p bunCap B stEnd.mem := by
    refine ⟨nB, hV, hnB, hE_lt, hbo_lt, hpar0,
      (hblk_pres _ (by unfold bsOffBunCap; omega) (by unfold bsOffBunCap bsInCandBase; omega)).trans h0,
      (hblk_pres _ (by unfold bsOffNB; omega) (by unfold bsOffNB bsInCandBase; omega)).trans h1,
      (hblk_pres _ (by unfold bsOffNE; omega) (by unfold bsOffNE bsInCandBase; omega)).trans h2,
      ?_, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨L, hL, hlen, hmem⟩ := hdll_all b hb
      have hb_cap : b < bunCap := lt_of_lt_of_le hb hnB
      refine ⟨L, hL.of_agree
        (hblk_pres _ (by unfold bsHeadBase; omega) (by unfold bsHeadBase bsInCandBase; omega))
        (fun k hk => by
          have hk' := hL.2.1 k hk
          exact hfr_all _ (by clear * - hhead_disj_prev hk'; omega)
            (by unfold bsInCandBase bundleSlotBlockSize; unfold bundleSlotBlockSize at hblk_prev; clear * - hblk_prev hk'; omega)
            (by clear * - hh_disj_prev hk'; omega))
        (fun k hk => by
          have hk' := hL.2.1 k hk
          exact hfr_all _ (by clear * - hhead_disj_next hk'; omega)
            (by unfold bsInCandBase bundleSlotBlockSize; unfold bundleSlotBlockSize at hblk_next; clear * - hblk_next hk'; omega)
            (by clear * - hh_disj_next hk'; omega)),
        (hblk_pres _ (by unfold bsSizeBase; omega) (by unfold bsSizeBase bsInCandBase; omega)).trans hlen, hmem⟩
    · intro b hb hem
      have hb_cap : b < bunCap := lt_of_lt_of_le hb hnB
      exact (hblk_pres _ (by unfold bsParentBase; omega) (by unfold bsParentBase bsInCandBase; omega)).trans (hpar_all b hb hem)
    · intro b hge hlt
      obtain ⟨t1, t2, t3⟩ := htail0 b hge hlt
      exact ⟨(hblk_pres _ (by unfold bsHeadBase; omega) (by unfold bsHeadBase bsInCandBase; omega)).trans t1,
        (hblk_pres _ (by unfold bsSizeBase; omega) (by unfold bsSizeBase bsInCandBase; omega)).trans t2,
        (hblk_pres _ (by unfold bsParentBase; omega) (by unfold bsParentBase bsInCandBase; omega)).trans t3⟩
    · intro b hb
      refine ⟨(hblk_pres _ (by unfold bsSeenBase; omega) (by unfold bsSeenBase bsInCandBase; omega)).trans (hseen0 b hb),
        ?_, ?_⟩
      · dsimp only [stEnd]
        rw [hfrS _ (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)
          (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)]
        exact (hscr0P b hb).1
      · dsimp only [stEnd]
        rw [hfrS _ (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)
          (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)]
        exact (hscr0P b hb).2
  refine ⟨stEnd, _, hfull,
    fun r hr h4 => by simp [stEnd, r4s, r20s, h4, show r ≠ 21 by omega, show r ≠ 20 by omega, hregsP r hr],
    by simp [stEnd, r4s, hcard], by simp [stEnd, r4s, r20s, hr18P], by simp [stEnd, r4s, r20s, hr19P, hcard],
    by dsimp only [stEnd]
       rw [hfrS _ (by clear * - hhead_disj_h hcard; omega) (by clear * - hhead_disj_h hcard; omega),
         hfrP _ (by unfold bsInCandBase bundleSlotBlockSize; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk; omega)
           (by clear * - hhead_disj_h hcard; omega)]; simp [mH],
    hrep_clean, hLatS,
    fun a ha => by
      by_cases h1 : a = candHeadBase + s
      · subst h1; dsimp only [stEnd]
        rw [hfrS _ (by clear * - hhead_disj_h hcard; omega) (by clear * - hhead_disj_h hcard; omega),
          hfrP _ (by unfold bsInCandBase bundleSlotBlockSize; unfold bundleSlotBlockSize at hhead_disj_blk; clear * - hhead_disj_blk; omega)
            (by clear * - hhead_disj_h hcard; omega)]; simp [mH]
      · by_cases h2 : bsInCandBase p bunCap ≤ a ∧ a < p + bundleSlotBlockSize bunCap
        · rcases h2 with ⟨h2a, h2b⟩
          by_cases h3 : a < bsCandNextBase p bunCap
          · have hb : a - bsInCandBase p bunCap < bunCap := by
              unfold bsInCandBase at h2a ⊢; unfold bsCandNextBase at h3; clear * - h2a h3; omega
            have heq : a = bsInCandBase p bunCap + (a - bsInCandBase p bunCap) := by omega
            set b := a - bsInCandBase p bunCap
            rw [heq]; dsimp only [stEnd]
            rw [hfrS _ (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)
              (by unfold bsInCandBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)]
            exact (hscr0P b hb).1
          · have hb : a - bsCandNextBase p bunCap < bunCap := by
              unfold bsCandNextBase at h3 ⊢; unfold bundleSlotBlockSize at h2b; clear * - h2b h3; omega
            have heq : a = bsCandNextBase p bunCap + (a - bsCandNextBase p bunCap) := by omega
            set b := a - bsCandNextBase p bunCap
            rw [heq]; dsimp only [stEnd]
            rw [hfrS _ (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)
              (by unfold bsCandNextBase; unfold bundleSlotBlockSize at hblk_disj_h; clear * - hblk_disj_h hb hcard; omega)]
            exact (hscr0P b hb).2
        · exact (hfr_all a h1 (by omega) (Or.inr ha)).trans (hzero a (by omega)),
    hfr_all, ?_⟩
  dsimp only [mergeSortContract] at hcS; rw [hcard] at hcS; omega

end

end MinCostFlow.SparseCore.Program
