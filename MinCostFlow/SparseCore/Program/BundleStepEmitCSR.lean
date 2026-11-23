module

public import MinCostFlow.SparseCore.Program.BundleStepEmitProcs
public import MinCostFlow.SparseCore.Program.BundleStepScanBridge

/-!
# Phase 3 scanned-end CSR builder verification (`BundleStepEmitCSR`)

Verifies `bundleStepEmitBuildCSRStmt`: consumes `btCurBunBase[s]` / `btCurTagBase[s]` (clearing
both to `0`), scatters the `M_s` scanned `(b, packedVK)` pairs onto `bsSeenBase[b]` using 2-word
heap nodes, and flattens them into flat CSR arrays `r13 = candScanOff[0..candCnt]` and
`r14 = candScanBuf[0..M_s)`, restoring `bsSeenBase[b] = 0` for every `b < bunCap` in
`≤ 80 * M_s + 50 * candCnt + 80` steps and `3 * M_s + candCnt + 1` heap words.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Heap-allocated singly-linked list of 2-word bucket nodes `[pk, nextPtr]` in `[lo, hi)`
(`1 ≤ lo`, terminated by `0`). -/
def BucketListAt (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → List ℕ → Prop
  | ptr, [] => ptr = 0
  | ptr, pk :: rest =>
      lo ≤ ptr ∧ ptr + 2 ≤ hi ∧
      mem ptr = pk ∧ BucketListAt mem lo hi (mem (ptr + 1)) rest

/-- Flat CSR representation of `scan_j` grouped by `cands`:
`mem[offPtr + i]` is the cumulative count of scanned entries for `cands.take i`, and for each
`i < cands.length`, `mem[bufPtr + off[i] .. bufPtr + off[i+1])` is a permutation of the packed
keys of `scan_j.filter (·.1 == cands[i])`. -/
def CSRAt (eCap : ℕ) (mem : ℕ → ℕ) (offPtr bufPtr : ℕ) (cands : List ℕ)
    (scan_j : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ i ≤ cands.length,
    mem (offPtr + i) = ((cands.take i).map fun b => (scan_j.filter fun t => t.1 == b).length).sum) ∧
  (∀ i (hi : i < cands.length),
    ∃ L_pk : List ℕ,
      L_pk.Perm ((scan_j.filter fun t => t.1 == cands[i]).map fun t => packEndKey eCap t.2.1 t.2.2) ∧
      ListAt mem (bufPtr + mem (offPtr + i)) L_pk)

end

public section

lemma bucketListAt_mono {lo hi hi' ptr : ℕ} {mem mem' : ℕ → ℕ} {L : List ℕ}
    (h : BucketListAt mem lo hi ptr L) (hle : hi ≤ hi')
    (hag : ∀ a, lo ≤ a → a < hi → mem' a = mem a) :
    BucketListAt mem' lo hi' ptr L := by
  induction L generalizing ptr with
  | nil => exact h
  | cons pk rest ih =>
    rcases h with ⟨hlo, hhi, h0, hrest⟩
    refine ⟨hlo, by omega, (hag ptr hlo (by omega)).trans h0, ?_⟩
    rw [hag (ptr + 1) (by omega) (by omega)]
    exact ih hrest

lemma sum_filter_lengths_eq {cands : List ℕ} {L : List (ℕ × ℕ × ℕ)}
    (hnd : cands.Nodup) (hin : ∀ t ∈ L, t.1 ∈ cands) :
    (cands.map fun b => (L.filter fun t => t.1 == b).length).sum = L.length := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    have ha := hin a List.mem_cons_self
    have htl := ih fun t ht => hin t (List.mem_cons_of_mem _ ht)
    simp only [List.length_cons, List.filter_cons]
    have hsplit : ∀ (cs : List ℕ), cs.Nodup →
        (cs.map fun b => (if (a.1 == b) = true then a :: tl.filter (fun t => t.1 == b)
          else tl.filter (fun t => t.1 == b)).length).sum =
        (if a.1 ∈ cs then 1 else 0) +
          (cs.map fun b => (tl.filter fun t => t.1 == b).length).sum := by
      intro cs
      induction cs with
      | nil => intro _; simp
      | cons c rest ihr =>
        intro hndc
        obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hndc
        simp only [List.map_cons, List.sum_cons, List.mem_cons]
        rw [ihr hnd']
        by_cases hac : a.1 = c
        · subst hac; simp [hnot]; omega
        · simp [hac]; omega
    rw [hsplit cands hnd, ite_eq_left ha, htl]
    omega

private lemma scatter_pass1_runs {w eCap p bunCap hStart h₀ hCur : ℕ}
    {pProg : Program} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hhStart_pos : 1 ≤ hStart) (hh0_le : h₀ ≤ hCur)
    (hp_lt_hCur : p + bundleSlotBlockSize bunCap ≤ hCur)
    (hp_disj_scan : p + bundleSlotBlockSize bunCap ≤ hStart ∨ h₀ ≤ p) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (hNow : ℕ) (buckets : ℕ → List ℕ) (st : State),
      hCur ≤ hNow →
      hNow + 2 * L.length < 2 ^ w →
      (∀ t ∈ L, t.1 < bunCap ∧ packEndKey eCap t.2.1 t.2.2 < 2 ^ w) →
      ScanNodesAt eCap st.mem hStart h₀ (st.regs 25) L →
      (∀ b < bunCap, BucketListAt st.mem hCur hNow (st.mem (bsSeenBase p bunCap + b)) (buckets b)) →
      st.regs 4 = hNow →
      st.regs 26 = bsSeenBase p bunCap →
      ∃ st1 c1,
        Runs w pProg ω
          (.loop (.reg 25)
            (.assign 27 (.load (.reg 25)) ;;
             .assign 28 (.load (.bin .add (.reg 25) (.const 1))) ;;
             .assign 25 (.load (.bin .add (.reg 25) (.const 2))) ;;
             .assign 29 (.load (.bin .add (.reg 26) (.reg 27))) ;;
             .store (.reg 4) (.reg 28) ;;
             .store (.bin .add (.reg 4) (.const 1)) (.reg 29) ;;
             .store (.bin .add (.reg 26) (.reg 27)) (.reg 4) ;;
             .assign 4 (.bin .add (.reg 4) (.const 2))))
          st .normal st1 c1 ∧
        (∀ r ≤ 24, r ≠ 4 → st1.regs r = st.regs r) ∧
        st1.regs 4 = hNow + 2 * L.length ∧
        st1.regs 26 = bsSeenBase p bunCap ∧
        (∀ b < bunCap, BucketListAt st1.mem hCur (hNow + 2 * L.length)
          (st1.mem (bsSeenBase p bunCap + b))
          (((L.filter fun t => t.1 == b).reverse.map fun t => packEndKey eCap t.2.1 t.2.2) ++ buckets b)) ∧
        (∀ a, (a < bsSeenBase p bunCap ∨ bsSeenBase p bunCap + bunCap ≤ a) →
          (a < hNow ∨ hNow + 2 * L.length ≤ a) → st1.mem a = st.mem a) ∧
        c1 ≤ 50 * L.length + 5 := by
  intro L
  induction L with
  | nil =>
    intro hNow buckets st _ _ _ hsn hbk hr4 hr26
    have hr25 : st.regs 25 = 0 := hsn
    refine ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr25], rfl, rfl, rfl⟩),
      fun _ _ _ => rfl, by simpa using hr4, hr26, fun b hb => by simpa using hbk b hb,
      fun _ _ _ => rfl, by omega⟩
  | cons hd tl ih =>
    rcases hd with ⟨b, v, key⟩
    intro hNow buckets st hhCur_le hh_w hL_ok hsn hbk hr4 hr26
    rcases hsn with ⟨hptr_lo, hptr_hi, hmb, hmpk, hsn_tl⟩
    set ptr := st.regs 25
    set pk := packEndKey eCap v key
    set nextPtr := st.mem (ptr + 2)
    set oldSeen := st.mem (bsSeenBase p bunCap + b)
    obtain ⟨hb_lt, hpk_w⟩ := hL_ok (b, v, key) List.mem_cons_self
    have h1_w : 1 < 2 ^ w := by omega
    have h2_w : 2 < 2 ^ w := by omega
    have hptr_pos : ptr ≠ 0 := by omega
    have hseen_w : bsSeenBase p bunCap + b < 2 ^ w := by
      unfold bsSeenBase; unfold bundleSlotBlockSize at hp_w; omega
    let r27 := Function.update st.regs 27 b
    let r28 := Function.update r27 28 pk
    let r25 := Function.update r28 25 nextPtr
    let r29 := Function.update r25 29 oldSeen
    let m1 := Function.update st.mem hNow pk
    let m2 := Function.update m1 (hNow + 1) oldSeen
    let m3 := Function.update m2 (bsSeenBase p bunCap + b) hNow
    let r4' := Function.update r29 4 (hNow + 2)
    let stA : State := { mem := m3, regs := r4', pos := st.pos }
    have ha27 : Runs w pProg ω (.assign 27 (.load (.reg 25))) st .normal { st with regs := r27 } 3 :=
      runs_assign_iff.mpr ⟨b, by simp [Expr.eval, ptr, hmb], rfl, rfl, rfl⟩
    have ha28 : Runs w pProg ω (.assign 28 (.load (.bin .add (.reg 25) (.const 1))))
        { st with regs := r27 } .normal { st with regs := r28 } 5 :=
      runs_assign_iff.mpr ⟨pk, by
        simp [Expr.eval, BinOp.eval, r27, ptr, h1_w, show ptr + 1 < 2 ^ w by omega, hmpk, pk], rfl, rfl, rfl⟩
    have ha25 : Runs w pProg ω (.assign 25 (.load (.bin .add (.reg 25) (.const 2))))
        { st with regs := r28 } .normal { st with regs := r25 } 5 :=
      runs_assign_iff.mpr ⟨nextPtr, by
        simp [Expr.eval, BinOp.eval, r28, r27, ptr, h2_w, show ptr + 2 < 2 ^ w by omega, nextPtr], rfl, rfl, rfl⟩
    have ha29 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 26) (.reg 27))))
        { st with regs := r25 } .normal { st with regs := r29 } 5 :=
      runs_assign_iff.mpr ⟨oldSeen, by
        simp [Expr.eval, BinOp.eval, r25, r28, r27, hr26, hseen_w, oldSeen], rfl, rfl, rfl⟩
    have hs1 : Runs w pProg ω (.store (.reg 4) (.reg 28))
        { st with regs := r29 } .normal { mem := m1, regs := r29, pos := st.pos } 3 :=
      runs_store_iff.mpr ⟨hNow, pk, by simp [Expr.eval, r29, r25, r28, r27, hr4],
        by simp [Expr.eval, r29, r25, r28], rfl, rfl, rfl⟩
    have hh_w' : hNow + 2 * (tl.length + 1) < 2 ^ w := by simpa only [List.length_cons] using hh_w
    have hs2 : Runs w pProg ω (.store (.bin .add (.reg 4) (.const 1)) (.reg 29))
        { mem := m1, regs := r29, pos := st.pos } .normal { mem := m2, regs := r29, pos := st.pos } 5 :=
      runs_store_iff.mpr ⟨hNow + 1, oldSeen,
        by simp [Expr.eval, BinOp.eval, r29, r25, r28, r27, hr4, h1_w, show hNow + 1 < 2 ^ w by omega],
        by simp [Expr.eval, r29], rfl, rfl, rfl⟩
    have hs3 : Runs w pProg ω (.store (.bin .add (.reg 26) (.reg 27)) (.reg 4))
        { mem := m2, regs := r29, pos := st.pos } .normal { mem := m3, regs := r29, pos := st.pos } 5 :=
      runs_store_iff.mpr ⟨bsSeenBase p bunCap + b, hNow,
        by simp [Expr.eval, BinOp.eval, r29, r25, r28, r27, hr26, hseen_w],
        by simp [Expr.eval, r29, r25, r28, r27, hr4], rfl, rfl, rfl⟩
    have ha4 : Runs w pProg ω (.assign 4 (.bin .add (.reg 4) (.const 2)))
        { mem := m3, regs := r29, pos := st.pos } .normal stA 4 :=
      runs_assign_iff.mpr ⟨hNow + 2,
        by simp [Expr.eval, BinOp.eval, r29, r25, r28, r27, hr4, h2_w, show hNow + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hbody := bundle_runs_seq_normal ha27 (bundle_runs_seq_normal ha28 (bundle_runs_seq_normal ha25
      (bundle_runs_seq_normal ha29 (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2
        (bundle_runs_seq_normal hs3 ha4))))))
    have hm3_eq : ∀ a, a ≠ bsSeenBase p bunCap + b → a ≠ hNow → a ≠ hNow + 1 → m3 a = st.mem a := by
      intro a h1 h2 h3; dsimp only [m3, m2, m1]
      rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2]
    have hseen_lt_hCur : bsSeenBase p bunCap + b < hCur := by
      unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega
    have hsn_A : ScanNodesAt eCap stA.mem hStart h₀ (stA.regs 25) tl := by
      simp only [stA, r4', r29, r25, Function.update_of_ne (by decide : (25 : ℕ) ≠ 4),
        Function.update_of_ne (by decide : (25 : ℕ) ≠ 29), Function.update_self]
      refine scanNodesAt_mono hsn_tl (le_refl _) fun a ha1 ha2 => ?_
      refine hm3_eq a ?_ (by omega) (by omega)
      unfold bsSeenBase; unfold bundleSlotBlockSize at hp_disj_scan; omega
    let buckets' : ℕ → List ℕ := Function.update buckets b (pk :: buckets b)
    have hbk_A : ∀ b' < bunCap, BucketListAt stA.mem hCur (hNow + 2)
        (stA.mem (bsSeenBase p bunCap + b')) (buckets' b') := by
      intro b' hb'
      dsimp only [stA, buckets']
      by_cases hbb : b' = b
      · subst hbb
        have hm3_b : m3 (bsSeenBase p bunCap + b') = hNow := Function.update_self _ _ _
        have hm3_0 : m3 hNow = pk := by
          dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        have hm3_1 : m3 (hNow + 1) = oldSeen := by
          dsimp only [m3, m2]
          rw [Function.update_of_ne (by omega), Function.update_self]
        rw [Function.update_self, hm3_b]
        refine ⟨hhCur_le, le_refl _, hm3_0, ?_⟩
        rw [hm3_1]
        exact bucketListAt_mono (hbk b' hb_lt) (by omega) fun a ha1 ha2 =>
          hm3_eq a (by omega) (by omega) (by omega)
      · have hseen_lt_b' : bsSeenBase p bunCap + b' < hCur := by
          unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega
        rw [Function.update_of_ne hbb, hm3_eq _ (by omega) (by omega) (by omega)]
        exact bucketListAt_mono (hbk b' hb') (by omega) fun a ha1 ha2 =>
          hm3_eq a (by omega) (by omega) (by omega)
    obtain ⟨st1, c1, hrest, hregs1, hr4_1, hr26_1, hbk1, hfr1, hc1⟩ :=
      ih (hNow + 2) buckets' stA (by omega) (by omega)
        (fun t ht => hL_ok t (List.mem_cons_of_mem _ ht)) hsn_A hbk_A
        (by simp [stA, r4']) (by simp [stA, r4', r29, r25, r28, r27, hr26])
    have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨ptr, stA, _, c1,
      by simp [Expr.eval, ptr], hptr_pos, hbody, hrest, rfl⟩))
    refine ⟨st1, _, hloop, fun r hr hne4 => by
        rw [hregs1 r hr hne4]
        simp [stA, r4', r29, r25, r28, r27, hne4, show r ≠ 29 by omega, show r ≠ 25 by omega,
          show r ≠ 28 by omega, show r ≠ 27 by omega],
      by simp only [List.length_cons]; omega, hr26_1, fun b' hb' => ?_,
      fun a ha1 ha2 => by
        simp only [List.length_cons] at ha2
        rw [hfr1 a ha1 (by omega)]
        exact hm3_eq a (by omega) (by omega) (by omega),
      by simp only [List.length_cons, Expr.size] at *; omega⟩
    have h1 := hbk1 b' hb'
    have hlist_eq : ((((b, v, key) :: tl).filter fun t => t.1 == b').reverse.map fun t => packEndKey eCap t.2.1 t.2.2) ++ buckets b' =
        ((tl.filter fun t => t.1 == b').reverse.map fun t => packEndKey eCap t.2.1 t.2.2) ++ buckets' b' := by
      dsimp only [buckets']
      by_cases hbb : b' = b
      · subst hbb; simp [pk, List.append_assoc]
      · simp [show (b == b') = false from beq_false_of_ne (Ne.symm hbb), Function.update_of_ne hbb]
    rw [hlist_eq]
    simpa only [List.length_cons, show hNow + 2 + 2 * tl.length = hNow + 2 * (tl.length + 1) by omega] using h1

private lemma flatten_inner_runs {w lo hi bufPtr : ℕ} {pProg : Program} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hlo_pos : 1 ≤ lo) (hdisj_buf : hi ≤ bufPtr) :
    ∀ (L : List ℕ) (off : ℕ) (st : State),
      bufPtr + off + L.length < 2 ^ w →
      hi < 2 ^ w →
      BucketListAt st.mem lo hi (st.regs 30) L →
      st.regs 14 = bufPtr →
      st.regs 27 = off →
      ∃ st1 c1,
        Runs w pProg ω
          (.loop (.reg 30)
            (.assign 31 (.load (.reg 30)) ;;
             .store (.bin .add (.reg 14) (.reg 27)) (.reg 31) ;;
             .assign 27 (.bin .add (.reg 27) (.const 1)) ;;
             .assign 30 (.load (.bin .add (.reg 30) (.const 1)))))
          st .normal st1 c1 ∧
        (∀ r ≤ 29, r ≠ 27 → st1.regs r = st.regs r) ∧
        st1.regs 27 = off + L.length ∧
        ListAt st1.mem (bufPtr + off) L ∧
        (∀ a, (a < bufPtr + off ∨ bufPtr + off + L.length ≤ a) → st1.mem a = st.mem a) ∧
        c1 ≤ 25 * L.length + 5 := by
  intro L
  induction L with
  | nil =>
    intro off st _ _ hbk _ hr27
    have hr30 : st.regs 30 = 0 := hbk
    refine ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr30], rfl, rfl, rfl⟩),
      fun _ _ _ => rfl, by simpa using hr27, (fun _ hlt => by cases hlt), fun _ _ => rfl, by omega⟩
  | cons pk rest ih =>
    intro off st hbuf_w hhi_w hbk hr14 hr27
    rcases hbk with ⟨hlo, hhi, hmpk, hbk_rest⟩
    set ptr := st.regs 30
    set nextPtr := st.mem (ptr + 1)
    have h1_w : 1 < 2 ^ w := by omega
    have hptr_pos : ptr ≠ 0 := by omega
    let r31 := Function.update st.regs 31 pk
    let m1 := Function.update st.mem (bufPtr + off) pk
    let r27' := Function.update r31 27 (off + 1)
    let r30' := Function.update r27' 30 nextPtr
    let stA : State := { mem := m1, regs := r30', pos := st.pos }
    have ha31 : Runs w pProg ω (.assign 31 (.load (.reg 30))) st .normal { st with regs := r31 } 3 :=
      runs_assign_iff.mpr ⟨pk, by simp [Expr.eval, ptr, hmpk], rfl, rfl, rfl⟩
    have hs1 : Runs w pProg ω (.store (.bin .add (.reg 14) (.reg 27)) (.reg 31))
        { st with regs := r31 } .normal { mem := m1, regs := r31, pos := st.pos } 5 :=
      runs_store_iff.mpr ⟨bufPtr + off, pk,
        by simp [Expr.eval, BinOp.eval, r31, hr14, hr27, show bufPtr + off < 2 ^ w by omega],
        by simp [Expr.eval, r31], rfl, rfl, rfl⟩
    have ha27 : Runs w pProg ω (.assign 27 (.bin .add (.reg 27) (.const 1)))
        { mem := m1, regs := r31, pos := st.pos } .normal { mem := m1, regs := r27', pos := st.pos } 4 :=
      runs_assign_iff.mpr ⟨off + 1,
        by simp [Expr.eval, BinOp.eval, r31, hr27, h1_w, show off + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have ha30 : Runs w pProg ω (.assign 30 (.load (.bin .add (.reg 30) (.const 1))))
        { mem := m1, regs := r27', pos := st.pos } .normal stA 5 :=
      runs_assign_iff.mpr ⟨nextPtr, by
        simp [Expr.eval, BinOp.eval, r27', r31, ptr, h1_w, show ptr + 1 < 2 ^ w by omega]
        dsimp only [m1]
        rw [Function.update_of_ne (by omega)], rfl, rfl, rfl⟩
    have hbody := bundle_runs_seq_normal ha31 (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal ha27 ha30))
    have hbk_A : BucketListAt stA.mem lo hi (stA.regs 30) rest := by
      simp only [stA, r30', Function.update_self]
      exact bucketListAt_mono hbk_rest (le_refl _) fun a _ ha2 => by
        dsimp only [m1]; exact Function.update_of_ne (by omega) _ _
    obtain ⟨st1, c1, hrest, hregs1, hr27_1, hLat1, hfr1, hc1⟩ :=
      ih (off + 1) stA (by simp only [List.length_cons] at hbuf_w; omega) hhi_w hbk_A
        (by simp [stA, r30', r27', r31, hr14]) (by simp [stA, r30', r27'])
    have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨ptr, stA, _, c1,
      by simp [Expr.eval, ptr], hptr_pos, hbody, hrest, rfl⟩))
    refine ⟨st1, _, hloop, fun r hr hne27 => by
        rw [hregs1 r hr hne27]
        simp [stA, r30', r27', r31, hne27, show r ≠ 30 by omega, show r ≠ 31 by omega],
      by simp only [List.length_cons]; omega, fun idx hidx => ?_, fun a ha => by
        simp only [List.length_cons] at ha
        rw [hfr1 a (by omega)]
        dsimp only [stA, m1]; exact Function.update_of_ne (by omega) _ _,
      by simp only [List.length_cons, Expr.size] at *; omega⟩
    cases idx with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [hfr1 (bufPtr + off) (Or.inl (by omega))]
      simp [stA, m1]
    | succ idx' =>
      simp only [List.length_cons] at hidx
      simpa [Nat.add_assoc, show 1 + idx' = idx' + 1 by omega] using hLat1 idx' (by omega)

/-- End-to-end verification of `bundleStepEmitBuildCSRStmt`: consumes `btCurBunBase[s]` and
`btCurTagBase[s]` (clearing both to `0`), builds flat CSR arrays `candScanOff` (in `r13`) and
`candScanBuf` (in `r14`), sets `r23 = scan_j.length`, and restores `bsSeenBase[b] = 0` for all
`b < bunCap`. -/
theorem bundleStepEmitBuildCSR_runs {w slotCap eCap tbl s p bunCap candArr hStart h₀ hCur : ℕ}
    {pProg : Program} {ω : ℕ → Bool}
    {cands : List ℕ} {scan_j : List (ℕ × ℕ × ℕ)} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hs_lt : s < slotCap)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hcand_w : candArr + cands.length < 2 ^ w)
    (hh_w : hCur + 3 * scan_j.length + cands.length + 1 < 2 ^ w)
    (hhStart_pos : 1 ≤ hStart) (hhStart_le : hStart ≤ h₀) (hh0_le : h₀ ≤ hCur)
    (hcur_lt_hStart : btCurTagBase tbl slotCap eCap + slotCap ≤ hStart)
    (hp_lt_hCur : p + bundleSlotBlockSize bunCap ≤ hCur)
    (hp_disj_scan : p + bundleSlotBlockSize bunCap ≤ hStart ∨ h₀ ≤ p)
    (hp_disj_tbl : p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
    (hcand_lt_hCur : candArr + cands.length ≤ hCur)
    (hcand_disj_blk : candArr + cands.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ candArr)
    (hcand_disj_cur : candArr + cands.length ≤ btCurBunBase tbl slotCap eCap ∨
      btCurTagBase tbl slotCap eCap + slotCap ≤ candArr)
    (hcands_nd : cands.Nodup)
    (hcands_lt : ∀ b ∈ cands, b < bunCap)
    (hscan_in_cands : ∀ t ∈ scan_j, t.1 ∈ cands)
    (hscan_pk_w : ∀ t ∈ scan_j, packEndKey eCap t.2.1 t.2.2 < 2 ^ w)
    (hmem_sc : st₀.mem tbl = slotCap)
    (hseen0 : ∀ b < bunCap, st₀.mem (bsSeenBase p bunCap + b) = 0)
    (hscan : ScanNodesAt eCap st₀.mem hStart h₀ (st₀.mem (btCurBunBase tbl slotCap eCap + s)) scan_j)
    (htag : st₀.mem (btCurTagBase tbl slotCap eCap + s) = scan_j.length)
    (hcandLat : ListAt st₀.mem candArr cands)
    (hzero : ZeroFrom st₀.mem hCur)
    (hr0 : st₀.regs 0 = tbl) (hr2 : st₀.regs 2 = s) (hr4 : st₀.regs 4 = hCur)
    (hr7 : st₀.regs 7 = p) (hr8 : st₀.regs 8 = bunCap)
    (hr15 : st₀.regs 15 = btSlotCandHeadBase tbl slotCap eCap)
    (hr18 : st₀.regs 18 = candArr) (hr19 : st₀.regs 19 = cands.length) :
    let offPtr := hCur + 2 * scan_j.length
    let bufPtr := offPtr + cands.length + 1
    let hEnd := bufPtr + scan_j.length
    ∃ stEnd cEnd,
      Runs w pProg ω bundleStepEmitBuildCSRStmt st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 19, r ≠ 4 → r ≠ 13 → r ≠ 14 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hEnd ∧ stEnd.regs 13 = offPtr ∧ stEnd.regs 14 = bufPtr ∧
      stEnd.regs 23 = scan_j.length ∧
      stEnd.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      stEnd.mem (btCurTagBase tbl slotCap eCap + s) = 0 ∧
      CSRAt eCap stEnd.mem offPtr bufPtr cands scan_j ∧
      ZeroFrom stEnd.mem hEnd ∧
      (∀ a, a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
        (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 80 * scan_j.length + 50 * cands.length + 80 := by
  intro offPtr bufPtr hEnd
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hcb_eq : btSlotCandHeadBase tbl slotCap eCap + slotCap + s = btCurBunBase tbl slotCap eCap + s := by
    unfold btSlotCandHeadBase btCurBunBase; omega
  have hct_eq : btCurBunBase tbl slotCap eCap + s + slotCap = btCurTagBase tbl slotCap eCap + s := by
    unfold btCurBunBase btCurTagBase; omega
  have hcb_lt_hStart : btCurBunBase tbl slotCap eCap + s < hStart := by
    unfold btCurTagBase at hcur_lt_hStart; unfold btCurBunBase; omega
  have hct_lt_hStart : btCurTagBase tbl slotCap eCap + s < hStart := by omega
  have hcb_ne_ct : btCurBunBase tbl slotCap eCap + s ≠ btCurTagBase tbl slotCap eCap + s := by
    unfold btCurBunBase btCurTagBase; omega
  set oldHead := st₀.mem (btCurBunBase tbl slotCap eCap + s)
  -- Header: load oldHead, M_s, clear curBun[s] & curTag[s], compute seenBase
  let r25a := Function.update st₀.regs 25 slotCap
  let r26a := Function.update r25a 26 (btCurBunBase tbl slotCap eCap + s)
  let r27a := Function.update r26a 27 (btCurTagBase tbl slotCap eCap + s)
  let r25b := Function.update r27a 25 oldHead
  let r23a := Function.update r25b 23 scan_j.length
  let m1 := Function.update st₀.mem (btCurBunBase tbl slotCap eCap + s) 0
  let m2 := Function.update m1 (btCurTagBase tbl slotCap eCap + s) 0
  let r26b := Function.update r23a 26 (bsSeenBase p bunCap)
  let stH : State := { mem := m2, regs := r26b, pos := st₀.pos }
  have ha25a : Runs w pProg ω (.assign 25 (.load (.reg 0))) st₀ .normal { st₀ with regs := r25a } 3 :=
    runs_assign_iff.mpr ⟨slotCap, by simp [Expr.eval, hr0, hmem_sc], rfl, rfl, rfl⟩
  have ha26a : Runs w pProg ω (.assign 26 (.bin .add (.bin .add (.reg 15) (.reg 25)) (.reg 2)))
      { st₀ with regs := r25a } .normal { st₀ with regs := r26a } 6 :=
    runs_assign_iff.mpr ⟨btCurBunBase tbl slotCap eCap + s, by
      simp [Expr.eval, BinOp.eval, r25a, hr15, hr2,
        show btSlotCandHeadBase tbl slotCap eCap + slotCap < 2 ^ w by unfold btSlotCandHeadBase; omega,
        hcb_eq, show btCurBunBase tbl slotCap eCap + s < 2 ^ w by unfold btCurBunBase; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha27a : Runs w pProg ω (.assign 27 (.bin .add (.reg 26) (.reg 25)))
      { st₀ with regs := r26a } .normal { st₀ with regs := r27a } 4 :=
    runs_assign_iff.mpr ⟨btCurTagBase tbl slotCap eCap + s, by
      simp [Expr.eval, BinOp.eval, r26a, r25a, hct_eq,
        show btCurTagBase tbl slotCap eCap + s < 2 ^ w by unfold btCurTagBase; omega], rfl, rfl, rfl⟩
  have ha25b : Runs w pProg ω (.assign 25 (.load (.reg 26)))
      { st₀ with regs := r27a } .normal { st₀ with regs := r25b } 3 :=
    runs_assign_iff.mpr ⟨oldHead, by simp [Expr.eval, r27a, r26a, oldHead], rfl, rfl, rfl⟩
  have ha23a : Runs w pProg ω (.assign 23 (.load (.reg 27)))
      { st₀ with regs := r25b } .normal { st₀ with regs := r23a } 3 :=
    runs_assign_iff.mpr ⟨scan_j.length, by simp [Expr.eval, r25b, r27a, htag], rfl, rfl, rfl⟩
  have hs_cb : Runs w pProg ω (.store (.reg 26) (.const 0))
      { st₀ with regs := r23a } .normal { mem := m1, regs := r23a, pos := st₀.pos } 3 :=
    runs_store_iff.mpr ⟨btCurBunBase tbl slotCap eCap + s, 0,
      by simp [Expr.eval, r23a, r25b, r27a, r26a], by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have hs_ct : Runs w pProg ω (.store (.reg 27) (.const 0))
      { mem := m1, regs := r23a, pos := st₀.pos } .normal { mem := m2, regs := r23a, pos := st₀.pos } 3 :=
    runs_store_iff.mpr ⟨btCurTagBase tbl slotCap eCap + s, 0,
      by simp [Expr.eval, r23a, r25b, r27a], by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha26b : Runs w pProg ω (.assign 26 (.bin .add (.bin .add (.reg 7) (.const 3)) (.bin .mul (.const 3) (.reg 8))))
      { mem := m2, regs := r23a, pos := st₀.pos } .normal stH 8 :=
    runs_assign_iff.mpr ⟨bsSeenBase p bunCap, by
      simp [Expr.eval, BinOp.eval, r23a, r25b, r27a, r26a, r25a, hr7, hr8, h3_w,
        show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show 3 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + 3 * bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega, bsSeenBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hm2_eq : ∀ a, a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
      m2 a = st₀.mem a := fun a h1 h2 => by dsimp only [m2, m1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have hcur_disj_blk : ∀ a, p ≤ a → a < p + bundleSlotBlockSize bunCap →
      a ≠ btCurBunBase tbl slotCap eCap + s ∧ a ≠ btCurTagBase tbl slotCap eCap + s := fun a h1 h2 => by
    unfold bundleTableFixedSize at hp_disj_tbl
    exact ⟨by unfold btCurBunBase; omega, by unfold btCurTagBase; omega⟩
  -- Pass 1: scatter
  obtain ⟨stP1, cP1, hrunP1, hregsP1, hr4P1, hr26P1, hbkP1, hfrP1, hcP1⟩ :=
    scatter_pass1_runs (eCap := eCap) (p := p) (bunCap := bunCap) (hStart := hStart) (h₀ := h₀) (hCur := hCur)
      hw16 hp_w hhStart_pos hh0_le hp_lt_hCur hp_disj_scan scan_j hCur (fun _ => []) stH
      (le_refl _) (by omega)
      (fun t ht => ⟨hcands_lt t.1 (hscan_in_cands t ht), hscan_pk_w t ht⟩)
      (by
        simp only [stH, r26b, r23a, r25b, Function.update_of_ne (by decide : (25 : ℕ) ≠ 26),
          Function.update_of_ne (by decide : (25 : ℕ) ≠ 23), Function.update_self]
        exact scanNodesAt_mono hscan (le_refl _) fun a ha1 _ => hm2_eq a (by omega) (by omega))
      (fun b hb => by
        dsimp only [stH]
        have hdisj := hcur_disj_blk (bsSeenBase p bunCap + b) (by unfold bsSeenBase; omega)
          (by unfold bsSeenBase bundleSlotBlockSize; omega)
        rw [hm2_eq _ hdisj.1 hdisj.2, hseen0 b hb]; rfl)
      (by simp [stH, r26b, r23a, r25b, r27a, r26a, r25a, hr4]) (by simp [stH, r26b])
  -- Allocate CSR pointers: r13 := offPtr, r14 := bufPtr, r4 := hEnd, r27 := 0
  let r13 := Function.update stP1.regs 13 offPtr
  let r14 := Function.update r13 14 bufPtr
  let r4e := Function.update r14 4 hEnd
  let r27_0 := Function.update r4e 27 0
  let stA : State := { stP1 with regs := r27_0 }
  have ha13 : Runs w pProg ω (.assign 13 (.reg 4)) stP1 .normal { stP1 with regs := r13 } 2 :=
    runs_assign_iff.mpr ⟨offPtr, by simp [Expr.eval, hr4P1, offPtr], rfl, rfl, rfl⟩
  have ha14 : Runs w pProg ω (.assign 14 (.bin .add (.bin .add (.reg 13) (.reg 19)) (.const 1)))
      { stP1 with regs := r13 } .normal { stP1 with regs := r14 } 6 :=
    runs_assign_iff.mpr ⟨bufPtr, by
      have hr19 : stP1.regs 19 = cands.length := (hregsP1 19 (by decide) (by decide)).trans
        (by simp [stH, r26b, r23a, r25b, r27a, r26a, r25a, hr19])
      simp [Expr.eval, BinOp.eval, r13, hr19, h1_w, show offPtr + cands.length < 2 ^ w by omega,
        show bufPtr < 2 ^ w by omega, bufPtr], rfl, rfl, by simp [Expr.size]⟩
  have ha4e : Runs w pProg ω (.assign 4 (.bin .add (.reg 14) (.reg 23)))
      { stP1 with regs := r14 } .normal { stP1 with regs := r4e } 4 :=
    runs_assign_iff.mpr ⟨hEnd, by
      have hr23 : stP1.regs 23 = scan_j.length := (hregsP1 23 (by decide) (by decide)).trans
        (by simp [stH, r26b, r23a])
      simp [Expr.eval, BinOp.eval, r14, r13, hr23, show hEnd < 2 ^ w by omega, hEnd], rfl, rfl, rfl⟩
  have ha27_0 : Runs w pProg ω (.assign 27 (.const 0)) { stP1 with regs := r4e } .normal stA 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  -- Pass 2: `forRange 28 0 cands.length`
  let prefLen : ℕ → ℕ := fun i => ((cands.take i).map fun b => (scan_j.filter fun t => t.1 == b).length).sum
  have hpref_le : ∀ i ≤ cands.length, prefLen i ≤ scan_j.length := fun i _ => by
    have h1 := congrArg (fun l => (l.map fun b => (scan_j.filter fun t => t.1 == b).length).sum) (List.take_append_drop i cands)
    rw [List.map_append, List.sum_append, sum_filter_lengths_eq hcands_nd hscan_in_cands] at h1
    dsimp only [prefLen]; omega
  let body2 : Stmt :=
    .assign 29 (.load (.bin .add (.reg 18) (.reg 28))) ;;
    .store (.bin .add (.reg 13) (.reg 28)) (.reg 27) ;;
    .assign 30 (.load (.bin .add (.reg 26) (.reg 29))) ;;
    .store (.bin .add (.reg 26) (.reg 29)) (.const 0) ;;
    .loop (.reg 30)
      (.assign 31 (.load (.reg 30)) ;;
       .store (.bin .add (.reg 14) (.reg 27)) (.reg 31) ;;
       .assign 27 (.bin .add (.reg 27) (.const 1)) ;;
       .assign 30 (.load (.bin .add (.reg 30) (.const 1))))
  let Inv2 : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 26, st.regs r = stA.regs r) ∧
    st.regs 27 = prefLen i ∧ st.regs 28 = i ∧
    (∀ t < i, st.mem (offPtr + t) = prefLen t) ∧
    (∀ t (ht : t < i) (ht' : t < cands.length),
      ListAt st.mem (bufPtr + prefLen t)
        (((scan_j.filter fun x => x.1 == cands[t]'ht').reverse).map fun x => packEndKey eCap x.2.1 x.2.2)) ∧
    (∀ b < bunCap, b ∈ cands.take i → st.mem (bsSeenBase p bunCap + b) = 0) ∧
    (∀ b < bunCap, b ∉ cands.take i →
      st.mem (bsSeenBase p bunCap + b) = stP1.mem (bsSeenBase p bunCap + b)) ∧
    (∀ a, (a < bsSeenBase p bunCap ∨ bsSeenBase p bunCap + bunCap ≤ a) →
      (a < offPtr ∨ offPtr + i ≤ a) → (a < bufPtr ∨ bufPtr + prefLen i ≤ a) →
      st.mem a = stP1.mem a)
  let sc2 : ℕ → ℕ := fun i => 25 * (scan_j.filter fun t => t.1 == cands.getD i 0).length + 30
  obtain ⟨stP2, cP2, _, hrunP2, hInvP2, hcP2⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 28) (lo := .const 0) (hi := .reg 19)
      (body := body2) (fun _ _ => 0) Inv2 sc2 cands.length (by omega) (fun _ => by omega)
      (st₀ := stA) (a₀ := ())
      (by
        refine ⟨by simp [Expr.eval, h0_w], ?_, rfl⟩
        exact ⟨fun r hr => by simp [show r ≠ 28 by omega], by simp [stA, r27_0, prefLen], by simp,
          fun _ h => by omega, fun _ h => by omega, fun _ _ h => by simp at h,
          fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.1)
      (fun _ _ st _ hI => by
        have h19 := hI.1 19 (by decide)
        simp [Expr.eval, h19, stA, r27_0, r4e, r14, r13, hregsP1 19 (by decide) (by decide),
          stH, r26b, r23a, r25b, r27a, r26a, r25a, hr19])
      (fun i _ st hi ⟨hregs, hr27, hr28, hoffs, hbufs, hseenZ, hseenK, hfr2⟩ => by
        set b := cands[i]'hi
        set Lb := ((scan_j.filter fun t => t.1 == b).reverse).map fun t => packEndKey eCap t.2.1 t.2.2
        have hb_lt : b < bunCap := hcands_lt b (List.getElem_mem hi)
        have hLb_len : Lb.length = (scan_j.filter fun t => t.1 == b).length := by simp [Lb]
        have hpref_succ : prefLen (i + 1) = prefLen i + Lb.length := by
          simp only [prefLen, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
          simp [Lb, b]
        have hpref_succ_le : prefLen (i + 1) ≤ scan_j.length := hpref_le (i + 1) (by omega)
        have hb_notin : b ∉ cands.take i := fun hm => by
          obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
          rw [List.length_take, Nat.min_eq_left (by omega)] at hj
          rw [List.getElem_take] at hjb
          have := hcands_nd.getElem_inj_iff.mp hjb; omega
        have hmem_b : st.mem (candArr + i) = b := by
          rw [hfr2 (candArr + i)
            (by unfold bsSeenBase; unfold bundleSlotBlockSize at hcand_disj_blk; omega)
            (Or.inl (by omega)) (Or.inl (by omega)),
            hfrP1 (candArr + i)
              (by unfold bsSeenBase; unfold bundleSlotBlockSize at hcand_disj_blk; omega)
              (Or.inl (by omega))]
          have hcb_ne : candArr + i ≠ btCurBunBase tbl slotCap eCap + s := by
            unfold btCurBunBase btCurTagBase at hcand_disj_cur; unfold btCurBunBase; omega
          have hct_ne : candArr + i ≠ btCurTagBase tbl slotCap eCap + s := by
            unfold btCurBunBase btCurTagBase at hcand_disj_cur; unfold btCurTagBase; omega
          exact (hm2_eq (candArr + i) hcb_ne hct_ne).trans (hcandLat i hi)
        have hr13s : st.regs 13 = offPtr := (hregs 13 (by decide)).trans (by simp [stA, r27_0, r4e, r14, r13])
        have hr14s : st.regs 14 = bufPtr := (hregs 14 (by decide)).trans (by simp [stA, r27_0, r4e, r14])
        have hr18s : st.regs 18 = candArr := (hregs 18 (by decide)).trans (by
          simp [stA, r27_0, r4e, r14, r13, hregsP1 18 (by decide) (by decide),
            stH, r26b, r23a, r25b, r27a, r26a, r25a, hr18])
        have hr26s : st.regs 26 = bsSeenBase p bunCap := (hregs 26 (le_refl _)).trans (by
          simp [stA, r27_0, r4e, r14, r13, hr26P1])
        have hseen_b_eq : st.mem (bsSeenBase p bunCap + b) = stP1.mem (bsSeenBase p bunCap + b) :=
          hseenK b hb_lt hb_notin
        set pNode := stP1.mem (bsSeenBase p bunCap + b)
        let r29 := Function.update st.regs 29 b
        let mA := Function.update st.mem (offPtr + i) (prefLen i)
        let r30 := Function.update r29 30 pNode
        let mB := Function.update mA (bsSeenBase p bunCap + b) 0
        let stB : State := { mem := mB, regs := r30, pos := st.pos }
        have ha29 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 18) (.reg 28))))
            st .normal { st with regs := r29 } 5 :=
          runs_assign_iff.mpr ⟨b, by simp [Expr.eval, BinOp.eval, hr18s, hr28, show candArr + i < 2 ^ w by omega, hmem_b], rfl, rfl, rfl⟩
        have hs_off : Runs w pProg ω (.store (.bin .add (.reg 13) (.reg 28)) (.reg 27))
            { st with regs := r29 } .normal { mem := mA, regs := r29, pos := st.pos } 5 :=
          runs_store_iff.mpr ⟨offPtr + i, prefLen i,
            by simp [Expr.eval, BinOp.eval, r29, hr13s, hr28, show offPtr + i < 2 ^ w by omega],
            by simp [Expr.eval, r29, hr27], rfl, rfl, rfl⟩
        have hseen_w : bsSeenBase p bunCap + b < 2 ^ w := by
          unfold bsSeenBase; unfold bundleSlotBlockSize at hp_w; omega
        have hseen_lt_off : bsSeenBase p bunCap + b < offPtr := by
          unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega
        have ha30 : Runs w pProg ω (.assign 30 (.load (.bin .add (.reg 26) (.reg 29))))
            { mem := mA, regs := r29, pos := st.pos } .normal { mem := mA, regs := r30, pos := st.pos } 5 :=
          runs_assign_iff.mpr ⟨pNode, by
            simp [Expr.eval, BinOp.eval, r29, hr26s, hseen_w]
            dsimp only [mA]; rw [Function.update_of_ne (by omega), hseen_b_eq], rfl, rfl, rfl⟩
        have hs_z : Runs w pProg ω (.store (.bin .add (.reg 26) (.reg 29)) (.const 0))
            { mem := mA, regs := r30, pos := st.pos } .normal stB 5 :=
          runs_store_iff.mpr ⟨bsSeenBase p bunCap + b, 0,
            by simp [Expr.eval, BinOp.eval, r30, r29, hr26s, hseen_w],
            by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
        have hbk_B : BucketListAt stB.mem hCur offPtr (stB.regs 30) Lb := by
          simp only [stB, r30, Function.update_self]
          have h1 := hbkP1 b hb_lt
          simp only [List.append_nil] at h1
          exact bucketListAt_mono h1 (le_refl _) fun a ha1 ha2 => by
            dsimp only [mB, mA]
            have hne_seen : a ≠ bsSeenBase p bunCap + b := by
              unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega
            rw [Function.update_of_ne hne_seen, Function.update_of_ne (by omega)]
            exact hfr2 a (by unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega)
              (Or.inl ha2) (Or.inl (by omega))
        obtain ⟨stC, cIn, hrunIn, hregsIn, hr27C, hLatC, hfrIn, hcIn⟩ :=
          flatten_inner_runs (lo := hCur) (hi := offPtr) (bufPtr := bufPtr)
            hw16 (by omega) (by omega) Lb (prefLen i) stB (by omega) (by omega) hbk_B
            (by simp [stB, r30, r29, hr14s]) (by simp [stB, r30, r29, hr27])
        have hbody_run := bundle_runs_seq_normal ha29 (bundle_runs_seq_normal hs_off
          (bundle_runs_seq_normal ha30 (bundle_runs_seq_normal hs_z hrunIn)))
        refine ⟨stC, _, (), hbody_run, (hregsIn 28 (by decide) (by decide)).trans (by simp [stB, r30, r29, hr28]),
          ?_, by dsimp only [sc2]; rw [List.getD_eq_getElem _ _ hi, ← hLb_len]; omega⟩
        refine ⟨fun r hr => by
            simp only [Function.update_of_ne (show r ≠ 28 by omega)]
            rw [hregsIn r (by omega) (by omega)]
            simp [stB, r30, r29, show r ≠ 30 by omega, show r ≠ 29 by omega, hregs r hr],
          by simp [hr27C, hpref_succ], by simp, ?_, ?_, ?_, ?_, ?_⟩
        · intro t ht
          rw [hfrIn (offPtr + t) (Or.inl (by omega))]
          dsimp only [stB, mB, mA]
          rw [Function.update_of_ne (by omega)]
          by_cases hti : t = i
          · subst hti; simp
          · rw [Function.update_of_ne (by omega)]; exact hoffs t (by omega)
        · intro t ht ht'
          by_cases hti : t = i
          · subst hti; exact hLatC
          · intro idx hidx
            have hle_t : prefLen (t + 1) ≤ prefLen i := by
              have h1 := congrArg (fun l => (l.map fun c => (scan_j.filter fun x => x.1 == c).length).sum)
                (List.take_append_drop (t + 1) (cands.take i))
              rw [List.take_take, Nat.min_eq_left (by omega), List.map_append, List.sum_append] at h1
              change prefLen (t + 1) + _ = prefLen i at h1; omega
            have hlen_t : prefLen (t + 1) = prefLen t + (scan_j.filter fun x => x.1 == cands[t]'ht').length := by
              simp only [prefLen, List.take_succ_eq_append_getElem ht', List.map_append, List.sum_append]; simp
            rw [hfrIn (bufPtr + prefLen t + idx) (Or.inl (by simp at hidx; omega))]
            dsimp only [stB, mB, mA]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hbufs t (by omega) ht' idx hidx
        · intro b' hb' hmem
          rw [hfrIn (bsSeenBase p bunCap + b') (Or.inl (by unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega))]
          dsimp only [stB, mB, mA]
          rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hm_prev | rfl
          · have hne : b' ≠ b := fun h => hb_notin (h ▸ hm_prev)
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega)]
            exact hseenZ b' hb' hm_prev
          · exact Function.update_self (bsSeenBase p bunCap + b) 0 mA
        · intro b' hb' hnot
          have hne : b' ≠ b := fun h => hnot (by
            subst h; rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_right _ List.mem_cons_self)
          have hnot_i : b' ∉ cands.take i := fun h => hnot (by
            rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_left _ h)
          rw [hfrIn (bsSeenBase p bunCap + b') (Or.inl (by unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega))]
          dsimp only [stB, mB, mA]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsSeenBase; unfold bundleSlotBlockSize at hp_lt_hCur; omega)]
          exact hseenK b' hb' hnot_i
        · intro a ha1 ha2 ha3
          have hne_buf : a < bufPtr + prefLen i ∨ bufPtr + prefLen i + Lb.length ≤ a := by
            clear * - ha3 hpref_succ; omega
          rw [hfrIn a hne_buf]
          dsimp only [stB, mB, mA]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr2 a ha1 (by omega) (by clear * - ha3 hpref_succ; omega))
  -- Trailing store: `mem[candScanOff + candCnt] := off` (`= scan_j.length`)
  rcases hInvP2 with ⟨hregs2, hr27_2, _, hoffs2, hbufs2, hseenZ2, hseenK2, hfr2_end⟩
  have hpref_full : prefLen cands.length = scan_j.length := by
    simp only [prefLen, List.take_length]; exact sum_filter_lengths_eq hcands_nd hscan_in_cands
  let mEnd := Function.update stP2.mem (offPtr + cands.length) scan_j.length
  let stEnd : State := { stP2 with mem := mEnd }
  have hs_last : Runs w pProg ω (.store (.bin .add (.reg 13) (.reg 19)) (.reg 27)) stP2 .normal stEnd 5 :=
    runs_store_iff.mpr ⟨offPtr + cands.length, scan_j.length,
      by simp [Expr.eval, BinOp.eval, hregs2 13 (by decide), hregs2 19 (by decide), stA, r27_0, r4e, r14, r13,
           hregsP1 19 (by decide) (by decide), stH, r26b, r23a, r25b, r27a, r26a, r25a, hr19,
           show offPtr + cands.length < 2 ^ w by omega],
      by simp [Expr.eval, hr27_2, hpref_full], rfl, rfl, rfl⟩
  have hrc2 : rangeCost sc2 0 cands.length = 25 * scan_j.length + 30 * cands.length := by
    have hgo : ∀ k ≤ cands.length, rangeCost sc2 0 k = 25 * prefLen k + 30 * k := by
      intro k; induction k with
      | zero => intro _; simp [rangeCost, prefLen]
      | succ k ih =>
        intro hk
        have hkl : k < cands.length := by omega
        rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih (by omega)]
        simp only [sc2, prefLen, List.take_succ_eq_append_getElem hkl, List.map_append, List.sum_append,
          List.getD_eq_getElem _ _ hkl]
        simp; ring
    rw [hgo cands.length (le_refl _), hpref_full]
  simp only [Expr.size] at hcP2; rw [hrc2] at hcP2
  have hfr_all : ∀ a, a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
      (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a := by
    intro a h1 h2 ha
    dsimp only [stEnd, mEnd]
    rw [Function.update_of_ne (by omega)]
    by_cases hseen : bsSeenBase p bunCap ≤ a ∧ a < bsSeenBase p bunCap + bunCap
    · set b := a - bsSeenBase p bunCap
      have hb_lt : b < bunCap := by omega
      have ha_eq : a = bsSeenBase p bunCap + b := by omega
      rw [ha_eq, hseen0 b hb_lt]
      by_cases hbc : b ∈ cands
      · exact hseenZ2 b hb_lt (by rwa [List.take_length])
      · rw [hseenK2 b hb_lt (by rwa [List.take_length])]
        have hbk := hbkP1 b hb_lt
        have hnil : scan_j.filter (fun t => t.1 == b) = [] := by
          rw [List.filter_eq_nil_iff]
          intro t ht; simp [show t.1 ≠ b from fun heq => hbc (heq ▸ hscan_in_cands t ht)]
        simpa [hnil, BucketListAt] using hbk
    · have hout_seen : a < bsSeenBase p bunCap ∨ bsSeenBase p bunCap + bunCap ≤ a := by omega
      rw [hfr2_end a hout_seen (by omega) (by rw [hpref_full]; omega),
        hfrP1 a hout_seen (by omega)]
      exact hm2_eq a h1 h2
  have hfull := bundle_runs_seq_normal ha25a (bundle_runs_seq_normal ha26a (bundle_runs_seq_normal ha27a
    (bundle_runs_seq_normal ha25b (bundle_runs_seq_normal ha23a (bundle_runs_seq_normal hs_cb
      (bundle_runs_seq_normal hs_ct (bundle_runs_seq_normal ha26b (bundle_runs_seq_normal hrunP1
        (bundle_runs_seq_normal ha13 (bundle_runs_seq_normal ha14 (bundle_runs_seq_normal ha4e
          (bundle_runs_seq_normal ha27_0 (bundle_runs_seq_normal hrunP2 hs_last)))))))))))))
  refine ⟨stEnd, _, hfull, fun r hr h4 h13 h14 => by
      dsimp only [stEnd]; rw [hregs2 r (by omega)]
      simp [stA, r27_0, r4e, r14, r13, h4, h13, h14, hregsP1 r (by omega) h4,
        stH, r26b, r23a, r25b, r27a, r26a, r25a, show r ≠ 26 by omega, show r ≠ 23 by omega,
        show r ≠ 25 by omega, show r ≠ 27 by omega],
    by dsimp only [stEnd]; rw [hregs2 4 (by decide)]; simp [stA, r27_0, r4e],
    by dsimp only [stEnd]; rw [hregs2 13 (by decide)]; simp [stA, r27_0, r4e, r14, r13],
    by dsimp only [stEnd]; rw [hregs2 14 (by decide)]; simp [stA, r27_0, r4e, r14],
    by dsimp only [stEnd]; rw [hregs2 23 (by decide)]
       simp [stA, r27_0, r4e, r14, r13, hregsP1 23 (by decide) (by decide), stH, r26b, r23a],
    by dsimp only [stEnd, mEnd]
       have hcb_out : btCurBunBase tbl slotCap eCap + s < bsSeenBase p bunCap ∨
           bsSeenBase p bunCap + bunCap ≤ btCurBunBase tbl slotCap eCap + s := by
         unfold bsSeenBase btCurBunBase; unfold bundleTableFixedSize bundleSlotBlockSize at hp_disj_tbl; omega
       rw [Function.update_of_ne (by omega), hfr2_end _ hcb_out (Or.inl (by omega)) (Or.inl (by omega)),
         hfrP1 _ hcb_out (Or.inl (by omega))]
       dsimp only [stH, m2, m1]; rw [Function.update_of_ne hcb_ne_ct, Function.update_self],
    by dsimp only [stEnd, mEnd]
       have hct_out : btCurTagBase tbl slotCap eCap + s < bsSeenBase p bunCap ∨
           bsSeenBase p bunCap + bunCap ≤ btCurTagBase tbl slotCap eCap + s := by
         unfold bsSeenBase btCurTagBase; unfold bundleTableFixedSize bundleSlotBlockSize at hp_disj_tbl; omega
       rw [Function.update_of_ne (by omega), hfr2_end _ hct_out (Or.inl (by omega)) (Or.inl (by omega)),
         hfrP1 _ hct_out (Or.inl (by omega))]
       simp [stH, m2],
    ⟨fun i hi => by
       dsimp only [stEnd, mEnd]
       by_cases hlt : i < cands.length
       · rw [Function.update_of_ne (by omega)]; exact hoffs2 i hlt
       · have heq : i = cands.length := by omega
         subst heq; simp only [Function.update_self, List.take_length]
         exact (sum_filter_lengths_eq hcands_nd hscan_in_cands).symm,
     fun i hi => by
       refine ⟨((scan_j.filter fun t => t.1 == cands[i]).reverse).map fun t => packEndKey eCap t.2.1 t.2.2,
         (List.reverse_perm _).map _, ?_⟩
       have hoff_i : stEnd.mem (offPtr + i) = prefLen i := by
         dsimp only [stEnd, mEnd]; rw [Function.update_of_ne (by omega)]; exact hoffs2 i hi
       rw [hoff_i]
       intro idx hidx
       dsimp only [stEnd, mEnd]
       rw [Function.update_of_ne (by omega)]
       exact hbufs2 i hi hi idx hidx⟩,
    fun a ha => (hfr_all a (by omega) (by omega) (Or.inr ha)).trans (hzero a (by omega)),
    hfr_all, by omega⟩

end

end MinCostFlow.SparseCore.Program
