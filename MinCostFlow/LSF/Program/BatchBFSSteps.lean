module

public import MinCostFlow.LSF.Program.BatchBFSBase
import Mathlib.Tactic.Linarith

/-!
# Lock-Step Dual-BFS Relabeling, Cleanup, Lock-Step, and Setup Triples (`BatchBFSSteps`)

Proves `relabelComp_triple`, `clearVis_triple`, `finishSide_triple`, `bfsLockStep_triple`, and
`bfsSetup_triple` for `splitCompBFSProc`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Relabel loop triple: sets `compId[q[i]] := root2` for `i < q.length`, leaving all other memory
unchanged, in cost `≤ 25 * q.length + 10`. -/
lemma relabelComp_triple {w compIdBase qBuf root2 vCap : ℕ} {rQBuf rQTail : ℕ}
    {p : Program} {mem0 regs_in : ℕ → ℕ} {q : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hr_dist : [10, 29, 32, rQBuf, rQTail].Nodup)
    (hcid_ltw : compIdBase + vCap < 2 ^ w)
    (hqBuf_ltw : qBuf + vCap < 2 ^ w)
    (hdisj : compIdBase + vCap ≤ qBuf ∨ qBuf + vCap ≤ compIdBase)
    (hq_len : q.length ≤ vCap)
    (hq_lt : ∀ v ∈ q, v < vCap)
    (_hroot2_ltw : root2 < 2 ^ w)
    (hLA : ListAt mem0 qBuf q) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs = regs_in ∧ st.regs 10 = root2 ∧ st.regs 29 = compIdBase ∧
        st.regs rQBuf = qBuf ∧ st.regs rQTail = q.length)
      (relabelCompStmt rQBuf rQTail)
      (normalPost fun st' =>
        (∀ a, ¬ (compIdBase ≤ a ∧ a < compIdBase + vCap) → st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (compIdBase + v) =
          if v ∈ q then root2 else mem0 (compIdBase + v)) ∧
        (∀ r, r ≠ 32 → st'.regs r = regs_in r))
      (fun _ => 25 * q.length + 10) := by
  classical
  have hne : ∀ i j (hi : i < 5) (hj : j < 5), i ≠ j →
      ([10, 29, 32, rQBuf, rQTail][i]'(by simpa using hi)) ≠
      ([10, 29, 32, rQBuf, rQTail][j]'(by simpa using hj)) := fun i j hi hj hij h =>
    hij ((hr_dist.getElem_inj_iff).mp h)
  have h10_32 : (10 : ℕ) ≠ 32 := by decide
  have h29_32 : (29 : ℕ) ≠ 32 := by decide
  have hrQB_32 : rQBuf ≠ 32 := hne 3 2 (by decide) (by decide) (by decide)
  have hrQT_32 : rQTail ≠ 32 := hne 4 2 (by decide) (by decide) (by decide)
  intro st ω ⟨hmem, hregs_in, h10, h29, hQB, hQT⟩
  let Inv : ℕ → State → Prop := fun k s =>
    (∀ a, ¬ (compIdBase ≤ a ∧ a < compIdBase + vCap) → s.mem a = mem0 a) ∧
    (∀ v < vCap, s.mem (compIdBase + v) = if v ∈ q.take k then root2 else mem0 (compIdBase + v)) ∧
    s.regs 32 = k ∧
    (∀ r, r ≠ 32 → s.regs r = regs_in r)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 32)
    (lo := .const 0) (hi := .reg rQTail)
    (body := .store (.bin .add (.reg 29) (.load (.bin .add (.reg rQBuf) (.reg 32)))) (.reg 10))
    (P := fun s => s = st) (Inv := Inv) 16 0 q.length (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by eval_expr, fun a _ => congrFun hmem a, fun v _ => by simp [hmem], by simp,
        fun r hr => by simp [hr, hregs_in]⟩)
    (fun _ s _ _ hi => hi.2.2.1)
    (fun _ s _ _ hi => by have := (hi.2.2.2 rQTail hrQT_32).trans (hregs_in ▸ hQT); eval_expr)
    (fun j _ hj s ω' ⟨hfr, hcid, h32, hreg⟩ => by
      have hj_v : q[j]'hj < vCap := hq_lt _ (List.getElem_mem hj)
      have h10' : s.regs 10 = root2 := (hreg 10 h10_32).trans (hregs_in ▸ h10)
      have h29' : s.regs 29 = compIdBase := (hreg 29 h29_32).trans (hregs_in ▸ h29)
      have hQB' : s.regs rQBuf = qBuf := (hreg rQBuf hrQB_32).trans (hregs_in ▸ hQB)
      have hqj_mem : s.mem (qBuf + j) = q[j]'hj := by
        rw [hfr _ (by rcases hdisj with h | h <;> omega)]
        exact hLA j hj
      have haddr : (Expr.bin .add (.reg 29) (.load (.bin .add (.reg rQBuf) (.reg 32)))).eval w s =
          some (compIdBase + q[j]'hj) := by
        have h1 : (Expr.reg 29).eval w s = some compIdBase := by eval_expr
        have h2 : (Expr.load (.bin .add (.reg rQBuf) (.reg 32))).eval w s = some (q[j]'hj) :=
          Expr.eval_load_of_eq (by eval_expr) hqj_mem
        exact Expr.eval_bin h1 h2 (by dsimp [BinOp.eval]; omega)
      have hval : (Expr.reg 10).eval w s = some root2 := by eval_expr
      refine runs_start_le (runs_store_le haddr hval ?_ (by dsimp [Expr.size]; omega))
      dsimp only [Inv]
      refine ⟨⟨fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha,
        fun v hv => ?_, by simp, fun r hr => by dsimp only; rw [Function.update_of_ne hr]; exact hreg r hr⟩,
        h32⟩
      dsimp only
      rw [List.take_succ_eq_append_getElem hj]
      by_cases hvq : v = q[j]'hj
      · subst hvq; rw [Function.update_self]
        simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
      · rw [Function.update_of_ne (by omega), hcid v hv]
        simp only [List.mem_append, List.mem_singleton, hvq, or_false])
  obtain ⟨o, st', c, hr, hq, hc⟩ := hloop st ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    refine ⟨.normal, st', c, hr, ?_, ?_⟩
    · rcases hq with ⟨hfr, hcid, _, hreg⟩
      refine ⟨hfr, fun v hv => by simpa [List.take_of_length_le le_rfl] using hcid v hv, hreg⟩
    · dsimp only [Expr.size] at hc ⊢; omega

/-- Clear-visited loop triple: sets `vis[q[i]] := 0` for `i < q.length`, restoring `vis` to all
zero (given `SideMemAt` and `q.Nodup`), leaving all other memory unchanged, in cost
`≤ 25 * q.length + 10`. -/
lemma clearVis_triple {w qBuf vis vCap : ℕ} {rQBuf rVis rQTail : ℕ}
    {p : Program} {mem0 regs_in : ℕ → ℕ} {q : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hr_dist : [32, rQBuf, rVis, rQTail].Nodup)
    (hqBuf_ltw : qBuf + vCap < 2 ^ w)
    (hvis_ltw : vis + vCap < 2 ^ w)
    (hdisj : qBuf + vCap ≤ vis ∨ vis + vCap ≤ qBuf)
    (hq_nd : q.Nodup)
    (hq_len : q.length ≤ vCap)
    (hq_lt : ∀ v ∈ q, v < vCap)
    (hSide : SideMemAt mem0 qBuf vis vCap q) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs = regs_in ∧ st.regs rQBuf = qBuf ∧ st.regs rVis = vis ∧
        st.regs rQTail = q.length)
      (clearVisStmt rQBuf rVis rQTail)
      (normalPost fun st' =>
        (∀ a, ¬ (vis ≤ a ∧ a < vis + vCap) → st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (vis + v) = 0) ∧
        (∀ r, r ≠ 32 → st'.regs r = regs_in r))
      (fun _ => 25 * q.length + 10) := by
  classical
  have hne : ∀ i j (hi : i < 4) (hj : j < 4), i ≠ j →
      ([32, rQBuf, rVis, rQTail][i]'(by simpa using hi)) ≠
      ([32, rQBuf, rVis, rQTail][j]'(by simpa using hj)) := fun i j hi hj hij h =>
    hij ((hr_dist.getElem_inj_iff).mp h)
  have hrQB_32 : rQBuf ≠ 32 := hne 1 0 (by decide) (by decide) (by decide)
  have hrV_32 : rVis ≠ 32 := hne 2 0 (by decide) (by decide) (by decide)
  have hrQT_32 : rQTail ≠ 32 := hne 3 0 (by decide) (by decide) (by decide)
  intro st ω ⟨hmem, hregs_in, hQB, hV, hQT⟩
  let Inv : ℕ → State → Prop := fun k s =>
    (∀ a, ¬ (vis ≤ a ∧ a < vis + vCap) → s.mem a = mem0 a) ∧
    (∀ v < vCap, s.mem (vis + v) = if v ∈ q.drop k then 1 else 0) ∧
    s.regs 32 = k ∧
    (∀ r, r ≠ 32 → s.regs r = regs_in r)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 32)
    (lo := .const 0) (hi := .reg rQTail)
    (body := .store (.bin .add (.reg rVis) (.load (.bin .add (.reg rQBuf) (.reg 32)))) (.const 0))
    (P := fun s => s = st) (Inv := Inv) 16 0 q.length (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by eval_expr, fun a _ => congrFun hmem a,
        fun v hv => by simpa [hmem] using hSide.2 v hv, by simp,
        fun r hr => by simp [hr, hregs_in]⟩)
    (fun _ s _ _ hi => hi.2.2.1)
    (fun _ s _ _ hi => by have := (hi.2.2.2 rQTail hrQT_32).trans (hregs_in ▸ hQT); eval_expr)
    (fun j _ hj s ω' ⟨hfr, hvis, h32, hreg⟩ => by
      have hj_v : q[j]'hj < vCap := hq_lt _ (List.getElem_mem hj)
      have hQB' : s.regs rQBuf = qBuf := (hreg rQBuf hrQB_32).trans (hregs_in ▸ hQB)
      have hV' : s.regs rVis = vis := (hreg rVis hrV_32).trans (hregs_in ▸ hV)
      have hqj_mem : s.mem (qBuf + j) = q[j]'hj := by
        rw [hfr _ (by rcases hdisj with h | h <;> omega)]
        exact hSide.1 j hj
      have haddr : (Expr.bin .add (.reg rVis) (.load (.bin .add (.reg rQBuf) (.reg 32)))).eval w s =
          some (vis + q[j]'hj) := by
        have h1 : (Expr.reg rVis).eval w s = some vis := by eval_expr
        have h2 : (Expr.load (.bin .add (.reg rQBuf) (.reg 32))).eval w s = some (q[j]'hj) :=
          Expr.eval_load_of_eq (by eval_expr) hqj_mem
        exact Expr.eval_bin h1 h2 (by dsimp [BinOp.eval]; omega)
      have hval : (Expr.const 0).eval w s = some 0 := by eval_expr
      refine runs_start_le (runs_store_le haddr hval ?_ (by dsimp [Expr.size]; omega))
      dsimp only [Inv]
      have hnot_in_tail : q[j]'hj ∉ q.drop (j + 1) := by
        have hnd_drop : (q.drop j).Nodup := hq_nd.sublist (List.drop_sublist _ _)
        rw [List.drop_eq_getElem_cons hj, List.nodup_cons] at hnd_drop
        exact hnd_drop.1
      refine ⟨⟨fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha,
        fun v hv => ?_, by simp, fun r hr => by dsimp only; rw [Function.update_of_ne hr]; exact hreg r hr⟩,
        h32⟩
      dsimp only
      by_cases hvq : v = q[j]'hj
      · subst hvq; simp [hnot_in_tail]
      · rw [Function.update_of_ne (by omega), hvis v hv, List.drop_eq_getElem_cons hj]
        simp only [List.mem_cons, hvq, false_or])
  obtain ⟨o, st', c, hr, hq, hc⟩ := hloop st ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    refine ⟨.normal, st', c, hr, ?_, ?_⟩
    · rcases hq with ⟨hfr, hvis, _, hreg⟩
      refine ⟨hfr, fun v hv => by simpa [List.drop_eq_nil_of_le le_rfl] using hvis v hv, hreg⟩
    · dsimp only [Expr.size] at hc ⊢; omega

/-- Triple for `finishSideStmt`: relabels `compId[v] := root2` for `v ∈ q`, sets
`compSize[root2] := q.length` and `compSize[oldCid] := newSum - q.length`, and assigns
`compRoot[root2]` / `compRoot[oldCid]` according to whether `root2 ∈ q`, in cost
`≤ 25 * q.length + 60`. -/
lemma finishSide_triple {w fAncPtr qBuf vis vCap oldCid root1 root2 newSum : ℕ}
    {rQBuf rVis rQTail : ℕ} {p : Program} {mem0 regs_in : ℕ → ℕ} {q : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hr_dist : [8, 9, 10, 11, 29, 30, 31, 32, rQBuf, rVis, rQTail].Nodup)
    (hcid_lt_cr : fCompIdBase fAncPtr vCap + vCap = fCompRootBase fAncPtr vCap)
    (hcr_lt_cs : fCompRootBase fAncPtr vCap + vCap = fCompSizeBase fAncPtr vCap)
    (hf_le_q : fCompSizeBase fAncPtr vCap + vCap ≤ qBuf)
    (hq_le_v : qBuf + vCap ≤ vis)
    (hv_ltw : vis + vCap < 2 ^ w)
    (hold_lt : oldCid < vCap) (hr1_lt : root1 < vCap) (hr2_lt : root2 < vCap)
    (hold_ne_r2 : oldCid ≠ root2)
    (hq_len : q.length ≤ vCap) (_hq_le_sum : q.length ≤ newSum) (hsum_ltw : newSum < 2 ^ w)
    (hq_lt : ∀ v ∈ q, v < vCap)
    (hSide : SideMemAt mem0 qBuf vis vCap q) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs = regs_in ∧
        st.regs 8 = oldCid ∧ st.regs 9 = root1 ∧ st.regs 10 = root2 ∧ st.regs 11 = newSum ∧
        st.regs 29 = fCompIdBase fAncPtr vCap ∧ st.regs 30 = fCompRootBase fAncPtr vCap ∧
        st.regs 31 = fCompSizeBase fAncPtr vCap ∧
        st.regs rQBuf = qBuf ∧ st.regs rVis = vis ∧ st.regs rQTail = q.length)
      (finishSideStmt rQBuf rVis rQTail)
      (normalPost fun st' =>
        (∀ a, ¬ (fCompIdBase fAncPtr vCap ≤ a ∧ a < fCompSizeBase fAncPtr vCap + vCap) →
          st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (fCompIdBase fAncPtr vCap + v) =
          if v ∈ q then root2 else mem0 (fCompIdBase fAncPtr vCap + v)) ∧
        (∀ c < vCap, c ≠ oldCid → c ≠ root2 →
          st'.mem (fCompRootBase fAncPtr vCap + c) = mem0 (fCompRootBase fAncPtr vCap + c) ∧
          st'.mem (fCompSizeBase fAncPtr vCap + c) = mem0 (fCompSizeBase fAncPtr vCap + c)) ∧
        st'.mem (fCompSizeBase fAncPtr vCap + root2) = q.length ∧
        st'.mem (fCompSizeBase fAncPtr vCap + oldCid) = newSum - q.length ∧
        ((root2 ∈ q ∧ st'.mem (fCompRootBase fAncPtr vCap + root2) = root2 ∧
            st'.mem (fCompRootBase fAncPtr vCap + oldCid) = root1) ∨
         (root2 ∉ q ∧ st'.mem (fCompRootBase fAncPtr vCap + root2) = root1 ∧
            st'.mem (fCompRootBase fAncPtr vCap + oldCid) = root2)) ∧
        (∀ r, r ≠ 32 → st'.regs r = regs_in r))
      (fun _ => 25 * q.length + 60) := by
  classical
  set compIdBase := fCompIdBase fAncPtr vCap
  set compRootBase := fCompRootBase fAncPtr vCap
  set compSizeBase := fCompSizeBase fAncPtr vCap
  have hne : ∀ i j (hi : i < 11) (hj : j < 11), i ≠ j →
      ([8, 9, 10, 11, 29, 30, 31, 32, rQBuf, rVis, rQTail][i]'(by simpa using hi)) ≠
      ([8, 9, 10, 11, 29, 30, 31, 32, rQBuf, rVis, rQTail][j]'(by simpa using hj)) :=
    fun i j hi hj hij h => hij ((hr_dist.getElem_inj_iff).mp h)
  have hrel_nd : [10, 29, 32, rQBuf, rQTail].Nodup :=
    hr_dist.sublist (.cons _ (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons _ (.cons _
      (.cons_cons _ (.cons_cons _ (.cons _ (.cons_cons _ .slnil)))))))))))
  intro st ω ⟨hm0, hr0, h8, h9, h10, h11, h29, h30, h31, hQB, hV, hQT⟩
  suffices h : ∃ o st' c, Runs w p ω (finishSideStmt rQBuf rVis rQTail) st o st' c ∧
      normalPost (fun st' =>
        (∀ a, ¬ (compIdBase ≤ a ∧ a < compSizeBase + vCap) → st'.mem a = mem0 a) ∧
        (∀ v < vCap, st'.mem (compIdBase + v) =
          if v ∈ q then root2 else mem0 (compIdBase + v)) ∧
        (∀ c < vCap, c ≠ oldCid → c ≠ root2 →
          st'.mem (compRootBase + c) = mem0 (compRootBase + c) ∧
          st'.mem (compSizeBase + c) = mem0 (compSizeBase + c)) ∧
        st'.mem (compSizeBase + root2) = q.length ∧
        st'.mem (compSizeBase + oldCid) = newSum - q.length ∧
        ((root2 ∈ q ∧ st'.mem (compRootBase + root2) = root2 ∧
            st'.mem (compRootBase + oldCid) = root1) ∨
         (root2 ∉ q ∧ st'.mem (compRootBase + root2) = root1 ∧
            st'.mem (compRootBase + oldCid) = root2)) ∧
        (∀ r, r ≠ 32 → st'.regs r = regs_in r)) o st' ∧
      0 + c ≤ 25 * q.length + 60 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  dsimp only [finishSideStmt]
  have hrel := relabelComp_triple (w := w) (p := p) (compIdBase := compIdBase)
    (qBuf := qBuf) (root2 := root2) (vCap := vCap) (rQBuf := rQBuf) (rQTail := rQTail)
    (mem0 := mem0) (regs_in := regs_in) (q := q)
    hw16 hrel_nd (by omega) (by omega) (Or.inl (by omega)) hq_len hq_lt (by omega) hSide.1
  refine runs_seq_triple_le hrel ⟨hm0, hr0, h10, h29, hQB, hQT⟩ ?_
  rintro st₁ ⟨hfr1, hcid1, hreg1⟩
  have h8_1 : st₁.regs 8 = oldCid := (hreg1 8 (by decide)).trans (hr0 ▸ h8)
  have h9_1 : st₁.regs 9 = root1 := (hreg1 9 (by decide)).trans (hr0 ▸ h9)
  have h10_1 : st₁.regs 10 = root2 := (hreg1 10 (by decide)).trans (hr0 ▸ h10)
  have h11_1 : st₁.regs 11 = newSum := (hreg1 11 (by decide)).trans (hr0 ▸ h11)
  have h30_1 : st₁.regs 30 = compRootBase := (hreg1 30 (by decide)).trans (hr0 ▸ h30)
  have h31_1 : st₁.regs 31 = compSizeBase := (hreg1 31 (by decide)).trans (hr0 ▸ h31)
  have hV_1 : st₁.regs rVis = vis := (hreg1 rVis (hne 9 7 (by decide) (by decide) (by decide))).trans (hr0 ▸ hV)
  have hQT_1 : st₁.regs rQTail = q.length := (hreg1 rQTail (hne 10 7 (by decide) (by decide) (by decide))).trans (hr0 ▸ hQT)
  refine runs_seq_store_le (x := compSizeBase + root2) (v := q.length) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := compSizeBase + oldCid) (v := newSum - q.length) (by eval_expr) (by eval_expr) ?_; dsimp only
  have hvis_r2 : Function.update (Function.update st₁.mem (compSizeBase + root2) q.length)
      (compSizeBase + oldCid) (newSum - q.length) (vis + root2) = if root2 ∈ q then 1 else 0 := by
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 _ (by omega)]
    exact hSide.2 root2 hr2_lt
  refine WordRAM.runs_cond_le (Expr.eval_load_of_eq (v := if root2 ∈ q then 1 else 0)
    (by eval_expr) hvis_r2) ?_ ?_
  · intro hr2_ne
    have hr2_in : root2 ∈ q := by by_contra hc; simp only [hc, ↓reduceIte] at hr2_ne; exact hr2_ne rfl
    refine runs_seq_store_le (x := compRootBase + root2) (v := root2) (by eval_expr) (by eval_expr) ?_; dsimp only
    refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
    dsimp only
    refine ⟨fun a ha => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 a (by omega)],
      fun v hv => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcid1 v hv],
      fun c hc hne1 hne2 =>
        ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 _ (by omega)],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 _ (by omega)]⟩,
      by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self],
      by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self],
      Or.inl ⟨hr2_in,
        by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
        by dsimp only; rw [Function.update_self]⟩,
      hreg1⟩
  · intro hr2_0
    have hr2_out : root2 ∉ q := fun hc => by simp only [hc, ↓reduceIte] at hr2_0; exact Nat.one_ne_zero hr2_0
    refine runs_seq_store_le (x := compRootBase + root2) (v := root1) (by eval_expr) (by eval_expr) ?_; dsimp only
    refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
    dsimp only
    refine ⟨fun a ha => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 a (by omega)],
      fun v hv => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcid1 v hv],
      fun c hc hne1 hne2 =>
        ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 _ (by omega)],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 _ (by omega)]⟩,
      by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self],
      by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self],
      Or.inr ⟨hr2_out,
        by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
        by dsimp only; rw [Function.update_self]⟩,
      hreg1⟩

/-- Lock-step dual-BFS loop triple: advances sides A and B in lock-step until either finishes,
running in at most `152 * (3 * min |E_{C_A}| |E_{C_B}| + 2) + 2` steps. -/
lemma bfsLockStep_triple {w dgFPtr vCap eCapF qBufA qBufB visA visB uA uB : ℕ}
    {p : Program} {mem0 regs_in : ℕ → ℕ} {F : MGraph} {incL : ℕ → List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hdg_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w)
    (hdg_le_qA : dgFPtr + dynGraphSize vCap eCapF ≤ qBufA)
    (hqA_qB : qBufA + vCap = qBufB) (hqB_vA : qBufB + vCap = visA) (hvA_vB : visA + vCap = visB)
    (hvB_ltw : visB + vCap < 2 ^ w)
    (hF : F.IsForest) (huA : uA ∈ F.V) (huB : uB ∈ F.V)
    (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V,
      mem0 (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem0 (dgIntToExtBase dgFPtr vCap + mem0 (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hIntToExt : ∀ s ∈ F.V,
      mem0 (dgIntToExtBase dgFPtr vCap + s) ∈ F.V ∧
      mem0 (dgExtToIntBase dgFPtr vCap + mem0 (dgIntToExtBase dgFPtr vCap + s)) = s)
    (hEndSlot : ∀ e ∈ F.E,
      mem0 (dgETailSlotBase dgFPtr vCap eCapF + e) = mem0 (dgExtToIntBase dgFPtr vCap + F.tail e) ∧
      mem0 (dgEHeadSlotBase dgFPtr vCap eCapF + e) = mem0 (dgExtToIntBase dgFPtr vCap + F.head e))
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem0 (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem0 (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem0 (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem0 (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s) :
    open Classical in
    Triple w p
      (fun st =>
        st.regs = regs_in ∧
        (∀ a, ¬ (qBufA ≤ a ∧ a < visB + vCap) → st.mem a = mem0 a) ∧
        regs_in 12 = dgExtToIntBase dgFPtr vCap ∧ regs_in 13 = dgIntToExtBase dgFPtr vCap ∧
        regs_in 14 = dgIncHeadBase dgFPtr vCap ∧ regs_in 15 = dgETailSlotBase dgFPtr vCap eCapF ∧
        regs_in 16 = dgEHeadSlotBase dgFPtr vCap eCapF ∧ regs_in 17 = dgHeNextBase dgFPtr vCap eCapF ∧
        regs_in 18 = qBufA ∧ regs_in 19 = qBufB ∧ regs_in 20 = visA ∧ regs_in 21 = visB ∧
        st.regs 28 = 1 ∧
        SideMemAt st.mem qBufA visA vCap [uA] ∧ SideMemAt st.mem qBufB visB vCap [uB] ∧
        st.regs 22 = 0 ∧ st.regs 23 = 1 ∧ st.regs 24 = 0 ∧
        st.regs 25 = 0 ∧ st.regs 26 = 1 ∧ st.regs 27 = 0)
      (.loop (.reg 28) bfsLockStepBody)
      (normalPost fun st =>
        (∀ a, ¬ (qBufA ≤ a ∧ a < visB + vCap) → st.mem a = mem0 a) ∧
        (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
          r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st.regs r = regs_in r) ∧
        ∃ k qA qHA remA qB qHB remB,
          BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL uA qA qHA remA k ∧
          BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL uB qB qHB remB k ∧
          SideMemAt st.mem qBufA visA vCap qA ∧
          SideMemAt st.mem qBufB visB vCap qB ∧
          DllTailAt st.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remA (st.regs 24) ∧
          DllTailAt st.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remB (st.regs 27) ∧
          st.regs 22 = qHA ∧ st.regs 23 = qA.length ∧
          st.regs 25 = qHB ∧ st.regs 26 = qB.length ∧
          ((qHA = qA.length ∧ remA = []) ∨ (qHB = qB.length ∧ remB = [])))
      (fun _ => 152 * (3 * min (F.E.filter fun e => F.Connected (F.tail e) uA).card
                               (F.E.filter fun e => F.Connected (F.tail e) uB).card + 2) + 2) := by
  classical
  intro st_init ω_init ⟨hreg0_eq, hfr0, hr12_0, hr13_0, hr14_0, hr15_0, hr16_0, hr17_0,
    hr18_0, hr19_0, hr20_0, hr21_0, h28_0, hSA0, hSB0, h22_0, h23_0, h24_0, h25_0, h26_0, h27_0⟩
  have hreg0 : ∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
      r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st_init.regs r = regs_in r :=
    fun r _ _ _ _ _ _ _ _ _ _ _ => congrFun hreg0_eq r
  set extToInt := dgExtToIntBase dgFPtr vCap
  set intToExt := dgIntToExtBase dgFPtr vCap
  set incHead := dgIncHeadBase dgFPtr vCap
  set eTailSlot := dgETailSlotBase dgFPtr vCap eCapF
  set eHeadSlot := dgEHeadSlotBase dgFPtr vCap eCapF
  set heNext := dgHeNextBase dgFPtr vCap eCapF
  set EA := F.E.filter fun e => F.Connected (F.tail e) uA
  set EB := F.E.filter fun e => F.Connected (F.tail e) uB
  set mSmall := min EA.card EB.card
  have h2e_v_ltw : 2 * eCapF + vCap < 2 ^ w := by dsimp [dynGraphSize] at hdg_ltw; omega
  have hHeNext_le : heNext + 2 * eCapF ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [heNext, dgHeNextBase, dynGraphSize]; omega
  let LoopInv : ℕ × Bool → State → Prop := fun ⟨k, running⟩ st =>
    (∀ a, ¬ (qBufA ≤ a ∧ a < visB + vCap) → st.mem a = mem0 a) ∧
    (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
      r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st.regs r = regs_in r) ∧
    st.regs 28 = (if running then 1 else 0) ∧
    ∃ qA qHA remA qB qHB remB,
      BfsInv F (fun v => mem0 (extToInt + v)) incL uA qA qHA remA k ∧
      BfsInv F (fun v => mem0 (extToInt + v)) incL uB qB qHB remB k ∧
      SideMemAt st.mem qBufA visA vCap qA ∧
      SideMemAt st.mem qBufB visB vCap qB ∧
      DllTailAt st.mem heNext (2 * eCapF) remA (st.regs 24) ∧
      DllTailAt st.mem heNext (2 * eCapF) remB (st.regs 27) ∧
      st.regs 22 = qHA ∧ st.regs 23 = qA.length ∧
      st.regs 25 = qHB ∧ st.regs 26 = qB.length ∧
      (running = false → (qHA = qA.length ∧ remA = []) ∨ (qHB = qB.length ∧ remB = []))
  let mMeas : ℕ × Bool → ℕ := fun ⟨k, running⟩ => if running then (3 * mSmall + 2) - k else 0
  let remCost : ℕ × Bool → ℕ := fun a => 152 * mMeas a + 2
  have hloop : Triple w p (LoopInv (0, true)) (.loop (.reg 28) bfsLockStepBody)
      (normalPost fun st => ∃ k, LoopInv (k, false) st)
      (fun _ => remCost (0, true)) := by
    refine Triple.loop_inv (m := mMeas) (rem := remCost) (condVal := fun st => st.regs 28)
      (Inv := LoopInv)
      (fun ⟨_, r⟩ st hI => Expr.eval_reg_of_eq rfl)
      (fun ⟨k, r⟩ st hI h0 => by
        have h28 : st.regs 28 = if r then 1 else 0 := hI.2.2.1
        have hr_false : r = false := by cases r <;> simp_all
        subst hr_false
        simp only [normalPost, Expr.size, remCost, mMeas, Bool.false_eq_true, ↓reduceIte]
        exact ⟨⟨k, hI⟩, by omega⟩)
      (fun ⟨k, r⟩ st hI hne => by
        have h28 : st.regs 28 = if r then 1 else 0 := hI.2.2.1
        have hr_true : r = true := by cases r <;> simp_all
        subst hr_true
        rcases hI with ⟨hfr, hreg, _, qA, qHA, remA, qB, qHB, remB,
          hBA, hBB, hSA, hSB, hDA, hDB, hr22, hr23, hr25, hr26, _⟩
        have hkA : k ≤ 3 * EA.card + 1 := hBA.steps_le hF huA hvCap heCap hExtToInt hincL
        have hkB : k ≤ 3 * EB.card + 1 := hBB.steps_le hF huB hvCap heCap hExtToInt hincL
        have hk_le : k ≤ 3 * mSmall + 1 := by dsimp only [mSmall]; omega
        have hqA_le : qA.length ≤ vCap :=
          list_len_le_vCap hvCap hBA.hq_nd (fun v hv => (hBA.hq_sub v hv).1)
        have hqB_le : qB.length ≤ vCap :=
          list_len_le_vCap hvCap hBB.hq_nd (fun v hv => (hBB.hq_sub v hv).1)
        have hchA_le : st.regs 24 ≤ 2 * eCapF := by
          cases remA with
          | nil => rw [hDA]; omega
          | cons a tl => obtain ⟨h1, h2, _⟩ := hDA; omega
        have hchB_le : st.regs 27 ≤ 2 * eCapF := by
          cases remB with
          | nil => rw [hDB]; omega
          | cons a tl => obtain ⟨h1, h2, _⟩ := hDB; omega
        refine ⟨150, ?_⟩
        intro s ω' hs
        subst s
        suffices h : ∃ o st' c, Runs w p ω' bfsLockStepBody st o st' c ∧
            normalPost (fun st' => ∃ a', LoopInv a' st' ∧ mMeas a' < mMeas (k, true) ∧
              (Expr.reg 28).size + 150 + remCost a' + 1 ≤ remCost (k, true)) o st' ∧ 0 + c ≤ 150 by
          rcases h with ⟨o, st', c, hr, hq, hc⟩
          refine ⟨o, st', c, hr, ?_, by simpa using hc⟩
          cases o with
          | returned _ => exact False.elim hq
          | normal => exact hq
        dsimp only [bfsLockStepBody]
        have hcondA_eval : (Expr.bin .add (.reg 24) (.bin .sub (.reg 23) (.reg 22))).eval w st =
            some (st.regs 24 + (qA.length - qHA)) := by
          have := hBA.hqh_le; eval_expr
        refine WordRAM.runs_cond_le hcondA_eval ?_ ?_
        · -- Side A is not done
          intro hA_ne
          have hcondB_eval : (Expr.bin .add (.reg 27) (.bin .sub (.reg 26) (.reg 25))).eval w st =
              some (st.regs 27 + (qB.length - qHB)) := by
            have := hBB.hqh_le; eval_expr
          refine WordRAM.runs_cond_le hcondB_eval ?_ ?_
          · -- Side B is not done either: run `bfsMicroStep` on A then on B
            intro hB_ne
            have hnotA : remA ≠ [] ∨ qHA < qA.length := by
              by_cases h1 : remA = []
              · subst h1; right; have := hBA.hqh_le; rw [hDA] at hA_ne; omega
              · exact Or.inl h1
            have hnotB : remB ≠ [] ∨ qHB < qB.length := by
              by_cases h1 : remB = []
              · subst h1; right; have := hBB.hqh_le; rw [hDB] at hB_ne; omega
              · exact Or.inl h1
            have hdgAg0 : ∀ a, a < dgFPtr + dynGraphSize vCap eCapF → st.mem a = mem0 a :=
              fun a ha => hfr a (by omega)
            have hget : ∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
                r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st.regs r = regs_in r := hreg
            have hmicroA := bfsMicroStep_triple (w := w) (p := p) (dgFPtr := dgFPtr) (vCap := vCap)
              (eCapF := eCapF) (qBuf := qBufA) (vis := visA) (u₀ := uA) (qHead := qHA) (steps := k)
              (rQBuf := 18) (rVis := 20) (rQHead := 22) (rQTail := 23) (rCurHe := 24)
              (mem0 := mem0) (mem_in := st.mem) (regs_in := st.regs) (q := qA) (remHe := remA)
              hw16 (by decide) hdg_ltw (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
              hF.1 hvCap heCap hExtToInt hIntToExt hEndSlot hincL hBA hnotA
            refine runs_seq_triple_le hmicroA
              ⟨rfl, rfl, hdgAg0, hSA, hDA,
               (hget 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr12_0,
               (hget 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr13_0,
               (hget 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr14_0,
               (hget 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr15_0,
               (hget 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr16_0,
               (hget 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr17_0,
               (hget 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr18_0,
               (hget 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr20_0,
               hr22, hr23⟩ ?_
            rintro st₁ ⟨qA', qHA', remA', hBA', hSA', hDA', hr22', hr23', hm1, hreg1⟩
            have hSB1 : SideMemAt st₁.mem qBufB visB vCap qB :=
              hSB.of_agree (fun i hi => hm1 _ (by omega) (by omega))
                (fun v hv => hm1 _ (by omega) (by omega)) hqB_le
            have hDB1 : DllTailAt st₁.mem heNext (2 * eCapF) remB (st₁.regs 27) := by
              rw [hreg1 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
              exact dllTailAt_congr hDB (fun h hh => hm1 (heNext + h) (by omega) (by omega))
            have hdgAg1 : ∀ a, a < dgFPtr + dynGraphSize vCap eCapF → st₁.mem a = mem0 a :=
              fun a ha => (hm1 a (by omega) (by omega)).trans (hdgAg0 a ha)
            have hmicroB := bfsMicroStep_triple (w := w) (p := p) (dgFPtr := dgFPtr) (vCap := vCap)
              (eCapF := eCapF) (qBuf := qBufB) (vis := visB) (u₀ := uB) (qHead := qHB) (steps := k)
              (rQBuf := 19) (rVis := 21) (rQHead := 25) (rQTail := 26) (rCurHe := 27)
              (mem0 := mem0) (mem_in := st₁.mem) (regs_in := st₁.regs) (q := qB) (remHe := remB)
              hw16 (by decide) hdg_ltw (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
              hF.1 hvCap heCap hExtToInt hIntToExt hEndSlot hincL hBB hnotB
            have hB_pre : st₁.mem = st₁.mem ∧ st₁.regs = st₁.regs ∧
                (∀ a, a < dgFPtr + dynGraphSize vCap eCapF → st₁.mem a = mem0 a) ∧
                SideMemAt st₁.mem qBufB visB vCap qB ∧
                DllTailAt st₁.mem heNext (2 * eCapF) remB (st₁.regs 27) ∧
                st₁.regs 12 = extToInt ∧ st₁.regs 13 = intToExt ∧ st₁.regs 14 = incHead ∧
                st₁.regs 15 = eTailSlot ∧ st₁.regs 16 = eHeadSlot ∧ st₁.regs 17 = heNext ∧
                st₁.regs 19 = qBufB ∧ st₁.regs 21 = visB ∧
                st₁.regs 25 = qHB ∧ st₁.regs 26 = qB.length := by
              refine ⟨rfl, rfl, hdgAg1, hSB1, hDB1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact (hreg1 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr12_0)
              · exact (hreg1 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr13_0)
              · exact (hreg1 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr14_0)
              · exact (hreg1 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr15_0)
              · exact (hreg1 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr16_0)
              · exact (hreg1 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr17_0)
              · exact (hreg1 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr19_0)
              · exact (hreg1 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hget 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr21_0)
              · exact (hreg1 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr25
              · exact (hreg1 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr26
            obtain ⟨o2, st₂, c2, hrun2, hpost2, hc2⟩ := hmicroB st₁ ω' hB_pre
            cases o2 with
            | returned _ => exact False.elim hpost2
            | normal =>
              rcases hpost2 with ⟨qB', qHB', remB', hBB', hSB', hDB', hr25', hr26', hm2, hreg2⟩
              refine ⟨.normal, st₂, c2, hrun2, ?_, by dsimp only [Expr.size] at hc2 ⊢; omega⟩
              have hqA'_le : qA'.length ≤ vCap :=
                list_len_le_vCap hvCap hBA'.hq_nd (fun v hv => (hBA'.hq_sub v hv).1)
              have hSA2 : SideMemAt st₂.mem qBufA visA vCap qA' :=
                hSA'.of_agree (fun i hi => hm2 _ (by omega) (by omega))
                  (fun v hv => hm2 _ (by omega) (by omega)) hqA'_le
              have hDA2 : DllTailAt st₂.mem heNext (2 * eCapF) remA' (st₂.regs 24) := by
                rw [hreg2 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                exact dllTailAt_congr hDA' (fun h hh => hm2 (heNext + h) (by omega) (by omega))
              have hreg12 : ∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
                  r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st₂.regs r = regs_in r :=
                fun r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32 =>
                  (hreg2 r h25 h26 h27 h29 h30 h31 h32).trans
                    ((hreg1 r h22 h23 h24 h29 h30 h31 h32).trans
                      (hreg r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32))
              have h28_2 : st₂.regs 28 = 1 :=
                (hreg2 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  ((hreg1 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                    (by simpa using h28))
              have hfr2 : ∀ a, ¬ (qBufA ≤ a ∧ a < visB + vCap) → st₂.mem a = mem0 a := fun a ha =>
                (hm2 a (by omega) (by omega)).trans ((hm1 a (by omega) (by omega)).trans (hfr a ha))
              refine ⟨(k + 1, true), ⟨hfr2, hreg12, by simpa using h28_2,
                qA', qHA', remA', qB', qHB', remB', hBA', hBB', hSA2, hSB', hDA2, hDB',
                by rw [hreg2 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr22',
                by rw [hreg2 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr23',
                hr25', hr26', fun h => by cases h⟩,
                by dsimp [mMeas]; omega, by dsimp [remCost, mMeas, Expr.size]; omega⟩
          · -- Side B is done! Set `r28 := 0`
            intro hB_0
            have hB_done : qHB = qB.length ∧ remB = [] := by
              have h1 : st.regs 27 = 0 := by omega
              have h2 : qHB = qB.length := by have := hBB.hqh_le; omega
              refine ⟨h2, ?_⟩
              cases remB with
              | nil => rfl
              | cons a tl => exfalso; exact Nat.succ_ne_zero a (hDB.1.symm.trans h1)
            refine runs_assign_le (v := 0) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
            refine ⟨(k, false), ⟨hfr, fun r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32 => by
              dsimp only; rw [Function.update_of_ne h28']; exact hreg r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32,
              by simp,
              qA, qHA, remA, qB, qHB, remB, hBA, hBB, hSA, hSB, by simpa using hDA,
              by simpa using hDB, by simp [hr22], by simp [hr23], by simp [hr25], by simp [hr26],
              fun _ => Or.inr hB_done⟩,
              by dsimp [mMeas]; omega, by dsimp [remCost, mMeas, Expr.size]; omega⟩
        · -- Side A is done! Set `r28 := 0`
          intro hA_0
          have hA_done : qHA = qA.length ∧ remA = [] := by
            have h1 : st.regs 24 = 0 := by omega
            have h2 : qHA = qA.length := by have := hBA.hqh_le; omega
            refine ⟨h2, ?_⟩
            cases remA with
            | nil => rfl
            | cons a tl => exfalso; exact Nat.succ_ne_zero a (hDA.1.symm.trans h1)
          refine runs_assign_le (v := 0) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
          refine ⟨(k, false), ⟨hfr, fun r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32 => by
            dsimp only; rw [Function.update_of_ne h28']; exact hreg r h22 h23 h24 h25 h26 h27 h28' h29 h30 h31 h32,
            by simp,
            qA, qHA, remA, qB, qHB, remB, hBA, hBB, hSA, hSB, by simpa using hDA,
            by simpa using hDB, by simp [hr22], by simp [hr23], by simp [hr25], by simp [hr26],
            fun _ => Or.inl hA_done⟩,
            by dsimp [mMeas]; omega, by dsimp [remCost, mMeas, Expr.size]; omega⟩)
      (0, true)
  obtain ⟨o, st', c, hr, hq, hc⟩ := hloop st_init ω_init
    ⟨hfr0, hreg0, by simpa using h28_0, [uA], 0, [], [uB], 0, [],
      bfsInv_init huA, bfsInv_init huB, hSA0, hSB0,
      by simp [DllTailAt, h24_0], by simp [DllTailAt, h27_0], h22_0, h23_0, h25_0, h26_0,
      fun h => by cases h⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨k, hfr, hreg, _, qA, qHA, remA, qB, qHB, remB,
      hBA, hBB, hSA, hSB, hDA, hDB, h22, h23, h25, h26, hdone⟩
    refine ⟨.normal, st', c, hr, ⟨hfr, hreg, k, qA, qHA, remA, qB, qHB, remB,
      hBA, hBB, hSA, hSB, hDA, hDB, h22, h23, h25, h26, hdone rfl⟩, ?_⟩
    simpa [remCost, mMeas] using hc

/-- Setup prefix triple: computes `r12..r21` and initializes queues `[uA]` and `[uB]` in at most
`140` steps, leaving all memory outside `[qBufA, visB + vCap)` and registers `r0..r11` unchanged. -/
lemma bfsSetup_triple {w dgFPtr fAncPtr auxPtr vCap eCapF n0 uA uB oldCid root1 root2 newSum : ℕ}
    {p : Program} {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hdg_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w)
    (haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w)
    (hqAPtr : mem (auxPtr + auxOffQBufAPtr) = auxQBufABase auxPtr vCap n0)
    (hqBPtr : mem (auxPtr + auxOffQBufBPtr) = auxQBufBBase auxPtr vCap n0)
    (hvAPtr : mem (auxPtr + auxOffVisAPtr) = auxVisABase auxPtr vCap n0)
    (hvBPtr : mem (auxPtr + auxOffVisBPtr) = auxVisBBase auxPtr vCap n0)
    (hvis0 : ∀ v < vCap, mem (auxVisABase auxPtr vCap n0 + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap n0 + v) = 0)
    (huA_lt : uA < vCap) (huB_lt : uB < vCap) :
    Triple w p
      (fun st => st.mem = mem ∧
        st.regs 0 = dgFPtr ∧ st.regs 1 = fAncPtr ∧ st.regs 2 = auxPtr ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCapF ∧ st.regs 6 = uA ∧ st.regs 7 = uB ∧
        st.regs 8 = oldCid ∧ st.regs 9 = root1 ∧ st.regs 10 = root2 ∧ st.regs 11 = newSum)
      bfsSetupStmt
      (normalPost fun st =>
        (∀ a, ¬ (auxQBufABase auxPtr vCap n0 ≤ a ∧ a < auxVisBBase auxPtr vCap n0 + vCap) →
          st.mem a = mem a) ∧
        st.regs 1 = fAncPtr ∧ st.regs 8 = oldCid ∧ st.regs 9 = root1 ∧ st.regs 10 = root2 ∧
        st.regs 11 = newSum ∧
        st.regs 12 = dgExtToIntBase dgFPtr vCap ∧ st.regs 13 = dgIntToExtBase dgFPtr vCap ∧
        st.regs 14 = dgIncHeadBase dgFPtr vCap ∧ st.regs 15 = dgETailSlotBase dgFPtr vCap eCapF ∧
        st.regs 16 = dgEHeadSlotBase dgFPtr vCap eCapF ∧ st.regs 17 = dgHeNextBase dgFPtr vCap eCapF ∧
        st.regs 18 = auxQBufABase auxPtr vCap n0 ∧ st.regs 19 = auxQBufBBase auxPtr vCap n0 ∧
        st.regs 20 = auxVisABase auxPtr vCap n0 ∧ st.regs 21 = auxVisBBase auxPtr vCap n0 ∧
        st.regs 28 = 1 ∧
        SideMemAt st.mem (auxQBufABase auxPtr vCap n0) (auxVisABase auxPtr vCap n0) vCap [uA] ∧
        SideMemAt st.mem (auxQBufBBase auxPtr vCap n0) (auxVisBBase auxPtr vCap n0) vCap [uB] ∧
        st.regs 22 = 0 ∧ st.regs 23 = 1 ∧ st.regs 24 = 0 ∧
        st.regs 25 = 0 ∧ st.regs 26 = 1 ∧ st.regs 27 = 0)
      (fun _ => 140) := by
  classical
  set qBufA := auxQBufABase auxPtr vCap n0
  set qBufB := auxQBufBBase auxPtr vCap n0
  set visA := auxVisABase auxPtr vCap n0
  set visB := auxVisBBase auxPtr vCap n0
  set extToInt := dgExtToIntBase dgFPtr vCap
  set intToExt := dgIntToExtBase dgFPtr vCap
  set incHead := dgIncHeadBase dgFPtr vCap
  set eTailSlot := dgETailSlotBase dgFPtr vCap eCapF
  set eHeadSlot := dgEHeadSlotBase dgFPtr vCap eCapF
  set heNext := dgHeNextBase dgFPtr vCap eCapF
  have hqA_qB : qBufA + vCap = qBufB := rfl
  have hqB_vA : qBufB + vCap = visA := rfl
  have hvA_vB : visA + vCap = visB := rfl
  have hvB_le : visB + vCap ≤ auxPtr + auxSize vCap n0 := by
    dsimp [visB, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
      auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
  have haux_hdr_lt : auxPtr + 14 < 2 ^ w := by dsimp [auxSize, auxHdrSize] at haux_ltw; omega
  have hdg_size_lt : dgFPtr + 4 + 7 * vCap + 7 * eCapF < 2 ^ w := by
    dsimp [dynGraphSize] at hdg_ltw; omega
  intro st ω ⟨hm, h0, h1, h2, h3, h4, h6, h7, h8, h9, h10, h11⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hm h0 h1 h2 h3 h4 h6 h7 h8 h9 h10 h11
  subst stm
  suffices h : ∃ o st' c, Runs w p ω bfsSetupStmt { mem := mem, regs := str, pos := stp } o st' c ∧
      normalPost (fun st =>
        (∀ a, ¬ (qBufA ≤ a ∧ a < visB + vCap) → st.mem a = mem a) ∧
        st.regs 1 = fAncPtr ∧ st.regs 8 = oldCid ∧ st.regs 9 = root1 ∧ st.regs 10 = root2 ∧
        st.regs 11 = newSum ∧
        st.regs 12 = extToInt ∧ st.regs 13 = intToExt ∧
        st.regs 14 = incHead ∧ st.regs 15 = eTailSlot ∧
        st.regs 16 = eHeadSlot ∧ st.regs 17 = heNext ∧
        st.regs 18 = qBufA ∧ st.regs 19 = qBufB ∧ st.regs 20 = visA ∧ st.regs 21 = visB ∧
        st.regs 28 = 1 ∧
        SideMemAt st.mem qBufA visA vCap [uA] ∧ SideMemAt st.mem qBufB visB vCap [uB] ∧
        st.regs 22 = 0 ∧ st.regs 23 = 1 ∧ st.regs 24 = 0 ∧
        st.regs 25 = 0 ∧ st.regs 26 = 1 ∧ st.regs 27 = 0) o st' ∧
      0 + c ≤ 140 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  dsimp only [bfsSetupStmt]
  refine runs_seq_assign_le (v := extToInt) (by dsimp only [extToInt, dgExtToIntBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := intToExt) (by dsimp only [intToExt, dgIntToExtBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := incHead) (by dsimp only [incHead, dgIncHeadBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := eTailSlot) (by dsimp only [eTailSlot, dgETailSlotBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := eHeadSlot) (by dsimp only [eHeadSlot, dgEHeadSlotBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := heNext) (by dsimp only [heNext, dgHeNextBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := qBufA) (by dsimp only [auxOffQBufAPtr]; eval_expr) hqAPtr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := qBufB) (by dsimp only [auxOffQBufBPtr]; eval_expr) hqBPtr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := visA) (by dsimp only [auxOffVisAPtr]; eval_expr) hvAPtr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := visB) (by dsimp only [auxOffVisBPtr]; eval_expr) hvBPtr) ?_; dsimp only
  refine runs_seq_store_le (x := qBufA) (v := uA) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := visA + uA) (v := 1) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := qBufB) (v := uB) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := visB + uB) (v := 1) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
  refine runs_assign_le (v := 1) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
  dsimp only
  refine ⟨fun a ha => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
    by simpa using h1, by simpa using h8, by simpa using h9, by simpa using h10, by simpa using h11,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨fun i hi => by
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      dsimp only
      rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]; rfl,
      fun v hv => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        by_cases hvu : v = uA
        · subst hvu; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), (hvis0 v hv).1]
          simp [hvu]⟩,
    ⟨fun i hi => by
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      dsimp only
      rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_self]; rfl,
      fun v hv => by
        dsimp only
        by_cases hvu : v = uB
        · subst hvu; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), (hvis0 v hv).2]
          simp [hvu]⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end MinCostFlow.LSF.Program
