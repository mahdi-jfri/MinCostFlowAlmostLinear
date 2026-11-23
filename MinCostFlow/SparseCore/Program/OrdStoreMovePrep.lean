module

public import MinCostFlow.SparseCore.Program.OrdStoreSort
public import MinCostFlow.SparseCore.Program.OrdStoreFreeTree
public import MinCostFlow.SparseCore.Program.OrdStoreInsertBack
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Preparation: Pure Lemmas and Mark/Unmark Passes

This file provides:
1. Pure lemmas for `moveEnds`: `TreeInv.freeTreeShape`, `leftSpine_treePhi_le`, and
   `sorted_pairs_eq_filter` (sorting distinct `(idxOf, u)` pairs recovers the filtered sublist).
2. Passes 1–2 of `ordMoveEndsBody`: `ordMoveMarkLoop` deduplicates the live nodes among the input
   key array using the node `mark` slot (offset `+ 6`) into `scratch`, and `ordMoveUnmarkLoop`
   resets every modified `mark` slot to `0`, restoring `OrdArenaAt` completely before any splay.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Pure helper lemmas for `moveEnds` -/

theorem SubtreeInv.freeTreeShape {sp : SplayState ℕ Unit Unit} {p : ℕ} {t : AuxTree}
    (h : SplayState.SubtreeInv ordPayload sp p t) : FreeTreeShape sp t := by
  induction t generalizing p with
  | leaf => trivial
  | node id l r ihl ihr =>
    rcases h with ⟨hnz, hl, hr, -, -, -, -, hsubL, hsubR⟩
    exact ⟨hnz, hl, hr, ihl hsubL, ihr hsubR⟩

theorem TreeInv.freeTreeShape {sp : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : TreeInv ordPayload sp t) : FreeTreeShape sp t :=
  SubtreeInv.freeTreeShape h.sub

theorem leftSpineGo_treePhi_le {eCap : ℕ} (acc : AuxTree) (us : List ℕ)
    (hsz : acc.countNodes + us.length ≤ 2 * eCap) :
    (leftSpine.leftSpineGo acc us).treePhi (fun _ => 0) ≤
      acc.treePhi (fun _ => 0) + us.length * ordStoreLog eCap := by
  induction us generalizing acc with
  | nil => simp [leftSpine.leftSpineGo]
  | cons u us ih =>
    simp only [leftSpine.leftSpineGo, List.length_cons]
    have hsz' : (AuxTree.node u acc .leaf).countNodes + us.length ≤ 2 * eCap := by
      simp only [AuxTree.countNodes, List.length_cons] at hsz ⊢; omega
    have hih := ih (.node u acc .leaf) hsz'
    have hrk : (AuxTree.node u acc .leaf).rank (fun _ => 0) ≤ ordStoreLog eCap :=
      rank_zero_le_ordStoreLog (by simp only [AuxTree.countNodes] at hsz' ⊢; omega)
    have hphi_step : (AuxTree.node u acc .leaf).treePhi (fun _ => 0) =
        (AuxTree.node u acc .leaf).rank (fun _ => 0) + acc.treePhi (fun _ => 0) := by
      simp [AuxTree.treePhi]
    have hmul : (us.length + 1) * ordStoreLog eCap = us.length * ordStoreLog eCap + ordStoreLog eCap := by ring
    omega

theorem leftSpine_treePhi_le {eCap : ℕ} (us : List ℕ) (hsz : us.length ≤ 2 * eCap) :
    (leftSpine us).treePhi (fun _ => 0) ≤ us.length * ordStoreLog eCap := by
  cases us with
  | nil => simp [leftSpine, AuxTree.treePhi]
  | cons u us =>
    simp only [leftSpine, List.length_cons]
    have hsz' : (AuxTree.node u .leaf .leaf).countNodes + us.length ≤ 2 * eCap := by
      simp only [AuxTree.countNodes, List.length_cons] at hsz ⊢; omega
    have hgo := leftSpineGo_treePhi_le (.node u .leaf .leaf) us hsz'
    have hbase : (AuxTree.node u .leaf .leaf).treePhi (fun _ => 0) = 0 := by
      simp [AuxTree.treePhi, AuxTree.rank, treeSize_zero_eq_countNodes, AuxTree.countNodes]
    have hmul : (us.length + 1) * ordStoreLog eCap = us.length * ordStoreLog eCap + ordStoreLog eCap := by ring
    omega

private theorem eq_of_mem_iff_of_strictMono {l1 l2 : List ℕ} {f : ℕ → ℕ}
    (h1 : (l1.map f).Pairwise (· < ·)) (h2 : (l2.map f).Pairwise (· < ·))
    (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2)
    (hinj : ∀ a ∈ l1, ∀ b ∈ l1, f a = f b → a = b) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b bs => exfalso; exact List.not_mem_nil ((hmem b).mpr List.mem_cons_self)
  | cons a as ih =>
    cases l2 with
    | nil => exfalso; exact List.not_mem_nil ((hmem a).mp List.mem_cons_self)
    | cons b bs =>
      rw [List.map_cons, List.pairwise_cons] at h1 h2
      have ha_in : a ∈ b :: bs := (hmem a).mp List.mem_cons_self
      have hb_in : b ∈ a :: as := (hmem b).mpr List.mem_cons_self
      have hab : a = b := by
        rcases List.mem_cons.mp ha_in with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp hb_in with rfl | hb_as
          · rfl
          · have hlt1 : f b < f a := h2.1 (f a) (List.mem_map_of_mem ha_bs)
            have hlt2 : f a < f b := h1.1 (f b) (List.mem_map_of_mem hb_as)
            omega
      subst hab
      have ha_nas : a ∉ as := fun h => Nat.lt_irrefl (f a) (h1.1 (f a) (List.mem_map_of_mem h))
      have ha_nbs : a ∉ bs := fun h => Nat.lt_irrefl (f a) (h2.1 (f a) (List.mem_map_of_mem h))
      congr 1
      apply ih h1.2 h2.2
      · intro x
        have hx := hmem x
        simp only [List.mem_cons] at hx
        constructor
        · intro hxs
          have hne : x ≠ a := fun h => ha_nas (h ▸ hxs)
          rcases hx.mp (Or.inr hxs) with rfl | hxb
          · exact absurd rfl hne
          · exact hxb
        · intro hxb
          have hne : x ≠ a := fun h => ha_nbs (h ▸ hxb)
          rcases hx.mpr (Or.inr hxb) with rfl | hxs
          · exact absurd rfl hne
          · exact hxs
      · intro x hx y hy hxy
        exact hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy

private theorem idxOf_strict_of_filter {L : List ℕ} {pred : ℕ → Bool} (hnd : L.Nodup) :
    ((L.filter pred).map L.idxOf).Pairwise (· < ·) := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨ha, htl⟩
    have hmap_tl : ∀ (xs : List ℕ), (∀ x ∈ xs, x ∈ tl) →
        xs.map (a :: tl).idxOf = (xs.map tl.idxOf).map (· + 1) := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x rest ihr =>
        have hne : a ≠ x := fun h => ha (h ▸ hxs x List.mem_cons_self)
        simp [List.idxOf_cons, hne]
        exact fun y hy h => ha (h ▸ hxs y (List.mem_cons_of_mem x hy))
    have hfilt_sub : ∀ x ∈ tl.filter pred, x ∈ tl := fun x hx => (List.mem_filter.mp hx).1
    have hpw_tl : ((tl.filter pred).map (a :: tl).idxOf).Pairwise (· < ·) := by
      rw [hmap_tl _ hfilt_sub]
      exact List.pairwise_map.mpr ((ih htl).imp fun {a b} h => Nat.succ_lt_succ h)
    by_cases hp : pred a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.idxOf_cons_self,
        List.pairwise_cons]
      refine ⟨fun k hk => ?_, hpw_tl⟩
      rw [hmap_tl _ hfilt_sub, List.mem_map] at hk
      rcases hk with ⟨m, _, rfl⟩
      omega
    · simp only [List.filter_cons, Bool.eq_false_iff.mpr hp, Bool.false_eq_true, ↓reduceIte]
      exact hpw_tl

theorem idxOf_injective_of_mem {L : List ℕ} {a b : ℕ} (ha : a ∈ L) (hb : b ∈ L)
    (heq : L.idxOf a = L.idxOf b) : a = b := by
  have ha_lt : L.idxOf a < L.length := List.idxOf_lt_length_iff.mpr ha
  have hb_lt : L.idxOf b < L.length := List.idxOf_lt_length_iff.mpr hb
  have h1 : L[L.idxOf a]'ha_lt = a := List.getElem_idxOf ha_lt
  have h2 : L[L.idxOf b]'hb_lt = b := List.getElem_idxOf hb_lt
  rw [← h1, ← h2]; congr 1

theorem sorted_pairs_eq_filter {L : List ℕ} {pred : ℕ → Bool} {pairs : List (ℕ × ℕ)}
    (hndL : L.Nodup)
    (hsort : pairs.Pairwise (fun a b => a.1 ≤ b.1))
    (hndP : (pairs.map Prod.snd).Nodup)
    (hpos : ∀ p ∈ pairs, p.2 ∈ L ∧ p.1 = L.idxOf p.2)
    (hmem : ∀ u ∈ L, pred u = true ↔ u ∈ pairs.map Prod.snd) :
    pairs.map Prod.snd = L.filter pred := by
  have hpw1 : ((pairs.map Prod.snd).map L.idxOf).Pairwise (· < ·) := by
    rw [List.map_map]
    clear hmem
    induction pairs with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.nodup_cons, List.pairwise_cons] at hndP hsort ⊢
      refine ⟨fun k hk => ?_, ih hsort.2 hndP.2 (fun q hq => hpos q (List.mem_cons_of_mem p hq))⟩
      rcases List.mem_map.mp hk with ⟨q, hq, rfl⟩
      have hp1 := hpos p List.mem_cons_self
      have hq1 := hpos q (List.mem_cons_of_mem p hq)
      have hle : p.1 ≤ q.1 := hsort.1 q hq
      have hne : p.2 ≠ q.2 := fun h => hndP.1 (List.mem_map.mpr ⟨q, hq, h.symm⟩)
      have hne_idx : L.idxOf p.2 ≠ L.idxOf q.2 := fun h => hne (idxOf_injective_of_mem hp1.1 hq1.1 h)
      simp only [Function.comp_apply]
      omega
  apply eq_of_mem_iff_of_strictMono hpw1 (idxOf_strict_of_filter hndL)
  · intro u
    rw [List.mem_filter]
    constructor
    · intro hu
      rcases List.mem_map.mp hu with ⟨p, hp, rfl⟩
      have hpL := (hpos p hp).1
      exact ⟨hpL, (hmem p.2 hpL).mpr hu⟩
    · rintro ⟨huL, hpu⟩
      exact (hmem u huL).mp hpu
  · intro a ha b hb heq
    rcases List.mem_map.mp ha with ⟨pa, hpa, rfl⟩
    rcases List.mem_map.mp hb with ⟨pb, hpb, rfl⟩
    exact idxOf_injective_of_mem (hpos pa hpa).1 (hpos pb hpb).1 heq

/-! ### Passes 1 and 2: mark/deduplicate and unmark -/

/-- Pass 1 of `moveEnds`: scans `j = 0 .. len - 1`, marks each newly seen live node at
`nb + 8 * u + 6`, and writes `u` to `scratch + 2 * cnt + 1`. -/
def ordMoveMarkLoop : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 4))
    (.assign 12 (.load (.bin .add (.reg 5) (.reg 10))) ;;
     .cond (.bin .lt (.reg 12) (.bin .add (.reg 7) (.reg 7)))
       (.assign 13 (.load (.bin .add (.reg 8) (.reg 12))) ;;
        .cond (.reg 13)
          (.assign 14 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 6)) ;;
           .assign 15 (.load (.reg 14)) ;;
           .cond (.bin .eq (.reg 15) (.const 0))
             (.store (.reg 14) (.const 1) ;;
              .store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 11) (.reg 11))) (.const 1)) (.reg 13) ;;
              .assign 11 (.bin .add (.reg 11) (.const 1)))
             .nop)
          .nop)
       .nop ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

/-- Pass 2 of `moveEnds`: clears `mark` (`offset + 6`) for every node in `scratch[0 .. 2*cnt - 1]`. -/
def ordMoveUnmarkLoop : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 11))
    (.assign 13 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1))) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 6)) (.const 0) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

theorem ordMoveMarkLoop_noRand : ordMoveMarkLoop.NoRand := by
  simp [ordMoveMarkLoop, Stmt.NoRand]

theorem ordMoveUnmarkLoop_noRand : ordMoveUnmarkLoop.NoRand := by
  simp [ordMoveUnmarkLoop, Stmt.NoRand]

theorem ordMoveMarkLoop_runs
    {w b len arrPtr scratch : ℕ} {p : Program} (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {mem0 : ℕ → ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem0)
    (hmem_eq : st0.mem = mem0)
    (harr_lt : arrPtr + len ≤ scratch)
    (harr_disj : ∀ j < len, ¬ ordFoot b S.vCap S.eCap (arrPtr + j))
    (harr_w : ∀ j < len, mem0 (arrPtr + j) < 2 ^ w)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch + 2 * len < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr4 : st0.regs 4 = len) (hr5 : st0.regs 5 = arrPtr) (hr6 : st0.regs 6 = scratch)
    (hr7 : st0.regs 7 = S.eCap) (hr8 : st0.regs 8 = ordENodeBase b S.vCap)
    (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr10 : st0.regs 10 = 0) (hr11 : st0.regs 11 = 0) :
    ∃ st' c, ∃ cand : List ℕ,
      Runs w p ω ordMoveMarkLoop st0 .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → st'.regs r = st0.regs r) ∧
      st'.regs 10 = len ∧ st'.regs 11 = cand.length ∧ cand.length ≤ len ∧
      cand.Nodup ∧
      (∀ u ∈ cand, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList) ∧
      (∀ u, u ∈ cand ↔ ∃ t < len, mem0 (arrPtr + t) < 2 * S.eCap ∧ S.eNode (mem0 (arrPtr + t)) = u ∧ u ≠ 0) ∧
      (∀ i < cand.length, st'.mem (scratch + 2 * i + 1) = cand.getD i 0) ∧
      (∀ u ∈ cand, st'.mem (ordNodesBase b S.vCap S.eCap + 8 * u + 6) = 1) ∧
      (∀ a, (∀ u ∈ cand, a ≠ ordNodesBase b S.vCap S.eCap + 8 * u + 6) →
            (∀ i < cand.length, a ≠ scratch + 2 * i + 1) → st'.mem a = mem0 a) ∧
      c ≤ 80 * len + 20 := by
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  set en := ordENodeBase b S.vCap with hen
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ scratch := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb]; omega
  have hloop : ∀ rem (j : ℕ) (st : State) (cand : List ℕ),
      j + rem = len →
      st.regs 4 = len → st.regs 5 = arrPtr → st.regs 6 = scratch →
      st.regs 7 = S.eCap → st.regs 8 = en → st.regs 9 = nb →
      st.regs 10 = j → st.regs 11 = cand.length → cand.length ≤ j →
      cand.Nodup →
      (∀ u ∈ cand, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList) →
      (∀ u, u ∈ cand ↔ ∃ t < j, mem0 (arrPtr + t) < 2 * S.eCap ∧ S.eNode (mem0 (arrPtr + t)) = u ∧ u ≠ 0) →
      (∀ i < cand.length, st.mem (scratch + 2 * i + 1) = cand.getD i 0) →
      (∀ u ∈ cand, st.mem (nb + 8 * u + 6) = 1) →
      (∀ a, (∀ u ∈ cand, a ≠ nb + 8 * u + 6) → (∀ i < cand.length, a ≠ scratch + 2 * i + 1) → st.mem a = mem0 a) →
      ∃ st' c, ∃ cand' : List ℕ,
        Runs w p ω ordMoveMarkLoop st .normal st' c ∧
        (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → st'.regs r = st.regs r) ∧
        st'.regs 10 = len ∧ st'.regs 11 = cand'.length ∧ cand'.length ≤ len ∧
        cand'.Nodup ∧
        (∀ u ∈ cand', ∃ w0 < S.vCap, u ∈ (S.trees w0).toList) ∧
        (∀ u, u ∈ cand' ↔ ∃ t < len, mem0 (arrPtr + t) < 2 * S.eCap ∧ S.eNode (mem0 (arrPtr + t)) = u ∧ u ≠ 0) ∧
        (∀ i < cand'.length, st'.mem (scratch + 2 * i + 1) = cand'.getD i 0) ∧
        (∀ u ∈ cand', st'.mem (nb + 8 * u + 6) = 1) ∧
        (∀ a, (∀ u ∈ cand', a ≠ nb + 8 * u + 6) → (∀ i < cand'.length, a ≠ scratch + 2 * i + 1) → st'.mem a = mem0 a) ∧
        c ≤ 80 * rem + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro j st cand hj r4 r5 r6 r7 r8 r9 r10 r11 hle hnd hlive hiff hscr hmk hout
      have hjlen : j = len := by omega
      subst hjlen
      have hcond : (Expr.bin .lt (.reg 10) (.reg 4)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r4) (by omega) (by omega)
      refine ⟨st, _, cand, ord_runs_loop_false hcond, fun _ _ _ _ _ _ _ => rfl, r10, r11, hle,
        hnd, hlive, hiff, hscr, hmk, hout, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro j st cand hj r4 r5 r6 r7 r8 r9 r10 r11 hle hnd hlive hiff hscr hmk hout
      have hcond : (Expr.bin .lt (.reg 10) (.reg 4)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r4) (by omega) (by omega)
      set k := mem0 (arrPtr + j) with hk_def
      have hmem_arr : st.mem (arrPtr + j) = k :=
        hout (arrPtr + j) (fun u hu h => by
          rcases hlive u hu with ⟨w0, hw0, hmemu⟩
          have hu_le := le_trans (hinv.live_le_nextNode hw0 hmemu).2 hinv.next_le
          exact harr_disj j (by omega) (by rw [h, hnb]; exact ordFoot_node hu_le (by decide)))
          (fun i _ => by omega)
      have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 5) (.reg 10)))) st .normal
          { st with regs := Function.update st.regs 12 k } _ :=
        runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r5)
          (Expr.eval_reg_of_eq r10) (by omega)) hmem_arr, rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 12 k }
      -- Conditional body: possibly append new live node u to cand
      have hstep : ∃ st2 c2, ∃ cand1 : List ℕ,
          Runs w p ω
            (.cond (.bin .lt (.reg 12) (.bin .add (.reg 7) (.reg 7)))
              (.assign 13 (.load (.bin .add (.reg 8) (.reg 12))) ;;
               .cond (.reg 13)
                 (.assign 14 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 6)) ;;
                  .assign 15 (.load (.reg 14)) ;;
                  .cond (.bin .eq (.reg 15) (.const 0))
                    (.store (.reg 14) (.const 1) ;;
                     .store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 11) (.reg 11))) (.const 1)) (.reg 13) ;;
                     .assign 11 (.bin .add (.reg 11) (.const 1)))
                    .nop)
                 .nop)
              .nop) st1 .normal st2 c2 ∧
          (∀ r, r ≠ 11 → r ≠ 13 → r ≠ 14 → r ≠ 15 → st2.regs r = st1.regs r) ∧
          st2.regs 11 = cand1.length ∧ cand1.length ≤ j + 1 ∧
          cand1.Nodup ∧
          (∀ u ∈ cand1, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList) ∧
          (∀ u, u ∈ cand1 ↔ ∃ t < j + 1, mem0 (arrPtr + t) < 2 * S.eCap ∧ S.eNode (mem0 (arrPtr + t)) = u ∧ u ≠ 0) ∧
          (∀ i < cand1.length, st2.mem (scratch + 2 * i + 1) = cand1.getD i 0) ∧
          (∀ u ∈ cand1, st2.mem (nb + 8 * u + 6) = 1) ∧
          (∀ a, (∀ u ∈ cand1, a ≠ nb + 8 * u + 6) → (∀ i < cand1.length, a ≠ scratch + 2 * i + 1) → st2.mem a = mem0 a) ∧
          c2 ≤ 55 := by
        by_cases hk : k < S.eCap + S.eCap
        · have hk2 : k < 2 * S.eCap := by omega
          have hc1 : (Expr.bin .lt (.reg 12) (.bin .add (.reg 7) (.reg 7))).eval w st1 = some 1 :=
            Expr.eval_lt_true (Expr.eval_reg_of_eq (v := k) (by simp [st1]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st1, r7]))
                (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st1, r7])) (by omega)) hk (by omega)
          have hmem_ek : st1.mem (en + k) = S.eNode k :=
            (hout (en + k) (fun _ _ => by rw [hen, hnb]; unfold ordENodeBase ordNodesBase; omega)
              (fun _ _ => by rw [hen]; unfold ordENodeBase; omega)).trans (harena.eNode_at k hk2)
          have ha13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 8) (.reg 12)))) st1 .normal
              { st1 with regs := Function.update st1.regs 13 (S.eNode k) } _ :=
            runs_assign_iff.mpr ⟨S.eNode k, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [st1, r8])) (Expr.eval_reg_of_eq (by simp [st1]))
              (by rw [hen]; unfold ordENodeBase; omega)) hmem_ek, rfl, rfl, rfl⟩
          set st2 : State := { st1 with regs := Function.update st1.regs 13 (S.eNode k) }
          rcases hinv.eNode_spec k hk2 with ⟨he0, _⟩ | ⟨w0, hw0, hu_mem, _⟩
          · have hc2 : (Expr.reg 13).eval w st2 = some 0 := Expr.eval_reg_of_eq (by simp [st2, he0])
            refine ⟨st2, _, cand, ord_runs_cond_true hc1 Nat.one_ne_zero (ord_runs_seq_normal ha13
              (ord_runs_cond_false hc2 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))),
              fun r _ h13 _ _ => by simp [st2, h13], by simp [st2, st1, r11], by omega, hnd, hlive,
              fun u => by
                rw [hiff u]; constructor
                · rintro ⟨t, ht, h1, h2, h3⟩; exact ⟨t, by omega, h1, h2, h3⟩
                · rintro ⟨t, ht, h1, h2, h3⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
                  · exact ⟨t, hlt, h1, h2, h3⟩
                  · rw [← hk_def, he0] at h2; exact absurd h2.symm h3,
              hscr, hmk, hout, by simp [Expr.size_load, Expr.size_bin, Expr.size_reg]⟩
          · set u := S.eNode k with hu_def
            have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero (hinv.tree_inv w0 hw0).sub hu_mem
            have hu_le : u ≤ S.nextNode := (hinv.live_le_nextNode hw0 hu_mem).2
            have hc2 : (Expr.reg 13).eval w st2 = some u := Expr.eval_reg_of_eq (by simp [st2, hu_def])
            have ha14 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 6))) st2 .normal
                { st2 with regs := Function.update st2.regs 14 (nb + 8 * u + 6) } _ :=
              runs_assign_iff.mpr ⟨nb + 8 * u + 6, Expr.eval_add (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [st2, st1, r9]))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2, hu_def])) (by omega)) (by omega))
                (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
            set st3 : State := { st2 with regs := Function.update st2.regs 14 (nb + 8 * u + 6) }
            by_cases hu_in : u ∈ cand
            · have hm_u : st3.mem (nb + 8 * u + 6) = 1 := hmk u hu_in
              have ha15 : Runs w p ω (.assign 15 (.load (.reg 14))) st3 .normal
                  { st3 with regs := Function.update st3.regs 15 1 } _ :=
                runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st3])) hm_u, rfl, rfl, rfl⟩
              set st4 : State := { st3 with regs := Function.update st3.regs 15 1 }
              have hc3 : (Expr.bin .eq (.reg 15) (.const 0)).eval w st4 = some 0 :=
                Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 1) (by simp [st4]))
                  (Expr.eval_const (by omega)) (by omega) (by omega)
              refine ⟨st4, _, cand, ord_runs_cond_true hc1 Nat.one_ne_zero (ord_runs_seq_normal ha13
                (ord_runs_cond_true hc2 hu_nz (ord_runs_seq_normal ha14 (ord_runs_seq_normal ha15
                  (ord_runs_cond_false hc3 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))),
                fun r _ h13 h14 h15 => by simp [st4, st3, st2, h13, h14, h15],
                by simp [st4, st3, st2, st1, r11], by omega, hnd, hlive,
                fun z => by
                  rw [hiff z]; constructor
                  · rintro ⟨t, ht, h1, h2, h3⟩; exact ⟨t, by omega, h1, h2, h3⟩
                  · rintro ⟨t, ht, h1, h2, h3⟩
                    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
                    · exact ⟨t, hlt, h1, h2, h3⟩
                    · rw [← hk_def] at h2; subst h2; exact (hiff u).mp hu_in,
                hscr, hmk, hout, by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
            · have hm_u : st3.mem (nb + 8 * u + 6) = 0 := by
                have h1 := hout (nb + 8 * u + 6)
                  (fun z hz h => hu_in (by have hzu : z = u := by omega
                                           exact hzu ▸ hz))
                  (fun i _ => by omega)
                exact h1.trans (harena.nodes_at u hu_le).2.2.2.2.2.2.1
              have ha15 : Runs w p ω (.assign 15 (.load (.reg 14))) st3 .normal
                  { st3 with regs := Function.update st3.regs 15 0 } _ :=
                runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st3])) hm_u, rfl, rfl, rfl⟩
              set st4 : State := { st3 with regs := Function.update st3.regs 15 0 }
              have hc3 : (Expr.bin .eq (.reg 15) (.const 0)).eval w st4 = some 1 :=
                Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [st4]))
                  (Expr.eval_const (by omega)) rfl (by omega)
              have hs1 : Runs w p ω (.store (.reg 14) (.const 1)) st4 .normal
                  { st4 with mem := Function.update st.mem (nb + 8 * u + 6) 1 } _ :=
                runs_store_iff.mpr ⟨nb + 8 * u + 6, 1, Expr.eval_reg_of_eq (by simp [st4, st3]),
                  Expr.eval_const (by omega), rfl, rfl, rfl⟩
              set m1 := Function.update st.mem (nb + 8 * u + 6) 1
              set st5 : State := { st4 with mem := m1 }
              have hs2 : Runs w p ω
                  (.store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 11) (.reg 11))) (.const 1)) (.reg 13)) st5 .normal
                  { st5 with mem := Function.update m1 (scratch + 2 * cand.length + 1) u } _ :=
                runs_store_iff.mpr ⟨scratch + 2 * cand.length + 1, u,
                  by
                    have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 11) (.reg 11))) (.const 1)).eval w st5 =
                        some (scratch + (cand.length + cand.length) + 1) :=
                      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r6]))
                        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r11]))
                          (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r11])) (by omega)) (by omega))
                        (Expr.eval_const (by omega)) (by omega)
                    rwa [show scratch + (cand.length + cand.length) + 1 = scratch + 2 * cand.length + 1 by omega] at he,
                  Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, hu_def]), rfl, rfl, rfl⟩
              set m2 := Function.update m1 (scratch + 2 * cand.length + 1) u
              set st6 : State := { st5 with mem := m2 }
              have ha11 : Runs w p ω (.assign 11 (.bin .add (.reg 11) (.const 1))) st6 .normal
                  { st6 with regs := Function.update st6.regs 11 (cand.length + 1) } _ :=
                runs_assign_iff.mpr ⟨cand.length + 1, Expr.eval_add
                  (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, r11]))
                  (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
              refine ⟨{ st6 with regs := Function.update st6.regs 11 (cand.length + 1) }, _, cand ++ [u],
                ord_runs_cond_true hc1 Nat.one_ne_zero (ord_runs_seq_normal ha13
                  (ord_runs_cond_true hc2 hu_nz (ord_runs_seq_normal ha14 (ord_runs_seq_normal ha15
                    (ord_runs_cond_true hc3 Nat.one_ne_zero (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 ha11))))))),
                fun r h11 h13 h14 h15 => by simp [st6, st5, st4, st3, st2, h11, h13, h14, h15],
                by simp, by simp; omega,
                List.nodup_append.mpr ⟨hnd, List.nodup_singleton u, fun a ha b hb h => by
                  rw [List.mem_singleton.mp hb] at h; exact hu_in (h ▸ ha)⟩,
                fun z hz => by
                  rw [List.mem_append, List.mem_singleton] at hz
                  rcases hz with hzc | rfl; exact hlive z hzc; exact ⟨w0, hw0, hu_mem⟩,
                fun z => by
                  rw [List.mem_append, List.mem_singleton, hiff z]; constructor
                  · rintro (⟨t, ht, h1, h2, h3⟩ | rfl)
                    · exact ⟨t, by omega, h1, h2, h3⟩
                    · exact ⟨j, by omega, hk2, rfl, hu_nz⟩
                  · rintro ⟨t, ht, h1, h2, h3⟩
                    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
                    · exact Or.inl ⟨t, hlt, h1, h2, h3⟩
                    · rw [← hk_def] at h2; exact Or.inr h2.symm,
                fun i hi => by
                  simp only [List.length_append, List.length_singleton] at hi
                  dsimp only [st6, m2, m1]
                  by_cases hil : i < cand.length
                  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hscr i hil]
                    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
                  · have hi_eq : i = cand.length := by omega
                    subst hi_eq; simp [List.getD_eq_getElem?_getD],
                fun z hz => by
                  dsimp only [st6, m2, m1]
                  rw [List.mem_append, List.mem_singleton] at hz
                  rcases hz with hzc | rfl
                  · have hz_le : z ≤ S.nextNode := by rcases hlive z hzc with ⟨wz, hwz, hmz⟩; exact (hinv.live_le_nextNode hwz hmz).2
                    rw [Function.update_of_ne (by omega), Function.update_of_ne (fun h => hu_in (by
                      have hzu : z = u := by omega
                      exact hzu ▸ hzc))]
                    exact hmk z hzc
                  · rw [Function.update_of_ne (by omega)]; simp,
                fun a h1 h2 => by
                  dsimp only [st6, m2, m1]
                  rw [Function.update_of_ne (h2 cand.length (by simp)),
                      Function.update_of_ne (h1 u (by simp))]
                  exact hout a (fun z hz => h1 z (List.mem_append_left _ hz))
                    (fun i hi => h2 i (by simp; omega)),
                by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
        · have hc1 : (Expr.bin .lt (.reg 12) (.bin .add (.reg 7) (.reg 7))).eval w st1 = some 0 :=
            Expr.eval_lt_false (Expr.eval_reg_of_eq (v := k) (by simp [st1]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st1, r7]))
                (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st1, r7])) (by omega)) (by omega) (by omega)
          refine ⟨st1, _, cand, ord_runs_cond_false hc1 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
            fun _ _ _ _ _ => rfl, by simp [st1, r11], by omega, hnd, hlive,
            fun u => by
              rw [hiff u]; constructor
              · rintro ⟨t, ht, h1, h2, h3⟩; exact ⟨t, by omega, h1, h2, h3⟩
              · rintro ⟨t, ht, h1, h2, h3⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
                · exact ⟨t, hlt, h1, h2, h3⟩
                · rw [← hk_def] at h1; omega,
            hscr, hmk, hout, by simp [Expr.size_bin, Expr.size_reg]⟩
      obtain ⟨st2, c2, cand1, hrun2, hreg2, r11_2, hle2, hnd2, hlive2, hiff2, hscr2, hmk2, hout2, hc2⟩ := hstep
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st2 .normal
          { st2 with regs := Function.update st2.regs 10 (j + 1) } _ :=
        runs_assign_iff.mpr ⟨j + 1, Expr.eval_add
          (Expr.eval_reg_of_eq (by rw [hreg2 10 (by decide) (by decide) (by decide) (by decide)]; simp [st1, r10]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 10 (j + 1) }
      obtain ⟨stF, cF, candF, hrunF, hregF, r10F, r11F, hleF, hndF, hliveF, hiffF, hscrF, hmkF, houtF, hcF⟩ :=
        ih (j + 1) st3 cand1 (by omega)
          (by simp [st3, hreg2 4 (by decide) (by decide) (by decide) (by decide), st1, r4])
          (by simp [st3, hreg2 5 (by decide) (by decide) (by decide) (by decide), st1, r5])
          (by simp [st3, hreg2 6 (by decide) (by decide) (by decide) (by decide), st1, r6])
          (by simp [st3, hreg2 7 (by decide) (by decide) (by decide) (by decide), st1, r7])
          (by simp [st3, hreg2 8 (by decide) (by decide) (by decide) (by decide), st1, r8])
          (by simp [st3, hreg2 9 (by decide) (by decide) (by decide) (by decide), st1, r9])
          (by simp [st3]) (by simp [st3, r11_2]) hle2 hnd2 hlive2 hiff2 hscr2 hmk2 hout2
      refine ⟨stF, _, candF,
        ord_runs_loop_true hcond Nat.one_ne_zero (ord_runs_seq_normal ha12 (ord_runs_seq_normal hrun2 ha10)) hrunF,
        fun r h10 h11 h12 h13 h14 h15 => by
          rw [hregF r h10 h11 h12 h13 h14 h15]; simp only [st3, Function.update_of_ne h10]
          rw [hreg2 r h11 h13 h14 h15]; simp [st1, h12],
        r10F, r11F, hleF, hndF, hliveF, hiffF, hscrF, hmkF, houtF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  exact hloop len 0 st0 [] (by omega) hr4 hr5 hr6 hr7 hr8 hr9 hr10 (by simpa using hr11) (by simp)
    List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
    (fun _ => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, ht, _⟩ => by omega⟩)
    (fun _ hi => by simp at hi) (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ _ => hmem_eq ▸ rfl)

theorem ordMoveUnmarkLoop_runs
    {w b scratch : ℕ} {p : Program} (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {mem0 : ℕ → ℕ} {cand : List ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem0)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch + 2 * cand.length < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hnd : cand.Nodup)
    (hlive : ∀ u ∈ cand, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList)
    (hscr : ∀ i < cand.length, st0.mem (scratch + 2 * i + 1) = cand.getD i 0)
    (hout : ∀ a, (∀ u ∈ cand, a ≠ ordNodesBase b S.vCap S.eCap + 8 * u + 6) →
                 (∀ i < cand.length, a ≠ scratch + 2 * i + 1) → st0.mem a = mem0 a)
    (hr6 : st0.regs 6 = scratch) (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr10 : st0.regs 10 = 0) (hr11 : st0.regs 11 = cand.length) :
    ∃ st' c,
      Runs w p ω ordMoveUnmarkLoop st0 .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 13 → st'.regs r = st0.regs r) ∧
      OrdArenaAt b S st'.mem ∧
      (∀ i < cand.length, st'.mem (scratch + 2 * i + 1) = cand.getD i 0) ∧
      (∀ a, (∀ i < cand.length, a ≠ scratch + 2 * i + 1) → st'.mem a = mem0 a) ∧
      c ≤ 35 * cand.length + 15 := by
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ scratch := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb]; omega
  have hloop : ∀ rem (i : ℕ) (st : State),
      i + rem = cand.length →
      st.regs 6 = scratch → st.regs 9 = nb → st.regs 10 = i → st.regs 11 = cand.length →
      (∀ t < cand.length, st.mem (scratch + 2 * t + 1) = cand.getD t 0) →
      (∀ a, (∀ u ∈ cand.drop i, a ≠ nb + 8 * u + 6) →
            (∀ t < cand.length, a ≠ scratch + 2 * t + 1) → st.mem a = mem0 a) →
      ∃ st' c,
        Runs w p ω ordMoveUnmarkLoop st .normal st' c ∧
        (∀ r, r ≠ 10 → r ≠ 13 → st'.regs r = st.regs r) ∧
        (∀ t < cand.length, st'.mem (scratch + 2 * t + 1) = cand.getD t 0) ∧
        (∀ a, (∀ t < cand.length, a ≠ scratch + 2 * t + 1) → st'.mem a = mem0 a) ∧
        c ≤ 35 * rem + 15 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi r6 r9 r10 r11 hsc ho
      have hi_eq : i = cand.length := by omega
      subst hi_eq
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) (by omega) (by omega)
      refine ⟨st, _, ord_runs_loop_false hcond, fun _ _ _ => rfl, hsc,
        fun a ha => ho a (by simp) ha, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro i st hi r6 r9 r10 r11 hsc ho
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) (by omega) (by omega)
      set u := cand.getD i 0 with hu_def
      have hu_eq : cand[i]'(by omega) = u := by simp [hu_def, List.getD_eq_getElem?_getD, show i < cand.length by omega]
      have hu_mem : u ∈ cand := hu_eq ▸ List.getElem_mem (by omega)
      have hu_le : u ≤ S.nextNode := by rcases hlive u hu_mem with ⟨w0, hw0, hm⟩; exact (hinv.live_le_nextNode hw0 hm).2
      have ha13 : Runs w p ω
          (.assign 13 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)))) st .normal
          { st with regs := Function.update st.regs 13 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_load_of_eq (by
          have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)).eval w st =
              some (scratch + (i + i) + 1) :=
            Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r6)
              (Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r10) (by omega)) (by omega))
              (Expr.eval_const (by omega)) (by omega)
          rwa [show scratch + (i + i) + 1 = scratch + 2 * i + 1 by omega] at he) (hsc i (by omega)), rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 13 u }
      have hs1 : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 6)) (.const 0)) st1 .normal
          { st1 with mem := Function.update st.mem (nb + 8 * u + 6) 0 } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u + 6, 0, Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (by simp [st1, r9]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st1])) (by omega)) (by omega))
          (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
      set st2 : State := { st1 with mem := Function.update st.mem (nb + 8 * u + 6) 0 }
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st2 .normal
          { st2 with regs := Function.update st2.regs 10 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, r10]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 10 (i + 1) }
      have hdrop_cons : cand.drop i = u :: cand.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by omega), hu_eq]
      have ho' : ∀ a, (∀ z ∈ cand.drop (i + 1), a ≠ nb + 8 * z + 6) →
          (∀ t < cand.length, a ≠ scratch + 2 * t + 1) → st3.mem a = mem0 a := fun a h1 h2 => by
        dsimp only [st3, st2]
        by_cases ha : a = nb + 8 * u + 6
        · subst ha; simp only [Function.update_self]
          exact (harena.nodes_at u hu_le).2.2.2.2.2.2.1.symm
        · rw [Function.update_of_ne ha]
          exact ho a (fun z hz => by rw [hdrop_cons, List.mem_cons] at hz; rcases hz with rfl | hz'; exact ha; exact h1 z hz') h2
      obtain ⟨stF, cF, hrunF, hregF, hscF, hoF, hcF⟩ :=
        ih (i + 1) st3 (by omega) (by simp [st3, st2, st1, r6]) (by simp [st3, st2, st1, r9])
          (by simp [st3]) (by simp [st3, st2, st1, r11])
          (fun t ht => by dsimp only [st3, st2]; rw [Function.update_of_ne (by omega)]; exact hsc t ht)
          ho'
      refine ⟨stF, _, ord_runs_loop_true hcond Nat.one_ne_zero
        (ord_runs_seq_normal ha13 (ord_runs_seq_normal hs1 ha10)) hrunF,
        fun r h10 h13 => by rw [hregF r h10 h13]; simp [st3, st2, st1, h10, h13],
        hscF, hoF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  obtain ⟨stF, cF, hrunF, hregF, hscF, hoF, hcF⟩ :=
    hloop cand.length 0 st0 (by omega) hr6 hr9 hr10 hr11 hscr (by simpa using hout)
  refine ⟨stF, cF, hrunF, hregF, ?_, hscF, hoF, hcF⟩
  exact harena.congr hinv.next_le fun a ha => hoF a (fun t _ => by unfold ordFoot at ha; omega)

end MinCostFlow.SparseCore.Program
