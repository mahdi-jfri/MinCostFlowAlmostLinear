module

public import MinCostFlow.DynSpanner.Program.SortOps
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Log

/-!
# Part 1 of `MergeSort`

The first part of `MergeSort.lean`, split off to keep files short. See `MergeSort.lean` for the
overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma list_take_drop_take_len {α : Type*} (L : List α) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ L.length) :
    (L.take lo ++ (L.drop lo).take (hi - lo) ++ L.drop hi).length = L.length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

private lemma list_slice_replace_perm {L M : List ℕ} {lo hi : ℕ}
    (hlo : lo ≤ hi) (_hhi : hi ≤ L.length)
    (hM : M.Perm ((L.drop lo).take (hi - lo))) :
    (L.take lo ++ M ++ L.drop hi).Perm L := by
  have hrecon : L.take lo ++ (L.drop lo).take (hi - lo) ++ L.drop hi = L := by
    rw [List.append_assoc]
    have hsplit : (L.drop lo).take (hi - lo) ++ L.drop hi = L.drop lo := by
      conv_rhs => rw [← List.take_append_drop (hi - lo) (L.drop lo)]
      rw [List.drop_drop, show lo + (hi - lo) = hi by omega]
    rw [hsplit, List.take_append_drop]
  exact (((List.Perm.refl _).append hM).append (.refl _)).trans (by rw [hrecon])

private lemma list_slice_replace_getElem? {L M : List ℕ} {lo hi : ℕ}
    (hlo : lo ≤ hi) (hhi : hi ≤ L.length) (hMlen : M.length = hi - lo) :
    let L' := L.take lo ++ M ++ L.drop hi
    (∀ i < lo, L'[i]? = L[i]?) ∧
    (∀ i, hi ≤ i → L'[i]? = L[i]?) ∧
    (L'.drop lo).take (hi - lo) = M := by
  dsimp only
  refine ⟨fun i hi_lt => ?_, fun i hi_ge => ?_, ?_⟩
  · have htl : (L.take lo).length = lo := List.length_take_of_le (le_trans hlo hhi)
    rw [List.append_assoc, List.getElem?_append_left (by omega)]
    rw [List.getElem?_take_of_lt hi_lt]
  · have htl : (L.take lo).length = lo := List.length_take_of_le (le_trans hlo hhi)
    have hlen12 : (L.take lo ++ M).length = hi := by rw [List.length_append, htl, hMlen]; omega
    rw [List.getElem?_append_right (by omega), hlen12, List.getElem?_drop]
    congr 1; omega
  · have htl : (L.take lo).length = lo := List.length_take_of_le (le_trans hlo hhi)
    rw [List.append_assoc, List.drop_append_of_le_length htl.symm.le,
      List.drop_of_length_le htl.le, List.nil_append,
      List.take_append_of_le_length hMlen.symm.le, List.take_of_length_le hMlen.le]

private lemma list_slice_replace_getElem_mem {L M : List ℕ} {lo hi r : ℕ}
    (hlo : lo ≤ hi) (hhi : hi ≤ L.length) (hMlen : M.length = hi - lo) (hr : r < hi - lo) :
    (L.take lo ++ M ++ L.drop hi)[lo + r]'(by
      rw [List.length_append, List.length_append, List.length_take, List.length_drop, hMlen]; omega) =
      M[r]'(hMlen.symm ▸ hr) := by
  have htl : (L.take lo).length = lo := List.length_take_of_le (le_trans hlo hhi)
  rw [List.getElem_append_left (by rw [List.length_append, htl, hMlen]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp [htl]

private lemma natMerge_nil_right (xs : List ℕ) : natMerge xs [] = xs := by
  cases xs <;> simp [natMerge]

private lemma drop_take_getElem? {L : List ℕ} {a b k : ℕ} (hk : k < b - a) (hb : b ≤ L.length) :
    ((L.drop a).take (b - a))[k]'(by rw [List.length_take, List.length_drop]; omega) =
      L[a + k]'(by omega) := by
  rw [List.getElem_take, List.getElem_drop]

private lemma drop_take_nil_of_le {L : List ℕ} {a b : ℕ} (h : b ≤ a) :
    (L.drop a).take (b - a) = [] := by
  simp [show b - a = 0 by omega]

private lemma drop_take_succ_left {L : List ℕ} {a b : ℕ} (hab : a < b) (hb : b ≤ L.length) :
    (L.drop a).take (b - a) = L[a] :: (L.drop (a + 1)).take (b - (a + 1)) := by
  refine List.ext_getElem (by simp; omega) fun i hi₁ hi₂ => ?_
  cases i with
  | zero => simp [List.getElem_take, List.getElem_drop]
  | succ j =>
    simp only [List.getElem_cons_succ, List.getElem_take, List.getElem_drop,
      show a + (j + 1) = a + 1 + j by omega]

public section

theorem runs_cond_le_ms {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hq, by omega⟩
  · rcases hT hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hq, by omega⟩


theorem mergePair_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ}
    {L : List ℕ} {lo mid hi : ℕ}
    (hp : p.HasAt b (sortProcs bSort)) :
    MeetsContract w p (b + sortIdxMergePair) (mergePairContract w L lo mid hi) := by
  refine meetsContract_of_runs (hp.get (i := sortIdxMergePair) (by simp [sortProcs, sortIdxMergePair]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨a, scratch, rfl, hw16, haB, hscB, hdisj, hlomid, hmidhi, hhiL,
    hLat, hLw, _, _⟩
  have hlt_a : a < 2 ^ w := hargs a (by simp)
  have hlt_sc : scratch < 2 ^ w := hargs scratch (by simp)
  have hlt_lo : lo < 2 ^ w := hargs lo (by simp)
  have hlt_mid : mid < 2 ^ w := hargs mid (by simp)
  have hlt_hi : hi < 2 ^ w := hargs hi (by simp)
  have hlt_len : hi - lo < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  let L₁ := (L.drop lo).take (mid - lo)
  let L₂ := (L.drop mid).take (hi - mid)
  let M := natMerge L₁ L₂
  have hL₁_len : L₁.length = mid - lo := by rw [List.length_take, List.length_drop]; omega
  have hL₂_len : L₂.length = hi - mid := by rw [List.length_take, List.length_drop]; omega
  have hM_len : M.length = hi - lo := by
    dsimp only [M]; rw [natMerge_length, hL₁_len, hL₂_len]; omega
  refine runs_start_le ?_
  dsimp only [sortProcs, sortIdxMergePair, List.getElem_cons_zero, mergePairStmt]
  refine runs_seq_assign_le (v := lo) (by eval_expr) ?_
  refine runs_seq_assign_le (v := mid) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := hi - lo) (by eval_expr) ?_
  let InvM : State → Prop := fun st =>
    ∃ (i j k : ℕ) (acc : List ℕ),
      lo ≤ i ∧ i ≤ mid ∧ mid ≤ j ∧ j ≤ hi ∧ k = (i - lo) + (j - mid) ∧
      acc.length = k ∧
      acc ++ natMerge ((L.drop i).take (mid - i)) ((L.drop j).take (hi - j)) = M ∧
      st.regs 0 = a ∧ st.regs 1 = scratch ∧ st.regs 2 = lo ∧ st.regs 3 = mid ∧ st.regs 4 = hi ∧
      st.regs 5 = i ∧ st.regs 6 = j ∧ st.regs 7 = k ∧ st.regs 8 = hi - lo ∧
      ListAt st.mem scratch acc ∧
      ∀ addr, addr < scratch ∨ scratch + (hi - lo) ≤ addr → st.mem addr = mem addr
  let condM : Expr := .bin .lt (.reg 7) (.reg 8)
  let bodyM : Stmt :=
    .cond (.bin .lt (.reg 5) (.reg 3))
      (.cond (.bin .lt (.reg 6) (.reg 4))
        (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
         .cond (.bin .lt (.reg 10) (.reg 9))
           (.store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
            .assign 6 (.bin .add (.reg 6) (.const 1)))
           (.store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
            .assign 5 (.bin .add (.reg 5) (.const 1))))
        (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
         .store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
         .assign 5 (.bin .add (.reg 5) (.const 1))))
      (.assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
       .store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
       .assign 6 (.bin .add (.reg 6) (.const 1))) ;;
    .assign 7 (.bin .add (.reg 7) (.const 1))
  let mM : State → ℕ := fun st => (hi - lo) - st.regs 7
  let remM : State → ℕ := fun st => 45 * ((hi - lo) - st.regs 7) + 10
  let condValM : State → ℕ := fun st => if st.regs 7 < hi - lo then 1 else 0
  have hLoopM : Triple w p InvM (.loop condM bodyM) (normalPost fun st =>
      st.regs 0 = a ∧ st.regs 1 = scratch ∧ st.regs 2 = lo ∧ st.regs 8 = hi - lo ∧
      ListAt st.mem scratch M ∧
      ∀ addr, addr < scratch ∨ scratch + (hi - lo) ≤ addr → st.mem addr = mem addr) remM := by
    refine Triple.loop_measure (condVal := condValM) (m := mM) (rem := remM)
      (fun st hInv => by
        rcases hInv with ⟨_, _, k, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr7, hr8, _, _⟩
        dsimp only [condM, condValM]
        by_cases hklt : k < hi - lo <;> simp [Expr.eval, BinOp.eval, hr7, hr8, hklt, h0_lt, h1_lt])
      (fun st hInv hv => by
        rcases hInv with ⟨i, j, k, acc, hli, him, hmj, hjh, hk, hacc_len, hacc_eq,
          hr0, hr1, hr2, _, _, _, _, hr7, hr8, hacc_at, hfr⟩
        dsimp only [condValM] at hv
        have hk_ge : hi - lo ≤ k := by
          rw [hr7] at hv; by_contra hc
          have hlt' : k < hi - lo := by omega
          simp [hlt'] at hv
        have hi_eq : i = mid := by omega
        have hj_eq : j = hi := by omega
        subst hi_eq hj_eq
        simp only [Nat.sub_self, List.take_zero, natMerge, List.append_nil] at hacc_eq
        subst hacc_eq
        refine ⟨⟨hr0, hr1, hr2, hr8, hacc_at, hfr⟩,
          by dsimp only [condM, Expr.size, remM]; rw [hr7]; omega⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨i, j, k, acc, hli, him, hmj, hjh, hk_eq, hacc_len, hacc_eq,
          hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hacc_at, hfr⟩
        dsimp only [condValM] at hv
        have hk_lt : k < hi - lo := by
          rw [hr7] at hv; by_contra hc; simp [hc] at hv
        have hk1_lt : k + 1 < 2 ^ w := by omega
        have hsc_k_lt : scratch + k < 2 ^ w := by omega
        have hdisj_a : ∀ idx, lo ≤ idx → idx < hi →
            a + idx < scratch ∨ scratch + (hi - lo) ≤ a + idx := fun idx hi_lo hi_hi => by omega
        refine ⟨40, ?_⟩
        intro s ω' hs_eq
        subst s
        let StepPre : State → Prop := fun stM =>
          ∃ (i' j' : ℕ) (acc' : List ℕ),
            lo ≤ i' ∧ i' ≤ mid ∧ mid ≤ j' ∧ j' ≤ hi ∧ k + 1 = (i' - lo) + (j' - mid) ∧
            acc'.length = k + 1 ∧
            acc' ++ natMerge ((L.drop i').take (mid - i')) ((L.drop j').take (hi - j')) = M ∧
            stM.regs 0 = a ∧ stM.regs 1 = scratch ∧ stM.regs 2 = lo ∧ stM.regs 3 = mid ∧ stM.regs 4 = hi ∧
            stM.regs 5 = i' ∧ stM.regs 6 = j' ∧ stM.regs 7 = k ∧ stM.regs 8 = hi - lo ∧
            ListAt stM.mem scratch acc' ∧
            ∀ addr, addr < scratch ∨ scratch + (hi - lo) ≤ addr → stM.mem addr = mem addr
        have hstep_post : ∀ stM c₁,
            Runs w p ω'
              (.cond (.bin .lt (.reg 5) (.reg 3))
                (.cond (.bin .lt (.reg 6) (.reg 4))
                  (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
                   .assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
                   .cond (.bin .lt (.reg 10) (.reg 9))
                     (.store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
                      .assign 6 (.bin .add (.reg 6) (.const 1)))
                     (.store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
                      .assign 5 (.bin .add (.reg 5) (.const 1))))
                  (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
                   .store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
                   .assign 5 (.bin .add (.reg 5) (.const 1))))
                (.assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
                 .store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
                 .assign 6 (.bin .add (.reg 6) (.const 1)))) st .normal stM c₁ →
            StepPre stM → c₁ ≤ 35 →
            ∃ o s' c, Runs w p ω' bodyM st o s' c ∧
              (match o with
                | .returned u => normalPost (fun st =>
                    st.regs 0 = a ∧ st.regs 1 = scratch ∧ st.regs 2 = lo ∧ st.regs 8 = hi - lo ∧
                    ListAt st.mem scratch M ∧
                    ∀ addr, addr < scratch ∨ scratch + (hi - lo) ≤ addr → st.mem addr = mem addr) (.returned u) s' ∧
                    condM.size + 40 + 1 ≤ remM st
                | .normal => InvM s' ∧ mM s' < mM st ∧ condM.size + 40 + remM s' + 1 ≤ remM st) ∧
              0 + c ≤ 40 := by
          intro stM c₁ hr₁ hpre hc₁
          rcases hpre with ⟨i', j', acc', hli', him', hmj', hjh', hk', ha_len', ha_eq',
            hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7', hr8', ha_at', hfr'⟩
          let stF : State := { mem := stM.mem, regs := Function.update stM.regs 7 (k + 1), pos := stM.pos }
          have hrA : Runs w p ω' (.assign 7 (.bin .add (.reg 7) (.const 1))) stM .normal stF
              ((Expr.bin .add (.reg 7) (.const 1)).size + 1) :=
            runs_assign_iff.mpr ⟨k + 1, by simp [Expr.eval, BinOp.eval, h1_lt, hr7', hk1_lt], rfl, rfl, rfl⟩
          refine ⟨.normal, stF, c₁ + ((Expr.bin .add (.reg 7) (.const 1)).size + 1) + 1,
            runs_seq_iff.mpr (Or.inr ⟨stM, c₁, _, hr₁, hrA, rfl⟩),
            ⟨⟨i', j', k + 1, acc', hli', him', hmj', hjh', hk', ha_len', ha_eq',
              by simp [stF, hr0'], by simp [stF, hr1'], by simp [stF, hr2'],
              by simp [stF, hr3'], by simp [stF, hr4'], by simp [stF, hr5'],
              by simp [stF, hr6'], by simp [stF], by simp [stF, hr8'], ha_at', hfr'⟩,
              (by dsimp only [mM, stF]; simp [hr7]; omega),
              (by dsimp only [condM, Expr.size, remM, stF]; simp [hr7]; omega)⟩,
            by dsimp only [Expr.size]; omega⟩
        suffices hmain : ∃ o stM c₁, Runs w p ω'
            (.cond (.bin .lt (.reg 5) (.reg 3))
              (.cond (.bin .lt (.reg 6) (.reg 4))
                (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
                 .assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
                 .cond (.bin .lt (.reg 10) (.reg 9))
                   (.store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
                    .assign 6 (.bin .add (.reg 6) (.const 1)))
                   (.store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
                    .assign 5 (.bin .add (.reg 5) (.const 1))))
                (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
                 .store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
                 .assign 5 (.bin .add (.reg 5) (.const 1))))
              (.assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
               .store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
               .assign 6 (.bin .add (.reg 6) (.const 1)))) st o stM c₁ ∧
            (o = .normal ∧ StepPre stM) ∧ 0 + c₁ ≤ 35 by
          rcases hmain with ⟨o, stM, c₁, hr₁, ⟨rfl, hpre⟩, hc₁⟩
          obtain ⟨o', s', c', hr', hq', hc'⟩ := hstep_post stM c₁ hr₁ hpre (by omega)
          exact ⟨o', s', c', hr', hq', by simpa using hc'⟩
        by_cases him_lt : i < mid
        · have hi_L : i < L.length := by omega
          have hai_lt : a + i < 2 ^ w := by omega
          have hxi_lt : L[i] < 2 ^ w := hLw L[i] (List.getElem_mem hi_L)
          have hxi_mem : st.mem (a + i) = L[i] := by
            rw [hfr _ (hdisj_a i hli (by omega))]; exact hLat i hi_L
          have hi1_lt : i + 1 < 2 ^ w := by omega
          refine runs_cond_le_ms (v := 1) (by simp [Expr.eval, BinOp.eval, hr3, hr5, him_lt, h1_lt]) ?_ ?_
          · intro _
            by_cases hjh_lt : j < hi
            · have hj_L : j < L.length := by omega
              have haj_lt : a + j < 2 ^ w := by omega
              have hyj_lt : L[j] < 2 ^ w := hLw L[j] (List.getElem_mem hj_L)
              have hyj_mem : st.mem (a + j) = L[j] := by
                rw [hfr _ (hdisj_a j (by omega) hjh_lt)]; exact hLat j hj_L
              have hj1_lt : j + 1 < 2 ^ w := by omega
              refine runs_cond_le_ms (v := 1) (by simp [Expr.eval, BinOp.eval, hr4, hr6, hjh_lt, h1_lt]) ?_ ?_
              · intro _
                refine runs_seq_assign_le (Expr.eval_load_of_eq (v := L[i])
                  (by simp [Expr.eval, BinOp.eval, hr0, hr5, hai_lt]) hxi_mem) ?_
                refine runs_seq_assign_le (Expr.eval_load_of_eq (v := L[j])
                  (by simp [Expr.eval, BinOp.eval, hr0, hr6, haj_lt]) hyj_mem) ?_
                have hd1 := drop_take_succ_left (L := L) him_lt (by omega)
                have hd2 := drop_take_succ_left (L := L) hjh_lt (by omega)
                by_cases hlt_yx : L[j] < L[i]
                · refine runs_cond_le_ms (v := 1) (by simp [Expr.eval, BinOp.eval, hlt_yx, h1_lt]) ?_ ?_
                  · intro _
                    refine runs_seq_store_le (v := L[j]) (x := scratch + k)
                      (by simp [Expr.eval, BinOp.eval, hr1, hr7, hsc_k_lt]) (by eval_expr) ?_
                    refine runs_assign_le (v := j + 1)
                      (by simp [Expr.eval, BinOp.eval, h1_lt, hr6, hj1_lt]) ?_
                      (by dsimp only [Expr.size]; omega)
                    refine ⟨rfl, i, j + 1, acc ++ [L[j]], hli, him, by omega, by omega, by omega,
                      by simp [hacc_len], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · rw [← hacc_eq, hd1, hd2]; simp [natMerge, hlt_yx, List.append_assoc]
                    · simp [hr0]
                    · simp [hr1]
                    · simp [hr2]
                    · simp [hr3]
                    · simp [hr4]
                    · simp [hr5]
                    · simp
                    · simp [hr7]
                    · simp [hr8]
                    · intro r hr
                      simp only [List.length_append, List.length_cons, List.length_nil] at hr
                      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : r < acc.length + 1)) with hr0' | heqr
                      · rw [List.getElem_append_left hr0']
                        dsimp only
                        rw [Function.update_of_ne (by omega)]
                        exact hacc_at r hr0'
                      · simp [heqr, List.getElem_append_right, hacc_len]
                    · intro addr hout
                      dsimp only
                      rw [Function.update_of_ne (by omega)]
                      exact hfr addr hout
                  · intro hc; cases hc
                · refine runs_cond_le_ms (v := 0) (by simp [Expr.eval, BinOp.eval, hlt_yx, h0_lt]) ?_ ?_
                  · intro hc; exact absurd rfl hc
                  · intro _
                    refine runs_seq_store_le (v := L[i]) (x := scratch + k)
                      (by simp [Expr.eval, BinOp.eval, hr1, hr7, hsc_k_lt]) (by eval_expr) ?_
                    refine runs_assign_le (v := i + 1)
                      (by simp [Expr.eval, BinOp.eval, h1_lt, hr5, hi1_lt]) ?_
                      (by dsimp only [Expr.size]; omega)
                    refine ⟨rfl, i + 1, j, acc ++ [L[i]], by omega, by omega, hmj, hjh, by omega,
                      by simp [hacc_len], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · rw [← hacc_eq, hd1, hd2]; simp [natMerge, hlt_yx, List.append_assoc]
                    · simp [hr0]
                    · simp [hr1]
                    · simp [hr2]
                    · simp [hr3]
                    · simp [hr4]
                    · simp
                    · simp [hr6]
                    · simp [hr7]
                    · simp [hr8]
                    · intro r hr
                      simp only [List.length_append, List.length_cons, List.length_nil] at hr
                      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : r < acc.length + 1)) with hr0' | heqr
                      · rw [List.getElem_append_left hr0']
                        dsimp only
                        rw [Function.update_of_ne (by omega)]
                        exact hacc_at r hr0'
                      · simp [heqr, List.getElem_append_right, hacc_len]
                    · intro addr hout
                      dsimp only
                      rw [Function.update_of_ne (by omega)]
                      exact hfr addr hout
              · intro hc; cases hc
            · have hj_eq : j = hi := by omega
              refine runs_cond_le_ms (v := 0) (by simp [Expr.eval, BinOp.eval, hr4, hr6, hjh_lt, h0_lt]) ?_ ?_
              · intro hc; exact absurd rfl hc
              · intro _
                refine runs_seq_assign_le (Expr.eval_load_of_eq (v := L[i])
                  (by simp [Expr.eval, BinOp.eval, hr0, hr5, hai_lt]) hxi_mem) ?_
                refine runs_seq_store_le (v := L[i]) (x := scratch + k)
                  (by simp [Expr.eval, BinOp.eval, hr1, hr7, hsc_k_lt]) (by eval_expr) ?_
                refine runs_assign_le (v := i + 1)
                  (by simp [Expr.eval, BinOp.eval, h1_lt, hr5, hi1_lt]) ?_
                  (by dsimp only [Expr.size]; omega)
                refine ⟨rfl, i + 1, j, acc ++ [L[i]], by omega, by omega, hmj, hjh, by omega,
                  by simp [hacc_len], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · have hd1 := drop_take_succ_left (L := L) him_lt (by omega)
                  have hd2 := drop_take_nil_of_le (L := L) (a := j) (b := hi) (by omega)
                  rw [← hacc_eq, hd1, hd2]
                  simp only [natMerge_nil_right, List.append_assoc, List.singleton_append]
                · simp [hr0]
                · simp [hr1]
                · simp [hr2]
                · simp [hr3]
                · simp [hr4]
                · simp
                · simp [hr6]
                · simp [hr7]
                · simp [hr8]
                · intro r hr
                  simp only [List.length_append, List.length_cons, List.length_nil] at hr
                  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : r < acc.length + 1)) with hr0' | heqr
                  · rw [List.getElem_append_left hr0']
                    dsimp only
                    rw [Function.update_of_ne (by omega)]
                    exact hacc_at r hr0'
                  · simp [heqr, List.getElem_append_right, hacc_len]
                · intro addr hout
                  dsimp only
                  rw [Function.update_of_ne (by omega)]
                  exact hfr addr hout
          · intro hc; cases hc
        · have hjh_lt : j < hi := by omega
          have hj_L : j < L.length := by omega
          have haj_lt : a + j < 2 ^ w := by omega
          have hyj_lt : L[j] < 2 ^ w := hLw L[j] (List.getElem_mem hj_L)
          have hyj_mem : st.mem (a + j) = L[j] := by
            rw [hfr _ (hdisj_a j (by omega) hjh_lt)]; exact hLat j hj_L
          have hj1_lt : j + 1 < 2 ^ w := by omega
          refine runs_cond_le_ms (v := 0) (by simp [Expr.eval, BinOp.eval, hr3, hr5, him_lt, h0_lt]) ?_ ?_
          · intro hc; exact absurd rfl hc
          · intro _
            refine runs_seq_assign_le (Expr.eval_load_of_eq (v := L[j])
              (by simp [Expr.eval, BinOp.eval, hr0, hr6, haj_lt]) hyj_mem) ?_
            refine runs_seq_store_le (v := L[j]) (x := scratch + k)
              (by simp [Expr.eval, BinOp.eval, hr1, hr7, hsc_k_lt]) (by eval_expr) ?_
            refine runs_assign_le (v := j + 1)
              (by simp [Expr.eval, BinOp.eval, h1_lt, hr6, hj1_lt]) ?_
              (by dsimp only [Expr.size]; omega)
            refine ⟨rfl, i, j + 1, acc ++ [L[j]], hli, him, by omega, by omega, by omega,
              by simp [hacc_len], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have hd1 := drop_take_nil_of_le (L := L) (a := i) (b := mid) (by omega)
              have hd2 := drop_take_succ_left (L := L) hjh_lt (by omega)
              rw [← hacc_eq, hd1, hd2]; simp [natMerge, List.append_assoc]
            · simp [hr0]
            · simp [hr1]
            · simp [hr2]
            · simp [hr3]
            · simp [hr4]
            · simp [hr5]
            · simp
            · simp [hr7]
            · simp [hr8]
            · intro r hr
              simp only [List.length_append, List.length_cons, List.length_nil] at hr
              rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : r < acc.length + 1)) with hr0' | heqr
              · rw [List.getElem_append_left hr0']
                dsimp only
                rw [Function.update_of_ne (by omega)]
                exact hacc_at r hr0'
              · simp [heqr, List.getElem_append_right, hacc_len]
            · intro addr hout
              dsimp only
              rw [Function.update_of_ne (by omega)]
              exact hfr addr hout)
  refine runs_seq_triple_le hLoopM
    ⟨lo, mid, 0, [], le_refl _, hlomid, le_refl _, hmidhi, by simp, rfl,
      (by simp [M, L₁, L₂]), (by simp [startState]), (by simp [startState]), (by simp [startState]),
      (by simp [startState]), (by simp [startState]), (by simp [startState]), (by simp [startState]),
      (by simp), (by simp), (fun _ hi => absurd hi (Nat.not_lt_zero _)), fun _ _ => rfl⟩ ?_
  intro stM ⟨hr0M, hr1M, hr2M, hr8M, hMat, hfrM⟩
  let L' := L.take lo ++ M ++ L.drop hi
  have hL'_len : L'.length = L.length := by
    dsimp only [L']
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, hM_len]; omega
  let InvC : ℕ → State → Prop := fun c st =>
    c ≤ hi - lo ∧
    st.regs 0 = a ∧ st.regs 1 = scratch ∧ st.regs 2 = lo ∧ st.regs 8 = hi - lo ∧ st.regs 9 = c ∧
    (∀ idx < lo, st.mem (a + idx) = L[idx]!) ∧
    (∀ idx, hi ≤ idx → idx < L.length → st.mem (a + idx) = L[idx]!) ∧
    (∀ r < c, st.mem (a + lo + r) = M[r]!) ∧
    ListAt st.mem scratch M ∧
    ∀ addr, addr < a + lo ∨ a + hi ≤ addr →
      (addr < scratch ∨ scratch + (hi - lo) ≤ addr → st.mem addr = mem addr)
  let bodyC : Stmt :=
    .assign 10 (.load (.bin .add (.reg 1) (.reg 9))) ;;
    .store (.bin .add (.bin .add (.reg 0) (.reg 2)) (.reg 9)) (.reg 10)
  let PC0 : State → Prop := fun st =>
    st.regs 0 = a ∧ st.regs 1 = scratch ∧ st.regs 2 = lo ∧ st.regs 8 = hi - lo ∧
    (∀ idx < lo, st.mem (a + idx) = L[idx]!) ∧
    (∀ idx, hi ≤ idx → idx < L.length → st.mem (a + idx) = L[idx]!) ∧
    ListAt st.mem scratch M ∧
    ∀ addr, addr < a + lo ∨ a + hi ≤ addr →
      (addr < scratch ∨ scratch + (hi - lo) ≤ addr → st.mem addr = mem addr)
  have hLoopC : Triple w p PC0 (forRange 9 (.const 0) (.reg 8) bodyC)
      (normalPost (InvC (hi - lo)))
      (fun _ => (hi - lo - 0) * (15 + Expr.size (.reg 8) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 8) + 5)) := by
    refine Triple.forRange_const 15 0 (hi - lo) (Nat.zero_le _) h1_lt (fun _ => hlt_len)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h8, hl, hg, hMat', hfr'⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, hl, hg,
            fun _ hr => absurd hr (Nat.not_lt_zero _), hMat', hfr'⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h8]
        · simp)
      (fun c st _ _ hk => hk.2.2.2.2.2.1)
      (fun c st _ _ hk => by
        rcases hk with ⟨_, _, _, _, hr8, _, _, _, _, _, _⟩
        simp [Expr.eval, hr8])
      (fun c _ hc_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr8, hr9, hl, hg, hc_at, hMat', hfr'⟩
        have hsc_c : scratch + c < 2 ^ w := by omega
        have halo_lt : a + lo < 2 ^ w := by omega
        have haloc_lt : a + lo + c < 2 ^ w := by omega
        have hMc_mem : st.mem (scratch + c) = M[c]'(hM_len.symm ▸ hc_lt) :=
          hMat' c (hM_len.symm ▸ hc_lt)
        have hMc_lt : M[c]'(hM_len.symm ▸ hc_lt) < 2 ^ w := by
          have hmemM := List.getElem_mem (hM_len.symm ▸ hc_lt)
          have hp := (natMerge_perm L₁ L₂).mem_iff.mp hmemM
          rw [List.mem_append] at hp
          rcases hp with h1m | h2m
          · exact hLw _ (List.mem_of_mem_drop (List.mem_of_mem_take h1m))
          · exact hLw _ (List.mem_of_mem_drop (List.mem_of_mem_take h2m))
        suffices h : ∃ o st₁ c', Runs w p ω' bodyC st o st₁ c' ∧
            (normalPost fun st₁ =>
              InvC (c + 1) { mem := st₁.mem, regs := Function.update st₁.regs 9 (c + 1), pos := st₁.pos } ∧
                st₁.regs 9 = c) o st₁ ∧
            0 + c' ≤ 15 by
          rcases h with ⟨o, st₁, c', hr, hq, hc⟩
          exact ⟨o, st₁, c', hr, hq, by simpa using hc⟩
        dsimp only [bodyC]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := M[c]'(hM_len.symm ▸ hc_lt))
          (by simp [Expr.eval, BinOp.eval, hr1, hr9, hsc_c]) hMc_mem) ?_
        refine runs_store_le (v := M[c]'(hM_len.symm ▸ hc_lt)) (x := a + lo + c)
          (by simp [Expr.eval, BinOp.eval, hr0, hr2, hr9, halo_lt, haloc_lt]) (by eval_expr) ?_
          (by dsimp only [Expr.size]; omega)
        refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [hr0]
        · simp [hr1]
        · simp [hr2]
        · simp [hr8]
        · simp
        · intro idx hidx
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hl idx hidx
        · intro idx hge hlt
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hg idx hge hlt
        · intro r hr
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hr0' | heqr
          · dsimp only; rw [Function.update_of_ne (by omega)]; exact hc_at r hr0'
          · simp only [heqr]
            rw [Function.update_self, getElem!_pos M c (hM_len.symm ▸ hc_lt)]
        · intro i hi'
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hMat' i hi'
        · intro addr hout1 hout2
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr' addr hout1 hout2
        · simp [hr9])
  refine runs_seq_triple_le hLoopC ⟨hr0M, hr1M, hr2M, hr8M,
    (fun idx hidx => by
      rw [hfrM _ (by rcases hdisj with hd | hd <;> [left; right] <;> omega), getElem!_pos L idx (by omega)]
      exact hLat idx (by omega)),
    (fun idx hge hlt => by
      rw [hfrM _ (by rcases hdisj with hd | hd <;> [left; right] <;> omega), getElem!_pos L idx hlt]
      exact hLat idx hlt),
    hMat, fun addr hout1 hout2 => hfrM addr hout2⟩ ?_
  intro stC ⟨_, _, _, _, _, _, hlC, hgC, hcC, _, hfrC⟩
  have hLat' : ListAt stC.mem a L' := by
    intro idx hidx
    rw [hL'_len] at hidx
    by_cases hlt_lo' : idx < lo
    · have h1 := (list_slice_replace_getElem? (L := L) (M := M) (by omega) hhiL hM_len).1 idx hlt_lo'
      have heq : L'[idx] = L[idx] := by
        have := List.getElem?_eq_getElem (by rw [hL'_len]; exact hidx)
        rw [h1, List.getElem?_eq_getElem hidx] at this
        exact (Option.some.inj this).symm
      rw [heq]; simpa [getElem!_pos L idx hidx] using hlC idx hlt_lo'
    · by_cases hge_hi' : hi ≤ idx
      · have h1 := (list_slice_replace_getElem? (L := L) (M := M) (by omega) hhiL hM_len).2.1 idx hge_hi'
        have heq : L'[idx] = L[idx] := by
          have := List.getElem?_eq_getElem (by rw [hL'_len]; exact hidx)
          rw [h1, List.getElem?_eq_getElem hidx] at this
          exact (Option.some.inj this).symm
        rw [heq]; simpa [getElem!_pos L idx hidx] using hgC idx hge_hi' hidx
      · have hr : idx - lo < hi - lo := by omega
        have heq := list_slice_replace_getElem_mem (L := L) (M := M) (lo := lo) (hi := hi) (r := idx - lo)
          (by omega) hhiL hM_len hr
        have heq' : L'[idx]'(by rw [hL'_len]; exact hidx) = M[idx - lo]'(hM_len.symm ▸ hr) := by
          dsimp only [L']
          convert heq using 2
          omega
        rw [heq']
        have hcm := hcC (idx - lo) hr
        rw [show a + lo + (idx - lo) = a + idx by omega, getElem!_pos M (idx - lo) (hM_len.symm ▸ hr)] at hcm
        exact hcm
  have hslice := list_slice_replace_getElem? (L := L) (M := M) (by omega) hhiL hM_len
  refine runs_ret_le (by eval_expr)
    ⟨a, scratch, L', rfl, rfl, hL'_len, hslice.1, hslice.2.1, hslice.2.2, hLat', hfrC⟩ ?_
  dsimp only [mergePairContract, remM, Expr.size]
  simp only [Function.update_self, Function.update_of_ne (by decide : (7 : ℕ) ≠ 8)]
  omega

/-! ## Iterative bottom-up merge sort (`mergeSort_meetsContract`) -/

end

end MinCostFlow.DynSpanner.Program
