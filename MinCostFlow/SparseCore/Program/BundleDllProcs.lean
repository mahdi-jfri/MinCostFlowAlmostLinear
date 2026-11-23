module

public import MinCostFlow.SparseCore.Program.BundleBaseProcs

import WordRAM.Tactic

/-!
# Doubly-linked list procedures for the bundle manager (`BundleDllProcs`)

Verifies `bundleDllPush_meetsContract` (`≤ 45` steps) and `bundleDllErase_meetsContract`
(`≤ 65` steps) for the 1-indexed `IsDoublyLinkedList` procedures defined in `BundleBaseProcs.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

public section

/-- Verification of `bundleDllPushStmt`. -/
theorem bundleDllPush_meetsContract {w prevBase nextBase headAddr cap key : ℕ} {L : List ℕ}
    {p : Program} {b : ℕ} (hp : p.HasAt b [bundleDllPushStmt]) :
    MeetsContract w p b (bundleDllPushContract w prevBase nextBase headAddr cap key L) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨rfl, hw16, hpCap, hnCap, hdisjPN, hdisjHP, hdisjHN, hkeyLt, hkeyNot, hdll⟩
  have hhd_lt : headAddr < 2 ^ w := hargs headAddr (by simp)
  cases L with
  | nil =>
    have hold0 : mem headAddr = 0 := hdll.2.2.1
    refine runs_start_le ?_
    dsimp only [bundleDllPushStmt, startState]
    wram_step; simp only [hold0]
    wram_run
    · dsimp only [bundleDllPushContract, Outcome.value]
      refine ⟨rfl, ?_, ?_⟩
      · refine hdll.cons hkeyLt hkeyNot (by simp)
          (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self])
          (by rw [Function.update_of_ne (by omega), Function.update_self]; exact hold0.symm)
          (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      · intro a ha1 ha2 ha3 _
        rw [Function.update_of_ne ha1, Function.update_of_ne ha3, Function.update_of_ne ha2]
    · dsimp only [bundleDllPushContract]; wram_cost
  | cons x xs =>
    have holdx : mem headAddr = x + 1 := hdll.2.2.1
    have hx_lt : x < cap := hdll.2.1 x List.mem_cons_self
    have hkx : key ≠ x := fun h => hkeyNot (h ▸ List.mem_cons_self)
    have hsub1 : x + 1 - 1 = x := by omega
    refine runs_start_le ?_
    dsimp only [bundleDllPushStmt, startState]
    wram_step; simp only [holdx]
    wram_step
    wram_step
    wram_step
    wram_step; simp only [hsub1]
    wram_run
    · dsimp only [bundleDllPushContract, Outcome.value]
      refine ⟨rfl, ?_, ?_⟩
      · refine hdll.cons hkeyLt hkeyNot (by simp)
          (by simp (disch := omega) only [Function.update_of_ne]; exact Function.update_self _ _ _)
          (by simp (disch := omega) only [Function.update_of_ne]
              rw [Function.update_self]; exact holdx.symm)
          (fun h₀ ys heq => by
            have h0x : h₀ = x := (List.cons.inj heq).1.symm
            subst h0x
            rw [Function.update_of_ne (by omega), Function.update_self])
          (fun y hy hne => by
            have hyx : y ≠ x := fun h => hne xs (h ▸ rfl)
            have hyk : y ≠ key := fun h => hkeyNot (h ▸ hy)
            have hyl : y < cap := hdll.2.1 y hy
            simp (disch := omega) only [Function.update_of_ne])
          (fun y hy => by
            have hyk : y ≠ key := fun h => hkeyNot (h ▸ hy)
            have hyl : y < cap := hdll.2.1 y hy
            simp (disch := omega) only [Function.update_of_ne])
      · intro a ha1 ha2 ha3 ha4
        have hax : a ≠ prevBase + x := ha4 x xs rfl
        rw [Function.update_of_ne ha1, Function.update_of_ne hax,
          Function.update_of_ne ha3, Function.update_of_ne ha2]
    · dsimp only [bundleDllPushContract]; wram_cost

/-- Verification of `bundleDllEraseStmt`. -/
theorem bundleDllErase_meetsContract {w prevBase nextBase headAddr cap key : ℕ} {L : List ℕ}
    {p : Program} {b : ℕ} (hp : p.HasAt b [bundleDllEraseStmt]) :
    MeetsContract w p b (bundleDllEraseContract w prevBase nextBase headAddr cap key L) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨rfl, hw16, hpCap, hnCap, hdisjPN, hdisjHP, hdisjHN, hkeyMem, hdll⟩
  have hhd_lt : headAddr < 2 ^ w := hargs headAddr (by simp)
  have hkeyLt : key < cap := hdll.2.1 key hkeyMem
  obtain ⟨idx, hidx, hLidx⟩ := List.getElem_of_mem hkeyMem
  have hbody := hdll.2.2.2 idx hidx
  rw [hLidx] at hbody
  set pr := mem (prevBase + key)
  set nx := mem (nextBase + key)
  have hpr_eq : pr = if idx = 0 then 0 else L[idx - 1]'(by omega) + 1 := hbody.1
  have hnx_eq : nx = if idx + 1 = L.length then 0 else L.getD (idx + 1) 0 + 1 := hbody.2
  have hpr_le : pr ≤ cap := by
    rw [hpr_eq]; split_ifs
    · exact Nat.zero_le _
    · have := hdll.2.1 (L[idx - 1]'(by omega)) (List.getElem_mem (by omega)); omega
  have hnx_le : nx ≤ cap := by
    rw [hnx_eq]; split_ifs
    · exact Nat.zero_le _
    · have hi1 : idx + 1 < L.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      have := hdll.2.1 L[idx + 1] (List.getElem_mem hi1); omega
  have hidxOf : L.idxOf key = idx := by rw [← hLidx]; exact hdll.1.idxOf_getElem idx hidx
  have hpr_def : mem (prevBase + key) = pr := rfl
  have hnx_def : mem (nextBase + key) = nx := rfl
  -- Prove the postcondition abstractly for the resulting 4-step updated memory `m4`
  let m1 := if pr = 0 then Function.update mem headAddr nx
            else Function.update mem (nextBase + (pr - 1)) nx
  let m2 := if nx = 0 then m1 else Function.update m1 (prevBase + (nx - 1)) pr
  let m3 := Function.update m2 (prevBase + key) 0
  let m4 := Function.update m3 (nextBase + key) 0
  have hpost_m4 : (bundleDllEraseContract w prevBase nextBase headAddr cap key L).post
      [prevBase, nextBase, headAddr, key] mem 0 m4 := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · refine hdll.erase hkeyMem ?_ ?_ ?_ ?_ ?_ ?_
      · intro _ _
        change m4 headAddr = if pr = 0 then nx else mem headAddr
        simp only [m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        by_cases hnx0 : nx = 0
        · simp only [hnx0, ↓reduceIte]
          by_cases hpr0 : pr = 0
          · simp only [hpr0, ↓reduceIte, Function.update_self]
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (show headAddr ≠ nextBase + (pr - 1) by omega)]
        · simp only [hnx0, ↓reduceIte, Function.update_of_ne (show headAddr ≠ prevBase + (nx - 1) by omega)]
          by_cases hpr0 : pr = 0
          · simp only [hpr0, ↓reduceIte, Function.update_self]
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (show headAddr ≠ nextBase + (pr - 1) by omega)]
      · intro hem
        have hlen1 : L.length = 1 := by
          have := List.length_erase_of_mem hkeyMem
          rw [hem] at this; simp at this; omega
        have hidx0 : idx = 0 := by omega
        have hpr0 : pr = 0 := by simp [hpr_eq, hidx0]
        have hnx0 : nx = 0 := by simp [hnx_eq, hidx0, hlen1]
        simp only [m4, m3, m2, m1, hpr0, hnx0, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      · intro y hy hyne
        have hyL : y ∈ L := List.mem_of_mem_erase hy
        have hyl : y < cap := hdll.2.1 y hyL
        have hyk : y ≠ key := fun h => hdll.1.mem_erase_iff.mp (h ▸ hy) |>.1 rfl
        simp only [m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        have hne_nx : nx ≠ 0 → prevBase + y ≠ prevBase + (nx - 1) := by
          intro hnx0
          have hi1 : idx + 1 < L.length := by
            by_contra hc'; have he : idx + 1 = L.length := by omega
            rw [he] at hnx_eq; exact hnx0 (by simpa using hnx_eq)
          have hnxv : nx - 1 = L[idx + 1] := by
            rw [hnx_eq, ite_eq_right (show idx + 1 ≠ L.length by omega),
              List.getD_eq_getElem _ _ hi1, Nat.add_sub_cancel]
          rw [hnxv]
          rw [hidxOf, dite_eq_left hi1] at hyne
          omega
        by_cases hnx0 : nx = 0
        · simp only [hnx0, ↓reduceIte]
          by_cases hpr0 : pr = 0
          · simp [hpr0, show prevBase + y ≠ headAddr by omega]
          · simp [hpr0, show prevBase + y ≠ nextBase + (pr - 1) by omega]
        · simp only [hnx0, ↓reduceIte, Function.update_of_ne (hne_nx hnx0)]
          by_cases hpr0 : pr = 0
          · simp [hpr0, show prevBase + y ≠ headAddr by omega]
          · simp [hpr0, show prevBase + y ≠ nextBase + (pr - 1) by omega]
      · intro k hk hLk
        have hkeq : k = idx := hdll.1.getElem_inj_iff.mp (hLk.trans hLidx.symm)
        subst hkeq
        have hnxv : nx = L[k + 1] + 1 := by
          rw [hnx_eq, ite_eq_right (show k + 1 ≠ L.length by omega), List.getD_eq_getElem _ _ hk]
        have hnx0 : nx ≠ 0 := by omega
        have hne1 : L[k + 1] ≠ key := by
          intro heq; have : L[k + 1] = L[k] := heq.trans hLidx.symm
          have := hdll.1.getElem_inj_iff.mp this; omega
        have hl1 : L[k + 1] < cap := hdll.2.1 _ (List.getElem_mem hk)
        simp only [m4, m3, m2, hnx0, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          show nx - 1 = L[k + 1] by omega, Function.update_self]
      · intro y hy hyne
        have hyL : y ∈ L := List.mem_of_mem_erase hy
        have hyl : y < cap := hdll.2.1 y hyL
        have hyk : y ≠ key := fun h => hdll.1.mem_erase_iff.mp (h ▸ hy) |>.1 rfl
        have hne_pr : pr ≠ 0 → nextBase + y ≠ nextBase + (pr - 1) := by
          intro hpr0
          have hidx0 : idx ≠ 0 := by
            intro h0; exact hpr0 (by simpa [h0] using hpr_eq)
          have hprv : pr - 1 = L[idx - 1]'(by omega) := by
            rw [hpr_eq, ite_eq_right hidx0, Nat.add_sub_cancel]
          have hypr : y ≠ pr - 1 := by
            rw [hprv]
            dsimp only at hyne
            rw [hidxOf, ite_eq_right hidx0] at hyne
            rwa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at hyne
          omega
        simp only [m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        by_cases hnx0 : nx = 0
        · simp only [hnx0, ↓reduceIte]
          by_cases hpr0 : pr = 0
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (show nextBase + y ≠ headAddr by omega)]
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (hne_pr hpr0)]
        · simp only [hnx0, ↓reduceIte, Function.update_of_ne (show nextBase + y ≠ prevBase + (nx - 1) by omega)]
          by_cases hpr0 : pr = 0
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (show nextBase + y ≠ headAddr by omega)]
          · simp only [hpr0, ↓reduceIte, Function.update_of_ne (hne_pr hpr0)]
      · intro k hk hkpos hLk
        have hkeq : k = idx := hdll.1.getElem_inj_iff.mp (hLk.trans hLidx.symm)
        subst hkeq
        have hprv : pr = L[k - 1]'(by omega) + 1 := by
          rw [hpr_eq, ite_eq_right (by omega)]
        have hpr0 : pr ≠ 0 := by omega
        have hne1 : L[k - 1]'(by omega) ≠ key := by
          intro heq; have : L[k - 1]'(by omega) = L[k] := heq.trans hLidx.symm
          have := hdll.1.getElem_inj_iff.mp this; omega
        have hl1 : L[k - 1]'(by omega) < cap := hdll.2.1 _ (List.getElem_mem (by omega))
        simp only [m4, m3, m2, m1, hpr0, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        by_cases hnx0 : nx = 0
        · simp only [hnx0, ↓reduceIte, show pr - 1 = L[k - 1]'(by omega) by omega,
            Function.update_self]
          exact hnx0.symm
        · simp only [hnx0, ↓reduceIte,
            Function.update_of_ne (show nextBase + L[k - 1]'(by omega) ≠ prevBase + (nx - 1) by omega),
            show pr - 1 = L[k - 1]'(by omega) by omega, Function.update_self]
          rfl
    · simp only [m4, m3]; rw [Function.update_of_ne (by omega), Function.update_self]
    · simp [m4]
    · intro a haH haL
      have haKey := haL key hkeyMem
      simp only [m4, m3, m2, m1]
      rw [Function.update_of_ne haKey.2, Function.update_of_ne haKey.1]
      have hne_pr : pr ≠ 0 → a ≠ nextBase + (pr - 1) := by
        intro hpr0
        have hidx0 : idx ≠ 0 := fun h0 => hpr0 (by simpa [h0] using hpr_eq)
        have hprv : pr - 1 = L[idx - 1]'(by omega) := by
          rw [hpr_eq, ite_eq_right hidx0, Nat.add_sub_cancel]
        rw [hprv]; exact (haL _ (List.getElem_mem (by omega))).2
      have hne_nx : nx ≠ 0 → a ≠ prevBase + (nx - 1) := by
        intro hnx0
        have hi1 : idx + 1 < L.length := by
          by_contra hc'; have he : idx + 1 = L.length := by omega
          rw [he] at hnx_eq; exact hnx0 (by simpa using hnx_eq)
        have hnxv : nx - 1 = L[idx + 1] := by
          rw [hnx_eq, ite_eq_right (show idx + 1 ≠ L.length by omega),
            List.getD_eq_getElem _ _ hi1, Nat.add_sub_cancel]
        rw [hnxv]; exact (haL _ (List.getElem_mem hi1)).1
      by_cases hnx0 : nx = 0
      · simp only [hnx0, ↓reduceIte]
        by_cases hpr0 : pr = 0
        · simp [hpr0, haH]
        · simp [hpr0, hne_pr hpr0]
      · simp only [hnx0, ↓reduceIte, Function.update_of_ne (hne_nx hnx0)]
        by_cases hpr0 : pr = 0
        · simp [hpr0, haH]
        · simp [hpr0, hne_pr hpr0]
  -- Now symbolically execute `bundleDllEraseStmt` via `wram_run`
  refine runs_start_le ?_
  dsimp only [bundleDllEraseStmt, startState]
  wram_step; simp only [hpr_def]
  wram_step; simp only [hnx_def]
  by_cases hpr0 : pr = 0 <;> by_cases hnx0 : nx = 0
  · wram_run
    · simpa [m4, m3, m2, m1, hpr0, hnx0, Outcome.value] using hpost_m4
    · dsimp only [bundleDllEraseContract]; wram_cost
  · wram_run
    · simpa [m4, m3, m2, m1, hpr0, hnx0, Outcome.value] using hpost_m4
    · dsimp only [bundleDllEraseContract]; wram_cost
  · wram_run
    · simpa [m4, m3, m2, m1, hpr0, hnx0, Outcome.value] using hpost_m4
    · dsimp only [bundleDllEraseContract]; wram_cost
  · wram_run
    · simpa [m4, m3, m2, m1, hpr0, hnx0, Outcome.value] using hpost_m4
    · dsimp only [bundleDllEraseContract]; wram_cost

end

end MinCostFlow.SparseCore.Program
