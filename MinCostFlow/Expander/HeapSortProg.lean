module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import WordRAM.Entry
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.GraphCompression

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# In-Place Heapsort Procedure (Word-RAM)

Deterministic `NoRand` Word-RAM implementation of `siftDownProc` (`O(log(end_ + 1) + 1)`) and
`heapSortProc` (`O(n * (log(n + 2) + 1) + 1)`), sorting `mem[base .. base + n - 1]` in-place.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Spanner

lemma runs_cond_true_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {s t : Stmt} {st st' : State} {o : Outcome} {v c₁ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (hr : Runs w p ω s st o st' c₁) :
    Runs w p ω (.cond e s t) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr, rfl⟩

lemma runs_cond_false_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {s t : Stmt} {st st' : State} {o : Outcome} {c₁ : ℕ}
    (he : e.eval w st = some 0) (hr : Runs w p ω t st o st' c₁) :
    Runs w p ω (.cond e s t) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨0, c₁, he, by simpa using hr, rfl⟩

lemma runs_nop_self {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    Runs w p ω .nop st .normal st 1 :=
  runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩

/-- `siftDownProc`: `args = [base, start, end_]`, restores max-heap on `base[start .. end_)`. -/
def siftDownProc : Stmt :=
  .seq (.assign 3 (.reg 1)) -- root := start
  (.seq (.assign 4 (.const 1)) -- flag := 1
  (.seq (.loop (.reg 4)
    (.seq (.assign 5 (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1))) -- child := 2*root + 1
    (.cond (.bin .lt (.reg 5) (.reg 2))
      (.seq (.assign 8 (.bin .add (.reg 5) (.const 1))) -- child2 := child + 1
      (.seq (.cond (.bin .lt (.reg 8) (.reg 2))
        (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
        (.seq (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))))
        (.cond (.bin .lt (.reg 7) (.reg 9))
          (.assign 5 (.reg 8))
          .nop)))
        .nop)
      (.seq (.assign 6 (.load (.bin .add (.reg 0) (.reg 3))))
      (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
      (.cond (.bin .lt (.reg 6) (.reg 7))
        (.seq (.store (.bin .add (.reg 0) (.reg 3)) (.reg 7))
        (.seq (.store (.bin .add (.reg 0) (.reg 5)) (.reg 6))
          (.assign 3 (.reg 5))))
        (.assign 4 (.const 0)))))))
      (.assign 4 (.const 0)))))
  (.ret (.const 0))))

lemma siftDownProc_noRand : siftDownProc.NoRand := by
  simp [siftDownProc, Stmt.NoRand]

/-- Contract for `siftDownProc`: args `[base, start, end_]`. -/
def siftDownContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ base start end_, args = [base, start, end_] ∧
      start < end_ ∧
      base + end_ < 2 ^ w ∧
      2 * end_ + 2 < 2 ^ w ∧
      4 ≤ 2 ^ w ∧
      (∀ i < end_, mem (base + i) < 2 ^ w) ∧
      IsHeapRange (tab end_ fun i => mem (base + i)) (start + 1) end_
  post args mem v mem' :=
    let base := args.getD 0 0
    let start := args.getD 1 0
    let end_ := args.getD 2 0
    let xs := tab end_ fun i => mem (base + i)
    let xs' := tab end_ fun i => mem' (base + i)
    v = 0 ∧
    xs'.Perm xs ∧
    (∀ i < end_, mem' (base + i) < 2 ^ w) ∧
    IsHeapRange xs' start end_ ∧
    MemFrame mem mem' (base + start) (base + end_)
  cost args _ :=
    let end_ := args.getD 2 0
    85 * (2 * Nat.log 2 (end_ + 1) + 1) + 15

theorem siftDown_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [siftDownProc]) :
    MeetsContract w p b (siftDownContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [siftDownContract] at hpre
  rcases hpre with ⟨base, start, end_, rfl, hse, hbe, h2e, hw4, hmem_lt, hheap⟩
  have hproc : p.procs[b]? = some siftDownProc := hp 0 (by simp)
  have hlt_base : base < 2 ^ w := hwords base (by simp)
  have hlt_start : start < 2 ^ w := hwords start (by simp)
  have hlt_end : end_ < 2 ^ w := hwords end_ (by simp)
  have htriple :
      Triple w p
        (fun st => st = startState [base, start, end_] mem pos)
        siftDownProc
        (fun o st' => o = .returned 0 ∧
          (tab end_ fun i => st'.mem (base + i)).Perm (tab end_ fun i => mem (base + i)) ∧
          (∀ i < end_, st'.mem (base + i) < 2 ^ w) ∧
          IsHeapRange (tab end_ fun i => st'.mem (base + i)) start end_ ∧
          MemFrame mem st'.mem (base + start) (base + end_))
        (fun _ => 85 * (2 * Nat.log 2 (end_ + 1) + 1) + 15) := by
    wram_enter
    · subst hpre
      dsimp only [siftDownProc]
      wram_step; wram_step
      let Inv : State → Prop := fun st =>
        st.regs 0 = base ∧ st.regs 1 = start ∧ st.regs 2 = end_ ∧
        (st.regs 4 = 0 ∨ st.regs 4 = 1) ∧
        (tab end_ fun i => st.mem (base + i)).Perm (tab end_ fun i => mem (base + i)) ∧
        (∀ i < end_, st.mem (base + i) < 2 ^ w) ∧
        MemFrame mem st.mem (base + start) (base + end_) ∧
        SiftInv (tab end_ fun i => st.mem (base + i)) start end_ (st.regs 3) (st.regs 4)
      let meas : State → ℕ := fun st =>
        if st.regs 4 = 0 then 0 else 2 * (Nat.log 2 end_ - Nat.log 2 (st.regs 3 + 1)) + 1
      have hloop : Triple w p Inv
          (.loop (.reg 4)
            (.seq (.assign 5 (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)))
            (.cond (.bin .lt (.reg 5) (.reg 2))
              (.seq (.assign 8 (.bin .add (.reg 5) (.const 1)))
              (.seq (.cond (.bin .lt (.reg 8) (.reg 2))
                (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
                (.seq (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))))
                (.cond (.bin .lt (.reg 7) (.reg 9))
                  (.assign 5 (.reg 8))
                  .nop)))
                .nop)
              (.seq (.assign 6 (.load (.bin .add (.reg 0) (.reg 3))))
              (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
              (.cond (.bin .lt (.reg 6) (.reg 7))
                (.seq (.store (.bin .add (.reg 0) (.reg 3)) (.reg 7))
                (.seq (.store (.bin .add (.reg 0) (.reg 5)) (.reg 6))
                  (.assign 3 (.reg 5))))
                (.assign 4 (.const 0)))))))
              (.assign 4 (.const 0)))))
          (normalPost fun st' => Inv st' ∧ st'.regs 4 = 0)
          (fun st => (1 + 80 + 1) * meas st + 1 + 1) := by
        refine Triple.loop_const_normal meas (fun st => st.regs 4) 80
          (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
          (fun st hInv hfl0 => ⟨hInv, hfl0⟩)
          (fun st hInv hfl_ne => ?_)
        rcases hInv with ⟨hr0, hr1, hr2, hfl, hperm, hlt_m, hframe, hsinv⟩
        have hfl1 : st.regs 4 = 1 := by omega
        have hroot_lt : st.regs 3 < end_ := hsinv.2.1
        have hroot_start : start ≤ st.regs 3 := hsinv.1
        have hlog_root : Nat.log 2 (st.regs 3 + 1) ≤ Nat.log 2 end_ :=
          Nat.log_mono_right (by omega)
        wram_enter
        · subst hpre
          wram_step
          wram_step
          · -- 2 * root + 1 < end_
            have hc1_lt : 2 * st.regs 3 + 1 < end_ := by rw [← hr2]; exact hcond
            wram_step
            let bodyTail : Stmt :=
              (.seq (.assign 6 (.load (.bin .add (.reg 0) (.reg 3))))
              (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
              (.cond (.bin .lt (.reg 6) (.reg 7))
                (.seq (.store (.bin .add (.reg 0) (.reg 3)) (.reg 7))
                (.seq (.store (.bin .add (.reg 0) (.reg 5)) (.reg 6))
                  (.assign 3 (.reg 5))))
                (.assign 4 (.const 0)))))
            have hlt1_m : st.mem (base + (2 * st.regs 3 + 1)) < 2 ^ w := hlt_m _ hc1_lt
            have hmid :
                ∃ (o : Outcome) (stMid : State) (c1 : ℕ),
                  Runs w p ω
                    (.cond (.bin .lt (.reg 8) (.reg 2))
                      (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
                      (.seq (.assign 9 (.load (.bin .add (.reg 0) (.reg 8))))
                      (.cond (.bin .lt (.reg 7) (.reg 9))
                        (.assign 5 (.reg 8))
                        .nop)))
                      .nop)
                    { mem := st.mem,
                      regs := Function.update (Function.update st.regs 5 (2 * st.regs 3 + 1)) 8
                        (2 * st.regs 3 + 1 + 1),
                      pos := st.pos }
                    o stMid c1 ∧
                  (o = .normal ∧
                    stMid.mem = st.mem ∧
                    stMid.regs 0 = base ∧ stMid.regs 1 = start ∧ stMid.regs 2 = end_ ∧
                    stMid.regs 3 = st.regs 3 ∧ stMid.regs 4 = 1 ∧
                    (stMid.regs 5 = 2 * st.regs 3 + 1 ∨ stMid.regs 5 = 2 * st.regs 3 + 2) ∧
                    stMid.regs 5 < end_ ∧
                    ∀ c2, c2 ∈ [2 * st.regs 3 + 1, 2 * st.regs 3 + 2] → c2 < end_ →
                      (tab end_ fun i => st.mem (base + i)).getD c2 0 ≤
                        (tab end_ fun i => st.mem (base + i)).getD (stMid.regs 5) 0) ∧
                  0 + c1 ≤ 25 := by
              wram_step
              · rename_i hc2_lt
                have hc2_lt' : 2 * st.regs 3 + 2 < end_ := by rw [hr2] at hc2_lt; omega
                have hc2_lt1 : 2 * st.regs 3 + 1 + 1 < end_ := by omega
                have hlt2_m : st.mem (base + (2 * st.regs 3 + 1 + 1)) < 2 ^ w := hlt_m _ hc2_lt1
                wram_run
                · rw [hr0] at hcond
                  exact ⟨rfl, rfl, hr0, hr1, hr2, rfl, hfl1, Or.inr (by simp), by simp; omega,
                    fun c2 hc2_mem _ => by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2_mem
                      simp only [Function.update_self, tab, List.getD_eq_getElem?_getD,
                        List.getElem?_map, show 2 * st.regs 3 + 1 + 1 = 2 * st.regs 3 + 2 by omega]
                      rcases hc2_mem with rfl | rfl
                      · simp [hc1_lt, hc2_lt', show st.mem (base + (2 * st.regs 3 + 1)) ≤
                          st.mem (base + (2 * st.regs 3 + 2)) by simpa [Nat.add_assoc] using hcond.le]
                      · simp [hc2_lt']⟩
                · wram_cost
                · rw [hr0] at hcond
                  exact ⟨rfl, rfl, hr0, hr1, hr2, rfl, hfl1, Or.inl (by simp), by simp; omega,
                    fun c2 hc2_mem _ => by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2_mem
                      simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map]
                      rcases hc2_mem with rfl | rfl
                      · simp [hc1_lt]
                      · simp [hc1_lt, hc2_lt', show st.mem (base + (2 * st.regs 3 + 2)) ≤
                          st.mem (base + (2 * st.regs 3 + 1)) by
                            simpa [Nat.add_assoc] using Nat.le_of_not_lt hcond]⟩
                · wram_cost
              · wram_run
                · exact ⟨rfl, rfl, hr0, hr1, hr2, rfl, hfl1, Or.inl (by simp), by simp; omega,
                    fun c2 hc2_mem hc2_lt => by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2_mem
                      rcases hc2_mem with rfl | rfl
                      · exact le_rfl
                      · omega⟩
                · wram_cost
            rcases hmid with ⟨o_mid, stMid, c1, hrun1, ⟨rfl, hmemMid, hm0, hm1, hm2, hm3, hm4, hch_cases, hch_lt', hsib⟩, hc1⟩
            have hvr_lt : stMid.mem (base + stMid.regs 3) < 2 ^ w := by
              rw [hmemMid, hm3]; exact hlt_m _ hroot_lt
            have hvc_lt : stMid.mem (base + stMid.regs 5) < 2 ^ w := by
              rw [hmemMid]; exact hlt_m _ hch_lt'
            have h_tail :
                ∃ (o : Outcome) (stEnd : State) (c2 : ℕ),
                  Runs w p ω bodyTail stMid o stEnd c2 ∧
                  (o = .normal ∧ Inv stEnd ∧ meas stEnd < meas st) ∧ 0 + c2 ≤ 30 := by
              dsimp only [bodyTail]
              wram_run
              · -- Swap case (`hcond` is `mem[base+root] < mem[base+child]`)
                have hswap : stMid.mem (base + stMid.regs 3) < stMid.mem (base + stMid.regs 5) := by
                  simpa [hm0, hm3] using hcond
                set mem1 := Function.update stMid.mem (base + st.regs 3) (stMid.mem (base + stMid.regs 5))
                set mem2 := Function.update mem1 (base + stMid.regs 5) (stMid.mem (base + st.regs 3))
                have htab_swap : tab end_ (fun i => mem2 (base + i)) =
                    listSwap (tab end_ fun i => st.mem (base + i)) (st.regs 3) (stMid.regs 5) := by
                  have heq_t : tab end_ (fun i => mem2 (base + i)) =
                      ((tab end_ fun i => stMid.mem (base + i)).set (st.regs 3)
                        (stMid.mem (base + stMid.regs 5))).set (stMid.regs 5)
                        (stMid.mem (base + st.regs 3)) := by
                    dsimp only [mem2, mem1]
                    rw [tab_update_set hch_lt', tab_update_set hroot_lt]
                  rw [heq_t]
                  simp only [tab, listSwap, List.getD_eq_getElem?_getD,
                    List.getElem?_map, List.getElem?_range, hmemMid, hroot_lt, hch_lt',
                    Option.map_some, Option.getD_some]
                have hperm' : (tab end_ fun i => mem2 (base + i)).Perm
                    (tab end_ fun i => mem (base + i)) := by
                  rw [htab_swap]
                  exact (listSwap_perm _ (by simp [tab]; omega) (by simp [tab]; omega)).trans hperm
                have hlt_m' : ∀ i < end_, mem2 (base + i) < 2 ^ w := by
                  intro i hi
                  dsimp only [mem2, mem1]
                  by_cases hi5 : base + i = base + stMid.regs 5
                  · rw [hi5, Function.update_self, hmemMid]; exact hlt_m _ hroot_lt
                  · rw [Function.update_of_ne hi5]
                    by_cases hi3 : base + i = base + st.regs 3
                    · rw [hi3, Function.update_self, hmemMid]; exact hlt_m _ hch_lt'
                    · rw [Function.update_of_ne hi3, hmemMid]; exact hlt_m _ hi
                have hfr1 : MemFrame stMid.mem mem1 (base + start) (base + end_) :=
                  memFrame_update (by omega : base + start ≤ base + st.regs 3)
                    (by omega : base + st.regs 3 < base + end_)
                have hfr2 : MemFrame mem1 mem2 (base + start) (base + end_) :=
                  memFrame_update (by omega : base + start ≤ base + stMid.regs 5)
                    (by omega : base + stMid.regs 5 < base + end_)
                have hframe' : MemFrame mem mem2 (base + start) (base + end_) :=
                  memFrame_trans (hmemMid ▸ hframe) (memFrame_trans hfr1 hfr2)
                have hsinv' : SiftInv (tab end_ fun i => mem2 (base + i)) start end_ (stMid.regs 5) 1 := by
                  rw [htab_swap]
                  refine siftInv_swap (by simp [tab]) (hfl1 ▸ hsinv) hch_cases hch_lt' hsib ?_
                  simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
                    hroot_lt, hch_lt', Option.map_some, Option.getD_some, ← hmemMid]
                  simpa [hm3] using hswap
                have hmeas_drop : 2 * (Nat.log 2 end_ - Nat.log 2 (stMid.regs 5 + 1)) + 1 <
                    meas st := by
                  dsimp only [meas]
                  simp only [hfl1, one_ne_zero, ↓reduceIte]
                  have hmul_le : (st.regs 3 + 1) * 2 ≤ stMid.regs 5 + 1 := by omega
                  have hlog_step : Nat.log 2 (st.regs 3 + 1) + 1 ≤ Nat.log 2 (stMid.regs 5 + 1) := by
                    rw [← Nat.log_mul_base (by decide) (by omega)]
                    exact Nat.log_mono_right hmul_le
                  have hlog_end : Nat.log 2 (stMid.regs 5 + 1) ≤ Nat.log 2 end_ :=
                    Nat.log_mono_right (by omega)
                  omega
                refine ⟨rfl, ⟨by simp [hm0], by simp [hm1], by simp [hm2], Or.inr (by simp [hm4]),
                  by simpa [hm0, hm3] using hperm', by simpa [hm0, hm3] using hlt_m',
                  by simpa [hm0, hm3] using hframe',
                  by simpa [hm0, hm3, hm4, mem2, mem1] using hsinv'⟩, ?_⟩
                simpa [meas, hm4] using hmeas_drop
              · wram_cost
              · -- No swap: flag := 0
                have hsinv' : SiftInv (tab end_ fun i => stMid.mem (base + i)) start end_
                    (st.regs 3) 0 := by
                  rw [hmemMid]
                  rcases hsinv with ⟨hs1, hs2, hs3, hs4, _⟩
                  refine ⟨hs1, hs2, hs3, hs4, fun _ => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
                  · have hc1_le := hsib (2 * st.regs 3 + 1) (by simp) h1
                    have hmid_le : (tab end_ fun i => st.mem (base + i)).getD (stMid.regs 5) 0 ≤
                        (tab end_ fun i => st.mem (base + i)).getD (st.regs 3) 0 := by
                      simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map,
                        List.getElem?_range, hch_lt', hroot_lt]
                      rw [← hmemMid, ← hm3]
                      simpa [hm0, hm3] using hcond
                    exact le_trans hc1_le hmid_le
                  · have hc2_le := hsib (2 * st.regs 3 + 2) (by simp) h2
                    have hmid_le : (tab end_ fun i => st.mem (base + i)).getD (stMid.regs 5) 0 ≤
                        (tab end_ fun i => st.mem (base + i)).getD (st.regs 3) 0 := by
                      simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map,
                        List.getElem?_range, hch_lt', hroot_lt]
                      rw [← hmemMid, ← hm3]
                      simpa [hm0, hm3] using hcond
                    exact le_trans hc2_le hmid_le
                refine ⟨rfl, ⟨by simp [hm0], by simp [hm1], by simp [hm2], Or.inl (by simp),
                  by simpa [hmemMid] using hperm, by simpa [hmemMid] using hlt_m,
                  by simpa [hmemMid] using hframe, by simp [hm3]; exact hsinv'⟩, ?_⟩
                dsimp only [meas]; simp [hfl1]
              · wram_cost
            rcases h_tail with ⟨o_end, stEnd, c2, hrun2, ⟨rfl, hInv', hmeas'⟩, hc2⟩
            exact ⟨.normal, stEnd, _, runs_seq_iff.mpr (Or.inr ⟨stMid, c1, c2, hrun1, hrun2, rfl⟩),
              ⟨hInv', hmeas'⟩, by wram_cost⟩
          · wram_step
            · refine ⟨⟨?_, ?_, ?_, Or.inl (by simp), hperm, hlt_m, hframe, ?_⟩, ?_⟩
              · simp [hr0]
              · simp [hr1]
              · simp [hr2]
              · simp only [Function.update_self]
                rcases hsinv with ⟨hs1, hs2, hs3, hs4, _⟩
                exact ⟨hs1, hs2, hs3, hs4, fun _ =>
                  ⟨fun h1 => by rw [← hr2] at h1; exact absurd h1 hcond,
                   fun h2 => by rw [← hr2] at h2; exact absurd (Nat.lt_of_succ_lt h2) hcond⟩⟩
              · dsimp only [meas]; simp [hfl1]
            · wram_cost
      refine runs_seq_triple_le hloop ?_ (fun st' hst' => ?_)
      · refine ⟨rfl, rfl, rfl, Or.inr rfl, List.Perm.refl _, hmem_lt,
          memFrame_refl _ _ _, ?_⟩
        simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
        exact siftInv_init hse hheap
      · wram_step
        · refine ⟨rfl, hst'.1.2.2.2.2.1, hst'.1.2.2.2.2.2.1,
            siftInv_done (hst'.2 ▸ hst'.1.2.2.2.2.2.2.2), hst'.1.2.2.2.2.2.2.1⟩
        · have hlog_le : Nat.log 2 end_ ≤ Nat.log 2 (end_ + 1) :=
            Nat.log_mono_right (Nat.le_succ end_)
          let st0_init : State :=
            { mem := mem,
              regs := Function.update (Function.update (startState [base, start, end_] mem pos).regs 3 start) 4 1,
              pos := pos }
          have hmeas_le : meas st0_init ≤ 2 * Nat.log 2 (end_ + 1) + 1 := by
            dsimp only [meas, st0_init, startState]
            simp only [Function.update_self, one_ne_zero, ↓reduceIte]
            omega
          simp only [Expr.size_const, Expr.size_reg] at *
          nlinarith [hmeas_le]
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [base, start, end_] mem pos) ω rfl
  rcases hpost with ⟨rfl, hp', hlt', hh', hfr'⟩
  exact ⟨siftDownProc, hproc, .returned 0, st', c, hrun, ⟨rfl, hp', hlt', hh', hfr'⟩, hcost⟩

/-- `heapSortProc b`: `args = [base, n]`, sorts `mem[base .. base + n - 1]` in-place by calling
`siftDown` at `b + 0`. -/
def heapSortProc (b : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.const 2))
    (.ret (.const 0))
    (.seq (.assign 2 (.bin .div (.reg 1) (.const 2))) -- idx := n / 2
    (.seq (.loop (.bin .lt (.const 0) (.reg 2))
      (.seq (.assign 2 (.bin .sub (.reg 2) (.const 1)))
        (.call 3 b [.reg 0, .reg 2, .reg 1])))
    (.seq (.assign 2 (.reg 1)) -- end_ := n
    (.seq (.loop (.bin .lt (.const 1) (.reg 2))
      (.seq (.assign 2 (.bin .sub (.reg 2) (.const 1)))
      (.seq (.assign 4 (.load (.reg 0)))
      (.seq (.assign 5 (.load (.bin .add (.reg 0) (.reg 2))))
      (.seq (.store (.reg 0) (.reg 5))
      (.seq (.store (.bin .add (.reg 0) (.reg 2)) (.reg 4))
        (.call 3 b [.reg 0, .const 0, .reg 2])))))))
    (.ret (.const 0))))))

lemma heapSortProc_noRand (b : ℕ) : (heapSortProc b).NoRand := by
  simp [heapSortProc, Stmt.NoRand]

/-- Contract for `heapSortProc b`: args `[base, n]`. -/
def heapSortContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ base n, args = [base, n] ∧
      base + n + 2 < 2 ^ w ∧
      2 * n + 2 < 2 ^ w ∧
      4 ≤ 2 ^ w ∧
      ∀ i < n, mem (base + i) < 2 ^ w
  post args mem v mem' :=
    let base := args.getD 0 0
    let n := args.getD 1 0
    let xs := tab n fun i => mem (base + i)
    let xs' := tab n fun i => mem' (base + i)
    v = 0 ∧
    xs'.Perm xs ∧
    xs'.Pairwise (· ≤ ·) ∧
    (∀ i < n, mem' (base + i) < 2 ^ w) ∧
    MemFrame mem mem' base (base + n)
  cost args _ :=
    let n := args.getD 1 0
    280 * (n * (2 * Nat.log 2 (n + 2) + 1) + 1)

private lemma pairwise_le_of_heap_step {xs : List ℕ} {n end_ : ℕ}
    (hlen : xs.length = n) (h1 : 1 ≤ end_) (hend : end_ ≤ n)
    (hdrop : (xs.drop end_).Pairwise (· ≤ ·))
    (hdom : ∀ i < end_, ∀ j, end_ ≤ j → j < n → xs.getD i 0 ≤ xs.getD j 0) :
    (xs.drop (end_ - 1)).Pairwise (· ≤ ·) := by
  set k := end_ - 1
  have hk_lt : k < xs.length := by omega
  rw [List.drop_eq_getElem_cons hk_lt, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [show k + 1 = end_ by omega] at hx
    rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
    simp only [List.length_drop, hlen] at hj
    rw [List.getElem_drop]
    have hj_lt : end_ + j < n := by omega
    have hdom' := hdom k (by omega) (end_ + j) (by omega) hj_lt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt,
      List.getElem?_eq_getElem (by omega : end_ + j < xs.length), Option.getD_some] at hdom'
    exact hdom'
  · rwa [show k + 1 = end_ by omega]

theorem heapSort_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp0 : p.HasAt b [siftDownProc]) (hp1 : p.HasAt (b + 1) [heapSortProc b]) :
    MeetsContract w p (b + 1) (heapSortContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [heapSortContract] at hpre
  rcases hpre with ⟨base, n, rfl, hbn, h2n, hw4, hmem_lt⟩
  have hproc : p.procs[b + 1]? = some (heapSortProc b) := hp1 0 (by simp)
  have hlt_base : base < 2 ^ w := hwords base (by simp)
  have hlt_n : n < 2 ^ w := hwords n (by simp)
  have hsift := siftDown_spec (w := w) hp0
  by_cases hn2 : n < 2
  · have htriple :
        Triple w p
          (fun st => st = startState [base, n] mem pos)
          (heapSortProc b)
          (fun o st' => o = .returned 0 ∧
            (tab n fun i => st'.mem (base + i)).Perm (tab n fun i => mem (base + i)) ∧
            (tab n fun i => st'.mem (base + i)).Pairwise (· ≤ ·) ∧
            (∀ i < n, st'.mem (base + i) < 2 ^ w) ∧
            MemFrame mem st'.mem base (base + n))
          (fun _ => 280 * (n * (2 * Nat.log 2 (n + 2) + 1) + 1)) := by
      wram_enter
      · subst hpre
        dsimp only [heapSortProc]
        wram_run
        · refine ⟨rfl, List.Perm.refl _, ?_, hmem_lt, memFrame_refl _ _ _⟩
          cases hn : n with
          | zero => simp [tab]
          | succ k =>
            have hk0 : k = 0 := by omega
            subst hk0
            simp [tab]
        · wram_cost
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [base, n] mem pos) ω rfl
    rcases hpost with ⟨rfl, hperm, hpair, hlt_out, hframe⟩
    exact ⟨heapSortProc b, hproc, .returned 0, st', c, hrun, ⟨rfl, hperm, hpair, hlt_out, hframe⟩, hcost⟩
  · have hn_ge : 2 ≤ n := Nat.le_of_not_lt hn2
    have htriple :
        Triple w p
          (fun st => st = startState [base, n] mem pos)
          (heapSortProc b)
          (fun o st' => o = .returned 0 ∧
            (tab n fun i => st'.mem (base + i)).Perm (tab n fun i => mem (base + i)) ∧
            (tab n fun i => st'.mem (base + i)).Pairwise (· ≤ ·) ∧
            (∀ i < n, st'.mem (base + i) < 2 ^ w) ∧
            MemFrame mem st'.mem base (base + n))
          (fun _ => 280 * (n * (2 * Nat.log 2 (n + 2) + 1) + 1)) := by
      wram_enter
      · subst hpre
        dsimp only [heapSortProc]
        wram_step
        wram_step
        let Inv1 : State → Prop := fun st =>
          st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 ≤ n ∧
          (tab n fun i => st.mem (base + i)).Perm (tab n fun i => mem (base + i)) ∧
          (∀ i < n, st.mem (base + i) < 2 ^ w) ∧
          MemFrame mem st.mem base (base + n) ∧
          IsHeapRange (tab n fun i => st.mem (base + i)) (st.regs 2) n
        let B1 := 85 * (2 * Nat.log 2 (n + 2) + 1) + 30
        have hloop1 : Triple w p Inv1
            (.loop (.bin .lt (.const 0) (.reg 2))
              (.seq (.assign 2 (.bin .sub (.reg 2) (.const 1)))
                (.call 3 b [.reg 0, .reg 2, .reg 1])))
            (normalPost fun st' => Inv1 st' ∧ st'.regs 2 = 0)
            (fun st => (3 + B1 + 1) * st.regs 2 + 3 + 1) := by
          refine Triple.loop_const_normal (fun st => st.regs 2)
            (fun st => if 0 < st.regs 2 then 1 else 0) B1
            (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
            (fun st hInv h0 => by
              simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
              exact ⟨hInv, by omega⟩)
            (fun st hInv hne => ?_)
          simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
          rcases hInv with ⟨hr0, hr1, hr2, hperm, hlt_m, hframe, hheap⟩
          have hpos : 0 < st.regs 2 := by omega
          wram_enter
          · subst hpre
            wram_step
            have hr2' : st.regs 2 - 1 < n := by omega
            refine runs_call_le hsift (by eval_expr) (by wram_words) ?_ ?_
            · refine ⟨base, st.regs 2 - 1, n, rfl, hr2', by omega, by omega, hw4, hlt_m, ?_⟩
              rwa [show st.regs 2 - 1 + 1 = st.regs 2 by omega]
            · intro v mem' pos' hpost
              rcases hpost with ⟨rfl, hperm', hlt', hh', hfr'⟩
              simp only [List.getD_cons_zero, List.getD_cons_succ] at hperm' hh' hfr'
              refine ⟨⟨⟨?_, ?_, ?_, hperm'.trans hperm, hlt',
                memFrame_trans hframe (memFrame_mono hfr' (by omega) le_rfl), ?_⟩, ?_⟩, ?_⟩
              · simp [hr0]
              · simp [hr1]
              · simp; omega
              · simpa [show ∀ r, Function.update (Function.update st.regs 2 (st.regs 2 - 1)) 3 0 r = _ from fun _ => rfl]
                  using hh'
              · simp; omega
              · have hle_log : Nat.log 2 (n + 1) ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
                simp [siftDownContract, B1, argsSize]
                omega
        refine runs_seq_triple_le hloop1 ?_ (fun st1 hst1 => ?_)
        · refine ⟨rfl, rfl, Nat.div_le_self _ _, List.Perm.refl _, hmem_lt,
            memFrame_refl _ _ _, isHeapRange_vacuous _ ?_⟩
          simp [Function.update_self]
          omega
        rcases hst1 with ⟨⟨hs1_0, hs1_1, _, hperm1, hlt1, hframe1, hheap1⟩, hs1_2⟩
        wram_step
        let Inv2 : State → Prop := fun st =>
          st.regs 0 = base ∧ st.regs 1 = n ∧ 1 ≤ st.regs 2 ∧ st.regs 2 ≤ n ∧
          (tab n fun i => st.mem (base + i)).Perm (tab n fun i => mem (base + i)) ∧
          (∀ i < n, st.mem (base + i) < 2 ^ w) ∧
          MemFrame mem st.mem base (base + n) ∧
          IsHeapRange (tab (st.regs 2) fun i => st.mem (base + i)) 0 (st.regs 2) ∧
          ((tab n fun i => st.mem (base + i)).drop (st.regs 2)).Pairwise (· ≤ ·) ∧
          (∀ i < st.regs 2, ∀ j, st.regs 2 ≤ j → j < n →
            st.mem (base + i) ≤ st.mem (base + j))
        let B2 := 85 * (2 * Nat.log 2 (n + 2) + 1) + 60
        have hloop2 : Triple w p Inv2
            (.loop (.bin .lt (.const 1) (.reg 2))
              (.seq (.assign 2 (.bin .sub (.reg 2) (.const 1)))
              (.seq (.assign 4 (.load (.reg 0)))
              (.seq (.assign 5 (.load (.bin .add (.reg 0) (.reg 2))))
              (.seq (.store (.reg 0) (.reg 5))
              (.seq (.store (.bin .add (.reg 0) (.reg 2)) (.reg 4))
                (.call 3 b [.reg 0, .const 0, .reg 2])))))))
            (normalPost fun st' => Inv2 st' ∧ st'.regs 2 = 1)
            (fun st => (3 + B2 + 1) * (st.regs 2 - 1) + 3 + 1) := by
          refine Triple.loop_const_normal (fun st => st.regs 2 - 1)
            (fun st => if 1 < st.regs 2 then 1 else 0) B2
            (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
            (fun st hInv h0 => by
              simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
              exact ⟨hInv, by rcases hInv with ⟨_, _, h1, _⟩; omega⟩)
            (fun st hInv hne => ?_)
          simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
          rcases hInv with ⟨hr0, hr1, h1e, hen, hperm, hlt_m, hframe, hheap, hdrop, hdom⟩
          have he_gt1 : 1 < st.regs 2 := by omega
          set e := st.regs 2 - 1
          have he_pos : 0 < e := by omega
          have he_lt : e < n := by omega
          let mem1 := Function.update st.mem base (st.mem (base + e))
          let mem2 := Function.update mem1 (base + e) (st.mem base)
          have htab_swap_n : tab n (fun i => mem2 (base + i)) =
              listSwap (tab n fun i => st.mem (base + i)) 0 e := by
            dsimp only [mem2, mem1]
            have hbase_eq : Function.update st.mem base (st.mem (base + e)) =
                Function.update st.mem (base + 0) (st.mem (base + e)) := by simp
            rw [tab_update_set he_lt, hbase_eq, tab_update_set (by omega : 0 < n)]
            simp [tab, listSwap, List.getD_eq_getElem?_getD, he_lt, show 0 < n by omega]
          have hperm2 : (tab n fun i => mem2 (base + i)).Perm (tab n fun i => mem (base + i)) := by
            rw [htab_swap_n]
            exact (listSwap_perm _ (by simp [tab]; omega) (by simp [tab]; omega)).trans hperm
          have hlt_m2 : ∀ i < n, mem2 (base + i) < 2 ^ w := by
            intro i hi
            dsimp only [mem2, mem1]
            by_cases hie : base + i = base + e
            · rw [hie, Function.update_self]; simpa using hlt_m 0 (by omega)
            · rw [Function.update_of_ne hie]
              by_cases hi0 : base + i = base
              · rw [hi0, Function.update_self]; exact hlt_m _ he_lt
              · rw [Function.update_of_ne hi0]; exact hlt_m _ hi
          have hframe2 : MemFrame mem mem2 base (base + n) :=
            memFrame_trans hframe (memFrame_trans
              (memFrame_update le_rfl (by omega)) (memFrame_update (by omega) (by omega)))
          have hheap2 : IsHeapRange (tab e fun i => mem2 (base + i)) 1 e := by
            intro p _
            have hp_mem : ∀ k < e, 0 < k → mem2 (base + k) = st.mem (base + k) := by
              intro k hke hk0
              dsimp only [mem2, mem1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            have hp_old := hheap p (Nat.zero_le p)
            refine ⟨fun h1 => ?_, fun h2 => ?_⟩
            · simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_range, h1, show p < e by omega, Option.map_some,
                Option.getD_some]
              rw [hp_mem (2 * p + 1) h1 (by omega), hp_mem p (by omega) (by omega)]
              simpa [tab, show 2 * p + 1 < st.regs 2 by omega, show p < st.regs 2 by omega]
                using hp_old.1 (by omega)
            · simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_range, h2, show p < e by omega, Option.map_some,
                Option.getD_some]
              rw [hp_mem (2 * p + 2) h2 (by omega), hp_mem p (by omega) (by omega)]
              simpa [tab, show 2 * p + 2 < st.regs 2 by omega, show p < st.regs 2 by omega]
                using hp_old.2 (by omega)
          have hdom2 : ∀ i < e, ∀ j, e ≤ j → j < n → mem2 (base + i) ≤ mem2 (base + j) := by
            intro i hie j hje hjn
            have hi_val : mem2 (base + i) =
                if i = 0 then st.mem (base + e) else st.mem (base + i) := by
              dsimp only [mem2, mem1]
              rw [Function.update_of_ne (by omega)]
              split_ifs with hi0
              · subst hi0; simp
              · exact Function.update_of_ne (by omega) _ st.mem
            have hj_val : mem2 (base + j) =
                if j = e then st.mem base else st.mem (base + j) := by
              dsimp only [mem2, mem1]
              split_ifs with hj0
              · subst hj0; simp
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            have hmax_old : ∀ k < st.regs 2, st.mem (base + k) ≤ st.mem base := by
              intro k hk
              have hm := isHeapRange_max _ hheap k hk
              simpa [tab, hk, show 0 < st.regs 2 by omega] using hm
            rw [hi_val, hj_val]
            split_ifs with hi0 hjeq
            · exact hmax_old e (by omega)
            · exact hdom e (by omega) j (by omega) hjn
            · exact hmax_old i (by omega)
            · exact hdom i (by omega) j (by omega) hjn
          have hdrop2 : ((tab n fun i => mem2 (base + i)).drop e).Pairwise (· ≤ ·) := by
            have hdrop_old : ((tab n fun i => mem2 (base + i)).drop (st.regs 2)).Pairwise (· ≤ ·) := by
              have heq_sub : (tab n fun i => mem2 (base + i)).drop (st.regs 2) =
                  (tab n fun i => st.mem (base + i)).drop (st.regs 2) := by
                apply List.ext_getElem
                · simp [tab]
                · intro k hk1 hk2
                  simp only [List.getElem_drop, tab, List.getElem_map, List.getElem_range]
                  dsimp only [mem2, mem1]
                  rw [Function.update_of_ne (by simp [tab] at hk1; omega),
                    Function.update_of_ne (by simp [tab] at hk1; omega)]
              rwa [heq_sub]
            refine pairwise_le_of_heap_step (xs := tab n fun i => mem2 (base + i))
              (by simp [tab]) h1e hen hdrop_old fun i hi j hj hjn => ?_
            simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range, hjn, show i < n by omega, Option.map_some, Option.getD_some]
            by_cases hie : i < e
            · have := hdom2 i hie j (by omega) hjn
              simpa [tab, show i < n by omega, hjn] using this
            · have hie_eq : i = e := by omega
              subst hie_eq
              dsimp only [mem2, mem1]
              rw [Function.update_self, Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              simpa using hdom 0 (by omega) j hj hjn
          wram_enter
          · subst hpre
            wram_step; wram_step; wram_step; wram_step; wram_step
            have hmem_goal : Function.update (Function.update st.mem (st.regs 0)
                (st.mem (st.regs 0 + (st.regs 2 - 1)))) (st.regs 0 + (st.regs 2 - 1))
                (st.mem (st.regs 0)) = mem2 := by
              simp only [hr0, mem2, mem1, e]
            simp only [hmem_goal]
            refine runs_call_le hsift (vs := [base, 0, e]) (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨base, 0, e, rfl, he_pos, by omega, by omega, hw4,
                fun i hi => hlt_m2 i (by omega), by simpa using hheap2⟩
            · intro v mem' pos' hpost
              rcases hpost with ⟨rfl, hperm_e, hlt_e, hh_e, hfr_e⟩
              simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at hperm_e hh_e hfr_e
              have hperm_all : (tab n fun i => mem' (base + i)).Perm (tab n fun i => mem (base + i)) := by
                have htake1 : (tab n (fun i => mem' (base + i))).take e = tab e (fun i => mem' (base + i)) := by
                  apply List.ext_getElem <;> simp [tab, min_eq_left (le_of_lt he_lt)]
                have htake2 : (tab n (fun i => mem2 (base + i))).take e = tab e (fun i => mem2 (base + i)) := by
                  apply List.ext_getElem <;> simp [tab, min_eq_left (le_of_lt he_lt)]
                have hdrop_eq : (tab n fun i => mem' (base + i)).drop e =
                    (tab n fun i => mem2 (base + i)).drop e := by
                  apply List.ext_getElem
                  · simp [tab]
                  · intro k hk1 _
                    simp only [List.getElem_drop, tab, List.getElem_map, List.getElem_range]
                    exact hfr_e (base + (e + k)) (Or.inr (by omega))
                rw [← List.take_append_drop e (tab n fun i => mem' (base + i)), htake1, hdrop_eq]
                refine (hperm_e.append (List.Perm.refl _)).trans ?_
                rw [← htake2, List.take_append_drop]
                exact hperm2
              have hlt_all : ∀ i < n, mem' (base + i) < 2 ^ w := by
                intro i hi
                by_cases hie : i < e
                · exact hlt_e i hie
                · rw [hfr_e (base + i) (Or.inr (by omega))]; exact hlt_m2 i hi
              have hdrop_all : ((tab n fun i => mem' (base + i)).drop e).Pairwise (· ≤ ·) := by
                have hdrop_eq : (tab n fun i => mem' (base + i)).drop e =
                    (tab n fun i => mem2 (base + i)).drop e := by
                  apply List.ext_getElem
                  · simp [tab]
                  · intro k hk1 _
                    simp only [List.getElem_drop, tab, List.getElem_map, List.getElem_range]
                    exact hfr_e (base + (e + k)) (Or.inr (by omega))
                rwa [hdrop_eq]
              have hdom_all : ∀ i < e, ∀ j, e ≤ j → j < n → mem' (base + i) ≤ mem' (base + j) := by
                intro i hie j hje hjn
                have hj_eq : mem' (base + j) = mem2 (base + j) := hfr_e (base + j) (Or.inr (by omega))
                have hi_mem : mem' (base + i) ∈ tab e (fun k => mem' (base + k)) := by
                  simp only [tab, List.mem_map, List.mem_range]
                  exact ⟨i, hie, rfl⟩
                rw [hperm_e.mem_iff] at hi_mem
                simp only [tab, List.mem_map, List.mem_range] at hi_mem
                rcases hi_mem with ⟨k, hke, hk_eq⟩
                rw [← hk_eq, hj_eq]
                exact hdom2 k hke j hje hjn
              refine ⟨⟨⟨?_, ?_, by simp; omega, by simp; omega, hperm_all, hlt_all,
                  memFrame_trans hframe2 (memFrame_mono hfr_e le_rfl (by omega)),
                  by simpa using hh_e, by simpa using hdrop_all,
                  fun i hi j hj hjn => by
                    simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)] at hi hj
                    exact hdom_all i hi j hj hjn⟩, by simp; omega⟩, ?_⟩
              · simp [hr0]
              · simp [hr1]
              · have hle_log : Nat.log 2 (e + 1) ≤ Nat.log 2 (n + 2) :=
                  Nat.log_mono_right (by omega)
                simp [siftDownContract, argsSize]
                dsimp only [B2]
                omega
        refine runs_seq_triple_le hloop2 ?_ (fun st2 hst2 => ?_)
        · refine ⟨by simpa using hs1_0, by simpa using hs1_1, by simp; omega,
            by simp, hperm1, hlt1, hframe1, ?_, ?_, ?_⟩
          · simp only [Function.update_self]
            exact hs1_2 ▸ hheap1
          · simp only [Function.update_self, tab]
            rw [List.drop_eq_nil_of_le (by simp)]
            exact List.Pairwise.nil
          · intro i hi j hj hjn
            simp only [Function.update_self] at hj
            omega
        · wram_step
          · rcases hst2 with ⟨⟨_, _, _, _, hperm2, hlt2, hframe2, _, hdrop2, hdom2⟩, hr2_one⟩
            have hpair : (tab n fun i => st2.mem (base + i)).Pairwise (· ≤ ·) := by
              have hk0 : 0 < (tab n fun i => st2.mem (base + i)).length := by simp [tab]; omega
              rw [show (tab n fun i => st2.mem (base + i)) =
                (tab n fun i => st2.mem (base + i)).drop 0 by simp,
                List.drop_eq_getElem_cons hk0, List.pairwise_cons]
              refine ⟨fun x hx => ?_, ?_⟩
              · simp only [Nat.zero_add] at hx
                rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
                simp only [List.length_drop, tab, List.length_map, List.length_range] at hj
                rw [List.getElem_drop]
                simp only [tab, List.getElem_map, List.getElem_range]
                exact hdom2 0 (by omega) (1 + j) (by omega) (by omega)
              · simpa [hr2_one] using hdrop2
            exact ⟨rfl, hperm2, hpair, hlt2, hframe2⟩
          · have hn_div_le : n / 2 ≤ n := Nat.div_le_self n 2
            have hn_sub_le : n - 1 ≤ n := Nat.sub_le n 1
            dsimp only [B1, B2, startState] at *
            simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Function.update_self] at *
            nlinarith [hn_div_le, hn_sub_le]
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [base, n] mem pos) ω rfl
    rcases hpost with ⟨rfl, hperm, hpair, hlt_out, hframe⟩
    exact ⟨heapSortProc b, hproc, .returned 0, st', c, hrun, ⟨rfl, hperm, hpair, hlt_out, hframe⟩, hcost⟩

end MinCostFlow.Expander
