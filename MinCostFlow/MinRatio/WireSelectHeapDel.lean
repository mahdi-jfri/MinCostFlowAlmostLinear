module

public import MinCostFlow.MinRatio.WireSelectHeapUpsert
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Select-heap deletion, conditional level deletion, bulk level clear, and relocatable module

Implements and verifies:
1. `heapDeleteBody rebal candErase` (`[hb, e, scratch]`): deletes edge `e` if present (`pos[e] ≠ 0`),
   removing it from its level's candidate list and swapping in `arr[size - 1]` + `heapRebalance`
   in `O((log(cap + 1) + 1) · (Lk^2 + 1))` steps.
2. `heapDeleteIfLevelBody del` (`[hb, e, lvl, scratch]`): deletes `e` iff `pos[e] ≠ 0 ∧ lvl[e] = lvl`.
3. `heapClearLevelBody self del` (`[hb, lvl, scratch]`): recursively deletes every candidate in
   level `lvl` via `candHead[lvl]`, in `O(|S_lvl| · (log(cap + 1) + 1) · (Lk^2 + 1))` steps.
4. `selectHeapOpsModule b h`: relocatable 22-procedure deterministic module bundling all select-heap
   operations (`keyCompare` through `heapClearLevel`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 1. `heapDelete`, `heapDeleteIfLevel`, `heapClearLevel` -/

/-- Delete edge `e` (`reg 1`) from heap `hb` (`reg 0`) if present, using scratch `reg 2`. -/
def heapDeleteBody (rebal candErase : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const shArrOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const shPosOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const shLvlOff))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 1))) ;;
  .cond (.bin .eq (.reg 6) (.const 0))
    (.ret (.reg 2))
    (.assign 7 (.bin .sub (.reg 6) (.const 1)) ;;
     .assign 8 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .call 9 candErase [.reg 0, .reg 8, .reg 1] ;;
     .assign 10 (.bin .sub (.load (.reg 0)) (.const 1)) ;;
     .store (.reg 0) (.reg 10) ;;
     .store (.bin .add (.reg 4) (.reg 1)) (.const 0) ;;
     .cond (.bin .lt (.reg 7) (.reg 10))
       (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
        .store (.bin .add (.reg 3) (.reg 7)) (.reg 11) ;;
        .store (.bin .add (.reg 4) (.reg 11)) (.bin .add (.reg 7) (.const 1)) ;;
        .call 12 rebal [.reg 0, .reg 7, .reg 2] ;;
        .ret (.reg 12))
       (.ret (.reg 2)))

theorem heapDeleteBody_noRand (rebal candErase : ℕ) :
    (heapDeleteBody rebal candErase).NoRand := by
  simp [heapDeleteBody, Stmt.NoRand]

/-- Step cost bound for `heapDeleteBody`: `O((log(cap + 1) + 1) · (Lk^2 + 1))`. -/
def heapDeleteCost (cap Lk : ℕ) : ℕ :=
  heapRebalanceCost cap Lk + 240

/-- Contract for `heapDeleteBody`: removes `e` if present (decreasing `size` by 1) and leaves the
heap unchanged if absent, preserving all other edges' membership, level, and key. -/
def heapDeleteContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ e scratch, args = [loc.hb, e, scratch] ∧
      16 < 2 ^ w ∧ loc.endAddr ≤ scratch ∧ e < loc.cap ∧
      SelectHeapAt mem loc h size ∧
      ZeroFrom mem scratch ∧
      scratch + heapRebalanceSpace loc.cap loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let e := args.getD 1 0
    let scratch := args.getD 2 0
    let size' := if mem (loc.posPtr + e) = 0 then size else size - 1
    scratch ≤ ret ∧ ret ≤ scratch + heapRebalanceSpace loc.cap loc.Lk ∧
    SelectHeapAt mem' loc h size' ∧
    ZeroFrom mem' ret ∧
    mem' (loc.posPtr + e) = 0 ∧
    (∀ e' < loc.cap, e' ≠ e →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e') ∧
    (∀ a < scratch, (a < loc.hb ∨ loc.numBase ≤ a) → mem' a = mem a)
  cost _ _ := heapDeleteCost loc.cap loc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- `heapDeleteBody` meets `heapDeleteContract` in `O((log(cap + 1) + 1) · (Lk^2 + 1))` steps. -/
theorem heapDelete_meetsContract {w h proc rebal candErase : ℕ}
    {loc : SelectHeapLoc} {size : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (heapDeleteBody rebal candErase))
    (hrebal : MeetsContract w p rebal (heapRebalanceContract w h loc (size - 1)))
    (herase : ∀ lists, MeetsContract w p candErase (candListEraseContract w loc size lists)) :
    MeetsContract w p proc (heapDeleteContract w h loc size) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨e, scratch, rfl, hw16, hendLe, heCap, hat, hz, hroom⟩ := hpre
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hat
  have hhr := selectHeap_header_reads hhdr
  have hlvlHdr : mem (loc.hb + 6) = loc.lvlPtr := by simpa using hhdr 6 (by simp)
  have hlayout : loc.hb + 14 = loc.arrPtr ∧ loc.arrPtr + loc.cap = loc.posPtr ∧
      loc.posPtr + loc.cap = loc.lvlPtr ∧ loc.lvlPtr + loc.cap = loc.candHead ∧
      loc.candHead + (loc.d + 1) = loc.candPrev ∧ loc.candPrev + loc.cap = loc.candNext ∧
      loc.candNext + loc.cap = loc.numBase ∧ loc.numBase + loc.cap * loc.Lk = loc.denBase ∧
      loc.denBase + loc.cap * loc.Lk = loc.endAddr := by
    unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase SelectHeapLoc.numBase
      SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
      SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have harrW : loc.arrPtr < 2 ^ w := by omega
  have hposW : loc.posPtr < 2 ^ w := by omega
  have hlvlPtrW : loc.lvlPtr < 2 ^ w := by omega
  have hposEW : mem (loc.posPtr + e) < 2 ^ w := by
    rcases hbij.2.2.2 e heCap with h0 | ⟨hle, _⟩
    · omega
    · have := hbij.1; omega
  apply runs_start_le
  dsimp only [startState]
  unfold heapDeleteBody
  simp only [shArrOff, shPosOff, shLvlOff]
  refine runs_seq_assign_flat (v := loc.arrPtr) (by eval_expr; exact hhr.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.posPtr) (by eval_expr; exact hhr.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.lvlPtr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mem (loc.posPtr + e)) (by eval_expr) ?_
  by_cases hpos0 : mem (loc.posPtr + e) = 0
  · refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hpos0, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [heapDeleteContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ↓reduceIte]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨hhdr, hbij, hkeys, hord, hcand⟩, hz, trivial,
        fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩, fun _ _ _ => trivial⟩
    · simp only [heapDeleteContract, heapDeleteCost, Expr.size]; omega
  · rcases hbij.2.2.2 e heCap with h0 | ⟨hkLe, harrK⟩
    · exact (hpos0 h0).elim
    let k := mem (loc.posPtr + e) - 1
    let size' := size - 1
    have hszLe : size ≤ loc.cap := hbij.1
    have hszPos : 0 < size := by omega
    have hkLt : k < size := by omega
    have hszW : size < 2 ^ w := by have := hbij.1; omega
    have hsz'W : size' < 2 ^ w := by omega
    have hkW : k < 2 ^ w := by omega
    have holdLvlD : mem (loc.lvlPtr + e) ≤ loc.d := (hkeys e heCap hpos0).1
    have holdLvlW : mem (loc.lvlPtr + e) < 2 ^ w := by omega
    obtain ⟨lists, hlists⟩ := hcand
    have heMemOld : e ∈ lists (mem (loc.lvlPtr + e)) :=
      ((hlists _ holdLvlD).2 e).mpr ⟨heCap, hpos0, rfl⟩
    have hdisjLists : ∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists i → x ∉ lists j :=
      fun i j hi hj hij x hxi hxj =>
        hij (((hlists i hi).2 x).mp hxi |>.2.2.symm.trans (((hlists j hj).2 x).mp hxj).2.2)
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hpos0, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_assign_flat (v := k) (by dsimp only [k]; eval_expr) ?_
    refine runs_seq_assign_flat (v := mem (loc.lvlPtr + e)) (by eval_expr) ?_
    refine runs_seq_call_flat (herase lists) (vs := [loc.hb, mem (loc.lvlPtr + e), e])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨mem (loc.lvlPtr + e), e, rfl, hw16, by omega, holdLvlD, heCap, heMemOld, hhdr,
        fun i hi => (hlists i hi).1, hdisjLists⟩
    · intro _ mem1 pos1 hp1
      obtain ⟨_, hdlls1, hfr1⟩ := hp1
      change (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem1 a = mem a) at hfr1
      have hhd1 : mem1 loc.hb = size := (hfr1 loc.hb (Or.inl (by omega))).trans hhr.1
      refine runs_seq_assign_flat (v := size') (by dsimp only [size']; eval_expr) ?_
      refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
      let mem2 := Function.update (Function.update mem1 loc.hb size') (loc.posPtr + e) 0
      have hm2_out (a : ℕ) (h1 : a ≠ loc.hb) (h2 : a ≠ loc.posPtr + e) : mem2 a = mem1 a := by
        dsimp only [mem2]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
      have hmem2_key (e' : ℕ) (he' : e' < loc.cap) :
          loc.readNum mem2 h e' = loc.readNum mem h e' ∧
          loc.readDen mem2 h e' = loc.readDen mem h e' := by
        have hbd' := selectHeap_slot_bounds he'
        exact ⟨Num.intVal_congr fun j hj => (hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega))),
          Num.intVal_congr fun j hj => (hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega)))⟩
      have hhdr2 : SelectHeapHeaderAt mem2 loc size' := fun j hj => by
        simp only [List.length_cons, List.length_nil] at hj
        cases j with
        | zero => dsimp only [mem2]; simp [Function.update_of_ne (by omega : loc.hb ≠ loc.posPtr + e)]
        | succ m =>
          rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
          exact hhdr (m + 1) (by simp only [List.length_cons, List.length_nil]; omega)
      have hcand2 : SelectHeapCandLists mem2 loc := by
        refine ⟨fun i => if i = mem (loc.lvlPtr + e) then (lists i).erase e else lists i, fun i hi => ?_⟩
        refine ⟨(hdlls1 i hi).of_agree (hm2_out _ (by omega) (by omega))
          (fun y hy => by have := (hdlls1 i hi).2.1 y hy; exact hm2_out _ (by omega) (by omega))
          (fun y hy => by have := (hdlls1 i hi).2.1 y hy; exact hm2_out _ (by omega) (by omega)),
          fun e' => ?_⟩
        dsimp only
        by_cases hee : e' = e
        · subst e'
          constructor
          · intro hmem
            split_ifs at hmem with hil
            · have hnd := (hlists i hi).1.1
              have := List.nodup_iff_count_le_one.mp hnd e
              have hc1 : List.count e ((lists i).erase e) = List.count e (lists i) - 1 := List.count_erase_self
              have hpos : 0 < List.count e ((lists i).erase e) := List.count_pos_iff.mpr hmem
              omega
            · exact (hdisjLists i _ hi holdLvlD hil e hmem heMemOld).elim
          · rintro ⟨_, hnz, _⟩; simp [mem2] at hnz
        · have hmemEq : e' ∈ (if i = mem (loc.lvlPtr + e) then (lists i).erase e else lists i) ↔ e' ∈ lists i := by
            split_ifs; exact List.mem_erase_of_ne hee; exact Iff.rfl
          rw [hmemEq, (hlists i hi).2 e']
          constructor
          · rintro ⟨he', hnz', hl'⟩
            exact ⟨he', by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact hnz',
              by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact hl'⟩
          · rintro ⟨he', hnz', hl'⟩
            exact ⟨he', by rwa [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))] at hnz',
              by rwa [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))] at hl'⟩
      -- Branch on `k < size'`
      by_cases hks : k < size'
      · let last := mem (loc.arrPtr + size')
        have hlastCap : last < loc.cap := hbij.2.1 size' (by omega)
        have hlastNe : last ≠ e := fun heq => by
          have := hbij.arr_inj (show size' < size by omega) hkLt (heq.trans harrK.symm); omega
        have hlastW : last < 2 ^ w := by omega
        have hlast2 : mem2 (loc.arrPtr + size') = last :=
          (hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega)))
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hks, hw1]) ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assign_flat (v := last) (by eval_expr) ?_
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        let mem3 := Function.update (Function.update mem2 (loc.arrPtr + k) last) (loc.posPtr + last) (k + 1)
        have hm3_out (a : ℕ) (h1 : a ≠ loc.arrPtr + k) (h2 : a ≠ loc.posPtr + last) : mem3 a = mem2 a := by
          dsimp only [mem3]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
        have hhdr3 : SelectHeapHeaderAt mem3 loc size' := fun j hj => by
          simp only [List.length_cons, List.length_nil] at hj
          exact (hm3_out _ (by omega) (by omega)).trans (hhdr2 j (by simpa using hj))
        have hbij3 : SelectHeapBijection mem3 loc size' := by
          refine ⟨by have := hbij.1; omega, fun p hp => ?_, fun p hp => ?_, fun e' he' => ?_⟩
          · by_cases hpk : p = k
            · subst p; dsimp only [mem3]; rw [Function.update_of_ne (by omega), Function.update_self]; exact hlastCap
            · rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
              exact hbij.2.1 p (by omega)
          · by_cases hpk : p = k
            · subst p
              have ha3 : mem3 (loc.arrPtr + k) = last := by
                dsimp only [mem3]; rw [Function.update_of_ne (by omega), Function.update_self]
              rw [ha3]; dsimp only [mem3]; rw [Function.update_self]
            · have hpCap := hbij.2.1 p (by omega)
              have hpNeLast : mem (loc.arrPtr + p) ≠ last := fun heq => by
                have := hbij.arr_inj (by omega) (by omega) heq; omega
              have hpNeE : mem (loc.arrPtr + p) ≠ e := fun heq => by
                have := hbij.arr_inj (by omega) hkLt (heq.trans harrK.symm); exact hpk this
              have ha3 : mem3 (loc.arrPtr + p) = mem (loc.arrPtr + p) :=
                (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega))))
              rw [ha3, hm3_out (loc.posPtr + mem (loc.arrPtr + p)) (by omega) (by omega),
                  hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
              exact hbij.2.2.1 p (by omega)
          · by_cases hee : e' = e
            · subst e'; left
              rw [hm3_out _ (by omega) (by omega)]; simp [mem2]
            · by_cases hel : e' = last
              · subst e'; right
                have hp3 : mem3 (loc.posPtr + last) = k + 1 := by simp [mem3]
                rw [hp3]
                refine ⟨by omega, by dsimp only [mem3]; simp only [Nat.add_sub_cancel]; rw [Function.update_of_ne (by omega), Function.update_self]⟩
              · rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
                rcases hbij.2.2.2 e' he' with h0 | ⟨hle, harr⟩
                · exact Or.inl h0
                · have hltSz : mem (loc.posPtr + e') - 1 < size' := by
                    by_contra hge
                    have heqS : mem (loc.posPtr + e') - 1 = size' := by omega
                    rw [heqS] at harr; exact hel harr.symm
                  have hneK : mem (loc.posPtr + e') - 1 ≠ k := fun h => by
                    rw [h] at harr; exact hee (harr.symm.trans harrK)
                  have := hbij.1
                  exact Or.inr ⟨by omega, by
                    rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
                    exact harr⟩
        have hpos3_iff (e' : ℕ) (he' : e' < loc.cap) :
            mem3 (loc.posPtr + e') ≠ 0 ↔ mem2 (loc.posPtr + e') ≠ 0 := by
          by_cases hel : e' = last
          · subst e'
            have hlastPos : mem (loc.posPtr + last) ≠ 0 := hbij.pos_arr_ne_zero (by omega)
            rw [show mem3 (loc.posPtr + last) = k + 1 by simp [mem3],
                hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
            simp [hlastPos]
          · rw [hm3_out _ (by omega) (by omega)]
        have hkeys3 : SelectHeapKeysValid mem3 loc h := fun e' he' hnz => by
          have hbd' := selectHeap_slot_bounds he'
          rw [hpos3_iff e' he'] at hnz
          have hee : e' ≠ e := fun h => by subst e'; simp [mem2] at hnz
          have hnz0 : mem (loc.posPtr + e') ≠ 0 := by
            rwa [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))] at hnz
          obtain ⟨hl', hvn', hvd', hdp'⟩ := hkeys e' he' hnz0
          refine ⟨by rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact hl',
            fun j hj => by rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inr (by omega))]; exact hvn' j hj,
            fun j hj => by rw [hm3_out _ (by omega) (by omega), hm2_out _ (by omega) (by omega), hfr1 _ (Or.inr (by omega))]; exact hvd' j hj, ?_⟩
          have hden3 : loc.readDen mem3 h e' = loc.readDen mem h e' :=
            Num.intVal_congr fun j hj => (hm3_out _ (by omega) (by omega)).trans
              ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega))))
          rw [hden3]; exact hdp'
        have hcand3 : SelectHeapCandLists mem3 loc := by
          obtain ⟨lists2, hlists2⟩ := hcand2
          refine ⟨lists2, fun i hi => ⟨(hlists2 i hi).1.of_agree (hm3_out _ (by omega) (by omega))
            (fun y hy => by have := (hlists2 i hi).1.2.1 y hy; exact hm3_out _ (by omega) (by omega))
            (fun y hy => by have := (hlists2 i hi).1.2.1 y hy; exact hm3_out _ (by omega) (by omega)),
            fun e' => ?_⟩⟩
          rw [(hlists2 i hi).2 e']
          constructor
          · rintro ⟨he', hnz', hl'⟩
            exact ⟨he', (hpos3_iff e' he').mpr hnz', (hm3_out _ (by omega) (by omega)).trans hl'⟩
          · rintro ⟨he', hnz', hl'⟩
            exact ⟨he', (hpos3_iff e' he').mp hnz', (hm3_out _ (by omega) (by omega)).symm.trans hl'⟩
        have hedge3 (e₁ e₂ : ℕ) (h1 : e₁ < loc.cap) (h2 : e₂ < loc.cap) :
            loc.edgeBetter mem3 h e₁ e₂ = loc.edgeBetter mem h e₁ e₂ := by
          have hb1 := selectHeap_slot_bounds h1; have hb2 := selectHeap_slot_bounds h2
          unfold SelectHeapLoc.edgeBetter SelectHeapLoc.readNum SelectHeapLoc.readDen
          rw [Num.intVal_congr (fun j hj => (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega))))),
              Num.intVal_congr (fun j hj => (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega))))),
              Num.intVal_congr (fun j hj => (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega))))),
              Num.intVal_congr (fun j hj => (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inr (by omega)))))]
        have harr3 (p : ℕ) (hp : p < size') (hpk : p ≠ k) : mem3 (loc.arrPtr + p) = mem (loc.arrPtr + p) :=
          (hm3_out _ (by omega) (by omega)).trans ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega))))
        have hother3 : ∀ p, 0 < p → p < size' → p ≠ k → (p - 1) / 2 ≠ k →
            loc.edgeBetter mem3 h (mem3 (loc.arrPtr + (p - 1) / 2)) (mem3 (loc.arrPtr + p)) = true := by
          intro p hp0 hp hpk hpp
          rw [harr3 _ (by omega) hpp, harr3 p hp hpk, hedge3 _ _ (hbij.2.1 _ (by omega)) (hbij.2.1 p (by omega))]
          exact hord p hp0 (by omega)
        have hskip3 : 0 < k → ∀ c < size', (c - 1) / 2 = k →
            loc.edgeBetter mem3 h (mem3 (loc.arrPtr + (k - 1) / 2)) (mem3 (loc.arrPtr + c)) = true := by
          intro hk0' c hc hck
          rw [harr3 _ (by omega) (by omega), harr3 c hc (by omega),
              hedge3 _ _ (hbij.2.1 _ (by omega)) (hbij.2.1 c (by omega))]
          exact selectHeapOrder_grandparent_beats_child hbij hkeys hord hk0' hkLt (by omega) hck
        have hz3 : ZeroFrom mem3 scratch := fun a ha =>
          (hm3_out a (by omega) (by omega)).trans ((hm2_out a (by omega) (by omega)).trans
            ((hfr1 a (Or.inr (by omega))).trans (hz a ha)))
        refine runs_seq_call_flat hrebal (vs := [loc.hb, k, scratch])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨k, scratch, rfl, hw16, hendLe, hks, hhdr3, hbij3, hkeys3, hcand3, hother3, hskip3, hz3, hroom⟩
        · intro ret mem4 pos4 hp4
          obtain ⟨hlo4, hhi4, hat4, hz4, hfr4, hpos4⟩ := hp4
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo4 hhi4 hfr4
          have hretw : ret < 2 ^ w := by omega
          refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · dsimp only [heapDeleteContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ↓reduceIte]
            refine ⟨hlo4, hhi4, hat4, hz4, ?_, ?_, ?_⟩
            · by_contra hne0
              have h3 : mem3 (loc.posPtr + e) ≠ 0 := (hpos4 e heCap).mp hne0
              rw [hm3_out _ (by omega) (by omega)] at h3; simp [mem2] at h3
            · intro e' he' hne
              have hbd' := selectHeap_slot_bounds he'
              refine ⟨(hpos4 e' he').trans ((hpos3_iff e' he').trans (by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))])),
                (hfr4 _ (by omega) (Or.inr (by omega))).trans ((hm3_out _ (by omega) (by omega)).trans
                  ((hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega))))),
                (Num.intVal_congr fun j hj => (hfr4 _ (by omega) (Or.inr (by omega))).trans
                  (hm3_out _ (by omega) (by omega))).trans (hmem2_key e' he').1,
                (Num.intVal_congr fun j hj => (hfr4 _ (by omega) (Or.inr (by omega))).trans
                  (hm3_out _ (by omega) (by omega))).trans (hmem2_key e' he').2⟩
            · intro a ha hout
              exact (hfr4 a ha (by omega)).trans ((hm3_out a (by omega) (by omega)).trans
                ((hm2_out a (by omega) (by omega)).trans (hfr1 a (by omega))))
          · simp only [heapDeleteContract, heapDeleteCost, candListEraseContract, heapRebalanceContract,
              Expr.size, argsSize]; omega
      · -- `k = size'`: removing the last element directly preserves heap order
        have hkEq : k = size' := by omega
        refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hks, show 0 < 2 ^ w by omega])
          (fun h => absurd rfl h) ?_
        intro _
        have hbij2 : SelectHeapBijection mem2 loc size' := by
          refine ⟨by have := hbij.1; omega, fun p hp => ?_, fun p hp => ?_, fun e' he' => ?_⟩
          · rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact hbij.2.1 p (by omega)
          · have hpCap := hbij.2.1 p (by omega)
            have hpNeE : mem (loc.arrPtr + p) ≠ e := fun heq => by
              have := hbij.arr_inj (by omega) hkLt (heq.trans harrK.symm); omega
            have ha2 : mem2 (loc.arrPtr + p) = mem (loc.arrPtr + p) :=
              (hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega)))
            rw [ha2, hm2_out (loc.posPtr + mem (loc.arrPtr + p)) (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
            exact hbij.2.2.1 p (by omega)
          · by_cases hee : e' = e
            · subst e'; left; simp [mem2]
            · rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
              rcases hbij.2.2.2 e' he' with h0 | ⟨hle, harr⟩
              · exact Or.inl h0
              · have hneK : mem (loc.posPtr + e') - 1 ≠ size' := fun h => by
                  rw [← hkEq] at h; rw [h] at harr; exact hee (harr.symm.trans harrK)
                have := hbij.1
                exact Or.inr ⟨by omega, by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact harr⟩
        have hkeys2 : SelectHeapKeysValid mem2 loc h := fun e' he' hnz => by
          have hbd' := selectHeap_slot_bounds he'
          have hee : e' ≠ e := fun h => by subst e'; simp [mem2] at hnz
          have hnz0 : mem (loc.posPtr + e') ≠ 0 := by
            rwa [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))] at hnz
          obtain ⟨hl', hvn', hvd', hdp'⟩ := hkeys e' he' hnz0
          refine ⟨by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]; exact hl',
            fun j hj => by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inr (by omega))]; exact hvn' j hj,
            fun j hj => by rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inr (by omega))]; exact hvd' j hj, ?_⟩
          rw [(hmem2_key e' he').2]; exact hdp'
        have hord2 : SelectHeapOrder mem2 loc h size' := fun p hp0 hp => by
          have h1 := hbij.2.1 _ (by omega : (p - 1) / 2 < size)
          have h2 := hbij.2.1 p (by omega)
          rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega)),
              hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))]
          unfold SelectHeapLoc.edgeBetter
          rw [(hmem2_key _ h1).1, (hmem2_key _ h1).2, (hmem2_key _ h2).1, (hmem2_key _ h2).2]
          exact hord p hp0 (by omega)
        have hz2 : ZeroFrom mem2 scratch := fun a ha =>
          (hm2_out a (by omega) (by omega)).trans ((hfr1 a (Or.inr (by omega))).trans (hz a ha))
        refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
        · dsimp only [heapDeleteContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ↓reduceIte]
          refine ⟨le_rfl, Nat.le_add_right _ _, ⟨hhdr2, hbij2, hkeys2, hord2, hcand2⟩, hz2,
            by simp, fun e' he' hne => ⟨by
                change mem2 (loc.posPtr + e') ≠ 0 ↔ _
                rw [hm2_out _ (by omega) (by omega), hfr1 _ (Or.inl (by omega))],
              (hm2_out _ (by omega) (by omega)).trans (hfr1 _ (Or.inl (by omega))),
              (hmem2_key e' he').1, (hmem2_key e' he').2⟩,
            fun a ha hout => (hm2_out a (by omega) (by omega)).trans (hfr1 a (by omega))⟩
        · simp only [heapDeleteContract, heapDeleteCost, candListEraseContract,
            Expr.size, argsSize]; omega

end MinCostFlow.MinRatio
