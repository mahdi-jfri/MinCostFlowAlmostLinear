module

public import MinCostFlow.DynSpanner.Program.DynGraphRefill
public import MinCostFlow.MinRatio.SelectBlocksRefill
import WordRAM.Tactic

/-!
# Refilling a select graph block from another `DynGraphAt` (`SelectGraphRefill`)

Provides deterministic Word-RAM helpers for refilling a select-owned `DynGraphAt` block
(`B.fPtr j` or `B.lastGPtr`, at global caps `(B.vCap, B.eCap)`) directly from any source
`DynGraphAt` (which may have different capacities, e.g. an op-`2` forest, an op-`3` sparsifier,
or a last-level branch forest) in live time `O(G_old.n + G_old.m + G_new.n + G_new.m + 1)`:

* `dgPackEdgeTriplesBody` (`[srcPtr, outPtr] → m`): scans the live edge list of `srcPtr` and writes
  `m` triples `[e, tail e, head e]` to `outPtr` in `≤ 80 * G.m + 80` steps and `3 * G.m` words.
* `dgRefillFromDynGraphBody packProc refillProc` (`[dstPtr, srcPtr, scratch] → scratch + 3 * m`):
  packs the edge triples of `srcPtr` into `scratch` and calls `dgRefillFromLists` on `dstPtr`,
  preserving `ZeroFrom` from the returned pointer and leaving all memory outside `dstPtr` and
  `[scratch, scratch + 3 * m)` unchanged.
* `selFilterPresentBody` (`[listPtr, len, presBase, outPtr] → cnt`): filters a list of edge IDs
  keeping those whose presence bit is nonzero (`O(len + 1)` steps).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-! ## 1. Packing edge triples from a `DynGraphAt` -/

/-- Step cost bound for `dgPackEdgeTriplesBody` on a graph with `m` edges. -/
def dgPackEdgeTriplesCost (m : ℕ) : ℕ := 80 * m + 80

/-- Scan the live edge list of a `DynGraphAt` at `srcPtr` and write `m` triples `[e, tail e, head e]`
at `outPtr` (`[srcPtr, outPtr] → m`). -/
def dgPackEdgeTriplesBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 9 (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 3))) ;;
  forRange 10 (.const 0) (.reg 4)
    (.assign 11 (.load (.bin .add (.reg 7) (.reg 10))) ;;
     .assign 12 (.load (.bin .add (.reg 8) (.reg 11))) ;;
     .assign 13 (.load (.bin .add (.reg 9) (.reg 11))) ;;
     .assign 14 (.load (.bin .add (.reg 5) (.reg 12))) ;;
     .assign 15 (.load (.bin .add (.reg 5) (.reg 13))) ;;
     .assign 16 (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 10))) ;;
     .store (.reg 16) (.reg 11) ;;
     .store (.bin .add (.reg 16) (.const 1)) (.reg 14) ;;
     .store (.bin .add (.reg 16) (.const 2)) (.reg 15)) ;;
  .ret (.reg 4)

theorem dgPackEdgeTriplesBody_noRand : dgPackEdgeTriplesBody.NoRand := by
  simp [dgPackEdgeTriplesBody, forRange, forUp, Stmt.NoRand]

/-- Contract of `dgPackEdgeTriplesBody` (`[srcPtr, outPtr] → G.m`). -/
def dgPackEdgeTriplesContract (w srcVCap srcECap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ srcPtr outPtr, args = [srcPtr, outPtr] ∧
    16 < 2 ^ w ∧
    srcPtr + dynGraphSize srcVCap srcECap < 2 ^ w ∧
    outPtr + 3 * G.m < 2 ^ w ∧
    (srcPtr + dynGraphSize srcVCap srcECap ≤ outPtr ∨ outPtr + 3 * G.m ≤ srcPtr) ∧
    DynGraphAt mem srcPtr srcVCap srcECap G
  post args mem ret mem' := ∃ (srcPtr outPtr : ℕ) (eEdges : List (ℕ × ℕ × ℕ)),
    args = [srcPtr, outPtr] ∧ ret = G.m ∧
    eEdges.length = G.m ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem' (outPtr + 3 * i) = eEdges[i].1 ∧
      mem' (outPtr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem' (outPtr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t ∈ eEdges, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1) ∧
    (∀ e ∈ G.E, ∃ t ∈ eEdges, t.1 = e) ∧
    (∀ a, a < outPtr ∨ outPtr + 3 * G.m ≤ a → mem' a = mem a)
  cost _ _ := dgPackEdgeTriplesCost G.m

/-! ## 2. Refilling a `DynGraphAt` directly from another `DynGraphAt` -/

/-- Step cost bound for `dgRefillFromDynGraphBody`. -/
def dgRefillFromDynGraphCost (nOld mOld nNew mNew : ℕ) : ℕ :=
  dgRefillFromListsCost nOld mOld nNew mNew + dgPackEdgeTriplesCost mNew + 60

/-- Refill `dstPtr` from `srcPtr` using `3 * G_new.m` scratch words at `scratch`, returning
`scratch + 3 * G_new.m` (`[dstPtr, srcPtr, scratch]`). -/
def dgRefillFromDynGraphBody (packProc refillProc : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 3)) ;;
  .call 6 packProc [.reg 1, .reg 2] ;;
  .call 7 refillProc [.reg 0, .reg 4, .reg 5, .reg 6, .reg 2] ;;
  .ret (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 6)))

theorem dgRefillFromDynGraphBody_noRand (packProc refillProc : ℕ) :
    (dgRefillFromDynGraphBody packProc refillProc).NoRand := by
  simp [dgRefillFromDynGraphBody, Stmt.NoRand]

/-- Contract of `dgRefillFromDynGraphBody` (`[dstPtr, srcPtr, scratch] → scratch + 3 * G_new.m`). -/
def dgRefillFromDynGraphContract (w vCap eCap srcVCap srcECap : ℕ) (G_old G_new : MGraph) :
    Contract where
  pre args mem := ∃ dstPtr srcPtr scratch, args = [dstPtr, srcPtr, scratch] ∧
    16 < 2 ^ w ∧
    dstPtr + dynGraphSize vCap eCap ≤ scratch ∧
    srcPtr + dynGraphSize srcVCap srcECap ≤ scratch ∧
    (dstPtr + dynGraphSize vCap eCap ≤ srcPtr ∨ srcPtr + dynGraphSize srcVCap srcECap ≤ dstPtr) ∧
    DynGraphAt mem dstPtr vCap eCap G_old ∧
    DynGraphAt mem srcPtr srcVCap srcECap G_new ∧
    (∀ v ∈ G_new.V, v < vCap) ∧ (∀ e ∈ G_new.E, e < eCap) ∧
    ZeroFrom mem scratch ∧
    scratch + 3 * G_new.m < 2 ^ w
  post args mem ret mem' := ∃ dstPtr srcPtr scratch, args = [dstPtr, srcPtr, scratch] ∧
    ret = scratch + 3 * G_new.m ∧
    DynGraphAt mem' dstPtr vCap eCap G_new ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, a < dstPtr ∨ dstPtr + dynGraphSize vCap eCap ≤ a → mem' a = mem a)
  cost _ _ := dgRefillFromDynGraphCost G_old.n G_old.m G_new.n G_new.m

/-! ## 3. Filtering edges whose presence bit is nonzero -/

/-- Keep the listed edges whose presence bit is nonzero (`[listPtr, len, presBase, outPtr]`). -/
def selFilterPresentBody : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .cond (.load (.bin .add (.reg 2) (.reg 6)))
       (.store (.bin .add (.reg 3) (.reg 4)) (.reg 6) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)))
       .nop) ;;
  .ret (.reg 4)

theorem selFilterPresentBody_noRand : selFilterPresentBody.NoRand := by
  simp [selFilterPresentBody, forRange, forUp, Stmt.NoRand]

/-- The listed edges whose presence bit at `presBase` is nonzero. -/
def selPresent (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun e => decide (mem (presBase + e) ≠ 0)

/-- Contract of `selFilterPresentBody` for the list `L`. -/
def selFilterPresentContract (w : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ listPtr presBase outPtr, args = [listPtr, L.length, presBase, outPtr] ∧
    16 < 2 ^ w ∧ listPtr + L.length < 2 ^ w ∧ outPtr + L.length < 2 ^ w ∧
    (listPtr + L.length ≤ outPtr ∨ outPtr + L.length ≤ listPtr) ∧
    ListAt mem listPtr L ∧
    (∀ e ∈ L, e < 2 ^ w ∧ presBase + e < 2 ^ w ∧ mem (presBase + e) < 2 ^ w ∧
      (presBase + e < outPtr ∨ outPtr + L.length ≤ presBase + e))
  post args mem ret mem' := ∃ listPtr presBase outPtr,
    args = [listPtr, L.length, presBase, outPtr] ∧
    ret = (selPresent mem presBase L).length ∧ ListAt mem' outPtr (selPresent mem presBase L) ∧
    ∀ a, (a < outPtr ∨ outPtr + L.length ≤ a) → mem' a = mem a
  cost _ _ := 40 * L.length + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

set_option maxHeartbeats 600000 in
theorem dgPackEdgeTriples_meetsContract {w proc srcVCap srcECap : ℕ} {G : MGraph} {p : Program}
    (hp : p.procs[proc]? = some dgPackEdgeTriplesBody) :
    MeetsContract w p proc (dgPackEdgeTriplesContract w srcVCap srcECap G) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨srcPtr, outPtr, rfl, hw16, hsrcW, houtW, hdisj, hG⟩ := hpre
  obtain ⟨hVal, hVCap, hECap, hV0, hE0, hN0, hM0, _, _, hE2I, hI2E, _,
    ⟨eL, heLen, heNd, heMem, heAt, _⟩, hEnds, _⟩ := hG
  have hsz : dynGraphSize srcVCap srcECap = 4 + 7 * srcVCap + 9 * srcECap := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hIntToExt : ∀ v ∈ G.V,
      mem (dgIntToExtBase srcPtr srcVCap + mem (dgExtToIntBase srcPtr srcVCap + v)) = v :=
    fun v hv => (hE2I v hv).2
  have hSlotBound : ∀ v ∈ G.V, mem (dgExtToIntBase srcPtr srcVCap + v) < srcVCap :=
    fun v hv => hVCap _ (hE2I v hv).1
  have hmLe : G.m ≤ srcECap := by
    have hsub : G.E ⊆ Finset.range srcECap := fun e he => Finset.mem_range.mpr (hECap e he)
    simpa [MGraph.m, Finset.card_range] using Finset.card_le_card hsub
  let eEdges : List (ℕ × ℕ × ℕ) := eL.map fun e => (e, G.tail e, G.head e)
  have hloop := Triple.forRange_const (p := p) (r := 10) (lo := .const 0) (hi := .reg 4)
    (body :=
      .assign 11 (.load (.bin .add (.reg 7) (.reg 10))) ;;
      .assign 12 (.load (.bin .add (.reg 8) (.reg 11))) ;;
      .assign 13 (.load (.bin .add (.reg 9) (.reg 11))) ;;
      .assign 14 (.load (.bin .add (.reg 5) (.reg 12))) ;;
      .assign 15 (.load (.bin .add (.reg 5) (.reg 13))) ;;
      .assign 16 (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 10))) ;;
      .store (.reg 16) (.reg 11) ;;
      .store (.bin .add (.reg 16) (.const 1)) (.reg 14) ;;
      .store (.bin .add (.reg 16) (.const 2)) (.reg 15))
    (P := fun st =>
      st.regs 0 = srcPtr ∧ st.regs 1 = outPtr ∧ st.regs 2 = srcVCap ∧ st.regs 3 = srcECap ∧
      st.regs 4 = G.m ∧ st.regs 5 = dgIntToExtBase srcPtr srcVCap ∧
      st.regs 6 = dgEPresBase srcPtr srcVCap ∧ st.regs 7 = dgEListBase srcPtr srcVCap srcECap ∧
      st.regs 8 = dgETailSlotBase srcPtr srcVCap srcECap ∧
      st.regs 9 = dgEHeadSlotBase srcPtr srcVCap srcECap ∧ st.mem = mem)
    (Inv := fun i st =>
      st.regs 0 = srcPtr ∧ st.regs 1 = outPtr ∧ st.regs 2 = srcVCap ∧ st.regs 3 = srcECap ∧
      st.regs 4 = G.m ∧ st.regs 5 = dgIntToExtBase srcPtr srcVCap ∧
      st.regs 6 = dgEPresBase srcPtr srcVCap ∧ st.regs 7 = dgEListBase srcPtr srcVCap srcECap ∧
      st.regs 8 = dgETailSlotBase srcPtr srcVCap srcECap ∧
      st.regs 9 = dgEHeadSlotBase srcPtr srcVCap srcECap ∧ st.regs 10 = i ∧
      (∀ k < i, ∀ (hk : k < eL.length),
        st.mem (outPtr + 3 * k) = eL[k] ∧
        st.mem (outPtr + 3 * k + 1) = G.tail eL[k] ∧
        st.mem (outPtr + 3 * k + 2) = G.head eL[k]) ∧
      (∀ a, a < outPtr ∨ outPtr + 3 * i ≤ a → st.mem a = mem a))
    70 0 G.m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩
      refine ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, by simp,
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => by simp [hm]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h4 := hi.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hdone, hout⟩
      have hiL : i < eL.length := heLen ▸ hi
      set e := eL[i]'hiL
      have heG : e ∈ G.E := (heMem e).mp (List.getElem_mem hiL)
      have heC : e < srcECap := hECap e heG
      have htV : G.tail e ∈ G.V := (hVal e heG).1
      have hhV : G.head e ∈ G.V := (hVal e heG).2
      have htC : G.tail e < srcVCap := hVCap _ htV
      have hhC : G.head e < srcVCap := hVCap _ hhV
      set tSlot := mem (dgETailSlotBase srcPtr srcVCap srcECap + e)
      set hSlot := mem (dgEHeadSlotBase srcPtr srcVCap srcECap + e)
      have htSlotEq : tSlot = mem (dgExtToIntBase srcPtr srcVCap + G.tail e) := (hEnds e heG).1
      have hhSlotEq : hSlot = mem (dgExtToIntBase srcPtr srcVCap + G.head e) := (hEnds e heG).2
      have htSlotC : tSlot < srcVCap := htSlotEq ▸ hSlotBound _ htV
      have hhSlotC : hSlot < srcVCap := hhSlotEq ▸ hSlotBound _ hhV
      have htExt : mem (dgIntToExtBase srcPtr srcVCap + tSlot) = G.tail e :=
        htSlotEq ▸ hIntToExt _ htV
      have hhExt : mem (dgIntToExtBase srcPtr srcVCap + hSlot) = G.head e :=
        hhSlotEq ▸ hIntToExt _ hhV
      have hsrcKeep : ∀ a, srcPtr ≤ a → a < srcPtr + dynGraphSize srcVCap srcECap →
          st.mem a = mem a := fun a h1 h2 => hout a (by omega)
      have h11 : st.mem (dgEListBase srcPtr srcVCap srcECap + i) = e := by
        rw [hsrcKeep _ (by unfold dgEListBase; omega) (by unfold dgEListBase; omega)]
        exact heAt i hiL
      have h12 : st.mem (dgETailSlotBase srcPtr srcVCap srcECap + e) = tSlot :=
        hsrcKeep _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)
      have h13 : st.mem (dgEHeadSlotBase srcPtr srcVCap srcECap + e) = hSlot :=
        hsrcKeep _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)
      have h14 : st.mem (dgIntToExtBase srcPtr srcVCap + tSlot) = G.tail e :=
        (hsrcKeep _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)).trans htExt
      have h15 : st.mem (dgIntToExtBase srcPtr srcVCap + hSlot) = G.head e :=
        (hsrcKeep _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)).trans hhExt
      have heListW : dgEListBase srcPtr srcVCap srcECap + i < 2 ^ w := by
        unfold dgEListBase; omega
      have htSlotW : dgETailSlotBase srcPtr srcVCap srcECap + e < 2 ^ w := by
        unfold dgETailSlotBase; omega
      have hhSlotW : dgEHeadSlotBase srcPtr srcVCap srcECap + e < 2 ^ w := by
        unfold dgEHeadSlotBase; omega
      have htIntW : dgIntToExtBase srcPtr srcVCap + tSlot < 2 ^ w := by
        unfold dgIntToExtBase; omega
      have hhIntW : dgIntToExtBase srcPtr srcVCap + hSlot < 2 ^ w := by
        unfold dgIntToExtBase; omega
      apply runs_start_le
      refine runs_seq_assign_le (v := e) (by eval_expr) ?_
      refine runs_seq_assign_le (v := tSlot) (by eval_expr) ?_
      refine runs_seq_assign_le (v := hSlot) (by eval_expr) ?_
      refine runs_seq_assign_le (v := G.tail e) (Expr.eval_load_of_eq (by eval_expr) h14) ?_
      refine runs_seq_assign_le (v := G.head e) (Expr.eval_load_of_eq (by eval_expr) h15) ?_
      refine runs_seq_assign_le (v := outPtr + 3 * i) (by eval_expr) ?_
      refine runs_seq_store_le (x := outPtr + 3 * i) (v := e) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := outPtr + 3 * i + 1) (v := G.tail e) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := outPtr + 3 * i + 2) (v := G.head e) (by eval_expr) (by eval_expr) ?_ ?_
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
          by simpa using h8, by simpa using h9, by simp, ?_, ?_⟩, by simp [h10]⟩
        · intro k hk hkL
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hdone k hlt hkL
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self, Function.update_of_ne (by omega), Function.update_self,
              Function.update_self]
            exact ⟨rfl, rfl, rfl⟩
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hout a (by omega)
      · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]; omega)
  apply runs_start_le
  unfold dgPackEdgeTriplesBody
  have hV0' : mem srcPtr = srcVCap := hV0
  have hE0' : mem (srcPtr + 1) = srcECap := hE0
  have hM0' : mem (srcPtr + 3) = G.m := hM0
  refine runs_seq_assign_le (v := srcVCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := srcECap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase srcPtr srcVCap)
    (by unfold dgIntToExtBase; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEPresBase srcPtr srcVCap)
    (by unfold dgEPresBase; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEListBase srcPtr srcVCap srcECap)
    (by unfold dgEListBase dgEPresBase; eval_expr) ?_
  refine runs_seq_assign_le (v := dgETailSlotBase srcPtr srcVCap srcECap)
    (by unfold dgETailSlotBase dgEPresBase; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase srcPtr srcVCap srcECap)
    (by unfold dgEHeadSlotBase dgEPresBase; eval_expr) ?_
  refine runs_seq_triple_le hloop (by simp [startState]) ?_
  intro st1 ⟨_, _, _, _, h4, _, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := G.m) (by eval_expr) ?_ ?_
  · refine ⟨srcPtr, outPtr, eEdges, rfl, rfl, by simp [eEdges, heLen],
      by simpa [eEdges, Function.comp_def] using heNd, fun i hi => ?_, fun t ht => ?_,
      fun e he => ?_, hout⟩
    · have hiL : i < eL.length := by simpa [eEdges] using hi
      simpa [eEdges, List.getElem_map] using hdone i (heLen ▸ hiL) hiL
    · obtain ⟨e, heL, rfl⟩ := List.mem_map.mp ht
      exact ⟨(heMem e).mp heL, rfl, rfl⟩
    · exact ⟨(e, G.tail e, G.head e), List.mem_map.mpr ⟨e, (heMem e).mpr he, rfl⟩, rfl⟩
  · simp only [dgPackEdgeTriplesContract, dgPackEdgeTriplesCost, Expr.size, Nat.sub_zero]
    nlinarith

set_option maxHeartbeats 600000 in
theorem dgRefillFromDynGraph_meetsContract {w proc packProc refillProc vCap eCap srcVCap srcECap : ℕ}
    {G_old G_new : MGraph} {p : Program}
    (hp : p.procs[proc]? = some (dgRefillFromDynGraphBody packProc refillProc))
    (hpack : MeetsContract w p packProc (dgPackEdgeTriplesContract w srcVCap srcECap G_new))
    (hrefill : ∀ vL eEdges,
      MeetsContract w p refillProc (dgRefillFromListsContract w vCap eCap G_old G_new vL eEdges)) :
    MeetsContract w p proc (dgRefillFromDynGraphContract w vCap eCap srcVCap srcECap G_old G_new) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨dstPtr, srcPtr, scratch, rfl, hw16, hdstLe, hsrcLe, hdisj, hGold, hGnew,
    hNewV, hNewE, hz, hroom⟩ := hpre
  have hszSrc : dynGraphSize srcVCap srcECap = 4 + 7 * srcVCap + 9 * srcECap := rfl
  have hszDst : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hGnew' := hGnew
  obtain ⟨hNewVal, hSrcV, hSrcE, hSrcVC, hSrcEC, hSrcN, hSrcM, _,
    ⟨vL, hvLen, _, hvMem, hvAt, _⟩, _⟩ := hGnew'
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hSrcNLe : G_new.n ≤ srcVCap := by
    have hsub : G_new.V ⊆ Finset.range srcVCap := fun v hv => Finset.mem_range.mpr (hSrcV v hv)
    simpa [MGraph.n, Finset.card_range] using Finset.card_le_card hsub
  have hvPtrW : dgVListBase srcPtr srcVCap + G_new.n < 2 ^ w := by
    unfold dgVListBase; omega
  have hSrcVC' : mem srcPtr = srcVCap := hSrcVC
  apply runs_start_le
  unfold dgRefillFromDynGraphBody
  refine runs_seq_assign_le (v := srcVCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G_new.n)
    (by have : mem (srcPtr + 2) = G_new.n := hSrcN; eval_expr) ?_
  refine runs_seq_assign_le (v := dgVListBase srcPtr srcVCap)
    (by unfold dgVListBase; eval_expr) ?_
  refine runs_seq_call_flat hpack (vs := [srcPtr, scratch]) (by eval_expr) (by wram_words)
    ⟨srcPtr, scratch, rfl, hw16, by omega, hroom, Or.inl hsrcLe, hGnew⟩ ?_
  intro eLen mem1 pos1 hp1
  dsimp only [dgPackEdgeTriplesContract] at hp1
  obtain ⟨_, _, eEdges, hEq1, rfl, heLen, heNd, heAt, heValid, heCov, hfr1⟩ := hp1
  simp only [List.cons.injEq, and_true] at hEq1
  obtain ⟨rfl, rfl⟩ := hEq1
  have hGold1 : DynGraphAt mem1 dstPtr vCap eCap G_old :=
    DynGraphAt.of_agree hGold fun a h1 h2 => hfr1 a (Or.inl (by omega))
  have hvAt1 : ListAt mem1 (dgVListBase srcPtr srcVCap) vL := fun i hi => by
    rw [hfr1 _ (Or.inl (by unfold dgVListBase; omega))]
    exact hvAt i hi
  have hGoldN : mem1 (dstPtr + dgNOff) = G_old.n := hGold1.2.2.2.2.2.1
  have hGoldM : mem1 (dstPtr + dgMOff) = G_old.m := hGold1.2.2.2.2.2.2.1
  refine runs_seq_call_flat (hrefill vL eEdges)
    (vs := [dstPtr, G_new.n, dgVListBase srcPtr srcVCap, G_new.m, scratch])
    (by eval_expr) (by wram_words)
    ⟨dstPtr, G_new.n, dgVListBase srcPtr srcVCap, G_new.m, scratch, rfl, by omega, by omega,
      hGold1, hNewVal, hNewV, hNewE, hvLen, hvAt1, hvMem, hvPtrW,
      fun i hi => by unfold dgVListBase; rcases hdisj with h | h <;> [right; left] <;> omega,
      heLen, heNd, heAt, heValid, heCov, hroom, fun i hi => Or.inr (by omega)⟩ ?_
  intro ret2 mem2 pos2 hp2
  dsimp only [dgRefillFromListsContract] at hp2
  obtain ⟨_, _, _, _, _, hEq2, _, hGnew2, hfr2⟩ := hp2
  simp only [List.cons.injEq, and_true] at hEq2
  obtain ⟨rfl, -, -, -, -⟩ := hEq2
  refine WordRAM.runs_ret_le (v := scratch + 3 * G_new.m) (by eval_expr) ?_ ?_
  · refine ⟨dstPtr, srcPtr, scratch, rfl, rfl, hGnew2, ?_, ?_⟩
    · intro a ha
      change scratch + 3 * G_new.m ≤ a at ha
      dsimp only
      rw [hfr2 a (Or.inr (by omega)), hfr1 a (Or.inr ha)]
      exact hz a (by omega)
    · intro a ha hout
      exact (hfr2 a hout).trans (hfr1 a (Or.inl ha))
  · simp only [dgRefillFromDynGraphContract, dgRefillFromDynGraphCost,
      dgPackEdgeTriplesContract, dgRefillFromListsContract,
      List.getD_cons_zero, List.getD_cons_succ, hGoldN, hGoldM, Expr.size, argsSize]
    omega

/-- Refilling `B.fPtr j` via `dgRefillFromDynGraphContract` updates `D.F j` and keeps all other
parts of `SelBlocksDataAt`. -/
theorem dgRefillFromDynGraph_setF {w P j pLast srcVCap srcECap : ℕ} {B : SelectBlocksLoc}
    {D : SelBlocksData} {F' : MGraph} {args : List ℕ} {mem mem' : ℕ → ℕ} {ret scratch : ℕ}
    (hblk : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d) (hBEnd : B.endAddr ≤ scratch)
    (hargs : args.getD 0 0 = B.fPtr j ∧ args.getD 2 0 = scratch)
    (hpost : (dgRefillFromDynGraphContract w B.vCap B.eCap srcVCap srcECap (D.F j) F').post
      args mem ret mem') :
    SelBlocksDataAt mem' B P { D with F := Function.update D.F j F' } pLast := by
  obtain ⟨dstPtr, srcPtr, sc, hEq, _, hG', _, hfr⟩ := hpost
  subst hEq
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  let memMid : ℕ → ℕ := fun a => if a < sc then mem' a else mem a
  have hGmid : DynGraphAt memMid (B.fPtr j) B.vCap B.eCap F' := by
    refine DynGraphAt.of_agree hG' fun a h1 h2 => ?_
    have hblkEnd := B.blk_le_last hj
    have hsz : B.fPtr j + dynGraphSize B.vCap B.eCap ≤ B.fPtr j + B.levelSize := by
      unfold SelectBlocksLoc.levelSize; omega
    have hlt : a < sc := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
    simp [memMid, hlt]
  have hmid : SelBlocksDataAt memMid B P { D with F := Function.update D.F j F' } pLast :=
    hblk.setF hj (fun a ha => by
      by_cases hlt : a < sc
      · simp only [memMid, hlt, ↓reduceIte]
        exact hfr a hlt (by unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at ha; omega)
      · simp [memMid, hlt]) hGmid
  exact hmid.of_agree fun a _ ha2 => by
    have hlt : a < sc := lt_of_lt_of_le ha2 hBEnd
    simp [memMid, hlt]

/-- Refilling `B.lastGPtr` via `dgRefillFromDynGraphContract` updates `D.Gd` and keeps all other
parts of `SelBlocksDataAt`. -/
theorem dgRefillFromDynGraph_setLast {w P pLast srcVCap srcECap : ℕ} {B : SelectBlocksLoc}
    {D : SelBlocksData} {Gd' : MGraph} {args : List ℕ} {mem mem' : ℕ → ℕ} {ret scratch : ℕ}
    (hblk : SelBlocksDataAt mem B P D pLast) (hBEnd : B.endAddr ≤ scratch)
    (hargs : args.getD 0 0 = B.lastGPtr ∧ args.getD 2 0 = scratch)
    (hpost : (dgRefillFromDynGraphContract w B.vCap B.eCap srcVCap srcECap D.Gd Gd').post
      args mem ret mem') :
    SelBlocksDataAt mem' B P { D with Gd := Gd' } pLast := by
  obtain ⟨dstPtr, srcPtr, sc, hEq, _, hG', _, hfr⟩ := hpost
  subst hEq
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  let memMid : ℕ → ℕ := fun a => if a < sc then mem' a else mem a
  have hGmid : DynGraphAt memMid B.lastGPtr B.vCap B.eCap Gd' := by
    refine DynGraphAt.of_agree hG' fun a h1 h2 => ?_
    have hlt : a < sc := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
    simp [memMid, hlt]
  have hmid : SelBlocksDataAt memMid B P { D with Gd := Gd' } pLast :=
    hblk.setLast (fun a ha => by
      by_cases hlt : a < sc
      · simp only [memMid, hlt, ↓reduceIte]
        exact hfr a hlt (by unfold SelectBlocksLoc.regLast SelectBlocksLoc.g0Ptr at ha; omega)
      · simp [memMid, hlt]) hGmid
  exact hmid.of_agree fun a _ ha2 => by
    have hlt : a < sc := lt_of_lt_of_le ha2 hBEnd
    simp [memMid, hlt]

theorem selPresent_take_succ (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) {i : ℕ}
    (hi : i < L.length) :
    selPresent mem presBase (L.take (i + 1)) =
      selPresent mem presBase (L.take i) ++ (if mem (presBase + L[i]) ≠ 0 then [L[i]] else []) := by
  unfold selPresent
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  congr 1
  by_cases h : mem (presBase + L[i]) ≠ 0 <;> simp [h]

theorem selPresent_length_le (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) :
    (selPresent mem presBase L).length ≤ L.length :=
  List.length_filter_le _ _

set_option maxHeartbeats 400000 in
theorem selFilterPresent_meetsContract {w proc : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some selFilterPresentBody) :
    MeetsContract w p proc (selFilterPresentContract w L) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨listPtr, presBase, outPtr, rfl, hw16, hlistW, houtW, hldisj, hlist, hent⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (body := .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
      .cond (.load (.bin .add (.reg 2) (.reg 6)))
        (.store (.bin .add (.reg 3) (.reg 4)) (.reg 6) ;;
         .assign 4 (.bin .add (.reg 4) (.const 1)))
        .nop)
    (P := fun st => st = { startState [listPtr, L.length, presBase, outPtr] mem pos with
      regs := Function.update (startState [listPtr, L.length, presBase, outPtr] mem pos).regs 4 0 })
    (Inv := fun i st => st.regs 0 = listPtr ∧ st.regs 1 = L.length ∧ st.regs 2 = presBase ∧
      st.regs 3 = outPtr ∧ st.regs 5 = i ∧
      st.regs 4 = (selPresent mem presBase (L.take i)).length ∧
      ListAt st.mem outPtr (selPresent mem presBase (L.take i)) ∧
      (∀ a, (a < outPtr ∨ outPtr + L.length ≤ a) → st.mem a = mem a))
    30 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ⟨rfl, rfl, rfl, rfl, by simp, by simp [selPresent], ?_,
        fun _ _ => rfl⟩⟩
      intro t ht; simp [selPresent] at ht)
    (fun _ _ _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h5, h4, hdone, hout⟩
      have heL : L[i] ∈ L := List.getElem_mem hi
      obtain ⟨heW, hpW, hbW, hpd⟩ := hent _ heL
      have hcnt : (selPresent mem presBase (L.take i)).length ≤ i := by
        have := selPresent_length_le mem presBase (L.take i)
        simp only [List.length_take] at this; omega
      have hread : st.mem (listPtr + i) = L[i] := by
        rw [hout _ (by rcases hldisj with h | h <;> omega)]
        exact hlist i hi
      have hbit : st.mem (presBase + L[i]) = mem (presBase + L[i]) := hout _ hpd
      have hstep := selPresent_take_succ mem presBase L hi
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      have hbW' : st.mem (presBase + L[i]) < 2 ^ w := hbit ▸ hbW
      refine WordRAM.runs_cond_le (v := mem (presBase + L[i])) (by rw [← hbit]; eval_expr) ?_ ?_
      · intro hne
        have hk : outPtr + (selPresent mem presBase (L.take i)).length < 2 ^ w := by omega
        refine runs_seq_store_le (x := outPtr + (selPresent mem presBase (L.take i)).length)
          (v := L[i]) (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := (selPresent mem presBase (L.take i)).length + 1)
          (by eval_expr) ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
            by simpa using h3, by simp, ?_, ?_, fun a ha => ?_⟩, by simpa using h5⟩ ?_
        · simp [hstep, hne]
        · rw [hstep, ite_eq_left hne]
          intro t ht
          simp only [List.length_append, List.length_singleton] at ht
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
          · rw [Function.update_of_ne (by omega), hdone t hlt, List.getElem_append_left hlt]
          · rw [Function.update_self, List.getElem_append_right (le_refl _)]
            simp
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hout a ha
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]; omega
      · intro hz
        refine runs_nop_le ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
          by simpa using h3, by simp, ?_, ?_, hout⟩, by simpa using h5⟩ ?_
        · simp only [Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide),
            Function.update_of_ne (show (4 : ℕ) ≠ 6 by decide), h4, hstep,
            show ¬ mem (presBase + L[i]) ≠ 0 from not_not.mpr hz, ↓reduceIte, List.append_nil]
        · rw [hstep, ite_eq_right (not_not.mpr hz), List.append_nil]; exact hdone
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load]; omega)
  apply runs_start_le
  unfold selFilterPresentBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, h4, hdone, hout⟩
  rw [List.take_length] at h4 hdone
  refine WordRAM.runs_ret_le (v := (selPresent mem presBase L).length) (by eval_expr) ?_ ?_
  · exact ⟨listPtr, presBase, outPtr, rfl, rfl, hdone, hout⟩
  · simp only [selFilterPresentContract, Expr.size, Nat.sub_zero]
    omega

theorem mem_selPresent_iff {mem : ℕ → ℕ} {gBase vCap eCap : ℕ} {G : MGraph} {L : List ℕ}
    (hG : DynGraphAt mem gBase vCap eCap G) (hcap : ∀ e ∈ L, e < eCap) (e : ℕ) :
    e ∈ selPresent mem (dgEPresBase gBase vCap) L ↔ e ∈ L ∧ e ∈ G.E := by
  unfold selPresent
  rw [List.mem_filter]
  constructor
  · rintro ⟨heL, hne⟩
    have hbit := hG.2.2.2.2.2.2.2.2.2.2.2.1 e (hcap e heL)
    refine ⟨heL, ?_⟩
    by_contra hnot
    rw [ite_eq_right hnot] at hbit
    simp [hbit] at hne
  · rintro ⟨heL, heG⟩
    have hbit := hG.2.2.2.2.2.2.2.2.2.2.2.1 e (hcap e heL)
    rw [ite_eq_left heG] at hbit
    exact ⟨heL, by simp [hbit]⟩

end MinCostFlow.MinRatio
