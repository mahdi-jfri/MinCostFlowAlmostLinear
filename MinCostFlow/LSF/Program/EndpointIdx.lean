module

public import MinCostFlow.LSF.Program.Spec
public import WordRAM.Tactic

/-!
# The endpoint-index arrays

The congestion order (`CongOrder.lean`) reads, for each edge `t < m0` of the edge list of
`G₀`, the indices in `vList` of its tail and head (`eu t` and `ev t`). The graph `G₀` is stored
as a `DynGraphAt` block: the tail of edge `e` is `intToExt[tailSlot[e]]`, and likewise for the
head. The index of a vertex `u` in `vList` is `vIdx[u] - 1`, since the index table stores
`i + 1` at `vList[i]`.

`endpointIdxProc` writes `eu` and `ev` this way, in time `O(m0)`
(`endpointIdx_meetsContract`). `endpointIdx_spec` turns the written values into the facts that
`congOrder_isApproxCongOrder` asks for.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The procedure -/

/-- One edge (register `8` is `t`): register `9` gets the edge ID `e`, then the two indices
are stored. -/
def endpointIdxBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .store (.bin .add (.reg 6) (.reg 8))
    (.bin .sub (.load (.bin .add (.reg 5)
      (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 2) (.reg 9))))))) (.const 1)) ;;
  .store (.bin .add (.reg 7) (.reg 8))
    (.bin .sub (.load (.bin .add (.reg 5)
      (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 3) (.reg 9))))))) (.const 1))

/-- Args: `[m0, eListPtr, tailSlotPtr, headSlotPtr, intToExtPtr, vIdxPtr, euPtr, evPtr]`. -/
def endpointIdxProc : Stmt :=
  forRange 8 (.const 0) (.reg 0) endpointIdxBody ;;
  .ret (.const 0)

lemma endpointIdxProc_noRand : endpointIdxProc.NoRand := by
  simp [endpointIdxProc, endpointIdxBody, forRange, forUp, Stmt.NoRand]

/-- The vertex that the slot array at `slotPtr` gives for edge `t` of the list. -/
def slotVert (mem : ℕ → ℕ) (eListPtr slotPtr intToExtPtr t : ℕ) : ℕ :=
  mem (intToExtPtr + mem (slotPtr + mem (eListPtr + t)))

/-- The contract of `endpointIdxProc`. Every cell that is read lies below the output. -/
def endpointIdxContract (w : ℕ) : Contract where
  pre args mem := ∃ (m0 eListPtr tsPtr hsPtr i2ePtr vIdxPtr euPtr evPtr : ℕ),
    args = [m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr, evPtr] ∧
    16 ≤ 2 ^ w ∧ eListPtr + m0 ≤ euPtr ∧ euPtr + m0 ≤ evPtr ∧ evPtr + m0 < 2 ^ w ∧
    ∀ t < m0, tsPtr + mem (eListPtr + t) < euPtr ∧ hsPtr + mem (eListPtr + t) < euPtr ∧
      i2ePtr + mem (tsPtr + mem (eListPtr + t)) < euPtr ∧
      i2ePtr + mem (hsPtr + mem (eListPtr + t)) < euPtr ∧
      vIdxPtr + slotVert mem eListPtr tsPtr i2ePtr t < euPtr ∧
      vIdxPtr + slotVert mem eListPtr hsPtr i2ePtr t < euPtr ∧
      mem (vIdxPtr + slotVert mem eListPtr tsPtr i2ePtr t) < 2 ^ w ∧
      mem (vIdxPtr + slotVert mem eListPtr hsPtr i2ePtr t) < 2 ^ w
  post args mem ret mem' := ∃ (m0 eListPtr tsPtr hsPtr i2ePtr vIdxPtr euPtr evPtr : ℕ),
    args = [m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr, evPtr] ∧ ret = 0 ∧
    (∀ t < m0, mem' (euPtr + t) = mem (vIdxPtr + slotVert mem eListPtr tsPtr i2ePtr t) - 1 ∧
      mem' (evPtr + t) = mem (vIdxPtr + slotVert mem eListPtr hsPtr i2ePtr t) - 1) ∧
    ∀ a, a < euPtr ∨ evPtr + m0 ≤ a → mem' a = mem a
  cost args _ := 50 * args.getD 0 0 + 20

/-! ## Proof -/

theorem endpointIdx_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some endpointIdxProc) :
    MeetsContract w p b (endpointIdxContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr, evPtr, rfl, hw, h1, h2, h3,
    hrd⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr, evPtr] with hargs
  let Done : ℕ → (ℕ → ℕ) → Prop := fun j m => ∀ t < j,
    m (euPtr + t) = mem (vIdxPtr + slotVert mem eListPtr tsPtr i2ePtr t) - 1 ∧
    m (evPtr + t) = mem (vIdxPtr + slotVert mem eListPtr hsPtr i2ePtr t) - 1
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < euPtr ∨ evPtr + m0 ≤ a → st.mem a = mem a) ∧ Done j st.mem
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 0) (.reg 0) endpointIdxBody) (normalPost (Inv m0))
      (fun _ => (m0 - 0) * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 40 0 m0 (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl,
        fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]
      interval_cases i <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro t _ ht st ω' hI
      obtain ⟨hR, h8, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = eListPtr := hR 1 (by omega)
      have r2 : st.regs 2 = tsPtr := hR 2 (by omega)
      have r3 : st.regs 3 = hsPtr := hR 3 (by omega)
      have r4 : st.regs 4 = i2ePtr := hR 4 (by omega)
      have r5 : st.regs 5 = vIdxPtr := hR 5 (by omega)
      have r6 : st.regs 6 = euPtr := hR 6 (by omega)
      have r7 : st.regs 7 = evPtr := hR 7 (by omega)
      obtain ⟨hts, hhs, hit, hih, hvt, hvh, hbt, hbh⟩ := hrd t ht
      have hE : st.mem (eListPtr + t) = mem (eListPtr + t) := hfr _ (Or.inl (by omega))
      set u := slotVert mem eListPtr tsPtr i2ePtr t with hu
      set v := slotVert mem eListPtr hsPtr i2ePtr t with hv
      have hu' : mem (i2ePtr + mem (tsPtr + mem (eListPtr + t))) = u := rfl
      have hv' : mem (i2ePtr + mem (hsPtr + mem (eListPtr + t))) = v := rfl
      have hT1 : st.mem (tsPtr + mem (eListPtr + t)) = mem (tsPtr + mem (eListPtr + t)) := hfr _ (Or.inl hts)
      have hT2 : st.mem (i2ePtr + st.mem (tsPtr + mem (eListPtr + t))) = u := by
        rw [hT1, ← hu']; exact hfr _ (Or.inl hit)
      have hT3 : st.mem (vIdxPtr + st.mem (i2ePtr + st.mem (tsPtr + mem (eListPtr + t)))) = mem (vIdxPtr + u) := by
        rw [hT2]; exact hfr _ (Or.inl hvt)
      refine runs_start_le ?_
      unfold endpointIdxBody
      refine runs_seq_assign_le (v := mem (eListPtr + t)) (by rw [← hE]; eval_expr) ?_
      refine runs_seq_store_le (x := euPtr + t) (v := mem (vIdxPtr + u) - 1)
        (by eval_expr) (by rw [← hT3]; eval_expr) ?_
      set m1 := Function.update st.mem (euPtr + t) (mem (vIdxPtr + u) - 1) with hm1
      have hH1 : m1 (hsPtr + mem (eListPtr + t)) = mem (hsPtr + mem (eListPtr + t)) := by
        rw [hm1, Function.update_of_ne (by omega)]; exact hfr _ (Or.inl hhs)
      have hH2 : m1 (i2ePtr + m1 (hsPtr + mem (eListPtr + t))) = v := by
        rw [hH1, hm1, Function.update_of_ne (by omega), ← hv']; exact hfr _ (Or.inl hih)
      have hH3 : m1 (vIdxPtr + m1 (i2ePtr + m1 (hsPtr + mem (eListPtr + t)))) = mem (vIdxPtr + v) := by
        rw [hH2, hm1, Function.update_of_ne (by omega)]; exact hfr _ (Or.inl hvh)
      refine runs_store_le (x := evPtr + t) (v := mem (vIdxPtr + v) - 1)
        (by eval_expr) (by rw [← hH3]; eval_expr) ⟨⟨fun i hi => ?_, by simp, ?_, ?_⟩,
          by simpa using h8⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 9 by omega)]
        exact hR i hi
      · intro a ha
        simp only [hm1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro j hj
        simp only [hm1]
        by_cases hjt : j = t
        · subst hjt
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self]
        · obtain ⟨d1, d2⟩ := hdone j (by omega)
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), d1]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), d2]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold endpointIdxProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr,
    evPtr, rfl, rfl, hdone, hfr⟩ ?_
  simp only [endpointIdxContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
    Nat.sub_zero]
  omega

/-! ## What the written values mean -/

/-- Reading the slot arrays of a `DynGraphAt` block gives the tail and head of the listed edge. -/
lemma slotVert_dynGraph {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 eListPtr t : ℕ} {G₀ : MGraph}
    {eList : List ℕ} (hG : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hL : ListAt mem eListPtr eList)
    (hsub : ∀ e ∈ eList, e ∈ G₀.E) (ht : t < eList.length) :
    slotVert mem eListPtr (dgETailSlotBase g0Ptr vCap0 eCap0) (dgIntToExtBase g0Ptr vCap0) t =
      G₀.tail (eList.getD t 0) ∧
    slotVert mem eListPtr (dgEHeadSlotBase g0Ptr vCap0 eCap0) (dgIntToExtBase g0Ptr vCap0) t =
      G₀.head (eList.getD t 0) := by
  obtain ⟨hval, -, -, -, -, -, -, -, -, hei, -, -, -, hslot, -⟩ := hG
  have he : mem (eListPtr + t) = eList.getD t 0 := by
    rw [hL t ht, List.getD_eq_getElem _ _ ht]
  have hmem : eList.getD t 0 ∈ G₀.E := by
    rw [List.getD_eq_getElem _ _ ht]; exact hsub _ (List.getElem_mem ht)
  obtain ⟨hst, hsh⟩ := hslot _ hmem
  obtain ⟨htV, hhV⟩ := hval _ hmem
  refine ⟨?_, ?_⟩
  · simp only [slotVert]; rw [he, hst]; exact (hei _ htV).2
  · simp only [slotVert]; rw [he, hsh]; exact (hei _ hhV).2

/-- The index table stores `i + 1` at `vList[i]`, so one less is the index. -/
lemma vIdx_index {mem : ℕ → ℕ} {vIdxPtr u : ℕ} {vList : List ℕ}
    (hidx : ∀ i (hi : i < vList.length), mem (vIdxPtr + vList[i]) = i + 1) (hu : u ∈ vList) :
    mem (vIdxPtr + u) - 1 < vList.length ∧ vList.getD (mem (vIdxPtr + u) - 1) 0 = u := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  rw [hidx i hi, Nat.add_sub_cancel]
  exact ⟨hi, List.getD_eq_getElem _ _ hi⟩

/-- The arrays written by `endpointIdxProc` from a `DynGraphAt` block are the endpoint indices
that `congOrder_isApproxCongOrder` asks for. -/
theorem endpointIdx_spec {mem mem' : ℕ → ℕ} {g0Ptr vCap0 eCap0 eListPtr vIdxPtr euPtr evPtr : ℕ}
    {G₀ : MGraph} {eList vList : List ℕ} (hG : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hL : ListAt mem eListPtr eList) (hsub : ∀ e ∈ eList, e ∈ G₀.E)
    (hidx : ∀ i (hi : i < vList.length), mem (vIdxPtr + vList[i]) = i + 1)
    (hV : ∀ u ∈ G₀.V, u ∈ vList)
    (hout : ∀ t < eList.length,
      mem' (euPtr + t) = mem (vIdxPtr + slotVert mem eListPtr (dgETailSlotBase g0Ptr vCap0 eCap0)
        (dgIntToExtBase g0Ptr vCap0) t) - 1 ∧
      mem' (evPtr + t) = mem (vIdxPtr + slotVert mem eListPtr (dgEHeadSlotBase g0Ptr vCap0 eCap0)
        (dgIntToExtBase g0Ptr vCap0) t) - 1) :
    (∀ t < eList.length, mem' (euPtr + t) < vList.length ∧
      vList.getD (mem' (euPtr + t)) 0 = G₀.tail (eList.getD t 0)) ∧
    (∀ t < eList.length, mem' (evPtr + t) < vList.length ∧
      vList.getD (mem' (evPtr + t)) 0 = G₀.head (eList.getD t 0)) := by
  have hE : ∀ t < eList.length, eList.getD t 0 ∈ G₀.E := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hsub _ (List.getElem_mem ht)
  have hval := hG.1
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [(hout t ht).1, (slotVert_dynGraph hG hL hsub ht).1]
    exact vIdx_index hidx (hV _ (hval _ (hE t ht)).1)
  · rw [(hout t ht).2, (slotVert_dynGraph hG hL hsub ht).2]
    exact vIdx_index hidx (hV _ (hval _ (hE t ht)).2)

end

end MinCostFlow.LSF.Program
