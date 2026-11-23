module

public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.WireSelectHeapRebal
import WordRAM.Tactic

/-!
# Copying walks into the embedding slots (`SelectEmbCopy`)

The block of level `j < d` keeps, for every edge `e` of the active core, its walk in the active
sparsifier, in a slot of `slot` words of its own (`SelPartEmb`, `SelectBlocksParts.lean`). The walks
come from the embedding readout of the sparse core (op `4`, `MEmbAt` of the core edges): at a
rebuild or a shift of level `j` for every core edge, and at an `Update` for the edges of the
re-embedded list. This file copies the walks of the listed edges into their slots.

* `selEmbCopyBody copyTo` (`[embTable, entryBase, eCap, slot, listPtr, len]`): for each edge `e`
  of the list, copy the walk that `embTable + e` points at into slot `e` (at
  `entryBase + eCap + e · slot`) with `copyLimbsToBody` (procedure `copyTo`), and point
  `entryBase + e` at the slot.
* `selEmbCopy_meetsContract`: the listed slots hold their walks, every word off the region is
  kept, and the entries and slots of the other edges are kept. Cost `len · (18 slot + 80) + 20`.
* `selEmbCopy_setEmb`: with `entryBase = B.embPtr j`, the call keeps every other part of the
  blocks and gives the embedding part of level `j` for the new edges and walks.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- Copy the walks of the listed edges into their slots
(`[embTable, entryBase, eCap, slot, listPtr, len]`). -/
def selEmbCopyBody (copyTo : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 1) (.reg 2)) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
     .assign 10 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 9)))) ;;
     .assign 11 (.bin .add (.reg 6) (.bin .mul (.reg 8) (.reg 3))) ;;
     .call 12 copyTo [.reg 9, .reg 11, .reg 10] ;;
     .store (.bin .add (.reg 1) (.reg 8)) (.reg 11)) ;;
  .ret (.const 0)

theorem selEmbCopyBody_noRand (copyTo : ℕ) : (selEmbCopyBody copyTo).NoRand := by
  simp [selEmbCopyBody, forRange, forUp, Stmt.NoRand]

/-- The facts of the source walk of one listed edge `e`: it fits its slot, it is stored where
`embTable + e` points, it fits in words, and it lies off the region `[lo, hi)` of the slots. -/
def SelEmbSrcOk (mem : ℕ → ℕ) (w embTable slot lo hi : ℕ) (emb : MinCostFlow.Embedding)
    (e : ℕ) : Prop :=
  (mWalkEncode (emb e)).length ≤ slot ∧ MWalkAt mem (mem (embTable + e)) (emb e) ∧
  embTable + e < 2 ^ w ∧ (embTable + e < lo ∨ hi ≤ embTable + e) ∧
  mem (embTable + e) + (mWalkEncode (emb e)).length < 2 ^ w ∧
  (∀ t < (mWalkEncode (emb e)).length, mem (mem (embTable + e) + t) < 2 ^ w) ∧
  (mem (embTable + e) + (mWalkEncode (emb e)).length ≤ lo ∨ hi ≤ mem (embTable + e))

/-- Contract of `selEmbCopyBody` for the list `L` and the source walks `emb`. -/
def selEmbCopyContract (w : ℕ) (L : List ℕ) (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ embTable entryBase eCap slot listPtr,
    args = [embTable, entryBase, eCap, slot, listPtr, L.length] ∧
    16 < 2 ^ w ∧ entryBase + eCap + eCap * slot < 2 ^ w ∧ listPtr + L.length < 2 ^ w ∧
    (listPtr + L.length ≤ entryBase ∨ entryBase + eCap + eCap * slot ≤ listPtr) ∧
    ListAt mem listPtr L ∧
    ∀ e ∈ L, e < eCap ∧
      SelEmbSrcOk mem w embTable slot entryBase (entryBase + eCap + eCap * slot) emb e
  post args mem ret mem' := ∃ embTable entryBase eCap slot listPtr,
    args = [embTable, entryBase, eCap, slot, listPtr, L.length] ∧ ret = 0 ∧
    (∀ e ∈ L, mem' (entryBase + e) = entryBase + eCap + e * slot ∧
      MWalkAt mem' (entryBase + eCap + e * slot) (emb e)) ∧
    (∀ a, (a < entryBase ∨ entryBase + eCap + eCap * slot ≤ a) → mem' a = mem a) ∧
    (∀ e < eCap, e ∉ L → mem' (entryBase + e) = mem (entryBase + e) ∧
      ∀ t < slot, mem' (entryBase + eCap + e * slot + t) = mem (entryBase + eCap + e * slot + t))
  cost args _ := L.length * (18 * args.getD 3 0 + 80) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

private theorem slot_end {e c S : ℕ} (h : e < c) : e * S + S ≤ c * S := by
  have := Nat.mul_le_mul_right S (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this
  exact this

private theorem slot_disj {e e' S t : ℕ} (hne : e ≠ e') (ht : t < S) :
    e * S + t < e' * S ∨ e' * S + S ≤ e * S + t := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left; have := slot_end (S := S) h; omega
  · right; have := slot_end (S := S) h; omega

/-- The words that the copies of the edges `L[i']`, `i' < i`, wrote: the entry and the slot. -/
private def Touched (L : List ℕ) (entryBase slotBase slot i a : ℕ) : Prop :=
  ∃ i' < i, ∃ (hi' : i' < L.length),
    a = entryBase + L[i'] ∨ (slotBase + L[i'] * slot ≤ a ∧ a < slotBase + L[i'] * slot + slot)

set_option maxHeartbeats 800000 in
/-- `selEmbCopyBody` meets `selEmbCopyContract`. -/
theorem selEmbCopy_meetsContract {w proc copyTo : ℕ} {L : List ℕ} {emb : MinCostFlow.Embedding}
    {p : Program}
    (hp : p.procs[proc]? = some (selEmbCopyBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selEmbCopyContract w L emb) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨embTable, entryBase, eCap, slot, listPtr, rfl, hw16, hregW, hlistW, hldisj, hlist,
    hsrc⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hcapL : ∀ e ∈ L, e < eCap := fun e he => (hsrc e he).1
  have hend : ∀ e ∈ L, e * slot + slot ≤ eCap * slot := fun e he => slot_end (hcapL e he)
  have hloop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body := .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .assign 9 (.load (.bin .add (.reg 0) (.reg 8))) ;;
      .assign 10 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 9)))) ;;
      .assign 11 (.bin .add (.reg 6) (.bin .mul (.reg 8) (.reg 3))) ;;
      .call 12 copyTo [.reg 9, .reg 11, .reg 10] ;;
      .store (.bin .add (.reg 1) (.reg 8)) (.reg 11))
    (P := fun st => st.regs 0 = embTable ∧ st.regs 1 = entryBase ∧ st.regs 2 = eCap ∧
      st.regs 3 = slot ∧ st.regs 4 = listPtr ∧ st.regs 5 = L.length ∧
      st.regs 6 = entryBase + eCap ∧ st.mem = mem)
    (Inv := fun i st => st.regs 0 = embTable ∧ st.regs 1 = entryBase ∧ st.regs 2 = eCap ∧
      st.regs 3 = slot ∧ st.regs 4 = listPtr ∧ st.regs 5 = L.length ∧
      st.regs 6 = entryBase + eCap ∧ st.regs 7 = i ∧
      (∀ i' < i, ∀ (hi' : i' < L.length),
        st.mem (entryBase + L[i']) = entryBase + eCap + L[i'] * slot ∧
        MWalkAt st.mem (entryBase + eCap + L[i'] * slot) (emb L[i'])) ∧
      (∀ a, ¬ Touched L entryBase (entryBase + eCap) slot i a → st.mem a = mem a))
    (18 * slot + 70) 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, hm⟩ := hst
      refine ⟨by eval_expr, ?_⟩
      refine ⟨h0, h1, h2, h3, h4, h5, h6, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
        fun a _ => by simp [hm]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h5 := hi.2.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hdone, hout⟩
      have heL : L[i] ∈ L := List.getElem_mem hi
      obtain ⟨hcapi, hfit, hwalk, htabW, htabOff, hsrcW, hsrcWords, hsrcOff⟩ := hsrc _ heL
      have hei := hend _ heL
      have hnotT : ∀ a, (a < entryBase ∨ entryBase + eCap + eCap * slot ≤ a) →
          ¬ Touched L entryBase (entryBase + eCap) slot i a := by
        rintro a ha ⟨i', _, hi', h | h⟩
        · have := hcapL _ (List.getElem_mem hi'); omega
        · have := hend _ (List.getElem_mem hi'); omega
      have hread : st.mem (listPtr + i) = L[i] := by
        rw [hout _ (hnotT _ (by rcases hldisj with h | h <;> omega))]; exact hlist i hi
      have htab : st.mem (embTable + L[i]) = mem (embTable + L[i]) :=
        hout _ (hnotT _ htabOff)
      set q := mem (embTable + L[i]) with hq
      have hsrcKeep : ∀ t < (mWalkEncode (emb L[i])).length, st.mem (q + t) = mem (q + t) :=
        fun t ht => hout _ (hnotT _ (by omega))
      have hhead : st.mem q = (emb L[i]).length := by
        rw [show q = q + 0 from rfl, hsrcKeep 0 (by rw [mWalkEncode_length]; omega)]
        exact MWalkAt_head hwalk
      have hlenEq : 1 + 2 * (emb L[i]).length = (mWalkEncode (emb L[i])).length :=
        (mWalkEncode_length _).symm
      have hslotW : entryBase + eCap + L[i] * slot + slot < 2 ^ w := by omega
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      refine runs_seq_assign_le (v := q) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 1 + 2 * (emb L[i]).length) (by eval_expr) ?_
      refine runs_seq_assign_le (v := entryBase + eCap + L[i] * slot) (by eval_expr) ?_
      refine runs_seq_call_le hcopy
        (vs := [q, entryBase + eCap + L[i] * slot, 1 + 2 * (emb L[i]).length])
        (by eval_expr) (by wram_words)
        ⟨q, entryBase + eCap + L[i] * slot, 1 + 2 * (emb L[i]).length, rfl, hw1, by omega,
          by omega, by omega, fun t ht => by rw [hsrcKeep t (by omega)]; exact hsrcWords t (by omega)⟩
        ?_
      intro v mem2 pos2 hpost
      obtain ⟨_, hcp, hfr⟩ := hpost
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hcp hfr
      refine runs_store_le (x := entryBase + L[i]) (v := entryBase + eCap + L[i] * slot)
        (by eval_expr) (by eval_expr) ?_ ?_
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6, by simp,
          fun i' hi'' hi' => ?_, fun a ha => ?_⟩, by simpa using h7⟩
        · dsimp only
          by_cases hii : L[i'] = L[i]
          · rw [hii, Function.update_self]
            refine ⟨rfl, fun t ht => ?_⟩
            rw [Function.update_of_ne (by
              have : t < 1 + 2 * (emb L[i]).length := by rw [hlenEq]; exact ht
              omega)]
            rw [hcp t (by rw [hlenEq]; exact ht), hsrcKeep t ht]
            exact hwalk t ht
          · have hne : i' ≠ i := fun h => hii (by subst h; rfl)
            have hcapi' := hcapL _ (List.getElem_mem hi')
            obtain ⟨hd1, hd2⟩ := hdone i' (by omega) hi'
            rw [Function.update_of_ne (by omega), hfr _ ?_]
            · refine ⟨hd1, fun t ht => ?_⟩
              have hfit' := (hsrc _ (List.getElem_mem hi')).2.1
              have ht' : t < slot := lt_of_lt_of_le ht hfit'
              rw [Function.update_of_ne ?_, hfr _ ?_]
              · exact hd2 t ht
              · rcases slot_disj hii ht' with h | h
                · left; omega
                · right; omega
              · omega
            · omega
        · dsimp only
          have hnot : ¬ Touched L entryBase (entryBase + eCap) slot i a := fun ⟨i', hi'', hi', h⟩ =>
            ha ⟨i', by omega, hi', h⟩
          have hnotI : a ≠ entryBase + L[i] ∧
              (a < entryBase + eCap + L[i] * slot ∨ entryBase + eCap + L[i] * slot + slot ≤ a) := by
            refine ⟨fun h => ha ⟨i, by omega, hi, Or.inl h⟩, ?_⟩
            by_contra hc
            exact ha ⟨i, by omega, hi, Or.inr (by omega)⟩
          rw [Function.update_of_ne hnotI.1, hfr _ ?_]
          · exact hout a hnot
          · have : 1 + 2 * (emb L[i]).length ≤ slot := by rw [hlenEq]; exact hfit
            omega
      · simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const, argsSize_cons,
          argsSize_nil]
        have : 1 + 2 * (emb L[i]).length ≤ slot := by rw [hlenEq]; exact hfit
        omega)
  apply runs_start_le
  dsimp only [startState]
  unfold selEmbCopyBody
  refine runs_seq_assign_flat (v := entryBase + eCap) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, rfl⟩ ?_
  intro st1 ⟨_, _, _, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · refine ⟨embTable, entryBase, eCap, slot, listPtr, rfl, rfl, fun e he => ?_, fun a ha => ?_,
      fun e he hnot => ⟨?_, fun t ht => ?_⟩⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact hdone i hi hi
    · refine hout a ?_
      rintro ⟨i', _, hi', h | h⟩
      · have := hcapL _ (List.getElem_mem hi'); omega
      · have := hend _ (List.getElem_mem hi'); omega
    · refine hout _ ?_
      rintro ⟨i', _, hi', h | h⟩
      · exact hnot (by have : e = L[i'] := by omega
                       exact this ▸ List.getElem_mem hi')
      · have := hcapL _ (List.getElem_mem hi'); omega
    · refine hout _ ?_
      rintro ⟨i', _, hi', h | h⟩
      · have := hcapL _ (List.getElem_mem hi'); omega
      · have hne : e ≠ L[i'] := fun h => hnot (h ▸ List.getElem_mem hi')
        rcases slot_disj hne ht with h' | h' <;> omega
  · simp only [selEmbCopyContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    nlinarith

/-- **The embedding part after the copy.** With `entryBase = B.embPtr j` and the caps of the
blocks, the call keeps every other part of the blocks, and gives the embedding part of level `j`
for the edges `E'` and the walks `emb'`: the source walks on the listed edges, and the old walks
on the others. -/
theorem selEmbCopy_setEmb {w P j pLast : ℕ} {B : SelectBlocksLoc} {L : List ℕ}
    {embsrc emb' : MinCostFlow.Embedding} {embTable listPtr : ℕ} {mem mem' : ℕ → ℕ} {ret : ℕ}
    {D : SelBlocksData} {E' : Finset ℕ}
    (hpost : (selEmbCopyContract w L embsrc).post
      [embTable, B.embPtr j, B.eCap, B.slot, listPtr, L.length] mem ret mem')
    (hblk : SelBlocksDataAt mem B P D pLast) (hj : j < B.d)
    (hLcap : ∀ e ∈ L, e < B.eCap ∧ (mWalkEncode (embsrc e)).length ≤ B.slot)
    (hnew : ∀ e ∈ E', e ∈ L ∨ e ∈ D.coreE j)
    (hvL : ∀ e ∈ E', e ∈ L → emb' e = embsrc e)
    (hvO : ∀ e ∈ E', e ∉ L → emb' e = D.emb j e) :
    SelBlocksDataAt mem' B P
      { D with coreE := Function.update D.coreE j E', emb := Function.update D.emb j emb' } pLast := by
  have hEmb := hblk.2.2.2.1 j hj
  obtain ⟨_, _, _, _, _, hargs, _, hcp, hout, hkeep⟩ := hpost
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -⟩ := hargs
  have hregEnd : B.embPtr j + B.eCap + B.eCap * B.slot = B.fPtr j + B.levelSize := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize
    omega
  refine hblk.setEmb hj (fun a ha => hout a ?_) fun e he => ?_
  · unfold SelectBlocksLoc.regEmb at ha; omega
  · by_cases heL : e ∈ L
    · obtain ⟨h1, h2⟩ := hcp e heL
      rw [hvL e he heL]
      exact ⟨(hLcap e heL).1, h1, (hLcap e heL).2, h2⟩
    · have heO := (hnew e he).resolve_left heL
      obtain ⟨c1, c2, c3, c4⟩ := hEmb e heO
      obtain ⟨k1, k2⟩ := hkeep e c1 heL
      rw [hvO e he heL]
      refine ⟨c1, k1.trans c2, c3, fun t ht => ?_⟩
      have := k2 t (lt_of_lt_of_le ht c3)
      unfold SelectBlocksLoc.slotPtr at c4 ⊢
      rw [this]; exact c4 t ht

end MinCostFlow.MinRatio
