module

public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.SelectBlocksSplit
public import MinCostFlow.MinRatio.WireSelectSplitPotModel
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
import WordRAM.Tactic

/-!
# Deterministic non-rebuilt select-block update primitives (`SelectNonRebuiltOps`)

Provides three deterministic Word-RAM procedures used to update the select blocks of non-rebuilt
levels `j < min firstReb d` at an `Update`:

1. `dgDeleteEdgeListBody` (`[gPtr, listPtr, len] → 0`): deletes every edge of a list from a
   `DynGraphAt` block in `490 * len + 20` steps (`dgDeleteEdgeList_meetsContract`), plus
   `dgApplyBatch_allowZero_and_deleteList_eq` connecting `dgApplyBatch (allowInsert = 0)` +
   `dgDeleteEdgeList` on `fDel` to the new active forest `F'_j`.
2. `selBatchCopySplitsBody` (`[batchPtr, phiPtr, Lk] → 0`): scans a `BatchAt` encoding of `U` and
   copies `φ_j[v] → φ_j[v']` at every `.split v v' _ _` in `U.length * (18 * Lk + 130) + 40` steps,
   updating `B.phiPtr j` from `φ_j` on `G.V` to `splitPot φ_j (batchSplits U)` on
   `(G.applyBatch U).V` (`selBatchCopySplits_meetsContract`, `selBatchCopySplits_setPhi`).
3. `selCopyG0FromExtBody` (`[gExt, inverse, g0Ptr, listPtr, len, Lk] → 0`): copies external
   gradients `g[inverse[e]]` into `B.g0Ptr[e]` for each listed surviving level-0 edge `e` in
   `len * (18 * Lk + 70) + 20` steps (`selCopyG0FromExt_meetsContract`, `selCopyG0FromExt_setG0`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner DynSpanner.Program SparseCore

/-! ## 1. Deleting a list of edges from `DynGraphAt` -/

/-- Delete a list of edges `L` from a `DynGraphAt` block (`[gPtr, listPtr, len] → 0`). -/
def dgDeleteEdgeListBody (delEdgeProc : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
     .call 5 delEdgeProc [.reg 0, .reg 4]) ;;
  .ret (.const 0)

theorem dgDeleteEdgeListBody_noRand (delEdgeProc : ℕ) :
    (dgDeleteEdgeListBody delEdgeProc).NoRand := by
  simp [dgDeleteEdgeListBody, forRange, forUp, Stmt.NoRand]

/-- Target graph of deleting every edge of `L` (when present) from `G`. -/
def dgDeleteEdgeListGraph (G : MGraph) (L : List ℕ) : MGraph :=
  L.foldl (fun H e => if e ∈ H.E then H.applyUpdate (.delete e) else H) G

/-- Contract for `dgDeleteEdgeListBody` (`[gPtr, listPtr, len] → 0`). -/
def dgDeleteEdgeListContract (w vCap eCap : ℕ) (G : MGraph) (L : List ℕ) : Contract where
  pre args mem := ∃ gPtr listPtr, args = [gPtr, listPtr, L.length] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ listPtr + L.length < 2 ^ w ∧
    (listPtr + L.length ≤ gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ listPtr) ∧
    ListAt mem listPtr L ∧ (∀ e ∈ L, e < 2 ^ w) ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr listPtr, args = [gPtr, listPtr, L.length] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap (dgDeleteEdgeListGraph G L) ∧
    ∀ a, (a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) → mem' a = mem a
  cost _ _ := L.length * 490 + 20

/-! ## 2. Copying frozen potentials across all splits in a `BatchAt` -/

/-- Loop statement of `selBatchCopySplitsBody`. -/
def selBatchCopySplitsLoop (copyTo : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 4) (.reg 3))
    (.assign 6 (.load (.reg 5)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 5 (.bin .add (.reg 5) (.const 4)))
       (.cond (.bin .eq (.reg 6) (.const 1))
         (.assign 5 (.bin .add (.reg 5) (.const 2)))
         (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
          .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
          .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
          .assign 10 (.load (.bin .add (.reg 5) (.const 4))) ;;
          .call 11 copyTo
            [.bin .add (.reg 1) (.bin .mul (.reg 7) (.reg 2)),
             .bin .add (.reg 1) (.bin .mul (.reg 8) (.reg 2)), .reg 2] ;;
          .assign 5 (.bin .add (.bin .add (.bin .add (.reg 5) (.const 5)) (.reg 9)) (.reg 10)))) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

/-- Scan a `BatchAt` at `batchPtr` and copy `phiPtr[v] → phiPtr[v']` for every `.split v v' _ _`
(`[batchPtr, phiPtr, Lk] → 0`). -/
def selBatchCopySplitsBody (copyTo : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 0) (.const 1)) ;;
  selBatchCopySplitsLoop copyTo ;;
  .ret (.const 0)

theorem selBatchCopySplitsBody_noRand (copyTo : ℕ) :
    (selBatchCopySplitsBody copyTo).NoRand := by
  simp [selBatchCopySplitsBody, selBatchCopySplitsLoop, Stmt.NoRand]

/-- Contract for `selBatchCopySplitsBody` (`[batchPtr, phiPtr, Lk] → 0`). -/
def selBatchCopySplitsContract (w vCap P : ℕ) (G : MGraph) (U : List Update) (totalWords : ℕ)
    (φj : ℕ → ℝ) : Contract where
  pre args mem := ∃ batchPtr phiPtr Lk, args = [batchPtr, phiPtr, Lk] ∧
    16 < 2 ^ w ∧ vCap < 2 ^ w ∧ batchPtr + totalWords < 2 ^ w ∧ phiPtr + vCap * Lk < 2 ^ w ∧
    (batchPtr + totalWords ≤ phiPtr ∨ phiPtr + vCap * Lk ≤ batchPtr) ∧
    BatchAt mem batchPtr G U totalWords ∧ G.BatchIsValid U ∧
    (∀ u ∈ U, match u with | .split _ v' _ _ => v' < vCap | _ => True) ∧
    (∀ v ∈ G.V, v < vCap) ∧
    EdgeValuesAt mem phiPtr 4 Lk P G.V φj
  post args mem ret mem' := ∃ batchPtr phiPtr Lk, args = [batchPtr, phiPtr, Lk] ∧ ret = 0 ∧
    (∀ v ∈ (G.applyBatch U).V, v < vCap) ∧
    EdgeValuesAt mem' phiPtr 4 Lk P (G.applyBatch U).V (splitPot φj (batchSplits U)) ∧
    ∀ a, (a < phiPtr ∨ phiPtr + vCap * Lk ≤ a) → mem' a = mem a
  cost args _ := U.length * (18 * args.getD 2 0 + 130) + 40

/-! ## 3. Copying level-0 gradients from external array via `inverse` -/

/-- Copy external gradients `gExt[inverse[e]]` into `g0Ptr[e]` for each `e` in `listPtr[0..len)`
(`[gExt, inverse, g0Ptr, listPtr, len, Lk] → 0`). -/
def selCopyG0FromExtBody (copyTo : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .call 9 copyTo
       [.bin .add (.reg 0) (.bin .mul (.reg 8) (.reg 5)),
        .bin .add (.reg 2) (.bin .mul (.reg 7) (.reg 5)), .reg 5]) ;;
  .ret (.const 0)

theorem selCopyG0FromExtBody_noRand (copyTo : ℕ) :
    (selCopyG0FromExtBody copyTo).NoRand := by
  simp [selCopyG0FromExtBody, forRange, forUp, Stmt.NoRand]

/-- Contract for `selCopyG0FromExtBody` (`[gExt, inverse, g0Ptr, listPtr, len, Lk] → 0`). -/
def selCopyG0FromExtContract (w m eCap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ gExt invPtr g0Ptr listPtr Lk,
    args = [gExt, invPtr, g0Ptr, listPtr, L.length, Lk] ∧
    16 < 2 ^ w ∧ m < 2 ^ w ∧ eCap < 2 ^ w ∧
    gExt + m * Lk < 2 ^ w ∧ invPtr + eCap < 2 ^ w ∧
    g0Ptr + eCap * Lk < 2 ^ w ∧ listPtr + L.length < 2 ^ w ∧
    (gExt + m * Lk ≤ g0Ptr ∨ g0Ptr + eCap * Lk ≤ gExt) ∧
    (invPtr + eCap ≤ g0Ptr ∨ g0Ptr + eCap * Lk ≤ invPtr) ∧
    (listPtr + L.length ≤ g0Ptr ∨ g0Ptr + eCap * Lk ≤ listPtr) ∧
    ListAt mem listPtr L ∧
    (∀ e ∈ L, e < eCap ∧ mem (invPtr + e) < m) ∧
    (∀ e ∈ L, ∀ t < Lk, mem (gExt + mem (invPtr + e) * Lk + t) < 2 ^ w)
  post args mem ret mem' := ∃ gExt invPtr g0Ptr listPtr Lk,
    args = [gExt, invPtr, g0Ptr, listPtr, L.length, Lk] ∧ ret = 0 ∧
    (∀ e ∈ L, ∀ t < Lk, mem' (g0Ptr + e * Lk + t) = mem (gExt + mem (invPtr + e) * Lk + t)) ∧
    (∀ a, (a < g0Ptr ∨ g0Ptr + eCap * Lk ≤ a) → mem' a = mem a) ∧
    (∀ e < eCap, e ∉ L → ∀ t < Lk, mem' (g0Ptr + e * Lk + t) = mem (g0Ptr + e * Lk + t))
  cost args _ := L.length * (18 * args.getD 5 0 + 70) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner DynSpanner.Program SparseCore

/-! ## 4. Verification of `dgDeleteEdgeListBody` and forest-update equivalence -/

theorem dgDeleteEdgeListGraph_props (G : MGraph) (L : List ℕ) :
    (dgDeleteEdgeListGraph G L).V = G.V ∧
    (dgDeleteEdgeListGraph G L).E = G.E \ L.toFinset ∧
    ∀ e ∈ (dgDeleteEdgeListGraph G L).E,
      (dgDeleteEdgeListGraph G L).tail e = G.tail e ∧
      (dgDeleteEdgeListGraph G L).head e = G.head e := by
  induction L generalizing G with
  | nil => simp [dgDeleteEdgeListGraph]
  | cons x rest ih =>
    let G1 := if x ∈ G.E then G.applyUpdate (.delete x) else G
    have hV1 : G1.V = G.V := by dsimp only [G1]; split_ifs <;> rfl
    have hE1 : G1.E = G.E.erase x := by
      dsimp only [G1]; split_ifs with hx
      · rfl
      · exact (Finset.erase_eq_of_notMem hx).symm
    have hEnd1 : ∀ e ∈ G1.E, G1.tail e = G.tail e ∧ G1.head e = G.head e := fun _ _ => by
      dsimp only [G1]; split_ifs <;> exact ⟨rfl, rfl⟩
    obtain ⟨hVr, hEr, hEndr⟩ := ih G1
    have hstep : dgDeleteEdgeListGraph G (x :: rest) = dgDeleteEdgeListGraph G1 rest := rfl
    rw [hstep]
    refine ⟨hVr.trans hV1, ?_, fun e he => ?_⟩
    · rw [hEr, hE1, List.toFinset_cons]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    · have h1 := hEndr e he
      have heG1 : e ∈ G1.E := (Finset.mem_sdiff.mp (hEr ▸ he)).1
      exact ⟨h1.1.trans (hEnd1 e heG1).1, h1.2.trans (hEnd1 e heG1).2⟩

theorem foldl_dgBatchTarget_zero_props {G F : MGraph} {U : List Update}
    (hBV : G.BatchIsValid U) (hSub : G.IsSubgraph F) (hV : F.V = G.V) :
    let Fmid := U.foldl (dgBatchTarget 0) F
    (G.applyBatch U).IsSubgraph Fmid ∧
    Fmid.V = (G.applyBatch U).V ∧
    (∀ e, e ∈ Fmid.E ↔ e ∈ F.E ∧ Update.delete e ∉ U) := by
  induction U generalizing G F with
  | nil => exact ⟨hSub, hV, fun _ => by simp⟩
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hBV
    obtain ⟨hSub1, hV1⟩ := dgBatchTarget_preserves_subgraph hu hSub hV
    have hF1eq : dgBatchTarget 0 F u = F.applyBatch (restrictUpdate u F) := rfl
    have hE1 : ∀ e, e ∈ (dgBatchTarget 0 F u).E ↔ e ∈ F.E ∧ u ≠ Update.delete e := by
      intro e
      rw [hF1eq]
      cases u with
      | insert _ _ _ => simp [restrictUpdate, MGraph.applyBatch]
      | delete e₀ =>
        simp only [restrictUpdate, MGraph.applyBatch]
        by_cases he₀ : e₀ ∈ F.E
        · simp [he₀, MGraph.applyUpdate, Finset.mem_erase, eq_comm, and_comm]
        · simp only [he₀, ↓reduceIte, List.foldl_nil, ne_eq, Update.delete.injEq]
          exact ⟨fun he => ⟨he, fun h => he₀ (h ▸ he)⟩, fun h => h.1⟩
      | split _ _ _ _ => simp [restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]
    obtain ⟨hSub2, hV2, hE2⟩ := ih hrest (hF1eq.symm ▸ hSub1) (hF1eq.symm ▸ hV1)
    refine ⟨hSub2, hV2, fun e => ?_⟩
    simp only [List.foldl_cons, List.mem_cons, not_or]
    rw [hE2 e, hE1 e]
    tauto

/-- Combining `dgApplyBatch (allowInsert = 0)` on `F` with `dgDeleteEdgeList` on `fDel` produces
`DynGraphAt` of the new decremental forest `F'`. -/
theorem dgApplyBatch_allowZero_and_deleteList_eq {mem : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    {G F F' : MGraph} {U : List Update} {fDel : List ℕ}
    (hBV : G.BatchIsValid U) (hSub : G.IsSubgraph F) (hVF : F.V = G.V)
    (hSub' : (G.applyBatch U).IsSubgraph F') (hVF' : F'.V = (G.applyBatch U).V)
    (hF'Sub : F'.E ⊆ F.E) (hF'NoDel : ∀ e ∈ F'.E, Update.delete e ∉ U)
    (hfDel : fDel.toFinset = F.E \ F'.E)
    (hDG : DynGraphAt mem gPtr vCap eCap
      (dgDeleteEdgeListGraph (U.foldl (dgBatchTarget 0) F) fDel)) :
    DynGraphAt mem gPtr vCap eCap F' := by
  obtain ⟨hSubMid, hVMid, hEMid⟩ := foldl_dgBatchTarget_zero_props hBV hSub hVF
  obtain ⟨hVOut, hEOut, hEndOut⟩ := dgDeleteEdgeListGraph_props (U.foldl (dgBatchTarget 0) F) fDel
  refine hDG.congr_ends (hVOut.trans (hVMid.trans hVF'.symm)) ?_ ?_
  · rw [hEOut, hfDel]
    ext e
    simp only [Finset.mem_sdiff, hEMid]
    constructor
    · rintro ⟨⟨heF, _⟩, hnot⟩
      by_contra hnotF'
      exact hnot ⟨heF, hnotF'⟩
    · intro heF'
      exact ⟨⟨hF'Sub heF', hF'NoDel e heF'⟩, fun h => h.2 heF'⟩
  · intro e he
    have heMid : e ∈ (U.foldl (dgBatchTarget 0) F).E := (Finset.mem_sdiff.mp (hEOut ▸ he)).1
    have heF' : e ∈ F'.E := by
      have h1 := Finset.mem_sdiff.mp (hEOut ▸ he)
      rw [hfDel] at h1
      have heF := ((hEMid e).mp h1.1).1
      by_contra hnot; exact h1.2 (Finset.mem_sdiff.mpr ⟨heF, hnot⟩)
    have hEndMid := hSubMid.2.2 e heMid
    have hEndF' := hSub'.2.2 e heF'
    exact ⟨(hEndOut e he).1.trans (hEndMid.1.trans hEndF'.1.symm),
      (hEndOut e he).2.trans (hEndMid.2.trans hEndF'.2.symm)⟩

/-- `dgDeleteEdgeListBody` meets `dgDeleteEdgeListContract`. -/
theorem dgDeleteEdgeList_meetsContract {w proc delEdgeProc vCap eCap : ℕ} {G : MGraph}
    {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some (dgDeleteEdgeListBody delEdgeProc))
    (hdel : ∀ H : MGraph, MeetsContract w p delEdgeProc (dgDeleteEdgeContract w vCap eCap H)) :
    MeetsContract w p proc (dgDeleteEdgeListContract w vCap eCap G L) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨gPtr, listPtr, rfl, hw16, hgW, hlistW, hdisj, hlist, hLW, hG⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
      .call 5 delEdgeProc [.reg 0, .reg 4])
    (P := fun st => st = startState [gPtr, listPtr, L.length] mem pos)
    (Inv := fun i st => st.regs 0 = gPtr ∧ st.regs 1 = listPtr ∧ st.regs 2 = L.length ∧
      st.regs 3 = i ∧
      DynGraphAt st.mem gPtr vCap eCap (dgDeleteEdgeListGraph G (L.take i)) ∧
      ∀ a, (a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) → st.mem a = mem a)
    480 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState, dgDeleteEdgeListGraph, hG]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, hGi, hfr⟩
      have hread : st.mem (listPtr + i) = L[i] := by
        rw [hfr _ (by rcases hdisj with h | h <;> omega)]
        exact hlist i hi
      have hLiW : L[i] < 2 ^ w := hLW _ (List.getElem_mem hi)
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      refine runs_call_le (hdel (dgDeleteEdgeListGraph G (L.take i))) (vs := [gPtr, L[i]])
        (by eval_expr) (by wram_words) ⟨gPtr, L[i], rfl, hw16, hgW, hGi⟩ ?_
      intro v mem' pos' hpost
      obtain ⟨_, _, hargs, _, hG', hfr'⟩ := hpost
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      have htake : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem hi
      have hstep : dgDeleteEdgeListGraph G (L.take (i + 1)) =
          (if L[i] ∈ (dgDeleteEdgeListGraph G (L.take i)).E
            then (dgDeleteEdgeListGraph G (L.take i)).applyUpdate (.delete L[i])
            else dgDeleteEdgeListGraph G (L.take i)) := by
        unfold dgDeleteEdgeListGraph
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp,
        hstep ▸ hG', fun a ha => (hfr' a ha).trans (hfr a ha)⟩, by simpa using h3⟩, ?_⟩
      simp only [dgDeleteEdgeContract, Expr.size_reg, Expr.size_bin, Expr.size_load,
        argsSize_cons, argsSize_nil]
      omega)
  apply runs_start_le
  unfold dgDeleteEdgeListBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, hGend, hfrend⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · rw [List.take_length] at hGend
    exact ⟨gPtr, listPtr, rfl, rfl, hGend, hfrend⟩
  · simp only [dgDeleteEdgeListContract, Expr.size, Nat.sub_zero]; nlinarith

/-! ## 5. Verification of `selBatchCopySplitsBody` -/

private lemma slot_mul_add_le {v vCap Lk : ℕ} (hv : v < vCap) :
    v * Lk + Lk ≤ vCap * Lk := by
  have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  exact this

private lemma slot_mul_disj {v v' Lk : ℕ} (hne : v ≠ v') :
    v * Lk + Lk ≤ v' * Lk ∨ v' * Lk + Lk ≤ v * Lk := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left; exact slot_mul_add_le h
  · right; exact slot_mul_add_le h

private lemma entry_disj_of_ne {e e' Lk t : ℕ} (hne : e ≠ e') (ht : t < Lk) :
    e * Lk + t < e' * Lk ∨ e' * Lk + Lk ≤ e * Lk + t := by
  rcases slot_mul_disj (Lk := Lk) hne with h | h <;> [left; right] <;> omega

private lemma runs_seq_left_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s1 s2 s3 : Stmt}
    {st : State} {Q : Outcome → State → Prop} {c0 B : ℕ}
    (hnoRet : ∀ v s', ¬ Q (.returned v) s')
    (h : ∃ o st' c, Runs w p ω (s1 ;; (s2 ;; s3)) st o st' c ∧ Q o st' ∧ c0 + c ≤ B) :
    ∃ o st' c, Runs w p ω ((s1 ;; s2) ;; s3) st o st' c ∧ Q o st' ∧ c0 + c ≤ B := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h
  rcases runs_seq_iff.mp hr with ⟨v, _, _, rfl, _⟩ | ⟨st1, c1, c2, h1, h23, rfl⟩
  · exact (hnoRet v st' hq).elim
  · rcases runs_seq_iff.mp h23 with ⟨v, _, _, rfl, _⟩ | ⟨st2, c2', c3, h2, h3, rfl⟩
    · exact (hnoRet v st' hq).elim
    · exact ⟨o, st', (c1 + c2' + 1) + c3 + 1,
        runs_seq_iff.mpr (Or.inr ⟨st2, c1 + c2' + 1, c3,
          runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2', h1, h2, rfl⟩), h3, rfl⟩),
        hq, by omega⟩

private lemma splitPot_append (φj : ℕ → ℝ) (s₁ s₂ : List (ℕ × ℕ)) :
    splitPot φj (s₁ ++ s₂) = splitPot (splitPot φj s₁) s₂ := by
  induction s₁ generalizing φj with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨v, v'⟩
    simp only [List.cons_append, splitPot]
    exact ih _

private lemma batchSplits_append (U₁ U₂ : List Update) :
    batchSplits (U₁ ++ U₂) = batchSplits U₁ ++ batchSplits U₂ := by
  induction U₁ with
  | nil => rfl
  | cons u rest ih =>
    cases u <;> simp [batchSplits, ih]

private lemma batchIsValid_take_drop_aux :
    ∀ (idx : ℕ) (G : MGraph) (U : List Update),
      G.BatchIsValid U → (G.applyBatch (U.take idx)).BatchIsValid (U.drop idx)
  | 0, _, _, h => by simpa [MGraph.applyBatch] using h
  | _ + 1, _, [], h => by simpa [MGraph.applyBatch] using h
  | idx + 1, G, u :: us, ⟨_, hus⟩ => by
    simpa [MGraph.applyBatch] using batchIsValid_take_drop_aux idx (G.applyUpdate u) us hus

set_option maxHeartbeats 800000 in
/-- `selBatchCopySplitsBody` meets `selBatchCopySplitsContract`. -/
theorem selBatchCopySplits_meetsContract {w proc copyTo vCap P : ℕ} {G : MGraph} {U : List Update}
    {totalWords : ℕ} {φj : ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (selBatchCopySplitsBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selBatchCopySplitsContract w vCap P G U totalWords φj) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨batchPtr, phiPtr, Lk, rfl, hw16, hvCapW, hbW, hphiW, hdisj, hbatch, hBV, hCaps, hGV,
    hPhi⟩ := hpre
  obtain ⟨htwPos, hlenRd, hbody⟩ := hbatch
  have hLkW : Lk < 2 ^ w := hwords Lk (by simp)
  have h2len := hbody.two_mul_length_le
  have hUlenW : U.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : State → Prop := fun st =>
    ∃ (idx remWords : ℕ),
      idx ≤ U.length ∧ remWords ≤ totalWords - 1 ∧
      st.regs 1 = phiPtr ∧ st.regs 2 = Lk ∧ st.regs 3 = U.length ∧
      st.regs 4 = idx ∧ st.regs 5 + remWords = batchPtr + totalWords ∧
      BatchBodyAt st.mem (st.regs 5) (G.applyBatch (U.take idx)) (U.drop idx) remWords ∧
      (∀ v ∈ (G.applyBatch (U.take idx)).V, v < vCap) ∧
      EdgeValuesAt st.mem phiPtr 4 Lk P (G.applyBatch (U.take idx)).V
        (splitPot φj (batchSplits (U.take idx))) ∧
      (∀ a, (a < phiPtr ∨ phiPtr + vCap * Lk ≤ a) → st.mem a = mem a)
  let condExpr : Expr := .bin .lt (.reg 4) (.reg 3)
  let bodyStmt : Stmt :=
    .assign 6 (.load (.reg 5)) ;;
    .cond (.bin .eq (.reg 6) (.const 0))
      (.assign 5 (.bin .add (.reg 5) (.const 4)))
      (.cond (.bin .eq (.reg 6) (.const 1))
        (.assign 5 (.bin .add (.reg 5) (.const 2)))
        (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
         .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
         .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
         .assign 10 (.load (.bin .add (.reg 5) (.const 4))) ;;
         .call 11 copyTo
           [.bin .add (.reg 1) (.bin .mul (.reg 7) (.reg 2)),
            .bin .add (.reg 1) (.bin .mul (.reg 8) (.reg 2)), .reg 2] ;;
         .assign 5 (.bin .add (.bin .add (.bin .add (.reg 5) (.const 5)) (.reg 9)) (.reg 10)))) ;;
    .assign 4 (.bin .add (.reg 4) (.const 1))
  let mFn : State → ℕ := fun st => U.length - st.regs 4
  let remFn : State → ℕ := fun st => (U.length - st.regs 4) * (18 * Lk + 130) + 10
  let condFn : State → ℕ := fun st => if st.regs 4 < U.length then 1 else 0
  have hloop : Triple w p Inv (.loop condExpr bodyStmt)
      (normalPost fun st =>
        (∀ v ∈ (G.applyBatch U).V, v < vCap) ∧
        EdgeValuesAt st.mem phiPtr 4 Lk P (G.applyBatch U).V (splitPot φj (batchSplits U)) ∧
        ∀ a, (a < phiPtr ∨ phiPtr + vCap * Lk ≤ a) → st.mem a = mem a)
      remFn := by
    refine Triple.loop_measure (condVal := condFn) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨idx, _, _, _, _, _, hr3, hr4, _, _, _, _, _⟩
        dsimp only [condExpr, condFn]; rw [hr4]; eval_expr)
      (fun st hInv hv => by
        rcases hInv with ⟨idx, _, hidx, _, _, _, _, hr4, _, _, hV, hP, hfr⟩
        dsimp only [condFn] at hv
        have hEq : idx = U.length := by
          rw [hr4] at hv; by_contra hne; simp [show idx < U.length by omega] at hv
        subst hEq
        refine ⟨⟨by simpa [List.take_length] using hV, by simpa [List.take_length] using hP, hfr⟩,
          by dsimp [condExpr, Expr.size, remFn]; omega⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨idx, remWords, hidx, hremLe, hr1, hr2, hr3, hr4, hr5Eq,
          hbodyIdx, hVIdx, hPIdx, hfrIdx⟩
        dsimp only [condFn] at hv
        have hidxLt : idx < U.length := by rw [hr4] at hv; by_contra h; simp [h] at hv
        have hdrop : U.drop idx = U[idx] :: U.drop (idx + 1) :=
          (List.cons_getElem_drop_succ (h := hidxLt)).symm
        rw [hdrop] at hbodyIdx
        obtain ⟨len, hlenRem, huAt, hrestBody⟩ := hbodyIdx
        have huValid : (G.applyBatch (U.take idx)).UpdateIsValid U[idx] := by
          have hvDrop := batchIsValid_take_drop_aux idx G U hBV
          rw [hdrop] at hvDrop; exact hvDrop.1
        have htake1 : U.take (idx + 1) = U.take idx ++ [U[idx]] :=
          List.take_succ_eq_append_getElem hidxLt
        have hGstep : G.applyBatch (U.take (idx + 1)) =
            (G.applyBatch (U.take idx)).applyUpdate U[idx] := by
          rw [htake1, MGraph.applyBatch, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
        have hSstep : splitPot φj (batchSplits (U.take (idx + 1))) =
            splitPot (splitPot φj (batchSplits (U.take idx))) (batchSplits [U[idx]]) := by
          rw [htake1, batchSplits_append, splitPot_append]
        have hcurW : st.regs 5 + len < 2 ^ w := by omega
        have hidx1W : idx + 1 < 2 ^ w := by omega
        cases huEq : U[idx] with
        | insert e x y =>
          rw [huEq] at huAt hGstep hSstep hrestBody
          obtain ⟨rfl, hlist⟩ := huAt
          have htag : st.mem (st.regs 5) = 0 := by simpa using hlist 0 (by simp)
          refine ⟨40, fun s ω' hs => ?_⟩
          subst s
          apply runs_start_le
          dsimp only [bodyStmt]
          refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
          refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hw1]) ?_
            (fun h => absurd h (by decide))
          intro _
          refine runs_seq_assign_le (v := st.regs 5 + 4) (by eval_expr) ?_
          refine runs_assign_le (v := idx + 1) (by eval_expr) ?_ (by simp [Expr.size])
          refine ⟨⟨idx + 1, remWords - 4, by omega, by omega, by simp [hr1], by simp [hr2],
            by simp [hr3], by simp, by simp; omega, ?_, ?_, ?_, hfrIdx⟩,
            by dsimp [mFn]; simp; omega, ?_⟩
          · simpa [hGstep] using hrestBody
          · simpa [hGstep, MGraph.applyUpdate] using hVIdx
          · simpa [hGstep, hSstep, MGraph.applyUpdate, batchSplits, splitPot] using hPIdx
          · dsimp only [remFn, condExpr, Expr.size]
            simp only [hr4, Function.update_self]
            have hsub : U.length - idx = (U.length - (idx + 1)) + 1 := by omega
            rw [hsub]; nlinarith
        | delete e =>
          rw [huEq] at huAt hGstep hSstep hrestBody
          obtain ⟨rfl, hlist⟩ := huAt
          have htag : st.mem (st.regs 5) = 1 := by simpa using hlist 0 (by simp)
          refine ⟨45, fun s ω' hs => ?_⟩
          subst s
          apply runs_start_le
          dsimp only [bodyStmt]
          refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
          refine runs_seq_cond_le (v := 0)
            (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega]) (fun h => absurd rfl h) ?_
          intro _
          refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hw1]) ?_
            (fun h => absurd h (by decide))
          intro _
          refine runs_seq_assign_le (v := st.regs 5 + 2) (by eval_expr) ?_
          refine runs_assign_le (v := idx + 1) (by eval_expr) ?_ (by simp [Expr.size])
          refine ⟨⟨idx + 1, remWords - 2, by omega, by omega, by simp [hr1], by simp [hr2],
            by simp [hr3], by simp, by simp; omega, ?_, ?_, ?_, hfrIdx⟩,
            by dsimp [mFn]; simp; omega, ?_⟩
          · simpa [hGstep] using hrestBody
          · simpa [hGstep, MGraph.applyUpdate] using hVIdx
          · simpa [hGstep, hSstep, MGraph.applyUpdate, batchSplits, splitPot] using hPIdx
          · dsimp only [remFn, condExpr, Expr.size]
            simp only [hr4, Function.update_self]
            have hsub : U.length - idx = (U.length - (idx + 1)) + 1 := by omega
            rw [hsub]; nlinarith
        | split v v' St Sh =>
          rw [huEq] at huAt huValid hGstep hSstep
          have hvV : v ∈ (G.applyBatch (U.take idx)).V := huValid.1
          have hv'Not : v' ∉ (G.applyBatch (U.take idx)).V := huValid.2.1
          have hne : v ≠ v' := fun h => hv'Not (h ▸ hvV)
          have hvCap : v < vCap := hVIdx v hvV
          have hv'Cap : v' < vCap := by
            have := hCaps U[idx] (List.getElem_mem hidxLt)
            simpa [huEq] using this
          have hvSlot := slot_mul_add_le (Lk := Lk) hvCap
          have hv'Slot := slot_mul_add_le (Lk := Lk) hv'Cap
          have hSlotDisj := slot_mul_disj (Lk := Lk) hne
          have hFields : ∃ tag kt kh, (tag = 2 ∨ tag = 3) ∧
              st.mem (st.regs 5) = tag ∧ st.mem (st.regs 5 + 1) = v ∧
              st.mem (st.regs 5 + 2) = v' ∧ st.mem (st.regs 5 + 3) = kt ∧
              st.mem (st.regs 5 + 4) = kh ∧ len = 5 + kt + kh := by
            rcases huAt with ⟨Lt, Lh, _, _, _, _, rfl, hlist⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hlist⟩
            · refine ⟨2, Lt.length, Lh.length, Or.inl rfl,
                by simpa using hlist 0 (by simp), by simpa using hlist 1 (by simp),
                by simpa using hlist 2 (by simp), by simpa using hlist 3 (by simp),
                by simpa using hlist 4 (by simp), rfl⟩
            · refine ⟨3, Lt.length, Lh.length, Or.inr rfl,
                by simpa using hlist 0 (by simp), by simpa using hlist 1 (by simp),
                by simpa using hlist 2 (by simp), by simpa using hlist 3 (by simp),
                by simpa using hlist 4 (by simp), rfl⟩
          obtain ⟨tag, kt, kh, htag23, htagRd, hvRd, hv'Rd, hktRd, hkhRd, hlenEq⟩ := hFields
          have htagW : tag < 2 ^ w := by omega
          have hvW : v < 2 ^ w := by omega
          have hv'W : v' < 2 ^ w := by omega
          have hktW : kt < 2 ^ w := by omega
          have hkhW : kh < 2 ^ w := by omega
          refine ⟨18 * Lk + 120, fun s ω' hs => ?_⟩
          subst s
          apply runs_start_le
          dsimp only [bodyStmt]
          have htagNe0 : tag ≠ 0 := by omega
          have htagNe1 : tag ≠ 1 := by omega
          refine runs_seq_assign_le (v := tag) (by eval_expr) ?_
          refine runs_seq_cond_le (v := 0)
            (by simp [Expr.eval, BinOp.eval, htagNe0, show 0 < 2 ^ w by omega])
            (fun h => absurd rfl h) ?_
          intro _
          refine runs_seq_cond_le (v := 0)
            (by simp [Expr.eval, BinOp.eval, htagNe1, show 1 < 2 ^ w by omega, show 0 < 2 ^ w by omega])
            (fun h => absurd rfl h) ?_
          intro _
          refine runs_seq_left_le (fun _ _ h => h.1) ?_
          refine runs_seq_assign_le (v := v) (by eval_expr) ?_
          refine runs_seq_left_le (fun _ _ h => h.1) ?_
          refine runs_seq_assign_le (v := v') (by eval_expr) ?_
          refine runs_seq_left_le (fun _ _ h => h.1) ?_
          refine runs_seq_assign_le (v := kt) (by eval_expr) ?_
          refine runs_seq_left_le (fun _ _ h => h.1) ?_
          refine runs_seq_assign_le (v := kh) (by eval_expr) ?_
          refine runs_seq_left_le (fun _ _ h => h.1) ?_
          refine runs_seq_call_le hcopy (vs := [phiPtr + v * Lk, phiPtr + v' * Lk, Lk])
            (by eval_expr) (by wram_words)
            ⟨phiPtr + v * Lk, phiPtr + v' * Lk, Lk, rfl, hw1, by omega, by omega,
              by rcases hSlotDisj with h | h <;> [left; right] <;> omega,
              fun t ht => lt_trans ((hPIdx v hvV).1 t ht) (by unfold Num.base; omega)⟩ ?_
          intro _ mem1 pos1 hpost1
          have hP1 := edgeValuesAt_of_copyLimbsTo_post hPIdx hvV hpost1
          have hfr1 : ∀ a, (a < phiPtr ∨ phiPtr + vCap * Lk ≤ a) → mem1 a = st.mem a := fun a ha => by
            obtain ⟨_, _, hfr⟩ := hpost1
            simp only [List.getD_cons_zero, List.getD_cons_succ] at hfr
            exact hfr a (by omega)
          refine runs_seq_assign_le (v := st.regs 5 + 5 + kt + kh) (by eval_expr) ?_
          refine runs_assign_le (v := idx + 1) (by eval_expr) ?_ ?_
          · refine ⟨⟨idx + 1, remWords - len, by omega, by omega, by simp [hr1], by simp [hr2],
              by simp [hr3], by simp, by simp [hlenEq]; omega, ?_, ?_, ?_,
              fun a ha => (hfr1 a ha).trans (hfrIdx a ha)⟩, by dsimp [mFn]; simp; omega, ?_⟩
            · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 4 by decide), Function.update_self]
              have haddrEq : st.regs 5 + 5 + kt + kh = st.regs 5 + len := by omega
              rw [haddrEq, hGstep]
              rw [huEq] at hrestBody
              exact hrestBody.of_agree fun t ht =>
                hfr1 _ (by rcases hdisj with h | h <;> [left; right] <;> omega)
            · intro x hx
              rw [hGstep] at hx
              rcases Finset.mem_insert.mp hx with rfl | hxG
              · exact hv'Cap
              · exact hVIdx x hxG
            · rw [hGstep, hSstep]
              simpa [MGraph.applyUpdate, batchSplits, splitPot] using hP1
            · dsimp only [remFn, condExpr, Expr.size]
              simp only [hr4, Function.update_self]
              have hsub : U.length - idx = (U.length - (idx + 1)) + 1 := by omega
              rw [hsub]; nlinarith
          · simp only [copyLimbsToContract, Expr.size,
              List.getD_cons_zero, List.getD_cons_succ, argsSize_cons, argsSize_nil]
            omega)
  apply runs_start_le
  unfold selBatchCopySplitsBody selBatchCopySplitsLoop
  refine runs_seq_assign_le (v := U.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := batchPtr + 1) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨0, totalWords - 1, Nat.zero_le _, le_rfl, by simp [startState], by simp [startState],
      by simp, by simp, by simp; omega, by simpa [startState, MGraph.applyBatch] using hbody,
      by simpa [MGraph.applyBatch] using hGV,
      by simpa [startState, MGraph.applyBatch, batchSplits, splitPot] using hPhi, fun _ _ => rfl⟩
  · intro st1 ⟨hV1, hPhi1, hfr1⟩
    refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
    · exact ⟨batchPtr, phiPtr, Lk, rfl, rfl, hV1, hPhi1, hfr1⟩
    · simp only [selBatchCopySplitsContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size, remFn, Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide),
        Function.update_self, Nat.sub_zero]
      omega

/-- Updating `B.phiPtr j` via `selBatchCopySplitsBody` updates `D.V j` and `D.φ j` in
`SelBlocksDataAt` while preserving all other parts. -/
theorem selBatchCopySplits_setPhi {w P j pLast totalWords batchPtr ret : ℕ} {B : SelectBlocksLoc}
    {G : MGraph} {U : List Update} {D : SelBlocksData} {mem mem' : ℕ → ℕ}
    (hj : j ≤ B.d) (hblk : SelBlocksDataAt mem B P D pLast)
    (hpost : (selBatchCopySplitsContract w B.vCap P G U totalWords (D.φ j)).post
      [batchPtr, B.phiPtr j, B.Lk] mem ret mem') :
    SelBlocksDataAt mem' B P
      { D with
        V := Function.update D.V j (G.applyBatch U).V
        φ := Function.update D.φ j (splitPot (D.φ j) (batchSplits U)) } pLast := by
  obtain ⟨_, _, _, hargs, _, hV', hPhi', hfr⟩ := hpost
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, -⟩ := hargs
  refine hblk.setPhi hj (fun a ha => hfr a ?_) ⟨hV', hPhi'⟩
  unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at ha
  omega

/-! ## 6. Verification of `selCopyG0FromExtBody` -/

set_option maxHeartbeats 400000 in
/-- `selCopyG0FromExtBody` meets `selCopyG0FromExtContract`. -/
theorem selCopyG0FromExt_meetsContract {w proc copyTo m eCap : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selCopyG0FromExtBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selCopyG0FromExtContract w m eCap L) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨gExt, invPtr, g0Ptr, listPtr, Lk, rfl, hw16, hmW, heCapW, hgExtW, hinvW, hg0W, hlistW,
    hdisjG, hdisjI, hdisjL, hlist, hcap, hvalW⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hentExt : ∀ e ∈ L, mem (invPtr + e) * Lk + Lk ≤ m * Lk := fun e he =>
    slot_mul_add_le (hcap e he).2
  have hentEnd : ∀ e ∈ L, e * Lk + Lk ≤ eCap * Lk := fun e he =>
    slot_mul_add_le (hcap e he).1
  have hloop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 4)
    (body := .assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
      .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
      .call 9 copyTo
        [.bin .add (.reg 0) (.bin .mul (.reg 8) (.reg 5)),
         .bin .add (.reg 2) (.bin .mul (.reg 7) (.reg 5)), .reg 5])
    (P := fun st => st = startState [gExt, invPtr, g0Ptr, listPtr, L.length, Lk] mem pos)
    (Inv := fun i st => st.regs 0 = gExt ∧ st.regs 1 = invPtr ∧ st.regs 2 = g0Ptr ∧
      st.regs 3 = listPtr ∧ st.regs 4 = L.length ∧ st.regs 5 = Lk ∧ st.regs 6 = i ∧
      (∀ i' < i, ∀ (hi' : i' < L.length), ∀ t < Lk,
        st.mem (g0Ptr + L[i'] * Lk + t) = mem (gExt + mem (invPtr + L[i']) * Lk + t)) ∧
      (∀ a, (∀ i' < i, ∀ (hi' : i' < L.length),
        a < g0Ptr + L[i'] * Lk ∨ g0Ptr + L[i'] * Lk + Lk ≤ a) → st.mem a = mem a))
    (18 * Lk + 60) 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h4 := hi.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, hdone, hout⟩
      have heL : L[i] ∈ L := List.getElem_mem hi
      have heCap := (hcap _ heL).1
      have heExt := (hcap _ heL).2
      have hExtEnd := hentExt _ heL
      have hG0End := hentEnd _ heL
      have hreadE : st.mem (listPtr + i) = L[i] := by
        rw [hout _ fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi'); rcases hdisjL with h | h <;> omega]
        exact hlist i hi
      have hreadExt : st.mem (invPtr + L[i]) = mem (invPtr + L[i]) :=
        hout _ fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi'); rcases hdisjI with h | h <;> omega
      have hsrcKeep : ∀ t < Lk,
          st.mem (gExt + mem (invPtr + L[i]) * Lk + t) =
            mem (gExt + mem (invPtr + L[i]) * Lk + t) := fun t ht =>
        hout _ fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi'); rcases hdisjG with h | h <;> omega
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      refine runs_seq_assign_le (v := mem (invPtr + L[i])) (by eval_expr) ?_
      refine runs_call_le hcopy
        (vs := [gExt + mem (invPtr + L[i]) * Lk, g0Ptr + L[i] * Lk, Lk])
        (by eval_expr) (by wram_words)
        ⟨gExt + mem (invPtr + L[i]) * Lk, g0Ptr + L[i] * Lk, Lk, rfl, hw1, by omega, by omega,
          by rcases hdisjG with h | h <;> [left; right] <;> omega,
          fun t ht => by rw [hsrcKeep t ht]; exact hvalW _ heL t ht⟩ ?_
      intro _ mem' pos' hpost
      obtain ⟨_, hcp, hfr⟩ := hpost
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hcp hfr
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simp, fun i' hi'' hi' t ht => ?_, fun a ha => ?_⟩,
        by simpa using h6⟩, ?_⟩
      · dsimp only
        by_cases hii : L[i'] = L[i]
        · rw [hii, hcp t ht, hsrcKeep t ht]
        · have hne : i' ≠ i := fun h => hii (by subst h; rfl)
          rw [hfr _ (by rcases entry_disj_of_ne hii ht with h | h <;> [left; right] <;> omega)]
          exact hdone i' (by omega) hi' t ht
      · dsimp only
        rw [hfr _ (ha i (by omega) hi)]
        exact hout a fun i' hi'' hi' => ha i' (by omega) hi'
      · simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_reg, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil]
        omega)
  apply runs_start_le
  unfold selCopyG0FromExtBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · refine ⟨gExt, invPtr, g0Ptr, listPtr, Lk, rfl, rfl, fun e he t ht => ?_, fun a ha => ?_,
      fun e he hnot t ht => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact hdone i hi hi t ht
    · refine hout a fun i' _ hi' => ?_
      have := hentEnd _ (List.getElem_mem hi')
      omega
    · refine hout _ fun i' _ hi' => ?_
      have hne : e ≠ L[i'] := fun h => hnot (h ▸ List.getElem_mem hi')
      rcases entry_disj_of_ne hne ht with h | h <;> [left; right] <;> omega
  · simp only [selCopyG0FromExtContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    nlinarith

/-- Updating `B.g0Ptr` via `selCopyG0FromExtBody` updates `D.E0` and `D.g` in `SelBlocksDataAt`
while preserving all other parts. -/
theorem selCopyG0FromExt_setG0 {w m P pLast gExt invPtr listPtr ret : ℕ} {B : SelectBlocksLoc}
    {L : List ℕ} {D : SelBlocksData} {E0' : Finset ℕ} {gExtVal g' : ℕ → ℝ} {mem mem' : ℕ → ℕ}
    (hpost : (selCopyG0FromExtContract w m B.eCap L).post
      [gExt, invPtr, B.g0Ptr, listPtr, L.length, B.Lk] mem ret mem')
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hExt : EdgeValuesAt mem gExt 4 B.Lk P (Finset.range m) gExtVal)
    (hLcap : ∀ e ∈ L, e < B.eCap ∧ mem (invPtr + e) < m)
    (hnew : ∀ e ∈ E0', e ∈ L ∨ e ∈ D.E0)
    (hvL : ∀ e ∈ E0', e ∈ L → g' e = gExtVal (mem (invPtr + e)))
    (hvO : ∀ e ∈ E0', e ∉ L → g' e = D.g e) :
    SelBlocksDataAt mem' B P { D with E0 := E0', g := g' } pLast := by
  have hG0 := hblk.2.2.2.2.2
  obtain ⟨_, _, _, _, _, hargs, _, hcp, hout, hkeep⟩ := hpost
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hargs
  refine hblk.setG0 (fun a ha => hout a ?_) ⟨fun e he => ?_, fun e he => ?_⟩
  · unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at ha; omega
  · rcases hnew e he with h | h
    · exact (hLcap e h).1
    · exact hG0.1 e h
  · by_cases heL : e ∈ L
    · have hs := hExt (mem (invPtr + e)) (Finset.mem_range.mpr (hLcap e heL).2)
      refine ⟨fun t ht => (hcp e heL t ht) ▸ hs.1 t ht, ?_⟩
      unfold Num.fixVal
      rw [Num.intVal_congr (hcp e heL), hvL e he heL]
      exact hs.2
    · have heO := (hnew e he).resolve_left heL
      have hs := hG0.2 e heO
      have hk := hkeep e (hG0.1 e heO) heL
      refine ⟨fun t ht => (hk t ht) ▸ hs.1 t ht, ?_⟩
      unfold Num.fixVal
      rw [Num.intVal_congr hk, hvO e he heL]
      exact hs.2

end MinCostFlow.MinRatio

end
