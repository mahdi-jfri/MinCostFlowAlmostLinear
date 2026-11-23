module

public import MinCostFlow.SparseCore.Program.BundleLayout
public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Bundle-graph export procedure (`BundleExportProcs`)

Implements and verifies `bundleExportGraphStmt` (`[tbl, s, h]`), which writes the current bundle
graph `B.graph` of slot `s` onto the heap at `h` in the exact vertex-list / edge-triple format
expected by `bucketSpannerDS` op `0` (`SpanBucketDefs.lean`, `DSInitPre`):

* Header at `[h, h + 4)`: `[nV, V_ptr, nE, E_ptr]` with `V_ptr = h + 4` and `E_ptr = h + 4 + nV`.
* Vertex list at `V_ptr`: `[0, 1, ..., nV - 1]` (matching `B.vertices = Finset.range nV`).
* Edge triples at `E_ptr`: `(e, B.graph.tail e, B.graph.head e)` for every `e ∈ B.edges`, each
  listed once (found by walking each bundle `b < nV`'s doubly-linked end list and emitting on every
  even `endKey = 2 * e`).

Time bound: `≤ 50 * nV + 90 * |B.edges| + 90` steps.
Space bound: `4 + nV + 3 * |B.edges|` words.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- `args = [tbl, s, h]`: exports slot `s`'s `B.graph` as header `[nV, V_ptr, nE, E_ptr]` at `h`,
vertex list `[0..nV-1]` at `V_ptr = h + 4`, and edge triples `(e, tail e, head e)` at
`E_ptr = h + 4 + nV`, returning `h + 4 + nV + 3 * nE`. -/
def bundleExportGraphStmt : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 3))) ;;                     -- slotPtrBase
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;                       -- p := slotPtr[s]
  .assign 5 (.load (.bin .add (.reg 4) (.const 1))) ;;                     -- nB
  .assign 6 (.load (.bin .add (.reg 4) (.const 2))) ;;                     -- nE
  .assign 7 (.load (.bin .add (.reg 0) (.const 5))) ;;                     -- endBundleBase
  .assign 8 (.load (.bin .add (.reg 0) (.const 7))) ;;                     -- endNextBase
  .assign 9 (.bin .add (.reg 2) (.const 4)) ;;                             -- V_ptr := h + 4
  .assign 10 (.bin .add (.reg 9) (.reg 5)) ;;                              -- E_ptr := h + 4 + nB
  .store (.reg 2) (.reg 5) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 9) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 6) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 10) ;;
  forRange 11 (.const 0) (.reg 5)
    (.store (.bin .add (.reg 9) (.reg 11)) (.reg 11)) ;;
  .assign 12 (.const 0) ;;                                                 -- cnt := 0
  forRange 11 (.const 0) (.reg 5)
    (.assign 13 (.load (.bin .add (.bin .add (.reg 4) (.const 3)) (.reg 11))) ;;  -- cur := head[b]
     .loop (.reg 13)
       (.assign 14 (.bin .sub (.reg 13) (.const 1)) ;;                     -- key := cur - 1
        .cond (.bin .eq (.bin .mod (.reg 14) (.const 2)) (.const 0))
          (.assign 15 (.bin .div (.reg 14) (.const 2)) ;;                  -- e := key / 2
           .assign 16 (.load (.bin .add (.reg 7) (.bin .add (.reg 14) (.const 1)))) ;; -- headBun
           .assign 17 (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 12))) ;;
           .store (.reg 17) (.reg 15) ;;
           .store (.bin .add (.reg 17) (.const 1)) (.reg 11) ;;
           .store (.bin .add (.reg 17) (.const 2)) (.reg 16) ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))
          .nop ;;
        .assign 13 (.load (.bin .add (.reg 8) (.reg 14))))) ;;
  .ret (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 6)))

lemma bundleExportGraphStmt_noRand : bundleExportGraphStmt.NoRand := by
  trivial

/-- Space used by `bundleExportGraphStmt` on a bundle state `B`. -/
def bundleExportSpace (B : BundleState) : ℕ :=
  4 + B.vertices.card + 3 * B.edges.card

/-- Cost bound of `bundleExportGraphStmt` on a bundle state `B`. -/
def bundleExportCost (B : BundleState) : ℕ :=
  50 * B.vertices.card + 100 * B.edges.card + 100

/-- Contract of `bundleExportGraphStmt` (`[tbl, s, h]`). -/
def bundleExportGraphContract (w slotCap vCap eCap tbl h : ℕ)
    (S : BundleTableState slotCap) (m : BundleTableMeta slotCap)
    (j : Fin slotCap) (B : BundleState) : Contract where
  pre args mem :=
    args = [tbl, j.1, h] ∧ 16 ≤ 2 ^ w ∧
    tbl + bundleTableFixedSize slotCap eCap < 2 ^ w ∧
    h + bundleExportSpace B < 2 ^ w ∧
    ZeroFrom mem h ∧
    (∀ a, bundleTableFoot eCap tbl m a → a < h) ∧
    BundleTableRepAt slotCap vCap eCap tbl S m mem ∧
    S j = some B
  post _ mem ret mem' :=
    let nV := B.vertices.card
    let nE := B.edges.card
    let vPtr := h + 4
    let ePtr := h + 4 + nV
    let vL := readList mem' vPtr nV
    let eT := readTriples mem' ePtr nE
    ret = h + bundleExportSpace B ∧
    ZeroFrom mem' ret ∧
    (∀ a < h, mem' a = mem a) ∧
    mem' h = nV ∧ mem' (h + 1) = vPtr ∧ mem' (h + 2) = nE ∧ mem' (h + 3) = ePtr ∧
    vL = List.range nV ∧
    (eT.map Prod.fst).Nodup ∧
    (∀ e, e ∈ eT.map Prod.fst ↔ e ∈ B.edges) ∧
    (∀ t ∈ eT, t.1 ∈ B.edges ∧ t.2.1 = B.graph.tail t.1 ∧ t.2.2 = B.graph.head t.1) ∧
    GraphEq (graphOfLists vL eT) B.graph
  cost _ _ := bundleExportCost B

end

/-! ## Verification helpers -/

public section

private lemma graphEq_of_export {B : BundleState} {nV : ℕ} (hV : B.vertices = Finset.range nV)
    {vL : List ℕ} (hvL : vL = List.range nV)
    {eT : List (ℕ × ℕ × ℕ)} (hnd : (eT.map Prod.fst).Nodup)
    (hmem : ∀ e, e ∈ eT.map Prod.fst ↔ e ∈ B.edges)
    (hspec : ∀ t ∈ eT, t.1 ∈ B.edges ∧ t.2.1 = B.graph.tail t.1 ∧ t.2.2 = B.graph.head t.1) :
    GraphEq (graphOfLists vL eT) B.graph := by
  refine ⟨?_, ?_, ?_⟩
  · change vL.toFinset = B.vertices
    rw [hvL, hV]
    ext v; simp
  · change (eT.map Prod.fst).toFinset = B.edges
    ext e; simp [hmem]
  · intro e he
    have he' : e ∈ eT.map Prod.fst := (hmem e).mpr (by
      change e ∈ (eT.map Prod.fst).toFinset at he
      exact (hmem e).mp (List.mem_toFinset.mp he))
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he'
    have hfind : eT.find? (fun u => u.1 == t.1) = some t := by
      have hgo : ∀ (xs : List (ℕ × ℕ × ℕ)), (xs.map Prod.fst).Nodup → t ∈ xs →
          xs.find? (fun u => u.1 == t.1) = some t := by
        intro xs
        induction xs with
        | nil => intro _ h; cases h
        | cons x xs ih =>
          intro hnd' hm
          rw [List.map_cons, List.nodup_cons] at hnd'
          rcases List.mem_cons.mp hm with rfl | hm'
          · simp
          · have hne : x.1 ≠ t.1 := fun h => hnd'.1 (h ▸ List.mem_map.mpr ⟨t, hm', rfl⟩)
            simp [hne]; exact ih hnd'.2 hm'
      exact hgo eT hnd ht
    have hsp := hspec t ht
    have hfind' : eT.find? (fun u => decide (u.1 = t.1)) = some t := by convert hfind using 2
    exact ⟨by change ((eT.find? _).map fun u => u.2.1).getD 0 = _; rw [hfind']; exact hsp.2.1,
      by change ((eT.find? _).map fun u => u.2.2).getD 0 = _; rw [hfind']; exact hsp.2.2⟩

/-- Total length of all bundle end lists in a valid `BundleSlotRepAt` equals `2 * B.edges.card`,
and the total number of even keys across all bundles equals `B.edges.card`. -/
lemma bundleSlot_sum_ends {nB : ℕ} {B : BundleState}
    (hbo : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (L : ℕ → List ℕ)
    (hL : ∀ b < nB, (L b).Nodup ∧ ∀ k, k ∈ L b ↔ endOfKey k ∈ B.ends b) :
    (∑ b ∈ Finset.range nB, (L b).length) = 2 * B.edges.card ∧
    (∑ b ∈ Finset.range nB, ((L b).filter fun k => k % 2 == 0).length) = B.edges.card := by
  have hcard : ∀ b < nB, (L b).length = (B.ends b).card := by
    intro b hb
    rw [← List.toFinset_card_of_nodup (hL b hb).1]
    apply Finset.card_bij (fun k _ => endOfKey k)
    · intro k hk; exact ((hL b hb).2 k).mp (List.mem_toFinset.mp hk)
    · intro k₁ _ k₂ _ heq
      have := congrArg endKey heq
      rwa [bundle_endKey_endOfKey, bundle_endKey_endOfKey] at this
    · intro x hx
      exact ⟨endKey x, List.mem_toFinset.mpr (((hL b hb).2 (endKey x)).mpr (by rwa [bundle_endOfKey_endKey])),
        bundle_endOfKey_endKey x⟩
  have heven : ∀ b < nB, ((L b).filter fun k => k % 2 == 0).length =
      (B.edges.filter fun e => B.bundleOf (e, true) = b).card := by
    intro b hb
    rw [← List.toFinset_card_of_nodup ((hL b hb).1.filter _)]
    apply Finset.card_bij (fun k _ => k / 2)
    · intro k hk
      obtain ⟨hkL, hk2⟩ := List.mem_filter.mp (List.mem_toFinset.mp hk)
      have hmod : k % 2 = 0 := by simpa using hk2
      have hmem := ((hL b hb).2 k).mp hkL
      have hof : endOfKey k = (k / 2, true) := by simp [endOfKey, hmod]
      rw [hof, BundleState.mem_ends] at hmem
      exact Finset.mem_filter.mpr hmem
    · intro k₁ hk₁ k₂ hk₂ heq
      have h1 : k₁ % 2 = 0 := by simpa using (List.mem_filter.mp (List.mem_toFinset.mp hk₁)).2
      have h2 : k₂ % 2 = 0 := by simpa using (List.mem_filter.mp (List.mem_toFinset.mp hk₂)).2
      omega
    · intro e he
      obtain ⟨heE, heB⟩ := Finset.mem_filter.mp he
      refine ⟨2 * e, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨?_, by simp⟩), by omega⟩
      rw [(hL b hb).2]
      have hof : endOfKey (2 * e) = (e, true) := by simp [endOfKey]
      rw [hof, BundleState.mem_ends]
      exact ⟨heE, heB⟩
  constructor
  · calc ∑ b ∈ Finset.range nB, (L b).length
        = ∑ b ∈ Finset.range nB, (B.ends b).card :=
          Finset.sum_congr rfl fun b hb => hcard b (Finset.mem_range.mp hb)
      _ = (edgeEnds B.edges).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext x
            simp only [Finset.mem_biUnion, Finset.mem_range, BundleState.mem_ends, mem_edgeEnds]
            exact ⟨fun ⟨_, _, h1, _⟩ => h1, fun hx => ⟨B.bundleOf x, hbo x ((mem_edgeEnds _ _).mpr hx), hx, rfl⟩⟩
          · intro b₁ _ b₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro x h1 h2
            exact hne (((BundleState.mem_ends _ _ _).mp h1).2.symm.trans ((BundleState.mem_ends _ _ _).mp h2).2)
      _ = 2 * B.edges.card := card_edgeEnds B.edges
  · calc ∑ b ∈ Finset.range nB, ((L b).filter fun k => k % 2 == 0).length
        = ∑ b ∈ Finset.range nB, (B.edges.filter fun e => B.bundleOf (e, true) = b).card :=
          Finset.sum_congr rfl fun b hb => heven b (Finset.mem_range.mp hb)
      _ = B.edges.card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext e
            simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
            exact ⟨fun ⟨_, _, h1, _⟩ => h1, fun he => ⟨B.bundleOf (e, true),
              hbo (e, true) ((mem_edgeEnds _ _).mpr he), he, rfl⟩⟩
          · intro b₁ _ b₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro e h1 h2
            exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

private lemma readTriples_snoc {mem : ℕ → ℕ} {base n e t hd : ℕ}
    (h1 : ∀ i < n, Function.update (Function.update (Function.update mem (base + 3 * n) e)
        (base + 3 * n + 1) t) (base + 3 * n + 2) hd (base + 3 * i) = mem (base + 3 * i) ∧
      Function.update (Function.update (Function.update mem (base + 3 * n) e)
        (base + 3 * n + 1) t) (base + 3 * n + 2) hd (base + 3 * i + 1) = mem (base + 3 * i + 1) ∧
      Function.update (Function.update (Function.update mem (base + 3 * n) e)
        (base + 3 * n + 1) t) (base + 3 * n + 2) hd (base + 3 * i + 2) = mem (base + 3 * i + 2)) :
    readTriples (Function.update (Function.update (Function.update mem (base + 3 * n) e)
        (base + 3 * n + 1) t) (base + 3 * n + 2) hd) base (n + 1) =
      readTriples mem base n ++ [(e, t, hd)] := by
  simp only [readTriples, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i hi
    obtain ⟨a, b, c⟩ := h1 i (List.mem_range.mp hi)
    simp [a, b, c]
  · simp

private def exportTriplesOf (B : BundleState) (b : ℕ) (xs : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (xs.filter fun k => k % 2 == 0).map fun k => (k / 2, b, B.bundleOf (k / 2, false))

private def exportKeyCost (k : ℕ) : ℕ := if k % 2 == 0 then 68 else 22

private def dllHeadVal : List ℕ → ℕ
  | [] => 0
  | x :: _ => x + 1

private lemma rangeCost_zero_eq_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ b ∈ Finset.range n, f b := by
  induction n with
  | zero => simp [rangeCost]
  | succ n ih =>
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, ← rangeCost_zero_eq_range, ih, Finset.sum_range_succ]

private lemma exportInnerLoop_triple {w slotCap eCap tbl ptr nB nE vPtr ePtr h b : ℕ}
    {p : Program} {B : BundleState} {mem mem1 : ℕ → ℕ} {L_b : List ℕ}
    {baseTriples : List (ℕ × ℕ × ℕ)}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_h : tbl + (12 + 4 * slotCap + 8 * eCap) ≤ h)
    (hhSpace' : h + (4 + nB + 3 * nE) < 2 ^ w)
    (hvPtr : vPtr = h + 4) (hePtr : ePtr = h + 4 + nB)
    (hb : b < nB)
    (hbo : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hendBundleVal : ∀ x ∈ edgeEnds B.edges,
      mem (tbl + 12 + slotCap + eCap + endKey x) = B.bundleOf x)
    (hm1_lt : ∀ a < h, mem1 a = mem a)
    (hLb_dll : IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase ptr + b) (2 * eCap) L_b)
    (hLb_mem : ∀ k, k ∈ L_b ↔ endOfKey k ∈ B.ends b)
    (hlen_le : (baseTriples ++ exportTriplesOf B b L_b).length ≤ nE) :
    let Inv : List ℕ → State → Prop := fun rem s =>
      ∃ pref, L_b = pref ++ rem ∧
        s.regs 4 = ptr ∧ s.regs 5 = nB ∧ s.regs 6 = nE ∧
        s.regs 7 = tbl + 12 + slotCap + eCap ∧
        s.regs 8 = tbl + 12 + slotCap + 5 * eCap ∧
        s.regs 9 = vPtr ∧ s.regs 10 = ePtr ∧ s.regs 11 = b ∧
        s.regs 12 = (baseTriples ++ exportTriplesOf B b pref).length ∧
        s.regs 13 = dllHeadVal rem ∧
        readTriples s.mem ePtr (baseTriples ++ exportTriplesOf B b pref).length =
          baseTriples ++ exportTriplesOf B b pref ∧
        (∀ a, a < ePtr ∨ ePtr + 3 * (baseTriples ++ exportTriplesOf B b pref).length ≤ a →
          s.mem a = mem1 a)
    Triple w p (Inv L_b)
      (.loop (.reg 13)
        (.assign 14 (.bin .sub (.reg 13) (.const 1)) ;;
         .cond (.bin .eq (.bin .mod (.reg 14) (.const 2)) (.const 0))
           (.assign 15 (.bin .div (.reg 14) (.const 2)) ;;
            .assign 16 (.load (.bin .add (.reg 7) (.bin .add (.reg 14) (.const 1)))) ;;
            .assign 17 (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 12))) ;;
            .store (.reg 17) (.reg 15) ;;
            .store (.bin .add (.reg 17) (.const 1)) (.reg 11) ;;
            .store (.bin .add (.reg 17) (.const 2)) (.reg 16) ;;
            .assign 12 (.bin .add (.reg 12) (.const 1)))
           .nop ;;
         .assign 13 (.load (.bin .add (.reg 8) (.reg 14)))))
      (normalPost (Inv []))
      (fun _ => (L_b.map exportKeyCost).sum + L_b.length * 2 + 2) := by
  intro Inv
  refine (Triple.loop_list (w := w) (p := p) (e := .reg 13)
    (Inv := Inv) (Q := normalPost (Inv [])) exportKeyCost
    (fun s hs => by
      rcases hs with ⟨pref, hEq, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, srt, sfr⟩
      dsimp only [dllHeadVal] at s13
      exact ⟨by eval_expr, ⟨pref, hEq, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, srt, sfr⟩⟩)
    (fun x xs s hs => by
      rcases hs with ⟨pref, hEq, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, srt, sfr⟩
      dsimp only [dllHeadVal] at s13
      have hx_mem : x ∈ L_b := by rw [hEq]; simp
      have hx_lt : x < 2 * eCap := hLb_dll.2.1 x hx_mem
      have hidx_lt : pref.length < L_b.length := by rw [hEq]; simp
      have hLidx : L_b[pref.length] = x := by simp [hEq]
      have hnext_mem : mem (tbl + 12 + slotCap + 5 * eCap + x) = dllHeadVal xs := by
        have hnb' : mem (tbl + 12 + slotCap + 5 * eCap + L_b[pref.length]) =
            if pref.length + 1 = L_b.length then 0
            else L_b.getD (pref.length + 1) 0 + 1 :=
          (hLb_dll.2.2.2 pref.length hidx_lt).2
        rw [hLidx] at hnb'; rw [hnb']
        cases xs with
        | nil => simp [dllHeadVal, show pref.length + 1 = L_b.length by rw [hEq]; simp]
        | cons y ys =>
          have hlt1 : pref.length + 1 < L_b.length := by rw [hEq]; simp
          simp only [dllHeadVal, show pref.length + 1 ≠ L_b.length by omega, ↓reduceIte,
            List.getD_eq_getElem _ _ hlt1]
          have hgy : L_b[pref.length + 1] = y := by
            have : (pref ++ x :: y :: ys)[pref.length + 1]'(by simp) = y := by
              rw [List.getElem_append_right (by omega)]; simp
            simp [hEq]
          rw [hgy]
      have hnext_lt : dllHeadVal xs < 2 ^ w := by
        cases xs with
        | nil => simp [dllHeadVal]
        | cons y _ => simp [dllHeadVal]; have := hLb_dll.2.1 y (by rw [hEq]; simp); omega
      have hs_lt : ∀ a < h, s.mem a = mem a := fun a ha =>
        (sfr a (Or.inl (by omega))).trans (hm1_lt a ha)
      have hnext_s : s.mem (tbl + 12 + slotCap + 5 * eCap + x) = dllHeadVal xs :=
        (hs_lt _ (by omega)).trans hnext_mem
      have hsub1 : x + 1 - 1 = x := by omega
      refine ⟨x + 1, by eval_expr, by omega, ?_⟩
      wram_enter; subst hpre
      by_cases hx2 : x % 2 = 0
      · have hpx : exportTriplesOf B b (pref ++ [x]) =
            exportTriplesOf B b pref ++ [(x / 2, b, B.bundleOf (x / 2, false))] := by
          simp [exportTriplesOf, List.filter_append, hx2]
        have hcur_lt : (baseTriples ++ exportTriplesOf B b pref).length < nE := by
          have h1 : (exportTriplesOf B b (pref ++ [x])).length ≤ (exportTriplesOf B b L_b).length := by
            rw [hEq, show pref ++ x :: xs = (pref ++ [x]) ++ xs by simp]
            simp only [exportTriplesOf, List.length_map, List.filter_append, List.length_append]
            omega
          rw [hpx, List.length_append, List.length_singleton] at h1
          simp only [List.length_append] at hlen_le ⊢; omega
        have he_in : x / 2 ∈ B.edges := by
          have := (hLb_mem x).mp hx_mem
          rw [show endOfKey x = (x / 2, true) by simp [endOfKey, hx2], BundleState.mem_ends] at this
          exact this.1
        have hhbun_eq : st.mem (tbl + 12 + slotCap + eCap + (x + 1)) =
            B.bundleOf (x / 2, false) := by
          rw [hs_lt _ (by omega)]
          have := hendBundleVal (x / 2, false) ((mem_edgeEnds _ _).mpr he_in)
          rwa [show endKey (x / 2, false) = x + 1 by simp [endKey]; omega] at this
        have hhbun_lt : B.bundleOf (x / 2, false) < 2 ^ w := by
          have := hbo (x / 2, false) ((mem_edgeEnds _ _).mpr he_in); omega
        set cur := (baseTriples ++ exportTriplesOf B b pref).length
        wram_step; simp only [hsub1]
        wram_step
        wram_step; wram_step
        wram_step; wram_step; dsimp only; simp only [s7, hhbun_eq]
        wram_step; wram_step; dsimp only; simp only [s10, s12]
        wram_step; wram_step; dsimp only
        wram_step; wram_step; dsimp only; simp only [s11]
        wram_step; wram_step; dsimp only
        wram_step; dsimp only; simp only [s12]
        refine runs_assign_le (v := dllHeadVal xs) ?_ ?_ ?_
        · have hval_load : Function.update (Function.update (Function.update st.mem
              (ePtr + 3 * cur) (x / 2)) (ePtr + 3 * cur + 1) b)
              (ePtr + 3 * cur + 2) (B.bundleOf (x / 2, false))
              (tbl + 12 + slotCap + 5 * eCap + x) = dllHeadVal xs := by
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hnext_s
          eval_expr
        · refine ⟨pref ++ [x], by simp [hEq], by simp [s4], by simp [s5], by simp [s6],
            by simp [s7], by simp [s8], by simp [s9], by simp [s10], by simp [s11],
            by rw [hpx, ← List.append_assoc, List.length_append, List.length_singleton]; simp [cur],
            by simp, ?_, ?_⟩
          · rw [hpx, ← List.append_assoc, List.length_append, List.length_singleton]
            change readTriples _ ePtr (cur + 1) =
              (baseTriples ++ exportTriplesOf B b pref) ++ [(x / 2, b, B.bundleOf (x / 2, false))]
            rw [readTriples_snoc (fun i hi => by
              refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne]),
              srt]
          · intro a ha
            rw [hpx, ← List.append_assoc, List.length_append, List.length_singleton] at ha
            change a < ePtr ∨ ePtr + 3 * (cur + 1) ≤ a at ha
            simp (disch := omega) only [Function.update_of_ne]
            exact sfr a (by omega)
        · simp only [exportKeyCost, hx2, beq_self_eq_true, ↓reduceIte]; wram_cost
      · have hmod1 : x % 2 = 1 := by omega
        have hpx : exportTriplesOf B b (pref ++ [x]) = exportTriplesOf B b pref := by
          simp [exportTriplesOf, List.filter_append, hmod1]
        wram_step; simp only [hsub1]
        wram_step; wram_step
        refine runs_assign_le (v := dllHeadVal xs) ?_ ?_ ?_
        · eval_expr
        · refine ⟨pref ++ [x], by simp [hEq], by simp [s4], by simp [s5], by simp [s6],
            by simp [s7], by simp [s8], by simp [s9], by simp [s10], by simp [s11],
            by rw [hpx]; simp [s12], by simp, by rw [hpx]; exact srt,
            fun a ha => sfr a (by simpa [hpx] using ha)⟩
        · simp only [exportKeyCost, hmod1, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
          wram_cost)
    L_b).mono_cost fun _ _ => by simp only [Expr.size]; omega

private def exportEmitPref (B : BundleState) (L : ℕ → List ℕ) (i : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range i).flatMap fun b => exportTriplesOf B b (L b)

private lemma exportOuterLoop_triple {w slotCap eCap tbl ptr bunCap nB nE vPtr ePtr h : ℕ}
    {p : Program} {B : BundleState} {mem : ℕ → ℕ} {st1 : State} {L : ℕ → List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hptr_h : ptr + (3 + 6 * bunCap) ≤ h)
    (htbl_h : tbl + (12 + 4 * slotCap + 8 * eCap) ≤ h)
    (hhSpace' : h + (4 + nB + 3 * nE) < 2 ^ w)
    (hnB : nB ≤ bunCap)
    (hvPtr : vPtr = h + 4) (hePtr : ePtr = h + 4 + nB)
    (hbo : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hendBundleVal : ∀ x ∈ edgeEnds B.edges,
      mem (tbl + 12 + slotCap + eCap + endKey x) = B.bundleOf x)
    (hL_dll : ∀ b < nB, IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase ptr + b) (2 * eCap) (L b))
    (hL_mem : ∀ b < nB, ∀ k, k ∈ L b ↔ endOfKey k ∈ B.ends b)
    (hemit_le : ∀ i ≤ nB, (exportEmitPref B L i).length ≤ nE)
    (r1_4 : st1.regs 4 = ptr) (r1_5 : st1.regs 5 = nB) (r1_6 : st1.regs 6 = nE)
    (r1_7 : st1.regs 7 = tbl + 12 + slotCap + eCap)
    (r1_8 : st1.regs 8 = tbl + 12 + slotCap + 5 * eCap)
    (r1_9 : st1.regs 9 = vPtr) (r1_10 : st1.regs 10 = ePtr)
    (m1_fr : ∀ a, a < h ∨ vPtr + nB ≤ a → st1.mem a = mem a) :
    let bunCost : ℕ → ℕ := fun b => ((L b).map exportKeyCost).sum + (L b).length * 2 + 12
    let Inv2 : ℕ → State → Prop := fun b st =>
      st.regs 4 = ptr ∧ st.regs 5 = nB ∧ st.regs 6 = nE ∧
      st.regs 7 = tbl + 12 + slotCap + eCap ∧ st.regs 8 = tbl + 12 + slotCap + 5 * eCap ∧
      st.regs 9 = vPtr ∧ st.regs 10 = ePtr ∧ st.regs 11 = b ∧
      st.regs 12 = (exportEmitPref B L b).length ∧
      readTriples st.mem ePtr (exportEmitPref B L b).length = exportEmitPref B L b ∧
      (∀ a, a < ePtr ∨ ePtr + 3 * (exportEmitPref B L b).length ≤ a → st.mem a = st1.mem a)
    Triple w p (fun st => st = { st1 with regs := Function.update st1.regs 12 0 })
      (forRange 11 (.const 0) (.reg 5)
        (.assign 13 (.load (.bin .add (.bin .add (.reg 4) (.const 3)) (.reg 11))) ;;
         .loop (.reg 13)
           (.assign 14 (.bin .sub (.reg 13) (.const 1)) ;;
            .cond (.bin .eq (.bin .mod (.reg 14) (.const 2)) (.const 0))
              (.assign 15 (.bin .div (.reg 14) (.const 2)) ;;
               .assign 16 (.load (.bin .add (.reg 7) (.bin .add (.reg 14) (.const 1)))) ;;
               .assign 17 (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 12))) ;;
               .store (.reg 17) (.reg 15) ;;
               .store (.bin .add (.reg 17) (.const 1)) (.reg 11) ;;
               .store (.bin .add (.reg 17) (.const 2)) (.reg 16) ;;
               .assign 12 (.bin .add (.reg 12) (.const 1)))
              .nop ;;
            .assign 13 (.load (.bin .add (.reg 8) (.reg 14))))))
      (normalPost (Inv2 nB))
      (fun _ => rangeCost bunCost 0 nB + nB * 9 + 7) := by
  intro bunCost Inv2
  refine (Triple.forRange_le (p := p) (w := w) (r := 11) (lo := .const 0) (hi := .reg 5)
    (P := fun st => st = { st1 with regs := Function.update st1.regs 12 0 })
    (Inv := Inv2) bunCost 0 nB (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, by simp [r1_4], by simp [r1_5], by simp [r1_6], by simp [r1_7],
        by simp [r1_8], by simp [r1_9], by simp [r1_10], by simp,
        by simp [exportEmitPref], by simp [exportEmitPref, readTriples], fun _ _ => rfl⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.1; eval_expr)
    (fun b _ hb => by
      intro st ω hI
      rcases hI with ⟨r4, r5, r6, r7, r8, r9, r10, r11, r12, hrt, hfr⟩
      have hmem_lt : ∀ a < h, st.mem a = mem a := fun a ha =>
        (hfr a (Or.inl (by omega))).trans (m1_fr a (Or.inl ha))
      have hLb_dll := hL_dll b hb
      have hhd_mem : st.mem (ptr + 3 + b) = dllHeadVal (L b) := by
        rw [hmem_lt (ptr + 3 + b) (by omega)]
        cases hLbc : L b with
        | nil => simpa [bsHeadBase, dllHeadVal, hLbc] using hLb_dll.2.2.1
        | cons x _ => simpa [bsHeadBase, dllHeadVal, hLbc] using hLb_dll.2.2.1
      have hhd_lt : dllHeadVal (L b) < 2 ^ w := by
        cases hLbc : L b with
        | nil => simp [dllHeadVal]
        | cons x _ => simp [dllHeadVal]; have := hLb_dll.2.1 x (hLbc ▸ List.mem_cons_self); omega
      have hstep : exportEmitPref B L (b + 1) = exportEmitPref B L b ++ exportTriplesOf B b (L b) := by
        simp [exportEmitPref, List.range_succ]
      have hinner := exportInnerLoop_triple (p := p) (B := B) (mem := mem) (mem1 := st1.mem)
        (L_b := L b) (baseTriples := exportEmitPref B L b) hw16 htbl_h hhSpace' hvPtr hePtr hb hbo
        hendBundleVal (fun a ha => m1_fr a (Or.inl ha)) hLb_dll (hL_mem b hb)
        (hstep ▸ hemit_le (b + 1) (by omega))
      refine runs_start_le ?_
      wram_step; dsimp only; simp only [hhd_mem]
      refine runs_triple_le hinner ?_ ?_ (by simp only [bunCost, Expr.size]; omega)
      · refine ⟨[], rfl, by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8],
          by simp [r9], by simp [r10], by simp [r11], by simp [r12, exportTriplesOf], by simp,
          by simpa [exportTriplesOf] using hrt,
          fun a ha => hfr a (by simpa [exportTriplesOf] using ha)⟩
      · intro o st' hq
        cases o with
        | returned _ => exact False.elim hq
        | normal =>
          rcases hq with ⟨pref, hEq, s4, s5, s6, s7, s8, s9, s10, s11, s12, _, srt, sfr⟩
          have hpref_eq : pref = L b := by simpa using hEq.symm
          subst hpref_eq
          refine ⟨⟨by simp [s4], by simp [s5], by simp [s6], by simp [s7], by simp [s8],
            by simp [s9], by simp [s10], by simp, by rw [hstep]; simp [s12],
            by rw [hstep]; exact srt, fun a ha => sfr a (by rwa [← hstep])⟩, s11⟩)).mono_cost
    fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega

private lemma exportEmitPref_props {nB : ℕ} {B : BundleState} {L : ℕ → List ℕ}
    (hbo : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hL_nd : ∀ b < nB, (L b).Nodup)
    (hL_mem : ∀ b < nB, ∀ k, k ∈ L b ↔ endOfKey k ∈ B.ends b) :
    (exportEmitPref B L nB).length = B.edges.card ∧
    (∀ i ≤ nB, (exportEmitPref B L i).length ≤ B.edges.card) ∧
    ((exportEmitPref B L nB).map Prod.fst).Nodup ∧
    (∀ e, e ∈ (exportEmitPref B L nB).map Prod.fst ↔ e ∈ B.edges) ∧
    (∀ t ∈ exportEmitPref B L nB,
      t.1 ∈ B.edges ∧ t.2.1 = B.graph.tail t.1 ∧ t.2.2 = B.graph.head t.1) ∧
    (∑ b ∈ Finset.range nB, (L b).length) = 2 * B.edges.card ∧
    (∑ b ∈ Finset.range nB, ((L b).filter fun k => k % 2 == 0).length) = B.edges.card := by
  have hsum_ends := bundleSlot_sum_ends hbo L (fun b hb => ⟨hL_nd b hb, hL_mem b hb⟩)
  have hemit_len : ∀ i, (exportEmitPref B L i).length =
      ∑ b ∈ Finset.range i, ((L b).filter fun k => k % 2 == 0).length := by
    intro i
    induction i with
    | zero => simp [exportEmitPref]
    | succ i ih =>
      simp only [exportEmitPref, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.length_append, Finset.sum_range_succ, exportTriplesOf,
        List.length_map]
      exact congrArg (· + _) ih
  refine ⟨by rw [hemit_len, hsum_ends.2], fun i hi => by
      rw [hemit_len, ← hsum_ends.2]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hi), ?_, ?_, ?_, hsum_ends.1, hsum_ends.2⟩
  · suffices ∀ i ≤ nB, ((exportEmitPref B L i).map Prod.fst).Nodup from this nB le_rfl
    intro i hi
    induction i with
    | zero => simp [exportEmitPref]
    | succ i ih =>
      have hi_lt : i < nB := by omega
      simp only [exportEmitPref, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.map_append, List.nodup_append]
      refine ⟨ih (by omega), ?_, ?_⟩
      · simp only [exportTriplesOf, List.map_map]
        refine ((hL_nd i hi_lt).filter _).map_on fun k₁ hk₁ k₂ hk₂ heq => ?_
        have h1 : k₁ % 2 = 0 := by simpa using (List.mem_filter.mp hk₁).2
        have h2 : k₂ % 2 = 0 := by simpa using (List.mem_filter.mp hk₂).2
        dsimp only [Function.comp_apply] at heq; omega
      · intro e₁ he1 e₂ he2 hEqE
        subst hEqE
        obtain ⟨t1, ht1, rfl⟩ := List.mem_map.mp he1
        obtain ⟨b1, hb1, ht1b⟩ := List.mem_flatMap.mp ht1
        have hb1_lt : b1 < i := List.mem_range.mp hb1
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ht1b
        obtain ⟨hk1L, hk1e⟩ := List.mem_filter.mp hk1
        have hk1mod : k1 % 2 = 0 := by simpa using hk1e
        have h1end : (k1 / 2, true) ∈ B.ends b1 := by
          have := (hL_mem b1 (by omega) k1).mp hk1L
          rwa [show endOfKey k1 = (k1 / 2, true) by simp [endOfKey, hk1mod]] at this
        obtain ⟨k2, ⟨hk2L, hk2e⟩, he2eq⟩ :
            ∃ k2, (k2 ∈ L i ∧ k2 % 2 = 0) ∧ k2 / 2 = k1 / 2 := by
          simpa [exportTriplesOf] using he2
        have h2end : (k2 / 2, true) ∈ B.ends i := by
          have := (hL_mem i hi_lt k2).mp hk2L
          rwa [show endOfKey k2 = (k2 / 2, true) by simp [endOfKey, hk2e]] at this
        rw [he2eq] at h2end
        have hb1eq : B.bundleOf (k1 / 2, true) = b1 := ((BundleState.mem_ends _ _ _).mp h1end).2
        have hieq : B.bundleOf (k1 / 2, true) = i := ((BundleState.mem_ends _ _ _).mp h2end).2
        omega
  · intro e
    constructor
    · intro he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
      obtain ⟨b, hb, htb⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp htb
      obtain ⟨hkL, hke⟩ := List.mem_filter.mp hk
      have hend := (hL_mem b (List.mem_range.mp hb) k).mp hkL
      rw [show endOfKey k = (k / 2, true) by simp [endOfKey, show k % 2 = 0 by simpa using hke],
        BundleState.mem_ends] at hend
      exact hend.1
    · intro he
      have hb_lt : B.bundleOf (e, true) < nB := hbo (e, true) ((mem_edgeEnds _ _).mpr he)
      have h2e : 2 * e ∈ L (B.bundleOf (e, true)) := (hL_mem _ hb_lt (2 * e)).mpr (by
        rw [show endOfKey (2 * e) = (e, true) by simp [endOfKey], BundleState.mem_ends]
        exact ⟨he, rfl⟩)
      refine List.mem_map.mpr ⟨(e, B.bundleOf (e, true), B.bundleOf (e, false)),
        List.mem_flatMap.mpr ⟨B.bundleOf (e, true), List.mem_range.mpr hb_lt,
          List.mem_map.mpr ⟨2 * e, List.mem_filter.mpr ⟨h2e, by simp⟩, by
            simp [Nat.mul_div_right _ (by omega : 0 < 2)]⟩⟩, rfl⟩
  · intro t ht
    obtain ⟨b, hb, htb⟩ := List.mem_flatMap.mp ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp htb
    obtain ⟨hkL, hke⟩ := List.mem_filter.mp hk
    have hend := (hL_mem b (List.mem_range.mp hb) k).mp hkL
    rw [show endOfKey k = (k / 2, true) by simp [endOfKey, show k % 2 = 0 by simpa using hke],
      BundleState.mem_ends] at hend
    exact ⟨hend.1, by simp [BundleState.graph, hend.2], by simp [BundleState.graph]⟩

private lemma exportVertLoop_triple {w slotCap eCap tbl ptr nB nE vPtr ePtr h : ℕ}
    {p : Program} {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hhSpace' : h + (4 + nB + 3 * nE) < 2 ^ w)
    (hvPtr : vPtr = h + 4) (hePtr : ePtr = h + 4 + nB) :
    let Pre1 : State → Prop := fun st =>
      st.regs 4 = ptr ∧ st.regs 5 = nB ∧ st.regs 6 = nE ∧
      st.regs 7 = tbl + 12 + slotCap + eCap ∧ st.regs 8 = tbl + 12 + slotCap + 5 * eCap ∧
      st.regs 9 = vPtr ∧ st.regs 10 = ePtr ∧
      st.mem h = nB ∧ st.mem (h + 1) = vPtr ∧ st.mem (h + 2) = nE ∧ st.mem (h + 3) = ePtr ∧
      (∀ a, a < h ∨ vPtr ≤ a → st.mem a = mem a)
    let Inv1 : ℕ → State → Prop := fun i st =>
      st.regs 4 = ptr ∧ st.regs 5 = nB ∧ st.regs 6 = nE ∧
      st.regs 7 = tbl + 12 + slotCap + eCap ∧ st.regs 8 = tbl + 12 + slotCap + 5 * eCap ∧
      st.regs 9 = vPtr ∧ st.regs 10 = ePtr ∧ st.regs 11 = i ∧
      st.mem h = nB ∧ st.mem (h + 1) = vPtr ∧ st.mem (h + 2) = nE ∧ st.mem (h + 3) = ePtr ∧
      (∀ k < i, st.mem (vPtr + k) = k) ∧
      (∀ a, a < h ∨ vPtr + i ≤ a → st.mem a = mem a)
    Triple w p Pre1
      (forRange 11 (.const 0) (.reg 5) (.store (.bin .add (.reg 9) (.reg 11)) (.reg 11)))
      (normalPost (Inv1 nB)) (fun _ => nB * 14 + 7) := by
  intro Pre1 Inv1
  refine (Triple.forRange_const (p := p) (w := w) (r := 11) (lo := .const 0) (hi := .reg 5)
    (body := .store (.bin .add (.reg 9) (.reg 11)) (.reg 11))
    (P := Pre1) (Inv := Inv1) 5 0 nB (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st hst => by
      rcases hst with ⟨r4, r5, r6, r7, r8, r9, r10, mh0, mh1, mh2, mh3, hfr⟩
      exact ⟨by eval_expr, by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8],
        by simp [r9], by simp [r10], by simp, mh0, mh1, mh2, mh3, fun k hk => by omega,
        fun a ha => hfr a (by simpa using ha)⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.1; eval_expr)
    (fun i _ hi => by
      wram_enter
      rcases hpre with ⟨r4, r5, r6, r7, r8, r9, r10, r11, mh0, mh1, mh2, mh3, hwr, hfr⟩
      wram_run
      · refine ⟨⟨by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8],
          by simp [r9], by simp [r10], by simp,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact mh0,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact mh1,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact mh2,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact mh3, fun k hk => by
            dsimp only; by_cases hki : k = i
            · subst hki; exact Function.update_self _ _ _
            · rw [Function.update_of_ne (by omega)]; exact hwr k (by omega),
          fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)⟩, r11⟩
      · wram_cost)).mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega

/-- Verification of `bundleExportGraphStmt`. -/
theorem bundleExportGraph_meetsContract {w slotCap vCap eCap tbl h : ℕ}
    {S : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {j : Fin slotCap} {B : BundleState} {p : Program} {bProc : ℕ}
    (hp : p.HasAt bProc [bundleExportGraphStmt]) :
    MeetsContract w p bProc (bundleExportGraphContract w slotCap vCap eCap tbl h S m j B) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, htblFit, hhSpace, hzero, hfoot, hrep, hSj⟩
  have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
  rw [hSj] at hslot
  cases hm : m.slotBlocks j with
  | none => rw [hm] at hslot; exact False.elim hslot
  | some pb =>
    rcases pb with ⟨ptr, bunCap⟩
    rw [hm] at hslot
    obtain ⟨nB, hBV, hnB, hBE, hbo, _, _, hnbEq, hneEq, hdll, _, _, _⟩ := hslot.2.1
    have hVcard : B.vertices.card = nB := by rw [hBV, Finset.card_range]
    have hj_lt : j.1 < slotCap := j.isLt
    have hptr_h : ptr + (3 + 6 * bunCap) ≤ h := by
      have hlast : bundleTableFoot eCap tbl m (ptr + (bundleSlotBlockSize bunCap - 1)) :=
        Or.inr ⟨j, ptr, bunCap, hm, Nat.le_add_right _ _, by unfold bundleSlotBlockSize; omega⟩
      have hlt := hfoot _ hlast
      unfold bundleSlotBlockSize at hlt; omega
    have htbl_h : tbl + (12 + 4 * slotCap + 8 * eCap) ≤ h := by
      have hlast : bundleTableFoot eCap tbl m (tbl + (bundleTableFixedSize slotCap eCap - 1)) :=
        Or.inl ⟨Nat.le_add_right _ _, by unfold bundleTableFixedSize; omega⟩
      have hlt := hfoot _ hlast
      unfold bundleTableFixedSize at hlt; omega
    have htblFit' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htblFit
    set vPtr := h + 4
    set ePtr := h + 4 + nB
    set nE := B.edges.card
    have hsp : bundleExportSpace B = 4 + nB + 3 * nE := by unfold bundleExportSpace; rw [hVcard]
    have hhSpace' : h + (4 + nB + 3 * nE) < 2 ^ w := by rwa [← hsp]
    have hcost_eq : bundleExportCost B = 50 * nB + 100 * nE + 100 := by
      unfold bundleExportCost; rw [hVcard]
    have hslotPtrBase : mem (tbl + 3) = tbl + 12 := hrep.2.2.2.1
    have hptrEq : mem (tbl + 12 + j.1) = ptr := hslot.1
    have hnbEq' : mem (ptr + 1) = nB := hnbEq
    have hneEq' : mem (ptr + 2) = nE := hneEq
    have hendBundleBase : mem (tbl + 5) = tbl + 12 + slotCap + eCap := hrep.2.2.2.2.2.1
    have hendNextBase : mem (tbl + 7) = tbl + 12 + slotCap + 5 * eCap := hrep.2.2.2.2.2.2.2.1
    have hendBundleVal : ∀ x ∈ edgeEnds B.edges,
        mem (tbl + 12 + slotCap + eCap + endKey x) = B.bundleOf x :=
      hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j B hSj
    have hLex : ∃ L : ℕ → List ℕ,
        (∀ b < nB, IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap)
          (btEndNextBase tbl slotCap eCap) (bsHeadBase ptr + b) (2 * eCap) (L b)) ∧
        (∀ b < nB, ∀ k, k ∈ L b ↔ endOfKey k ∈ B.ends b) := by
      classical
      exact ⟨fun b => if hb : b < nB then (hdll b hb).choose else [],
        fun b hb => by simp only [dite_eq_left hb]; exact (hdll b hb).choose_spec.1,
        fun b hb => by simp only [dite_eq_left hb]; exact (hdll b hb).choose_spec.2.2⟩
    obtain ⟨L, hL_dll, hL_mem⟩ := hLex
    obtain ⟨hemit_nB_len, hemit_le, hemit_nodup, hemit_mem, hemit_spec, hsum1, hsum2⟩ :=
      exportEmitPref_props hbo (fun b hb => (hL_dll b hb).1) hL_mem
    -- Straight-line prefix: step through the 6 loads rewriting each read value, then `wram_run`
    refine runs_start_le ?_
    dsimp only [bundleExportGraphStmt, startState]
    wram_step; simp only [hslotPtrBase]
    wram_step; simp only [hptrEq]
    wram_step; simp only [hnbEq']
    wram_step; simp only [hneEq']
    wram_step; simp only [hendBundleBase]
    wram_step; simp only [hendNextBase]
    wram_run
    -- Loop 1: write vertex list [0..nB-1] at vPtr
    have hloop1 := exportVertLoop_triple (w := w) (slotCap := slotCap) (eCap := eCap)
      (tbl := tbl) (ptr := ptr) (nB := nB) (nE := nE) (vPtr := vPtr) (ePtr := ePtr) (h := h)
      (p := p) (mem := mem) hw16 hhSpace' rfl rfl
    refine runs_seq_triple_le hloop1 ?_ ?_
    · refine ⟨by simp, by simp, by simp, by simp, by simp, by simp [vPtr], by simp [ePtr],
        ?_, ?_, ?_, by simp [ePtr], fun a ha => by simp (disch := omega) only [Function.update_of_ne]⟩
      · simp (disch := omega) only [Function.update_of_ne]; simp
      · simp (disch := omega) only [Function.update_of_ne]; simp [vPtr]
      · simp (disch := omega) only [Function.update_of_ne]; simp
    intro st1 hI1
    wram_step
    rcases hI1 with ⟨r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_10, _, m1_h0, m1_h1, m1_h2, m1_h3, m1_v, m1_fr⟩
    -- Loop 2: walk every bundle DLL and emit edge triples on even keys
    let bunCost : ℕ → ℕ := fun b => ((L b).map exportKeyCost).sum + (L b).length * 2 + 12
    have hloop2 := exportOuterLoop_triple (p := p) (B := B) (mem := mem) (st1 := st1) (L := L)
      hw16 hptr_h htbl_h hhSpace' hnB rfl rfl hbo hendBundleVal hL_dll hL_mem hemit_le
      r1_4 r1_5 r1_6 r1_7 r1_8 r1_9 r1_10 m1_fr
    refine runs_seq_triple_le hloop2 rfl ?_
    intro stF hIF
    clear hloop1 hloop2
    rcases hIF with ⟨_, _, f6, _, _, _, f10, _, _, f_rt, f_fr⟩
    have hsum_bunCost : rangeCost bunCost 0 nB ≤ 12 * nB + 94 * nE := by
      have hkc : ∀ b < nB, ((L b).map exportKeyCost).sum =
          46 * ((L b).filter fun k => k % 2 == 0).length + 22 * (L b).length := by
        intro b _
        induction L b with
        | nil => simp
        | cons k ks ih =>
          by_cases hk : k % 2 = 0
          · simp [exportKeyCost, hk, ih]; omega
          · have hk1 : (k % 2 == 0) = false := by simp [hk]
            simp [exportKeyCost, hk1, ih]; omega
      rw [rangeCost_zero_eq_sum]
      have hle_sum : (∑ b ∈ Finset.range nB, bunCost b) =
          46 * (∑ b ∈ Finset.range nB, ((L b).filter fun k => k % 2 == 0).length) +
          24 * (∑ b ∈ Finset.range nB, (L b).length) + 12 * nB := by
        calc ∑ b ∈ Finset.range nB, bunCost b
            = ∑ b ∈ Finset.range nB, (46 * ((L b).filter fun k => k % 2 == 0).length +
                24 * (L b).length + 12) :=
              Finset.sum_congr rfl fun b hb => by
                simp only [bunCost, hkc b (Finset.mem_range.mp hb)]; omega
          _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
      rw [hle_sum, hsum1, hsum2]; omega
    refine runs_ret_le (v := ePtr + 3 * nE) (by eval_expr) ?_ ?_
    · have hlen_eq : (exportEmitPref B L nB).length = nE := hemit_nB_len
      have hvL : readList stF.mem vPtr nB = List.range nB := by
        simp only [readList]
        conv_rhs => rw [← List.map_id (List.range nB)]
        apply List.map_congr_left
        intro k hk
        rw [f_fr (vPtr + k) (Or.inl (by have := List.mem_range.mp hk; omega))]
        exact m1_v k (List.mem_range.mp hk)
      have heT : readTriples stF.mem ePtr nE = exportEmitPref B L nB := by
        rw [← hlen_eq]; exact f_rt
      have hret_eq : ePtr + 3 * nE = h + bundleExportSpace B := by
        rw [hsp]; simp only [ePtr]; omega
      have hf_lt : ∀ a < h + 4, stF.mem a = st1.mem a := fun a ha =>
        f_fr a (Or.inl (Nat.lt_of_lt_of_le ha (Nat.le_add_right _ _)))
      have hlt_h : ∀ a < h, stF.mem a = mem a := fun a ha =>
        (hf_lt a (Nat.lt_add_right 4 ha)).trans (m1_fr a (Or.inl ha))
      have hhdr_F : stF.mem h = nB ∧ stF.mem (h + 1) = vPtr ∧ stF.mem (h + 2) = nE ∧
          stF.mem (h + 3) = ePtr :=
        ⟨(hf_lt h (by simp)).trans m1_h0, (hf_lt (h + 1) (Nat.add_lt_add_left (by decide) h)).trans m1_h1,
         (hf_lt (h + 2) (Nat.add_lt_add_left (by decide) h)).trans m1_h2,
         (hf_lt (h + 3) (Nat.add_lt_add_left (by decide) h)).trans m1_h3⟩
      have hzeroF : ZeroFrom stF.mem (ePtr + 3 * nE) := fun a ha => by
        rw [f_fr a (Or.inr (by rw [hlen_eq]; exact ha)),
          m1_fr a (Or.inr (Nat.le_trans (Nat.le_add_right _ _) ha))]
        exact hzero a (Nat.le_trans (Nat.le_trans (Nat.le_add_right h (4 + nB)) (by simp [ePtr, Nat.add_assoc]))
          (Nat.le_trans (Nat.le_add_right _ _) ha))
      dsimp only [bundleExportGraphContract, Outcome.value]; rw [hVcard]
      exact ⟨hret_eq, hret_eq ▸ hzeroF, hlt_h, hhdr_F.1, hhdr_F.2.1, hhdr_F.2.2.1, hhdr_F.2.2.2,
        hvL, heT ▸ hemit_nodup, heT ▸ hemit_mem, heT ▸ hemit_spec,
        graphEq_of_export hBV hvL (heT ▸ hemit_nodup) (heT ▸ hemit_mem) (heT ▸ hemit_spec)⟩
    · dsimp only [bundleExportGraphContract]; dsimp only [bunCost] at hsum_bunCost
      rw [hcost_eq]
      simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
      clear * - hsum_bunCost; omega

end

end MinCostFlow.SparseCore.Program
