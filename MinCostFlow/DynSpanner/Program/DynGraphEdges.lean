module

public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph edge insertion and deletion definitions (`DynGraphEdges`)

This file defines `dgEdgeProcs bOps` (`dgInsertEdgeStmt` and `dgDeleteEdgeStmt`), their contracts
(`dgInsertEdgeContract` and `dgDeleteEdgeContract`), and shared list/swap-delete helpers.
Verifications live in `MinCostFlow.DynSpanner.Program.DynGraphInsert` and
`MinCostFlow.DynSpanner.Program.DynGraphDelete`.

* `dgIdxInsertEdge` (`0` in `dgEdgeProcs bOps`): insert edge `e = (u, v)` in `O(1)` time (no-op if
  `e ∈ G.E` or `e ≥ eCap`). Self-loops (`u = v`) properly insert both half-edges `2 * e` and
  `2 * e + 1` into `incL (extToInt[u])`.
* `dgIdxDeleteEdge` (`1` in `dgEdgeProcs bOps`): delete edge `e` in `O(1)` time using swap-with-last
  on `eList`/`ePos` and `dgDllRemove` on both half-edges (no-op if `e ∉ G.E`, including `e ≥ eCap`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

def dgIdxInsertEdge : ℕ := 0
def dgIdxDeleteEdge : ℕ := 1

/-- Part 1 of edge insertion: set `ePres[e] := 1`, append `e` to `eList`, set `ePos[e] := m`,
increment `m`. Expects `r0 = gPtr, r1 = e, r2 = u, r3 = v, r4 = vCap, r5 = eCap`. -/
def dgInsertEdgePart1Stmt : Stmt :=
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 4))) ;;
  .store (.bin .add (.reg 6) (.reg 1)) (.const 1) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .store (.bin .add (.bin .add (.reg 6) (.reg 5)) (.reg 7)) (.reg 1) ;;
  .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 5))) (.reg 1)) (.reg 7) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.bin .add (.reg 7) (.const 1))

/-- Part 2 of edge insertion: load `s_u, s_v`, store `eTailSlot[e], eHeadSlot[e]`, and compute
base pointers `r10 = hePrevBase, r11 = heNextBase, r12 = incHeadBase, r13 = slotDegBase`. -/
def dgInsertEdgePart2Stmt : Stmt :=
  .assign 8 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 4))) (.reg 2))) ;;
  .assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 4))) (.reg 3))) ;;
  .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 5))) (.reg 1)) (.reg 8) ;;
  .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 5))) (.reg 1)) (.reg 9) ;;
  .assign 10 (.bin .add (.reg 6) (.bin .mul (.const 5) (.reg 5))) ;;
  .assign 11 (.bin .add (.reg 6) (.bin .mul (.const 7) (.reg 5))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 4))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 4)))

/-- Insert edge `e = (u, v)` (`[gPtr, e, u, v]`), no-op if `e` is already present or `e ≥ eCap`. -/
def dgInsertEdgeStmt (bOps : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .lt (.reg 1) (.reg 5))
    (.cond (.bin .eq (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 4))) (.reg 1))) (.const 0))
      (dgInsertEdgePart1Stmt ;;
       dgInsertEdgePart2Stmt ;;
       .call 14 (bOps + dgIdxDllCons)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 8), .bin .add (.reg 13) (.reg 8), .bin .mul (.const 2) (.reg 1)] ;;
       .call 14 (bOps + dgIdxDllCons)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 9), .bin .add (.reg 13) (.reg 9), .bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)])
      .nop)
    .nop ;;
  .ret (.const 0)

/-- Part 1 of edge deletion: clear `ePres[e]`, decrement `m`, swap `last := eList[m]` into
`pos := ePos[e]` and set `ePos[last] := pos`. Expects `r0 = gPtr, r1 = e, r2 = vCap, r3 = eCap`. -/
def dgDeleteEdgePart1Stmt : Stmt :=
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) ;;
  .store (.bin .add (.reg 6) (.reg 1)) (.const 0) ;;
  .assign 7 (.bin .sub (.load (.bin .add (.reg 0) (.const 3))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 7) ;;
  .assign 8 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 1))) ;;
  .assign 9 (.load (.bin .add (.bin .add (.reg 6) (.reg 3)) (.reg 7))) ;;
  .store (.bin .add (.bin .add (.reg 6) (.reg 3)) (.reg 8)) (.reg 9) ;;
  .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 9)) (.reg 8)

/-- Part 2 of edge deletion: load `s_u := eTailSlot[e]`, `s_v := eHeadSlot[e]` into `r4, r5` and
compute base pointers `r10..r13`. -/
def dgDeleteEdgePart2Stmt : Stmt :=
  .assign 4 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 3))) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 3))) (.reg 1))) ;;
  .assign 10 (.bin .add (.reg 6) (.bin .mul (.const 5) (.reg 3))) ;;
  .assign 11 (.bin .add (.reg 6) (.bin .mul (.const 7) (.reg 3))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 2))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 2)))

/-- Delete edge `e` (`[gPtr, e]`), no-op if `e ∉ G.E` (including `e ≥ eCap`). -/
def dgDeleteEdgeStmt (bOps : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .lt (.reg 1) (.reg 3))
    (.cond (.bin .eq (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) (.reg 1))) (.const 1))
      (dgDeleteEdgePart1Stmt ;;
       dgDeleteEdgePart2Stmt ;;
       .call 14 (bOps + dgIdxDllRemove)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 4), .bin .add (.reg 13) (.reg 4), .bin .mul (.const 2) (.reg 1)] ;;
       .call 14 (bOps + dgIdxDllRemove)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 5), .bin .add (.reg 13) (.reg 5), .bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)])
      .nop)
    .nop ;;
  .ret (.const 0)

/-- Dynamic-graph edge insertion and deletion procedures (`[dgInsertEdgeStmt, dgDeleteEdgeStmt]`). -/
def dgEdgeProcs (bOps : ℕ) : List Stmt :=
  [dgInsertEdgeStmt bOps, dgDeleteEdgeStmt bOps]

lemma dgEdgeProcs_length (bOps : ℕ) : (dgEdgeProcs bOps).length = 2 := rfl

lemma dgEdgeProcs_noRand (bOps : ℕ) : ∀ s ∈ dgEdgeProcs bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract for `dgInsertEdgeStmt` (`[gPtr, e, u, v]`) specialized to `(vCap, eCap, G)`. -/
def dgInsertEdgeContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr e u v, args = [gPtr, e, u, v] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    u ∈ G.V ∧ v ∈ G.V ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr e u v, args = [gPtr, e, u, v] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap
      (if e < eCap ∧ e ∉ G.E then G.applyUpdate (.insert e u v) else G) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 450

/-- Contract for `dgDeleteEdgeStmt` (`[gPtr, e]`) specialized to `(vCap, eCap, G)`. -/
def dgDeleteEdgeContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr e, args = [gPtr, e] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr e, args = [gPtr, e] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap
      (if e ∈ G.E then G.applyUpdate (.delete e) else G) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 450

end

/-! ## Shared list and swap-with-last helpers -/

public section

lemma eList_swap_delete {G : MGraph} {eL : List ℕ} {e : ℕ}
    (heL_len : eL.length = G.m) (heL_nd : eL.Nodup)
    (heL_mem : ∀ x, x ∈ eL ↔ x ∈ G.E) (heE : e ∈ G.E) :
    let pos := eL.idxOf e
    let m' := G.m - 1
    let last := eL[m']'(by
      have hm_pos : 0 < G.m := Finset.card_pos.mpr ⟨e, heE⟩
      omega)
    let eL' := if pos = m' then eL.take m' else (eL.take m').set pos last
    pos < G.m ∧
    eL'.length = (G.E.erase e).card ∧
    eL'.Nodup ∧
    (∀ x, x ∈ eL' ↔ x ∈ G.E.erase e) ∧
    ∀ i (hi : i < m'), eL'[i]'(by
      dsimp only [eL']
      split_ifs <;> simp [List.length_take, List.length_set, heL_len] <;> omega) =
      if i = pos then last else eL[i]'(by omega) := by
  intro pos m' last eL'
  have hm_pos : 0 < G.m := Finset.card_pos.mpr ⟨e, heE⟩
  have he_mem : e ∈ eL := (heL_mem e).mpr heE
  have hpos_lt : pos < G.m := heL_len ▸ List.idxOf_lt_length_of_mem he_mem
  have he_at_pos : eL[pos]'(by omega) = e := List.getElem_idxOf (List.idxOf_lt_length_of_mem he_mem)
  have hlen_er : (G.E.erase e).card = m' := Finset.card_erase_of_mem heE
  have heL'_len : eL'.length = m' := by
    dsimp only [eL']
    split_ifs <;> simp [List.length_take, List.length_set, heL_len] <;> omega
  have hget : ∀ i (hi : i < m'),
      eL'[i]'(by omega) = if i = pos then last else eL[i]'(by omega) := by
    intro i hi
    dsimp only [eL']
    by_cases hpm : pos = m'
    · have him : i ≠ m' := by omega
      simp only [hpm, ↓reduceIte, him, List.getElem_take]
    · simp only [hpm, ↓reduceIte]
      have hpos_lt' : pos < (eL.take m').length := by
        simp [List.length_take, heL_len]; omega
      by_cases hip : i = pos
      · subst hip
        simp [List.getElem_set_self]
      · simp only [hip, ↓reduceIte]
        rw [List.getElem_set_ne (by omega), List.getElem_take]
  have hnd' : eL'.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ hEq
    simp only [Fin.mk.injEq]
    have hi' : i < m' := by omega
    have hj' : j < m' := by omega
    dsimp only at hEq
    rw [hget i hi', hget j hj'] at hEq
    by_cases hip : i = pos <;> by_cases hjp : j = pos
    · exact hip.trans hjp.symm
    · simp only [hip, hjp, ↓reduceIte] at hEq
      have hinj := heL_nd.getElem_inj_iff.mp hEq
      omega
    · simp only [hip, hjp, ↓reduceIte] at hEq
      have hinj := heL_nd.getElem_inj_iff.mp hEq
      omega
    · simp only [hip, hjp, ↓reduceIte] at hEq
      exact heL_nd.getElem_inj_iff.mp hEq
  have hmem' : ∀ x, x ∈ eL' ↔ x ∈ G.E.erase e := by
    intro x
    rw [List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < m' := by omega
      rw [hget i hi']
      by_cases hip : i = pos
      · simp only [hip, ↓reduceIte]
        have hlastE : last ∈ G.E := (heL_mem _).mp (List.getElem_mem _)
        have hne_e : last ≠ e := by
          intro hEq
          have h1 := hEq.trans he_at_pos.symm
          have hinj := heL_nd.getElem_inj_iff.mp h1
          omega
        exact Finset.mem_erase.mpr ⟨hne_e, hlastE⟩
      · simp only [hip, ↓reduceIte]
        have hxE : eL[i] ∈ G.E := (heL_mem _).mp (List.getElem_mem _)
        have hne_e : eL[i] ≠ e := by
          intro hEq
          have h1 := hEq.trans he_at_pos.symm
          exact hip (heL_nd.getElem_inj_iff.mp h1)
        exact Finset.mem_erase.mpr ⟨hne_e, hxE⟩
    · intro hx
      rcases Finset.mem_erase.mp hx with ⟨hx_ne, hxE⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((heL_mem x).mpr hxE)
      have hj_ne_pos : j ≠ pos := fun hc => hx_ne (by subst hc; exact he_at_pos)
      by_cases hjm : j < m'
      · refine ⟨j, by omega, ?_⟩
        rw [hget j hjm]
        simp only [hj_ne_pos, ↓reduceIte]
      · have hjeq : j = m' := by omega
        subst hjeq
        have hpm : pos < m' := by omega
        refine ⟨pos, by omega, ?_⟩
        rw [hget pos hpm]
        simp [last]
  exact ⟨hpos_lt, heL'_len.trans hlen_er.symm, hnd', hmem', hget⟩

lemma nodup_length_lt_of_notMem {L : List ℕ} {cap h : ℕ}
    (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < cap) (hh : h < cap) (hh_not : h ∉ L) :
    L.length + 1 ≤ cap := by
  have hsub : L.toFinset ⊂ Finset.range cap := by
    rw [Finset.ssubset_iff_of_subset (fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx)))]
    exact ⟨h, Finset.mem_range.mpr hh, fun hc => hh_not (List.mem_toFinset.mp hc)⟩
  have hcard := Finset.card_lt_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard

lemma nodup_length_le_cap {L : List ℕ} {cap : ℕ}
    (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < cap) : L.length ≤ cap := by
  have hsub : L.toFinset ⊆ Finset.range cap := fun x hx =>
    Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard

lemma half_ne_of_ne_pair {h e : ℕ} (h1 : h ≠ 2 * e) (h2 : h ≠ 2 * e + 1) :
    h / 2 ≠ e := by omega

end

end MinCostFlow.DynSpanner.Program
