module

public import WordRAM.Tactic
public import MinCostFlow.Expander.PruningStepBase
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Expander.DecrementalPaths
public import MinCostFlow.Expander.PathDSProg.Params

import Mathlib.Tactic.Linarith

/-!
# Deterministic Word-RAM Subdivision, Filtering, Mask, and Walk-Projection Subroutines

Implements the deterministic (`Stmt.NoRand`) Word-RAM helper statements used across `init`,
`Delete`, and `GetPath` of `PathDSImpl`:
1. `writeSubdivGraphStmt`: constructs `GraphAt mem' dst (subdivGraph G)` from `GraphAt mem gAddr G`
   in time `≤ 110 * G.m + 45`.
2. `filterNewVhatStmt`: filters and deduplicates `[CS21]`'s `SeqAt mem src L_s` down to original
   vertices `< n` not yet in `inVhat`, updating `inVhat` and writing `SeqAt mem' dst L` in time
   `≤ 70 * L_s.length + 35`.
3. `emitAllVhatStmt`: emits all remaining vertices `v < n` with `inVhat[v] = 0` at `dst` and sets
   all `inVhat[0..n-1] := 1` (used when `[CS21]` deletion budget is exceeded) in time `≤ 55 * n + 35`.
4. `initMasksStmt`: initializes `outR[0..n_s-1] := 1` and `eMask[0..m_s-1] := 1` in time
   `≤ 25 * (n_s + m_s) + 30`.
5. `fbUpdateBStmt`: sets `inB[0..n_s-1]` to `1 - outR[v]`, marks endpoints `n + 2*e`, `n + 2*e + 1`
   in `inB`, and clears `eMask[3*e + 1] := 0` in time `≤ 45 * n_s + 55`.
6. `emitNewVhatFromOutRStmt`: emits newly pruned original vertices (`outR[v] = 0`, `inVhat[v] = 0`),
   updating `inVhat` and writing `SeqAt mem' dst L` in time `≤ 65 * n + 35`.
7. `projSeqToWalkStmt`: projects an alternating subdivision path sequence `P_s` stored with prefix
   `mem[src] = P_s.length` and `ListAt mem (src + 1) P_s` to
   `WalkAt mem' dst ⟨projPath n P_s, projEdges n P_s⟩` in time `≤ 65 * ((P_s.length - 1) / 3) + 70`.

All subroutines use scratch registers `20..31` only, preserving `∀ r < 20, st'.regs r = st.regs r`
and `st'.pos = st.pos`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure List & Layout Helpers -/

theorem walkAt_of_cells {mem : ℕ → ℕ} {a : ℕ} {P : Walk}
    (hlenV : mem a = P.verts.length)
    (hV : ∀ i (hi : i < P.verts.length), mem (a + 1 + i) = P.verts[i])
    (hlenE : mem (a + 1 + P.verts.length) = P.edges.length)
    (hE : ∀ i (hi : i < P.edges.length), mem (a + 2 + P.verts.length + i) = P.edges[i]) :
    WalkAt mem a P := by
  rw [walkAt_iff]
  refine ⟨hlenV, fun i hi => by simpa [Nat.add_assoc] using hV i hi, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hlenE
  · intro i hi
    simpa [Nat.add_assoc] using hE i hi

theorem subdivGraph_graphAt_of_cells {mem : ℕ → ℕ} {dst : ℕ} {G : Cited.Graph}
    (hm0 : mem dst = G.n + 2 * G.m)
    (hm1 : mem (dst + 1) = 3 * G.m)
    (hed : ∀ k < G.m,
      let e := G.edges.getD k (0, 0)
      mem (dst + 2 + 6 * k) = e.1 ∧
      mem (dst + 3 + 6 * k) = G.n + 2 * k ∧
      mem (dst + 4 + 6 * k) = G.n + 2 * k ∧
      mem (dst + 5 + 6 * k) = G.n + 2 * k + 1 ∧
      mem (dst + 6 + 6 * k) = G.n + 2 * k + 1 ∧
      mem (dst + 7 + 6 * k) = e.2) :
    GraphAt mem dst (subdivGraph G) := by
  refine graphAt_of_cells (by rw [hm0, subdivGraph_n]) (by rw [hm1, subdivGraph_m]) fun j hj => ?_
  have hj3 : j < 3 * G.m := by simpa [subdivGraph_m] using hj
  have hedges := subdivGraph_edges_getD G hj3
  have hk_lt : j / 3 < G.m := Nat.div_lt_of_lt_mul (by omega)
  have hget : (subdivGraph G).edges[j]'hj = (subdivGraph G).edges.getD j (0, 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rcases hed (j / 3) hk_lt with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  rw [hget, hedges]
  have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hmod with hr | hr | hr
  · simp only [hr, ↓reduceIte]
    exact ⟨by simpa [show dst + 2 + 2 * j = dst + 2 + 6 * (j / 3) by omega] using hc0,
      by simpa [show dst + 3 + 2 * j = dst + 3 + 6 * (j / 3) by omega] using hc1⟩
  · simp only [hr, Nat.one_ne_zero, ↓reduceIte]
    exact ⟨by simpa [show dst + 2 + 2 * j = dst + 4 + 6 * (j / 3) by omega] using hc2,
      by simpa [show dst + 3 + 2 * j = dst + 5 + 6 * (j / 3) by omega] using hc3⟩
  · simp only [show j % 3 ≠ 0 by omega, show j % 3 ≠ 1 by omega, ↓reduceIte]
    exact ⟨by simpa [show dst + 2 + 2 * j = dst + 6 + 6 * (j / 3) by omega] using hc4,
      by simpa [show dst + 3 + 2 * j = dst + 7 + 6 * (j / 3) by omega] using hc5⟩

lemma six_lt_two_pow_of_le {w : ℕ} (h : 6 ≤ 2 ^ w) : 6 < 2 ^ w := by
  rcases Nat.lt_or_ge w 3 with hw | hw
  · interval_cases w <;> norm_num at h
  · have : 8 ≤ 2 ^ w := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hw)
    omega

lemma listAt_append_singleton {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} {v : ℕ}
    (hlist : ListAt mem a l)
    (hold : ∀ j < l.length, mem' (a + j) = mem (a + j))
    (hnew : mem' (a + l.length) = v) :
    ListAt mem' a (l ++ [v]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
  · rw [List.getElem_append_left hj', hold j hj']
    exact hlist j hj'
  · rw [List.getElem_append_right (le_refl _)]
    simpa using hnew

/-- Deduplicated filter keeping elements `< n` not in `seen` (preserving first occurrence). -/
def dedupFilter (seen : Finset ℕ) (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | v :: vs =>
    if v < n ∧ v ∉ seen then v :: dedupFilter (insert v seen) n vs
    else dedupFilter seen n vs

lemma dedupFilter_mem (seen : Finset ℕ) (n : ℕ) : ∀ xs v,
    v ∈ dedupFilter seen n xs ↔ v ∈ xs ∧ v < n ∧ v ∉ seen
  | [], v => by simp [dedupFilter]
  | x :: xs, v => by
    simp only [dedupFilter]
    split_ifs with hx
    · rw [List.mem_cons, dedupFilter_mem (insert x seen) n xs v]
      by_cases hvx : v = x
      · subst hvx; simp [hx]
      · simp [hvx, Finset.mem_insert]
    · rw [dedupFilter_mem seen n xs v]
      by_cases hvx : v = x
      · subst hvx; simp [hx]
      · simp [hvx]

lemma dedupFilter_nodup (seen : Finset ℕ) (n : ℕ) : ∀ xs, (dedupFilter seen n xs).Nodup
  | [] => by simp [dedupFilter]
  | x :: xs => by
    simp only [dedupFilter]
    split_ifs with hx
    · refine List.nodup_cons.mpr ⟨?_, dedupFilter_nodup _ n xs⟩
      intro hmem
      exact ((dedupFilter_mem _ n xs x).mp hmem).2.2 (Finset.mem_insert_self x seen)
    · exact dedupFilter_nodup seen n xs

lemma dedupFilter_toFinset (seen : Finset ℕ) (n : ℕ) (xs : List ℕ) :
    (dedupFilter seen n xs).toFinset = (xs.filter (· < n)).toFinset \ seen := by
  ext v
  simp only [List.mem_toFinset, dedupFilter_mem, Finset.mem_sdiff, List.mem_filter,
    decide_eq_true_eq]
  tauto

lemma dedupFilter_length_le (seen : Finset ℕ) (n : ℕ) (xs : List ℕ) :
    (dedupFilter seen n xs).length ≤ n := by
  have hsub : (dedupFilter seen n xs).toFinset ⊆ Finset.range n := fun v hv => by
    rw [List.mem_toFinset, dedupFilter_mem] at hv
    exact Finset.mem_range.mpr hv.2.1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range, List.toFinset_card_of_nodup (dedupFilter_nodup seen n xs)] at hc
  exact hc

lemma dedupFilter_length_lt_of_new {seen : Finset ℕ} {n : ℕ} {xs : List ℕ} {v : ℕ}
    (hv : v < n) (hnew : v ∉ seen ∪ (xs.filter (· < n)).toFinset) :
    (dedupFilter seen n xs).length < n := by
  have hsub : insert v (dedupFilter seen n xs).toFinset ⊆ Finset.range n := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu'
    · exact Finset.mem_range.mpr hv
    · rw [List.mem_toFinset, dedupFilter_mem] at hu'
      exact Finset.mem_range.mpr hu'.2.1
  have hnv : v ∉ (dedupFilter seen n xs).toFinset := by
    rw [dedupFilter_toFinset, Finset.mem_sdiff]
    intro hmem
    exact hnew (Finset.mem_union_right _ hmem.1)
  have hlt : (dedupFilter seen n xs).toFinset.card + 1 ≤ n := by
    simpa [Finset.card_insert_of_notMem hnv, Finset.card_range] using Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (dedupFilter_nodup seen n xs)] at hlt
  omega

lemma dedupFilter_append_singleton (seen : Finset ℕ) (n : ℕ) : ∀ (xs : List ℕ) (v : ℕ),
    dedupFilter seen n (xs ++ [v]) =
      if v < n ∧ v ∉ seen ∪ (xs.filter (· < n)).toFinset then dedupFilter seen n xs ++ [v]
      else dedupFilter seen n xs
  | [], v => by simp [dedupFilter]
  | x :: xs, v => by
    simp only [List.cons_append, dedupFilter]
    by_cases hx : x < n ∧ x ∉ seen
    · simp only [hx.1, hx.2, not_false_eq_true, and_self, ↓reduceIte,
        dedupFilter_append_singleton (insert x seen) n xs v]
      have hiff : (v < n ∧ v ∉ insert x seen ∪ (xs.filter (· < n)).toFinset) ↔
          (v < n ∧ v ∉ seen ∪ ((x :: xs).filter (· < n)).toFinset) := by
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_filter,
          List.mem_cons, decide_eq_true_eq]
        tauto
      by_cases h1 : v < n ∧ v ∉ insert x seen ∪ (xs.filter (· < n)).toFinset
      · have h2 := hiff.mp h1
        simp only [eq_true h1, eq_true h2, ↓reduceIte, List.cons_append]
      · have h2 : ¬ (v < n ∧ v ∉ seen ∪ ((x :: xs).filter (· < n)).toFinset) := fun h => h1 (hiff.mpr h)
        simp only [eq_false h1, eq_false h2, ↓reduceIte]
    · simp only [hx, ↓reduceIte, dedupFilter_append_singleton seen n xs v]
      have hiff : (v < n ∧ v ∉ seen ∪ (xs.filter (· < n)).toFinset) ↔
          (v < n ∧ v ∉ seen ∪ ((x :: xs).filter (· < n)).toFinset) := by
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, List.mem_cons,
          decide_eq_true_eq]
        constructor
        · rintro ⟨hvn, hnot⟩
          refine ⟨hvn, fun hmem => ?_⟩
          rcases hmem with hseen | ⟨rfl | hvxs, _⟩
          · exact hnot (Or.inl hseen)
          · exact hx ⟨hvn, fun hs => hnot (Or.inl hs)⟩
          · exact hnot (Or.inr ⟨hvxs, hvn⟩)
        · rintro ⟨hvn, hnot⟩
          refine ⟨hvn, fun hmem => hnot ?_⟩
          rcases hmem with hseen | ⟨hvxs, _⟩
          · exact Or.inl hseen
          · exact Or.inr ⟨Or.inr hvxs, hvn⟩
      by_cases h1 : v < n ∧ v ∉ seen ∪ (xs.filter (· < n)).toFinset
      · have h2 := hiff.mp h1
        simp only [eq_true h1, eq_true h2, ↓reduceIte]
      · have h2 : ¬ (v < n ∧ v ∉ seen ∪ ((x :: xs).filter (· < n)).toFinset) := fun h => h1 (hiff.mpr h)
        simp only [eq_false h1, eq_false h2, ↓reduceIte]

/-- A path vertex list `P_s` alternates in groups of 3 (`< n` at `3i`, `≥ n` at `3i+1, 3i+2`),
the exact structural shape of every simple path in `subdivGraph G` between original vertices. -/
def SubdivAltSeq (n k : ℕ) (P_s : List ℕ) : Prop :=
  P_s.length = 3 * k + 1 ∧
  (∀ i ≤ k, P_s.getD (3 * i) 0 < n) ∧
  (∀ i < k, n ≤ P_s.getD (3 * i + 1) 0 ∧ n ≤ P_s.getD (3 * i + 2) 0)

lemma projPath_subdivAlt (n : ℕ) : ∀ k (P_s : List ℕ), SubdivAltSeq n k P_s →
    (projPath n P_s).length = k + 1 ∧
    (projPath n P_s).getD 0 0 = P_s.getD 0 0 ∧
    (∀ i < k, (projPath n P_s).getD (i + 1) 0 = P_s.getD (3 * i + 3) 0)
  | 0, P_s, ⟨hlen, horig, _⟩ => by
    rcases P_s with _ | ⟨u, _ | _⟩ <;> (simp at hlen; try omega)
    have hu : u < n := horig 0 (le_refl 0)
    simp [projPath, hu]
  | k + 1, P_s, ⟨hlen, horig, hmid⟩ => by
    rcases P_s with _ | ⟨u, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> (simp at hlen; try omega)
    have hu : u < n := horig 0 (Nat.zero_le _)
    have hy : ¬ y < n := Nat.not_lt_of_ge (hmid 0 (Nat.zero_lt_succ _)).1
    have hz : ¬ z < n := Nat.not_lt_of_ge (hmid 0 (Nat.zero_lt_succ _)).2
    have hrest : SubdivAltSeq n k rest := by
      refine ⟨by omega, fun i hi => ?_, fun i hi => ?_⟩
      · simpa [show 3 * (i + 1) = 3 * i + 3 by omega] using horig (i + 1) (by omega)
      · simpa [show 3 * (i + 1) + 1 = (3 * i + 1) + 3 by omega,
          show 3 * (i + 1) + 2 = (3 * i + 2) + 3 by omega] using hmid (i + 1) (by omega)
    obtain ⟨ih_len, ih_0, ih_succ⟩ := projPath_subdivAlt n k rest hrest
    have hfilt : projPath n (u :: y :: z :: rest) = u :: projPath n rest := by
      simp [projPath, hu, hy, hz]
    rw [hfilt]
    refine ⟨by simp [ih_len], by simp, fun i hi => ?_⟩
    cases i with
    | zero => simpa using ih_0
    | succ i' =>
      simpa [show 3 * (i' + 1) + 3 = (3 * i' + 3) + 3 by omega] using ih_succ i' (by omega)

lemma projEdges_subdivAlt (n : ℕ) : ∀ k (P_s : List ℕ), SubdivAltSeq n k P_s →
    (projEdges n P_s).length = k ∧
    ∀ i < k, (projEdges n P_s).getD i 0 = (P_s.getD (3 * i + 1) 0 - n) / 2
  | 0, P_s, ⟨hlen, _, _⟩ => by
    rcases P_s with _ | ⟨u, _ | _⟩ <;> (simp at hlen; try omega)
    simp [projEdges]
  | k + 1, P_s, ⟨hlen, horig, hmid⟩ => by
    rcases P_s with _ | ⟨u, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest'⟩⟩⟩⟩ <;> (simp at hlen; try omega)
    have hrest : SubdivAltSeq n k (w :: rest') := by
      refine ⟨by simp; omega, fun i hi => ?_, fun i hi => ?_⟩
      · simpa [show 3 * (i + 1) = 3 * i + 3 by omega] using horig (i + 1) (by omega)
      · simpa [show 3 * (i + 1) + 1 = (3 * i + 1) + 3 by omega,
          show 3 * (i + 1) + 2 = (3 * i + 2) + 3 by omega] using hmid (i + 1) (by omega)
    obtain ⟨ih_len, ih_get⟩ := projEdges_subdivAlt n k (w :: rest') hrest
    dsimp only [projEdges]
    rw [List.length_cons, ih_len]
    refine ⟨rfl, fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ i' =>
      simpa [show 3 * (i' + 1) + 1 = (3 * i' + 1) + 3 by omega] using ih_get i' (by omega)

/-! ## 2. `writeSubdivGraphStmt` (`G ↦ subdivGraph G`) -/

def writeSubdivSetupA : Stmt :=
  seqStmts
    [ .assign 22 (.load (.reg 20))
    , .assign 23 (.load (.bin .add (.reg 20) (.const 1)))
    , .store (.reg 21) (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 23)))
    , .store (.bin .add (.reg 21) (.const 1)) (.bin .mul (.const 3) (.reg 23)) ]

def writeSubdivSetupB : Stmt :=
  seqStmts
    [ .assign 24 (.bin .add (.bin .add (.reg 21) (.const 2)) (.bin .mul (.const 6) (.reg 23)))
    , .assign 26 (.bin .add (.reg 20) (.const 2))
    , .assign 27 (.bin .add (.reg 21) (.const 2))
    , .assign 28 (.reg 22) ]

def writeSubdivEdgeHeadStmt : Stmt :=
  seqStmts
    [ .assign 29 (.load (.reg 26))
    , .assign 30 (.load (.bin .add (.reg 26) (.const 1)))
    , .assign 31 (.bin .add (.reg 28) (.const 1)) ]

def writeSubdivEdgeMidAStmt : Stmt :=
  seqStmts
    [ .store (.reg 27) (.reg 29)
    , .store (.bin .add (.reg 27) (.const 1)) (.reg 28)
    , .store (.bin .add (.reg 27) (.const 2)) (.reg 28) ]

def writeSubdivEdgeMidBStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 27) (.const 3)) (.reg 31)
    , .store (.bin .add (.reg 27) (.const 4)) (.reg 31)
    , .store (.bin .add (.reg 27) (.const 5)) (.reg 30) ]

def writeSubdivEdgeTailStmt : Stmt :=
  seqStmts
    [ .assign 26 (.bin .add (.reg 26) (.const 2))
    , .assign 27 (.bin .add (.reg 27) (.const 6))
    , .assign 28 (.bin .add (.reg 28) (.const 2)) ]

def writeSubdivEdgeBody : Stmt :=
  writeSubdivEdgeHeadStmt ;;
    (writeSubdivEdgeMidAStmt ;; (writeSubdivEdgeMidBStmt ;; writeSubdivEdgeTailStmt))

/-- Builds `subdivGraph G` at `r21 = dst` from `GraphAt mem r20 G`, writing end pointer
`dst + 2 + 6 * G.m` to `r24`. Uses only scratch registers `20..31`. -/
def writeSubdivGraphStmt : Stmt :=
  (writeSubdivSetupA ;; writeSubdivSetupB) ;; forRange 25 (.const 0) (.reg 23) writeSubdivEdgeBody

lemma writeSubdivGraphStmt_noRand : writeSubdivGraphStmt.NoRand := by
  simp [writeSubdivGraphStmt, writeSubdivSetupA, writeSubdivSetupB, writeSubdivEdgeBody,
    writeSubdivEdgeHeadStmt, writeSubdivEdgeMidAStmt, writeSubdivEdgeMidBStmt,
    writeSubdivEdgeTailStmt, seqStmts, forRange, forUp, Stmt.NoRand]

private lemma writeSubdivEdgeMidA_triple {w a v0 v1 : ℕ} {p : Program}
    (st₀ : State) (hr27 : st₀.regs 27 = a) (hr28 : st₀.regs 28 = v1) (hr29 : st₀.regs 29 = v0)
    (ha_w : a + 2 < 2 ^ w) (_hv0_w : v0 < 2 ^ w) (_hv1_w : v1 < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    Triple w p (fun st => st = st₀) writeSubdivEdgeMidAStmt
      (normalPost fun st' =>
        MemFrame st₀.mem st'.mem a (a + 3) ∧
        st'.mem a = v0 ∧ st'.mem (a + 1) = v1 ∧ st'.mem (a + 2) = v1 ∧
        st'.regs = st₀.regs ∧ st'.pos = st₀.pos)
      (fun _ => 16) := by
  wram_enter; subst hpre; dsimp only [writeSubdivEdgeMidAStmt, seqStmts]
  wram_run
  · refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
    · exact memFrame_trans (memFrame_update (by omega) (by omega))
        (memFrame_trans (memFrame_update (by omega) (by omega)) (memFrame_update (by omega) (by omega)))
    · try dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · try dsimp only
      rw [Function.update_of_ne (by omega), Function.update_self]
    · try dsimp only
      rw [Function.update_self]
  · wram_cost

private lemma writeSubdivEdgeMidB_triple {w a v3 v5 : ℕ} {p : Program}
    (st₀ : State) (hr27 : st₀.regs 27 = a) (hr30 : st₀.regs 30 = v5) (hr31 : st₀.regs 31 = v3)
    (ha_w : a + 5 < 2 ^ w) (_hv3_w : v3 < 2 ^ w) (_hv5_w : v5 < 2 ^ w) (hw5 : 5 < 2 ^ w) :
    Triple w p (fun st => st = st₀) writeSubdivEdgeMidBStmt
      (normalPost fun st' =>
        MemFrame st₀.mem st'.mem (a + 3) (a + 6) ∧
        st'.mem (a + 3) = v3 ∧ st'.mem (a + 4) = v3 ∧ st'.mem (a + 5) = v5 ∧
        st'.regs = st₀.regs ∧ st'.pos = st₀.pos)
      (fun _ => 18) := by
  wram_enter; subst hpre; dsimp only [writeSubdivEdgeMidBStmt, seqStmts]
  wram_run
  · refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
    · exact memFrame_trans (memFrame_update (by omega) (by omega))
        (memFrame_trans (memFrame_update (by omega) (by omega)) (memFrame_update (by omega) (by omega)))
    · try dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · try dsimp only
      rw [Function.update_of_ne (by omega), Function.update_self]
    · try dsimp only
      rw [Function.update_self]
  · wram_cost

theorem writeSubdivGraphStmt_triple {w gAddr dst : ℕ} {p : Program}
    {G : Cited.Graph} (hV : G.IsValid) (st₀ : State)
    (hr20 : st₀.regs 20 = gAddr) (hr21 : st₀.regs 21 = dst)
    (hG : GraphAt st₀.mem gAddr G)
    (hdisj : dst + 2 + 6 * G.m ≤ gAddr ∨ gAddr + 2 + 2 * G.m ≤ dst)
    (hsrc_w : gAddr + 2 + 2 * G.m < 2 ^ w)
    (hdst_w : dst + 2 + 6 * G.m < 2 ^ w)
    (hns_w : G.n + 2 * G.m < 2 ^ w)
    (h3m_w : 3 * G.m < 2 ^ w)
    (hw6 : 6 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) writeSubdivGraphStmt
      (normalPost fun st' =>
        st'.regs 24 = dst + 2 + 6 * G.m ∧
        GraphAt st'.mem dst (subdivGraph G) ∧
        MemFrame st₀.mem st'.mem dst (dst + 2 + 6 * G.m) ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 110 * G.m + 60) := by
  have hw6_lt : 6 < 2 ^ w := six_lt_two_pow_of_le hw6
  have hw2 : 1 < 2 ^ w := by omega
  have hgn_eq : st₀.mem gAddr = G.n := graphAt_n hG
  have hgm_eq : st₀.mem (gAddr + 1) = G.m := graphAt_m hG
  have hm_w : G.m < 2 ^ w := by omega
  have hn_w : G.n < 2 ^ w := by omega
  have h2m_w : 2 * G.m < 2 ^ w := by omega
  let MidS : State → Prop := fun st =>
    st.regs 20 = gAddr ∧ st.regs 21 = dst ∧ st.regs 22 = G.n ∧ st.regs 23 = G.m ∧
    MemFrame st₀.mem st.mem dst (dst + 2 + 6 * G.m) ∧
    st.mem dst = G.n + 2 * G.m ∧ st.mem (dst + 1) = 3 * G.m ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let PreL : State → Prop := fun st =>
    st.regs 20 = gAddr ∧ st.regs 21 = dst ∧ st.regs 22 = G.n ∧ st.regs 23 = G.m ∧
    st.regs 24 = dst + 2 + 6 * G.m ∧ st.regs 26 = gAddr + 2 ∧ st.regs 27 = dst + 2 ∧
    st.regs 28 = G.n ∧ MemFrame st₀.mem st.mem dst (dst + 2 + 6 * G.m) ∧
    st.mem dst = G.n + 2 * G.m ∧ st.mem (dst + 1) = 3 * G.m ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 20 = gAddr ∧ st.regs 21 = dst ∧ st.regs 22 = G.n ∧ st.regs 23 = G.m ∧
    st.regs 24 = dst + 2 + 6 * G.m ∧ st.regs 25 = j ∧
    st.regs 26 = gAddr + 2 + 2 * j ∧ st.regs 27 = dst + 2 + 6 * j ∧
    st.regs 28 = G.n + 2 * j ∧
    MemFrame st₀.mem st.mem dst (dst + 2 + 6 * G.m) ∧
    st.mem dst = G.n + 2 * G.m ∧ st.mem (dst + 1) = 3 * G.m ∧
    (∀ k < j,
      let e := G.edges.getD k (0, 0)
      st.mem (dst + 2 + 6 * k) = e.1 ∧
      st.mem (dst + 3 + 6 * k) = G.n + 2 * k ∧
      st.mem (dst + 4 + 6 * k) = G.n + 2 * k ∧
      st.mem (dst + 5 + 6 * k) = G.n + 2 * k + 1 ∧
      st.mem (dst + 6 + 6 * k) = G.n + 2 * k + 1 ∧
      st.mem (dst + 7 + 6 * k) = e.2) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hsetupA : Triple w p (fun st => st = st₀) writeSubdivSetupA (normalPost MidS) (fun _ => 26) := by
    wram_enter; subst hpre; dsimp only [writeSubdivSetupA, seqStmts]
    wram_step; simp only [hgn_eq]
    wram_step; simp only [hr20, hgm_eq]
    wram_run
    · refine ⟨by simp [hr20], by simp [hr21], by simp, by simp, ?_, ?_, ?_,
        fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega, rfl⟩
      · rw [hr21]
        exact memFrame_trans (memFrame_update (by omega) (by omega)) (memFrame_update (by omega) (by omega))
      · (try dsimp only); rw [hr21, Function.update_of_ne (by omega), Function.update_self]
      · (try dsimp only); rw [hr21, Function.update_self]
    · wram_cost
  have hsetupB : Triple w p MidS writeSubdivSetupB (normalPost PreL) (fun _ => 22) := by
    wram_enter; rcases hpre with ⟨h20, h21, h22, h23, hfr, hm0, hm1, hlt20, hpos⟩
    dsimp only [writeSubdivSetupB, seqStmts]
    wram_run
    · refine ⟨by simp [h20], by simp [h21], by simp [h22], by simp [h23],
        by simp [h21], by simp [h20], by simp [h21], by simp [h22], hfr, hm0, hm1,
        fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
        hpos⟩
    · wram_cost
  have hsetup : Triple w p (fun st => st = st₀) (writeSubdivSetupA ;; writeSubdivSetupB)
      (normalPost PreL) (fun _ => 49) :=
    Triple.seq_normal_const hsetupA hsetupB
  have hloop := Triple.forRange_const (p := p) (r := 25) (lo := .const 0) (hi := .reg 23)
    (body := writeSubdivEdgeBody) (P := PreL) (Inv := Inv) 67 0 G.m (Nat.zero_le G.m) hw2 (fun _ => hm_w)
    (fun st ⟨h20, h21, h22, h23, h24, h26, h27, h28, hfr, hm0, hm1, hlt20, hpos⟩ => ⟨by eval_expr,
      ⟨by simp [h20], by simp [h21], by simp [h22], by simp [h23], by simp [h24], by simp,
        by simp [h26], by simp [h27], by simp [h28], hfr, hm0, hm1,
        fun _ hk => absurd hk (Nat.not_lt_zero _),
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.1; eval_expr)
    (fun j _ hjlt => by
      have hjG : j < G.edges.length := hjlt
      have hedV := hV _ (List.getElem_mem hjG)
      have he_eq : G.edges.getD j (0, 0) = G.edges[j]'hjG := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjG]
      set e := G.edges.getD j (0, 0)
      have hu_lt : e.1 < 2 ^ w := by simp only [e, he_eq]; omega
      have hv_lt : e.2 < 2 ^ w := by simp only [e, he_eq]; omega
      let PostH : State → Prop := fun st =>
        Inv j st ∧ st.regs 29 = e.1 ∧ st.regs 30 = e.2 ∧ st.regs 31 = G.n + 2 * j + 1
      let PostA : State → Prop := fun st =>
        st.regs 20 = gAddr ∧ st.regs 21 = dst ∧ st.regs 22 = G.n ∧ st.regs 23 = G.m ∧
        st.regs 24 = dst + 2 + 6 * G.m ∧ st.regs 25 = j ∧
        st.regs 26 = gAddr + 2 + 2 * j ∧ st.regs 27 = dst + 2 + 6 * j ∧
        st.regs 28 = G.n + 2 * j ∧ st.regs 30 = e.2 ∧ st.regs 31 = G.n + 2 * j + 1 ∧
        MemFrame st₀.mem st.mem dst (dst + 2 + 6 * G.m) ∧
        st.mem dst = G.n + 2 * G.m ∧ st.mem (dst + 1) = 3 * G.m ∧
        (∀ k < j,
          let ek := G.edges.getD k (0, 0)
          st.mem (dst + 2 + 6 * k) = ek.1 ∧
          st.mem (dst + 3 + 6 * k) = G.n + 2 * k ∧
          st.mem (dst + 4 + 6 * k) = G.n + 2 * k ∧
          st.mem (dst + 5 + 6 * k) = G.n + 2 * k + 1 ∧
          st.mem (dst + 6 + 6 * k) = G.n + 2 * k + 1 ∧
          st.mem (dst + 7 + 6 * k) = ek.2) ∧
        st.mem (dst + 2 + 6 * j) = e.1 ∧
        st.mem (dst + 3 + 6 * j) = G.n + 2 * j ∧
        st.mem (dst + 4 + 6 * j) = G.n + 2 * j ∧
        (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
      let PostB : State → Prop := fun st =>
        st.regs 20 = gAddr ∧ st.regs 21 = dst ∧ st.regs 22 = G.n ∧ st.regs 23 = G.m ∧
        st.regs 24 = dst + 2 + 6 * G.m ∧ st.regs 25 = j ∧
        st.regs 26 = gAddr + 2 + 2 * j ∧ st.regs 27 = dst + 2 + 6 * j ∧
        st.regs 28 = G.n + 2 * j ∧
        MemFrame st₀.mem st.mem dst (dst + 2 + 6 * G.m) ∧
        st.mem dst = G.n + 2 * G.m ∧ st.mem (dst + 1) = 3 * G.m ∧
        (∀ k < j + 1,
          let ek := G.edges.getD k (0, 0)
          st.mem (dst + 2 + 6 * k) = ek.1 ∧
          st.mem (dst + 3 + 6 * k) = G.n + 2 * k ∧
          st.mem (dst + 4 + 6 * k) = G.n + 2 * k ∧
          st.mem (dst + 5 + 6 * k) = G.n + 2 * k + 1 ∧
          st.mem (dst + 6 + 6 * k) = G.n + 2 * k + 1 ∧
          st.mem (dst + 7 + 6 * k) = ek.2) ∧
        (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
      have hH : Triple w p (Inv j) writeSubdivEdgeHeadStmt (normalPost PostH) (fun _ => 15) := by
        wram_enter
        rcases hpre with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, hfr, hmd0, hmd1, hed, hlt20, hpos⟩
        have hsrc1 : st.mem (gAddr + 2 + 2 * j) = e.1 := by
          rw [hfr _ (by omega)]; simp only [e, he_eq]; exact graphAt_edge_fst hG hjG
        have hsrc2 : st.mem (gAddr + 2 + 2 * j + 1) = e.2 := by
          rw [hfr _ (by omega)]; simp only [e, he_eq]
          rw [show gAddr + 2 + 2 * j + 1 = gAddr + 3 + 2 * j by omega]
          exact graphAt_edge_snd hG hjG
        dsimp only [writeSubdivEdgeHeadStmt, seqStmts]
        wram_step; simp only [hsrc1]
        wram_step; simp only [h26, hsrc2]
        wram_run
        · refine ⟨⟨by simp [h20], by simp [h21], by simp [h22], by simp [h23], by simp [h24],
            by simp [h25], by simp [h26], by simp [h27], by simp [h28], hfr, hmd0, hmd1, hed,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp, by simp, by simp [h28]⟩
        · wram_cost
      have hA : Triple w p PostH writeSubdivEdgeMidAStmt (normalPost PostA) (fun _ => 16) := by
        intro st ω ⟨⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, hfr, hmd0, hmd1, hed, hlt20, hpos⟩, h29, h30, h31⟩
        rcases writeSubdivEdgeMidA_triple st h27 h28 h29 (by omega) hu_lt (by omega) (by omega) st ω rfl with
          ⟨o, st', c, hrun, hpost, hc⟩
        cases o with
        | returned _ => exact False.elim hpost
        | normal =>
          rcases hpost with ⟨hfa, hc0, hc1, hc2, hregs, hpos'⟩
          refine ⟨.normal, st', c, hrun, ?_, hc⟩
          have hfa' : ∀ x, x < dst + 2 + 6 * j ∨ dst + 5 + 6 * j ≤ x → st'.mem x = st.mem x :=
            fun x hx => hfa x (by omega)
          refine ⟨hregs ▸ h20, hregs ▸ h21, hregs ▸ h22, hregs ▸ h23, hregs ▸ h24, hregs ▸ h25,
            hregs ▸ h26, hregs ▸ h27, hregs ▸ h28, hregs ▸ h30, hregs ▸ h31,
            memFrame_trans hfr (memFrame_mono hfa (by omega) (by omega)),
            by rw [hfa' _ (by omega), hmd0], by rw [hfa' _ (by omega), hmd1],
            fun k hk => ?_, hc0,
            by rw [show dst + 3 + 6 * j = dst + 2 + 6 * j + 1 by omega]; exact hc1,
            by rw [show dst + 4 + 6 * j = dst + 2 + 6 * j + 2 by omega]; exact hc2,
            fun r hr => by rw [hregs]; exact hlt20 r hr, hpos'.trans hpos⟩
          rcases hed k hk with ⟨d0, d1, d2, d3, d4, d5⟩
          exact ⟨by rw [hfa' _ (by omega), d0], by rw [hfa' _ (by omega), d1],
            by rw [hfa' _ (by omega), d2], by rw [hfa' _ (by omega), d3],
            by rw [hfa' _ (by omega), d4], by rw [hfa' _ (by omega), d5]⟩
      have hB : Triple w p PostA writeSubdivEdgeMidBStmt (normalPost PostB) (fun _ => 18) := by
        intro st ω ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, h31,
            hfr, hmd0, hmd1, hed, hc0, hc1, hc2, hlt20, hpos⟩
        rcases writeSubdivEdgeMidB_triple st h27 h30 h31 (by omega) (by omega) hv_lt (by omega) st ω rfl with
          ⟨o, st', c, hrun, hpost, hc⟩
        cases o with
        | returned _ => exact False.elim hpost
        | normal =>
          rcases hpost with ⟨hfb, hc3, hc4, hc5, hregs, hpos'⟩
          refine ⟨.normal, st', c, hrun, ?_, hc⟩
          have hfb' : ∀ x, x < dst + 5 + 6 * j ∨ dst + 8 + 6 * j ≤ x → st'.mem x = st.mem x :=
            fun x hx => hfb x (by omega)
          refine ⟨hregs ▸ h20, hregs ▸ h21, hregs ▸ h22, hregs ▸ h23, hregs ▸ h24, hregs ▸ h25,
            hregs ▸ h26, hregs ▸ h27, hregs ▸ h28,
            memFrame_trans hfr (memFrame_mono hfb (by omega) (by omega)),
            by rw [hfb' _ (by omega), hmd0], by rw [hfb' _ (by omega), hmd1],
            fun k hk => ?_, fun r hr => by rw [hregs]; exact hlt20 r hr, hpos'.trans hpos⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · rcases hed k hk' with ⟨d0, d1, d2, d3, d4, d5⟩
            exact ⟨by rw [hfb' _ (by omega), d0], by rw [hfb' _ (by omega), d1],
              by rw [hfb' _ (by omega), d2], by rw [hfb' _ (by omega), d3],
              by rw [hfb' _ (by omega), d4], by rw [hfb' _ (by omega), d5]⟩
          · exact ⟨by rw [hfb' _ (by omega), hc0], by rw [hfb' _ (by omega), hc1],
              by rw [hfb' _ (by omega), hc2],
              by rw [show dst + 5 + 6 * k = dst + 2 + 6 * k + 3 by omega]; exact hc3,
              by rw [show dst + 6 + 6 * k = dst + 2 + 6 * k + 4 by omega]; exact hc4,
              by rw [show dst + 7 + 6 * k = dst + 2 + 6 * k + 5 by omega]; exact hc5⟩
      have hT : Triple w p PostB writeSubdivEdgeTailStmt
          (normalPost fun st₁ => Inv (j + 1) { st₁ with regs := Function.update st₁.regs 25 (j + 1) } ∧ st₁.regs 25 = j)
          (fun _ => 15) := by
        wram_enter
        rcases hpre with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, hfr, hmd0, hmd1, hed, hlt20, hpos⟩
        dsimp only [writeSubdivEdgeTailStmt, seqStmts]
        wram_run
        · refine ⟨⟨by simp [h20], by simp [h21], by simp [h22], by simp [h23], by simp [h24], by simp,
            by simp; omega, by simp [h27]; omega, by simp [h28]; omega,
            hfr, hmd0, hmd1, hed,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h25]⟩
        · wram_cost
      have hBT := Triple.seq_normal_const hB hT
      have hABT := Triple.seq_normal_const hA hBT
      exact (Triple.seq_normal_const hH hABT).conseq (fun _ h => h) (fun _ _ h => h)
        (fun _ _ => by omega))
  have hseq : Triple w p (fun st => st = st₀) writeSubdivGraphStmt (normalPost (Inv G.m))
      (fun _ => 110 * G.m + 60) :=
    (Triple.seq_normal hsetup hloop (T := fun _ => 110 * G.m + 60)
      (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq
      (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)
  refine hseq.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨_, _, _, _, h24, _, _, _, _, hfr, hm0, hm1, hed, hlt20, hpos⟩
    exact ⟨h24, subdivGraph_graphAt_of_cells hm0 hm1 hed, hfr, hlt20, hpos⟩

/-! ## 3. `filterNewVhatStmt` -/

def filterNewVhatBody : Stmt :=
  seqStmts
    [ .assign 27 (.load (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 26)))
    , .cond (.bin .lt (.reg 27) (.reg 23))
        (seqStmts
          [ .assign 28 (.load (.bin .add (.reg 22) (.reg 27)))
          , .cond (.bin .eq (.reg 28) (.const 0))
              (seqStmts
                [ .store (.bin .add (.reg 22) (.reg 27)) (.const 1)
                , .store (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 25)) (.reg 27)
                , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
              .nop ])
        .nop ]

/-- Filters `SeqAt mem r20 L_s` down to `< r23` (`n`) elements not yet marked in `inVhat` (`r22`),
marking them in `inVhat` and writing deduplicated `SeqAt mem' r21 L` (length in `r24`). -/
def filterNewVhatStmt : Stmt :=
  ((.assign 24 (.load (.reg 20)) ;; .assign 25 (.const 0)) ;;
   forRange 26 (.const 0) (.reg 24) filterNewVhatBody) ;;
  (.store (.reg 21) (.reg 25) ;; .assign 24 (.reg 25))

lemma filterNewVhatStmt_noRand : filterNewVhatStmt.NoRand := by
  simp [filterNewVhatStmt, filterNewVhatBody, seqStmts, forRange, forUp, Stmt.NoRand]

theorem filterNewVhatStmt_triple {w src dst inVhatAddr n : ℕ} {p : Program}
    (st₀ : State) (Vhat : Finset ℕ) (L_s : List ℕ)
    (hr20 : st₀.regs 20 = src) (hr21 : st₀.regs 21 = dst)
    (hr22 : st₀.regs 22 = inVhatAddr) (hr23 : st₀.regs 23 = n)
    (hLs : SeqAt st₀.mem src L_s) (hLs_w : ∀ x ∈ L_s, x < 2 ^ w)
    (hinVhat : ∀ v < n, st₀.mem (inVhatAddr + v) = if v ∈ Vhat then 1 else 0)
    (hdisj_di : dst + 1 + n ≤ inVhatAddr ∨ inVhatAddr + n ≤ dst)
    (hdisj_sd : dst + 1 + n ≤ src ∨ src + 1 + L_s.length ≤ dst)
    (hdisj_si : inVhatAddr + n ≤ src ∨ src + 1 + L_s.length ≤ inVhatAddr)
    (hsrc_w : src + 1 + L_s.length < 2 ^ w)
    (hdst_w : dst + 1 + n < 2 ^ w)
    (hin_w : inVhatAddr + n < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) filterNewVhatStmt
      (normalPost fun st' =>
        let L := dedupFilter Vhat n L_s
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = (L_s.filter (· < n)).toFinset \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) =
          if v ∈ Vhat ∪ (L_s.filter (· < n)).toFinset then 1 else 0) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        (∀ a, dst + 1 + L.length ≤ a → a < dst + 1 + n → st'.mem a = st₀.mem a) ∧
        st'.regs 24 = L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 70 * L_s.length + 35) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hlen_lt : L_s.length < 2 ^ w := by omega
  have hlen_eq : st₀.mem src = L_s.length := hLs.1
  let PreL : State → Prop := fun st =>
    st.regs 20 = src ∧ st.regs 21 = dst ∧ st.regs 22 = inVhatAddr ∧ st.regs 23 = n ∧
    st.regs 24 = L_s.length ∧ st.regs 25 = 0 ∧ st.mem = st₀.mem ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let Inv : ℕ → State → Prop := fun i st =>
    let pref := L_s.take i
    let curL := dedupFilter Vhat n pref
    i ≤ L_s.length ∧
    st.regs 20 = src ∧ st.regs 21 = dst ∧ st.regs 22 = inVhatAddr ∧ st.regs 23 = n ∧
    st.regs 24 = L_s.length ∧ st.regs 25 = curL.length ∧ st.regs 26 = i ∧
    PreservedOutside2 st₀.mem st.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
    (∀ a, dst + 1 + curL.length ≤ a → a < dst + 1 + n → st.mem a = st₀.mem a) ∧
    ListAt st.mem (dst + 1) curL ∧
    (∀ v < n, st.mem (inVhatAddr + v) =
      if v ∈ Vhat ∪ (pref.filter (· < n)).toFinset then 1 else 0) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hsetup : Triple w p (fun st => st = st₀)
      (.assign 24 (.load (.reg 20)) ;; .assign 25 (.const 0))
      (normalPost PreL) (fun _ => 10) := by
    wram_enter; subst hpre
    wram_step; simp only [hlen_eq]
    wram_run
    · refine ⟨by simp [hr20], by simp [hr21], by simp [hr22], by simp [hr23],
        by simp, by simp, rfl,
        fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega,
        rfl⟩
    · wram_cost
  have hloop := Triple.forRange_const (p := p) (r := 26) (lo := .const 0) (hi := .reg 24)
    (body := filterNewVhatBody) (P := PreL) (Inv := Inv) 40 0 L_s.length (Nat.zero_le L_s.length) hw2 (fun _ => hlen_lt)
    (fun st ⟨h20, h21, h22, h23, h24, h25, hm, hlt20, hpos⟩ => ⟨by eval_expr, by
      refine ⟨Nat.zero_le _, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
        by simp [h24], by simp [h25, dedupFilter], by simp, ?_, ?_, ?_, ?_,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩
      · rw [hm]; exact preservedOutside2_refl _ _ _ _ _
      · intro a _ _; simp [hm]
      · intro k hk; simp [dedupFilter] at hk
      · intro v hv; simp [hm, hinVhat v hv]⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.2.2.1; eval_expr)
    (fun i _ hilt st ω hI => by
      rcases hI with ⟨_, h20, h21, h22, h23, h24, h25, h26, hpo, hkeep, hlist, hinV, hlt20, hpos⟩
      set pref := L_s.take i
      set curL := dedupFilter Vhat n pref
      set v := L_s[i]
      have hv_w : v < 2 ^ w := hLs_w v (List.getElem_mem hilt)
      have hsrc_v : st.mem (src + 1 + i) = v := by
        rw [hpo _ (by omega) (by omega)]
        exact hLs.2 i hilt
      have hlen_cur_le : curL.length ≤ n := dedupFilter_length_le Vhat n pref
      have htake_succ : L_s.take (i + 1) = pref ++ [v] := by
        show L_s.take (i + 1) = L_s.take i ++ [L_s[i]]
        rw [List.take_add_one, List.getElem?_eq_getElem hilt]
        simp
      refine runs_start_le ?_
      dsimp only [filterNewVhatBody, seqStmts]
      wram_step; simp only [hsrc_v]
      by_cases hvn : v < n
      · have hin_eq : st.mem (inVhatAddr + v) =
            if v ∈ Vhat ∪ (pref.filter (· < n)).toFinset then 1 else 0 := hinV v hvn
        have hin_v_w : st.mem (inVhatAddr + v) < 2 ^ w := by rw [hin_eq]; split_ifs <;> omega
        wram_step
        · by_cases hvmem : v ∈ Vhat ∪ (pref.filter (· < n)).toFinset
          · have heval1 : st.mem (inVhatAddr + v) = 1 := by simp only [hin_eq, eq_true hvmem, ↓reduceIte]
            wram_step; simp only [h22, heval1]
            wram_run
            · have hcur_eq : dedupFilter Vhat n (L_s.take (i + 1)) = curL := by
                rw [htake_succ, dedupFilter_append_singleton]
                split_ifs with hcond
                · exact False.elim (hcond.2 hvmem)
                · rfl
              refine ⟨⟨hilt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
                by simp [h24], by simp [h25, hcur_eq], by simp, hpo,
                by simpa only [hcur_eq] using hkeep,
                by simpa only [hcur_eq] using hlist, fun u hu => ?_,
                fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
                hpos⟩, by simp [h26]⟩
              rw [hinV u hu, htake_succ, List.filter_append]
              simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hvmem ⊢
              by_cases huv : u = v
              · subst huv; simp [hvn]; tauto
              · simp [huv]
            · wram_cost
          · have heval0 : st.mem (inVhatAddr + v) = 0 := by simp only [hin_eq, eq_false hvmem, ↓reduceIte]
            have hcur_lt : curL.length < n := dedupFilter_length_lt_of_new hvn hvmem
            have hcur_eq : dedupFilter Vhat n (L_s.take (i + 1)) = curL ++ [v] := by
              rw [htake_succ, dedupFilter_append_singleton]
              split_ifs with hcond
              · rfl
              · exact False.elim (hcond ⟨hvn, hvmem⟩)
            wram_step; simp only [h22, heval0]
            wram_run
            · refine ⟨⟨hilt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
                by simp [h24], by simp [h25, hcur_eq], by simp, ?_, ?_, ?_, fun u hu => ?_,
                fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
                hpos⟩, by simp [h26]⟩
              · (try dsimp only); rw [h22, h21, h25]
                exact preservedOutside2_trans hpo
                  (preservedOutside2_trans
                    (preservedOutside2_update_right (by omega) (by omega))
                    (preservedOutside2_update_left (by omega) (by omega)))
              · intro a ha1 ha2
                simp only [hcur_eq, List.length_append, List.length_singleton] at ha1
                (try dsimp only); rw [h22, h21, h25]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hkeep a (by omega) ha2
              · simp only [hcur_eq]
                refine listAt_append_singleton hlist (fun j hj => ?_) ?_
                · rw [h21, h25, h22]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                · rw [h21, h25]
                  rw [Function.update_self]
              · rw [htake_succ, List.filter_append]
                by_cases huv : u = v
                · subst huv; (try dsimp only); rw [h21, h25, h22]
                  rw [Function.update_of_ne (by omega), Function.update_self]
                  simp [hvn]
                · (try dsimp only); rw [h21, h25, h22]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hinV u hu]
                  simp [huv, hvn]
            · wram_cost
      · wram_run
        · have hcur_eq : dedupFilter Vhat n (L_s.take (i + 1)) = curL := by
            rw [htake_succ, dedupFilter_append_singleton]
            split_ifs with hcond
            · exact False.elim (hvn hcond.1)
            · rfl
          refine ⟨⟨hilt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
            by simp [h24], by simp [h25, hcur_eq], by simp, hpo,
            by simpa only [hcur_eq] using hkeep,
            by simpa only [hcur_eq] using hlist, fun u hu => ?_,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h26]⟩
          rw [hinV u hu, htake_succ, List.filter_append]
          have hnv : ¬ v < n := hvn
          simp [hnv]
        · wram_cost)
  have hmid : Triple w p (fun st => st = st₀)
      ((.assign 24 (.load (.reg 20)) ;; .assign 25 (.const 0)) ;;
       forRange 26 (.const 0) (.reg 24) filterNewVhatBody)
      (normalPost (Inv L_s.length)) (fun _ => 70 * L_s.length + 24) :=
    (Triple.seq_normal hsetup hloop (T := fun _ => 70 * L_s.length + 24)
      (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)
  have htail : Triple w p (Inv L_s.length)
      (.store (.reg 21) (.reg 25) ;; .assign 24 (.reg 25))
      (normalPost fun st' =>
        let L := dedupFilter Vhat n L_s
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = (L_s.filter (· < n)).toFinset \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) =
          if v ∈ Vhat ∪ (L_s.filter (· < n)).toFinset then 1 else 0) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        (∀ a, dst + 1 + L.length ≤ a → a < dst + 1 + n → st'.mem a = st₀.mem a) ∧
        st'.regs 24 = L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 10) := by
    wram_enter
    rcases hpre with ⟨_, _, h21, h22, _, _, h25, _, hpo, hkeep, hlist, hinV, hlt20, hpos⟩
    have htake : L_s.take L_s.length = L_s := List.take_length
    rw [htake] at h25 hkeep hlist hinV
    have hlen_le : (dedupFilter Vhat n L_s).length ≤ n := dedupFilter_length_le Vhat n L_s
    wram_run
    · refine ⟨⟨?_, fun k hk => ?_⟩, dedupFilter_nodup Vhat n L_s, hlen_le,
        dedupFilter_toFinset Vhat n L_s, fun v hv => ?_, ?_, fun a ha1 ha2 => ?_, by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩
      · simp
      · (try dsimp only); rw [Function.update_of_ne (by omega)]; exact hlist k hk
      · (try dsimp only); rw [Function.update_of_ne (by omega)]; exact hinV v hv
      · (try dsimp only)
        exact preservedOutside2_trans hpo (preservedOutside2_update_left (by omega) (by omega))
      · (try dsimp only); rw [Function.update_of_ne (by omega)]; exact hkeep a ha1 ha2
    · wram_cost
  exact (Triple.seq_normal hmid htail (T := fun _ => 70 * L_s.length + 35)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)

/-! ## 4. `emitAllVhatStmt` (`overBudget` full emission) -/

def emitAllVhatBody : Stmt :=
  seqStmts
    [ .assign 25 (.load (.bin .add (.reg 21) (.reg 24)))
    , .cond (.bin .eq (.reg 25) (.const 0))
        (seqStmts
          [ .store (.bin .add (.reg 21) (.reg 24)) (.const 1)
          , .store (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 23)) (.reg 24)
          , .assign 23 (.bin .add (.reg 23) (.const 1)) ])
        .nop ]

/-- Scans `v = 0 .. n - 1` (`r22`), marking any unpruned `inVhat[v] = 0` (`r21`) to `1` and
emitting `v` into `dst` (`r20`) as a `SeqAt` list (`r24 := dst + 1 + outLen`). -/
def emitAllVhatStmt : Stmt :=
  (.assign 23 (.const 0) ;; forRange 24 (.const 0) (.reg 22) emitAllVhatBody) ;;
  (.store (.reg 20) (.reg 23) ;; .assign 24 (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 23)))

lemma emitAllVhatStmt_noRand : emitAllVhatStmt.NoRand := by
  simp [emitAllVhatStmt, emitAllVhatBody, seqStmts, forRange, forUp, Stmt.NoRand]

theorem emitAllVhatStmt_triple {w dst inVhatAddr n : ℕ} {p : Program}
    (st₀ : State) (Vhat : Finset ℕ)
    (hr20 : st₀.regs 20 = dst) (hr21 : st₀.regs 21 = inVhatAddr) (hr22 : st₀.regs 22 = n)
    (hinVhat : ∀ v < n, st₀.mem (inVhatAddr + v) = if v ∈ Vhat then 1 else 0)
    (hdisj : dst + 1 + n ≤ inVhatAddr ∨ inVhatAddr + n ≤ dst)
    (hdst_w : dst + 1 + n < 2 ^ w) (hin_w : inVhatAddr + n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) emitAllVhatStmt
      (normalPost fun st' =>
        let L := (List.range n).filter fun v => decide (v ∉ Vhat)
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = Finset.range n \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) = 1) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        st'.regs 24 = dst + 1 + L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 55 * n + 35) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let PreL : State → Prop := fun st =>
    st.regs 20 = dst ∧ st.regs 21 = inVhatAddr ∧ st.regs 22 = n ∧ st.regs 23 = 0 ∧
    st.mem = st₀.mem ∧ (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let Inv : ℕ → State → Prop := fun k st =>
    let curL := (List.range k).filter fun v => decide (v ∉ Vhat)
    k ≤ n ∧ st.regs 20 = dst ∧ st.regs 21 = inVhatAddr ∧ st.regs 22 = n ∧
    st.regs 23 = curL.length ∧ st.regs 24 = k ∧
    PreservedOutside2 st₀.mem st.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
    ListAt st.mem (dst + 1) curL ∧
    (∀ v < n, st.mem (inVhatAddr + v) = if v < k ∨ v ∈ Vhat then 1 else 0) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hsetup : Triple w p (fun st => st = st₀) (.assign 23 (.const 0)) (normalPost PreL) (fun _ => 4) := by
    wram_enter; subst hpre; wram_run
    · exact ⟨by simp [hr20], by simp [hr21], by simp [hr22], by simp, rfl,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], rfl⟩
    · wram_cost
  have hloop := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 22)
    (body := emitAllVhatBody) (P := PreL) (Inv := Inv) 30 0 n (Nat.zero_le n) hw2 (fun _ => hn_w)
    (fun st ⟨h20, h21, h22, h23, hm, hlt20, hpos⟩ => ⟨by eval_expr, by
      refine ⟨Nat.zero_le _, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
        by simp, hm ▸ preservedOutside2_refl _ _ _ _ _, fun _ hk => by simp at hk,
        fun v hv => by simpa [hm] using hinVhat v hv,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.1; eval_expr)
    (fun k _ hklt st ω hI => by
      rcases hI with ⟨_, h20, h21, h22, h23, h24, hpo, hlist, hinV, hlt20, hpos⟩
      set curL := (List.range k).filter fun v => decide (v ∉ Vhat)
      have hcur_le : curL.length ≤ k := by
        have hlen := List.length_filter_le (fun v => decide (v ∉ Vhat)) (List.range k)
        simpa [curL, List.length_range] using hlen
      have hin_k : st.mem (inVhatAddr + k) = if k ∈ Vhat then 1 else 0 := by
        simpa [Nat.lt_irrefl] using hinV k hklt
      have hin_kw : st.mem (inVhatAddr + k) < 2 ^ w := by rw [hin_k]; split_ifs <;> omega
      refine runs_start_le ?_
      dsimp only [emitAllVhatBody, seqStmts]
      by_cases hkV : k ∈ Vhat
      · have hin_k1 : st.mem (inVhatAddr + k) = 1 := by simp [hin_k, hkV]
        wram_step; simp only [hin_k1]
        wram_run
        · have hcur' : (List.range (k + 1)).filter (fun v => decide (v ∉ Vhat)) = curL := by
            rw [List.range_succ, List.filter_append]; simp [hkV, curL]
          refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h23, hcur'],
            by simp, hpo, by simpa only [hcur'] using hlist, fun v hv => ?_,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h24]⟩
          rw [hinV v hv]
          by_cases hvk : v = k
          · subst hvk; simp [hkV]
          · simp [show v < k + 1 ↔ v < k by omega]
        · wram_cost
      · have hin_k0 : st.mem (inVhatAddr + k) = 0 := by simp [hin_k, hkV]
        have hcur' : (List.range (k + 1)).filter (fun v => decide (v ∉ Vhat)) = curL ++ [k] := by
          rw [List.range_succ, List.filter_append]; simp [hkV, curL]
        wram_step; simp only [hin_k0]
        wram_run
        · refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22],
            by dsimp only; simp only [hcur', List.length_append, List.length_cons, List.length_nil]
               rw [Function.update_of_ne (by decide), Function.update_self, h23],
            by simp, ?_, ?_, fun v hv => ?_,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h24]⟩
          · (try dsimp only); rw [h20, h21, h23, h24]
            exact preservedOutside2_trans hpo
              (preservedOutside2_trans (preservedOutside2_update_right (by omega) (by omega))
                (preservedOutside2_update_left (by omega) (by omega)))
          · simp only [hcur']
            refine listAt_append_singleton hlist (fun j hj => ?_) ?_
            · rw [h20, h21, h23, h24, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            · rw [h20, h23, h24, Function.update_self]
          · by_cases hvk : v = k
            · subst hvk; (try dsimp only); rw [h20, h21, h23, h24]
              rw [Function.update_of_ne (by omega), Function.update_self]; simp
            · (try dsimp only); rw [h20, h21, h23, h24]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hinV v hv]
              simp [show v < k + 1 ↔ v < k by omega]
        · wram_cost)
  have hmid : Triple w p (fun st => st = st₀)
      (.assign 23 (.const 0) ;; forRange 24 (.const 0) (.reg 22) emitAllVhatBody)
      (normalPost (Inv n)) (fun _ => 55 * n + 15) :=
    (Triple.seq_normal hsetup hloop (T := fun _ => 55 * n + 15)
      (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)
  have htail : Triple w p (Inv n)
      (.store (.reg 20) (.reg 23) ;; .assign 24 (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 23)))
      (normalPost fun st' =>
        let L := (List.range n).filter fun v => decide (v ∉ Vhat)
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = Finset.range n \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) = 1) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        st'.regs 24 = dst + 1 + L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 15) := by
    wram_enter
    rcases hpre with ⟨_, h20, h21, _, h23, _, hpo, hlist, hinV, hlt20, hpos⟩
    have hlen_le : ((List.range n).filter fun v => decide (v ∉ Vhat)).length ≤ n := by
      simpa using List.length_filter_le (fun v => decide (v ∉ Vhat)) (List.range n)
    wram_run
    · refine ⟨⟨by simp, fun k hk => ?_⟩, List.nodup_range.filter _, hlen_le, ?_,
        fun v hv => ?_, ?_, by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩
      · (try dsimp only)
        rw [Function.update_of_ne (by omega)]; exact hlist k hk
      · ext x; simp [Finset.mem_sdiff, Finset.mem_range]
      · (try dsimp only)
        rw [Function.update_of_ne (by omega)]; simp [hinV v hv, hv]
      · (try dsimp only)
        exact preservedOutside2_trans hpo (preservedOutside2_update_left (by omega) (by omega))
    · wram_cost
  exact (Triple.seq_normal hmid htail (T := fun _ => 55 * n + 35)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)


end MinCostFlow.Expander.PathDSProg
