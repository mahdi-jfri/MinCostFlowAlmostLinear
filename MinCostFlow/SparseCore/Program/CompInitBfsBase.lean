module

public import MinCostFlow.SparseCore.Program.CompLayout
import WordRAM.Tactic

/-!
# Connected-Component BFS Discovery: Definitions and Context (`CompInitBfsBase`)

Defines the deterministic (`NoRand`) Word-RAM BFS helper `compBfsCompProc`, its contract
`compBfsCompContract`, the graph-theoretic reachability and degree-sum lemmas, and the loop
invariant structures shared by `CompInitBfsInner` and `CompInitBfs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedure body and contract -/

/-- Inner incidence-list traversal loop of `compBfsCompProc`. -/
def compBfsInnerBody : Stmt :=
  .assign 24 (.bin .sub (.reg 23) (.const 1)) ;;
  .assign 25 (.bin .div (.reg 24) (.const 2)) ;;
  .assign 26 (.bin .mod (.reg 24) (.const 2)) ;;
  .assign 27 (.load (.bin .add (.reg 15) (.reg 25))) ;;
  .assign 28 (.load (.bin .add (.reg 16) (.reg 25))) ;;
  .assign 27 (.load (.bin .add (.reg 13) (.reg 27))) ;;
  .assign 28 (.load (.bin .add (.reg 13) (.reg 28))) ;;
  .cond (.reg 26)
    (.assign 29 (.reg 27))
    (.store (.bin .add (.reg 3) (.reg 25)) (.reg 8) ;;
     .store (.bin .add (.reg 4) (.reg 25)) (.reg 8) ;;
     .assign 30 (.bin .mul (.const 3) (.reg 20)) ;;
     .store (.bin .add (.reg 6) (.reg 30)) (.reg 25) ;;
     .store (.bin .add (.reg 6) (.bin .add (.reg 30) (.const 1))) (.reg 27) ;;
     .store (.bin .add (.reg 6) (.bin .add (.reg 30) (.const 2))) (.reg 28) ;;
     .assign 20 (.bin .add (.reg 20) (.const 1)) ;;
     .assign 29 (.reg 28)) ;;
  .assign 30 (.load (.bin .add (.reg 1) (.reg 29))) ;;
  .cond (.reg 30)
    .nop
    (.store (.bin .add (.reg 1) (.reg 29)) (.const 1) ;;
     .store (.bin .add (.reg 2) (.reg 29)) (.reg 8) ;;
     .store (.bin .add (.reg 5) (.reg 19)) (.reg 29) ;;
     .assign 19 (.bin .add (.reg 19) (.const 1))) ;;
  .assign 23 (.load (.bin .add (.reg 17) (.reg 24)))

/-- Inner incidence loop of `compBfsCompProc`. -/
def compBfsInnerLoop : Stmt :=
  .loop (.reg 23) compBfsInnerBody

/-- Outer BFS queue loop of `compBfsCompProc`. -/
def compBfsOuterLoop : Stmt :=
  .loop (.bin .lt (.reg 18) (.reg 19))
    (.assign 21 (.load (.bin .add (.reg 5) (.reg 18))) ;;
     .assign 18 (.bin .add (.reg 18) (.const 1)) ;;
     .assign 22 (.load (.bin .add (.reg 12) (.reg 21))) ;;
     .assign 23 (.load (.bin .add (.reg 14) (.reg 22))) ;;
     compBfsInnerLoop)

/-- `args = [g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr]`.
Runs BFS from `v0` in `DynGraphAt` at `g0Ptr`, marks `vis[u] = 1` and `vComp[u] = c` for `u ∈ C`,
sets `edgeC1[e] = edgeC2[e] = c` for `e ∈ compEdgeSet G₀ C`, writes `bfsQ[0..nC-1]` and
`compEdges[0..3*mC-1]`, stores `mC` at `outM0Addr`, and returns `nC`. -/
def compBfsCompProc : Stmt :=
  .assign 10 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 10))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 10))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 10))) ;;
  .assign 15 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 10)))
    (.bin .mul (.const 3) (.reg 11))) ;;
  .assign 16 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 10)))
    (.bin .mul (.const 4) (.reg 11))) ;;
  .assign 17 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 10)))
    (.bin .mul (.const 7) (.reg 11))) ;;
  .store (.bin .add (.reg 1) (.reg 7)) (.const 1) ;;
  .store (.bin .add (.reg 2) (.reg 7)) (.reg 8) ;;
  .store (.reg 5) (.reg 7) ;;
  .assign 18 (.const 0) ;;
  .assign 19 (.const 1) ;;
  .assign 20 (.const 0) ;;
  compBfsOuterLoop ;;
  .store (.reg 9) (.reg 20) ;;
  .ret (.reg 19)

lemma compBfsCompProc_noRand : compBfsCompProc.NoRand := by
  simp [compBfsCompProc, compBfsOuterLoop, compBfsInnerLoop, compBfsInnerBody, Stmt.NoRand]

/-- Disjointness of two address intervals `[a₁, a₁ + l₁)` and `[a₂, a₂ + l₂)`. -/
def RangesDisj (a₁ l₁ a₂ l₂ : ℕ) : Prop :=
  a₁ + l₁ ≤ a₂ ∨ a₂ + l₂ ≤ a₁

/-- Memory predicate for a list of edge triples `(e, u, v)` packed at `ptr`. -/
def EdgeTriplesAt (mem : ℕ → ℕ) (ptr : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ i (hi : i < L.length),
    mem (ptr + 3 * i) = L[i].1 ∧
    mem (ptr + 3 * i + 1) = L[i].2.1 ∧
    mem (ptr + 3 * i + 2) = L[i].2.2

/-- Contract for `compBfsCompProc`. -/
noncomputable def compBfsCompContract (w vCap eCap : ℕ) (G₀ : MGraph) (C visSet : Finset ℕ) : Contract where
  pre args mem := ∃ g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase v0 c outM0Addr,
    args = [g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr] ∧
    16 ≤ 2 ^ w ∧
    DynGraphAt mem g0Ptr vCap eCap G₀ ∧
    C ∈ components G₀ ∧ v0 ∈ C ∧
    visSet ⊆ G₀.V ∧ Disjoint visSet C ∧
    (∀ v < vCap, mem (visBase + v) = if v ∈ visSet then 1 else 0) ∧
    c < vCap ∧
    g0Ptr + dynGraphSize vCap eCap < 2 ^ w ∧
    visBase + vCap < 2 ^ w ∧ vCompBase + vCap < 2 ^ w ∧
    edgeC1Base + eCap < 2 ^ w ∧ edgeC2Base + eCap < 2 ^ w ∧
    bfsQBase + (compGraph G₀ C).n < 2 ^ w ∧
    compEdgesBase + 3 * (compGraph G₀ C).m < 2 ^ w ∧
    outM0Addr + 1 < 2 ^ w ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) visBase vCap ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) vCompBase vCap ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) edgeC1Base eCap ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) edgeC2Base eCap ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) bfsQBase (compGraph G₀ C).n ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj g0Ptr (dynGraphSize vCap eCap) outM0Addr 1 ∧
    RangesDisj visBase vCap vCompBase vCap ∧
    RangesDisj visBase vCap edgeC1Base eCap ∧
    RangesDisj visBase vCap edgeC2Base eCap ∧
    RangesDisj visBase vCap bfsQBase (compGraph G₀ C).n ∧
    RangesDisj visBase vCap compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj visBase vCap outM0Addr 1 ∧
    RangesDisj vCompBase vCap edgeC1Base eCap ∧
    RangesDisj vCompBase vCap edgeC2Base eCap ∧
    RangesDisj vCompBase vCap bfsQBase (compGraph G₀ C).n ∧
    RangesDisj vCompBase vCap compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj vCompBase vCap outM0Addr 1 ∧
    RangesDisj edgeC1Base eCap edgeC2Base eCap ∧
    RangesDisj edgeC1Base eCap bfsQBase (compGraph G₀ C).n ∧
    RangesDisj edgeC1Base eCap compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj edgeC1Base eCap outM0Addr 1 ∧
    RangesDisj edgeC2Base eCap bfsQBase (compGraph G₀ C).n ∧
    RangesDisj edgeC2Base eCap compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj edgeC2Base eCap outM0Addr 1 ∧
    RangesDisj bfsQBase (compGraph G₀ C).n compEdgesBase (3 * (compGraph G₀ C).m) ∧
    RangesDisj bfsQBase (compGraph G₀ C).n outM0Addr 1 ∧
    RangesDisj compEdgesBase (3 * (compGraph G₀ C).m) outM0Addr 1
  post args mem ret mem' := ∃ g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase v0 c outM0Addr,
    args = [g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr] ∧
    ret = (compGraph G₀ C).n ∧
    mem' outM0Addr = (compGraph G₀ C).m ∧
    (∀ v < vCap, mem' (visBase + v) = if v ∈ visSet ∪ C then 1 else 0) ∧
    (∀ u ∈ C, mem' (vCompBase + u) = c) ∧
    (∀ u < vCap, u ∉ C → mem' (vCompBase + u) = mem (vCompBase + u)) ∧
    (∀ e ∈ compEdgeSet G₀ C, mem' (edgeC1Base + e) = c ∧ mem' (edgeC2Base + e) = c) ∧
    (∀ e < eCap, e ∉ compEdgeSet G₀ C →
      mem' (edgeC1Base + e) = mem (edgeC1Base + e) ∧ mem' (edgeC2Base + e) = mem (edgeC2Base + e)) ∧
    (∃ qL : List ℕ, qL.length = (compGraph G₀ C).n ∧ qL.Nodup ∧ (∀ u, u ∈ qL ↔ u ∈ C) ∧
      ListAt mem' bfsQBase qL) ∧
    (∃ eL : List (ℕ × ℕ × ℕ), eL.length = (compGraph G₀ C).m ∧ (eL.map Prod.fst).Nodup ∧
      EdgeTriplesAt mem' compEdgesBase eL ∧
      (∀ t ∈ eL, t.1 ∈ compEdgeSet G₀ C ∧ t.2.1 = G₀.tail t.1 ∧ t.2.2 = G₀.head t.1) ∧
      (∀ e ∈ compEdgeSet G₀ C, ∃ t ∈ eL, t.1 = e)) ∧
    ∀ a, (a < visBase ∨ visBase + vCap ≤ a) →
      (a < vCompBase ∨ vCompBase + vCap ≤ a) →
      (a < edgeC1Base ∨ edgeC1Base + eCap ≤ a) →
      (a < edgeC2Base ∨ edgeC2Base + eCap ≤ a) →
      (a < bfsQBase ∨ bfsQBase + (compGraph G₀ C).n ≤ a) →
      (a < compEdgesBase ∨ compEdgesBase + 3 * (compGraph G₀ C).m ≤ a) →
      a ≠ outM0Addr →
      mem' a = mem a
  cost _ _ := 100 * (compGraph G₀ C).n + 350 * (compGraph G₀ C).m + 180

/-! ## 2. Graph-theoretic BFS lemmas -/

lemma compBfs_reach_all {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) {v0 : ℕ} (hv0 : v0 ∈ C) {qL : List ℕ}
    (hv0_q : v0 ∈ qL) (hsub : ∀ u ∈ qL, u ∈ C)
    (hclosed : ∀ u ∈ qL, ∀ e ∈ G₀.E,
      (G₀.tail e = u → G₀.head e ∈ qL) ∧ (G₀.head e = u → G₀.tail e ∈ qL)) :
    ∀ x, x ∈ qL ↔ x ∈ C := by
  intro x
  refine ⟨hsub x, fun hx => ?_⟩
  obtain ⟨P, hP⟩ := compGraph_connected hG₀ hC v0 hv0 x hx
  have hwalk : ∀ a b Q, (compGraph G₀ C).IsWalk a b Q → a ∈ qL → b ∈ qL := by
    intro a b Q hQ
    induction hQ with
    | nil _ => exact id
    | @cons a b z rest hzE hsrc hdst ih =>
      intro ha
      rcases z with ⟨e, dir⟩
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ hzE
      have hmid : (compGraph G₀ C).dst (e, dir) ∈ qL := by
        cases dir
        · simp only [MGraph.src, compGraph, Bool.false_eq_true, ↓reduceIte] at hsrc
          simp only [MGraph.dst, compGraph, Bool.false_eq_true, ↓reduceIte]
          exact (hclosed a ha e heG).2 hsrc
        · simp only [MGraph.src, compGraph, ↓reduceIte] at hsrc
          simp only [MGraph.dst, compGraph, ↓reduceIte]
          exact (hclosed a ha e heG).1 hsrc
      exact ih hmid
  exact hwalk v0 x P hP hv0_q

lemma compBfs_sum_incLen {mem : ℕ → ℕ} {g0Ptr vCap eCap : ℕ} {G₀ : MGraph}
    (hdg : DynGraphAt mem g0Ptr vCap eCap G₀) {C : Finset ℕ} (hC : C ∈ components G₀)
    {incL : ℕ → List ℕ}
    (hinc : ∀ s < vCap,
      (incL s).Nodup ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap ∧ h / 2 ∈ G₀.E ∧
        (if h % 2 = 0 then mem (dgETailSlotBase g0Ptr vCap eCap + h / 2)
         else mem (dgEHeadSlotBase g0Ptr vCap eCap + h / 2)) = s) :
    C.sum (fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).length) =
      2 * (compGraph G₀ C).m := by
  classical
  have hG₀ := hdg.1
  have hVlt := hdg.2.1
  have hElt := hdg.2.2.1
  have hE2I := hdg.2.2.2.2.2.2.2.2.2.1
  have hEnds := hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC_sub : C ⊆ G₀.V := fun u hu => by
    rcases Finset.mem_image.mp hC with ⟨w, _, rfl⟩
    exact (mem_compOf_iff.mp hu).1
  have hlen_eq : ∀ u ∈ C, (incL (mem (dgExtToIntBase g0Ptr vCap + u))).length =
      (incL (mem (dgExtToIntBase g0Ptr vCap + u))).toFinset.card := fun u hu => by
    have hsu := (hE2I u (hC_sub hu)).1
    exact (List.toFinset_card_of_nodup (hinc _ (hVlt _ hsu)).1).symm
  have hdisj : Set.PairwiseDisjoint (↑C : Set ℕ)
      (fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).toFinset) := by
    intro u1 hu1 u2 hu2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h hh1 hh2
    rw [List.mem_toFinset] at hh1 hh2
    have hs1 := (hE2I u1 (hC_sub hu1)).1
    have hs2 := (hE2I u2 (hC_sub hu2)).1
    have h1 := ((hinc _ (hVlt _ hs1)).2 h).mp hh1
    have h2 := ((hinc _ (hVlt _ hs2)).2 h).mp hh2
    have hseq : mem (dgExtToIntBase g0Ptr vCap + u1) = mem (dgExtToIntBase g0Ptr vCap + u2) :=
      h1.2.2.symm.trans h2.2.2
    have hu_eq : u1 = u2 := by
      have r1 := (hE2I u1 (hC_sub hu1)).2
      have r2 := (hE2I u2 (hC_sub hu2)).2
      rw [hseq] at r1; exact r1.symm.trans r2
    exact hne hu_eq
  have hbiU_eq : C.biUnion (fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).toFinset) =
      (compEdgeSet G₀ C).biUnion (fun e => ({2 * e, 2 * e + 1} : Finset ℕ)) := by
    ext h
    simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, hh⟩
      have hsu := (hE2I u (hC_sub hu)).1
      obtain ⟨_, heG, hslot⟩ := ((hinc _ (hVlt _ hsu)).2 h).mp hh
      have hends := hEnds (h / 2) heG
      refine ⟨h / 2, ?_, ?_⟩
      · rw [compEdgeSet, Finset.mem_filter]; refine ⟨heG, ?_⟩
        by_cases hp : h % 2 = 0
        · simp only [hp, ↓reduceIte, hends.1] at hslot
          have ht_eq : G₀.tail (h / 2) = u := by
            have := (hE2I (G₀.tail (h / 2)) (hG₀ _ heG).1).2
            rw [hslot, (hE2I u (hC_sub hu)).2] at this; exact this.symm
          exact ht_eq ▸ hu
        · simp only [hp, ↓reduceIte, hends.2] at hslot
          have hh_eq : G₀.head (h / 2) = u := by
            have := (hE2I (G₀.head (h / 2)) (hG₀ _ heG).2).2
            rw [hslot, (hE2I u (hC_sub hu)).2] at this; exact this.symm
          rcases Finset.mem_image.mp hC with ⟨w, _, rfl⟩
          exact mem_compOf_iff.mpr ⟨(hG₀ _ heG).1,
            connected_trans (mem_compOf_iff.mp (hh_eq ▸ hu)).2 (connected_symm (connected_of_edge heG))⟩
      · omega
    · rintro ⟨e, heC, rfl | rfl⟩
      · have ⟨heG, htC, _⟩ := mem_compEdgeSet_endpoints hG₀ hC heC
        have hst := (hE2I (G₀.tail e) (hG₀ e heG).1).1
        refine ⟨G₀.tail e, htC, ((hinc _ (hVlt _ hst)).2 (2 * e)).mpr ?_⟩
        refine ⟨by have := hElt e heG; omega, by simpa using heG, ?_⟩
        simp [(hEnds e heG).1]
      · have ⟨heG, _, hhC⟩ := mem_compEdgeSet_endpoints hG₀ hC heC
        have hsh := (hE2I (G₀.head e) (hG₀ e heG).2).1
        refine ⟨G₀.head e, hhC, ((hinc _ (hVlt _ hsh)).2 (2 * e + 1)).mpr ?_⟩
        have hdiv : (2 * e + 1) / 2 = e := by omega
        have hmod : (2 * e + 1) % 2 = 1 := by omega
        refine ⟨by have := hElt e heG; omega, by simpa [hdiv] using heG, ?_⟩
        simp [hdiv, hmod, (hEnds e heG).2]
  have hdisjE : Set.PairwiseDisjoint (↑(compEdgeSet G₀ C) : Set ℕ)
      (fun e => ({2 * e, 2 * e + 1} : Finset ℕ)) := by
    intro e1 _ e2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    omega
  calc C.sum (fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).length)
      = C.sum (fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).toFinset.card) :=
        Finset.sum_congr rfl hlen_eq
    _ = (C.biUnion fun u => (incL (mem (dgExtToIntBase g0Ptr vCap + u))).toFinset).card :=
        (Finset.card_biUnion hdisj).symm
    _ = ((compEdgeSet G₀ C).biUnion fun e => ({2 * e, 2 * e + 1} : Finset ℕ)).card := by
        rw [hbiU_eq]
    _ = (compEdgeSet G₀ C).sum (fun e => ({2 * e, 2 * e + 1} : Finset ℕ).card) :=
        Finset.card_biUnion hdisjE
    _ = (compEdgeSet G₀ C).sum (fun _ => 2) :=
        Finset.sum_congr rfl fun e _ => Finset.card_pair (by omega)
    _ = 2 * (compGraph G₀ C).m := by simp [compGraph, MGraph.m, mul_comm]

/-! ## 3. Shared loop invariants and context -/

/-- Memory invariant preserved across outer and inner loops of `compBfsCompProc`. -/
def BfsMemInv (mem0 mem : ℕ → ℕ)
    (vCap eCap visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase outM0Addr c : ℕ)
    (G₀ : MGraph) (C visSet : Finset ℕ) (qL : List ℕ) (eL : List (ℕ × ℕ × ℕ)) : Prop :=
  qL.Nodup ∧ (∀ u ∈ qL, u ∈ C) ∧ ListAt mem bfsQBase qL ∧
  (eL.map Prod.fst).Nodup ∧ EdgeTriplesAt mem compEdgesBase eL ∧
  (∀ t ∈ eL, t.1 ∈ compEdgeSet G₀ C ∧ t.2.1 = G₀.tail t.1 ∧ t.2.2 = G₀.head t.1) ∧
  (∀ v < vCap, mem (visBase + v) = if v ∈ visSet ∨ v ∈ qL then 1 else 0) ∧
  (∀ u ∈ qL, mem (vCompBase + u) = c) ∧
  (∀ u < vCap, u ∉ qL → mem (vCompBase + u) = mem0 (vCompBase + u)) ∧
  (∀ t ∈ eL, mem (edgeC1Base + t.1) = c ∧ mem (edgeC2Base + t.1) = c) ∧
  (∀ e < eCap, (∀ t ∈ eL, t.1 ≠ e) →
    mem (edgeC1Base + e) = mem0 (edgeC1Base + e) ∧
    mem (edgeC2Base + e) = mem0 (edgeC2Base + e)) ∧
  (∀ a, (a < visBase ∨ visBase + vCap ≤ a) →
    (a < vCompBase ∨ vCompBase + vCap ≤ a) →
    (a < edgeC1Base ∨ edgeC1Base + eCap ≤ a) →
    (a < edgeC2Base ∨ edgeC2Base + eCap ≤ a) →
    (a < bfsQBase ∨ bfsQBase + (compGraph G₀ C).n ≤ a) →
    (a < compEdgesBase ∨ compEdgesBase + 3 * (compGraph G₀ C).m ≤ a) →
    a ≠ outM0Addr →
    mem a = mem0 a)

lemma bfs_qL_len_le {C : Finset ℕ} {qL : List ℕ}
    (hnd : qL.Nodup) (hsub : ∀ u ∈ qL, u ∈ C) : qL.length ≤ C.card := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card fun u hu => hsub u (List.mem_toFinset.mp hu)

lemma bfs_eL_len_le {G₀ : MGraph} {C : Finset ℕ} {eL : List (ℕ × ℕ × ℕ)}
    (hnd : (eL.map Prod.fst).Nodup)
    (hsub : ∀ t ∈ eL, t.1 ∈ compEdgeSet G₀ C ∧ t.2.1 = G₀.tail t.1 ∧ t.2.2 = G₀.head t.1) :
    eL.length ≤ (compGraph G₀ C).m := by
  classical
  have hlen : eL.length = (eL.map Prod.fst).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hlen]
  exact Finset.card_le_card fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact (hsub t ht).1

/-- Register invariant for the fixed base pointers of `compBfsCompProc`. -/
structure BfsRegsOK (g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase
    c outM0Addr vCap eCap : ℕ) (r : ℕ → ℕ) : Prop where
  r0 : r 0 = g0Ptr
  r1 : r 1 = visBase
  r2 : r 2 = vCompBase
  r3 : r 3 = edgeC1Base
  r4 : r 4 = edgeC2Base
  r5 : r 5 = bfsQBase
  r6 : r 6 = compEdgesBase
  r8 : r 8 = c
  r9 : r 9 = outM0Addr
  r10 : r 10 = vCap
  r11 : r 11 = eCap
  r12 : r 12 = dgExtToIntBase g0Ptr vCap
  r13 : r 13 = dgIntToExtBase g0Ptr vCap
  r14 : r 14 = dgIncHeadBase g0Ptr vCap
  r15 : r 15 = dgETailSlotBase g0Ptr vCap eCap
  r16 : r 16 = dgEHeadSlotBase g0Ptr vCap eCap
  r17 : r 17 = dgHeNextBase g0Ptr vCap eCap

lemma BfsRegsOK.update_ge18 {g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase
    c outM0Addr vCap eCap k v : ℕ} {r : ℕ → ℕ}
    (hR : BfsRegsOK g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase
      c outM0Addr vCap eCap r) (hk : 18 ≤ k) :
    BfsRegsOK g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase
      c outM0Addr vCap eCap (Function.update r k v) where
  r0 := by rw [Function.update_of_ne (by omega)]; exact hR.r0
  r1 := by rw [Function.update_of_ne (by omega)]; exact hR.r1
  r2 := by rw [Function.update_of_ne (by omega)]; exact hR.r2
  r3 := by rw [Function.update_of_ne (by omega)]; exact hR.r3
  r4 := by rw [Function.update_of_ne (by omega)]; exact hR.r4
  r5 := by rw [Function.update_of_ne (by omega)]; exact hR.r5
  r6 := by rw [Function.update_of_ne (by omega)]; exact hR.r6
  r8 := by rw [Function.update_of_ne (by omega)]; exact hR.r8
  r9 := by rw [Function.update_of_ne (by omega)]; exact hR.r9
  r10 := by rw [Function.update_of_ne (by omega)]; exact hR.r10
  r11 := by rw [Function.update_of_ne (by omega)]; exact hR.r11
  r12 := by rw [Function.update_of_ne (by omega)]; exact hR.r12
  r13 := by rw [Function.update_of_ne (by omega)]; exact hR.r13
  r14 := by rw [Function.update_of_ne (by omega)]; exact hR.r14
  r15 := by rw [Function.update_of_ne (by omega)]; exact hR.r15
  r16 := by rw [Function.update_of_ne (by omega)]; exact hR.r16
  r17 := by rw [Function.update_of_ne (by omega)]; exact hR.r17

/-- Bundled static preconditions for the inner and outer loop proofs of `compBfsCompProc`. -/
structure BfsCtx (w vCap eCap : ℕ) (G₀ : MGraph) (C visSet : Finset ℕ) (mem : ℕ → ℕ) where
  g0Ptr : ℕ
  visBase : ℕ
  vCompBase : ℕ
  edgeC1Base : ℕ
  edgeC2Base : ℕ
  bfsQBase : ℕ
  compEdgesBase : ℕ
  v0 : ℕ
  c : ℕ
  outM0Addr : ℕ
  hw16 : 16 ≤ 2 ^ w
  hdg : DynGraphAt mem g0Ptr vCap eCap G₀
  incL : ℕ → List ℕ
  hincFull : ∀ s < vCap,
    IsDoublyLinkedList mem (dgHePrevBase g0Ptr vCap eCap) (dgHeNextBase g0Ptr vCap eCap)
      (dgIncHeadBase g0Ptr vCap + s) (2 * eCap) (incL s) ∧
    (∀ h ∈ incL s, h < 2 * eCap) ∧
    ∀ h, h ∈ incL s ↔ h < 2 * eCap ∧ h / 2 ∈ G₀.E ∧
      (if h % 2 = 0 then mem (dgETailSlotBase g0Ptr vCap eCap + h / 2)
       else mem (dgEHeadSlotBase g0Ptr vCap eCap + h / 2)) = s
  hC : C ∈ components G₀
  hv0 : v0 ∈ C
  hvisSub : visSet ⊆ G₀.V
  hvisDisj : Disjoint visSet C
  hvisAt : ∀ v < vCap, mem (visBase + v) = if v ∈ visSet then 1 else 0
  hc_lt : c < vCap
  hg0_w : g0Ptr + dynGraphSize vCap eCap < 2 ^ w
  hvis_w : visBase + vCap < 2 ^ w
  hvc_w : vCompBase + vCap < 2 ^ w
  hec1_w : edgeC1Base + eCap < 2 ^ w
  hec2_w : edgeC2Base + eCap < 2 ^ w
  hbq_w : bfsQBase + (compGraph G₀ C).n < 2 ^ w
  hce_w : compEdgesBase + 3 * (compGraph G₀ C).m < 2 ^ w
  hm0_w : outM0Addr + 1 < 2 ^ w
  hd_gv : RangesDisj g0Ptr (dynGraphSize vCap eCap) visBase vCap
  hd_gvc : RangesDisj g0Ptr (dynGraphSize vCap eCap) vCompBase vCap
  hd_ge1 : RangesDisj g0Ptr (dynGraphSize vCap eCap) edgeC1Base eCap
  hd_ge2 : RangesDisj g0Ptr (dynGraphSize vCap eCap) edgeC2Base eCap
  hd_gbq : RangesDisj g0Ptr (dynGraphSize vCap eCap) bfsQBase (compGraph G₀ C).n
  hd_gce : RangesDisj g0Ptr (dynGraphSize vCap eCap) compEdgesBase (3 * (compGraph G₀ C).m)
  hd_gm0 : RangesDisj g0Ptr (dynGraphSize vCap eCap) outM0Addr 1
  hd_vvc : RangesDisj visBase vCap vCompBase vCap
  hd_ve1 : RangesDisj visBase vCap edgeC1Base eCap
  hd_ve2 : RangesDisj visBase vCap edgeC2Base eCap
  hd_vbq : RangesDisj visBase vCap bfsQBase (compGraph G₀ C).n
  hd_vce : RangesDisj visBase vCap compEdgesBase (3 * (compGraph G₀ C).m)
  hd_vm0 : RangesDisj visBase vCap outM0Addr 1
  hd_vce1 : RangesDisj vCompBase vCap edgeC1Base eCap
  hd_vce2 : RangesDisj vCompBase vCap edgeC2Base eCap
  hd_vcbq : RangesDisj vCompBase vCap bfsQBase (compGraph G₀ C).n
  hd_vcce : RangesDisj vCompBase vCap compEdgesBase (3 * (compGraph G₀ C).m)
  hd_vcm0 : RangesDisj vCompBase vCap outM0Addr 1
  hd_e1e2 : RangesDisj edgeC1Base eCap edgeC2Base eCap
  hd_e1bq : RangesDisj edgeC1Base eCap bfsQBase (compGraph G₀ C).n
  hd_e1ce : RangesDisj edgeC1Base eCap compEdgesBase (3 * (compGraph G₀ C).m)
  hd_e1m0 : RangesDisj edgeC1Base eCap outM0Addr 1
  hd_e2bq : RangesDisj edgeC2Base eCap bfsQBase (compGraph G₀ C).n
  hd_e2ce : RangesDisj edgeC2Base eCap compEdgesBase (3 * (compGraph G₀ C).m)
  hd_e2m0 : RangesDisj edgeC2Base eCap outM0Addr 1
  hd_bqce : RangesDisj bfsQBase (compGraph G₀ C).n compEdgesBase (3 * (compGraph G₀ C).m)
  hd_bqm0 : RangesDisj bfsQBase (compGraph G₀ C).n outM0Addr 1
  hd_cem0 : RangesDisj compEdgesBase (3 * (compGraph G₀ C).m) outM0Addr 1

lemma BfsCtx.hC_sub {w vCap eCap : ℕ} {G₀ : MGraph} {C visSet : Finset ℕ} {mem : ℕ → ℕ}
    (ctx : BfsCtx w vCap eCap G₀ C visSet mem) : C ⊆ G₀.V := fun u hu => by
  rcases Finset.mem_image.mp ctx.hC with ⟨w', _, rfl⟩
  exact (mem_compOf_iff.mp hu).1

lemma BfsCtx.hg0_agree {w vCap eCap : ℕ} {G₀ : MGraph} {C visSet : Finset ℕ} {mem m' : ℕ → ℕ}
    (ctx : BfsCtx w vCap eCap G₀ C visSet mem)
    (hfr : ∀ a, (a < ctx.visBase ∨ ctx.visBase + vCap ≤ a) →
      (a < ctx.vCompBase ∨ ctx.vCompBase + vCap ≤ a) →
      (a < ctx.edgeC1Base ∨ ctx.edgeC1Base + eCap ≤ a) →
      (a < ctx.edgeC2Base ∨ ctx.edgeC2Base + eCap ≤ a) →
      (a < ctx.bfsQBase ∨ ctx.bfsQBase + (compGraph G₀ C).n ≤ a) →
      (a < ctx.compEdgesBase ∨ ctx.compEdgesBase + 3 * (compGraph G₀ C).m ≤ a) →
      a ≠ ctx.outM0Addr → m' a = mem a) :
    ∀ a, ctx.g0Ptr ≤ a → a < ctx.g0Ptr + dynGraphSize vCap eCap → m' a = mem a := by
  intro a ha1 ha2
  refine hfr a ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rcases ctx.hd_gv with h | h <;> omega
  · rcases ctx.hd_gvc with h | h <;> omega
  · rcases ctx.hd_ge1 with h | h <;> omega
  · rcases ctx.hd_ge2 with h | h <;> omega
  · rcases ctx.hd_gbq with h | h <;> omega
  · rcases ctx.hd_gce with h | h <;> omega
  · rcases ctx.hd_gm0 with h | h <;> omega

end

end MinCostFlow.SparseCore.Program
