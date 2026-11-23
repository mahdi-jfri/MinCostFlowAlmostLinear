module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.PortGraph
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase
public import MinCostFlow.ExpanderDecomp.ProgCloud

import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Port Graph Word-RAM Procedure — Base Definitions, Setup, Init, and Clear (`ProgPortGraphBase`)

Provides the pure helpers, workspace layout, procedure definitions (`NoRand`), register invariant,
and verified triples for `pgSetupStmt`, `pgInitLocStmt`, and `pgClearLocStmt` used by
`portGraphEntry` (`ProgPortGraph.lean`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helpers for `cloud`, `PortGraph`, and Cloud Offsets -/

/-- `ProgCloud.cloud` satisfies `IsCloudExpander` with `cloudAlpha = 1 / 12`. -/
theorem isCloudExpander_cloud : IsCloudExpander cloud cloudAlpha where
  n_eq _ hs := (cloud_spec hs).1
  isValid _ hs := (cloud_spec hs).2.1
  deg_le _ hs := (cloud_spec hs).2.2.2.1
  expansion _ hs := (cloud_spec hs).2.2.2.2

/-- `portOwner G X` depends only on `G.inside X`. -/
lemma portOwner_congr_inside {G₁ G₂ : Graph} {X : Finset ℕ}
    (h : G₁.inside X = G₂.inside X) (p : ℕ) :
    portOwner G₁ X p = portOwner G₂ X p := by
  unfold portOwner; rw [h]

/-- `cloudPortsList G X` depends only on `G.inside X`. -/
lemma cloudPortsList_congr_inside {G₁ G₂ : Graph} {X : Finset ℕ}
    (h : G₁.inside X = G₂.inside X) (v : ℕ) :
    cloudPortsList G₁ X v = cloudPortsList G₂ X v := by
  unfold cloudPortsList
  simp only [h]
  congr 1; funext p; rw [portOwner_congr_inside h]

/-- `portGraph cl G X` depends only on `G.inside X`. -/
lemma portGraph_congr_inside (cl : ℕ → Graph) {G₁ G₂ : Graph} {X : Finset ℕ}
    (h : G₁.inside X = G₂.inside X) :
    portGraph cl G₁ X = portGraph cl G₂ X := by
  unfold portGraph allCloudEdges cloudEdgesFor
  simp only [h]
  congr 1; congr 1; apply List.flatMap_congr; intro v _
  simp only [cloudPortsList_congr_inside h]

private lemma pairwise_le_eq_of_perm {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· ≤ ·))
    (h₂ : l₂.Pairwise (· ≤ ·)) (hperm : l₁.Perm l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (List.Perm.nil_eq hperm)
  | cons a t ih =>
    cases l₂ with
    | nil => exact False.elim (by simpa using hperm.length_eq)
    | cons b s =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        have ha_mem : a ∈ b :: s := hperm.subset List.mem_cons_self
        have hb_mem : b ∈ a :: t := hperm.symm.subset List.mem_cons_self
        rcases List.mem_cons.mp ha_mem with rfl | has
        · rfl
        · rcases List.mem_cons.mp hb_mem with rfl | hbt
          · rfl
          · exact le_antisymm (h₁.1 b hbt) (h₂.1 a has)
      subst hab
      congr 1
      exact ih h₁.2 h₂.2 ((List.perm_cons a).mp hperm)

/-- A strictly increasing list `verts` equals `verts.toFinset.sort (· ≤ ·)`. -/
lemma pairwise_lt_eq_sort (verts : List ℕ) (hsorted : verts.Pairwise (· < ·)) :
    verts = verts.toFinset.sort (· ≤ ·) := by
  have hnd : verts.Nodup := hsorted.imp fun h => Nat.ne_of_lt h
  have hnd_s : (verts.toFinset.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hperm : verts.Perm (verts.toFinset.sort (· ≤ ·)) := by
    refine (List.perm_ext_iff_of_nodup hnd hnd_s).mpr fun x => ?_
    simp [Finset.mem_sort]
  have hle1 : verts.Pairwise (· ≤ ·) := hsorted.imp fun h => Nat.le_of_lt h
  have hle2 : (verts.toFinset.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  exact pairwise_le_eq_of_perm hle1 hle2 hperm

/-- Prefix sum of cloud sizes for the first `i` vertices of `verts`. -/
def cloudOff (verts : List ℕ) (G : Graph) (X : Finset ℕ) (i : ℕ) : ℕ :=
  (Finset.range i).sum fun t => (cloudPortsList G X (verts.getD t 0)).length

lemma cloudOff_zero (verts : List ℕ) (G : Graph) (X : Finset ℕ) :
    cloudOff verts G X 0 = 0 := by
  simp [cloudOff]

lemma cloudOff_succ (verts : List ℕ) (G : Graph) (X : Finset ℕ) (i : ℕ) :
    cloudOff verts G X (i + 1) =
      cloudOff verts G X i + (cloudPortsList G X (verts.getD i 0)).length := by
  simp [cloudOff, Finset.sum_range_succ]

lemma cloudOff_mono (verts : List ℕ) (G : Graph) (X : Finset ℕ) {i j : ℕ} (hij : i ≤ j) :
    cloudOff verts G X i ≤ cloudOff verts G X j := by
  unfold cloudOff
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

/-- The total cloud size across a duplicate-free list `verts` with `X = verts.toFinset` equals
`2 * (G.inside X).length`. -/
lemma cloudOff_length {verts : List ℕ} (hnd : verts.Nodup) (G : Graph) :
    cloudOff verts G verts.toFinset verts.length = 2 * (G.inside verts.toFinset).length := by
  set X := verts.toFinset
  have h1 : cloudOff verts G X verts.length = ∑ v ∈ X, (cloudOf G X v).card := by
    unfold cloudOff
    trans (Finset.range verts.length).sum fun t => (cloudOf G X (verts.getD t 0)).card
    · exact Finset.sum_congr rfl fun t _ => cloudPortsList_length G X _
    · symm
      refine Finset.sum_bij (fun v _ => verts.idxOf v) ?_ ?_ ?_ ?_
      · intro v hv
        exact Finset.mem_range.mpr (List.idxOf_lt_length_of_mem (List.mem_toFinset.mp hv))
      · intro v₁ hv₁ v₂ hv₂ heq
        have h1 := nodup_getD_idxOf (List.mem_toFinset.mp hv₁)
        have h2 := nodup_getD_idxOf (List.mem_toFinset.mp hv₂)
        rw [← h1, heq, h2]
      · intro t ht
        have ht' : t < verts.length := Finset.mem_range.mp ht
        refine ⟨verts[t]'ht', List.mem_toFinset.mpr (List.getElem_mem ht'), ?_⟩
        rw [← List.getD_eq_getElem verts 0 ht']
        exact nodup_idxOf_getD hnd ht'
      · intro v hv
        rw [nodup_getD_idxOf (List.mem_toFinset.mp hv)]
  rw [h1]
  have h2 : ∑ v ∈ X, (cloudOf G X v).card = (X.biUnion (cloudOf G X)).card := by
    rw [Finset.card_biUnion]
    intro u _ v _ huv
    exact cloudOf_disjoint G X huv
  rw [h2, ← liftSet_eq_biUnion]
  have h3 : liftSet G X X = Finset.range (2 * (G.inside X).length) := by
    ext p
    simp only [liftSet, Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    exact portOwner_mem
  rw [h3, Finset.card_range]

lemma cloudOff_le_two_mul_e {verts : List ℕ} (hnd : verts.Nodup) (G : Graph) {i : ℕ}
    (hi : i ≤ verts.length) :
    cloudOff verts G verts.toFinset i ≤ 2 * (G.inside verts.toFinset).length := by
  calc cloudOff verts G verts.toFinset i
      ≤ cloudOff verts G verts.toFinset verts.length := cloudOff_mono _ _ _ hi
    _ = 2 * (G.inside verts.toFinset).length := cloudOff_length hnd G

/-- Prefix of `cloudPortsList G X v` consisting of ports `< p`. -/
def cloudPortsPrefix (G : Graph) (X : Finset ℕ) (v p : ℕ) : List ℕ :=
  (List.range p).filter fun q => decide (portOwner G X q = v)

lemma cloudPortsPrefix_zero (G : Graph) (X : Finset ℕ) (v : ℕ) :
    cloudPortsPrefix G X v 0 = [] := rfl

lemma cloudPortsPrefix_full (G : Graph) (X : Finset ℕ) (v : ℕ) :
    cloudPortsPrefix G X v (2 * (G.inside X).length) = cloudPortsList G X v := rfl

lemma cloudPortsPrefix_succ (G : Graph) (X : Finset ℕ) (v p : ℕ) :
    cloudPortsPrefix G X v (p + 1) =
      cloudPortsPrefix G X v p ++ if portOwner G X p = v then [p] else [] := by
  unfold cloudPortsPrefix
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases h : portOwner G X p = v <;> simp [h]

lemma cloudPortsPrefix_length_le (G : Graph) (X : Finset ℕ) (v : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    (cloudPortsPrefix G X v p).length ≤ (cloudPortsPrefix G X v q).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, cloudPortsPrefix_succ, List.length_append]
    omega

/-- Prefix sum of cloud-expander heap space for the first `i` vertices of `verts`. -/
def cloudHeapUsed (verts : List ℕ) (G : Graph) (X : Finset ℕ) (i : ℕ) : ℕ :=
  (Finset.range i).sum fun t =>
    let s := (cloudPortsList G X (verts.getD t 0)).length
    if 2 ≤ s then cloudExpanderSpace s else 0

/-- Polynomial heap space budget covering all cloud expander calls for `e = |G.inside X|` edges. -/
def portGraphHeapSpace (e : ℕ) : ℕ :=
  41600 * e ^ 4 + 4

private lemma sum_pow_four_le (k : ℕ) (f : ℕ → ℕ) :
    (Finset.range k).sum (fun t => f t ^ 4) ≤ ((Finset.range k).sum f) ^ 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := (Finset.range k).sum f
    set x := f k
    have hexp : (S + x) ^ 4 = S ^ 4 + 4 * S ^ 3 * x + 6 * S ^ 2 * x ^ 2 + 4 * S * x ^ 3 + x ^ 4 := by
      ring
    omega

private lemma cloudExpanderSpace_le_mul_pow_four {s : ℕ} (hs : 2 ≤ s) :
    cloudExpanderSpace s ≤ 2600 * s ^ 4 := by
  unfold cloudExpanderSpace
  have h1 : s + 3 ≤ 3 * s := by omega
  have h2 : (s + 3) ^ 4 ≤ (3 * s) ^ 4 := Nat.pow_le_pow_left h1 4
  have h3 : (3 * s) ^ 4 = 81 * s ^ 4 := by ring
  have h4 : 16 ≤ s ^ 4 := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ s ^ 4 := Nat.pow_le_pow_left hs 4
  omega

lemma cloudHeapUsed_le {verts : List ℕ} (hnd : verts.Nodup) (G : Graph) {i : ℕ}
    (hi : i ≤ verts.length) :
    cloudHeapUsed verts G verts.toFinset i ≤ portGraphHeapSpace (G.inside verts.toFinset).length := by
  set X := verts.toFinset
  set e := (G.inside X).length
  have hmono : cloudHeapUsed verts G X i ≤ cloudHeapUsed verts G X verts.length :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hi)
  have h1 : cloudHeapUsed verts G X verts.length ≤
      (Finset.range verts.length).sum
        (fun t => 2600 * (cloudPortsList G X (verts.getD t 0)).length ^ 4) := by
    refine Finset.sum_le_sum fun t _ => ?_
    dsimp only
    split_ifs with hs
    · exact cloudExpanderSpace_le_mul_pow_four hs
    · exact Nat.zero_le _
  have h2 : (Finset.range verts.length).sum
        (fun t => 2600 * (cloudPortsList G X (verts.getD t 0)).length ^ 4) =
      2600 * (Finset.range verts.length).sum
        (fun t => (cloudPortsList G X (verts.getD t 0)).length ^ 4) := by
    rw [Finset.mul_sum]
  have h3 := sum_pow_four_le verts.length (fun t => (cloudPortsList G X (verts.getD t 0)).length)
  have hsum : (Finset.range verts.length).sum
      (fun t => (cloudPortsList G X (verts.getD t 0)).length) = 2 * e :=
    cloudOff_length hnd G
  rw [hsum] at h3
  have h4 : 2600 * (2 * e) ^ 4 = 41600 * e ^ 4 := by ring
  unfold portGraphHeapSpace
  have h5 := Nat.mul_le_mul_left 2600 h3
  omega

/-- Prefix of `allCloudEdges` over the first `i` vertices of `verts`. -/
def allCloudEdgesPrefix (verts : List ℕ) (G : Graph) (X : Finset ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  (verts.take i).flatMap (cloudEdgesFor cloud G X)

lemma allCloudEdgesPrefix_zero (verts : List ℕ) (G : Graph) (X : Finset ℕ) :
    allCloudEdgesPrefix verts G X 0 = [] := rfl

lemma allCloudEdgesPrefix_succ {verts : List ℕ} (G : Graph) (X : Finset ℕ) {i : ℕ}
    (hi : i < verts.length) :
    allCloudEdgesPrefix verts G X (i + 1) =
      allCloudEdgesPrefix verts G X i ++ cloudEdgesFor cloud G X (verts[i]'hi) := by
  unfold allCloudEdgesPrefix
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

lemma allCloudEdgesPrefix_full {verts : List ℕ} (hsorted : verts.Pairwise (· < ·)) (G : Graph) :
    allCloudEdgesPrefix verts G verts.toFinset verts.length =
      allCloudEdges cloud G verts.toFinset := by
  unfold allCloudEdgesPrefix allCloudEdges
  rw [List.take_length, ← pairwise_lt_eq_sort verts hsorted]

lemma allCloudEdgesPrefix_length_le {verts : List ℕ} (hnd : verts.Nodup) (G : Graph) {i : ℕ}
    (hi : i ≤ verts.length) :
    (allCloudEdgesPrefix verts G verts.toFinset i).length ≤
      9 * (G.inside verts.toFinset).length := by
  set X := verts.toFinset
  have hlen_for : ∀ v, 2 * (cloudEdgesFor cloud G X v).length ≤
      9 * (cloudPortsList G X v).length := by
    intro v
    unfold cloudEdgesFor
    dsimp only
    split_ifs with hs
    · rw [List.length_map,
        List.filter_eq_self.mpr fun e he => decide_eq_true ((cloud_spec hs).2.2.1 e he)]
      exact cloud_m_le hs
    · simp
  have hsum_le : 2 * (allCloudEdgesPrefix verts G X i).length ≤ 9 * cloudOff verts G X i := by
    induction i with
    | zero => simp [allCloudEdgesPrefix, cloudOff]
    | succ j ih =>
      have hj : j < verts.length := by omega
      rw [allCloudEdgesPrefix_succ G X hj, List.length_append, cloudOff_succ,
        List.getD_eq_getElem verts 0 hj]
      have h1 := ih (by omega)
      have h2 := hlen_for (verts[j]'hj)
      omega
  have hoff : cloudOff verts G X i ≤ 2 * (G.inside X).length := cloudOff_le_two_mul_e hnd G hi
  omega

/-- Edge-count bound for `portGraph cloud G X`: `m ≤ 10 * e`. -/
lemma portGraph_cloud_m_le (G : Graph) (X : Finset ℕ) :
    (portGraph cloud G X).m ≤ 10 * (G.inside X).length :=
  portGraph_m_le isCloudExpander_cloud G X

/-! ## 2. Registers, Workspace Layout, and Procedures (`NoRand`) -/

def pgK : ℕ := 0
def pgVerts : ℕ := 1
def pgE : ℕ := 2
def pgEdges : ℕ := 3
def pgLoc : ℕ := 4
def pgOutOwner : ℕ := 5
def pgOutGraph : ℕ := 6
def pgWork : ℕ := 7
def pgH : ℕ := 8
def pgOff : ℕ := 9
def pgCur : ℕ := 10
def pgPorts : ℕ := 11
def pgCloudBuf : ℕ := 12
def pgI : ℕ := 13
def pgU : ℕ := 14
def pgV : ℕ := 15
def pgTmp1 : ℕ := 16
def pgTmp2 : ℕ := 17
def pgCM : ℕ := 18
def pgJ : ℕ := 19
def pgOutM : ℕ := 20
def pgHCur : ℕ := 21
def pgPA : ℕ := 22
def pgPB : ℕ := 23

/-- Contiguous scratch workspace size inside `workAddr`: `2 * k + 20 * e + 4`. -/
def portGraphWorkSpace (k e : ℕ) : ℕ :=
  2 * k + 20 * e + 4

/-- Setup derived workspace addresses `r9..r12`. -/
def pgSetupStmt : Stmt :=
  seqStmts [
    .assign pgOff (.bin .add (.reg pgWork) (.const 1)),
    .assign pgCur (.bin .add (.bin .add (.reg pgOff) (.reg pgK)) (.const 1)),
    .assign pgPorts (.bin .add (.reg pgCur) (.reg pgK)),
    .assign pgCloudBuf (.bin .add (.reg pgPorts) (.bin .mul (.const 2) (.reg pgE)))
  ]

/-- Stage 1: populate `locAddr[verts[i]] := i + 1` and zero `curAddr[i] := 0`. -/
def pgInitLocStmt : Stmt :=
  forRange pgI (.const 0) (.reg pgK) (
    seqStmts [
      .assign pgU (.load (.bin .add (.reg pgVerts) (.reg pgI))),
      .store (.bin .add (.reg pgLoc) (.reg pgU)) (.bin .add (.reg pgI) (.const 1)),
      .store (.bin .add (.reg pgCur) (.reg pgI)) (.const 0)
    ]
  )

/-- Stage 2: scan `inEdges`, write `portOwner` and `origPortEdges e`, and count cloud degrees. -/
def pgOrigAndDegStmt : Stmt :=
  forRange pgI (.const 0) (.reg pgE) (
    seqStmts [
      .assign pgU (.load (.bin .add (.reg pgEdges) (.bin .mul (.const 2) (.reg pgI)))),
      .assign pgV (.load (.bin .add (.bin .add (.reg pgEdges) (.bin .mul (.const 2) (.reg pgI))) (.const 1))),
      .store (.bin .add (.reg pgOutOwner) (.bin .mul (.const 2) (.reg pgI))) (.reg pgU),
      .store (.bin .add (.bin .add (.reg pgOutOwner) (.bin .mul (.const 2) (.reg pgI))) (.const 1)) (.reg pgV),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 2)) (.bin .mul (.const 2) (.reg pgI)))
        (.bin .mul (.const 2) (.reg pgI)),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 3)) (.bin .mul (.const 2) (.reg pgI)))
        (.bin .add (.bin .mul (.const 2) (.reg pgI)) (.const 1)),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgU))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1)),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgV))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1))
    ]
  )

/-- Stage 3: prefix sum of cloud sizes into `offAddr[0..k]` and initialize `curAddr[i] := off[i]`. -/
def pgPrefixSumStmt : Stmt :=
  seqStmts [
    .store (.reg pgOff) (.const 0),
    .assign pgTmp1 (.const 0),
    forRange pgI (.const 0) (.reg pgK) (
      seqStmts [
        .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgI))),
        .store (.bin .add (.reg pgCur) (.reg pgI)) (.reg pgTmp1),
        .assign pgTmp1 (.bin .add (.reg pgTmp1) (.reg pgTmp2)),
        .store (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)) (.reg pgTmp1)
      ]
    )
  ]

/-- Stage 4: scatter ports `p = 0 .. 2 * e - 1` into `portsAddr` in increasing order per cloud. -/
def pgScatterPortsStmt : Stmt :=
  forRange pgI (.const 0) (.bin .mul (.const 2) (.reg pgE)) (
    seqStmts [
      .assign pgV (.load (.bin .add (.reg pgOutOwner) (.reg pgI))),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgV))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgPorts) (.reg pgTmp2)) (.reg pgI),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1))
    ]
  )

/-- Inner loop of Stage 5: map `cm = r18` cloud expander edges from `cloudBufAddr + 2` through
`portsAddr + sStart` (`sStart = r16`) into `outGraphAddr + 2 + 2 * outM`. -/
def pgMapCloudEdgesStmt : Stmt :=
  forRange pgJ (.const 0) (.reg pgCM) (
    seqStmts [
      .assign pgU (.load (.bin .add (.bin .add (.reg pgCloudBuf) (.const 2)) (.bin .mul (.const 2) (.reg pgJ)))),
      .assign pgV (.load (.bin .add (.bin .add (.reg pgCloudBuf) (.const 3)) (.bin .mul (.const 2) (.reg pgJ)))),
      .assign pgPA (.load (.bin .add (.bin .add (.reg pgPorts) (.reg pgTmp1)) (.reg pgU))),
      .assign pgPB (.load (.bin .add (.bin .add (.reg pgPorts) (.reg pgTmp1)) (.reg pgV))),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 2)) (.bin .mul (.const 2) (.reg pgOutM))) (.reg pgPA),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 3)) (.bin .mul (.const 2) (.reg pgOutM))) (.reg pgPB),
      .assign pgOutM (.bin .add (.reg pgOutM) (.const 1))
    ]
  )

/-- Stage 5: for each vertex `i < k`, if cloud size `s ≥ 2`, call `cloudExpanderEntry` at `b + 1`
and append its mapped edges to `outGraphAddr`. -/
def pgCloudLoopStmt (b : ℕ) : Stmt :=
  seqStmts [
    .assign pgOutM (.reg pgE),
    .assign pgHCur (.reg pgH),
    .assign pgI (.const 0),
    .loop (.bin .lt (.reg pgI) (.reg pgK)) (
      seqStmts [
        .assign pgTmp1 (.load (.bin .add (.reg pgOff) (.reg pgI))),
        .assign pgTmp2 (.bin .sub
          (.load (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)))
          (.reg pgTmp1)),
        .cond (.bin .lt (.const 1) (.reg pgTmp2))
          (seqStmts [
            .store (.reg pgWork) (.reg pgTmp2),
            .call pgHCur (b + 1) [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
            .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
            pgMapCloudEdgesStmt
          ])
          .nop,
        .assign pgI (.bin .add (.reg pgI) (.const 1))
      ]
    ),
    .store (.reg pgOutGraph) (.bin .mul (.const 2) (.reg pgE)),
    .store (.bin .add (.reg pgOutGraph) (.const 1)) (.reg pgOutM)
  ]

/-- Stage 6: restore `locAddr[verts[i]] := 0` for `i < k`. -/
def pgClearLocStmt : Stmt :=
  forRange pgI (.const 0) (.reg pgK) (
    seqStmts [
      .assign pgU (.load (.bin .add (.reg pgVerts) (.reg pgI))),
      .store (.bin .add (.reg pgLoc) (.reg pgU)) (.const 0)
    ]
  )

/-- Entry procedure for building `portGraph cloud G X` and `portOwner G X`.
Arguments: `[k, vertsAddr, e, edgesAddr, locAddr, outOwnerAddr, outGraphAddr, workAddr, h]`. -/
def portGraphEntry (b : ℕ) : Stmt :=
  seqStmts [
    pgSetupStmt,
    pgInitLocStmt,
    pgOrigAndDegStmt,
    pgPrefixSumStmt,
    pgScatterPortsStmt,
    pgCloudLoopStmt b,
    pgClearLocStmt,
    .ret (.reg pgHCur)
  ]

/-- Self-contained procedure module for `portGraphEntry` plus `cloudExpanderProcs (b + 1)`. -/
def portGraphProcs (b : ℕ) : List Stmt :=
  portGraphEntry b :: cloudExpanderProcs (b + 1)

lemma portGraphEntry_noRand (b : ℕ) : (portGraphEntry b).NoRand := by
  simp [portGraphEntry, pgSetupStmt, pgInitLocStmt, pgOrigAndDegStmt, pgPrefixSumStmt,
    pgScatterPortsStmt, pgCloudLoopStmt, pgMapCloudEdgesStmt, pgClearLocStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

theorem portGraphProcs_noRand (b : ℕ) : ∀ s ∈ portGraphProcs b, s.NoRand := by
  intro s hs
  simp only [portGraphProcs, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact portGraphEntry_noRand b
  · exact cloudExpanderProcs_noRand (b + 1) s hs

/-! ## 3. Register Invariant, Memory Constraints, Setup, Stage 1, and Stage 6 -/

/-- Persistent register invariant `r0..r12` after `pgSetupStmt`. -/
structure PgRegs (k vertsAddr e edgesAddr locAddr outOwnerAddr outGraphAddr workAddr h : ℕ)
    (st : State) : Prop where
  r_k : st.regs pgK = k
  r_verts : st.regs pgVerts = vertsAddr
  r_e : st.regs pgE = e
  r_edges : st.regs pgEdges = edgesAddr
  r_loc : st.regs pgLoc = locAddr
  r_outOwner : st.regs pgOutOwner = outOwnerAddr
  r_outGraph : st.regs pgOutGraph = outGraphAddr
  r_work : st.regs pgWork = workAddr
  r_h : st.regs pgH = h
  r_off : st.regs pgOff = workAddr + 1
  r_cur : st.regs pgCur = workAddr + k + 2
  r_ports : st.regs pgPorts = workAddr + 2 * k + 2
  r_cloudBuf : st.regs pgCloudBuf = workAddr + 2 * k + 2 + 2 * e

lemma pgRegs_update_ge {k va e ea la oa ga wa h r val : ℕ} {st : State}
    (hr : 13 ≤ r) (hR : PgRegs k va e ea la oa ga wa h st) :
    PgRegs k va e ea la oa ga wa h { st with regs := Function.update st.regs r val } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by unfold pgK; omega)]; exact hR.r_k,
   by dsimp only; rw [Function.update_of_ne (by unfold pgVerts; omega)]; exact hR.r_verts,
   by dsimp only; rw [Function.update_of_ne (by unfold pgE; omega)]; exact hR.r_e,
   by dsimp only; rw [Function.update_of_ne (by unfold pgEdges; omega)]; exact hR.r_edges,
   by dsimp only; rw [Function.update_of_ne (by unfold pgLoc; omega)]; exact hR.r_loc,
   by dsimp only; rw [Function.update_of_ne (by unfold pgOutOwner; omega)]; exact hR.r_outOwner,
   by dsimp only; rw [Function.update_of_ne (by unfold pgOutGraph; omega)]; exact hR.r_outGraph,
   by dsimp only; rw [Function.update_of_ne (by unfold pgWork; omega)]; exact hR.r_work,
   by dsimp only; rw [Function.update_of_ne (by unfold pgH; omega)]; exact hR.r_h,
   by dsimp only; rw [Function.update_of_ne (by unfold pgOff; omega)]; exact hR.r_off,
   by dsimp only; rw [Function.update_of_ne (by unfold pgCur; omega)]; exact hR.r_cur,
   by dsimp only; rw [Function.update_of_ne (by unfold pgPorts; omega)]; exact hR.r_ports,
   by dsimp only; rw [Function.update_of_ne (by unfold pgCloudBuf; omega)]; exact hR.r_cloudBuf⟩

lemma pgRegs_update_mem {k va e ea la oa ga wa h a val : ℕ} {st : State}
    (hR : PgRegs k va e ea la oa ga wa h st) :
    PgRegs k va e ea la oa ga wa h { st with mem := Function.update st.mem a val } :=
  ⟨hR.r_k, hR.r_verts, hR.r_e, hR.r_edges, hR.r_loc, hR.r_outOwner, hR.r_outGraph, hR.r_work,
   hR.r_h, hR.r_off, hR.r_cur, hR.r_ports, hR.r_cloudBuf⟩

/-- Word-size and below-heap layout bounds for `portGraphEntry`. -/
def PortGraphBounds (w n k e vertsAddr edgesAddr locAddr outOwnerAddr outGraphAddr workAddr h : ℕ) :
    Prop :=
  vertsAddr + k ≤ h ∧
  edgesAddr + 2 * e ≤ h ∧
  locAddr + n ≤ h ∧
  outOwnerAddr + 2 * e ≤ h ∧
  outGraphAddr + 2 + 20 * e ≤ h ∧
  workAddr + portGraphWorkSpace k e ≤ h ∧
  h + portGraphHeapSpace e ≤ 2 ^ w ∧
  16 < 2 ^ w

/-- Pairwise disjointness of mutable buffers from each other and from read buffers. -/
def PortGraphDisjoint (n k e vertsAddr edgesAddr locAddr outOwnerAddr outGraphAddr workAddr : ℕ) :
    Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n edgesAddr (2 * e) ∧
  DisjointRange locAddr n outOwnerAddr (2 * e) ∧
  DisjointRange locAddr n outGraphAddr (2 + 20 * e) ∧
  DisjointRange locAddr n workAddr (portGraphWorkSpace k e) ∧
  DisjointRange outOwnerAddr (2 * e) vertsAddr k ∧
  DisjointRange outOwnerAddr (2 * e) edgesAddr (2 * e) ∧
  DisjointRange outOwnerAddr (2 * e) outGraphAddr (2 + 20 * e) ∧
  DisjointRange outOwnerAddr (2 * e) workAddr (portGraphWorkSpace k e) ∧
  DisjointRange outGraphAddr (2 + 20 * e) vertsAddr k ∧
  DisjointRange outGraphAddr (2 + 20 * e) edgesAddr (2 * e) ∧
  DisjointRange outGraphAddr (2 + 20 * e) workAddr (portGraphWorkSpace k e) ∧
  DisjointRange workAddr (portGraphWorkSpace k e) vertsAddr k ∧
  DisjointRange workAddr (portGraphWorkSpace k e) edgesAddr (2 * e)

/-- Setup triple: computes `r9..r12` from `startState`. -/
lemma pgSetup_triple {w n k e va ea la oa ga wa h : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h) :
    Triple w p
      (fun st => st = startState [k, va, e, ea, la, oa, ga, wa, h] mem pos)
      pgSetupStmt
      (normalPost fun st' => PgRegs k va e ea la oa ga wa h st' ∧ st'.mem = mem ∧ st'.pos = pos)
      (fun _ => 40) := by
  rcases hb with ⟨_, _, _, _, _, hws, hhw, hw16⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  intro st ω hst; subst hst
  refine runs_start_le ?_
  dsimp only [pgSetupStmt, seqStmts]
  refine runs_seq_assign_le (v := wa + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := wa) (by simp [startState, pgWork]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := wa + k + 2)
    (Expr.eval_eq_of_eq
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (v := wa + 1) (by simp [pgOff]))
          (Expr.eval_reg_of_eq (v := k) (by simp [startState, pgK, pgOff])) (by omega))
        (Expr.eval_const (by omega)) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := wa + 2 * k + 2)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (v := wa + k + 2) (by simp [pgCur]))
        (Expr.eval_reg_of_eq (v := k) (by simp [startState, pgK, pgOff, pgCur])) (by omega))
      (by omega)) ?_
  refine runs_assign_le (v := wa + 2 * k + 2 + 2 * e)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := wa + 2 * k + 2) (by simp [pgPorts]))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (v := e) (by simp [startState, pgE, pgOff, pgCur, pgPorts])) (by omega))
      (by omega)) ?_ (by simp [Expr.size])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  all_goals simp [startState, pgK, pgVerts, pgE, pgEdges, pgLoc, pgOutOwner, pgOutGraph, pgWork,
    pgH, pgOff, pgCur, pgPorts, pgCloudBuf]

/-- Stage 1 triple: sets `locAddr[verts[i]] := i + 1` and zeroes `curAddr[i] := 0`. -/
lemma pgInitLoc_triple {w n k e va ea la oa ga wa h : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem va verts)
    (hloc0 : ∀ u < n, mem (la + u) = 0)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd : PortGraphDisjoint n k e va ea la oa ga wa)
    (hregs : PgRegs k va e ea la oa ga wa h st₀) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) pgInitLocStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧ st'.pos = st₀.pos ∧
        PreservedOutside2 mem st'.mem la (la + n) (wa + k + 2) (wa + 2 * k + 2) ∧
        (∀ u < n, st'.mem (la + u) = if u ∈ verts then verts.idxOf u + 1 else 0) ∧
        (∀ i < k, st'.mem (wa + k + 2 + i) = 0))
      (fun _ => 50 * k + 20) := by
  rcases hb with ⟨hva_h, _, hla_h, _, _, hws_h, hhw, hw16⟩
  rcases hd with ⟨hd_lv, _, _, _, hd_lw, _, _, _, _, _, _, _, hd_wv, _⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let curAddr := wa + k + 2
  let Inv : ℕ → State → Prop := fun i st =>
    PgRegs k va e ea la oa ga wa h st ∧ st.regs pgI = i ∧ st.pos = st₀.pos ∧
    PreservedOutside2 mem st.mem la (la + n) curAddr (curAddr + k) ∧
    (∀ u < n, st.mem (la + u) = if u ∈ verts.take i then verts.idxOf u + 1 else 0) ∧
    (∀ j < i, st.mem (curAddr + j) = 0)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgI) (lo := .const 0) (hi := .reg pgK)
    (body := seqStmts [
      .assign pgU (.load (.bin .add (.reg pgVerts) (.reg pgI))),
      .store (.bin .add (.reg pgLoc) (.reg pgU)) (.bin .add (.reg pgI) (.const 1)),
      .store (.bin .add (.reg pgCur) (.reg pgI)) (.const 0)])
    (P := fun st => st = st₀) (Inv := Inv) 36 0 k (Nat.zero_le k) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), pgRegs_update_ge (r := pgI) (by decide) hregs,
        by simp, rfl, fun a _ _ => by simp [hmem], fun u hu => by simp [hmem, hloc0 u hu],
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hpr, hmap, hzero⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (va + i) = verts[i]'hi_lt := by
        rw [hpr (va + i)
          (disjointRange_outside hd_lv (by omega) (by omega))
          (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega)]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_seq_store_le (x := la + verts[i]'hi_lt) (v := i + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := la) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := i) (by dsimp only; rw [Function.update_of_ne (by decide), hi]))
          (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_store_le (x := curAddr + i) (v := 0)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curAddr) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_cur]))
          (Expr.eval_reg_of_eq (v := i) (by dsimp only; rw [Function.update_of_ne (by decide), hi])) (by omega))
        (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_mem (pgRegs_update_mem (pgRegs_update_ge (r := pgU) (by decide) hr))),
        by simp, hpos, ?_, ?_, ?_⟩, by dsimp only; rw [Function.update_of_ne (by decide), hi]⟩
      · intro a hal hac
        dsimp only
        rw [Function.update_of_ne (by rcases hac with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hal with h1 | h1 <;> omega)]
        exact hpr a hal hac
      · intro u hu
        dsimp only
        have hne : la + u ≠ curAddr + i := by rcases hd_lw with h1 | h1 <;> omega
        rw [Function.update_of_ne hne]
        by_cases huv : u = verts[i]'hi_lt
        · subst huv
          have hidx : verts.idxOf (verts[i]'hi_lt) = i := by
            have hlt := List.idxOf_lt_length_of_mem (List.getElem_mem hi_lt)
            exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hlt)
          rw [List.take_succ_eq_append_getElem hi_lt]
          simp only [Function.update_self, List.mem_append, List.mem_singleton, or_true, ↓reduceIte, hidx]
        · rw [Function.update_of_ne (by omega), List.take_succ_eq_append_getElem hi_lt]
          simp only [List.mem_append, List.mem_singleton, huv, or_false]
          exact hmap u hu
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · have hne : curAddr + j ≠ la + verts[i]'hi_lt := by rcases hd_lw with h1 | h1 <;> omega
          rw [Function.update_of_ne (by omega), Function.update_of_ne hne]
          exact hzero j (by omega))
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hpr, hmap, hzero⟩
    refine ⟨hr, hpos, ?_, fun u hu => ?_, hzero⟩
    · intro a hal hac
      exact hpr a hal (by rcases hac with h1 | h1 <;> [left; right] <;> omega)
    · have := hmap u hu
      rwa [← hvlen, List.take_length] at this
  · exact False.elim hq

/-- Stage 6 triple: restores `locAddr[verts[i]] := 0` for all `i < k`. -/
lemma pgClearLoc_triple {w n k e va ea la oa ga wa h hCur : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem va verts)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd_lv : DisjointRange la n va k)
    (hregs : PgRegs k va e ea la oa ga wa h st₀)
    (hhcur : st₀.regs pgHCur = hCur) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) pgClearLocStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧ st'.regs pgHCur = hCur ∧ st'.pos = st₀.pos ∧
        MemFrame mem st'.mem la (la + n) ∧
        (∀ a, (∀ u ∈ verts, a ≠ la + u) → st'.mem a = mem a) ∧
        (∀ u ∈ verts, st'.mem (la + u) = 0))
      (fun _ => 36 * k + 15) := by
  rcases hb with ⟨hva_h, _, hla_h, _, _, _, hhw, hw16⟩
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let Inv : ℕ → State → Prop := fun i st =>
    PgRegs k va e ea la oa ga wa h st ∧ st.regs pgI = i ∧ st.regs pgHCur = hCur ∧
    st.pos = st₀.pos ∧ MemFrame mem st.mem la (la + n) ∧
    (∀ a, (∀ u ∈ verts, a ≠ la + u) → st.mem a = mem a) ∧
    (∀ j < i, ∀ (hj : j < verts.length), st.mem (la + verts[j]'hj) = 0)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgI) (lo := .const 0) (hi := .reg pgK)
    (body := seqStmts [
      .assign pgU (.load (.bin .add (.reg pgVerts) (.reg pgI))),
      .store (.bin .add (.reg pgLoc) (.reg pgU)) (.const 0)])
    (P := fun st => st = st₀) (Inv := Inv) 22 0 k (Nat.zero_le k) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), pgRegs_update_ge (r := pgI) (by decide) hregs,
        by simp, by dsimp only; rw [Function.update_of_ne (by decide), hhcur], rfl,
        hmem ▸ memFrame_refl _ _ _, fun a _ => by simp [hmem],
        fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hhcur', hpos, hfr, hpt, hclr⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (va + i) = verts[i]'hi_lt := by
        rw [hfr (va + i) (disjointRange_outside hd_lv (by omega) (by omega))]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_store_le (x := la + verts[i]'hi_lt) (v := 0)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := la) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_mem (pgRegs_update_ge (r := pgU) (by decide) hr)),
        by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hhcur'],
        hpos,
        memFrame_trans hfr (memFrame_update (by omega) (by omega)),
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (ha _ (List.getElem_mem hi_lt))]
          exact hpt a ha, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), hi]⟩
      intro j hj hjk
      dsimp only
      by_cases hji : verts[j]'hjk = verts[i]'hi_lt
      · rw [hji]; simp
      · have hne : j ≠ i := fun h1 => hji (by subst h1; rfl)
        rw [Function.update_of_ne (by omega)]
        exact hclr j (by omega) hjk)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hhcur', hpos, hfr, hpt, hclr⟩
    refine ⟨hr, hhcur', hpos, hfr, hpt, fun u hu => ?_⟩
    rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
    exact hclr j (hvlen ▸ hj) hj
  · exact False.elim hq

end MinCostFlow.ExpanderDecomp
