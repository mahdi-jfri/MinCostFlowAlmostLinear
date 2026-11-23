module

public import WordRAM.Logic
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift

/-!
# Deterministic Word-RAM Component & Subgraph Preparation (`ProgWitnessPrep`)

Implements Phase A + Phase B of `buildWitness` as a deterministic (`Stmt.NoRand`) Word-RAM module:
1. Buckets `J0_strip` edges by decomposition level `0..d_ℓ` in `O(J0_strip.m + 1)` time using a
   downward scan (`b = m0 - 1` down to `0`) so each bucket list `lvlHead[i]` preserves strictly
   increasing edge-index order (`DecomposeOutput.edgesAt J0_strip i`).
2. Extracts `j0Edges` directly from `lvlHead[0]`.
3. Parses `rawComps` metadata into a `7`-word-per-component table (`compsRec`) and processes each
   non-empty level block `[ciStart, ciEnd)` in `O(|block| + |edgesAt lvl| + ∑_{c ∈ block} |c.X|)`
   time using vertex-stamp arrays `vertComp`/`vertLoc` (cleared per block without `O(J.n)` re-zeroing),
   building exact `GraphAt mem' jSubPtr c.J_sub`, `ListAt mem' jOrigPtr c.jSubOrigEdges`, and
   degree tables `[c.J_sub.deg 0, ..., c.J_sub.deg (c.X.card - 1)]`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. Pure Chain, Component-Block & Subgraph Helpers -/

/-- Edges of `G` at level `lvl` starting from index `idx`. -/
def edgesAtFrom (level : List ℕ) (m0 lvl idx : ℕ) : List ℕ :=
  ((List.range m0).drop idx).filter fun b => decide (level.getD b 0 = lvl)

theorem edgesAtFrom_m0 (level : List ℕ) (m0 lvl : ℕ) :
    edgesAtFrom level m0 lvl m0 = [] := by
  have h : (List.range m0).drop m0 = [] := List.drop_eq_nil_iff.mpr (by simp)
  simp [edgesAtFrom, h]

theorem edgesAtFrom_zero_eq (J0 : Graph) (d : DecomposeOutput)
    (hlevel : ∀ j < J0.m, ((List.range J0.m).map d.level).getD j 0 = d.level j) (lvl : ℕ) :
    edgesAtFrom ((List.range J0.m).map d.level) J0.m lvl 0 = d.edgesAt J0 lvl := by
  simp only [edgesAtFrom, List.drop_zero, DecomposeOutput.edgesAt]
  refine List.filter_congr fun b hb => ?_
  rw [hlevel b (List.mem_range.mp hb)]

theorem edgesAtFrom_step_match {level : List ℕ} {m0 lvl b : ℕ} (hb : b < m0)
    (hl : level.getD b 0 = lvl) :
    edgesAtFrom level m0 lvl b = b :: edgesAtFrom level m0 lvl (b + 1) := by
  have hd : (List.range m0).drop b = b :: (List.range m0).drop (b + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hb), List.getElem_range]
  simp only [edgesAtFrom, hd, List.filter_cons, hl, decide_true, ↓reduceIte]

theorem edgesAtFrom_step_ne {level : List ℕ} {m0 lvl b : ℕ} (hb : b < m0)
    (hl : level.getD b 0 ≠ lvl) :
    edgesAtFrom level m0 lvl b = edgesAtFrom level m0 lvl (b + 1) := by
  have hd : (List.range m0).drop b = b :: (List.range m0).drop (b + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hb), List.getElem_range]
  simp only [edgesAtFrom, hd, List.filter_cons, decide_eq_true_eq, hl, ↓reduceIte]

/-- Linked-list chain predicate for `b` nodes (`1`-based pointers, `0` = nil) in `edgeNext`. -/
def ChainAt (mem : ℕ → ℕ) (aNext ptr : ℕ) : List ℕ → Prop
  | [] => ptr = 0
  | b :: bs => ptr = b + 1 ∧ ChainAt mem aNext (mem (aNext + b)) bs

theorem chainAt_of_agree {mem' mem : ℕ → ℕ} {aNext ptr : ℕ} {xs : List ℕ}
    (hch : ChainAt mem aNext ptr xs)
    (hag : ∀ b ∈ xs, mem' (aNext + b) = mem (aNext + b)) :
    ChainAt mem' aNext ptr xs := by
  induction xs generalizing ptr with
  | nil => exact hch
  | cons x xs ih =>
    rcases hch with ⟨rfl, htail⟩
    exact ⟨rfl, hag x List.mem_cons_self ▸
      ih htail (fun b hb => hag b (List.mem_cons_of_mem x hb))⟩

theorem edgesAtFrom_ge {level : List ℕ} {m0 lvl idx b : ℕ}
    (hb : b ∈ edgesAtFrom level m0 lvl idx) : idx ≤ b ∧ b < m0 := by
  simp only [edgesAtFrom, List.mem_filter, decide_eq_true_eq] at hb
  rcases List.mem_iff_getElem.mp hb.1 with ⟨k, hk, hkeq⟩
  rw [List.length_drop, List.length_range] at hk
  rw [List.getElem_drop, List.getElem_range] at hkeq
  omega

/-- Contiguous level-block partition of sorted `rawComps`.
Returns `(startIdx, lvl, block)` tuples covering `rawComps` left-to-right. -/
def compBlocksAux (idx : ℕ) : List (ℕ × List ℕ) → List (ℕ × ℕ × List (ℕ × List ℕ))
  | [] => []
  | c :: rest =>
    let tailSame := rest.takeWhile (fun p => decide (p.1 = c.1))
    let block := c :: tailSame
    let rem := rest.dropWhile (fun p => decide (p.1 = c.1))
    (idx, c.1, block) :: compBlocksAux (idx + block.length) rem
termination_by xs => xs.length
decreasing_by
  have hle : (rest.dropWhile (fun p => decide (p.1 = c.1))).length ≤ rest.length :=
    (List.dropWhile_suffix _).sublist.length_le
  simp only [List.length_cons]
  omega

private theorem mem_takeWhile_true {α : Type*} (p : α → Bool) :
    ∀ (l : List α) {x : α}, x ∈ l.takeWhile p → p x = true
  | [], _, hx => by simp at hx
  | a :: as, x, hx => by
    rw [List.takeWhile_cons] at hx
    split_ifs at hx with hpa
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpa
      · exact mem_takeWhile_true p as hx'
    · simp at hx

theorem compBlocksAux_takeWhile_spec (c : ℕ × List ℕ) (rest : List (ℕ × List ℕ))
    (hpw : List.Pairwise (fun a b => a.1 ≤ b.1) (c :: rest)) :
    let p : (ℕ × List ℕ) → Bool := fun q => decide (q.1 = c.1)
    let tailSame := rest.takeWhile p
    let rem := rest.dropWhile p
    (∀ q ∈ tailSame, q.1 = c.1) ∧
      (∀ q ∈ rem, c.1 < q.1) ∧
      (rem = [] ∨ ∃ q rem', rem = q :: rem' ∧ c.1 < q.1) ∧
      c :: rest = (c :: tailSame) ++ rem := by
  intro p tailSame rem
  have hsplit : tailSame ++ rem = rest := List.takeWhile_append_dropWhile
  have htail_eq : ∀ q ∈ tailSame, q.1 = c.1 := fun q hq =>
    of_decide_eq_true (mem_takeWhile_true p rest hq)
  have hrem_gt : ∀ q ∈ rem, c.1 < q.1 := by
    cases hdw : rem with
    | nil => intro q hq; simp at hq
    | cons hd tl =>
      have hne_nil : rest.dropWhile p ≠ [] := by
        change rem ≠ []; rw [hdw]; simp
      have hnot : p ((rest.dropWhile p).head hne_nil) = false :=
        List.head_dropWhile_not p hne_nil
      have hhd_eq : (rest.dropWhile p).head hne_nil = hd := by
        simp [rem] at hdw; simp [hdw]
      rw [hhd_eq] at hnot
      have hne : hd.1 ≠ c.1 := fun heq => by simp [p, heq] at hnot
      have hpw_c := (List.pairwise_cons.mp hpw).1
      have hmem_hd : hd ∈ rest := (List.dropWhile_suffix p).subset (by simp [rem, hdw])
      have hlt_hd : c.1 < hd.1 := Nat.lt_of_le_of_ne (hpw_c hd hmem_hd) hne.symm
      have hpw_rest := (List.pairwise_cons.mp hpw).2
      have hsub : List.Pairwise (fun a b => a.1 ≤ b.1) rem :=
        List.Pairwise.sublist (List.dropWhile_suffix p).sublist hpw_rest
      rw [hdw] at hsub
      have hpw_tl := (List.pairwise_cons.mp hsub).1
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hqtl
      · exact hlt_hd
      · exact lt_of_lt_of_le hlt_hd (hpw_tl q hqtl)
  refine ⟨htail_eq, hrem_gt, ?_, ?_⟩
  · cases hdw : rem with
    | nil => left; rfl
    | cons hd tl => right; exact ⟨hd, tl, rfl, hrem_gt hd (by simp [hdw])⟩
  · exact congrArg (c :: ·) hsplit.symm

theorem compBlocksAux_props (idx : ℕ) (xs : List (ℕ × List ℕ))
    (hpw : List.Pairwise (fun a b => a.1 ≤ b.1) xs) :
    (compBlocksAux idx xs).Pairwise (fun a b => a.2.1 < b.2.1) ∧
      ((compBlocksAux idx xs).map fun b => b.2.2.length).sum = xs.length ∧
      ((compBlocksAux idx xs).flatMap fun b => b.2.2) = xs ∧
      (∀ b ∈ compBlocksAux idx xs, 0 < b.2.2.length ∧ ∀ c ∈ b.2.2, c.1 = b.2.1) := by
  induction hlen : xs.length using Nat.strongRecOn generalizing idx xs with
  | ind n ih =>
    cases xs with
    | nil => subst hlen; simp [compBlocksAux]
    | cons c rest =>
      rcases compBlocksAux_takeWhile_spec c rest hpw with ⟨htail, hrem_gt, _, hsplit⟩
      set p : (ℕ × List ℕ) → Bool := fun q => decide (q.1 = c.1)
      set tailSame := rest.takeWhile p
      set rem := rest.dropWhile p
      have hrem_len : rem.length < (c :: rest).length := by
        have hle : rem.length ≤ rest.length := (List.dropWhile_suffix p).sublist.length_le
        simp only [List.length_cons]
        omega
      have hpw_rem : List.Pairwise (fun a b => a.1 ≤ b.1) rem :=
        (List.pairwise_append.mp (hsplit ▸ hpw)).2.1
      rcases ih rem.length (hlen ▸ hrem_len) (idx + (c :: tailSame).length) rem hpw_rem rfl with
        ⟨ih_pw, ih_sum, ih_flat, ih_mem⟩
      rw [compBlocksAux.eq_2, ← hlen]
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, ih_pw⟩
        have hb0 := ih_mem b hb
        cases hbl : b.2.2 with
        | nil => simp [hbl] at hb0
        | cons hd tl =>
          have hfirst_in : hd ∈ (compBlocksAux (idx + (c :: tailSame).length) rem).flatMap
              (fun b => b.2.2) :=
            List.mem_flatMap.mpr ⟨b, hb, by simp [hbl]⟩
          rw [ih_flat] at hfirst_in
          have heq1 : hd.1 = b.2.1 := hb0.2 hd (by simp [hbl])
          rw [← heq1]
          exact hrem_gt hd hfirst_in
      · rw [ih_sum]
        have hlen_split := congrArg List.length hsplit
        simp only [List.length_append] at hlen_split
        change (c :: tailSame).length + rem.length = (c :: rest).length
        simp only [List.length_cons] at hlen_split ⊢
        omega
      · rw [ih_flat]
        exact hsplit.symm
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · refine ⟨Nat.zero_lt_succ _, fun q hq => ?_⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · rfl
          · exact htail q hq
        · exact ih_mem b hb

theorem compBlocksAux_getElem (idx : ℕ) (xs : List (ℕ × List ℕ))
    (hpw : List.Pairwise (fun a b => a.1 ≤ b.1) xs) :
    ∀ b ∈ compBlocksAux idx xs,
      idx ≤ b.1 ∧
      b.1 + b.2.2.length ≤ idx + xs.length ∧
      (∀ k < b.2.2.length, xs[b.1 - idx + k]? = b.2.2[k]?) ∧
      (b.1 + b.2.2.length < idx + xs.length →
        ∃ q, xs[b.1 - idx + b.2.2.length]? = some q ∧ b.2.1 < q.1) := by
  induction hlen : xs.length using Nat.strongRecOn generalizing idx xs with
  | ind n ih =>
    cases xs with
    | nil => subst hlen; simp [compBlocksAux]
    | cons c rest =>
      rcases compBlocksAux_takeWhile_spec c rest hpw with ⟨htail, hrem_gt, hrem_cases, hsplit⟩
      set p : (ℕ × List ℕ) → Bool := fun q => decide (q.1 = c.1)
      set tailSame := rest.takeWhile p
      set rem := rest.dropWhile p
      have hrem_len : rem.length < (c :: rest).length := by
        have hle : rem.length ≤ rest.length := (List.dropWhile_suffix p).sublist.length_le
        simp only [List.length_cons]
        omega
      have hpw_rem : List.Pairwise (fun a b => a.1 ≤ b.1) rem :=
        (List.pairwise_append.mp (hsplit ▸ hpw)).2.1
      have hrec := ih rem.length (hlen ▸ hrem_len) (idx + (c :: tailSame).length) rem hpw_rem rfl
      rw [compBlocksAux.eq_2, ← hlen]
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · refine ⟨le_rfl, ?_, ?_, ?_⟩
        · have hlen_split := congrArg List.length hsplit
          simp only [List.length_append] at hlen_split
          change idx + (c :: tailSame).length ≤ idx + (c :: rest).length
          dsimp only [tailSame] at hlen_split ⊢
          simp only [List.length_cons] at hlen_split ⊢
          omega
        · intro k hk
          dsimp only at hk ⊢
          simp only [Nat.sub_self, zero_add]
          rw [hsplit, List.getElem?_append_left hk]
        · intro hlt
          dsimp only at hlt ⊢
          have hlen_split := congrArg List.length hsplit
          simp only [List.length_append] at hlen_split
          have hpos : 0 < rem.length := by
            change idx + (c :: tailSame).length < idx + (c :: rest).length at hlt
            dsimp only [tailSame, rem] at hlen_split hlt ⊢
            simp only [List.length_cons] at hlen_split hlt
            omega
          rcases hrem_cases with hnil | ⟨hd, tl, hrem_cons, hgt⟩
          · simp [hnil] at hpos
          · refine ⟨hd, ?_, hgt⟩
            rw [Nat.sub_self, zero_add, hsplit, List.getElem?_append_right le_rfl]
            simp [hrem_cons]
      · rcases hrec b hb with ⟨hge, hle, hget, hnext⟩
        have hlen_split := congrArg List.length hsplit
        simp only [List.length_append] at hlen_split
        change idx ≤ b.1 ∧ b.1 + b.2.2.length ≤ idx + (c :: rest).length ∧
          (∀ k < b.2.2.length, (c :: rest)[b.1 - idx + k]? = b.2.2[k]?) ∧
          (b.1 + b.2.2.length < idx + (c :: rest).length →
            ∃ q, (c :: rest)[b.1 - idx + b.2.2.length]? = some q ∧ b.2.1 < q.1)
        refine ⟨by omega, ?_, ?_, ?_⟩
        · dsimp only [tailSame, rem] at hle hlen_split ⊢
          simp only [List.length_cons] at hle hlen_split ⊢
          omega
        · intro k hk
          have hk' := hget k hk
          have hoff : b.1 - idx + k = (c :: tailSame).length + (b.1 - (idx + (c :: tailSame).length) + k) := by omega
          rw [hoff, hsplit, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hk'
        · intro hlt
          have hoff : b.1 - idx + b.2.2.length =
              (c :: tailSame).length + (b.1 - (idx + (c :: tailSame).length) + b.2.2.length) := by omega
          rw [hoff, hsplit, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hnext (by
            dsimp only [tailSame, rem] at hlen_split hlt ⊢
            simp only [List.length_cons] at hlen_split hlt ⊢
            omega)

theorem edgesAt_inside_filter_eq {J0 : Graph} {d : DecomposeOutput} {lvl : ℕ}
    {X : Finset ℕ} (hiff : ∀ e ∈ (d.graphAt J0 lvl).edges, e.1 ∈ X ↔ e.2 ∈ X) :
    ((insideIndices (d.graphAt J0 lvl) X).map fun a => (d.edgesAt J0 lvl).getD a 0) =
      (d.edgesAt J0 lvl).filter (fun b => decide ((J0.edges.getD b (0, 0)).1 ∈ X)) := by
  set eds := d.edgesAt J0 lvl
  set Gi := d.graphAt J0 lvl
  have hm : Gi.m = eds.length := by dsimp only [Gi, eds]; simp [DecomposeOutput.graphAt, Graph.m]
  have h1 : ∀ a ∈ List.range eds.length,
      decide ((Gi.edges.getD a (0, 0)).1 ∈ X ∧ (Gi.edges.getD a (0, 0)).2 ∈ X) =
        decide ((J0.edges.getD (eds.getD a 0) (0, 0)).1 ∈ X) := by
    intro a ha
    have ha' : a < eds.length := List.mem_range.mp ha
    have ha_m : a < Gi.edges.length := by simpa [Gi, eds, DecomposeOutput.graphAt] using ha'
    have hedge : Gi.edges.getD a (0, 0) = J0.edges.getD (eds.getD a 0) (0, 0) := by
      simp only [Gi, eds, DecomposeOutput.graphAt]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ha'), List.getElem_map,
        List.getD_eq_getElem _ _ ha']
    have hmem : Gi.edges.getD a (0, 0) ∈ Gi.edges := by
      rw [List.getD_eq_getElem _ _ ha_m]; exact List.getElem_mem ha_m
    have hxy := hiff _ hmem
    rw [hedge] at hxy ⊢
    by_cases hx : (J0.edges.getD (eds.getD a 0) (0, 0)).1 ∈ X
    · simp only [hx, hxy.mp hx, and_self, decide_true]
    · simp only [hx, false_and, decide_false]
  have h2 : insideIndices Gi X =
      (List.range eds.length).filter (fun a => decide ((J0.edges.getD (eds.getD a 0) (0, 0)).1 ∈ X)) := by
    unfold insideIndices
    rw [hm]
    exact List.filter_congr h1
  change ((insideIndices Gi X).map fun a => eds.getD a 0) = _
  rw [h2]
  clear h1 h2 hm
  induction eds with
  | nil => simp
  | cons b bs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
    by_cases hx : (J0.edges.getD b (0, 0)).1 ∈ X
    · simp only [hx, decide_true, ↓reduceIte, List.map_cons]
      rw [List.filter_cons]
      simp only [hx, decide_true, ↓reduceIte]
      congr 1
      simpa [Function.comp_def] using ih
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_cons]
      simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      simpa [Function.comp_def] using ih

theorem inducedSubgraph_edges_eq_filter_map {J0 : Graph} {d : DecomposeOutput} {lvl : ℕ}
    {X : Finset ℕ} (hiff : ∀ e ∈ (d.graphAt J0 lvl).edges, e.1 ∈ X ↔ e.2 ∈ X) :
    (inducedSubgraph (d.graphAt J0 lvl) X).edges =
      ((d.edgesAt J0 lvl).filter (fun b => decide ((J0.edges.getD b (0, 0)).1 ∈ X))).map
        (fun b =>
          let e := J0.edges.getD b (0, 0)
          ((vertsOf X).idxOf e.1, (vertsOf X).idxOf e.2)) := by
  have hmap := edgesAt_inside_filter_eq hiff
  rw [← hmap, List.map_map]
  simp only [inducedSubgraph]
  refine List.map_congr_left fun a ha => ?_
  have ha' := (mem_insideIndices.mp ha).1
  have ha_ed : a < (d.edgesAt J0 lvl).length := by
    simpa [DecomposeOutput.graphAt, Graph.m] using ha'
  have hedge : (d.graphAt J0 lvl).edges.getD a (0, 0) =
      J0.edges.getD ((d.edgesAt J0 lvl).getD a 0) (0, 0) := by
    simp only [DecomposeOutput.graphAt]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ha_ed), List.getElem_map,
      List.getD_eq_getElem _ _ ha_ed]
  simp only [Function.comp_def, hedge]

theorem comp_jSubOrigEdges_eq_filter_map {J0 : Graph} {nlIdx : List ℕ} {d : DecomposeOutput}
    {lvl : ℕ} {X : Finset ℕ} (hiff : ∀ e ∈ (d.graphAt J0 lvl).edges, e.1 ∈ X ↔ e.2 ∈ X) :
    ((insideIndices (d.graphAt J0 lvl) X).map
        (fun a => nlIdx.getD ((d.edgesAt J0 lvl).getD a 0) 0)) =
      ((d.edgesAt J0 lvl).filter (fun b => decide ((J0.edges.getD b (0, 0)).1 ∈ X))).map
        (fun b => nlIdx.getD b 0) := by
  rw [← edgesAt_inside_filter_eq hiff, List.map_map]
  rfl

/-! ## 2. Word-RAM AST (`witnessPrepModule`) and `NoRand` -/

/-- Phase A initial setup: reads `n, m0, d_ℓ, numComps` and sets bucket/array base registers. -/
def prepInitStmt : Stmt :=
  Stmt.assign 5 (.load (.reg 0)) ;;
  Stmt.assign 6 (.load (.bin .add (.reg 1) (.const 1))) ;;
  Stmt.assign 7 (.load (.reg 3)) ;;
  Stmt.assign 8 (.load (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 6))) ;;
  Stmt.assign 9 (.bin .add (.reg 4) (.const 8)) ;;
  Stmt.assign 10 (.bin .add (.bin .add (.reg 9) (.reg 7)) (.const 1)) ;;
  Stmt.assign 11 (.bin .add (.reg 10) (.reg 6)) ;;
  Stmt.assign 12 (.const 0)

/-- Downward scan `b = m0 - 1` down to `0`, prepending `b + 1` into `lvlHead[level[b]]`. -/
def prepBucketBody : Stmt :=
  Stmt.assign 20 (.bin .sub (.reg 19) (.const 1)) ;;
  Stmt.assign 21 (.load (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 20))) ;;
  Stmt.assign 29 (.load (.bin .add (.reg 9) (.reg 21))) ;;
  Stmt.store (.bin .add (.reg 10) (.reg 20)) (.reg 29) ;;
  Stmt.store (.bin .add (.reg 9) (.reg 21)) (.reg 19) ;;
  Stmt.assign 19 (.reg 20)

def prepBucketStmt : Stmt :=
  Stmt.assign 19 (.reg 6) ;;
  Stmt.loop (.bin .lt (.const 0) (.reg 19)) prepBucketBody

/-- Traverse `lvlHead[0]` linked list to populate `j0Edges` (`j0Out[0..j0Len)`). -/
def prepJ0Body : Stmt :=
  Stmt.assign 20 (.bin .sub (.reg 29) (.const 1)) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
  Stmt.store (.bin .add (.reg 11) (.reg 12)) (.reg 21) ;;
  Stmt.assign 12 (.bin .add (.reg 12) (.const 1)) ;;
  Stmt.assign 29 (.load (.bin .add (.reg 10) (.reg 20)))

def prepJ0Stmt : Stmt :=
  Stmt.assign 29 (.load (.reg 9)) ;;
  Stmt.loop (.bin .lt (.const 0) (.reg 29)) prepJ0Body

/-- Compute `a_comps, a_vComp, a_vLoc, h_cur` and write the 8-word prep header `[h+0..h+7]`. -/
def prepHdrStoreStmt : Stmt :=
  Stmt.assign 13 (.bin .add (.reg 11) (.reg 12)) ;;
  Stmt.assign 14 (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 8))) ;;
  Stmt.assign 15 (.bin .add (.reg 14) (.reg 5)) ;;
  Stmt.assign 16 (.bin .add (.reg 15) (.reg 5)) ;;
  Stmt.store (.reg 4) (.reg 12) ;;
  Stmt.store (.bin .add (.reg 4) (.const 1)) (.reg 11) ;;
  Stmt.store (.bin .add (.reg 4) (.const 2)) (.reg 8) ;;
  Stmt.store (.bin .add (.reg 4) (.const 3)) (.reg 13) ;;
  Stmt.store (.bin .add (.reg 4) (.const 4)) (.reg 9) ;;
  Stmt.store (.bin .add (.reg 4) (.const 5)) (.reg 10) ;;
  Stmt.store (.bin .add (.reg 4) (.const 6)) (.reg 14) ;;
  Stmt.store (.bin .add (.reg 4) (.const 7)) (.reg 15) ;;
  Stmt.assign 18 (.bin .add (.bin .add (.reg 3) (.const 4)) (.reg 6)) ;;
  Stmt.assign 17 (.const 0)

/-- Parse `rawComps` into slots `0, 1, 2` (`level, card, vertsPtr`) of `compsRec`. -/
def prepParseBody : Stmt :=
  Stmt.assign 20 (.load (.reg 18)) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 18) (.const 1))) ;;
  Stmt.assign 30 (.bin .add (.reg 18) (.const 2)) ;;
  Stmt.assign 31 (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 17))) ;;
  Stmt.store (.reg 31) (.reg 20) ;;
  Stmt.store (.bin .add (.reg 31) (.const 1)) (.reg 21) ;;
  Stmt.store (.bin .add (.reg 31) (.const 2)) (.reg 30) ;;
  Stmt.assign 18 (.bin .add (.reg 30) (.reg 21))

def prepParseStmt : Stmt :=
  forUp 17 (.reg 8) prepParseBody

/-- Advance `ciEnd` (`r22`) over all contiguous components sharing level `r23`. -/
def prepFindEndStmt : Stmt :=
  Stmt.assign 23 (.load (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 17)))) ;;
  Stmt.assign 22 (.bin .add (.reg 17) (.const 1)) ;;
  Stmt.assign 19 (.const 1) ;;
  Stmt.loop (.reg 19)
    (Stmt.cond (.bin .lt (.reg 22) (.reg 8))
      (Stmt.cond
        (.bin .eq (.load (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 22)))) (.reg 23))
        (Stmt.assign 22 (.bin .add (.reg 22) (.const 1)))
        (Stmt.assign 19 (.const 0)))
      (Stmt.assign 19 (.const 0)))

/-- Mark `vertComp[x] := ci + 1` and `vertLoc[x] := k` for every `c` in `[r17, r22)`. -/
def prepMarkVertBody : Stmt :=
  Stmt.assign 19 (.load (.bin .add (.reg 21) (.reg 25))) ;;
  Stmt.store (.bin .add (.reg 14) (.reg 19)) (.reg 30) ;;
  Stmt.store (.bin .add (.reg 15) (.reg 19)) (.reg 25)

def prepMarkBody : Stmt :=
  Stmt.assign 31 (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 24))) ;;
  Stmt.assign 20 (.load (.bin .add (.reg 31) (.const 1))) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 31) (.const 2))) ;;
  Stmt.assign 30 (.bin .add (.reg 24) (.const 1)) ;;
  Stmt.assign 25 (.const 0) ;;
  forUp 25 (.reg 20) prepMarkVertBody

def prepMarkStmt : Stmt :=
  forRange 24 (.reg 17) (.reg 22) prepMarkBody

/-- Count `c.J_sub.m` per component in block by walking `lvlHead[r23]`. -/
def prepCountBody : Stmt :=
  Stmt.assign 20 (.bin .sub (.reg 29) (.const 1)) ;;
  Stmt.assign 19 (.load (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 20)))) ;;
  Stmt.assign 30 (.load (.bin .add (.reg 14) (.reg 19))) ;;
  Stmt.assign 31 (.bin .sub (.reg 30) (.const 1)) ;;
  Stmt.assign 26 (.bin .add (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 31))) (.const 6)) ;;
  Stmt.assign 27 (.load (.reg 26)) ;;
  Stmt.store (.reg 26) (.bin .add (.reg 27) (.const 1)) ;;
  Stmt.assign 29 (.load (.bin .add (.reg 10) (.reg 20)))

def prepCountStmt : Stmt :=
  Stmt.assign 29 (.load (.bin .add (.reg 9) (.reg 23))) ;;
  Stmt.loop (.bin .lt (.const 0) (.reg 29)) prepCountBody

/-- Allocate `(J_sub, jOrig, deg)` blocks for `[r17, r22)` and store pointers in `compsRec`. -/
def prepAllocBody : Stmt :=
  Stmt.assign 31 (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 24))) ;;
  Stmt.assign 20 (.load (.bin .add (.reg 31) (.const 1))) ;;
  Stmt.assign 26 (.load (.bin .add (.reg 31) (.const 6))) ;;
  Stmt.assign 27 (.reg 16) ;;
  Stmt.store (.reg 27) (.reg 20) ;;
  Stmt.store (.bin .add (.reg 27) (.const 1)) (.reg 26) ;;
  Stmt.assign 28 (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 26))) ;;
  Stmt.assign 30 (.bin .add (.reg 28) (.reg 26)) ;;
  Stmt.assign 16 (.bin .add (.reg 30) (.reg 20)) ;;
  Stmt.store (.bin .add (.reg 31) (.const 3)) (.reg 27) ;;
  Stmt.store (.bin .add (.reg 31) (.const 4)) (.reg 28) ;;
  Stmt.store (.bin .add (.reg 31) (.const 5)) (.reg 30) ;;
  Stmt.store (.bin .add (.reg 31) (.const 6)) (.const 0)

def prepAllocStmt : Stmt :=
  forRange 24 (.reg 17) (.reg 22) prepAllocBody

/-- Fill `J_sub.edges`, `jSubOrigEdges`, and `deg` tables by re-walking `lvlHead[r23]`. -/
def prepFillBody : Stmt :=
  Stmt.assign 20 (.bin .sub (.reg 29) (.const 1)) ;;
  Stmt.assign 19 (.load (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 20)))) ;;
  Stmt.assign 21 (.load (.bin .add (.bin .add (.reg 1) (.const 3)) (.bin .mul (.const 2) (.reg 20)))) ;;
  Stmt.assign 30 (.load (.bin .add (.reg 14) (.reg 19))) ;;
  Stmt.assign 31 (.bin .add (.reg 13) (.bin .mul (.const 7) (.bin .sub (.reg 30) (.const 1)))) ;;
  Stmt.assign 25 (.load (.bin .add (.reg 15) (.reg 19))) ;;
  Stmt.assign 30 (.load (.bin .add (.reg 15) (.reg 21))) ;;
  Stmt.assign 26 (.load (.bin .add (.reg 31) (.const 3))) ;;
  Stmt.assign 27 (.load (.bin .add (.reg 31) (.const 4))) ;;
  Stmt.assign 28 (.load (.bin .add (.reg 31) (.const 5))) ;;
  Stmt.assign 19 (.load (.bin .add (.reg 31) (.const 6))) ;;
  Stmt.assign 21 (.bin .add (.bin .add (.reg 26) (.const 2)) (.bin .mul (.const 2) (.reg 19))) ;;
  Stmt.store (.reg 21) (.reg 25) ;;
  Stmt.store (.bin .add (.reg 21) (.const 1)) (.reg 30) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
  Stmt.store (.bin .add (.reg 27) (.reg 19)) (.reg 21) ;;
  Stmt.store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 19) (.const 1)) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 28) (.reg 25))) ;;
  Stmt.store (.bin .add (.reg 28) (.reg 25)) (.bin .add (.reg 21) (.const 1)) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 28) (.reg 30))) ;;
  Stmt.store (.bin .add (.reg 28) (.reg 30)) (.bin .add (.reg 21) (.const 1)) ;;
  Stmt.assign 29 (.load (.bin .add (.reg 10) (.reg 20)))

def prepFillStmt : Stmt :=
  Stmt.assign 29 (.load (.bin .add (.reg 9) (.reg 23))) ;;
  Stmt.loop (.bin .lt (.const 0) (.reg 29)) prepFillBody

/-- Clear `vertComp[x]` and `vertLoc[x]` back to `0` for every `c` in `[r17, r22)`. -/
def prepUnmarkVertBody : Stmt :=
  Stmt.assign 19 (.load (.bin .add (.reg 21) (.reg 25))) ;;
  Stmt.store (.bin .add (.reg 14) (.reg 19)) (.const 0) ;;
  Stmt.store (.bin .add (.reg 15) (.reg 19)) (.const 0)

def prepUnmarkBody : Stmt :=
  Stmt.assign 31 (.bin .add (.reg 13) (.bin .mul (.const 7) (.reg 24))) ;;
  Stmt.assign 20 (.load (.bin .add (.reg 31) (.const 1))) ;;
  Stmt.assign 21 (.load (.bin .add (.reg 31) (.const 2))) ;;
  Stmt.assign 25 (.const 0) ;;
  forUp 25 (.reg 20) prepUnmarkVertBody

def prepUnmarkStmt : Stmt :=
  forRange 24 (.reg 17) (.reg 22) prepUnmarkBody

def prepBlockBody : Stmt :=
  prepFindEndStmt ;;
  prepMarkStmt ;;
  prepCountStmt ;;
  prepAllocStmt ;;
  prepFillStmt ;;
  prepUnmarkStmt ;;
  Stmt.assign 17 (.reg 22)

def prepBlockLoopStmt : Stmt :=
  Stmt.assign 17 (.const 0) ;;
  Stmt.loop (.bin .lt (.reg 17) (.reg 8)) prepBlockBody

def witnessPrepBody : Stmt :=
  prepInitStmt ;;
  prepBucketStmt ;;
  prepJ0Stmt ;;
  prepHdrStoreStmt ;;
  prepParseStmt ;;
  prepBlockLoopStmt ;;
  Stmt.ret (.reg 16)

def witnessPrepModule : List Stmt := [witnessPrepBody]

theorem witnessPrepBody_noRand : witnessPrepBody.NoRand := by
  simp [witnessPrepBody, prepInitStmt, prepBucketStmt, prepBucketBody, prepJ0Stmt, prepJ0Body,
    prepHdrStoreStmt, prepParseStmt, prepParseBody, prepBlockLoopStmt, prepBlockBody,
    prepFindEndStmt, prepMarkStmt, prepMarkBody, prepMarkVertBody, prepCountStmt, prepCountBody,
    prepAllocStmt, prepAllocBody, prepFillStmt, prepFillBody, prepUnmarkStmt, prepUnmarkBody,
    prepUnmarkVertBody, Stmt.NoRand, WordRAM.forUp, WordRAM.forRange]

theorem witnessPrepModule_noRand : ∀ s ∈ witnessPrepModule, s.NoRand := by
  intro s hs
  simp only [witnessPrepModule, List.mem_singleton] at hs
  subst hs
  exact witnessPrepBody_noRand

/-! ## 3. Word-RAM Specification, Bounds & Phase A Verification -/

/-- Mathematical bundle of inputs read below `h` by `witnessPrepModule`. -/
structure PrepInput where
  jAddr : ℕ
  j0Addr : ℕ
  nlAddr : ℕ
  decAddr : ℕ
  h : ℕ
  J : Graph
  J0_strip : Graph
  nlIdx : List ℕ
  d_ℓ : ℕ
  phiNum_dec : ℕ
  phiDen_dec : ℕ
  level : List ℕ
  rawComps : List (ℕ × List ℕ)
  c_ℓ : ℝ

def PrepInput.decomp (inp : PrepInput) : DecomposeOutput :=
  mkDecomposeOutput inp.d_ℓ inp.level inp.rawComps

def PrepInput.j0Edges (inp : PrepInput) : List ℕ :=
  (inp.decomp.edgesAt inp.J0_strip 0).map fun b => inp.nlIdx.getD b 0

def PrepInput.cJSub (inp : PrepInput) (c : ℕ × List ℕ) : Graph :=
  inducedSubgraph (inp.decomp.graphAt inp.J0_strip c.1) c.2.toFinset

def PrepInput.cJOrig (inp : PrepInput) (c : ℕ × List ℕ) : List ℕ :=
  (insideIndices (inp.decomp.graphAt inp.J0_strip c.1) c.2.toFinset).map
    fun a => inp.nlIdx.getD ((inp.decomp.edgesAt inp.J0_strip c.1).getD a 0) 0

def PrepInput.degList (G : Graph) : List ℕ :=
  (List.range G.n).map G.deg

def PrepInput.hBlocksStart (inp : PrepInput) : ℕ :=
  inp.h + 9 + inp.d_ℓ + inp.J0_strip.m + inp.j0Edges.length +
    7 * inp.rawComps.length + 2 * inp.J.n

def PrepInput.hEnd (inp : PrepInput) : ℕ :=
  inp.hBlocksStart +
    (inp.rawComps.map fun c => 2 + 3 * (inp.cJSub c).m + c.2.length).sum

def PrepInput.Valid (inp : PrepInput) (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.J.IsValid ∧
  GraphAt mem inp.jAddr inp.J ∧
  inp.J0_strip = stripLoops inp.J ∧
  GraphAt mem inp.j0Addr inp.J0_strip ∧
  inp.nlIdx = nonloopIndices inp.J ∧
  ListAt mem inp.nlAddr inp.nlIdx ∧
  DecomposeOutAt mem inp.decAddr inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps ∧
  inp.level.length = inp.J0_strip.m ∧
  1 ≤ inp.phiNum_dec ∧ inp.phiNum_dec ≤ inp.phiDen_dec ∧
  inp.rawComps.Pairwise (fun a b => a.1 ≤ b.1) ∧
  (∀ c ∈ inp.rawComps, 1 ≤ c.1 ∧ c.1 ≤ inp.d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length) ∧
  DecomposeProp inp.c_ℓ inp.J0_strip inp.decomp ((inp.phiNum_dec : ℝ) / (inp.phiDen_dec : ℝ)) ∧
  inp.jAddr + inp.J.encode.length ≤ inp.h ∧
  inp.j0Addr + inp.J0_strip.encode.length ≤ inp.h ∧
  inp.nlAddr + inp.nlIdx.length ≤ inp.h ∧
  inp.decAddr + (Decompose.encode inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps).length ≤ inp.h ∧
  ZeroFrom mem inp.h ∧
  1 < 2 ^ w ∧
  inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n < 2 ^ w

theorem PrepInput.valid_of_agree {inp : PrepInput} {mem mem' : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem w) (hag : ∀ x < inp.h, mem' x = mem x)
    (hzero' : ZeroFrom mem' inp.h) :
    inp.Valid mem' w := by
  rcases hv with ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp,
    hjle, hj0le, hnlle, hdecle, _, hw1, hwb⟩
  exact ⟨hJ, hgJ.of_agree_below hjle hag, hJ0, hgJ0.of_agree_below hj0le hag, hnl,
    listAt_of_congr hlNl (fun i hi => hag _ (by omega)),
    listAt_of_congr hdec (fun i hi => hag _ (by omega)),
    hllen, hpn, hpnd, hpw, hprops, hdp, hjle, hj0le, hnlle, hdecle, hzero', hw1, hwb⟩

private theorem sum_filter_pairwise_le {α ι : Type*} (bs : List α) (P : ι → α → Bool) :
    ∀ ks : List ι, ks.Pairwise (fun k₁ k₂ => ∀ b, !(P k₁ b && P k₂ b)) →
      (ks.map fun k => (bs.filter (P k)).length).sum ≤ bs.length := by
  induction bs with
  | nil =>
    intro ks _
    induction ks with
    | nil => simp
    | cons k ks _ => simp
  | cons b bs ih =>
    intro ks hpw
    have hstep : ∀ ys : List ι, ys.Pairwise (fun k₁ k₂ => ∀ a, !(P k₁ a && P k₂ a)) →
        (ys.map fun k => if P k b then 1 else 0).sum ≤ 1 := by
      intro ys hy
      induction ys with
      | nil => simp
      | cons y ys ihy =>
        rw [List.pairwise_cons] at hy
        simp only [List.map_cons, List.sum_cons]
        by_cases hpb : P y b = true
        · have hzero : (ys.map fun z => if P z b then 1 else 0).sum = 0 :=
            List.sum_eq_zero <| fun z hz => by
              rcases List.mem_map.mp hz with ⟨k, hk, rfl⟩
              have hdis := hy.1 k hk b
              simp [hpb] at hdis
              simp [hdis]
          simp [hpb, hzero]
        · simp [hpb, ihy hy.2]
    have hcongr : ∀ ys : List ι,
        (ys.map fun k => ((b :: bs).filter (P k)).length).sum =
          (ys.map fun k => if P k b then 1 else 0).sum +
            (ys.map fun k => (bs.filter (P k)).length).sum := by
      intro ys
      induction ys with
      | nil => simp
      | cons k ks ihk =>
        rw [List.map_cons, List.sum_cons, ihk]
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        by_cases hpk : P k b = true
        · simp only [hpk, ↓reduceIte, List.length_cons]; omega
        · simp only [hpk, Bool.false_eq_true, ↓reduceIte]; omega
    rw [hcongr ks]
    have h1 := hstep ks hpw
    have h2 := ih ks hpw
    simp only [List.length_cons]
    omega

private theorem sum_filter_disjoint_le {α : Type*} (eds : List α) (f : α → ℕ)
    (xs : List (Finset ℕ)) (hpw : xs.Pairwise Disjoint) :
    (xs.map fun X => (eds.filter fun b => decide (f b ∈ X)).length).sum ≤ eds.length :=
  sum_filter_pairwise_le eds (fun X b => decide (f b ∈ X)) xs <|
    hpw.imp fun {X₁ X₂} h b => by
      by_cases hb : f b ∈ X₁
      · simp [hb, Finset.disjoint_left.mp h hb]
      · simp [hb]

private theorem sum_edgesAt_disjoint_le (J0 : Graph) (d : DecomposeOutput)
    (lvls : List ℕ) (hnodup : lvls.Nodup) :
    (lvls.map fun lvl => (d.edgesAt J0 lvl).length).sum ≤ J0.m := by
  simpa [DecomposeOutput.edgesAt, List.length_range] using
    sum_filter_pairwise_le (List.range J0.m) (fun lvl b => decide (d.level b = lvl)) lvls <|
      (List.nodup_iff_pairwise_ne.mp hnodup).imp fun {l₁ l₂} hne b => by
        by_cases h1 : d.level b = l₁
        · simp [h1, hne]
        · simp [h1]

theorem PrepInput.size_bounds {inp : PrepInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem w) :
    inp.j0Edges.length ≤ inp.J0_strip.m ∧
    inp.rawComps.length ≤ inp.J0_strip.m ∧
    (inp.rawComps.map fun c => 2 + c.2.length).sum ≤ 4 * inp.J0_strip.m ∧
    inp.j0Edges.length + (inp.rawComps.map fun c => (inp.cJSub c).m).sum ≤ inp.J0_strip.m ∧
    inp.hEnd ≤ inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n ∧
    inp.J0_strip.m ≤ inp.J.m := by
  rcases hv with ⟨hJ, _, hJ0, _, _, _, _, _, hpn, hpnd, hpw, hprops, hdp, _⟩
  have hraw_eq : inp.rawComps.map (fun c => (c.1, c.2.toFinset)) =
      (List.range inp.d_ℓ).flatMap fun i' => (inp.decomp.comps (i' + 1)).map fun X => (i' + 1, X) :=
    (mkDecomposeOutput_rawComps_eq inp.d_ℓ inp.level inp.rawComps hpw fun c hc =>
      ⟨(hprops c hc).1, (hprops c hc).2.1⟩).symm
  have hraw_nd : ∀ c ∈ inp.rawComps, c.2.Nodup ∧ 2 ≤ c.2.length := fun c hc =>
    ⟨(hprops c hc).2.2.1.imp (fun h => h.ne), (hprops c hc).2.2.2⟩
  have hdisj : ∀ i, 1 ≤ i → i ≤ inp.d_ℓ → (inp.decomp.comps i).Pairwise Disjoint :=
    fun i hi0 hiℓ => (hdp.2.2.2 i hi0 hiℓ).1
  have hcard2 : ∀ i, 1 ≤ i → i ≤ inp.d_ℓ → ∀ X ∈ inp.decomp.comps i, 2 ≤ X.card :=
    fun i hi0 hiℓ X hX => (hdp.2.2.2 i hi0 hiℓ).2.1 X hX |>.2.1
  have hdeg_pos : ∀ i, 1 ≤ i → i ≤ inp.d_ℓ → ∀ X ∈ inp.decomp.comps i,
      ∀ x ∈ X, 1 ≤ (inp.decomp.graphAt inp.J0_strip i).degIn X x := by
    intro i hi0 hiℓ X hX x hx
    have hge := (hdp.2.2.2 i hi0 hiℓ).2.1 X hX |>.2.2.2.1 x hx
    have hpos_phi : (0 : ℝ) < (inp.phiNum_dec : ℝ) / (inp.phiDen_dec : ℝ) :=
      div_pos (Nat.cast_pos.mpr hpn) (Nat.cast_pos.mpr (lt_of_lt_of_le hpn hpnd))
    have hpow : (1 : ℝ) ≤ (2 ^ i : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have hreal : (0 : ℝ) < ((inp.decomp.graphAt inp.J0_strip i).degIn X x : ℝ) :=
      lt_of_lt_of_le (mul_pos hpos_phi (by positivity)) hge
    exact Nat.cast_pos.mp hreal
  have hraw_sum4 := decompose_rawComps_size_le hraw_eq hraw_nd hdisj hcard2 hdeg_pos
  have hlen4 : 4 * inp.rawComps.length ≤ (inp.rawComps.map fun c => 2 + c.2.length).sum := by
    have hgen : ∀ xs : List (ℕ × List ℕ), (∀ c ∈ xs, 2 ≤ c.2.length) →
        4 * xs.length ≤ (xs.map fun c => 2 + c.2.length).sum := by
      intro xs hxs
      induction xs with
      | nil => simp
      | cons c cs ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have hc2 : 2 ≤ c.2.length := hxs c List.mem_cons_self
        have ih' := ih fun q hq => hxs q (List.mem_cons_of_mem c hq)
        omega
    exact hgen inp.rawComps fun c hc => (hprops c hc).2.2.2
  have hj0_le : inp.j0Edges.length ≤ inp.J0_strip.m := by
    simp only [PrepInput.j0Edges, List.length_map, DecomposeOutput.edgesAt]
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hblocks := compBlocksAux_props 0 inp.rawComps hpw
  have hjm_sum : inp.j0Edges.length + (inp.rawComps.map fun c => (inp.cJSub c).m).sum ≤
      inp.J0_strip.m := by
    set blocks := compBlocksAux 0 inp.rawComps
    have hj0_eq : inp.j0Edges.length = (inp.decomp.edgesAt inp.J0_strip 0).length := by
      simp [PrepInput.j0Edges]
    have hflat_jm : (inp.rawComps.map fun c => (inp.cJSub c).m).sum =
        (blocks.map fun b => (b.2.2.map fun c => (inp.cJSub c).m).sum).sum := by
      have hcongr_bs : ∀ bs : List (ℕ × ℕ × List (ℕ × List ℕ)),
          ((bs.flatMap fun x => x.2.2).map fun c => (inp.cJSub c).m).sum =
            (bs.map fun b => (b.2.2.map fun c => (inp.cJSub c).m).sum).sum := by
        intro bs
        induction bs with
        | nil => simp
        | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]
      conv_lhs => rw [← hblocks.2.2.1]
      exact hcongr_bs blocks
    have hflat_filter : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
        bs.Pairwise (fun a b => a.2.1 < b.2.1) →
        (∀ b ∈ bs, ∀ c ∈ b.2.2, c.1 = b.2.1) →
        ∀ b ∈ bs, (bs.flatMap fun x => x.2.2).filter (fun p => decide (p.1 = b.2.1)) = b.2.2 := by
      intro bs
      induction bs with
      | nil => intro _ _ b hb; simp at hb
      | cons hd tl ih =>
        intro hpw_bs hmem_bs b hb
        rw [List.pairwise_cons] at hpw_bs
        simp only [List.flatMap_cons, List.filter_append]
        rcases List.mem_cons.mp hb with rfl | hbtl
        · have h1 : b.2.2.filter (fun p => decide (p.1 = b.2.1)) = b.2.2 :=
            List.filter_eq_self.mpr fun q hq => by simp [hmem_bs b List.mem_cons_self q hq]
          have h2 : (tl.flatMap fun x => x.2.2).filter (fun p => decide (p.1 = b.2.1)) = [] :=
            List.filter_eq_nil_iff.mpr fun q hq => by
              rw [List.mem_flatMap] at hq
              rcases hq with ⟨b', hb', hqb'⟩
              have hlt := hpw_bs.1 b' hb'
              have heq := hmem_bs b' (List.mem_cons_of_mem b hb') q hqb'
              simp only [decide_eq_true_eq]; omega
          rw [h1, h2, List.append_nil]
        · have h1 : hd.2.2.filter (fun p => decide (p.1 = b.2.1)) = [] :=
            List.filter_eq_nil_iff.mpr fun q hq => by
              have hlt := hpw_bs.1 b hbtl
              have heq := hmem_bs hd List.mem_cons_self q hq
              simp only [decide_eq_true_eq]; omega
          have h2 := ih hpw_bs.2 (fun x hx => hmem_bs x (List.mem_cons_of_mem hd hx)) b hbtl
          rw [h1, List.nil_append, h2]
    have hblock_le : ∀ b ∈ blocks,
        (b.2.2.map fun c => (inp.cJSub c).m).sum ≤ (inp.decomp.edgesAt inp.J0_strip b.2.1).length := by
      intro b hb
      rcases b with ⟨ciStart, lvl, block⟩
      have hb_in := hblocks.2.2.2 (ciStart, lvl, block) hb
      have hpos := hb_in.1
      have hc_lvl := hb_in.2
      have hblk_sub : ∀ c ∈ block, c ∈ inp.rawComps := fun c hc => by
        rw [← hblocks.2.2.1]
        exact List.mem_flatMap.mpr ⟨_, hb, hc⟩
      have hc0 : block[0]'(by simpa using hpos) ∈ inp.rawComps := hblk_sub _ (List.getElem_mem _)
      have hlvl_eq : lvl = (block[0]'(by simpa using hpos)).1 := (hc_lvl _ (List.getElem_mem _)).symm
      have hlvl1 : 1 ≤ lvl := hlvl_eq ▸ (hprops _ hc0).1
      have hlvlℓ : lvl ≤ inp.d_ℓ := hlvl_eq ▸ (hprops _ hc0).2.1
      have hblk_filter : block = inp.rawComps.filter (fun p => decide (p.1 = lvl)) := by
        have hf := hflat_filter blocks hblocks.1 (fun b' hb' => (hblocks.2.2.2 b' hb').2)
          (ciStart, lvl, block) hb
        simpa [hblocks.2.2.1] using hf.symm
      have hcomp_eq : block.map (fun c => c.2.toFinset) = inp.decomp.comps lvl := by
        simp [PrepInput.decomp, mkDecomposeOutput, hblk_filter]
      have hpw_fin : (block.map fun c => c.2.toFinset).Pairwise Disjoint :=
        hcomp_eq ▸ hdisj lvl hlvl1 hlvlℓ
      have hmap_len : block.map (fun c => (inp.cJSub c).m) =
          (block.map fun c => c.2.toFinset).map fun X =>
            ((inp.decomp.edgesAt inp.J0_strip lvl).filter
              (fun eIdx => decide ((inp.J0_strip.edges.getD eIdx (0, 0)).1 ∈ X))).length := by
        rw [List.map_map]
        refine List.map_congr_left fun c hc => ?_
        have hc_cl : c.1 = lvl := hc_lvl c hc
        have hX_mem : c.2.toFinset ∈ inp.decomp.comps lvl := by
          rw [← hcomp_eq]; exact List.mem_map.mpr ⟨c, hc, rfl⟩
        have hiff := (hdp.2.2.2 lvl hlvl1 hlvlℓ).2.1 c.2.toFinset hX_mem |>.2.2.2.2
        have hfilt := edgesAt_inside_filter_eq hiff
        have hm : (inp.cJSub c).m =
            ((insideIndices (inp.decomp.graphAt inp.J0_strip lvl) c.2.toFinset).map
              fun a => (inp.decomp.edgesAt inp.J0_strip lvl).getD a 0).length := by
          simp [PrepInput.cJSub, hc_cl, inducedSubgraph, Graph.m]
        rw [hm, hfilt]
        rfl
      rw [hmap_len]
      exact sum_filter_disjoint_le _ _ _ hpw_fin
    have hnodup_lvls : (0 :: blocks.map fun b => b.2.1).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h0
        rcases List.mem_map.mp h0 with ⟨b, hb, hbeq⟩
        have hb_in := hblocks.2.2.2 b hb
        have hc0 := hb_in.1
        have hmem_first : b.2.2[0]'(by simpa using hc0) ∈ inp.rawComps := by
          rw [← hblocks.2.2.1]
          exact List.mem_flatMap.mpr ⟨b, hb, List.getElem_mem _⟩
        have h1 := (hprops _ hmem_first).1
        have h2 := hb_in.2 (b.2.2[0]'hc0) (List.getElem_mem hc0)
        omega
      · exact ((List.pairwise_map (R := (· ≠ ·))).mpr (hblocks.1.imp fun {a b} h => Nat.ne_of_lt h)).nodup
    have hsum_lvls := sum_edgesAt_disjoint_le inp.J0_strip inp.decomp (0 :: blocks.map fun x => x.2.1) hnodup_lvls
    have hblocks_sum_le : (blocks.map fun b => (b.2.2.map fun c => (inp.cJSub c).m).sum).sum ≤
        (blocks.map fun b => (inp.decomp.edgesAt inp.J0_strip b.2.1).length).sum := by
      have hgen : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
          (∀ b ∈ bs, (b.2.2.map fun c => (inp.cJSub c).m).sum ≤
            (inp.decomp.edgesAt inp.J0_strip b.2.1).length) →
          (bs.map fun b => (b.2.2.map fun c => (inp.cJSub c).m).sum).sum ≤
            (bs.map fun b => (inp.decomp.edgesAt inp.J0_strip b.2.1).length).sum := by
        intro bs hbs
        induction bs with
        | nil => simp
        | cons hd tl ih =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (hbs hd List.mem_cons_self)
            (ih fun x hx => hbs x (List.mem_cons_of_mem hd hx))
      exact hgen blocks hblock_le
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at hsum_lvls
    rw [hj0_eq, hflat_jm]
    omega
  refine ⟨hj0_le, ?_, hraw_sum4, hjm_sum, ?_, ?_⟩
  · omega
  · dsimp only [PrepInput.hEnd, PrepInput.hBlocksStart]
    have hsum_3 : (inp.rawComps.map fun c => 2 + 3 * (inp.cJSub c).m + c.2.length).sum =
        (inp.rawComps.map fun c => 2 + c.2.length).sum + 3 * (inp.rawComps.map fun c => (inp.cJSub c).m).sum := by
      have hgen : ∀ xs : List (ℕ × List ℕ),
          (xs.map fun c => 2 + 3 * (inp.cJSub c).m + c.2.length).sum =
            (xs.map fun c => 2 + c.2.length).sum + 3 * (xs.map fun c => (inp.cJSub c).m).sum := by
        intro xs
        induction xs with
        | nil => simp
        | cons c cs ih => simp only [List.map_cons, List.sum_cons, ih]; omega
      exact hgen inp.rawComps
    rw [hsum_3]
    omega
  · rw [hJ0]; exact stripLoops_m_le inp.J

end MinCostFlow.Spanner


