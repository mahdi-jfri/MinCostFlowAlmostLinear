module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBPrim
public import MinCostFlow.ExpanderDecomp.ProgStepBScatter
public import MinCostFlow.ExpanderDecomp.OneShotHelpers

import Mathlib.Tactic.Linarith

/-!
# Witness Graph Relabeling and Sub-Core Result Lifting (`ProgStepBRelabel`)

Provides the local witness-graph relabeling and output-lifting subroutines used by Step B
before and after each recursive `bSubCore` call so that every recursive call operates on a
vertex set `Finset.range b` (`W'.n = b ≤ 2048 * L * N^r`, independent of `G.n`):

* `liftCoreResult`, `relabelGraph_isExpansionExpanderOn_iff`, `coreSpec_of_relabel`:
  graph-isomorphism transfer of `IsExpansionExpanderOn` and `CoreSpec` across `relabelGraph`.
* `sbRelabelGraphStmt`, `sbRelabelGraph_triple`: writes `relabelGraph verts es` at `wRelA`
  using `locA` as a temporary index map and restores `locA` to all zeros in `≤ 60 * b + 70 * m + 90`
  steps without scanning `range G.n`.
* `sbLiftOutStmt`, `sbLiftOut_triple`: lifts `CoreOutAt mem subOutA res'` in place to
  `CoreOutAt mem' subOutA (liftCoreResult verts res')` in `≤ 45 * b + 30` steps.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `CoreSpec` Transfer under `relabelGraph` -/

/-- Lift a `CoreResult` on `Finset.range verts.length` back to `verts.toFinset` via `verts.getD · 0`. -/
def liftCoreResult (verts : List ℕ) : CoreResult → CoreResult
  | .cut U' => .cut (U'.image fun i => verts.getD i 0)
  | .expander S' => .expander (S'.image fun i => verts.getD i 0)

/-- Vertex-expansion isomorphism across `relabelGraph`. -/
theorem relabelGraph_isExpansionExpanderOn_iff {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {A : Finset ℕ} (hA : A ⊆ Finset.range verts.length) {φ : ℝ} :
    (relabelGraph verts es).IsExpansionExpanderOn A φ ↔
      (Graph.mk n es).IsExpansionExpanderOn (A.image fun i => verts.getD i 0) φ := by
  let f : ℕ → ℕ := fun i => verts.getD i 0
  have hinjA : Set.InjOn f (A : Set ℕ) := fun i hi j hj hij =>
    nodup_getD_inj hnd (Finset.mem_range.mp (hA hi)) (Finset.mem_range.mp (hA hj)) hij
  constructor
  · intro hexp S hS hSne hSneA
    let S_loc : Finset ℕ := A.filter fun i => f i ∈ S
    have hSloc_sub : S_loc ⊆ A := Finset.filter_subset _ _
    have hS_eq : S_loc.image f = S := by
      ext u; simp only [S_loc, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨_, hfi⟩, rfl⟩; exact hfi
      · intro hu; rcases Finset.mem_image.mp (hS hu) with ⟨i, hiA, rfl⟩; exact ⟨i, ⟨hiA, hu⟩, rfl⟩
    have hSloc_ne : S_loc.Nonempty := by
      rcases hSne with ⟨u, hu⟩; rw [← hS_eq] at hu
      rcases Finset.mem_image.mp hu with ⟨i, hi, _⟩; exact ⟨i, hi⟩
    have hSloc_neA : S_loc ≠ A := fun heq => hSneA (by rw [← hS_eq, heq])
    have h := hexp S_loc hSloc_sub hSloc_ne hSloc_neA
    have hcardS : S.card = S_loc.card := by
      rw [← hS_eq, Finset.card_image_of_injOn (hinjA.mono hSloc_sub)]
    have hcardD : (A.image f \ S).card = (A \ S_loc).card := by
      rw [← hS_eq, ← image_sdiff_getD hnd hA (hSloc_sub.trans hA),
        Finset.card_image_of_injOn (hinjA.mono Finset.sdiff_subset)]
    rw [relabelGraph_cutIn (n := n) hnd hes hA hSloc_sub, hS_eq] at h
    rw [hcardS, hcardD]; exact h
  · intro hexp S_loc hSA hSne hSneA
    have hS_sub : S_loc.image f ⊆ A.image f := Finset.image_subset_image hSA
    have hS_ne : (S_loc.image f).Nonempty := hSne.image f
    have hS_neA : S_loc.image f ≠ A.image f := by
      intro heq; apply hSneA; ext i; constructor
      · intro hi; exact hSA hi
      · intro hiA
        have hmem : f i ∈ S_loc.image f := heq ▸ Finset.mem_image_of_mem f hiA
        rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
        have heq_ij : j = i := hinjA (hSA hj) hiA hji
        exact heq_ij ▸ hj
    have h := hexp (S_loc.image f) hS_sub hS_ne hS_neA
    have hcardS : (S_loc.image f).card = S_loc.card :=
      Finset.card_image_of_injOn (hinjA.mono hSA)
    have hcardD : (A.image f \ S_loc.image f).card = (A \ S_loc).card := by
      rw [← image_sdiff_getD hnd hA (hSA.trans hA),
        Finset.card_image_of_injOn (hinjA.mono Finset.sdiff_subset)]
    rw [hcardS, hcardD, ← relabelGraph_cutIn (n := n) hnd hes hA hSA] at h
    exact h

/-- `CoreSpec` on `relabelGraph verts es` lifts directly to `CoreSpec` on `Graph.mk n es`. -/
theorem coreSpec_of_relabel {cp : CoreParams} {q' n b : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    {B : Finset ℕ} {res' : CoreResult}
    (hnd : verts.Nodup) (hlen : verts.length = b) (hfin : verts.toFinset = B)
    (hes : ∀ e ∈ es, e.1 ∈ B ∧ e.2 ∈ B)
    (hSpec' : CoreSpec cp q' (relabelGraph verts es) (Finset.range b) res') :
    CoreSpec cp q' (Graph.mk n es) B (liftCoreResult verts res') := by
  have hes' : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset := by rwa [hfin]
  have hB_eq : (Finset.range verts.length).image (fun i => verts.getD i 0) = B := by
    rw [image_range_getD, hfin]
  have hB_eq' : (Finset.range b).image (fun i => verts.getD i 0) = B := hlen ▸ hB_eq
  have hinj : Set.InjOn (fun i => verts.getD i 0) (Finset.range b : Set ℕ) := fun i hi j hj hij =>
    nodup_getD_inj hnd (hlen.symm ▸ Finset.mem_range.mp hi) (hlen.symm ▸ Finset.mem_range.mp hj) hij
  have hB_card : B.card = b := by rw [← hfin, List.toFinset_card_of_nodup hnd, hlen]
  cases res' with
  | cut U' =>
    rcases hSpec' with ⟨hU_sub, h4U, h4D, hcut⟩
    have hU_sub' : U' ⊆ Finset.range verts.length := hlen.symm ▸ hU_sub
    have hcardU : (U'.image fun i => verts.getD i 0).card = U'.card :=
      Finset.card_image_of_injOn (hinj.mono hU_sub)
    have hcardD : (B \ U'.image fun i => verts.getD i 0).card = (Finset.range b \ U').card := by
      rw [← hB_eq', ← hlen, ← image_sdiff_getD hnd (Finset.Subset.refl _) hU_sub', hlen,
        Finset.card_image_of_injOn (hinj.mono Finset.sdiff_subset)]
    have hcut_eq : (Graph.mk n es).cutIn B (U'.image fun i => verts.getD i 0) =
        (relabelGraph verts es).cutIn (Finset.range b) U' := by
      have h := relabelGraph_cutIn (n := n) hnd hes' (Finset.Subset.refl (Finset.range verts.length)) hU_sub'
      rw [hB_eq, hlen] at h; exact h.symm
    simp only [liftCoreResult, CoreSpec, Finset.card_range] at h4U h4D hcut ⊢
    refine ⟨hfin ▸ image_getD_subset_toFinset hU_sub', ?_, ?_, ?_⟩
    · rw [hB_card, hcardU]; exact h4U
    · rw [hB_card, hcardD]; exact h4D
    · rw [hB_card, hcut_eq]; exact hcut
  | expander S' =>
    rcases hSpec' with ⟨hS_sub, h2S, hexp⟩
    have hS_sub' : S' ⊆ Finset.range verts.length := hlen.symm ▸ hS_sub
    have hcardS : (S'.image fun i => verts.getD i 0).card = S'.card :=
      Finset.card_image_of_injOn (hinj.mono hS_sub)
    simp only [liftCoreResult, CoreSpec, Finset.card_range] at h2S ⊢
    refine ⟨hfin ▸ image_getD_subset_toFinset hS_sub', ?_, ?_⟩
    · rw [hB_card, hcardS]; exact h2S
    · exact (relabelGraph_isExpansionExpanderOn_iff (n := n) hnd hes' hS_sub').mp hexp

/-- Looplessness transfers to `relabelGraph`. -/
lemma relabelGraph_loopless {n b : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hlen : verts.length = b)
    (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    (hloop : ∀ e ∈ (Graph.mk n es).inside verts.toFinset, e.1 ≠ e.2) :
    ∀ e ∈ (relabelGraph verts es).inside (Finset.range b), e.1 ≠ e.2 := by
  intro e he
  rw [← hlen, relabelGraph_inside (n := n) hnd hes (Finset.Subset.refl _), image_range_getD] at he
  simp only [relabelEdges, List.mem_map] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have hne := hloop e₀ he₀
  have h12 := hes e₀ (mem_inside_iff.mp he₀).1
  intro heq
  apply hne
  have h1 := nodup_getD_idxOf (List.mem_toFinset.mp h12.1)
  have h2 := nodup_getD_idxOf (List.mem_toFinset.mp h12.2)
  dsimp only at heq
  rw [← h1, ← h2, heq]

/-! ## 2. Word-RAM Witness Relabeling (`sbRelabelGraphStmt`) -/

/-- Relabels graph at `r29 = wAddr` (with all endpoints in `verts` at `r28 = blkA`, length `r4 = b`)
into `r32 = wRelA`, using `r8 = locA` as a temporary index table and restoring `locA` to zero.
Uses scratch `r33..r37`; preserves `r < 33`. -/
def sbRelabelGraphStmt : Stmt :=
  seqStmts [
    forRange 33 (.const 0) (.reg 4)
      (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 28) (.reg 33)))) (.reg 33)),
    .assign 34 (.load (.bin .add (.reg 29) (.const 1))),
    .store (.reg 32) (.reg 4),
    .store (.bin .add (.reg 32) (.const 1)) (.reg 34),
    forRange 33 (.const 0) (.reg 34) (seqStmts [
      .assign 35 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 33))),
      .assign 36 (.load (.bin .add (.reg 29) (.reg 35))),
      .assign 37 (.load (.bin .add (.bin .add (.reg 29) (.reg 35)) (.const 1))),
      .store (.bin .add (.reg 32) (.reg 35)) (.load (.bin .add (.reg 8) (.reg 36))),
      .store (.bin .add (.bin .add (.reg 32) (.reg 35)) (.const 1)) (.load (.bin .add (.reg 8) (.reg 37)))
    ]),
    .assign 35 (.const 0),
    sbMarkListStmt 28 4 8 35 33 34
  ]

theorem sbRelabelGraphStmt_noRand : sbRelabelGraphStmt.NoRand := by
  simp [sbRelabelGraphStmt, sbMarkListStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Triple for the index-marking loop `locA[verts[i]] := i` (`i = 0..b-1`). -/
private lemma sbMarkIdx_triple {w n b blkA locA : ℕ}
    {p : Program} {mem : ℕ → ℕ} {verts : List ℕ} {st₀ : State}
    (hlen : verts.length = b) (hnd : verts.Nodup)
    (hlat : ListAt mem blkA verts) (hsub : ∀ u ∈ verts, u < n)
    (hd_loc_blk : DisjointRange locA n blkA b)
    (hblk_w : blkA + b < 2 ^ w) (hloc_w : locA + n < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA) (hr28 : st₀.regs 28 = blkA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀)
      (forRange 33 (.const 0) (.reg 4)
        (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 28) (.reg 33)))) (.reg 33)))
      (normalPost fun st' =>
        (∀ r, r ≠ 33 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem locA (locA + n) ∧
        (∀ u ∈ verts, st'.mem (locA + u) = verts.idxOf u) ∧
        (∀ u < n, u ∉ verts → st'.mem (locA + u) = mem (locA + u)))
      (fun _ => 32 * b + 20) := by
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 33 = j ∧
    (∀ r, r ≠ 33 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem locA (locA + n) ∧
    (∀ i, i < j → ∀ (hib : i < b), st.mem (locA + verts[i]'(hlen.symm ▸ hib)) = i) ∧
    (∀ u < n, u ∉ verts → st.mem (locA + u) = mem (locA + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 33) (lo := .const 0) (hi := .reg 4)
    (body := .store (.bin .add (.reg 8) (.load (.bin .add (.reg 28) (.reg 33)))) (.reg 33))
    (P := fun st => st = st₀) (Inv := Inv) 16 0 b (Nat.zero_le b) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne hr],
        rfl, hmem ▸ memFrame_refl _ _ _, fun _ hi => absurd hi (Nat.not_lt_zero _),
        fun _ _ _ => congrFun hmem _⟩)
    (fun _ _ _ _ hInv => hInv.1)
    (fun _ _ _ _ hInv => Expr.eval_reg_of_eq ((hInv.2.1 4 (by decide)).trans hr4))
    (fun j _ hj => by
      intro st ω ⟨hr33, hoth, hpos, hfr, hmap, hnot⟩
      have hju : verts[j]'(hlen.symm ▸ hj) < n := hsub _ (List.getElem_mem (hlen.symm ▸ hj))
      have hblk_j : st.mem (blkA + j) = verts[j]'(hlen.symm ▸ hj) := by
        rw [hfr _ (by rcases hd_loc_blk with h | h <;> [right; left] <;> omega)]
        exact hlat j (hlen.symm ▸ hj)
      refine runs_start_le ?_
      refine runs_store_le (x := locA + verts[j]'(hlen.symm ▸ hj)) (v := j)
        (Expr.eval_add (Expr.eval_reg_of_eq ((hoth 8 (by decide)).trans hr8))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth 28 (by decide)).trans hr28))
            (Expr.eval_reg_of_eq hr33) (by omega)) hblk_j) (by omega))
        (Expr.eval_reg_of_eq hr33) ?_ (by simp only [Expr.size]; omega)
      refine ⟨⟨by simp, fun r hr => by dsimp only; rw [Function.update_of_ne hr]; exact hoth r hr,
        hpos, fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha,
        fun i hi hib => ?_, fun u hu hnotv => ?_⟩, hr33⟩
      · dsimp only
        by_cases hij : i = j
        · subst hij; rw [Function.update_self]
        · have hne : verts[i]'(hlen.symm ▸ hib) ≠ verts[j]'(hlen.symm ▸ hj) :=
            fun h => hij ((List.Nodup.getElem_inj_iff hnd).mp h)
          rw [Function.update_of_ne (by omega)]
          exact hmap i (by omega) hib
      · dsimp only
        have hne : u ≠ verts[j]'(hlen.symm ▸ hj) := fun h => hnotv (h ▸ List.getElem_mem (hlen.symm ▸ hj))
        rw [Function.update_of_ne (by omega)]
        exact hnot u hu hnotv)
  exact hloop.conseq (fun _ h => h)
    (fun o st' h => by
      cases o with
      | returned _ => exact h
      | normal =>
        rcases h with ⟨_, hoth, hpos, hfr, hmap, hnot⟩
        refine ⟨hoth, hpos, hfr, fun u hu => ?_, hnot⟩
        have hlt : verts.idxOf u < b := hlen ▸ List.idxOf_lt_length_of_mem hu
        have hget : verts[verts.idxOf u]'(hlen.symm ▸ hlt) = u := List.getElem_idxOf (hlen.symm ▸ hlt)
        have := hmap (verts.idxOf u) hlt hlt
        rwa [hget] at this)
    (fun _ _ => by simp only [Expr.size]; omega)

/-- Triple for `sbRelabelGraphStmt`: writes `relabelGraph verts es` at `wRelA`, restores `locA`
to zero, preserves memory outside `locA` and `[wRelA, wRelA + 2 + 2 * m)`, and runs in
`≤ 60 * b + 70 * es.length + 90` steps. -/
theorem sbRelabelGraph_triple {w n b blkA wAddr wRelA locA : ℕ}
    {p : Program} {mem : ℕ → ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)} {st₀ : State}
    (hlen : verts.length = b) (hnd : verts.Nodup)
    (hlat : ListAt mem blkA verts) (hsub : ∀ u ∈ verts, u < n)
    (hG_at : GraphAt mem wAddr (Graph.mk n es))
    (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hd_loc_blk : DisjointRange locA n blkA b)
    (hd_loc_w : DisjointRange locA n wAddr (2 + 2 * es.length))
    (hd_loc_rel : DisjointRange locA n wRelA (2 + 2 * es.length))
    (hd_rel_blk : DisjointRange wRelA (2 + 2 * es.length) blkA b)
    (hd_rel_w : DisjointRange wRelA (2 + 2 * es.length) wAddr (2 + 2 * es.length))
    (hblk_w : blkA + b < 2 ^ w) (hloc_w : locA + n < 2 ^ w)
    (hw_w : wAddr + 2 + 2 * es.length < 2 ^ w) (hrel_w : wRelA + 2 + 2 * es.length < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA)
    (hr28 : st₀.regs 28 = blkA) (hr29 : st₀.regs 29 = wAddr) (hr32 : st₀.regs 32 = wRelA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbRelabelGraphStmt
      (normalPost fun st' =>
        (∀ r < 33, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < wRelA ∨ wRelA + 2 + 2 * es.length ≤ a) →
          st'.mem a = mem a) ∧
        GraphAt st'.mem wRelA (relabelGraph verts es))
      (fun _ => 60 * b + 70 * es.length + 100) := by
  have hm_w : es.length < 2 ^ w := by omega
  have hG_iff := (graphAt_mk_iff).mp hG_at
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbRelabelGraphStmt, seqStmts]
  refine runs_seq_triple_le
    (sbMarkIdx_triple hlen hnd hlat hsub hd_loc_blk hblk_w hloc_w hw16 hr4 hr8 hr28 hmem) rfl ?_
  intro st1 ⟨hoth1, hpos1, hfr1, hmap1, hnot1⟩
  have hG1_m : st1.mem (wAddr + 1) = es.length := by
    rw [hfr1 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hG_iff.2.1
  have hG1_e : EdgesAt st1.mem (wAddr + 2) es := fun j hj => by
    have h1 : wAddr + 2 + 2 * j < locA ∨ locA + n ≤ wAddr + 2 + 2 * j := by rcases hd_loc_w with h | h <;> [right; left] <;> omega
    have h2 : wAddr + 2 + 2 * j + 1 < locA ∨ locA + n ≤ wAddr + 2 + 2 * j + 1 := by rcases hd_loc_w with h | h <;> [right; left] <;> omega
    rw [hfr1 _ h1, hfr1 _ h2]; exact hG_iff.2.2 j hj
  refine runs_seq_assign_le (v := es.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth1 29 (by decide)).trans hr29))
      (Expr.eval_const (by omega)) (by omega)) hG1_m) ?_
  refine runs_seq_store_le (x := wRelA) (v := b)
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth1 32 (by decide), hr32]))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth1 4 (by decide), hr4])) ?_
  refine runs_seq_store_le (x := wRelA + 1) (v := es.length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth1 32 (by decide), hr32]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self])) ?_
  let mem2 := Function.update (Function.update st1.mem wRelA b) (wRelA + 1) es.length
  let st2 : State := { mem := mem2, regs := Function.update st1.regs 34 es.length, pos := st1.pos }
  let Inv2 : ℕ → State → Prop := fun j st =>
    st.regs 33 = j ∧
    (∀ r < 33, st.regs r = st₀.regs r) ∧
    st.regs 34 = es.length ∧
    st.pos = st₀.pos ∧
    MemFrame mem2 st.mem (wRelA + 2) (wRelA + 2 + 2 * es.length) ∧
    (∀ e, e < j → ∀ (hem : e < es.length),
      st.mem (wRelA + 2 + 2 * e) = verts.idxOf (es[e]'hem).1 ∧
      st.mem (wRelA + 2 + 2 * e + 1) = verts.idxOf (es[e]'hem).2)
  have hloop2 : Triple w p (fun st => st = st2)
      (forRange 33 (.const 0) (.reg 34) (seqStmts [
        .assign 35 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 33))),
        .assign 36 (.load (.bin .add (.reg 29) (.reg 35))),
        .assign 37 (.load (.bin .add (.bin .add (.reg 29) (.reg 35)) (.const 1))),
        .store (.bin .add (.reg 32) (.reg 35)) (.load (.bin .add (.reg 8) (.reg 36))),
        .store (.bin .add (.bin .add (.reg 32) (.reg 35)) (.const 1)) (.load (.bin .add (.reg 8) (.reg 37)))
      ]))
      (normalPost (Inv2 es.length))
      (fun _ => 68 * es.length + 20) := by
    have hl := Triple.forRange_const (w := w) (p := p) (r := 33) (lo := .const 0) (hi := .reg 34)
      (body := seqStmts [
        .assign 35 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 33))),
        .assign 36 (.load (.bin .add (.reg 29) (.reg 35))),
        .assign 37 (.load (.bin .add (.bin .add (.reg 29) (.reg 35)) (.const 1))),
        .store (.bin .add (.reg 32) (.reg 35)) (.load (.bin .add (.reg 8) (.reg 36))),
        .store (.bin .add (.bin .add (.reg 32) (.reg 35)) (.const 1)) (.load (.bin .add (.reg 8) (.reg 37)))
      ])
      (P := fun st => st = st2) (Inv := Inv2) 56 0 es.length (Nat.zero_le _) (by omega) (fun _ => hm_w)
      (fun st hs => by
        subst hs
        refine ⟨Expr.eval_const (by omega), by simp,
          fun r hr => by dsimp only [st2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth1 r (by omega)],
          by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_self],
          hpos1, memFrame_refl _ _ _, fun _ he => absurd he (Nat.not_lt_zero _)⟩)
      (fun _ _ _ _ hInv => hInv.1)
      (fun _ _ _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
      (fun j _ hj => by
        intro st ω ⟨hr33, hlt33, hr34, hpos, hfr2, hed2⟩
        have he_mem := hes (es[j]'hj) (List.getElem_mem hj)
        have hu_mem : (es[j]'hj).1 ∈ verts := List.mem_toFinset.mp he_mem.1
        have hv_mem : (es[j]'hj).2 ∈ verts := List.mem_toFinset.mp he_mem.2
        have hu_lt : (es[j]'hj).1 < n := hsub _ hu_mem
        have hv_lt : (es[j]'hj).2 < n := hsub _ hv_mem
        have hu_idx : verts.idxOf (es[j]'hj).1 < b := hlen ▸ List.idxOf_lt_length_of_mem hu_mem
        have hv_idx : verts.idxOf (es[j]'hj).2 < b := hlen ▸ List.idxOf_lt_length_of_mem hv_mem
        have hread_u : st.mem (wAddr + (2 + 2 * j)) = (es[j]'hj).1 := by
          have ha : wAddr + (2 + 2 * j) = wAddr + 2 + 2 * j := by omega
          rw [ha, hfr2 _ (by rcases hd_rel_w with h | h <;> [right; left] <;> omega)]
          dsimp only [mem2]
          rw [Function.update_of_ne (by rcases hd_rel_w with h | h <;> omega),
            Function.update_of_ne (by rcases hd_rel_w with h | h <;> omega)]
          exact (hG1_e j hj).1
        have hread_v : st.mem (wAddr + (2 + 2 * j) + 1) = (es[j]'hj).2 := by
          have ha : wAddr + (2 + 2 * j) + 1 = wAddr + 2 + 2 * j + 1 := by omega
          rw [ha, hfr2 _ (by rcases hd_rel_w with h | h <;> [right; left] <;> omega)]
          dsimp only [mem2]
          rw [Function.update_of_ne (by rcases hd_rel_w with h | h <;> omega),
            Function.update_of_ne (by rcases hd_rel_w with h | h <;> omega)]
          exact (hG1_e j hj).2
        have hloc_u : st.mem (locA + (es[j]'hj).1) = verts.idxOf (es[j]'hj).1 := by
          rw [hfr2 _ (by rcases hd_loc_rel with h | h <;> [left; right] <;> omega)]
          dsimp only [mem2]
          rw [Function.update_of_ne (by rcases hd_loc_rel with h | h <;> omega),
            Function.update_of_ne (by rcases hd_loc_rel with h | h <;> omega)]
          exact hmap1 _ hu_mem
        have hloc_v : st.mem (locA + (es[j]'hj).2) = verts.idxOf (es[j]'hj).2 := by
          rw [hfr2 _ (by rcases hd_loc_rel with h | h <;> [left; right] <;> omega)]
          dsimp only [mem2]
          rw [Function.update_of_ne (by rcases hd_loc_rel with h | h <;> omega),
            Function.update_of_ne (by rcases hd_loc_rel with h | h <;> omega)]
          exact hmap1 _ hv_mem
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := 2 + 2 * j)
          (Expr.eval_add (Expr.eval_const (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr33) (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := (es[j]'hj).1)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hlt33 29 (by decide), hr29]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) hread_u) ?_
        refine runs_seq_assign_le (v := (es[j]'hj).2)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 29 (by decide), hr29]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
            (Expr.eval_const (by omega)) (by omega)) hread_v) ?_
        refine runs_seq_store_le (x := wRelA + (2 + 2 * j)) (v := verts.idxOf (es[j]'hj).1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 32 (by decide), hr32]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])) (by omega))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 8 (by decide), hr8]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega)) hloc_u) ?_
        have hloc_v' : Function.update st.mem (wRelA + (2 + 2 * j)) (verts.idxOf (es[j]'hj).1) (locA + (es[j]'hj).2) =
            verts.idxOf (es[j]'hj).2 := by
          rw [Function.update_of_ne (by rcases hd_loc_rel with h | h <;> omega)]; exact hloc_v
        refine runs_store_le (x := wRelA + (2 + 2 * j) + 1) (v := verts.idxOf (es[j]'hj).2)
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 32 (by decide), hr32]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 8 (by decide), hr8]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) hloc_v') ?_ (by simp only [Expr.size]; omega)
        refine ⟨⟨by simp,
          fun r hr => by
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), hlt33 r hr],
          by simp [hr34],
          hpos,
          fun a ha => by
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr2 a ha,
          fun e he hem => ?_⟩, by simp [hr33]⟩
        dsimp only
        by_cases hej : e = j
        · subst hej
          have ha1 : wRelA + 2 + 2 * e = wRelA + (2 + 2 * e) := by omega
          rw [ha1]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self], by rw [Function.update_self]⟩
        · exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hed2 e (by omega) hem).1,
            by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hed2 e (by omega) hem).2⟩)
    exact hl.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => by simp only [Expr.size]; omega)
  refine runs_seq_triple_le hloop2 rfl ?_
  intro st3 ⟨_, hlt33_3, _, hpos3, hfr3, hed3⟩
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st4 : State := { mem := st3.mem, regs := Function.update st3.regs 35 0, pos := st3.pos }
  have hlat3 : ListAt st3.mem blkA verts := fun i hi => by
    have h1 : blkA + i < wRelA + 2 ∨ wRelA + 2 + 2 * es.length ≤ blkA + i := by rcases hd_rel_blk with h | h <;> [right; left] <;> omega
    have h2 : blkA + i ≠ wRelA + 1 := by rcases hd_rel_blk with h | h <;> omega
    have h3 : blkA + i ≠ wRelA := by rcases hd_rel_blk with h | h <;> omega
    have h4 : blkA + i < locA ∨ locA + n ≤ blkA + i := by rcases hd_loc_blk with h | h <;> [right; left] <;> omega
    rw [hfr3 _ h1]; dsimp only [mem2]; rw [Function.update_of_ne h2, Function.update_of_ne h3, hfr1 _ h4]
    exact hlat i hi
  refine runs_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := b) (sa := blkA) (la := locA) (val := 0)
      (rSrc := 28) (rLen := 4) (rLoc := 8) (rVal := 35) (rI := 33) (rU := 34) (by decide)
      p st3.mem verts st4 hlen hlat3 hsub hd_loc_blk hblk_w hloc_w hw16
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hlt33_3 28 (by decide), hr28])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hlt33_3 4 (by decide), hr4])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hlt33_3 8 (by decide), hr8])
      (by dsimp only [st4]; rw [Function.update_self]) rfl) rfl ?_ (by simp only [Expr.size]; omega)
  rintro (_ | _) st5 h5
  · rcases h5 with ⟨hoth5, hpos5, hfr5, hloc5⟩
    refine ⟨fun r hr => by
        rw [hoth5 r (by omega) (by omega)]; dsimp only [st4]
        rw [Function.update_of_ne (by omega), hlt33_3 r hr],
      hpos5.trans hpos3,
      fun u hu => by
        rw [hloc5 u hu]
        by_cases hmem_v : u ∈ verts.toFinset
        · simp [hmem_v]
        · simp only [hmem_v, ite_false]
          have h1 : locA + u < wRelA + 2 ∨ wRelA + 2 + 2 * es.length ≤ locA + u := by rcases hd_loc_rel with h | h <;> [left; right] <;> omega
          have h2 : locA + u ≠ wRelA + 1 := by rcases hd_loc_rel with h | h <;> omega
          have h3 : locA + u ≠ wRelA := by rcases hd_loc_rel with h | h <;> omega
          rw [hfr3 _ h1]; dsimp only [mem2]; rw [Function.update_of_ne h2, Function.update_of_ne h3]
          rw [hnot1 u hu (fun hv => hmem_v (List.mem_toFinset.mpr hv)), hloc0 u hu],
      fun a ha_loc ha_rel => by
        rw [hfr5 a ha_loc, hfr3 a (by omega)]
        dsimp only [mem2]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfr1 a ha_loc],
      by
        rw [relabelGraph, graphAt_mk_iff]
        have hdisj_rel : ∀ a, wRelA ≤ a → a < wRelA + 2 + 2 * es.length → st5.mem a = st3.mem a := fun a h1 h2 =>
          hfr5 a (by rcases hd_loc_rel with h | h <;> [right; left] <;> omega)
        refine ⟨by rw [hdisj_rel wRelA (by omega) (by omega), hfr3 wRelA (Or.inl (by omega))]
                   dsimp only [mem2]; rw [Function.update_of_ne (by omega), Function.update_self, hlen],
          by rw [hdisj_rel (wRelA + 1) (by omega) (by omega), hfr3 (wRelA + 1) (Or.inl (by omega))]
             dsimp only [mem2]; rw [Function.update_self, relabelEdges, List.length_map],
          fun j hj => by
            simp only [relabelEdges, List.length_map] at hj
            simp only [relabelEdges, List.getElem_map]
            rw [hdisj_rel (wRelA + 2 + 2 * j) (by omega) (by omega),
              hdisj_rel (wRelA + 2 + 2 * j + 1) (by omega) (by omega)]
            exact hed3 j hj hj⟩⟩
  · exact h5

/-! ## 3. Word-RAM In-Place Output Lifting (`sbLiftOutStmt`) -/

/-- Lifts `CoreOutAt mem subOutA res'` in place by replacing each vertex index `idx` at
`subOutA + 2 + i` with `mem[blkA + idx]` (`r28 = blkA`, `r30 = subOutA`).
Uses scratch `r33..r36`; preserves `r < 33`. -/
def sbLiftOutStmt : Stmt :=
  seqStmts [
    .assign 34 (.load (.bin .add (.reg 30) (.const 1))),
    forRange 33 (.const 0) (.reg 34) (seqStmts [
      .assign 35 (.bin .add (.bin .add (.reg 30) (.const 2)) (.reg 33)),
      .assign 36 (.load (.reg 35)),
      .store (.reg 35) (.load (.bin .add (.reg 28) (.reg 36)))
    ])
  ]

theorem sbLiftOutStmt_noRand : sbLiftOutStmt.NoRand := by
  simp [sbLiftOutStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Triple for `sbLiftOutStmt`: transforms `CoreOutAt mem subOutA res'` (for `res'` on
`Finset.range b`) in place into `CoreOutAt mem' subOutA (liftCoreResult verts res')` in
`≤ 45 * b + 35` steps. -/
theorem sbLiftOut_triple {w b blkA subOutA : ℕ}
    {p : Program} {mem : ℕ → ℕ} {verts : List ℕ} {res' : CoreResult} {st₀ : State}
    (hlen : verts.length = b) (hnd : verts.Nodup)
    (hlat : ListAt mem blkA verts)
    (hOut : CoreOutAt mem subOutA res')
    (hsub : match res' with | .cut U' => U' ⊆ Finset.range b | .expander S' => S' ⊆ Finset.range b)
    (hd_out_blk : DisjointRange subOutA (2 + b) blkA b)
    (hblk_w : blkA + b < 2 ^ w) (hout_w : subOutA + 2 + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr28 : st₀.regs 28 = blkA) (hr30 : st₀.regs 30 = subOutA) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbLiftOutStmt
      (normalPost fun st' =>
        (∀ r < 33, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem (subOutA + 2) (subOutA + 2 + b) ∧
        CoreOutAt st'.mem subOutA (liftCoreResult verts res'))
      (fun _ => 45 * b + 35) := by
  have hExt : ∃ (ls : List ℕ), ls.Nodup ∧ ls.length ≤ b ∧
      mem (subOutA + 1) = ls.length ∧ ListAt mem (subOutA + 2) ls ∧
      (∀ u ∈ ls, u < b) ∧
      (match res' with
       | .cut U' => mem subOutA = 0 ∧ ls.toFinset = U'
       | .expander S' => mem subOutA = 1 ∧ ls.toFinset = S') := by
    cases res' with
    | cut U' =>
      rcases hOut with ⟨htag, ls, hnd_l, hfin_l, hlm, hlat_l⟩
      have hlen_le : ls.length ≤ b := by
        rw [← List.toFinset_card_of_nodup hnd_l, hfin_l]
        exact (Finset.card_le_card hsub).trans (by simp)
      exact ⟨ls, hnd_l, hlen_le, hlm, hlat_l,
        fun u hu => Finset.mem_range.mp (hsub (hfin_l ▸ List.mem_toFinset.mpr hu)), htag, hfin_l⟩
    | expander S' =>
      rcases hOut with ⟨htag, ls, hnd_l, hfin_l, hlm, hlat_l⟩
      have hlen_le : ls.length ≤ b := by
        rw [← List.toFinset_card_of_nodup hnd_l, hfin_l]
        exact (Finset.card_le_card hsub).trans (by simp)
      exact ⟨ls, hnd_l, hlen_le, hlm, hlat_l,
        fun u hu => Finset.mem_range.mp (hsub (hfin_l ▸ List.mem_toFinset.mpr hu)), htag, hfin_l⟩
  rcases hExt with ⟨ls, hnd_ls, hls_le, hlen_mem, hlat_ls, hls_lt, hres_info⟩
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbLiftOutStmt, seqStmts]
  refine runs_seq_assign_le (v := ls.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr30) (Expr.eval_const (by omega)) (by omega))
      (by rw [hmem, hlen_mem])) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 34 ls.length, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 33 = j ∧
    (∀ r < 33, st.regs r = st₀.regs r) ∧
    st.regs 34 = ls.length ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem (subOutA + 2) (subOutA + 2 + j) ∧
    (∀ i, i < j → ∀ (hil : i < ls.length), st.mem (subOutA + 2 + i) = verts.getD (ls[i]'hil) 0)
  have hloop : Triple w p (fun st => st = st1)
      (forRange 33 (.const 0) (.reg 34) (seqStmts [
        .assign 35 (.bin .add (.bin .add (.reg 30) (.const 2)) (.reg 33)),
        .assign 36 (.load (.reg 35)),
        .store (.reg 35) (.load (.bin .add (.reg 28) (.reg 36)))
      ]))
      (normalPost (Inv ls.length))
      (fun _ => 44 * ls.length + 20) := by
    have hl := Triple.forRange_const (w := w) (p := p) (r := 33) (lo := .const 0) (hi := .reg 34)
      (body := seqStmts [
        .assign 35 (.bin .add (.bin .add (.reg 30) (.const 2)) (.reg 33)),
        .assign 36 (.load (.reg 35)),
        .store (.reg 35) (.load (.bin .add (.reg 28) (.reg 36)))
      ])
      (P := fun st => st = st1) (Inv := Inv) 32 0 ls.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hs => by
        subst hs
        refine ⟨Expr.eval_const (by omega), by simp,
          fun r hr => by dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
          by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self],
          rfl, hmem ▸ memFrame_refl _ _ _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩)
      (fun _ _ _ _ hInv => hInv.1)
      (fun _ _ _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
      (fun j _ hj => by
        intro st ω ⟨hr33, hlt33, hr34, hpos, hfr, hlifted⟩
        have hidx_lt : ls[j]'hj < b := hls_lt _ (List.getElem_mem hj)
        have hread_idx : st.mem (subOutA + 2 + j) = ls[j]'hj := by
          rw [hfr _ (Or.inr (le_refl _))]; exact hlat_ls j hj
        have hread_v : st.mem (blkA + ls[j]'hj) = verts[ls[j]'hj]'(hlen.symm ▸ hidx_lt) := by
          rw [hfr _ (by rcases hd_out_blk with h | h <;> [right; left] <;> omega)]
          exact hlat (ls[j]'hj) (hlen.symm ▸ hidx_lt)
        have hgetD_eq : verts[ls[j]'hj]'(hlen.symm ▸ hidx_lt) = verts.getD (ls[j]'hj) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen.symm ▸ hidx_lt), Option.getD_some]
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := subOutA + 2 + j)
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hlt33 30 (by decide)).trans hr30))
            (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq hr33) (by omega)) ?_
        refine runs_seq_assign_le (v := ls[j]'hj)
          (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hread_idx) ?_
        refine runs_store_le (x := subOutA + 2 + j) (v := verts.getD (ls[j]'hj) 0)
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
          (Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hlt33 28 (by decide), hr28]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) (hgetD_eq ▸ hread_v)) ?_
          (by simp only [Expr.size]; omega)
        refine ⟨⟨by simp,
          fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hlt33 r hr],
          by simp [hr34],
          hpos,
          fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega),
          fun i hi hil => ?_⟩, by simp [hr33]⟩
        dsimp only
        by_cases hij : i = j
        · subst hij; rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hlifted i (by omega) hil)
    exact hl.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => by simp only [Expr.size]; omega)
  refine runs_triple_le hloop rfl ?_ (by simp only [Expr.size]; omega)
  rintro (_ | _) st' h'
  · rcases h' with ⟨_, hlt33, _, hpos, hfr, hlifted⟩
    have hfr_b : MemFrame mem st'.mem (subOutA + 2) (subOutA + 2 + b) := fun a ha =>
      hfr a (by omega)
    let ls' := ls.map fun idx => verts.getD idx 0
    have hnd_ls' : ls'.Nodup :=
      hnd_ls.map_on fun x hx y hy hxy =>
        nodup_getD_inj hnd (hlen.symm ▸ hls_lt x hx) (hlen.symm ▸ hls_lt y hy) hxy
    have hfin_ls' : ls'.toFinset = ls.toFinset.image (fun idx => verts.getD idx 0) := by
      ext x; simp [ls']
    have hlat_ls' : ListAt st'.mem (subOutA + 2) ls' := fun i hi => by
      simp only [ls', List.length_map] at hi
      simp only [ls', List.getElem_map]
      exact hlifted i hi hi
    have hlen_ls' : st'.mem (subOutA + 1) = ls'.length := by
      rw [hfr_b (subOutA + 1) (Or.inl (by omega)), hlen_mem, List.length_map]
    refine ⟨hlt33, hpos, hfr_b, ?_⟩
    cases res' with
    | cut U' =>
      refine ⟨by rw [hfr_b subOutA (Or.inl (by omega))]; exact hres_info.1,
        ls', hnd_ls', hfin_ls'.trans (by rw [hres_info.2]), hlen_ls', hlat_ls'⟩
    | expander S' =>
      refine ⟨by rw [hfr_b subOutA (Or.inl (by omega))]; exact hres_info.1,
        ls', hnd_ls', hfin_ls'.trans (by rw [hres_info.2]), hlen_ls', hlat_ls'⟩
  · exact h'

end MinCostFlow.ExpanderDecomp
