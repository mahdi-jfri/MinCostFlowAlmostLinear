module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepModel
public import MinCostFlow.SparseCore.Program.OutStepSpec

import MinCostFlow.LSF.Lemma54Split
import Mathlib.Tactic

/-!
# Forest-cut synchronization and `OutSplitPrefixAt` (`AssemblyFirstTourStepSync`)

Connects the individual Word-RAM tour operations (`tourOp 0` `applyEdits`, `tourOp 1` `cut`,
`tourOp 3` `changeRoot`, and P7's `outSmallSide`) to `canonSplitList`,
`restrictSplits keep (canonCoreBatch cs U)`, and `OutSplitListsAt`:

1. **`OutSplitPrefixAt`**: snoc-composable linked-list prefix predicate matching `outSmallSide`'s
   append-at-`last` mutation (`outSplitPrefixAt_nil`, `outSplitPrefixAt_snoc`,
   `outSplitPrefixAt_mono`, `outSplitPrefixAt_finish`).
2. **Forest-refinement helper (`tourCut_split_sync`)**: for any forest edge `e ∈ s.rf.F.E` and
   canonical new root `fresh` satisfying `L'.F = ⟨eraseForestEdge s.rf.F e, insert fresh s.rf.R⟩`,
   proves `TourValid`, `TourMarksAt`, `TourKeepMatch` with `S' = S.applyUpdate (.split kept fresh ...)`,
   and the partition equations (`hother`, `hunion`) for `tourMarkPot_split_step`.
3. **Vertex-split + `changeRoot` helper (`tourMove_changeRoot_sync`)**: for `u = .split v v' St Sh`
   with `edit = .moveEnds v v' sel c` matching `splitEnds St Sh`, proves that `rTmp := if v' ∈ s₁.rf.R
   then v' else v` is connected to `fresh` in `s₁.rf.F`, `tourChangeRoot s₁ rTmp fresh` equals
   `(inputMid cs u).F` (up to `GraphEq`), and `tourMarkPot_split_step` applies.
4. **Release-prefix commutation (`tourStep_nonForest_commute`)**: proves that `.insert` and
   non-forest `.delete` preserve `TourValid`, `TourMarksAt`, `TourKeepMatch`, and `keep`-src
   agreement on top of any already-cut release forest `rf_ahead`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. Snoc-composable `OutSplitPrefixAt` linked-list builder -/

@[expose] public section

/-- Continuation-style prefix of `OutSplitListsAt`: for any valid tail `OutSplitListsAt` starting at
`mem (last + 4)` (when `last ≠ 0`) or `0` (when `last = 0`), the full list starting at `splitPtr`
satisfies `OutSplitListsAt`. Also tracks `last = 0 ↔ P_done = []`, `last ≠ 0 → last + 4 < top`,
`last ≠ 0 → mem (last + 4) = 0`, and that every cell of every record/list lies strictly below `top`
and outside `avoid`. -/
def OutSplitPrefixAt (mem : ℕ → ℕ) (splitPtr last top : ℕ) (avoid : ℕ → Prop)
    (keep E₀ : Finset ℕ) (G₀ : MGraph) (P_done : List Update) (G_cur : MGraph)
    (Ys_done : List (List End)) : Prop :=
  G_cur = G₀.applyBatch P_done ∧
  (P_done = [] → splitPtr = 0 ∧ last = 0 ∧ Ys_done = []) ∧
  (P_done ≠ [] → 0 < splitPtr ∧ 0 < last ∧ last + 5 ≤ top ∧ ¬ avoid (last + 4) ∧
    mem (last + 4) = 0) ∧
  (∀ (mem' : ℕ → ℕ) (top' : ℕ) (avoid' : ℕ → Prop) (nextPtr : ℕ)
      (P_rest : List Update) (Ys_rest : List (List End)),
    top ≤ top' →
    (∀ a < top, ¬ avoid a → avoid' a → False) →
    (∀ a < top, ¬ avoid a → (last = 0 ∨ a ≠ last + 4) → mem' a = mem a) →
    (last ≠ 0 → mem' (last + 4) = nextPtr) →
    OutSplitListsAt mem' top' avoid' keep E₀ nextPtr G_cur P_rest Ys_rest →
    OutSplitListsAt mem' top' avoid' keep E₀ (if splitPtr = 0 then nextPtr else splitPtr)
      G₀ (P_done ++ P_rest) (Ys_done ++ Ys_rest))

end

public section

theorem outSplitPrefixAt_nil (mem : ℕ → ℕ) (top : ℕ) (avoid : ℕ → Prop)
    (keep E₀ : Finset ℕ) (G₀ : MGraph) :
    OutSplitPrefixAt mem 0 0 top avoid keep E₀ G₀ [] G₀ [] := by
  refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h => (h rfl).elim, ?_⟩
  intro mem' top' avoid' nextPtr P_rest Ys_rest _ _ _ _ hrest
  simpa using hrest

/-- Frame preservation for `OutSplitPrefixAt` when `mem'` agrees with `mem` on `< top` outside
`avoid`, `top ≤ top'`, and `avoid'` adds no cells below `top` outside `avoid`. -/
theorem outSplitPrefixAt_mono {mem mem' : ℕ → ℕ} {splitPtr last top top' : ℕ}
    {avoid avoid' : ℕ → Prop} {keep E₀ : Finset ℕ} {G₀ G_cur : MGraph}
    {P_done : List Update} {Ys_done : List (List End)}
    (h : OutSplitPrefixAt mem splitPtr last top avoid keep E₀ G₀ P_done G_cur Ys_done)
    (htop : top ≤ top')
    (hav : ∀ a < top, ¬ avoid a → ¬ avoid' a)
    (hfr : ∀ a < top, ¬ avoid a → mem' a = mem a) :
    OutSplitPrefixAt mem' splitPtr last top' avoid' keep E₀ G₀ P_done G_cur Ys_done := by
  obtain ⟨hG, hnil, hne, hcont⟩ := h
  refine ⟨hG, hnil, fun hP => ?_, ?_⟩
  · obtain ⟨hs, hl, hl5, hlav, hmz⟩ := hne hP
    exact ⟨hs, hl, by omega, hav (last + 4) (by omega) hlav,
      (hfr (last + 4) (by omega) hlav).trans hmz⟩
  · intro mem'' top'' avoid'' nextPtr P_rest Ys_rest htop2 hav2 hfr2 hpatch hrest
    exact hcont mem'' top'' avoid'' nextPtr P_rest Ys_rest (htop.trans htop2)
      (fun a ha hna => hav2 a (lt_of_lt_of_le ha htop) (hav a ha hna))
      (fun a ha hna hneL => (hfr2 a (lt_of_lt_of_le ha htop) (hav a ha hna) hneL).trans (hfr a ha hna))
      hpatch hrest

/-- Append one `outSmallSide` record written at `recPtr` (`top ≤ recPtr`) to `OutSplitPrefixAt`. -/
theorem outSplitPrefixAt_snoc {mem mem' : ℕ → ℕ} {splitPtr last top recPtr top' : ℕ}
    {avoid avoid' : ℕ → Prop} {keep E₀ : Finset ℕ} {G₀ G_cur : MGraph}
    {P_done : List Update} {Ys_done : List (List End)}
    {v v' side ptr : ℕ} {St Sh : Finset ℕ} {Y : List End}
    (h : OutSplitPrefixAt mem splitPtr last top avoid keep E₀ G₀ P_done G_cur Ys_done)
    (hrec_pos : 0 < recPtr) (htop_le : top ≤ recPtr) (hrec5 : recPtr + 5 ≤ ptr)
    (hptr_end : ptr + 1 + Y.length ≤ top')
    (hav_old : ∀ a < top, ¬ avoid a → ¬ avoid' a)
    (hav_rec : ∀ i < 5, ¬ avoid' (recPtr + i))
    (hav_Y : ∀ i < 1 + Y.length, ¬ avoid' (ptr + i))
    (hfr : ∀ a < top, ¬ avoid a → (last = 0 ∨ a ≠ last + 4) → mem' a = mem a)
    (hpatch : last ≠ 0 → mem' (last + 4) = recPtr)
    (hv_mem : mem' recPtr = v) (hv'_mem : mem' (recPtr + 1) = v')
    (hside_mem : mem' (recPtr + 2) = side) (hside_le : side ≤ 1)
    (hptr_mem : mem' (recPtr + 3) = ptr) (hnext_mem : mem' (recPtr + 4) = 0)
    (hEL : EndListAt mem' ptr Y) (hnd : Y.Nodup) (hYE : ∀ x ∈ Y, x.1 ∈ E₀)
    (hkeep : ∀ x : End, x.1 ∈ keep →
      (x ∈ Y ↔ (G_cur.applyUpdate (.split v v' St Sh)).src x = if side = 0 then v else v')) :
    let splitPtr' := if splitPtr = 0 then recPtr else splitPtr
    OutSplitPrefixAt mem' splitPtr' recPtr top' avoid' keep E₀ G₀
      (P_done ++ [.split v v' St Sh]) (G_cur.applyUpdate (.split v v' St Sh)) (Ys_done ++ [Y]) := by
  intro splitPtr'
  obtain ⟨hG, hnil, hne, hcont⟩ := h
  refine ⟨by simp [MGraph.applyBatch, List.foldl_append, hG],
    fun hEq => by simp at hEq,
    fun _ => ⟨by dsimp only [splitPtr']; split_ifs with hz; exact hrec_pos; exact Nat.pos_of_ne_zero hz,
      hrec_pos, by omega, hav_rec 4 (by decide), hnext_mem⟩, ?_⟩
  intro mem'' top'' avoid'' nextPtr P_rest Ys_rest htop2 hav2 hfr2 hpatch2 hrest
  have hrec_lt_top' : recPtr + 5 ≤ top' := by omega
  have hkeep_rec : ∀ i < 4, mem'' (recPtr + i) = mem' (recPtr + i) := fun i hi =>
    hfr2 (recPtr + i) (by omega) (hav_rec i (by omega)) (Or.inr (by omega))
  have hkeep_Y : ∀ i < 1 + Y.length, mem'' (ptr + i) = mem' (ptr + i) := fun i hi =>
    hfr2 (ptr + i) (by omega) (hav_Y i hi) (Or.inr (by omega))
  have hEL'' : EndListAt mem'' ptr Y := by
    refine ⟨(hkeep_Y 0 (by omega)).trans hEL.1, fun i hi => ?_⟩
    have h1 := hkeep_Y (1 + i) (by omega)
    rw [← Nat.add_assoc] at h1
    exact h1.trans (hEL.2 i hi)
  have hnext'' : mem'' (recPtr + 4) = nextPtr := hpatch2 (Nat.ne_of_gt hrec_pos)
  have h1 : OutSplitListsAt mem'' top'' avoid'' keep E₀ recPtr G_cur
      (.split v v' St Sh :: P_rest) (Y :: Ys_rest) := by
    refine ⟨hrec_pos, by omega, fun i hi => hav2 (recPtr + i) (by omega) (hav_rec i hi),
      (hkeep_rec 0 (by decide)).trans hv_mem,
      (hkeep_rec 1 (by decide)).trans hv'_mem,
      by rw [(hkeep_rec 2 (by decide)).trans hside_mem]; exact hside_le,
      by rw [(hkeep_rec 3 (by decide)).trans hptr_mem]; exact hEL'',
      by rw [(hkeep_rec 3 (by decide)).trans hptr_mem]; omega,
      by rw [(hkeep_rec 3 (by decide)).trans hptr_mem]; exact fun i hi => hav2 (ptr + i) (by omega) (hav_Y i hi),
      hnd, hYE,
      by rw [(hkeep_rec 2 (by decide)).trans hside_mem]; exact hkeep,
      by rw [hnext'']; exact hrest⟩
  have hsp_ne : splitPtr' ≠ 0 := by
    dsimp only [splitPtr']; split_ifs with hz
    · exact Nat.ne_of_gt hrec_pos
    · exact hz
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append]
  have hres := hcont mem'' top'' avoid'' recPtr (.split v v' St Sh :: P_rest) (Y :: Ys_rest)
    (by omega)
    (fun a ha hna => hav2 a (by omega) (hav_old a ha hna))
    (fun a ha hna hneL =>
      (hfr2 a (by omega) (hav_old a ha hna) (Or.inr (by omega))).trans (hfr a ha hna hneL))
    (fun hlast => by
      have hlt_last : last + 4 < top := by
        by_cases hP : P_done = []
        · exact absurd (hnil hP).2.1 hlast
        · have := (hne hP).2.2.1; omega
      have hlav : ¬ avoid (last + 4) := by
        by_cases hP : P_done = []
        · exact absurd (hnil hP).2.1 hlast
        · exact (hne hP).2.2.2.1
      exact (hfr2 (last + 4) (by omega) (hav_old _ hlt_last hlav) (Or.inr (by omega))).trans (hpatch hlast))
    h1
  simpa only [splitPtr', hsp_ne, ↓reduceIte] using hres

/-- Finish an `OutSplitPrefixAt` into `OutSplitListsAt` at the end of the step. -/
theorem outSplitPrefixAt_finish {mem : ℕ → ℕ} {splitPtr last top : ℕ} {avoid : ℕ → Prop}
    {keep E₀ : Finset ℕ} {G₀ G_cur : MGraph} {P_done : List Update} {Ys_done : List (List End)}
    (h : OutSplitPrefixAt mem splitPtr last top avoid keep E₀ G₀ P_done G_cur Ys_done) :
    OutSplitListsAt mem top avoid keep E₀ splitPtr G₀ P_done Ys_done := by
  obtain ⟨_, hnil, hne, hcont⟩ := h
  have hres := hcont mem top avoid 0 [] [] (le_refl _) (fun _ _ hna ha => hna ha)
    (fun _ _ _ _ => rfl)
    (fun hlast => by
      by_cases hP : P_done = []
      · exact absurd (hnil hP).2.1 hlast
      · exact (hne hP).2.2.2.2)
    rfl
  simp only [List.append_nil] at hres
  by_cases hs0 : splitPtr = 0
  · simpa [hs0] using hres
  · simpa [hs0] using hres

end

/-! ## 2. Forest-cut and vertex-split synchronization lemmas -/

public section

/-- Connectedness in `eraseForestEdge F e` implies connectedness in `F`. -/
private lemma connected_of_eraseForestEdge {F : MGraph} {e u v : ℕ}
    (h : (eraseForestEdge F e).Connected u v) : F.Connected u v :=
  connected_of_subgraph (eraseForestEdge_subgraph F e) h

/-- **Single forest cut (`tourCut s e fresh`) synchronization.**
When `s` holds `TourValid`, `TourMarksAt s M` (with `e ∉ M`), and `TourKeepMatch keep s S`,
cutting forest edge `e ∈ s.rf.F.E` with new root `fresh ∈ s.rf.F.V \ s.rf.R` such that
`kept = s.rf.root (s.rf.F.tail e)` and `insert fresh s.rf.R` uniquely roots `eraseForestEdge s.rf.F e`
preserves `TourValid` and `TourMarksAt`, updates `TourKeepMatch` by the restricted split
`split kept fresh (St ∩ keep) (Sh ∩ keep)`, and yields the partition equations of
`tourMarkPot_split_step`. -/
theorem tourCut_split_sync {vCap eCap e kept fresh : ℕ} {s : TourAbs}
    {keep M : Finset ℕ} {S : MGraph} {St Sh : Finset ℕ}
    (hv : TourValid vCap eCap s)
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S)
    (he : e ∈ s.rf.F.E) (heM : e ∉ M)
    (hkept_eq : kept = s.rf.root (s.rf.F.tail e))
    (hfreshV : fresh ∈ s.rf.F.V) (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh) :
    let s' := tourCut s e fresh
    let S' := S.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))
    TourValid vCap eCap s' ∧
    TourMarksAt s' M ∧
    TourKeepMatch keep s' S' ∧
    kept ∈ s.rf.R ∧
    (∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset) ∧
    (tourMarkedList s' kept).toFinset ∪ (tourMarkedList s' fresh).toFinset =
      (tourMarkedList s kept).toFinset := by
  intro s' S'
  have hv' : TourValid vCap eCap s' := tourValid_cut hv he hfreshV huniq'
  have htailV : s.rf.F.tail e ∈ s.rf.F.V := (hv.compat.forest.1 e he).1
  have hkeptR : kept ∈ s.rf.R := by
    rw [hkept_eq]
    obtain ⟨r, ⟨hrR, hc⟩, huniq⟩ := hv.unique_root _ htailV
    have hreq : s.rf.root (s.rf.F.tail e) = r := hv.root_eq_of_mem htailV hrR hc
    rw [hreq]; exact hrR
  have hM' : TourMarksAt s' M := by
    intro z
    change z ∈ s.marked ↔ (∃ v, z ∈ s.ord v) ∧ z.1 ∉ s.rf.F.E.erase e ∧ z.1 ∈ M
    rw [hM z]
    constructor
    · rintro ⟨hact, hopen, hzM⟩
      exact ⟨hact, fun h => hopen (Finset.mem_of_mem_erase h), hzM⟩
    · rintro ⟨hact, hopen, hzM⟩
      refine ⟨hact, fun h => ?_, hzM⟩
      have hne : z.1 ≠ e := fun heq => heM (heq ▸ hzM)
      exact hopen (Finset.mem_erase.mpr ⟨hne, h⟩)
  -- Root movement under `tourCut`: every vertex keeps its old root OR moves from `kept` to `fresh`.
  have hroot_move : ∀ v ∈ s.rf.F.V,
      (s'.rf.root v = s.rf.root v) ∨ (s.rf.root v = kept ∧ s'.rf.root v = fresh) := by
    intro v hvV
    obtain ⟨r', ⟨hr'R, hvr'⟩, _⟩ := hv'.unique_root v hvV
    have hreq' : s'.rf.root v = r' := hv'.root_eq_of_mem hvV hr'R hvr'
    rw [hreq']
    have hvr_old : s.rf.F.Connected v r' := connected_of_eraseForestEdge hvr'
    rcases Finset.mem_insert.mp hr'R with rfl | hr'Old
    · -- `r' = fresh`: show `s.rf.root v = kept`.
      obtain ⟨_, _, _, hconn_kf, _⟩ := cut_component_partition hv he hfreshV hfreshNotR huniq'
      have hvf : s.rf.F.Connected v kept := connected_trans hvr_old (connected_symm (hkept_eq ▸ hconn_kf))
      exact Or.inr ⟨hv.root_eq_of_mem hvV hkeptR hvf, rfl⟩
    · exact Or.inl (hv.root_eq_of_mem hvV hr'Old hvr_old).symm
  have hK' : TourKeepMatch keep s' S' := by
    refine ⟨hK.1, fun x hx => ?_⟩
    obtain ⟨⟨v, hxv⟩, hopen, hrt⟩ := hK.2 x hx
    have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hxv)
    have hsrc_v : ordSrc s.ord x = v := hv.compat.ordSrc_eq hxv
    refine ⟨⟨v, hxv⟩, fun h => hopen (Finset.mem_of_mem_erase h), ?_⟩
    change s'.rf.root (ordSrc s.ord x) = S'.src x
    rw [src_applyUpdate_split]
    have hcond_iff :
        ((if x.2 then x.1 ∈ St ∩ keep else x.1 ∈ Sh ∩ keep) ∧ S.src x = kept) ↔
        s'.rf.root (ordSrc s.ord x) = fresh := by
      have hxb : (if x.2 then x.1 ∈ St ∩ keep else x.1 ∈ Sh ∩ keep) ↔
          s'.rf.root (ordSrc s.ord x) = fresh := by
        obtain ⟨f, b⟩ := x
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_inter, hx, and_true]; exact hSh f hx
        · simp only [↓reduceIte, Finset.mem_inter, hx, and_true]; exact hSt f hx
      rw [hxb]
      constructor
      · exact And.left
      · intro hf
        refine ⟨hf, ?_⟩
        rw [← hrt, hsrc_v]
        rcases hroot_move v hvV with hsame | ⟨hwas, _⟩
        · exfalso
          rw [hsrc_v, hsame] at hf
          obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root v hvV
          have hreq := hv.root_eq_of_mem hvV hrR hvr
          exact hfreshNotR (hf ▸ hreq ▸ hrR)
        · exact hwas
    by_cases hf : s'.rf.root (ordSrc s.ord x) = fresh
    · rw [ite_eq_left (hcond_iff.mpr hf)]; exact hf
    · rw [ite_eq_right (fun h => hf (hcond_iff.mp h)), ← hrt, hsrc_v]
      rcases hroot_move v hvV with hsame | ⟨_, hfr⟩
      · exact hsame
      · exact absurd (hsrc_v ▸ hfr) hf
  have hother : ∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset := by
    intro r hrR hrne
    ext z
    rw [List.mem_toFinset, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
      mem_tourMarkedList_iff hv hM]
    have hrR' : r ∈ s'.rf.R := Finset.mem_insert_of_mem hrR
    have hrneF : r ≠ fresh := fun h => hfreshNotR (h ▸ hrR)
    constructor
    · rintro ⟨_, ⟨v, hzv⟩, hopen', hzM, hrt'⟩
      have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
      have hsrc : ordSrc s.ord z = v := hv.compat.ordSrc_eq hzv
      have hopen : z.1 ∉ s.rf.F.E := fun h => hopen' (Finset.mem_erase.mpr ⟨fun heq => heM (heq ▸ hzM), h⟩)
      refine ⟨hrR, ⟨v, hzv⟩, hopen, hzM, ?_⟩
      change s'.rf.root (ordSrc s.ord z) = r at hrt'
      rw [hsrc] at hrt' ⊢
      rcases hroot_move v hvV with hsame | ⟨_, hfr⟩
      · exact hsame.symm.trans hrt'
      · exact absurd (hrt'.symm.trans hfr) hrneF
    · rintro ⟨_, ⟨v, hzv⟩, hopen, hzM, hrt⟩
      have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
      have hsrc : ordSrc s.ord z = v := hv.compat.ordSrc_eq hzv
      refine ⟨hrR', ⟨v, hzv⟩, fun h => hopen (Finset.mem_of_mem_erase h), hzM, ?_⟩
      change s'.rf.root (ordSrc s.ord z) = r
      rw [hsrc] at hrt ⊢
      rcases hroot_move v hvV with hsame | ⟨hwas, _⟩
      · exact hsame.trans hrt
      · exact absurd (hrt.symm.trans hwas) hrne
  have hunion : (tourMarkedList s' kept).toFinset ∪ (tourMarkedList s' fresh).toFinset =
      (tourMarkedList s kept).toFinset := by
    ext z
    simp only [Finset.mem_union, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
      mem_tourMarkedList_iff hv hM]
    have hkeptR' : kept ∈ s'.rf.R := Finset.mem_insert_of_mem hkeptR
    have hfreshR' : fresh ∈ s'.rf.R := Finset.mem_insert_self _ _
    constructor
    · rintro (⟨_, ⟨v, hzv⟩, hopen', hzM, hrt'⟩ | ⟨_, ⟨v, hzv⟩, hopen', hzM, hrt'⟩)
      · have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
        have hsrc : ordSrc s.ord z = v := hv.compat.ordSrc_eq hzv
        have hopen : z.1 ∉ s.rf.F.E := fun h => hopen' (Finset.mem_erase.mpr ⟨fun heq => heM (heq ▸ hzM), h⟩)
        refine ⟨hkeptR, ⟨v, hzv⟩, hopen, hzM, ?_⟩
        change s'.rf.root (ordSrc s.ord z) = kept at hrt'
        rw [hsrc] at hrt' ⊢
        rcases hroot_move v hvV with hsame | ⟨hwas, _⟩
        · exact hsame.symm.trans hrt'
        · exact hwas
      · have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
        have hsrc : ordSrc s.ord z = v := hv.compat.ordSrc_eq hzv
        have hopen : z.1 ∉ s.rf.F.E := fun h => hopen' (Finset.mem_erase.mpr ⟨fun heq => heM (heq ▸ hzM), h⟩)
        refine ⟨hkeptR, ⟨v, hzv⟩, hopen, hzM, ?_⟩
        change s'.rf.root (ordSrc s.ord z) = fresh at hrt'
        rw [hsrc] at hrt' ⊢
        rcases hroot_move v hvV with hsame | ⟨hwas, _⟩
        · exfalso
          rw [hsame] at hrt'
          obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root v hvV
          exact hfreshNotR (hrt' ▸ hv.root_eq_of_mem hvV hrR hvr ▸ hrR)
        · exact hwas
    · rintro ⟨_, ⟨v, hzv⟩, hopen, hzM, hrt⟩
      have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
      have hsrc : ordSrc s.ord z = v := hv.compat.ordSrc_eq hzv
      have hopen' : z.1 ∉ s'.rf.F.E := fun h => hopen (Finset.mem_of_mem_erase h)
      rw [hsrc] at hrt
      rcases hroot_move v hvV with hsame | ⟨_, hfr⟩
      · exact Or.inl ⟨hkeptR', ⟨v, hzv⟩, hopen', hzM, by change s'.rf.root (ordSrc s.ord z) = kept; rw [hsrc, hsame, hrt]⟩
      · exact Or.inr ⟨hfreshR', ⟨v, hzv⟩, hopen', hzM, by change s'.rf.root (ordSrc s.ord z) = fresh; rw [hsrc, hfr]⟩
  exact ⟨hv', hM', hK', hkeptR, hother, hunion⟩

/-- **Vertex split (`.moveEnds` + `changeRoot`) synchronization.**
When `s` holds `TourValid`, `TourMarksAt s M`, and `TourKeepMatch keep s S`, applying
`edit = .moveEnds v v' sel c` (with `s₁ := tourApplyEdit s edit`) creates temporary root
`rTmp := if v' ∈ s₁.rf.R then v' else v`. Given `fresh` with `insert fresh s.rf.R` uniquely rooting
`s₁.rf.F` (the canonical roots of `inputMid cs (.split v v' At Ah)`), `rTmp` and `fresh` lie in the
same component of `s₁.rf.F`, `s' := tourChangeRoot s₁ rTmp fresh` has `s'.rf.R = insert fresh s.rf.R`,
preserves `TourValid` and `TourMarksAt`, updates `TourKeepMatch`, and gives the partition equations
for `tourMarkPot_split_step`. -/
theorem tourMove_changeRoot_sync {vCap eCap v v' kept fresh : ℕ}
    {sel : Finset End} {c : Bool} {s : TourAbs}
    {keep M : Finset ℕ} {S : MGraph} {St Sh : Finset ℕ}
    (hv : TourValid vCap eCap s)
    (hvalid1 : TourValid vCap eCap (tourApplyEdit s (.moveEnds v v' sel c)))
    (hEdit : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S)
    (hkept_eq : kept = s.rf.root v)
    (hfreshLt : fresh < vCap)
    (hfreshV : fresh ∈ (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.V)
    (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ w ∈ (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.Connected w r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔
      (tourChangeRoot (tourApplyEdit s (.moveEnds v v' sel c))
        (if v' ∈ (tourApplyEdit s (.moveEnds v v' sel c)).rf.R then v' else v) fresh).rf.root
        (ordSrc (tourApplyEdit s (.moveEnds v v' sel c)).ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔
      (tourChangeRoot (tourApplyEdit s (.moveEnds v v' sel c))
        (if v' ∈ (tourApplyEdit s (.moveEnds v v' sel c)).rf.R then v' else v) fresh).rf.root
        (ordSrc (tourApplyEdit s (.moveEnds v v' sel c)).ord (f, false)) = fresh) :
    let s₁ := tourApplyEdit s (.moveEnds v v' sel c)
    let rTmp := if v' ∈ s₁.rf.R then v' else v
    let s' := tourChangeRoot s₁ rTmp fresh
    let S' := S.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))
    rTmp ∈ s₁.rf.R ∧ rTmp ∉ s.rf.R ∧ s₁.rf.F.Connected rTmp fresh ∧
    s'.rf.R = insert fresh s.rf.R ∧
    TourValid vCap eCap s' ∧
    TourMarksAt s' M ∧
    TourKeepMatch keep s' S' ∧
    kept ∈ s.rf.R ∧
    (∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset) ∧
    (tourMarkedList s' kept).toFinset ∪ (tourMarkedList s' fresh).toFinset =
      (tourMarkedList s kept).toFinset := by
  intro s₁ rTmp s' S'
  classical
  obtain ⟨hvCap, hv'Cap, hvv', hvV, hv'NotV, hordv', _⟩ := hEdit
  have hkeptR : kept ∈ s.rf.R := by
    rw [hkept_eq]
    obtain ⟨r, ⟨hrR, hc⟩, _⟩ := hv.unique_root v hvV
    rw [hv.root_eq_of_mem hvV hrR hc]; exact hrR
  set moved := ((s.ord v).filter (movedBy sel c)).toFinset
  set StM := (moved.filter fun x => x.2).image Prod.fst
  set ShM := (moved.filter fun x => !x.2).image Prod.fst
  set F' := s.rf.F.applyUpdate (.split v v' StM ShM)
  set newR := if F'.Connected v (s.rf.root v) then v' else v
  have hs1F : s₁.rf.F = F' := rfl
  have hs1R : s₁.rf.R = insert newR s.rf.R := rfl
  have hv'NotR : v' ∉ s.rf.R := fun h => hv'NotV (hv.roots_sub h)
  have hrTmp_eq : rTmp = newR := by
    dsimp only [rTmp]
    rw [hs1R]
    by_cases hconn : F'.Connected v (s.rf.root v)
    · have hnr : newR = v' := ite_eq_left hconn
      rw [hnr]; simp
    · have hnr : newR = v := ite_eq_right hconn
      rw [hnr]
      have hv'NotIn : v' ∉ insert v s.rf.R := fun h => by
        rcases Finset.mem_insert.mp h with h1 | h2
        · exact hvv' h1.symm
        · exact hv'NotR h2
      simp [hv'NotIn]
  have hrTmp_in1 : rTmp ∈ s₁.rf.R := by rw [hrTmp_eq, hs1R]; exact Finset.mem_insert_self _ _
  have hrTmp_not0 : rTmp ∉ s.rf.R := by
    rw [hrTmp_eq]; dsimp only [newR]
    by_cases hconn : F'.Connected v (s.rf.root v)
    · rw [ite_eq_left hconn]; exact hv'NotR
    · rw [ite_eq_right hconn]
      intro hvR
      have hreq : s.rf.root v = v := hv.root_eq_of_mem hvV hvR (connected_refl _ v)
      exact hconn (by rw [hreq]; exact connected_refl F' v)
  have hR'_eq : s'.rf.R = insert fresh s.rf.R := by
    change insert fresh (s₁.rf.R.erase rTmp) = insert fresh s.rf.R
    rw [hs1R, hrTmp_eq, Finset.erase_insert (hrTmp_eq ▸ hrTmp_not0)]
  have hF'_eq : s'.rf.F = F' := rfl
  have hconn_rf : s₁.rf.F.Connected rTmp fresh := by
    have hrTmpV : rTmp ∈ F'.V := hvalid1.roots_sub hrTmp_in1
    obtain ⟨r, ⟨hrR, hcr⟩, _⟩ := huniq' rTmp hrTmpV
    rcases Finset.mem_insert.mp hrR with rfl | hrOld
    · exact hcr
    · exfalso
      have hr1 : r ∈ s₁.rf.R := hs1R ▸ Finset.mem_insert_of_mem hrOld
      obtain ⟨r0, _, huniq1⟩ := hvalid1.unique_root rTmp hrTmpV
      have heq1 : r = rTmp := (huniq1 r ⟨hr1, hcr⟩).trans (huniq1 rTmp ⟨hrTmp_in1, connected_refl _ _⟩).symm
      exact hrTmp_not0 (heq1 ▸ hrOld)
  have hv' : TourValid vCap eCap s' :=
    { ordWithin := hvalid1.ordWithin
      compat := hvalid1.compat
      roots_sub := by
        rw [hR'_eq, hF'_eq]
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr0
        · exact hfreshV
        · exact Finset.mem_insert_of_mem (hv.roots_sub hr0)
      verts_lt := hvalid1.verts_lt
      unique_root := by rw [hR'_eq, hF'_eq]; exact huniq'
      marked_open := hvalid1.marked_open }
  -- Order-membership projection between `s.ord` and `s'.ord`: ends move only from `v` to `v'`.
  have hord_eq : s'.ord = applyOrdEdit s.ord (.moveEnds v v' sel c) := rfl
  have hord_ex : ∀ z : End, (∃ u, z ∈ s'.ord u) ↔ (∃ u, z ∈ s.ord u) := by
    intro z
    constructor
    · rintro ⟨u, hu⟩
      rw [hord_eq] at hu
      simp only [applyOrdEdit] at hu
      split_ifs at hu with h1 h2
      · exact ⟨v, (List.mem_filter.mp hu).1⟩
      · rw [hordv', List.nil_append] at hu; exact ⟨v, (List.mem_filter.mp hu).1⟩
      · exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩
      by_cases huv : u = v
      · subst huv
        by_cases hm : movedBy sel c z
        · refine ⟨v', ?_⟩
          rw [hord_eq]; simp [applyOrdEdit, hvv'.symm, hordv', hu, hm]
        · refine ⟨u, ?_⟩
          rw [hord_eq]; simp [applyOrdEdit, hu, hm]
      · refine ⟨u, ?_⟩
        have huv' : u ≠ v' := fun h => by rw [h, hordv'] at hu; cases hu
        rw [hord_eq]; simp [applyOrdEdit, huv, huv', hu]
  have hsrc_proj : ∀ z : End, (∃ u, z ∈ s.ord u) →
      (if ordSrc s'.ord z = v' then v else ordSrc s'.ord z) = ordSrc s.ord z := by
    intro z ⟨u, hu⟩
    have hsrc0 : ordSrc s.ord z = u := hv.compat.ordSrc_eq hu
    obtain ⟨u', hu'⟩ := (hord_ex z).mpr ⟨u, hu⟩
    have hsrc' : ordSrc s'.ord z = u' := hv'.compat.ordSrc_eq hu'
    rw [hsrc0, hsrc']
    rw [hord_eq] at hu'
    simp only [applyOrdEdit] at hu'
    split_ifs at hu' with h1 h2
    · subst h1
      have := hv.compat.unique u' u z (List.mem_filter.mp hu').1 hu
      rw [ite_eq_right hvv']; exact this
    · subst h2
      rw [hordv', List.nil_append] at hu'
      have := hv.compat.unique v u z (List.mem_filter.mp hu').1 hu
      simp [this]
    · have := hv.compat.unique u' u z hu' hu
      rw [ite_eq_right h2]; exact this
  -- Forest connectedness projection under `.split v v' StM ShM`
  have hroot_move : ∀ w ∈ F'.V,
      let w0 := if w = v' then v else w
      w0 ∈ s.rf.F.V ∧ (s'.rf.root w = s.rf.root w0 ∨ (s.rf.root w0 = kept ∧ s'.rf.root w = fresh)) := by
    intro w hwV
    have hw0V : (if w = v' then v else w) ∈ s.rf.F.V := by
      split_ifs with h
      · exact hvV
      · rcases Finset.mem_insert.mp hwV with rfl | hw0
        · exact absurd rfl h
        · exact hw0
    refine ⟨hw0V, ?_⟩
    obtain ⟨r', ⟨hr'R, hwr'⟩, _⟩ := hv'.unique_root w hwV
    have hreq' : s'.rf.root w = r' := hv'.root_eq_of_mem hwV hr'R hwr'
    rw [hreq']
    rw [hR'_eq] at hr'R
    rcases Finset.mem_insert.mp hr'R with rfl | hrOld
    · -- `r' = fresh`: connect `w0` to `v` (and hence `kept`) via `rTmp`!
      have hwr : F'.Connected w rTmp := connected_trans hwr' (connected_symm hconn_rf)
      have hproj := connected_applySplit_proj hv.compat.forest.1 hv'NotV StM ShM hwr
      have hrTmp0 : (if rTmp = v' then v else rTmp) = v := by
        by_cases h1 : rTmp = v'
        · simp [h1]
        · simp only [h1, ↓reduceIte]
          have h2 : newR ≠ v' := hrTmp_eq ▸ h1
          dsimp only [newR] at h2 ⊢
          by_cases hc : F'.Connected v (s.rf.root v)
          · exact absurd (ite_eq_left hc) h2
          · exact hrTmp_eq.trans (ite_eq_right hc)
      rw [hrTmp0] at hproj
      have hwk : s.rf.F.Connected (if w = v' then v else w) kept := by
        obtain ⟨r0, ⟨hr0R, hvr0⟩, _⟩ := hv.unique_root v hvV
        have hke : kept = r0 := hkept_eq.trans (hv.root_eq_of_mem hvV hr0R hvr0)
        rw [hke]; exact connected_trans hproj hvr0
      exact Or.inr ⟨hv.root_eq_of_mem hw0V hkeptR hwk, rfl⟩
    · have hproj := connected_applySplit_proj hv.compat.forest.1 hv'NotV StM ShM hwr'
      have hrne : r' ≠ v' := fun h => hv'NotR (h ▸ hrOld)
      rw [ite_eq_right hrne] at hproj
      exact Or.inl (hv.root_eq_of_mem hw0V hrOld hproj).symm
  have hM' : TourMarksAt s' M := by
    intro z
    change z ∈ s.marked ↔ (∃ u, z ∈ s'.ord u) ∧ z.1 ∉ s.rf.F.E ∧ z.1 ∈ M
    rw [hM z, hord_ex z]
  have hK' : TourKeepMatch keep s' S' := by
    refine ⟨hK.1, fun x hx => ?_⟩
    obtain ⟨hact0, hopen0, hrt0⟩ := hK.2 x hx
    obtain ⟨w, hxw⟩ := (hord_ex x).mpr hact0
    have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hxw)
    have hsrc' : ordSrc s'.ord x = w := hv'.compat.ordSrc_eq hxw
    have hproj := hsrc_proj x hact0
    rw [hsrc'] at hproj
    refine ⟨⟨w, hxw⟩, hopen0, ?_⟩
    rw [src_applyUpdate_split]
    have hcond_iff :
        ((if x.2 then x.1 ∈ St ∩ keep else x.1 ∈ Sh ∩ keep) ∧ S.src x = kept) ↔
        s'.rf.root (ordSrc s'.ord x) = fresh := by
      have hxb : (if x.2 then x.1 ∈ St ∩ keep else x.1 ∈ Sh ∩ keep) ↔
          s'.rf.root (ordSrc s'.ord x) = fresh := by
        obtain ⟨f, b⟩ := x; cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_inter, hx, and_true]; exact hSh f hx
        · simp only [↓reduceIte, Finset.mem_inter, hx, and_true]; exact hSt f hx
      rw [hxb]
      constructor
      · exact And.left
      · intro hf
        refine ⟨hf, ?_⟩
        rw [← hrt0, ← hproj]
        rcases (hroot_move w hwV).2 with hsame | ⟨hwas, _⟩
        · exfalso
          rw [hsrc', hsame] at hf
          obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root _ (hroot_move w hwV).1
          exact hfreshNotR (hf ▸ hv.root_eq_of_mem (hroot_move w hwV).1 hrR hvr ▸ hrR)
        · exact hwas
    by_cases hf : s'.rf.root (ordSrc s'.ord x) = fresh
    · rw [ite_eq_left (hcond_iff.mpr hf)]; exact hf
    · rw [ite_eq_right (fun h => hf (hcond_iff.mp h)), ← hrt0, ← hproj, hsrc']
      rcases (hroot_move w hwV).2 with hsame | ⟨_, hfr⟩
      · exact hsame
      · exact absurd (hsrc' ▸ hfr) hf
  have hother : ∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset := by
    intro r hrR hrne
    ext z
    rw [List.mem_toFinset, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
      mem_tourMarkedList_iff hv hM]
    have hrR' : r ∈ s'.rf.R := hR'_eq ▸ Finset.mem_insert_of_mem hrR
    have hrneF : r ≠ fresh := fun h => hfreshNotR (h ▸ hrR)
    constructor
    · rintro ⟨_, ⟨w, hzw⟩, hopen, hzM, hrt'⟩
      have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hzw)
      have hsrc' : ordSrc s'.ord z = w := hv'.compat.ordSrc_eq hzw
      have hact0 := (hord_ex z).mp ⟨w, hzw⟩
      have hproj := hsrc_proj z hact0
      rw [hsrc'] at hproj hrt'
      refine ⟨hrR, hact0, hopen, hzM, ?_⟩
      rw [← hproj]
      rcases (hroot_move w hwV).2 with hsame | ⟨_, hfr⟩
      · exact hsame.symm.trans hrt'
      · exact absurd (hrt'.symm.trans hfr) hrneF
    · rintro ⟨_, hact0, hopen, hzM, hrt⟩
      obtain ⟨w, hzw⟩ := (hord_ex z).mpr hact0
      have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hzw)
      have hsrc' : ordSrc s'.ord z = w := hv'.compat.ordSrc_eq hzw
      have hproj := hsrc_proj z hact0
      rw [hsrc'] at hproj
      rw [← hproj] at hrt
      refine ⟨hrR', ⟨w, hzw⟩, hopen, hzM, ?_⟩
      rw [hsrc']
      rcases (hroot_move w hwV).2 with hsame | ⟨hwas, _⟩
      · exact hsame.trans hrt
      · exact absurd (hrt.symm.trans hwas) hrne
  have hunion : (tourMarkedList s' kept).toFinset ∪ (tourMarkedList s' fresh).toFinset =
      (tourMarkedList s kept).toFinset := by
    ext z
    simp only [Finset.mem_union, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
      mem_tourMarkedList_iff hv hM]
    have hkeptR' : kept ∈ s'.rf.R := hR'_eq ▸ Finset.mem_insert_of_mem hkeptR
    have hfreshR' : fresh ∈ s'.rf.R := hR'_eq ▸ Finset.mem_insert_self _ _
    constructor
    · rintro (⟨_, ⟨w, hzw⟩, hopen, hzM, hrt'⟩ | ⟨_, ⟨w, hzw⟩, hopen, hzM, hrt'⟩)
      · have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hzw)
        have hsrc' : ordSrc s'.ord z = w := hv'.compat.ordSrc_eq hzw
        have hact0 := (hord_ex z).mp ⟨w, hzw⟩
        have hproj := hsrc_proj z hact0
        rw [hsrc'] at hproj hrt'
        refine ⟨hkeptR, hact0, hopen, hzM, ?_⟩
        rw [← hproj]
        rcases (hroot_move w hwV).2 with hsame | ⟨hwas, _⟩
        · exact hsame.symm.trans hrt'
        · exact hwas
      · have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hzw)
        have hsrc' : ordSrc s'.ord z = w := hv'.compat.ordSrc_eq hzw
        have hact0 := (hord_ex z).mp ⟨w, hzw⟩
        have hproj := hsrc_proj z hact0
        rw [hsrc'] at hproj hrt'
        refine ⟨hkeptR, hact0, hopen, hzM, ?_⟩
        rw [← hproj]
        rcases (hroot_move w hwV).2 with hsame | ⟨hwas, _⟩
        · exfalso
          rw [hsame] at hrt'
          obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root _ (hroot_move w hwV).1
          exact hfreshNotR (hrt' ▸ hv.root_eq_of_mem (hroot_move w hwV).1 hrR hvr ▸ hrR)
        · exact hwas
    · rintro ⟨_, hact0, hopen, hzM, hrt⟩
      obtain ⟨w, hzw⟩ := (hord_ex z).mpr hact0
      have hwV : w ∈ F'.V := hv'.compat.vert w (List.ne_nil_of_mem hzw)
      have hsrc' : ordSrc s'.ord z = w := hv'.compat.ordSrc_eq hzw
      have hproj := hsrc_proj z hact0
      rw [hsrc'] at hproj
      rw [← hproj] at hrt
      rcases (hroot_move w hwV).2 with hsame | ⟨_, hfr⟩
      · exact Or.inl ⟨hkeptR', ⟨w, hzw⟩, hopen, hzM, by rw [hsrc', hsame, hrt]⟩
      · exact Or.inr ⟨hfreshR', ⟨w, hzw⟩, hopen, hzM, by rw [hsrc', hfr]⟩
  exact ⟨hrTmp_in1, hrTmp_not0, hconn_rf, hR'_eq, hv', hM', hK', hkeptR, hother, hunion⟩

end

end MinCostFlow.SparseCore.Program
