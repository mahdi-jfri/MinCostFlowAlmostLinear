module

public import MinCostFlow.ExpanderDecomp.RouteShortPath
public import MinCostFlow.ExpanderDecomp.RouteProgBFS
public import MinCostFlow.ExpanderDecomp.RouteProgDFS

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short-Path Blocking Word-RAM Procedure: Base Lemmas, Layout, and Sub-Triples

Provides:
1. Pure `adj`-general helper lemmas for `bfsLayers`, `dfsBlock`, and `shortPathBlockLoop`.
2. Configuration block (`SpCfg`, `SpCfgAt`), disjointness (`SpDisj`), write set (`SpWriteSet`),
   output predicate (`SpOutAt`), and deterministic procedure `shortPathBlockProc`.
3. Phase-level `BfsDisj`/`DfsDisj` derivations and helper sub-triples (`spLoadCfg_triple`,
   `spInitFilter_triple`, `spIsolateLoop_triple`, `spFilterInPlace_triple`, `spWriteRet_triple`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helper Lemmas for `bfsLayers`, `dfsBlock`, and `shortPathBlockLoop` -/

lemma DisjRange.of_sub {a la b lb b' lb' : ℕ}
    (h : DisjRange a la b lb) (h1 : b ≤ b') (h2 : b' + lb' ≤ b + lb) :
    DisjRange a la b' lb' := by
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

lemma sort_filter_eq_inter_sort (S V : Finset ℕ) :
    (S.sort (· ≤ ·)).filter (fun x => decide (x ∈ V)) = (S ∩ V).sort (· ≤ ·) := by
  have hnd1 : ((S.sort (· ≤ ·)).filter (fun x => decide (x ∈ V))).Nodup :=
    (S.sort_nodup (· ≤ ·)).filter _
  have hnd2 : ((S ∩ V).sort (· ≤ ·)).Nodup := (S ∩ V).sort_nodup (· ≤ ·)
  have hpw1 : ((S.sort (· ≤ ·)).filter (fun x => decide (x ∈ V))).Pairwise (· ≤ ·) :=
    (S.pairwise_sort (· ≤ ·)).filter _
  have hpw2 : ((S ∩ V).sort (· ≤ ·)).Pairwise (· ≤ ·) := (S ∩ V).pairwise_sort (· ≤ ·)
  have hperm : ((S.sort (· ≤ ·)).filter (fun x => decide (x ∈ V))).Perm ((S ∩ V).sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
    intro x
    simp [Finset.mem_sort, Finset.mem_inter]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hpw1 hpw2

lemma bfsLayers_inter (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ) (d : ℕ) (T : Finset ℕ) :
    bfsLayers adj V (S ∩ V) d T = bfsLayers adj V S d T := by
  unfold bfsLayers
  rw [Finset.inter_assoc, Finset.inter_self]

lemma dfsBlock_inter (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j : ℕ) :
    dfsBlock adj V (S ∩ V) T dist j = dfsBlock adj V S T dist j := by
  unfold dfsBlock
  rw [Finset.inter_assoc, Finset.inter_self]

private lemma bfsScanAdj_inv (V : Finset ℕ) (nd : ℕ) (es : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hnone : ∀ x, x ∉ vis → dist x = none) :
    let r := bfsScanAdj V nd es nxt vis dist
    vis ⊆ r.2.1 ∧
    (∀ x, x ∉ r.2.1 → r.2.2.1 x = none) ∧
    (∀ x ∈ vis, r.2.2.1 x = dist x) := by
  induction es generalizing nxt vis dist with
  | nil => exact ⟨Finset.Subset.refl _, hnone, fun _ _ => rfl⟩
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    dsimp only [bfsScanAdj]
    split_ifs with hw
    · have hnone' : ∀ x, x ∉ insert w vis → Function.update dist w (some nd) x = none := by
        intro x hx
        have hne : x ≠ w := fun h => hx (h ▸ Finset.mem_insert_self _ _)
        rw [Function.update_of_ne hne]
        exact hnone x (fun h => hx (Finset.mem_insert_of_mem h))
      obtain ⟨hsub, hnn, hkeep⟩ := ih (w :: nxt) (insert w vis) (Function.update dist w (some nd)) hnone'
      refine ⟨Finset.Subset.trans (Finset.subset_insert _ _) hsub, hnn, fun x hx => ?_⟩
      rw [hkeep x (Finset.mem_insert_of_mem hx)]
      exact Function.update_of_ne (fun h => by subst h; exact hw.2 hx) _ _
    · exact ih nxt vis dist hnone

private lemma bfsExpandFrontier_inv (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nd : ℕ)
    (fr nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hnone : ∀ x, x ∉ vis → dist x = none) :
    let r := bfsExpandFrontier adj V nd fr nxt vis dist
    vis ⊆ r.2.1 ∧
    (∀ x, x ∉ r.2.1 → r.2.2.1 x = none) ∧
    (∀ x ∈ vis, r.2.2.1 x = dist x) := by
  induction fr generalizing nxt vis dist with
  | nil => exact ⟨Finset.Subset.refl _, hnone, fun _ _ => rfl⟩
  | cons u rest ih =>
    dsimp only [bfsExpandFrontier]
    obtain ⟨hs1, hn1, hk1⟩ := bfsScanAdj_inv V nd (adj u) nxt vis dist hnone
    set r1 := bfsScanAdj V nd (adj u) nxt vis dist
    obtain ⟨hs2, hn2, hk2⟩ := ih r1.1 r1.2.1 r1.2.2.1 hn1
    exact ⟨Finset.Subset.trans hs1 hs2, hn2, fun x hx => (hk2 x (hs1 hx)).trans (hk1 x hx)⟩

private lemma bfsLoop_inv (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ) :
    ∀ (rem curDist : ℕ) (fr : List ℕ) (revL : List (List ℕ)) (vis : Finset ℕ)
      (dist : ℕ → Option ℕ) (cost : ℕ),
      (∀ x, x ∉ vis → dist x = none) →
      let res := bfsLoop adj V stopSet rem curDist fr revL vis dist cost
      vis ⊆ res.visited ∧
      (∀ x, x ∉ res.visited → res.dist x = none) ∧
      (∀ x ∈ vis, res.dist x = dist x) ∧
      res.maxReached ≤ curDist + rem ∧
      cost ≤ res.cost := by
  intro rem
  induction rem with
  | zero =>
    intro curDist fr revL vis dist cost hnone
    exact ⟨Finset.Subset.refl _, hnone, fun _ _ => rfl, le_rfl, le_rfl⟩
  | succ rem ih =>
    intro curDist fr revL vis dist cost hnone
    dsimp only [bfsLoop]
    obtain ⟨hs1, hn1, hk1⟩ := bfsExpandFrontier_inv adj V (curDist + 1) fr [] vis dist hnone
    set r := bfsExpandFrontier adj V (curDist + 1) fr [] vis dist
    split_ifs with he hhit
    · dsimp only; exact ⟨hs1, hn1, hk1, by omega, by omega⟩
    · dsimp only; exact ⟨hs1, hn1, hk1, by omega, by omega⟩
    · obtain ⟨hs2, hn2, hk2, hmr, hco⟩ :=
        ih (curDist + 1) r.1 (r.1 :: revL) r.2.1 r.2.2.1 (cost + r.2.2.2 + 1 + r.1.length) hn1
      exact ⟨Finset.Subset.trans hs1 hs2, hn2,
        fun x hx => (hk2 x (hs1 hx)).trans (hk1 x hx), by omega, by omega⟩

lemma bfsLayers_inv (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ) (d : ℕ) (T : Finset ℕ) :
    let res := bfsLayers adj V S d T
    (∀ x, x ∉ res.visited → res.dist x = none) ∧
    (∀ s ∈ S ∩ V, res.dist s = some 0) ∧
    res.maxReached ≤ d ∧
    1 ≤ res.cost ∧
    (res.hitStop = true → (S ∩ V).card ≤ res.cost) ∧
    ((S ∩ V).Nonempty → (S ∩ V).card ≤ res.cost) := by
  dsimp only [bfsLayers]
  set S0 := S ∩ V
  set initLayer := S0.sort (· ≤ ·)
  split_ifs with he hhit
  · dsimp only
    have hS0e : S0 = ∅ := by
      have hnil : initLayer = [] := List.isEmpty_iff.mp he
      have hlen : initLayer.length = 0 := by rw [hnil]; rfl
      rw [Finset.length_sort] at hlen
      exact Finset.card_eq_zero.mp hlen
    refine ⟨fun _ _ => rfl, fun s hs => by simp [hS0e] at hs, Nat.zero_le _, le_rfl,
      fun h => by simp at h, fun hne => by simp [hS0e] at hne⟩
  · dsimp only
    have hlen : initLayer.length = S0.card := Finset.length_sort _
    refine ⟨fun x hx => by simp [hx], fun s hs => by simp [hs], Nat.zero_le _, by omega,
      fun _ => by omega, fun _ => by omega⟩
  · have hlen : initLayer.length = S0.card := Finset.length_sort _
    have hnone0 : ∀ x, x ∉ S0 → (fun v => if v ∈ S0 then some 0 else none) x = none :=
      fun x hx => by simp [hx]
    obtain ⟨_, hn, hk, hmr, hco⟩ :=
      bfsLoop_inv adj V T d 0 initLayer [initLayer] S0
        (fun v => if v ∈ S0 then some 0 else none) (initLayer.length + initLayer.length + 1) hnone0
    refine ⟨hn, fun s hs => by rw [hk s hs]; simp [hs], by omega, by omega,
      fun _ => by omega, fun _ => by omega⟩

private lemma dfsStep_inv (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s : ℕ) :
    ∀ (fuel u r : ℕ) (trail : List (ℕ × ℕ)) (st : DFSState),
      st.used ⊆ V →
      (∀ x ∈ stackVerts u trail, x ∈ V) →
      (∀ x ∈ stackVerts u trail, x ∉ st.used) →
      st.used.card ≤ st.cost →
      st.paths.length ≤ st.used.card →
      let st' := dfsStep V T dist j s fuel u r trail st
      st'.used ⊆ V ∧
      st'.used.card ≤ st'.cost ∧
      st'.paths.length ≤ st'.used.card := by
  intro fuel
  induction fuel with
  | zero =>
    intro u r trail st hsub _ _ hle hpl
    exact ⟨hsub, hle, hpl⟩
  | succ fuel ih =>
    intro u r trail st hsub hstk hnu hle hpl
    dsimp only [dfsStep]
    split_ifs with huT hrj
    · have hsv_sub : (stackVerts u trail).toFinset ⊆ V := fun x hx => hstk x (List.mem_toFinset.mp hx)
      have hunion_sub : st.used ∪ (stackVerts u trail).toFinset ⊆ V := Finset.union_subset hsub hsv_sub
      have hcard_le : (st.used ∪ (stackVerts u trail).toFinset).card ≤
          st.used.card + (stackVerts u trail).length := by
        calc (st.used ∪ (stackVerts u trail).toFinset).card
            ≤ st.used.card + (stackVerts u trail).toFinset.card := Finset.card_union_le _ _
          _ ≤ st.used.card + (stackVerts u trail).length :=
              Nat.add_le_add_left (List.toFinset_card_le _) _
      have hu_not : u ∉ st.used := hnu u List.mem_cons_self
      have hu_in : u ∈ (stackVerts u trail).toFinset := List.mem_toFinset.mpr List.mem_cons_self
      have hcard_ge : st.used.card + 1 ≤ (st.used ∪ (stackVerts u trail).toFinset).card := by
        have hsub_ins : insert u st.used ⊆ st.used ∪ (stackVerts u trail).toFinset :=
          Finset.insert_subset (Finset.mem_union_right _ hu_in) Finset.subset_union_left
        have := Finset.card_le_card hsub_ins
        rwa [Finset.card_insert_of_notMem hu_not] at this
      refine ⟨hunion_sub, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; simp only [List.length_cons]; omega
    · cases trail with
      | nil => dsimp only; exact ⟨hsub, by omega, hpl⟩
      | cons hd rest =>
        dsimp only
        exact ih hd.1 (r - 1) rest
          { st with dead := insert u st.dead, cost := st.cost + 1 }
          hsub (fun x hx => hstk x (List.mem_cons_of_mem _ hx))
          (fun x hx => hnu x (List.mem_cons_of_mem _ hx)) (by dsimp only; omega) hpl
    · cases hcur : st.cursor u with
      | nil =>
        cases trail with
        | nil => dsimp only; exact ⟨hsub, by omega, hpl⟩
        | cons hd rest =>
          dsimp only
          exact ih hd.1 (r - 1) rest
            { st with dead := insert u st.dead, cost := st.cost + 1 }
            hsub (fun x hx => hstk x (List.mem_cons_of_mem _ hx))
            (fun x hx => hnu x (List.mem_cons_of_mem _ hx)) (by dsimp only; omega) hpl
      | cons p rest =>
        rcases p with ⟨w, e⟩
        dsimp only
        split_ifs with hpush
        · have hstk' : ∀ x ∈ stackVerts w ((u, e) :: trail), x ∈ V := by
            intro x hx
            simp only [stackVerts, List.map_cons, List.mem_cons] at hx
            rcases hx with rfl | hxu | hx
            · exact hpush.1
            · rw [hxu]; exact hstk u List.mem_cons_self
            · exact hstk x (List.mem_cons_of_mem _ hx)
          have hnu' : ∀ x ∈ stackVerts w ((u, e) :: trail), x ∉ st.used := by
            intro x hx
            simp only [stackVerts, List.map_cons, List.mem_cons] at hx
            rcases hx with rfl | hxu | hx
            · exact hpush.2.1
            · rw [hxu]; exact hnu u List.mem_cons_self
            · exact hnu x (List.mem_cons_of_mem _ hx)
          exact ih w (r + 1) ((u, e) :: trail)
            { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
            hsub hstk' hnu' (by dsimp only; omega) hpl
        · exact ih u r trail
            { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
            hsub hstk hnu (by dsimp only; omega) hpl

private lemma dfsSources_inv (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ)
    (srcs : List ℕ) (st : DFSState)
    (hsrcs : ∀ s ∈ srcs, s ∈ V)
    (hsub : st.used ⊆ V) (hle : st.used.card ≤ st.cost) (hpl : st.paths.length ≤ st.used.card) :
    let st' := dfsSources V T dist j fuel srcs st
    st'.used ⊆ V ∧ st'.used.card ≤ st'.cost ∧ st'.paths.length ≤ st'.used.card := by
  induction srcs generalizing st with
  | nil => exact ⟨hsub, hle, hpl⟩
  | cons s rest ih =>
    dsimp only [dfsSources]
    split_ifs with hskip
    · exact ih _ (fun x hx => hsrcs x (List.mem_cons_of_mem _ hx)) hsub (by dsimp only; omega) hpl
    · push Not at hskip
      have hsV : s ∈ V := hsrcs s List.mem_cons_self
      obtain ⟨hsub1, hle1, hpl1⟩ := dfsStep_inv V T dist j s fuel s 0 [] { st with cost := st.cost + 1 }
        hsub (by simp [stackVerts, hsV]) (by simp [stackVerts, hskip.1]) (by dsimp only; omega) hpl
      exact ih _ (fun x hx => hsrcs x (List.mem_cons_of_mem _ hx)) hsub1 hle1 hpl1

lemma dfsBlock_inv (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j : ℕ) :
    let res := dfsBlock adj V S T dist j
    res.used ⊆ V ∧ res.used.card ≤ res.cost ∧ res.paths.length ≤ res.used.card := by
  unfold dfsBlock
  refine dfsSources_inv V T dist j _ ((S ∩ V).sort (· ≤ ·)) _
    (fun s hs => (Finset.mem_inter.mp ((Finset.mem_sort (· ≤ ·)).mp hs)).2)
    (Finset.empty_subset _) (Nat.zero_le _) (Nat.zero_le _)

lemma shortPathBlockLoop_cost_add (adj : ℕ → List (ℕ × ℕ)) (S T : Finset ℕ) (d : ℕ) :
    ∀ (rem : ℕ) (V : Finset ℕ) (acc : List ((ℕ × ℕ) × List ℕ)) (c1 c2 : ℕ),
      (shortPathBlockLoop adj S T d rem V acc (c1 + c2)).paths =
        (shortPathBlockLoop adj S T d rem V acc c1).paths ∧
      (shortPathBlockLoop adj S T d rem V acc (c1 + c2)).remVerts =
        (shortPathBlockLoop adj S T d rem V acc c1).remVerts ∧
      (shortPathBlockLoop adj S T d rem V acc (c1 + c2)).cost =
        (shortPathBlockLoop adj S T d rem V acc c1).cost + c2 := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _; exact ⟨rfl, rfl, rfl⟩
  | succ rem ih =>
    intro V acc c1 c2
    dsimp only [shortPathBlockLoop]
    split_ifs with hhit
    · have h1 : c1 + c2 + (bfsLayers adj V S d T).cost + 1 +
          (dfsBlock adj V S T (bfsLayers adj V S d T).dist (bfsLayers adj V S d T).maxReached).cost =
          (c1 + (bfsLayers adj V S d T).cost + 1 +
            (dfsBlock adj V S T (bfsLayers adj V S d T).dist (bfsLayers adj V S d T).maxReached).cost) + c2 := by
        omega
      rw [h1]; exact ih _ _ _ _
    · dsimp only; exact ⟨rfl, rfl, by omega⟩

lemma shortPathBlockLoop_remVerts_sub (adj : ℕ → List (ℕ × ℕ)) (S T : Finset ℕ) (d : ℕ) :
    ∀ (rem : ℕ) (V : Finset ℕ) (acc : List ((ℕ × ℕ) × List ℕ)) (c : ℕ),
      (shortPathBlockLoop adj S T d rem V acc c).remVerts ⊆ V ∧
      c ≤ (shortPathBlockLoop adj S T d rem V acc c).cost := by
  intro rem
  induction rem with
  | zero => intro _ _ _; exact ⟨Finset.Subset.refl _, le_rfl⟩
  | succ rem ih =>
    intro V acc c
    dsimp only [shortPathBlockLoop]
    split_ifs with hhit
    · obtain ⟨hs, hc⟩ := ih (V \ (dfsBlock adj V S T (bfsLayers adj V S d T).dist
        (bfsLayers adj V S d T).maxReached).used) _ _
      exact ⟨Finset.Subset.trans hs Finset.sdiff_subset, by omega⟩
    · dsimp only; exact ⟨Finset.Subset.refl _, by omega⟩

lemma shortPathBlock_inter_card_le_cost (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (d : ℕ) :
    (S ∩ V).card ≤ (shortPathBlock adj V S T d).cost := by
  by_cases hne : (S ∩ V).Nonempty
  · have hbfs := (bfsLayers_inv adj V S d T).2.2.2.2.2 hne
    unfold shortPathBlock
    dsimp only [shortPathBlockLoop]
    split_ifs
    · have hc := (shortPathBlockLoop_remVerts_sub adj S T d d
        (V \ (dfsBlock adj V S T (bfsLayers adj V S d T).dist
          (bfsLayers adj V S d T).maxReached).used)
        ((dfsBlock adj V S T (bfsLayers adj V S d T).dist
          (bfsLayers adj V S d T).maxReached).paths ++ [])
        (0 + (bfsLayers adj V S d T).cost + 1 +
          (dfsBlock adj V S T (bfsLayers adj V S d T).dist
            (bfsLayers adj V S d T).maxReached).cost)).2
      omega
    · dsimp only; omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

lemma card_sdiff_sdiff_eq {V0 V U : Finset ℕ} (hV : V ⊆ V0) (hU : U ⊆ V) :
    (V0 \ (V \ U)).card = (V0 \ V).card + U.card := by
  have heq : V0 \ (V \ U) = (V0 \ V) ∪ U := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro ⟨hx0, hnot⟩
      by_cases hxV : x ∈ V
      · right; by_contra hxU; exact hnot ⟨hxV, hxU⟩
      · left; exact ⟨hx0, hxV⟩
    · rintro (⟨hx0, hxV⟩ | hxU)
      · exact ⟨hx0, fun h => hxV h.1⟩
      · exact ⟨hV (hU hxU), fun h => h.2 hxU⟩
  have hdisj : Disjoint (V0 \ V) U := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    exact (Finset.mem_sdiff.mp hx).2 (hU hxU)
  rw [heq, Finset.card_union_of_disjoint hdisj]

/-! ## 2. Configuration Block, Write Set, Disjointness, and Statements -/

/-- 12-word input configuration block for `shortPathBlockProc` at `cfgAddr + 0 .. cfgAddr + 11`.
Outputs are written at `cfgAddr + 12 .. cfgAddr + 17`. -/
structure SpCfg where
  bfsCfgAddr : ℕ
  dfsCfgAddr : ℕ
  maskArrAddr : ℕ
  maskBadVal : ℕ
  usedListAddr : ℕ
  sBufAddr : ℕ
  srcInPtr : ℕ
  srcInLen : ℕ
  d : ℕ
  bfsGenIn : ℕ
  dfsGenIn : ℕ
  heapIn : ℕ

/-- The 12 input configuration words of `cfg` reside at `cfgAddr + 0 .. cfgAddr + 11`. -/
def SpCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (cfg : SpCfg) : Prop :=
  mem (cfgAddr + 0) = cfg.bfsCfgAddr ∧
  mem (cfgAddr + 1) = cfg.dfsCfgAddr ∧
  mem (cfgAddr + 2) = cfg.maskArrAddr ∧
  mem (cfgAddr + 3) = cfg.maskBadVal ∧
  mem (cfgAddr + 4) = cfg.usedListAddr ∧
  mem (cfgAddr + 5) = cfg.sBufAddr ∧
  mem (cfgAddr + 6) = cfg.srcInPtr ∧
  mem (cfgAddr + 7) = cfg.srcInLen ∧
  mem (cfgAddr + 8) = cfg.d ∧
  mem (cfgAddr + 9) = cfg.bfsGenIn ∧
  mem (cfgAddr + 10) = cfg.dfsGenIn ∧
  mem (cfgAddr + 11) = cfg.heapIn

/-- Addresses that `shortPathBlockProc` may overwrite (all BFS/DFS scratch arrays, dynamic
sub-config words, `maskArr`, `sBuf`, heap `[heapIn, heapIn + 10 * nX)`, and `cfgAddr + 12..17`). -/
def SpWriteSet (nX : ℕ) (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg) (spCfgAddr : ℕ)
    (a : ℕ) : Prop :=
  BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a ∨
  DfsWriteSet nX { dfsCfg with heapIn := spCfg.heapIn } spCfg.dfsCfgAddr a ∨
  (spCfg.heapIn ≤ a ∧ a < spCfg.heapIn + 10 * nX) ∨
  (spCfg.bfsCfgAddr + 12 = a ∨ spCfg.bfsCfgAddr + 15 = a) ∨
  (spCfg.dfsCfgAddr + 8 = a ∨ spCfg.dfsCfgAddr + 17 = a ∨ spCfg.dfsCfgAddr + 18 = a ∨
   (spCfg.dfsCfgAddr + 20 ≤ a ∧ a < spCfg.dfsCfgAddr + 24)) ∨
  (spCfg.maskArrAddr ≤ a ∧ a < spCfg.maskArrAddr + nX) ∨
  (spCfg.sBufAddr ≤ a ∧ a < spCfg.sBufAddr + nX) ∨
  (spCfgAddr + 12 ≤ a ∧ a < spCfgAddr + 18)

/-- Compatibility, disjointness, and word-size bounds for `shortPathBlockProc`. -/
structure SpDisj (w nX m2 : ℕ) (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg)
    (spCfgAddr : ℕ) : Prop where
  -- Static linkage between SpCfg, BfsCfg, and DfsCfg
  bfs_mask : bfsCfg.maskArrAddr = spCfg.maskArrAddr
  bfs_bad : bfsCfg.maskBadVal = spCfg.maskBadVal
  bfs_hasStop : bfsCfg.hasStop = 1
  bfs_maxDist : bfsCfg.maxDist = spCfg.d
  bfs_initPtr : bfsCfg.initPtr = spCfg.sBufAddr
  dfs_off : dfsCfg.offAddr = bfsCfg.offAddr
  dfs_nb : dfsCfg.nbAddr = bfsCfg.nbAddr
  dfs_mask : dfsCfg.maskArrAddr = spCfg.maskArrAddr
  dfs_bad : dfsCfg.maskBadVal = spCfg.maskBadVal
  dfs_stop : dfsCfg.stopArrAddr = bfsCfg.stopArrAddr
  dfs_stopVal : dfsCfg.stopVal = bfsCfg.stopVal
  dfs_vis : dfsCfg.visStampAddr = bfsCfg.visStampAddr
  dfs_dist : dfsCfg.distAddr = bfsCfg.distAddr
  dfs_usedList : dfsCfg.usedListAddr = spCfg.usedListAddr
  dfs_srcPtr : dfsCfg.srcPtr = spCfg.sBufAddr
  -- Base BFS and DFS disjointness at maximum sizes
  bfs_disj : BfsDisj w nX m2
    ({ bfsCfg with initLen := nX, bfsGen := spCfg.bfsGenIn + spCfg.d + 1 }) spCfg.bfsCfgAddr
  dfs_disj : DfsDisj w nX m2
    ({ dfsCfg with
        srcLen := nX
        bfsGen := spCfg.bfsGenIn + spCfg.d + 1
        dfsGen := spCfg.dfsGenIn + spCfg.d + 1
        targetDepth := spCfg.d
        heapIn := spCfg.heapIn }) spCfg.dfsCfgAddr
  -- Extended heap headroom `[heapIn, heapIn + 10 * nX)` disjoint from non-heap DFS regions
  cs_hp10 : DisjRange dfsCfg.curStampAddr nX spCfg.heapIn (10 * nX)
  cur_hp10 : DisjRange dfsCfg.curAddr nX spCfg.heapIn (10 * nX)
  us_hp10 : DisjRange dfsCfg.usedStampAddr nX spCfg.heapIn (10 * nX)
  ds_hp10 : DisjRange dfsCfg.deadStampAddr nX spCfg.heapIn (10 * nX)
  sv_hp10 : DisjRange dfsCfg.stkVertAddr nX spCfg.heapIn (10 * nX)
  se_hp10 : DisjRange dfsCfg.stkEdgeAddr nX spCfg.heapIn (10 * nX)
  ul_hp10 : DisjRange dfsCfg.usedListAddr nX spCfg.heapIn (10 * nX)
  dco_hp10 : DisjRange (spCfg.dfsCfgAddr + 24) 5 spCfg.heapIn (10 * nX)
  dcfg_hp10 : DisjRange spCfg.dfsCfgAddr 24 spCfg.heapIn (10 * nX)
  off_hp10 : DisjRange bfsCfg.offAddr (nX + 1) spCfg.heapIn (10 * nX)
  nb_hp10 : DisjRange bfsCfg.nbAddr m2 spCfg.heapIn (10 * nX)
  edge_hp10 : DisjRange dfsCfg.edgeAddr m2 spCfg.heapIn (10 * nX)
  mask_hp10 : DisjRange spCfg.maskArrAddr nX spCfg.heapIn (10 * nX)
  stop_hp10 : DisjRange bfsCfg.stopArrAddr nX spCfg.heapIn (10 * nX)
  vis_hp10 : DisjRange bfsCfg.visStampAddr nX spCfg.heapIn (10 * nX)
  dist_hp10 : DisjRange bfsCfg.distAddr nX spCfg.heapIn (10 * nX)
  sbuf_hp10 : DisjRange spCfg.sBufAddr nX spCfg.heapIn (10 * nX)
  -- Cross disjointness between BFS/DFS config blocks, scratch arrays, maskArr, sBuf, spCfg, srcIn
  bcfg_dcfg : DisjRange spCfg.bfsCfgAddr 21 spCfg.dfsCfgAddr 29
  bcfg_sp : DisjRange spCfg.bfsCfgAddr 21 spCfgAddr 18
  dcfg_sp : DisjRange spCfg.dfsCfgAddr 29 spCfgAddr 18
  bcfg_off : DisjRange spCfg.bfsCfgAddr 21 bfsCfg.offAddr (nX + 1)
  bcfg_nb : DisjRange spCfg.bfsCfgAddr 21 bfsCfg.nbAddr m2
  bcfg_edge : DisjRange spCfg.bfsCfgAddr 21 dfsCfg.edgeAddr m2
  bcfg_stop : DisjRange spCfg.bfsCfgAddr 21 bfsCfg.stopArrAddr nX
  bcfg_vis : DisjRange spCfg.bfsCfgAddr 21 bfsCfg.visStampAddr nX
  bcfg_dist : DisjRange spCfg.bfsCfgAddr 21 bfsCfg.distAddr nX
  bcfg_cs : DisjRange spCfg.bfsCfgAddr 21 dfsCfg.curStampAddr nX
  bcfg_us : DisjRange spCfg.bfsCfgAddr 21 dfsCfg.usedStampAddr nX
  bcfg_ds : DisjRange spCfg.bfsCfgAddr 21 dfsCfg.deadStampAddr nX
  dcfg_off : DisjRange spCfg.dfsCfgAddr 29 bfsCfg.offAddr (nX + 1)
  dcfg_nb : DisjRange spCfg.dfsCfgAddr 29 bfsCfg.nbAddr m2
  dcfg_edge : DisjRange spCfg.dfsCfgAddr 29 dfsCfg.edgeAddr m2
  dcfg_stop : DisjRange spCfg.dfsCfgAddr 29 bfsCfg.stopArrAddr nX
  dcfg_vis : DisjRange spCfg.dfsCfgAddr 29 bfsCfg.visStampAddr nX
  dcfg_dist : DisjRange spCfg.dfsCfgAddr 29 bfsCfg.distAddr nX
  dcfg_cs : DisjRange spCfg.dfsCfgAddr 29 dfsCfg.curStampAddr nX
  dcfg_us : DisjRange spCfg.dfsCfgAddr 29 dfsCfg.usedStampAddr nX
  dcfg_ds : DisjRange spCfg.dfsCfgAddr 29 dfsCfg.deadStampAddr nX
  dcfg_ul : DisjRange spCfg.dfsCfgAddr 29 spCfg.usedListAddr nX
  sp_off : DisjRange spCfgAddr 18 bfsCfg.offAddr (nX + 1)
  sp_nb : DisjRange spCfgAddr 18 bfsCfg.nbAddr m2
  sp_edge : DisjRange spCfgAddr 18 dfsCfg.edgeAddr m2
  sp_stop : DisjRange spCfgAddr 18 bfsCfg.stopArrAddr nX
  sp_vis : DisjRange spCfgAddr 18 bfsCfg.visStampAddr nX
  sp_cs : DisjRange spCfgAddr 18 dfsCfg.curStampAddr nX
  sp_us : DisjRange spCfgAddr 18 dfsCfg.usedStampAddr nX
  sp_ds : DisjRange spCfgAddr 18 dfsCfg.deadStampAddr nX
  bcfg_dfsW : ∀ a, spCfg.bfsCfgAddr ≤ a ∧ a < spCfg.bfsCfgAddr + 21 →
    ¬ DfsWriteSet nX { dfsCfg with heapIn := spCfg.heapIn } spCfg.dfsCfgAddr a
  bcfg_hp10 : DisjRange spCfg.bfsCfgAddr 21 spCfg.heapIn (10 * nX)
  dcfg_bfsW : ∀ a, spCfg.dfsCfgAddr ≤ a ∧ a < spCfg.dfsCfgAddr + 29 →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  edge_bfsW : ∀ a, dfsCfg.edgeAddr ≤ a ∧ a < dfsCfg.edgeAddr + m2 →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  cs_bfsW : ∀ a, dfsCfg.curStampAddr ≤ a ∧ a < dfsCfg.curStampAddr + nX →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  us_bfsW : ∀ a, dfsCfg.usedStampAddr ≤ a ∧ a < dfsCfg.usedStampAddr + nX →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  ds_bfsW : ∀ a, dfsCfg.deadStampAddr ≤ a ∧ a < dfsCfg.deadStampAddr + nX →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  hp10_bfsW : ∀ a, spCfg.heapIn ≤ a ∧ a < spCfg.heapIn + 10 * nX →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a
  -- maskArr and sBuf disjoint from non-mask/non-sBuf regions needed across phases
  mask_sbuf : DisjRange spCfg.maskArrAddr nX spCfg.sBufAddr nX
  mask_bcfg : DisjRange spCfg.maskArrAddr nX spCfg.bfsCfgAddr 21
  mask_dcfg : DisjRange spCfg.maskArrAddr nX spCfg.dfsCfgAddr 29
  mask_sp : DisjRange spCfg.maskArrAddr nX spCfgAddr 18
  mask_off : DisjRange spCfg.maskArrAddr nX bfsCfg.offAddr (nX + 1)
  mask_nb : DisjRange spCfg.maskArrAddr nX bfsCfg.nbAddr m2
  mask_edge : DisjRange spCfg.maskArrAddr nX dfsCfg.edgeAddr m2
  mask_stop : DisjRange spCfg.maskArrAddr nX bfsCfg.stopArrAddr nX
  mask_vis : DisjRange spCfg.maskArrAddr nX bfsCfg.visStampAddr nX
  mask_dist : DisjRange spCfg.maskArrAddr nX bfsCfg.distAddr nX
  mask_cs : DisjRange spCfg.maskArrAddr nX dfsCfg.curStampAddr nX
  mask_us : DisjRange spCfg.maskArrAddr nX dfsCfg.usedStampAddr nX
  mask_ds : DisjRange spCfg.maskArrAddr nX dfsCfg.deadStampAddr nX
  mask_ul : DisjRange spCfg.maskArrAddr nX spCfg.usedListAddr nX
  sbuf_bcfg : DisjRange spCfg.sBufAddr nX spCfg.bfsCfgAddr 21
  sbuf_dcfg : DisjRange spCfg.sBufAddr nX spCfg.dfsCfgAddr 29
  sbuf_sp : DisjRange spCfg.sBufAddr nX spCfgAddr 18
  sbuf_off : DisjRange spCfg.sBufAddr nX bfsCfg.offAddr (nX + 1)
  sbuf_nb : DisjRange spCfg.sBufAddr nX bfsCfg.nbAddr m2
  sbuf_edge : DisjRange spCfg.sBufAddr nX dfsCfg.edgeAddr m2
  sbuf_stop : DisjRange spCfg.sBufAddr nX bfsCfg.stopArrAddr nX
  sbuf_vis : DisjRange spCfg.sBufAddr nX bfsCfg.visStampAddr nX
  sbuf_cs : DisjRange spCfg.sBufAddr nX dfsCfg.curStampAddr nX
  sbuf_us : DisjRange spCfg.sBufAddr nX dfsCfg.usedStampAddr nX
  sbuf_ds : DisjRange spCfg.sBufAddr nX dfsCfg.deadStampAddr nX
  sbuf_src : DisjRange spCfg.sBufAddr nX spCfg.srcInPtr spCfg.srcInLen
  -- spCfg outputs disjoint from all read/write buffers
  sp_out_disj : ∀ a, spCfgAddr + 12 ≤ a ∧ a < spCfgAddr + 18 →
    ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a ∧
    ¬ DfsWriteSet nX { dfsCfg with heapIn := spCfg.heapIn } spCfg.dfsCfgAddr a
  sp_out_hp10 : DisjRange (spCfgAddr + 12) 6 spCfg.heapIn (10 * nX)
  sp_in_disj : ∀ a, spCfgAddr ≤ a ∧ a < spCfgAddr + 12 →
    ¬ SpWriteSet nX spCfg bfsCfg dfsCfg spCfgAddr a
  -- Word-size bounds
  w_sp : spCfgAddr + 24 < 2 ^ w
  w_srcIn : spCfg.srcInPtr + spCfg.srcInLen + 5 < 2 ^ w
  w_hp10 : spCfg.heapIn + 10 * nX + 5 < 2 ^ w
  w_bgen : spCfg.bfsGenIn + spCfg.d + 3 < 2 ^ w
  w_dgen : spCfg.dfsGenIn + spCfg.d + 3 < 2 ^ w
  w_d : spCfg.d + 5 < 2 ^ w

/-- Phase-level `BfsDisj` derived from `SpDisj`. -/
lemma BfsDisj.of_sp {w nX m2 : ℕ} {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg}
    {spCfgAddr bfsGen sLen : ℕ}
    (h : SpDisj w nX m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hgen : bfsGen ≤ spCfg.bfsGenIn + spCfg.d + 1) (hlen : sLen ≤ nX) :
    BfsDisj w nX m2 { bfsCfg with bfsGen := bfsGen, initLen := sLen } spCfg.bfsCfgAddr := by
  have hb := h.bfs_disj
  rcases hb with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    r1, r2, r3, r4, r5, r6, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19⟩
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    r1, r2, r3, r4, r5, ?_, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, ?_, w12, w13, w14, ?_,
    w16, w17, w18, w19⟩
  · intro a ha; exact r6 a ⟨ha.1, by dsimp only at ha ⊢; omega⟩
  · dsimp only at w11 ⊢; omega
  · dsimp only at w15 ⊢; omega

/-- Phase-level `DfsDisj` derived from `SpDisj`. -/
lemma DfsDisj.of_sp {w nX m2 : ℕ} {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg}
    {spCfgAddr bfsGen dfsGen targetDepth sLen heapPtr inHead inTail : ℕ}
    (h : SpDisj w nX m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hbgen : bfsGen ≤ spCfg.bfsGenIn + spCfg.d + 1)
    (hdgen : dfsGen ≤ spCfg.dfsGenIn + spCfg.d + 1)
    (htd : targetDepth ≤ spCfg.d)
    (hlen : sLen ≤ nX)
    (hhp1 : spCfg.heapIn ≤ heapPtr)
    (hhp2 : heapPtr ≤ spCfg.heapIn + 5 * nX) :
    DfsDisj w nX m2
      ({ dfsCfg with
        bfsGen := bfsGen
        dfsGen := dfsGen
        targetDepth := targetDepth
        srcLen := sLen
        heapIn := heapPtr
        inHead := inHead
        inTail := inTail })
      spCfg.dfsCfgAddr := by
  have hd := h.dfs_disj
  have hsub_ro : ∀ a,
      (∀ b, spCfg.heapIn ≤ b ∧ b < spCfg.heapIn + 10 * nX → b ≠ a) →
      ¬ DfsWriteSet nX ({ dfsCfg with
        srcLen := nX
        bfsGen := spCfg.bfsGenIn + spCfg.d + 1
        dfsGen := spCfg.dfsGenIn + spCfg.d + 1
        targetDepth := spCfg.d
        heapIn := spCfg.heapIn }) spCfg.dfsCfgAddr a →
      ¬ DfsWriteSet nX ({ dfsCfg with
        bfsGen := bfsGen
        dfsGen := dfsGen
        targetDepth := targetDepth
        srcLen := sLen
        heapIn := heapPtr
        inHead := inHead
        inTail := inTail }) spCfg.dfsCfgAddr a := by
    intro a hne hnot hw
    rcases hw with c | c | c | c | c | c | c | c | c
    · exact hnot (Or.inl c)
    · exact hnot (Or.inr (Or.inl c))
    · exact hnot (Or.inr (Or.inr (Or.inl c)))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))))
    · dsimp only at c; exact hne a ⟨by omega, by omega⟩ rfl
  have hhp_sub : heapPtr + 5 * nX ≤ spCfg.heapIn + 10 * nX := by omega
  refine
    { cs_cur := hd.cs_cur, cs_us := hd.cs_us, cs_ds := hd.cs_ds, cs_sv := hd.cs_sv,
      cs_se := hd.cs_se, cs_ul := hd.cs_ul, cs_co := hd.cs_co,
      cs_hp := h.cs_hp10.of_sub hhp1 hhp_sub,
      cur_us := hd.cur_us, cur_ds := hd.cur_ds, cur_sv := hd.cur_sv, cur_se := hd.cur_se,
      cur_ul := hd.cur_ul, cur_co := hd.cur_co,
      cur_hp := h.cur_hp10.of_sub hhp1 hhp_sub,
      us_ds := hd.us_ds, us_sv := hd.us_sv, us_se := hd.us_se, us_ul := hd.us_ul,
      us_co := hd.us_co, us_hp := h.us_hp10.of_sub hhp1 hhp_sub,
      ds_sv := hd.ds_sv, ds_se := hd.ds_se, ds_ul := hd.ds_ul, ds_co := hd.ds_co,
      ds_hp := h.ds_hp10.of_sub hhp1 hhp_sub,
      sv_se := hd.sv_se, sv_ul := hd.sv_ul, sv_co := hd.sv_co,
      sv_hp := h.sv_hp10.of_sub hhp1 hhp_sub,
      se_ul := hd.se_ul, se_co := hd.se_co, se_hp := h.se_hp10.of_sub hhp1 hhp_sub,
      ul_co := hd.ul_co, ul_hp := h.ul_hp10.of_sub hhp1 hhp_sub,
      co_hp := h.dco_hp10.of_sub hhp1 hhp_sub,
      ro_cfg := fun a ha => hsub_ro a (fun b hb => by rcases h.dcfg_hp10 with x | x <;> omega) (hd.ro_cfg a ha),
      ro_off := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_off] at ha; rcases h.off_hp10 with x | x <;> omega) (hd.ro_off a ha),
      ro_nb := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_nb] at ha; rcases h.nb_hp10 with x | x <;> omega) (hd.ro_nb a ha),
      ro_edge := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rcases h.edge_hp10 with x | x <;> omega) (hd.ro_edge a ha),
      ro_mask := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_mask] at ha; rcases h.mask_hp10 with x | x <;> omega) (hd.ro_mask a ha),
      ro_stop := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_stop] at ha; rcases h.stop_hp10 with x | x <;> omega) (hd.ro_stop a ha),
      ro_vis := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_vis] at ha; rcases h.vis_hp10 with x | x <;> omega) (hd.ro_vis a ha),
      ro_dist := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_dist] at ha; rcases h.dist_hp10 with x | x <;> omega) (hd.ro_dist a ha),
      ro_src := fun a ha => hsub_ro a (fun b hb => by dsimp only at ha; rw [h.dfs_srcPtr] at ha; rcases h.sbuf_hp10 with x | x <;> omega)
        (hd.ro_src a ⟨ha.1, by dsimp only at ha ⊢; omega⟩),
      hheap_pos := by have := hd.hheap_pos; dsimp only at this ⊢; omega,
      w_cfg := hd.w_cfg, w_off := hd.w_off, w_nb := hd.w_nb, w_edge := hd.w_edge,
      w_mask := hd.w_mask, w_stop := hd.w_stop, w_vis := hd.w_vis, w_dist := hd.w_dist,
      w_cs := hd.w_cs, w_cur := hd.w_cur, w_us := hd.w_us, w_ds := hd.w_ds,
      w_sv := hd.w_sv, w_se := hd.w_se, w_ul := hd.w_ul,
      w_src := by have := hd.w_src; dsimp only at this ⊢; omega,
      w_heap := by have := h.w_hp10; dsimp only; omega,
      w_mb := hd.w_mb, w_sv_val := hd.w_sv_val,
      w_bgen := by have := h.w_bgen; dsimp only; omega,
      w_dgen := by have := h.w_dgen; dsimp only; omega,
      w_td := by have := h.w_d; dsimp only; omega,
      w_m2 := hd.w_m2, w_nX := hd.w_nX, w4 := hd.w4 }

/-- Post-state predicate for `shortPathBlockProc` matching `res : ShortPathResult`. -/
def SpOutAt (mem : ℕ → ℕ) (X V : Finset ℕ) (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg)
    (spCfgAddr : ℕ) (res : ShortPathResult) : Prop :=
  let outHead := mem (spCfgAddr + 12)
  let outTail := mem (spCfgAddr + 13)
  let outHeap := mem (spCfgAddr + 14)
  let outPathsCnt := mem (spCfgAddr + 15)
  let outBfsGen := mem (spCfgAddr + 16)
  let outDfsGen := mem (spCfgAddr + 17)
  outPathsCnt = res.paths.length ∧
  spCfg.heapIn ≤ outHeap ∧
  outHeap ≤ spCfg.heapIn + 5 * (V \ res.remVerts).card ∧
  spCfg.bfsGenIn ≤ outBfsGen ∧ outBfsGen ≤ spCfg.bfsGenIn + spCfg.d + 1 ∧
  spCfg.dfsGenIn ≤ outDfsGen ∧ outDfsGen ≤ spCfg.dfsGenIn + spCfg.d + 1 ∧
  PathChainAt mem X spCfg.heapIn outHeap outHead outTail res.paths ∧
  (∀ v < X.card, mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ res.remVerts) ∧
  (∀ v < X.card, mem (bfsCfg.visStampAddr + v) ≤ outBfsGen) ∧
  (∀ v < X.card, mem (dfsCfg.curStampAddr + v) ≤ outDfsGen) ∧
  (∀ v < X.card, mem (dfsCfg.usedStampAddr + v) ≤ outDfsGen) ∧
  (∀ v < X.card, mem (dfsCfg.deadStampAddr + v) ≤ outDfsGen)

/-- Explicit step bound for `shortPathBlockProc`. -/
def spProgCost (modelCost sDiff : ℕ) : ℕ :=
  900 * modelCost + 50 * sDiff + 250

/-! ## 3. Deterministic Word-RAM Statements -/

/-- Load the 12 words of `SpCfg` into `r1 .. r12`. -/
def spLoadCfgStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))
    , .assign 5 (.load (.bin .add (.reg 0) (.const 4)))
    , .assign 6 (.load (.bin .add (.reg 0) (.const 5)))
    , .assign 7 (.load (.bin .add (.reg 0) (.const 6)))
    , .assign 8 (.load (.bin .add (.reg 0) (.const 7)))
    , .assign 9 (.load (.bin .add (.reg 0) (.const 8)))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 9)))
    , .assign 11 (.load (.bin .add (.reg 0) (.const 10)))
    , .assign 12 (.load (.bin .add (.reg 0) (.const 11))) ]

/-- Filter `srcInPtr[0..srcInLen-1]` into `sBufAddr`, keeping `v` with `maskArr[v] ≠ maskBadVal`. -/
def spInitFilterStmt : Stmt :=
  seqStmts
    [ .assign 14 (.const 0)
    , .assign 21 (.const 0)
    , .loop (.bin .lt (.reg 21) (.reg 8))
        (seqStmts
          [ .assign 22 (.load (.bin .add (.reg 7) (.reg 21)))
          , .cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 22))) (.reg 4))
              .nop
              (seqStmts
                [ .store (.bin .add (.reg 6) (.reg 14)) (.reg 22)
                , .assign 14 (.bin .add (.reg 14) (.const 1)) ])
          , .assign 21 (.bin .add (.reg 21) (.const 1)) ]) ]

/-- Mark all vertices in `usedList[0..r24-1]` as isolated (`maskArr[u] := maskBadVal`). -/
def spIsolateLoopStmt : Stmt :=
  seqStmts
    [ .assign 26 (.const 0)
    , .loop (.bin .lt (.reg 26) (.reg 24))
        (seqStmts
          [ .assign 27 (.load (.bin .add (.reg 5) (.reg 26)))
          , .store (.bin .add (.reg 3) (.reg 27)) (.reg 4)
          , .assign 26 (.bin .add (.reg 26) (.const 1)) ]) ]

/-- Filter `sBuf[0..r14-1]` in place, keeping `v` with `maskArr[v] ≠ maskBadVal`, writing new length to `r27`. -/
def spFilterInPlaceStmt : Stmt :=
  seqStmts
    [ .assign 26 (.const 0)
    , .assign 27 (.const 0)
    , .loop (.bin .lt (.reg 26) (.reg 14))
        (seqStmts
          [ .assign 28 (.load (.bin .add (.reg 6) (.reg 26)))
          , .cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 28))) (.reg 4))
              .nop
              (seqStmts
                [ .store (.bin .add (.reg 6) (.reg 27)) (.reg 28)
                , .assign 27 (.bin .add (.reg 27) (.const 1)) ])
          , .assign 26 (.bin .add (.reg 26) (.const 1)) ]) ]

/-- Main phase loop of `shortPathBlockProc` calling BFS procedure `bBfs` and DFS procedure `bDfs`. -/
def spPhaseLoopStmt (bBfs bDfs : ℕ) : Stmt :=
  .loop (.reg 13)
    (seqStmts
      [ .assign 15 (.bin .add (.reg 15) (.const 1))
      , .store (.bin .add (.reg 1) (.const 12)) (.reg 15)
      , .store (.bin .add (.reg 1) (.const 15)) (.reg 14)
      , .call 21 bBfs [.reg 1]
      , .assign 22 (.load (.bin .add (.reg 1) (.const 19)))
      , .cond (.reg 22)
          (seqStmts
            [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
            , .assign 16 (.bin .add (.reg 16) (.const 1))
            , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
            , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
            , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
            , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
            , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
            , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
            , .store (.bin .add (.reg 2) (.const 23)) (.reg 19)
            , .call 24 bDfs [.reg 2]
            , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
            , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
            , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
            , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
            , .assign 20 (.bin .add (.reg 20) (.reg 25))
            , spIsolateLoopStmt
            , spFilterInPlaceStmt
            , .assign 14 (.reg 27)
            , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
          (.assign 13 (.const 0)) ])

/-- Write the 6 output words at `cfgAddr + 12 .. cfgAddr + 17` and return `pathsCnt`. -/
def spWriteRetStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 0) (.const 12)) (.reg 18)
    , .store (.bin .add (.reg 0) (.const 13)) (.reg 19)
    , .store (.bin .add (.reg 0) (.const 14)) (.reg 17)
    , .store (.bin .add (.reg 0) (.const 15)) (.reg 20)
    , .store (.bin .add (.reg 0) (.const 16)) (.reg 15)
    , .store (.bin .add (.reg 0) (.const 17)) (.reg 16)
    , .ret (.reg 20) ]

/-- Full deterministic Word-RAM procedure for `shortPathBlock`. -/
def shortPathBlockProc (bBfs bDfs : ℕ) : Stmt :=
  seqStmts
    [ spLoadCfgStmt
    , spInitFilterStmt
    , .assign 13 (.bin .add (.reg 9) (.const 1))
    , .assign 15 (.reg 10)
    , .assign 16 (.reg 11)
    , .assign 17 (.reg 12)
    , .assign 18 (.const 0)
    , .assign 19 (.const 0)
    , .assign 20 (.const 0)
    , spPhaseLoopStmt bBfs bDfs
    , spWriteRetStmt ]

theorem shortPathBlockProc_noRand (bBfs bDfs : ℕ) : (shortPathBlockProc bBfs bDfs).NoRand := by
  simp [shortPathBlockProc, spLoadCfgStmt, spInitFilterStmt, spPhaseLoopStmt,
    spIsolateLoopStmt, spFilterInPlaceStmt, spWriteRetStmt, seqStmts, Stmt.NoRand]


end MinCostFlow.ExpanderDecomp
