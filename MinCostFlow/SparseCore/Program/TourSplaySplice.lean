module

public import MinCostFlow.SparseCore.Program.TourSplayModel
import Mathlib.Tactic

/-!
# Root splice operations on tour splay forests

Defines `tourDetachLeft`, `tourDetachRight`, `tourAttachLeft`, and `tourSetVal` on
`SplayState TourVal TourSum Unit` and proves preservation of `TourForestInv` and `forestPhi`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree SplayState

/-! ## Root splices: `tourDetachLeft`, `tourDetachRight`, `tourAttachLeft`, `tourSetVal` -/

/-- Detach the left child of root `x` into a separate tree (keeping `ppar = 0`). -/
def tourDetachLeft (st : SplayState TourVal TourSum Unit) (x : ℕ) :
    SplayState TourVal TourSum Unit :=
  if x = 0 then st
  else
    let l := (st.nodes x).left
    if l = 0 then st
    else
      let st1 := st.setPar l 0
      let st2 := st1.setLeft x 0
      pull tourPayload st2 x

/-- Detach the right child of root `x` into a separate tree (keeping `ppar = 0`). -/
def tourDetachRight (st : SplayState TourVal TourSum Unit) (x : ℕ) :
    SplayState TourVal TourSum Unit :=
  if x = 0 then st
  else
    let r := (st.nodes x).right
    if r = 0 then st
    else
      let st1 := st.setPar r 0
      let st2 := st1.setRight x 0
      pull tourPayload st2 x

/-- Attach a separate tree rooted at `l` as the left child of root `y` (which has `left = 0`). -/
def tourAttachLeft (st : SplayState TourVal TourSum Unit) (y l : ℕ) :
    SplayState TourVal TourSum Unit :=
  if y = 0 then st
  else
    let st1 := st.setLeft y l
    let st2 := if l = 0 then st1 else (st1.setPar l y).setPpar l 0
    pull tourPayload st2 y

/-- Overwrite the value of root `x` and pull its summary. -/
def tourSetVal (st : SplayState TourVal TourSum Unit) (x : ℕ) (v : TourVal) :
    SplayState TourVal TourSum Unit :=
  if x = 0 then st
  else pull tourPayload (st.updateNode x fun nd => { nd with val := v }) x

theorem ptrOk_tourDetachLeft {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (tourDetachLeft st x) := by
  unfold tourDetachLeft; dsimp only
  split_ifs
  · exact h
  · exact h
  · exact ((h.setPar (h x hx).1 (Nat.zero_le _)).setLeft hx (Nat.zero_le _)).pull hx

theorem ptrOk_tourDetachRight {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (tourDetachRight st x) := by
  unfold tourDetachRight; dsimp only
  split_ifs
  · exact h
  · exact h
  · exact ((h.setPar (h x hx).2.1 (Nat.zero_le _)).setRight hx (Nat.zero_le _)).pull hx

theorem ptrOk_tourAttachLeft {cap y l : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : PtrOk cap st) (hy : y ≤ cap) (hl : l ≤ cap) : PtrOk cap (tourAttachLeft st y l) := by
  unfold tourAttachLeft; dsimp only
  split_ifs
  · exact h
  · exact (h.setLeft hy hl).pull hy
  · exact (((h.setLeft hy hl).setPar hl hy).setPpar hl (Nat.zero_le _)).pull hy

theorem ptrOk_tourSetVal {cap x : ℕ} {st : SplayState TourVal TourSum Unit} {v : TourVal}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (tourSetVal st x v) := by
  unfold tourSetVal; split_ifs
  · exact h
  · refine PtrOk.pull ?_ hx
    intro u hu
    by_cases hux : u = x
    · subst hux; simpa [updateNode] using h u hu
    · simpa [updateNode, hux] using h u hu

private theorem nodup_node_intro' {x : ℕ} {l r : AuxTree}
    (hl : l.toList.Nodup) (hxl : x ∉ l.toList)
    (hr : r.toList.Nodup) (hxr : x ∉ r.toList)
    (hdisj : ∀ a ∈ l.toList, a ∉ r.toList) :
    (AuxTree.node x l r).toList.Nodup := by
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hl, List.nodup_singleton x, ?_⟩, hr, ?_⟩
  · intro a ha b hb h; simp only [List.mem_singleton] at hb; subst hb; subst h; exact hxl ha
  · intro a ha b hb h; subst h
    rcases List.mem_append.mp ha with hal | hax
    · exact hdisj a hal hb
    · simp only [List.mem_singleton] at hax; subst hax; exact hxr hb

/-- Correctness and non-increasing potential for `tourDetachLeft`. -/
theorem tourDetachLeft_preserves {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree}
    (h : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) :
    let st' := tourDetachLeft st x
    let mid : List AuxTree := (if L = .leaf then [] else [L]) ++ [AuxTree.node x .leaf R]
    TourForestInv cap st' (pre ++ mid ++ post) ∧
    (∀ u ∉ (AuxTree.node x L R).toList, st'.nodes u = st.nodes u) ∧
    (∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val) ∧
    forestPhi (pre ++ mid ++ post) ≤ forestPhi (pre ++ AuxTree.node x L R :: post) := by
  have ht_mem : AuxTree.node x L R ∈ pre ++ AuxTree.node x L R :: post := by simp
  have ht := h.treesInv _ ht_mem
  have hx_cap : x ≤ cap := (h.mem_inCap ht_mem (by simp [AuxTree.toList])).2
  have hrev_x : (st.nodes x).rev = false := h.noRev x hx_cap
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨hL_nd, hx_nL, hR_nd, hx_nR, hdisj⟩
  rcases ht.sub with ⟨hx_nz, hl_eq, hr_eq, hpar, _, _, _, hL_sub, hR_sub⟩
  have hphi_le : (if L = .leaf then 0 else L.treePhi tourVSize) +
      (AuxTree.node x .leaf R).treePhi tourVSize ≤ (AuxTree.node x L R).treePhi tourVSize := by
    have hLphi : (if L = .leaf then 0 else L.treePhi tourVSize) = L.treePhi tourVSize := by
      cases L <;> simp [AuxTree.treePhi]
    rw [hLphi]
    simp only [AuxTree.treePhi]
    have hrk : (AuxTree.node x .leaf R).rank tourVSize ≤ (AuxTree.node x L R).rank tourVSize := by
      simp only [AuxTree.rank, treeSize_tourVSize, AuxTree.countNodes]
      exact Nat.log_mono_right (by omega)
    omega
  cases L with
  | leaf =>
    have hl0 : (st.nodes x).left = 0 := by simpa [AuxTree.rootId] using hl_eq
    have hst' : tourDetachLeft st x = st := by simp [tourDetachLeft, hx_nz, hl0]
    refine ⟨by simpa [hst'] using h, fun _ _ => by simp [hst'], fun _ _ => by simp [hst'],
      by simp⟩
  | node lid lL lR =>
    have hlid_nz : lid ≠ 0 := hL_sub.1
    have hleft_lid : (st.nodes x).left = lid := hl_eq
    have hlx : lid ≠ x := fun heq => hx_nL (heq ▸ by simp [AuxTree.toList])
    set st1 := st.setPar lid 0
    set st2 := st1.setLeft x 0
    set st' := tourDetachLeft st x
    have hst'_eq : st' = pull tourPayload st2 x := by
      simp only [st', tourDetachLeft, hx_nz, ↓reduceIte, hleft_lid, hlid_nz, st1, st2]
    have hx2 : st2.nodes x = { st.nodes x with left := 0 } := by
      simp [st2, st1, setLeft, setPar, hlx.symm]
    have hlid2 : st2.nodes lid = { st.nodes lid with par := 0 } := by
      simp [st2, st1, setLeft, setPar, hlx]
    have hu2 : ∀ u, u ≠ x → u ≠ lid → st2.nodes u = st.nodes u := fun u h1 h2 => by
      simp [st2, st1, setLeft, setPar, h1, h2]
    have hR2 : SubtreeInv tourPayload st2 x R :=
      SubtreeInv_agree hR_sub fun u hu => (hu2 u (fun heq => hx_nR (heq ▸ hu))
        (fun heq => hdisj lid (by simp [AuxTree.toList]) (heq ▸ hu))).symm
    have hL2 : SubtreeInv tourPayload st2 0 (.node lid lL lR) := by
      rcases AuxTree.nodup_node_unfold hL_nd with ⟨_, hlid_nlL, _, hlid_nlR, _⟩
      rcases hL_sub with ⟨_, hl_l, hr_l, _, _, hsz_l, hsum_l, hlL_sub, hlR_sub⟩
      have h1 : SubtreeInv tourPayload st2 lid lL := SubtreeInv_agree hlL_sub fun u hu =>
        (hu2 u (fun heq => hx_nL (heq ▸ by simp [AuxTree.toList, hu]))
          (fun heq => hlid_nlL (heq ▸ hu))).symm
      have h2 : SubtreeInv tourPayload st2 lid lR := SubtreeInv_agree hlR_sub fun u hu =>
        (hu2 u (fun heq => hx_nL (heq ▸ by simp [AuxTree.toList, hu]))
          (fun heq => hlid_nlR (heq ▸ hu))).symm
      have hevL2 : evalPairs tourPayload st2 (.node lid lL lR) false () =
          evalPairs tourPayload st (.node lid lL lR) false () := by
        refine evalPairs_agree_vrt tourPayload (fun u hu => ?_) false ()
        by_cases hul : u = lid
        · subst hul; simp [hlid2]
        · rw [hu2 u (fun heq => hx_nL (heq ▸ hu)) hul]; exact ⟨rfl, rfl, rfl⟩
      exact ⟨hlid_nz, by simpa [hlid2] using hl_l, by simpa [hlid2] using hr_l,
        by simp [hlid2], fun hc => absurd rfl hc, by simpa [hlid2] using hsz_l,
        by rw [hevL2]; simp [hlid2, hsum_l], h1, h2⟩
    rcases pull_node_build tourPayload_laws (st := st2) (l := .leaf) hx_nz
      (by simp [AuxTree.toList]) hx_nR (by simp [hx2, AuxTree.rootId])
      (by rw [hx2]; exact hr_eq) (by rw [hx2]; exact hpar) (fun hc => absurd rfl hc)
      (by rw [hx2]; exact hrev_x) rfl trivial hR2 with ⟨hx_sub', _, _, _, hne'⟩
    rw [← hst'_eq] at hx_sub' hne'
    have hL_inv' : TreeInv tourPayload st' (.node lid lL lR) :=
      ⟨hL_nd, SubtreeInv_agree hL2 fun u hu => (hne' u (fun heq => hx_nL (heq ▸ hu))).symm⟩
    have hR_inv' : TreeInv tourPayload st' (.node x .leaf R) :=
      ⟨nodup_node_intro' (by simp [AuxTree.toList]) (by simp [AuxTree.toList]) hR_nd hx_nR
        (fun _ ha => by simp [AuxTree.toList] at ha), hx_sub'⟩
    have hout : ∀ u ∉ (AuxTree.node x (.node lid lL lR) R).toList, st'.nodes u = st.nodes u := by
      intro u hu
      have hux : u ≠ x := fun heq => hu (by subst heq; simp [AuxTree.toList])
      have hul : u ≠ lid := fun heq => hu (by subst heq; simp [AuxTree.toList])
      exact (hne' u hux).trans (hu2 u hux hul)
    have hval : ∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val := fun u _ => by
      rw [hst'_eq, pull_val_eq']
      by_cases hux : u = x
      · subst hux; simp [hx2]
      · by_cases hul : u = lid
        · subst hul; simp [hlid2]
        · rw [hu2 u hux hul]
    have hflat : (pre ++ [AuxTree.node lid lL lR, AuxTree.node x .leaf R] ++ post).flatMap AuxTree.toList =
        (pre ++ AuxTree.node x (AuxTree.node lid lL lR) R :: post).flatMap AuxTree.toList := by
      simp [List.flatMap_append, AuxTree.toList, List.append_assoc]
    have hinv' : TourForestInv cap st' (pre ++ [AuxTree.node lid lL lR, AuxTree.node x .leaf R] ++ post) :=
      { nonEmpty := fun s hs => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with (h1 | rfl | rfl) | h2
          · exact h.nonEmpty s (by simp [h1])
          · simp
          · simp
          · exact h.nonEmpty s (by simp [h2])
        treesInv := fun s hs => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with (h1 | rfl | rfl) | h2
          · exact treeInv_agree (h.treesInv s (by simp [h1]))
              fun u hu => hout u (h.disjoint_other (by simp [h1]) hu)
          · exact hL_inv'
          · exact hR_inv'
          · exact treeInv_agree (h.treesInv s (by simp [h2]))
              fun u hu => hout u (h.disjoint_other (by simp [h2]) hu)
        nodupAll := hflat ▸ h.nodupAll
        inCap := fun u hu => h.inCap u (hflat ▸ hu)
        ptrOk := ptrOk_tourDetachLeft h.ptrOk hx_cap
        noRev := by
          rw [hst'_eq]
          exact tourNoRev_pull (tourNoRev_setLeft (tourNoRev_setPar h.noRev)) }
    refine ⟨by simpa using hinv', hout, hval, ?_⟩
    simp only [reduceCtorEq, ↓reduceIte, List.cons_append, List.nil_append] at hphi_le ⊢
    simp only [forestPhi, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    omega

/-- Correctness and non-increasing potential for `tourDetachRight`. -/
theorem tourDetachRight_preserves {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree}
    (h : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) :
    let st' := tourDetachRight st x
    let mid : List AuxTree := [AuxTree.node x L .leaf] ++ (if R = .leaf then [] else [R])
    TourForestInv cap st' (pre ++ mid ++ post) ∧
    (∀ u ∉ (AuxTree.node x L R).toList, st'.nodes u = st.nodes u) ∧
    (∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val) ∧
    forestPhi (pre ++ mid ++ post) ≤ forestPhi (pre ++ AuxTree.node x L R :: post) := by
  have ht_mem : AuxTree.node x L R ∈ pre ++ AuxTree.node x L R :: post := by simp
  have ht := h.treesInv _ ht_mem
  have hx_cap : x ≤ cap := (h.mem_inCap ht_mem (by simp [AuxTree.toList])).2
  have hrev_x : (st.nodes x).rev = false := h.noRev x hx_cap
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨hL_nd, hx_nL, hR_nd, hx_nR, hdisj⟩
  rcases ht.sub with ⟨hx_nz, hl_eq, hr_eq, hpar, _, _, _, hL_sub, hR_sub⟩
  have hphi_le : (AuxTree.node x L .leaf).treePhi tourVSize +
      (if R = .leaf then 0 else R.treePhi tourVSize) ≤ (AuxTree.node x L R).treePhi tourVSize := by
    have hRphi : (if R = .leaf then 0 else R.treePhi tourVSize) = R.treePhi tourVSize := by
      cases R <;> simp [AuxTree.treePhi]
    rw [hRphi]
    simp only [AuxTree.treePhi]
    have hrk : (AuxTree.node x L .leaf).rank tourVSize ≤ (AuxTree.node x L R).rank tourVSize := by
      simp only [AuxTree.rank, treeSize_tourVSize, AuxTree.countNodes]
      exact Nat.log_mono_right (by omega)
    omega
  cases R with
  | leaf =>
    have hr0 : (st.nodes x).right = 0 := by simpa [AuxTree.rootId] using hr_eq
    have hst' : tourDetachRight st x = st := by simp [tourDetachRight, hx_nz, hr0]
    refine ⟨by simpa [hst'] using h, fun _ _ => by simp [hst'], fun _ _ => by simp [hst'],
      by simp⟩
  | node rid rL rR =>
    have hrid_nz : rid ≠ 0 := hR_sub.1
    have hright_rid : (st.nodes x).right = rid := hr_eq
    have hrx : rid ≠ x := fun heq => hx_nR (heq ▸ by simp [AuxTree.toList])
    set st1 := st.setPar rid 0
    set st2 := st1.setRight x 0
    set st' := tourDetachRight st x
    have hst'_eq : st' = pull tourPayload st2 x := by
      simp only [st', tourDetachRight, hx_nz, ↓reduceIte, hright_rid, hrid_nz, st1, st2]
    have hx2 : st2.nodes x = { st.nodes x with right := 0 } := by
      simp [st2, st1, setRight, setPar, hrx.symm]
    have hrid2 : st2.nodes rid = { st.nodes rid with par := 0 } := by
      simp [st2, st1, setRight, setPar, hrx]
    have hu2 : ∀ u, u ≠ x → u ≠ rid → st2.nodes u = st.nodes u := fun u h1 h2 => by
      simp [st2, st1, setRight, setPar, h1, h2]
    have hL2 : SubtreeInv tourPayload st2 x L :=
      SubtreeInv_agree hL_sub fun u hu => (hu2 u (fun heq => hx_nL (heq ▸ hu))
        (fun heq => hdisj u hu (heq ▸ by simp [AuxTree.toList]))).symm
    have hR2 : SubtreeInv tourPayload st2 0 (.node rid rL rR) := by
      rcases AuxTree.nodup_node_unfold hR_nd with ⟨_, hrid_nrL, _, hrid_nrR, _⟩
      rcases hR_sub with ⟨_, hl_r, hr_r, _, _, hsz_r, hsum_r, hrL_sub, hrR_sub⟩
      have h1 : SubtreeInv tourPayload st2 rid rL := SubtreeInv_agree hrL_sub fun u hu =>
        (hu2 u (fun heq => hx_nR (heq ▸ by simp [AuxTree.toList, hu]))
          (fun heq => hrid_nrL (heq ▸ hu))).symm
      have h2 : SubtreeInv tourPayload st2 rid rR := SubtreeInv_agree hrR_sub fun u hu =>
        (hu2 u (fun heq => hx_nR (heq ▸ by simp [AuxTree.toList, hu]))
          (fun heq => hrid_nrR (heq ▸ hu))).symm
      have hevR2 : evalPairs tourPayload st2 (.node rid rL rR) false () =
          evalPairs tourPayload st (.node rid rL rR) false () := by
        refine evalPairs_agree_vrt tourPayload (fun u hu => ?_) false ()
        by_cases hur : u = rid
        · subst hur; simp [hrid2]
        · rw [hu2 u (fun heq => hx_nR (heq ▸ hu)) hur]; exact ⟨rfl, rfl, rfl⟩
      exact ⟨hrid_nz, by simpa [hrid2] using hl_r, by simpa [hrid2] using hr_r,
        by simp [hrid2], fun hc => absurd rfl hc, by simpa [hrid2] using hsz_r,
        by rw [hevR2]; simp [hrid2, hsum_r], h1, h2⟩
    rcases pull_node_build tourPayload_laws (st := st2) (r := .leaf) hx_nz hx_nL
      (by simp [AuxTree.toList]) (by rw [hx2]; exact hl_eq) (by simp [hx2, AuxTree.rootId])
      (by rw [hx2]; exact hpar) (fun hc => absurd rfl hc) (by rw [hx2]; exact hrev_x)
      rfl hL2 trivial with ⟨hx_sub', _, _, _, hne'⟩
    rw [← hst'_eq] at hx_sub' hne'
    have hL_inv' : TreeInv tourPayload st' (.node x L .leaf) :=
      ⟨nodup_node_intro' hL_nd hx_nL (by simp [AuxTree.toList]) (by simp [AuxTree.toList])
        (fun _ _ hb => by simp [AuxTree.toList] at hb), hx_sub'⟩
    have hR_inv' : TreeInv tourPayload st' (.node rid rL rR) :=
      ⟨hR_nd, SubtreeInv_agree hR2 fun u hu => (hne' u (fun heq => hx_nR (heq ▸ hu))).symm⟩
    have hout : ∀ u ∉ (AuxTree.node x L (.node rid rL rR)).toList, st'.nodes u = st.nodes u := by
      intro u hu
      have hux : u ≠ x := fun heq => hu (by subst heq; simp [AuxTree.toList])
      have hur : u ≠ rid := fun heq => hu (by subst heq; simp [AuxTree.toList])
      exact (hne' u hux).trans (hu2 u hux hur)
    have hval : ∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val := fun u _ => by
      rw [hst'_eq, pull_val_eq']
      by_cases hux : u = x
      · subst hux; simp [hx2]
      · by_cases hur : u = rid
        · subst hur; simp [hrid2]
        · rw [hu2 u hux hur]
    have hflat : (pre ++ [AuxTree.node x L .leaf, AuxTree.node rid rL rR] ++ post).flatMap AuxTree.toList =
        (pre ++ AuxTree.node x L (AuxTree.node rid rL rR) :: post).flatMap AuxTree.toList := by
      simp [List.flatMap_append, AuxTree.toList, List.append_assoc]
    have hinv' : TourForestInv cap st' (pre ++ [AuxTree.node x L .leaf, AuxTree.node rid rL rR] ++ post) :=
      { nonEmpty := fun s hs => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with (h1 | rfl | rfl) | h2
          · exact h.nonEmpty s (by simp [h1])
          · simp
          · simp
          · exact h.nonEmpty s (by simp [h2])
        treesInv := fun s hs => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with (h1 | rfl | rfl) | h2
          · exact treeInv_agree (h.treesInv s (by simp [h1]))
              fun u hu => hout u (h.disjoint_other (by simp [h1]) hu)
          · exact hL_inv'
          · exact hR_inv'
          · exact treeInv_agree (h.treesInv s (by simp [h2]))
              fun u hu => hout u (h.disjoint_other (by simp [h2]) hu)
        nodupAll := hflat ▸ h.nodupAll
        inCap := fun u hu => h.inCap u (hflat ▸ hu)
        ptrOk := ptrOk_tourDetachRight h.ptrOk hx_cap
        noRev := by
          rw [hst'_eq]
          exact tourNoRev_pull (tourNoRev_setRight (tourNoRev_setPar h.noRev)) }
    refine ⟨by simpa using hinv', hout, hval, ?_⟩
    simp only [reduceCtorEq, ↓reduceIte, List.cons_append, List.nil_append] at hphi_le ⊢
    simp only [forestPhi, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    omega

/-- Correctness and `O(log (cap + 2))` potential bound for `tourAttachLeft`. -/
theorem tourAttachLeft_preserves {cap y : ℕ} {st : SplayState TourVal TourSum Unit}
    {rest : List AuxTree} {tL R : AuxTree}
    (h : TourForestInv cap st (tL :: AuxTree.node y .leaf R :: rest)) :
    let st' := tourAttachLeft st y tL.rootId
    TourForestInv cap st' (AuxTree.node y tL R :: rest) ∧
    (∀ u ∉ (AuxTree.node y tL R).toList, st'.nodes u = st.nodes u) ∧
    (∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val) ∧
    forestPhi (AuxTree.node y tL R :: rest) ≤
      forestPhi (tL :: AuxTree.node y .leaf R :: rest) + Nat.log 2 (cap + 2) := by
  have htL_mem : tL ∈ tL :: AuxTree.node y .leaf R :: rest := by simp
  have htR_mem : AuxTree.node y .leaf R ∈ tL :: AuxTree.node y .leaf R :: rest := by simp
  have htL := h.treesInv tL htL_mem
  have htR := h.treesInv _ htR_mem
  have htL_ne := h.nonEmpty tL htL_mem
  have hy_cap : y ≤ cap := (h.mem_inCap htR_mem (by simp [AuxTree.toList])).2
  have hl_cap : tL.rootId ≤ cap := (h.mem_inCap htL_mem (AuxTree.rootId_mem htL_ne)).2
  have hrev_y : (st.nodes y).rev = false := h.noRev y hy_cap
  rcases AuxTree.nodup_node_unfold htR.nodup with ⟨_, _, hR_nd, hy_nR, _⟩
  rcases htR.sub with ⟨hy_nz, _, hr_y, hpar_y, _, _, _, _, hR_sub⟩
  have hnd_all := h.nodupAll
  rw [List.flatMap_cons, List.flatMap_cons] at hnd_all
  have hnd1 := List.nodup_append.mp hnd_all
  have hnd2 := List.nodup_append.mp hnd1.2.1
  have hdisj_LR : ∀ a ∈ tL.toList, a ∉ (AuxTree.node y .leaf R).toList := fun a ha hR =>
    hnd1.2.2 a ha a (List.mem_append.mpr (Or.inl hR)) rfl
  have hy_ntL : y ∉ tL.toList := fun hm => hdisj_LR y hm (by simp [AuxTree.toList])
  set l := tL.rootId
  have hl_nz : l ≠ 0 := by
    cases tL with
    | leaf => exact absurd rfl htL_ne
    | node lid _ _ => exact htL.sub.1
  have hly : l ≠ y := fun heq => hy_ntL (heq ▸ AuxTree.rootId_mem htL_ne)
  set st1 := st.setLeft y l
  set st2 := (st1.setPar l y).setPpar l 0
  set st' := tourAttachLeft st y l
  have hst'_eq : st' = pull tourPayload st2 y := by
    simp only [st', tourAttachLeft, hy_nz, ↓reduceIte, hl_nz, st1, st2]
  have hy2 : st2.nodes y = { st.nodes y with left := l } := by
    simp [st2, st1, setPpar, setPar, setLeft, hly.symm]
  have hl2 : st2.nodes l = { st.nodes l with par := y, ppar := 0 } := by
    simp [st2, st1, setPpar, setPar, setLeft, hly]
  have hu2 : ∀ u, u ≠ y → u ≠ l → st2.nodes u = st.nodes u := fun u h1 h2 => by
    simp [st2, st1, setPpar, setPar, setLeft, h1, h2]
  have hR2 : SubtreeInv tourPayload st2 y R :=
    SubtreeInv_agree hR_sub fun u hu => (hu2 u (fun heq => hy_nR (heq ▸ hu))
      (fun heq => hdisj_LR l (AuxTree.rootId_mem htL_ne)
        (by rw [← heq]; simp [AuxTree.toList, hu]))).symm
  have htL2 : SubtreeInv tourPayload st2 y tL := by
    cases htLc : tL with
    | leaf => exact absurd htLc htL_ne
    | node lid lL lR =>
      have hlid : lid = l := by simp [l, htLc, AuxTree.rootId]
      subst hlid
      have hndL := htL.nodup; rw [htLc] at hndL
      rcases AuxTree.nodup_node_unfold hndL with ⟨_, hl_nlL, _, hl_nlR, _⟩
      have hsubL := htL.sub; rw [htLc] at hsubL
      rcases hsubL with ⟨_, hl_l, hr_l, _, _, hsz_l, hsum_l, hlL_sub, hlR_sub⟩
      have h1 : SubtreeInv tourPayload st2 l lL := SubtreeInv_agree hlL_sub fun u hu =>
        (hu2 u (fun heq => hy_ntL (by rw [htLc, ← heq]; simp [AuxTree.toList, hu]))
          (fun heq => hl_nlL (heq ▸ hu))).symm
      have h2 : SubtreeInv tourPayload st2 l lR := SubtreeInv_agree hlR_sub fun u hu =>
        (hu2 u (fun heq => hy_ntL (by rw [htLc, ← heq]; simp [AuxTree.toList, hu]))
          (fun heq => hl_nlR (heq ▸ hu))).symm
      have hevL2 : evalPairs tourPayload st2 (.node l lL lR) false () =
          evalPairs tourPayload st (.node l lL lR) false () := by
        refine evalPairs_agree_vrt tourPayload (fun u hu => ?_) false ()
        by_cases hul : u = l
        · subst hul; simp [hl2]
        · rw [hu2 u (fun heq => hy_ntL (by rw [htLc, ← heq]; exact hu)) hul]; exact ⟨rfl, rfl, rfl⟩
      exact ⟨hl_nz, by simpa [hl2] using hl_l, by simpa [hl2] using hr_l,
        by simp [hl2], fun _ => by simp [hl2], by simpa [hl2] using hsz_l,
        by rw [hevL2]; simp [hl2, hsum_l], h1, h2⟩
  rcases pull_node_build tourPayload_laws (st := st2) hy_nz hy_ntL hy_nR
    (by simp [hy2, l]) (by rw [hy2]; exact hr_y) (by rw [hy2]; exact hpar_y)
    (fun hc => absurd rfl hc) (by rw [hy2]; exact hrev_y) rfl htL2 hR2 with
    ⟨hsub', _, _, _, hne'⟩
  rw [← hst'_eq] at hsub' hne'
  have hnd' : (AuxTree.node y tL R).toList.Nodup :=
    nodup_node_intro' htL.nodup hy_ntL hR_nd hy_nR fun a ha hR =>
      hdisj_LR a ha (by simp [AuxTree.toList, hR])
  have hout : ∀ u ∉ (AuxTree.node y tL R).toList, st'.nodes u = st.nodes u := by
    intro u hu
    have huy : u ≠ y := fun heq => hu (by subst heq; simp [AuxTree.toList])
    have hul : u ≠ l := fun heq => hu (by
      rw [heq]; simp only [AuxTree.toList, List.mem_append]; exact Or.inl (Or.inl (AuxTree.rootId_mem htL_ne)))
    exact (hne' u huy).trans (hu2 u huy hul)
  have hval : ∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val := fun u _ => by
    rw [hst'_eq, pull_val_eq']
    by_cases huy : u = y
    · subst huy; simp [hy2]
    · by_cases hul : u = l
      · subst hul; simp [hl2]
      · rw [hu2 u huy hul]
  have hflat : (AuxTree.node y tL R :: rest).flatMap AuxTree.toList =
      (tL :: AuxTree.node y .leaf R :: rest).flatMap AuxTree.toList := by
    simp [AuxTree.toList, List.append_assoc]
  have hinv' : TourForestInv cap st' (AuxTree.node y tL R :: rest) :=
    { nonEmpty := fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hr
        · simp
        · exact h.nonEmpty s (by simp [hr])
      treesInv := fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hr
        · exact ⟨hnd', hsub'⟩
        · refine treeInv_agree (h.treesInv s (by simp [hr])) fun u hu => hout u fun hm => ?_
          have hurest : u ∈ rest.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨s, hr, hu⟩
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm
          rcases hm with (h1 | rfl) | h2
          · exact hnd1.2.2 u h1 u (List.mem_append.mpr (Or.inr hurest)) rfl
          · exact hnd2.2.2 u (by simp [AuxTree.toList]) u hurest rfl
          · exact hnd2.2.2 u (by simp [AuxTree.toList, h2]) u hurest rfl
      nodupAll := hflat ▸ h.nodupAll
      inCap := fun u hu => h.inCap u (hflat ▸ hu)
      ptrOk := ptrOk_tourAttachLeft h.ptrOk hy_cap hl_cap
      noRev := by
        rw [hst'_eq]
        exact tourNoRev_pull (tourNoRev_setPpar (tourNoRev_setPar (tourNoRev_setLeft h.noRev))) }
  have hcnt : (AuxTree.node y tL R).countNodes ≤ cap := hinv'.countNodes_le (by simp)
  have hrk : (AuxTree.node y tL R).rank tourVSize ≤ Nat.log 2 (cap + 2) := rank_tourVSize_le hcnt
  refine ⟨hinv', hout, hval, ?_⟩
  simp only [forestPhi, List.map_cons, List.sum_cons, AuxTree.treePhi]
  omega

/-- Updating the value of root `x` preserves `TourForestInv` with the exact same `trees`
(zero potential change). -/
theorem tourSetVal_preserves {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree} (v : TourVal)
    (h : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) :
    let st' := tourSetVal st x v
    TourForestInv cap st' (pre ++ AuxTree.node x L R :: post) ∧
    (st'.nodes x).val = v ∧
    (∀ u ≠ x, st'.nodes u = st.nodes u) := by
  have ht_mem : AuxTree.node x L R ∈ pre ++ AuxTree.node x L R :: post := by simp
  have ht := h.treesInv _ ht_mem
  have hx_cap : x ≤ cap := (h.mem_inCap ht_mem (by simp [AuxTree.toList])).2
  have hrev_x : (st.nodes x).rev = false := h.noRev x hx_cap
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨_, hx_nL, _, hx_nR, _⟩
  rcases ht.sub with ⟨hx_nz, hl_x, hr_x, hpar_x, _, _, _, hL_sub, hR_sub⟩
  set st1 := st.updateNode x fun nd => { nd with val := v }
  set st' := tourSetVal st x v
  have hst'_eq : st' = pull tourPayload st1 x := by simp [st', tourSetVal, hx_nz, st1]
  have hL1 : SubtreeInv tourPayload st1 x L :=
    SubtreeInv_agree hL_sub fun u hu => by simp [st1, updateNode, show u ≠ x from fun heq => hx_nL (heq ▸ hu)]
  have hR1 : SubtreeInv tourPayload st1 x R :=
    SubtreeInv_agree hR_sub fun u hu => by simp [st1, updateNode, show u ≠ x from fun heq => hx_nR (heq ▸ hu)]
  rcases pull_node_build tourPayload_laws (st := st1) hx_nz hx_nL hx_nR
    (by simpa [st1] using hl_x) (by simpa [st1] using hr_x) (by simpa [st1] using hpar_x)
    (fun hc => absurd rfl hc) (by simpa [st1] using hrev_x) rfl hL1 hR1 with
    ⟨hx_sub', _, _, _, hne'⟩
  rw [← hst'_eq] at hx_sub' hne'
  have hout : ∀ u ≠ x, st'.nodes u = st.nodes u := fun u hux =>
    (hne' u hux).trans (by simp [st1, updateNode, hux])
  have hinv' : TourForestInv cap st' (pre ++ AuxTree.node x L R :: post) :=
    { nonEmpty := h.nonEmpty
      treesInv := fun s hs => by
        simp only [List.mem_append, List.mem_cons] at hs
        rcases hs with h1 | rfl | h2
        · exact treeInv_agree (h.treesInv s (by simp [h1]))
            fun u hu => hout u fun heq => h.disjoint_other (by simp [h1]) hu (heq ▸ by simp [AuxTree.toList])
        · exact ⟨ht.nodup, hx_sub'⟩
        · exact treeInv_agree (h.treesInv s (by simp [h2]))
            fun u hu => hout u fun heq => h.disjoint_other (by simp [h2]) hu (heq ▸ by simp [AuxTree.toList])
      nodupAll := h.nodupAll
      inCap := h.inCap
      ptrOk := ptrOk_tourSetVal h.ptrOk hx_cap
      noRev := by
        rw [hst'_eq]
        refine tourNoRev_pull fun u hu => ?_
        by_cases hux : u = x
        · subst hux; simpa [st1] using h.noRev u hu
        · simpa [st1, updateNode, hux] using h.noRev u hu }
  exact ⟨hinv', by rw [hst'_eq, pull_val_eq']; simp [st1], hout⟩

end MinCostFlow.SparseCore.Program
