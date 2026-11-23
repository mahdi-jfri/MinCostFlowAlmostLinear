module

public import MinCostFlow.SparseCore.Program.TourSplayModel
public import MinCostFlow.LinkCut.Gen.Splay
public import MinCostFlow.LinkCut.Gen.Walk
public import MinCostFlow.LinkCut.Gen.Descend
import Mathlib.Tactic

/-!
# Representability (`tourOk w`) for tour splay operations

Proves that `TourValsOk w cap st` implies `RotateOk`, `SplayOk`, `WalkOk`, and `DescendOk`
for all `LinkCut.Gen` procedures on a `TourForestInv cap st trees` forest.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree SplayState

/-! ## Word-bound representability (`tourOk w`) -/

/-- Every summary and value in a tour forest is representable at word size `w` whenever
`cap + 2 < 2 ^ w` and every node's `rootTag < 2 ^ w`. -/
def TourValsOk (w cap : ℕ) (st : SplayState TourVal TourSum Unit) : Prop :=
  cap + 2 < 2 ^ w ∧ ∀ u ≤ cap, (st.nodes u).val.rootTag < 2 ^ w

theorem tourOk_pullSum {w cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (hok : TourValsOk w cap st) (hsz : ∀ u ≤ cap, (st.nodes u).sum.sz ≤ cap ∧
      (st.nodes u).sum.openCnt ≤ (st.nodes u).sum.sz ∧
      (st.nodes u).sum.markCnt ≤ (st.nodes u).sum.sz ∧
      (st.nodes u).sum.rootTag < 2 ^ w)
    (hx : x ≤ cap) (hptr : PtrOk cap st)
    (hsum_le : 1 + (if (st.nodes x).left = 0 then 0 else (st.nodes (st.nodes x).left).sum.sz) +
      (if (st.nodes x).right = 0 then 0 else (st.nodes (st.nodes x).right).sum.sz) ≤ cap) :
    (tourOk w).sumOk (pullSum tourPayload st x) := by
  have h1 := hok.1
  have hv := hok.2 x hx
  have hl := hsz (st.nodes x).left (hptr x hx).1
  have hr := hsz (st.nodes x).right (hptr x hx).2.1
  unfold pullSum tourOk tourPayload
  dsimp only
  split_ifs at hsum_le ⊢ <;> (try dsimp) <;> refine ⟨by omega, by omega, by omega, by omega⟩

theorem TourForestInv.sum_bounds {w cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) (hok : TourValsOk w cap st)
    {t : AuxTree} (ht : t ∈ trees) :
    ∀ u ∈ t.toList, (st.nodes u).sum.sz ≤ t.countNodes ∧
      (st.nodes u).sum.openCnt ≤ (st.nodes u).sum.sz ∧
      (st.nodes u).sum.markCnt ≤ (st.nodes u).sum.sz ∧
      (st.nodes u).sum.rootTag < 2 ^ w := by
  have hsub_all : ∀ {rp : ℕ} (c : AuxTree), c.toList.Nodup → SubtreeInv tourPayload st rp c →
      (∀ z ∈ c.toList, z ≤ cap) →
      ∀ u ∈ c.toList, (st.nodes u).sum.sz ≤ c.countNodes ∧
        (st.nodes u).sum.openCnt ≤ (st.nodes u).sum.sz ∧
        (st.nodes u).sum.markCnt ≤ (st.nodes u).sum.sz ∧
        (st.nodes u).sum.rootTag < 2 ^ w := by
    intro rp c hnd hc hcap
    induction c generalizing rp with
    | leaf => intro _ hu; simp [AuxTree.toList] at hu
    | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, _⟩
      rcases hc with ⟨_, _, _, _, _, _, hsum, hsl, hsr⟩
      have hcap_l : ∀ z ∈ l.toList, z ≤ cap := fun z hz => hcap z (by simp [AuxTree.toList, hz])
      have hcap_r : ∀ z ∈ r.toList, z ≤ cap := fun z hz => hcap z (by simp [AuxTree.toList, hz])
      intro u hu
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hu | hiu) | hu
      · have h1 := ihl hl_nd hsl hcap_l u hu
        exact ⟨le_trans h1.1 (by simp [AuxTree.countNodes]; omega), h1.2⟩
      · rw [hiu]
        rw [tourEvalPairs_eq_map (fun z hz => h.noRev z (hcap z hz))] at hsum
        have hsz_eq : (st.nodes id).sum.sz = (AuxTree.node id l r).countNodes := by
          rw [hsum, tourPayload_listSummary_sz, List.length_map, AuxTree.length_toList]
        have hop_le : (st.nodes id).sum.openCnt ≤ (st.nodes id).sum.sz := by
          rw [hsum, tourPayload_listSummary_openCnt, tourPayload_listSummary_sz]
          exact List.length_filter_le _ _
        have hmk_le : (st.nodes id).sum.markCnt ≤ (st.nodes id).sum.sz := by
          rw [hsum, tourPayload_listSummary_markCnt, tourPayload_listSummary_sz]
          exact List.length_filter_le _ _
        have hrt_lt : (st.nodes id).sum.rootTag < 2 ^ w := by
          rw [hsum, tourPayload_listSummary_rootTag, List.map_map]
          have : ∀ xs : List ℕ, (∀ z ∈ xs, z < 2 ^ w) → xs.foldr max 0 < 2 ^ w := by
            intro xs hxs
            induction xs with
            | nil => exact Nat.two_pow_pos w
            | cons a as ih =>
              exact max_lt (hxs a List.mem_cons_self)
                (ih fun b hb => hxs b (List.mem_cons_of_mem _ hb))
          exact this _ fun z hz => by
            obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hz
            exact hok.2 u' (hcap u' hu')
        exact ⟨le_of_eq hsz_eq, hop_le, hmk_le, hrt_lt⟩
      · have h1 := ihr hr_nd hsr hcap_r u hu
        exact ⟨le_trans h1.1 (by simp only [AuxTree.countNodes]; omega), h1.2⟩
  exact hsub_all t (h.treesInv t ht).nodup (h.treesInv t ht).sub (fun z hz => (h.mem_inCap ht hz).2)

theorem tourPushDownOk {w cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (hnr : TourNoRev cap st) (hx : x ≤ cap) :
    PushDownOk (tourOk w) tourPayload st x := by
  refine ⟨?_, ?_⟩
  · intro _ hrev; exact absurd (hnr x hx) (by simp [hrev])
  · intro _ hne; simp [tourPayload] at hne

private theorem tourPull_sum_self (s : SplayState TourVal TourSum Unit) {x : ℕ} (hx : x ≠ 0) :
    ((pull tourPayload s x).nodes x).sum = pullSum tourPayload s x := by
  simp [pull, pullSum, hx, updateNode]

private theorem tourPull_sum_ne (s : SplayState TourVal TourSum Unit) {x y : ℕ} (hne : y ≠ x) :
    ((pull tourPayload s x).nodes y).sum = (s.nodes y).sum := by
  unfold pull; split_ifs
  · rfl
  · simp [updateNode, hne]

private theorem tourValsOk_of_val_eq {w cap : ℕ} {s₁ s₂ : SplayState TourVal TourSum Unit}
    (hok : TourValsOk w cap s₁) (heq : ∀ u ≤ cap, (s₂.nodes u).val = (s₁.nodes u).val) :
    TourValsOk w cap s₂ :=
  ⟨hok.1, fun u hu => by rw [heq u hu]; exact hok.2 u hu⟩

theorem tourRotateOk_of_tree {w cap y : ℕ} {s : SplayState TourVal TourSum Unit} {u : AuxTree}
    (hu : TreeInv tourPayload s u) (hp : PtrOk cap s) (hnr : TourNoRev cap s)
    (hv : TourValsOk w cap s) (hcnt : u.countNodes ≤ cap) (hucap : ∀ z ∈ u.toList, z ≤ cap)
    (hy : y ∈ u.toList) :
    RotateOk (tourOk w) tourPayload s y := by
  intro hy0 hp0
  have hyr : y ≠ u.rootId := by
    intro heq
    have hpar : (s.nodes y).par = u.parentIn y 0 := SubtreeInv_par_eq_parentIn hu.nodup hu.sub hy
    exact hp0 (hpar.trans (by rw [heq, parentIn_rootId]))
  have hclean : ∀ z ∈ u.pathTo y, (s.nodes z).rev = false ∧ (s.nodes z).tag = () :=
    fun z hz => ⟨hnr z (hucap z (AuxTree.mem_pathTo hz)), rfl⟩
  rcases rotate_preserves tourPayload_laws hu hy hyr hclean with ⟨hu', hperm', _, _, _, _⟩
  set s' := rotate tourPayload s y
  have hy_cap : y ≤ cap := hucap y hy
  have hp_eq : (s.nodes y).par = u.parentIn y 0 := SubtreeInv_par_eq_parentIn hu.nodup hu.sub hy
  have hp_mem_u : (s.nodes y).par ∈ u.toList :=
    hp_eq ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hu.nodup hy hyr).1
  have hpy_ne : (s.nodes y).par ≠ y := by
    intro heq
    have hdep := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hu.nodup hy hyr).2.1
    rw [← hp_eq, heq] at hdep; omega
  have hinv' : TourForestInv cap s' [u.rotateAt y] :=
    ⟨fun a ha => by
       rw [List.mem_singleton.mp ha]; intro h0
       have := hperm'.symm.mem_iff.mp hy; rw [h0] at this; simp [AuxTree.toList] at this,
     fun a ha => by rw [List.mem_singleton.mp ha]; exact hu',
     by simpa using hu'.nodup,
     fun z hz => by
       have hzm : z ∈ (u.rotateAt y).toList := by simpa using hz
       exact ⟨Nat.pos_of_ne_zero (SubtreeInv_nonZero hu'.sub hzm), hucap z (hperm'.mem_iff.mp hzm)⟩,
     hp.rotate hy_cap, tourNoRev_rotate hnr⟩
  have hv' : TourValsOk w cap s' := tourValsOk_of_val_eq hv fun z _ => val_rotate_eq s y z
  have hbd := hinv'.sum_bounds hv' List.mem_cons_self
  have hcnt' : (u.rotateAt y).countNodes ≤ cap := by
    rw [← AuxTree.length_toList, hperm'.length_eq, AuxTree.length_toList]; exact hcnt
  have hsum_ok : ∀ z ∈ (u.rotateAt y).toList, (tourOk w).sumOk (s'.nodes z).sum := fun z hz => by
    have hb := hbd z hz; have hw := hv.1
    exact ⟨by omega, by omega, by omega, hb.2.2.2⟩
  have hrot_eq := rotate_eq (P := tourPayload) (st := s) hy0 hp0
  have hsp : pullSum tourPayload (rotateMid s y) (s.nodes y).par = (s'.nodes (s.nodes y).par).sum := by
    rw [show s' = pull tourPayload (pull tourPayload (rotateMid s y) (s.nodes y).par) y from hrot_eq,
      tourPull_sum_ne _ hpy_ne, tourPull_sum_self _ hp0]
  have hsy : pullSum tourPayload (pull tourPayload (rotateMid s y) (s.nodes y).par) y =
      (s'.nodes y).sum := by
    rw [show s' = pull tourPayload (pull tourPayload (rotateMid s y) (s.nodes y).par) y from hrot_eq,
      tourPull_sum_self _ hy0]
  rw [hsp, hsy]
  exact ⟨hsum_ok _ (hperm'.symm.mem_iff.mp hp_mem_u), hsum_ok _ (hperm'.symm.mem_iff.mp hy)⟩

theorem tourSplayOk_of_forest {w cap fuel x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {t : AuxTree}
    (h : TourForestInv cap st (pre ++ t :: post)) (hok : TourValsOk w cap st)
    (hx : x ∈ t.toList) :
    SplayOk (tourOk w) tourPayload st fuel x := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have hx_cap : x ≤ cap := (h.mem_inCap ht_mem hx).2
  have hpp_ok : ∀ k y, y ≤ cap → PushPathOk (tourOk w) tourPayload st k y := by
    intro k
    induction k with
    | zero => intro _ _; trivial
    | succ k ih =>
      intro y hy _
      have hpd : PushDownOk (tourOk w) tourPayload st y := tourPushDownOk h.noRev hy
      refine ⟨fun _ => ih _ (h.ptrOk y hy).2.2.1, ?_⟩
      split_ifs
      · exact hpd
      · rw [tourPushPath_eq_self h.ptrOk h.noRev k _ (h.ptrOk y hy).2.2.1]; exact hpd
  have hstep_ok : ∀ (s : SplayState TourVal TourSum Unit) (u : AuxTree),
      TreeInv tourPayload s u → PtrOk cap s → TourNoRev cap s → TourValsOk w cap s →
      u.countNodes ≤ cap → (∀ z ∈ u.toList, z ≤ cap) → x ∈ u.toList → x ≠ u.rootId →
      SplayStepOk (tourOk w) tourPayload s x := by
    intro s u hu hp hnr hv hcnt hucap hxu hxr
    have hp_eq : (s.nodes x).par = u.parentIn x 0 := SubtreeInv_par_eq_parentIn hu.nodup hu.sub hxu
    have hp_mem : (s.nodes x).par ∈ u.toList :=
      hp_eq ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hu.nodup hxu hxr).1
    unfold SplayStepOk; dsimp only
    split_ifs with hg hzz
    · exact tourRotateOk_of_tree hu hp hnr hv hcnt hucap hxu
    · have hpr : (s.nodes x).par ≠ u.rootId := by
        intro heq
        have hgp : (s.nodes (s.nodes x).par).par = u.parentIn (s.nodes x).par 0 :=
          SubtreeInv_par_eq_parentIn hu.nodup hu.sub hp_mem
        exact hg (hgp.trans (by rw [heq, parentIn_rootId]))
      have hclean_p : ∀ z ∈ u.pathTo (s.nodes x).par, (s.nodes z).rev = false ∧ (s.nodes z).tag = () :=
        fun z hz => ⟨hnr z (hucap z (AuxTree.mem_pathTo hz)), rfl⟩
      rcases rotate_preserves tourPayload_laws hu hp_mem hpr hclean_p with ⟨hu1, hperm1, _, _, _, _⟩
      have hcnt1 : (u.rotateAt (s.nodes x).par).countNodes ≤ cap := by
        rw [← AuxTree.length_toList, hperm1.length_eq, AuxTree.length_toList]; exact hcnt
      exact ⟨tourRotateOk_of_tree hu hp hnr hv hcnt hucap hp_mem,
        tourRotateOk_of_tree hu1 (hp.rotate (hucap _ hp_mem))
          (tourNoRev_rotate hnr)
          (tourValsOk_of_val_eq hv fun z _ => val_rotate_eq s _ z)
          hcnt1 (fun z hz => hucap z (hperm1.mem_iff.mp hz)) (hperm1.symm.mem_iff.mp hxu)⟩
    · have hclean_x : ∀ z ∈ u.pathTo x, (s.nodes z).rev = false ∧ (s.nodes z).tag = () :=
        fun z hz => ⟨hnr z (hucap z (AuxTree.mem_pathTo hz)), rfl⟩
      rcases rotate_preserves tourPayload_laws hu hxu hxr hclean_x with ⟨hu1, hperm1, _, _, _, _⟩
      have hcnt1 : (u.rotateAt x).countNodes ≤ cap := by
        rw [← AuxTree.length_toList, hperm1.length_eq, AuxTree.length_toList]; exact hcnt
      exact ⟨tourRotateOk_of_tree hu hp hnr hv hcnt hucap hxu,
        tourRotateOk_of_tree hu1 (hp.rotate (hucap x hxu))
          (tourNoRev_rotate hnr)
          (tourValsOk_of_val_eq hv fun z _ => val_rotate_eq s x z)
          hcnt1 (fun z hz => hucap z (hperm1.mem_iff.mp hz)) (hperm1.symm.mem_iff.mp hxu)⟩
  have hloop_ok : ∀ k (s : SplayState TourVal TourSum Unit) (u : AuxTree),
      TreeInv tourPayload s u → PtrOk cap s → TourNoRev cap s → TourValsOk w cap s →
      u.countNodes ≤ cap → (∀ z ∈ u.toList, z ≤ cap) → x ∈ u.toList →
      SplayLoopOk (tourOk w) tourPayload s k x := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ _ _ _ _; trivial
    | succ k ih =>
      intro s u hu hp hnr hv hcnt hucap hxu hx0 hp0
      have hxr : x ≠ u.rootId := by
        intro heq
        have hpar : (s.nodes x).par = u.parentIn x 0 := SubtreeInv_par_eq_parentIn hu.nodup hu.sub hxu
        exact hp0 (hpar.trans (by rw [heq, parentIn_rootId]))
      have hclean : ∀ z ∈ u.pathTo x, (s.nodes z).rev = false ∧ (s.nodes z).tag = () :=
        fun z hz => ⟨hnr z (hucap z (AuxTree.mem_pathTo hz)), rfl⟩
      rcases splayStep_preserves tourPayload_laws hu hxu hxr hclean with
        ⟨u', hu', hperm', _, _, _, _, _, _, _⟩
      have hcnt' : u'.countNodes ≤ cap := by
        rw [← AuxTree.length_toList, hperm'.length_eq, AuxTree.length_toList]; exact hcnt
      have hnr' : TourNoRev cap (splayStep tourPayload s x) := by
        unfold splayStep; dsimp only
        rw [ite_eq_right_iff.mpr (fun heq => absurd heq hx0),
          ite_eq_right_iff.mpr (fun heq => absurd heq hp0)]
        split_ifs
        · exact tourNoRev_rotate hnr
        · exact tourNoRev_rotate (tourNoRev_rotate hnr)
        · exact tourNoRev_rotate (tourNoRev_rotate hnr)
      have hv' : TourValsOk w cap (splayStep tourPayload s x) := by
        refine tourValsOk_of_val_eq hv fun z _ => ?_
        unfold splayStep; dsimp only
        rw [ite_eq_right_iff.mpr (fun heq => absurd heq hx0),
          ite_eq_right_iff.mpr (fun heq => absurd heq hp0)]
        split_ifs
        · exact val_rotate_eq s x z
        · rw [val_rotate_eq, val_rotate_eq]
        · rw [val_rotate_eq, val_rotate_eq]
      exact ⟨hstep_ok s u hu hp hnr hv hcnt hucap hxu hxr,
        ih _ u' hu' (hp.splayStep (hucap x hxu)) hnr' hv' hcnt'
          (fun z hz => hucap z (hperm'.mem_iff.mp hz)) (hperm'.symm.mem_iff.mp hxu)⟩
  intro _
  refine ⟨hpp_ok fuel x hx_cap, ?_⟩
  rw [tourPushPath_eq_self h.ptrOk h.noRev fuel x hx_cap]
  exact hloop_ok fuel st t (h.treesInv t ht_mem) h.ptrOk h.noRev hok (h.countNodes_le ht_mem)
    (fun z hz => (h.mem_inCap ht_mem hz).2) hx

theorem tourWalkOk_of_forest {w cap : ℕ} {st : SplayState TourVal TourSum Unit}
    (hp : PtrOk cap st) (hnr : TourNoRev cap st) :
    ∀ k x, x ≤ cap → WalkOk (tourOk w) tourPayload st k x
  | 0, _, _ => trivial
  | k + 1, x, hx => fun _ => by
    refine ⟨tourPushDownOk hnr hx, ?_⟩
    rw [tourPushDown_eq_self hnr hx]
    exact tourWalkOk_of_forest hp hnr k (st.nodes x).left (hp x hx).1

theorem tourDescendOk_of_forest {w cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (hp : PtrOk cap st) (hnr : TourNoRev cap st) :
    ∀ k x, x ≤ cap → DescendOk (tourOk w) tourPayload rs rv st k x
  | 0, _, _ => trivial
  | k + 1, x, hx => by
    unfold DescendOk; dsimp only
    refine ⟨tourPushDownOk hnr hx, ?_⟩
    rw [tourPushDown_eq_self hnr hx]
    split_ifs
    · exact tourDescendOk_of_forest hp hnr k (st.nodes x).left (hp x hx).1
    · exact tourDescendOk_of_forest hp hnr k (st.nodes x).right (hp x hx).2.1

end MinCostFlow.SparseCore.Program
