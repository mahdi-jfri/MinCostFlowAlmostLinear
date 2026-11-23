module

public import MinCostFlow.SparseCore.Program.TourOpsList
import Mathlib.Tactic

/-!
# Zero-scratch splay listing procedures (`tourWalk0Body`, `tourDescMark0Body`, `tourListMark0Body`)

Because `tourPayload` has trivial lazy tags (`Unit`) and `TourForestInv` maintains `TourNoRev`
(`rev = false`), `pushDown` and `pushPath` are the identity on states. Calling `splayLoopBody`
directly together with zero-heap `tourWalk0Body` and `tourDescMark0Body` removes the `2`-word
splay scratch requirement, giving `tourListMark0Body_runs` under `HeapOk ... splayHeap 0 mem`
(`splayHeap < 2 ^ w`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Zero-scratch `splayLoop` amortized bound with descent credit -/

/-- Running `splayLoopBody` on `x ∈ t.toList` under `TourForestInv` requires `0` heap scratch
(`HeapOk ... heap 0 mem`) and retains `5000 * (t.depthOf x / 2)` credit to pay for a preceding
`tourWalk0Body` or `tourDescMark0Body`. -/
theorem tourSplayLoop_runs_amort {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {pre post : List AuxTree} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (pre ++ t :: post)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : t.depthOf x < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem) :
    ∃ t' o st' c,
      let s' := SplayState.splay tourPayload st fuel x
      Runs w p ω (splayLoopBody C.splay.loop C.splay.step)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (pre ++ t' :: post) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = x ∧ t'.toList = t.toList ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + 5000 * (t.depthOf x / 2) + TOUR_PHI_MULT * forestPhi (pre ++ t' :: post) ≤
        TOUR_PHI_MULT * forestPhi (pre ++ t :: post) + TOUR_SPLAY_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have hx_in := hf.mem_inCap ht_mem hx
  have hx_nz : x ≠ 0 := by omega
  have hx_cap : x ≤ cap := hx_in.2
  have hpp : SplayState.pushPath tourPayload st fuel x = st :=
    tourPushPath_eq_self hf.ptrOk hf.noRev fuel x hx_cap
  have hsp_eq : SplayState.splay tourPayload st fuel x = SplayState.splayLoop tourPayload st fuel x := by
    simp [SplayState.splay, hx_nz, hpp]
  have hokL : SplayLoopOk (tourOk w) tourPayload st fuel x := by
    have h : SplayOk (tourOk w) tourPayload st fuel x := tourSplayOk_of_forest hf hvals hx
    have h2 := (h hx_nz).2
    rwa [hpp] at h2
  have hheap' : HeapOk tourLayout w nb cap heap C.steps.space mem := by
    simpa [C.steps_space] using hheap
  obtain ⟨o, st', c, hrun, ⟨hn', hfr'⟩, hc⟩ :=
    splayLoopBody_runs C.steps C.splay.pull_body C.splay.rotate_body C.splay.step_body
      C.splay.loop_body ω fuel x pos hnodes hf.ptrOk hx_cap hheap' hfuelW hokL
  obtain ⟨t', hinv', hne', hroot', hlist', hout', hval', hphi'⟩ := tourSplay_preserves hf hx hfuel
  have hsc := splayCost_le tourPayload_laws C.steps (hf.treesInv t ht_mem) hx hfuel
  rw [splayDepth_eq_depthOf (hf.treesInv t ht_mem) hx hfuel, C.splayRate_eq] at hsc
  have hc_sc : c ≤ splayCost C.steps st fuel x := by
    unfold splayCost; rw [hpp]; omega
  rw [← hsp_eq] at hn'
  refine ⟨t', o, st', c, hrun, hn', hfr', hinv',
    ⟨hvals.1, fun u hu => by rw [hval' u hu]; exact hvals.2 u hu⟩,
    hne', hroot', hlist', hout', ?_⟩
  have h1 : c ≤ (t.depthOf x / 2 + 1) * 9700 := le_trans hc_sc hsc
  have h2 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi'
  simp only [TOUR_PHI_MULT, TOUR_SPLAY_AMORT] at h2 ⊢
  nlinarith

/-! ## Zero-heap `tourWalk0Body` and `tourDescMark0Body` -/

/-- Zero-heap leftmost walk `[nb, x, fuel, heap]`: follows `left` pointers in `TourNoRev` trees. -/
def tourWalk0Body : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1)))) ;;
  .loop (.reg 4)
    (.assign 1 (.reg 4) ;;
     .assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))) ;;
  .ret (.reg 1)

/-- Zero-heap leftmost-marked descent `[nb, x, fuel, heap]`: walks down to the leftmost node with
`isMarked = true` in a `TourNoRev` tree whose root has `0 < markCnt`. -/
def tourDescMark0Body : Stmt :=
  .assign 4 (.const 1) ;;
  .loop (.reg 4)
    (.assign 5 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) ;;
     .assign 6 (.load (.reg 5)) ;;
     .assign 7 (.const 0) ;;
     .cond (.reg 6)
       (.assign 7 (.bin .lt (.const 0)
         (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 6))) (.const 14)))))
       .nop ;;
     .cond (.reg 7)
       (.assign 1 (.reg 6))
       (.cond (.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 10))))
         (.assign 4 (.const 0))
         (.assign 1 (.load (.bin .add (.reg 5) (.const 1)))))) ;;
  .ret (.reg 1)

theorem tourListZero_bodies_noRand :
    tourWalk0Body.NoRand ∧ tourDescMark0Body.NoRand := by
  simp [tourWalk0Body, tourDescMark0Body, Stmt.NoRand]

private theorem subtree_sum_markCnt {st : SplayState TourVal TourSum Unit} {par : ℕ} {t : AuxTree}
    (hsub : SubtreeInv tourPayload st par t) (ht : t ≠ .leaf)
    (hnr : ∀ u ∈ t.toList, (st.nodes u).rev = false) :
    (st.nodes t.rootId).sum.markCnt = (t.toList.filter fun u => (st.nodes u).val.isMarked).length := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r =>
    have hsum := hsub.2.2.2.2.2.2.1
    simp only [AuxTree.rootId]
    rw [hsum, tourEvalPairs_eq_map hnr, tourPayload_listSummary_markCnt, List.filter_map, List.length_map]
    rfl

private theorem tourWalk0Body_runs {w nb cap heap fuel pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState TourVal TourSum Unit} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (ht_inv : TreeInv tourPayload st t) (ht_ne : t ≠ .leaf)
    (ht_cap : ∀ u ∈ t.toList, 1 ≤ u ∧ u ≤ cap)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem) :
    ∃ m st' c,
      Runs w p ω tourWalk0Body (startState [nb, t.rootId, fuel, heap] mem pos) (.returned m) st' c ∧
      st'.mem = mem ∧ m ∈ t.toList ∧ t.toList.head? = some m ∧
      c ≤ 25 * (t.depthOf m + 1) + 20 := by
  have hwide := hheap.wide; have hroom := hheap.room
  have hA : ∀ u ≤ cap, nb + 17 * u + 17 ≤ heap := fun u hu => by
    simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hu
  have hloop : ∀ (s : AuxTree) (par : ℕ) (regs : ℕ → ℕ) (lpos : ℕ),
      SubtreeInv tourPayload st par s → s.toList.Nodup → s ≠ .leaf → (∀ u ∈ s.toList, 1 ≤ u ∧ u ≤ cap) →
      regs 0 = nb → regs 1 = s.rootId → regs 4 = (st.nodes s.rootId).left →
      ∃ m regs' lpos' c,
        Runs w p ω (.loop (.reg 4)
          (.assign 1 (.reg 4) ;;
           .assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))))
          ⟨mem, regs, lpos⟩ .normal ⟨mem, regs', lpos'⟩ c ∧
        regs' 1 = m ∧ m ∈ s.toList ∧ s.toList.head? = some m ∧
        c ≤ 25 * s.depthOf m + 10 := by
    intro s
    induction s with
    | leaf => intro _ _ _ _ _ hne; exact absurd rfl hne
    | node id L R ihL _ =>
      intro par regs lpos hsub hnd _ hcap hr0 hr1 hr4
      have hid_cap : id ≤ cap := (hcap id (by simp [AuxTree.toList])).2
      have hl_eq : (st.nodes id).left = L.rootId := hsub.2.1
      cases L with
      | leaf =>
        have hr40 : regs 4 = 0 := by simpa [AuxTree.rootId] using hr4.trans hl_eq
        refine ⟨id, regs, lpos, 2,
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr40], rfl, rfl, rfl⟩),
          by simpa [AuxTree.rootId] using hr1, by simp [AuxTree.toList], by simp [AuxTree.toList], by omega⟩
      | node lid lL lR =>
        set Lne := AuxTree.node lid lL lR
        have hL_sub : SubtreeInv tourPayload st id Lne := hsub.2.2.2.2.2.2.2.1
        have hL_nd : Lne.toList.Nodup := (AuxTree.nodup_node_unfold hnd).1
        have hL_cap : ∀ u ∈ Lne.toList, 1 ≤ u ∧ u ≤ cap :=
          fun u hu => hcap u (by simp [AuxTree.toList, hu])
        have hlid_nz : lid ≠ 0 := hL_sub.1
        have hlid_cap : lid ≤ cap := (hL_cap lid (by simp [Lne, AuxTree.toList])).2
        have hAlid := hA lid hlid_cap
        have hr4_lid : regs 4 = lid := by simpa [Lne, AuxTree.rootId] using hr4.trans hl_eq
        set r1 := Function.update regs 1 lid
        set r2 := Function.update r1 4 (st.nodes lid).left
        have ha1 : Runs w p ω (.assign 1 (.reg 4)) ⟨mem, regs, lpos⟩ .normal ⟨mem, r1, lpos⟩ 2 :=
          runs_assign_iff.mpr ⟨lid, by simp [Expr.eval, hr4_lid], rfl, rfl, rfl⟩
        have hm_lid : mem (nb + 17 * lid) = (st.nodes lid).left := by
          simpa [nodeAddr, tourLayout_stride, OFF_LEFT] using (hnodes lid hlid_cap).1
        have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1)))))
            ⟨mem, r1, lpos⟩ .normal ⟨mem, r2, lpos⟩ 7 :=
          runs_assign_iff.mpr ⟨(st.nodes lid).left, by
            simp [Expr.eval, r1, hr0, BinOp.eval, hm_lid,
              (by omega : 17 < 2 ^ w), (by omega : 17 * lid < 2 ^ w), (by omega : nb + 17 * lid < 2 ^ w)],
            rfl, rfl, rfl⟩
        obtain ⟨m, regs', lpos', c', hrun', hm_r1, hm_L, hm_hd, hc'⟩ :=
          ihL id r2 lpos hL_sub hL_nd (by simp [Lne]) hL_cap (by simp [r2, r1, hr0])
            (by simp [r2, r1, Lne, AuxTree.rootId]) (by simp [r2, Lne, AuxTree.rootId])
        have hm_ne_id : m ≠ id := fun h => (AuxTree.nodup_node_unfold hnd).2.1 (h ▸ hm_L)
        have hdep : (AuxTree.node id Lne R).depthOf m = 1 + Lne.depthOf m := by
          rw [AuxTree.depthOf.eq_2]; simp [hm_ne_id, hm_L]; omega
        have hL_ne : Lne.toList ≠ [] := List.ne_nil_of_mem hm_L
        refine ⟨m, regs', lpos', _,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨lid, ⟨mem, r2, lpos⟩, _, c',
            by simp [Expr.eval, hr4_lid], hlid_nz, tour_runs_seq_normal ha1 ha4, hrun', rfl⟩)),
          hm_r1, by simp [AuxTree.toList, hm_L],
          by rw [AuxTree.toList, List.append_assoc, List.head?_append_of_ne_nil _ hL_ne]; exact hm_hd,
          by rw [hdep]; simp only [Expr.size]; omega⟩
  unfold tourWalk0Body; rw [startState]
  set r0 := fun i => [nb, t.rootId, fuel, heap].getD i 0
  have hr_cap : t.rootId ≤ cap := (ht_cap t.rootId (AuxTree.rootId_mem ht_ne)).2
  have hAr := hA t.rootId hr_cap
  have hm_r : mem (nb + 17 * t.rootId) = (st.nodes t.rootId).left := by
    simpa [nodeAddr, tourLayout_stride, OFF_LEFT] using (hnodes t.rootId hr_cap).1
  set r1 := Function.update r0 4 (st.nodes t.rootId).left
  have ha0 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1)))))
      ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ 7 :=
    runs_assign_iff.mpr ⟨(st.nodes t.rootId).left, by
      simp [Expr.eval, r0, BinOp.eval, hm_r,
        (by omega : 17 < 2 ^ w), (by omega : 17 * t.rootId < 2 ^ w), (by omega : nb + 17 * t.rootId < 2 ^ w)],
      rfl, rfl, rfl⟩
  obtain ⟨m, regs', lpos', c_lp, hrun_lp, hm_r1, hm_t, hm_hd, hc_lp⟩ :=
    hloop t 0 r1 pos ht_inv.sub ht_inv.nodup ht_ne ht_cap (by simp [r1, r0]) (by simp [r1, r0]) (by simp [r1])
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem, regs', lpos'⟩) (r := 1) (v := m) hm_r1
  exact ⟨m, ⟨mem, regs', lpos'⟩, _, tour_runs_seq_normal ha0 (tour_runs_seq_normal hrun_lp hret),
    rfl, hm_t, hm_hd, by omega⟩

private theorem tourDescMark0Body_runs {w nb cap heap fuel pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState TourVal TourSum Unit} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (ht_inv : TreeInv tourPayload st t) (ht_ne : t ≠ .leaf)
    (ht_cap : ∀ u ∈ t.toList, 1 ≤ u ∧ u ≤ cap)
    (ht_nr : ∀ u ∈ t.toList, (st.nodes u).rev = false)
    (hmk : 0 < (st.nodes t.rootId).sum.markCnt)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem) :
    ∃ y st' c,
      Runs w p ω tourDescMark0Body (startState [nb, t.rootId, fuel, heap] mem pos) (.returned y) st' c ∧
      st'.mem = mem ∧ y ∈ t.toList ∧
      t.toList.find? (fun u => (st.nodes u).val.isMarked) = some y ∧
      c ≤ 65 * (t.depthOf y + 1) + 20 := by
  have hwide := hheap.wide; have hroom := hheap.room
  have hA : ∀ u ≤ cap, nb + 17 * u + 17 ≤ heap := fun u hu => by
    simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hu
  set lbody : Stmt :=
    .assign 5 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) ;;
    .assign 6 (.load (.reg 5)) ;;
    .assign 7 (.const 0) ;;
    .cond (.reg 6)
      (.assign 7 (.bin .lt (.const 0)
        (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 6))) (.const 14)))))
      .nop ;;
    .cond (.reg 7)
      (.assign 1 (.reg 6))
      (.cond (.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 10))))
        (.assign 4 (.const 0))
        (.assign 1 (.load (.bin .add (.reg 5) (.const 1)))))
  have hloop : ∀ (s : AuxTree) (par : ℕ) (regs : ℕ → ℕ) (lpos : ℕ),
      SubtreeInv tourPayload st par s → s.toList.Nodup → s ≠ .leaf →
      (∀ u ∈ s.toList, 1 ≤ u ∧ u ≤ cap) →
      (∀ u ∈ s.toList, (st.nodes u).rev = false) →
      0 < (st.nodes s.rootId).sum.markCnt →
      regs 0 = nb → regs 1 = s.rootId → regs 4 = 1 →
      ∃ y regs' lpos' c,
        Runs w p ω (.loop (.reg 4) lbody) ⟨mem, regs, lpos⟩ .normal ⟨mem, regs', lpos'⟩ c ∧
        regs' 1 = y ∧ y ∈ s.toList ∧
        s.toList.find? (fun u => (st.nodes u).val.isMarked) = some y ∧
        c ≤ 65 * (s.depthOf y + 1) + 10 := by
    intro s
    induction s with
    | leaf => intro _ _ _ _ _ hne; exact absurd rfl hne
    | node id L R ihL ihR =>
      intro par regs lpos hsub hnd _ hcap hnr hmkS hr0 hr1 hr4
      have hid_cap : id ≤ cap := (hcap id (by simp [AuxTree.toList])).2
      have hAid := hA id hid_cap
      have hl_eq : (st.nodes id).left = L.rootId := hsub.2.1
      have hr_eq : (st.nodes id).right = R.rootId := hsub.2.2.1
      have hnd_nd := AuxTree.nodup_node_unfold hnd
      have hL_nr : ∀ u ∈ L.toList, (st.nodes u).rev = false :=
        fun u hu => hnr u (by simp [AuxTree.toList, hu])
      have hR_nr : ∀ u ∈ R.toList, (st.nodes u).rev = false :=
        fun u hu => hnr u (by simp [AuxTree.toList, hu])
      have hL_cap : ∀ u ∈ L.toList, 1 ≤ u ∧ u ≤ cap :=
        fun u hu => hcap u (by simp [AuxTree.toList, hu])
      have hR_cap : ∀ u ∈ R.toList, 1 ≤ u ∧ u ≤ cap :=
        fun u hu => hcap u (by simp [AuxTree.toList, hu])
      have hm_l : mem (nb + 17 * id) = L.rootId := by
        simpa [nodeAddr, tourLayout_stride, OFF_LEFT, hl_eq] using (hnodes id hid_cap).1
      have hm_r : mem (nb + 17 * id + 1) = R.rootId := by
        simpa [nodeAddr, tourLayout_stride, OFF_RIGHT, hr_eq] using (hnodes id hid_cap).2.1
      have hm_mk : mem (nb + 17 * id + 10) = if (st.nodes id).val.isMarked then 1 else 0 := by
        simpa [nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using (hnodes id hid_cap).2.2.2.2.2.2.1.2.2.2.2.1
      set r1 := Function.update regs 5 (nb + 17 * id)
      set r2 := Function.update r1 6 L.rootId
      set r3 := Function.update r2 7 0
      have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))
          ⟨mem, regs, lpos⟩ .normal ⟨mem, r1, lpos⟩ 6 :=
        runs_assign_iff.mpr ⟨nb + 17 * id, by
          simp [Expr.eval, hr0, hr1, AuxTree.rootId, BinOp.eval,
            (by omega : 17 < 2 ^ w), (by omega : 17 * id < 2 ^ w), (by omega : nb + 17 * id < 2 ^ w)],
          rfl, rfl, rfl⟩
      have ha6 : Runs w p ω (.assign 6 (.load (.reg 5))) ⟨mem, r1, lpos⟩ .normal ⟨mem, r2, lpos⟩ 3 :=
        runs_assign_iff.mpr ⟨L.rootId, by simp [Expr.eval, r1, hm_l], rfl, rfl, rfl⟩
      have ha7 : Runs w p ω (.assign 7 (.const 0)) ⟨mem, r2, lpos⟩ .normal ⟨mem, r3, lpos⟩ 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
      set goL : ℕ := if L = .leaf then 0 else if 0 < (st.nodes L.rootId).sum.markCnt then 1 else 0
      set r4 := Function.update r3 7 goL
      have hcond_L : ∃ cL, cL ≤ 16 ∧
          Runs w p ω (.cond (.reg 6)
            (.assign 7 (.bin .lt (.const 0)
              (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 6))) (.const 14)))))
            .nop) ⟨mem, r3, lpos⟩ .normal ⟨mem, r4, lpos⟩ cL := by
        cases L with
        | leaf =>
          have hr4_eq : r4 = r3 := by
            funext k; by_cases hk : k = 7 <;> simp [r4, r3, goL, hk]
          rw [hr4_eq]
          exact ⟨_, by simp [Expr.size], tour_runs_cond_false (by simp [Expr.eval, r3, r2, AuxTree.rootId])
            (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)⟩
        | node lid lL lR =>
          have hlid_nz : lid ≠ 0 := hsub.2.2.2.2.2.2.2.1.1
          have hlid_cap : lid ≤ cap := (hL_cap lid (by simp [AuxTree.toList])).2
          have hAlid := hA lid hlid_cap
          have hm_lmk : mem (nb + 17 * lid + 14) = (st.nodes lid).sum.markCnt := by
            simpa [nodeAddr, tourLayout_stride, tourLayout_offSum] using (hnodes lid hlid_cap).2.2.2.2.2.2.2.1.2.2.1
          have hgoL_eq : goL = if 0 < (st.nodes lid).sum.markCnt then 1 else 0 := by
            dsimp only [goL]; split_ifs <;> simp_all [AuxTree.rootId]
          have hset7 : Runs w p ω (.assign 7 (.bin .lt (.const 0)
              (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 6))) (.const 14)))))
              ⟨mem, r3, lpos⟩ .normal ⟨mem, r4, lpos⟩ 11 :=
            runs_assign_iff.mpr ⟨goL, by
              have hlt1 : (if 0 < (st.nodes lid).sum.markCnt then 1 else 0) < 2 ^ w := by split_ifs <;> omega
              simp [Expr.eval, r3, r2, r1, hr0, AuxTree.rootId, BinOp.eval, hm_lmk, hgoL_eq, hlt1,
                (by omega : 0 < 2 ^ w), (by omega : 14 < 2 ^ w), (by omega : 17 < 2 ^ w),
                (by omega : 17 * lid < 2 ^ w), (by omega : nb + 17 * lid < 2 ^ w),
                (by omega : nb + 17 * lid + 14 < 2 ^ w)],
              rfl, rfl, rfl⟩
          exact ⟨_, by simp [Expr.size],
            tour_runs_cond_true (by simp [Expr.eval, r3, r2, AuxTree.rootId]) hlid_nz hset7⟩
      obtain ⟨cL, hcL, hrunL⟩ := hcond_L
      by_cases hgoL : goL = 1
      · have hL_ne : L ≠ .leaf := by intro h; simp [goL, h] at hgoL
        have hL_mk : 0 < (st.nodes L.rootId).sum.markCnt := by
          by_contra hle
          have : goL = 0 := by simp [goL, hL_ne, hle]
          omega
        set r5 := Function.update r4 1 L.rootId
        have hst1 : Runs w p ω (.assign 1 (.reg 6)) ⟨mem, r4, lpos⟩ .normal ⟨mem, r5, lpos⟩ 2 :=
          runs_assign_iff.mpr ⟨L.rootId, by simp [Expr.eval, r4, r3, r2], rfl, rfl, rfl⟩
        have hcond7 := tour_runs_cond_true (e := .reg 7) (v := 1) (st := ⟨mem, r4, lpos⟩)
          (s₂ := .cond (.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 10))))
            (.assign 4 (.const 0)) (.assign 1 (.load (.bin .add (.reg 5) (.const 1)))))
          (by simp [Expr.eval, r4, hgoL]) (by omega) hst1
        obtain ⟨y, regs', lpos', c', hrun', hy_r1, hy_L, hy_find, hc'⟩ :=
          ihL id r5 lpos hsub.2.2.2.2.2.2.2.1 hnd_nd.1 hL_ne hL_cap hL_nr hL_mk
            (by simp [r5, r4, r3, r2, r1, hr0]) (by simp [r5]) (by simp [r5, r4, r3, r2, r1, hr4])
        have hy_ne_id : y ≠ id := fun h => hnd_nd.2.1 (h ▸ hy_L)
        have hdep : (AuxTree.node id L R).depthOf y = 1 + L.depthOf y := by
          rw [AuxTree.depthOf.eq_2]; simp [hy_ne_id, hy_L]; omega
        have hfind_all : (AuxTree.node id L R).toList.find? (fun u => (st.nodes u).val.isMarked) = some y := by
          rw [AuxTree.toList, List.append_assoc, List.find?_append, hy_find]; rfl
        have hbody := tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hrunL hcond7)))
        refine ⟨y, regs', lpos', _,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, ⟨mem, r5, lpos⟩, _, c',
            by simp [Expr.eval, hr4], by omega, hbody, hrun', rfl⟩)),
          hy_r1, by simp [AuxTree.toList, hy_L], hfind_all, ?_⟩
        rw [hdep]; simp only [Expr.size]; omega
      · have hgoL0 : goL = 0 := by dsimp only [goL] at hgoL ⊢; split_ifs at hgoL ⊢ <;> omega
        have hL_none : L.toList.find? (fun u => (st.nodes u).val.isMarked) = none := by
          cases L with
          | leaf => rfl
          | node lid lL lR =>
            have hL0 : (st.nodes lid).sum.markCnt = 0 := by
              by_contra hnz
              exact hgoL (by simp [goL, AuxTree.rootId, show 0 < (st.nodes lid).sum.markCnt by omega])
            have hfil := subtree_sum_markCnt hsub.2.2.2.2.2.2.2.1 (by simp) hL_nr
            simp only [AuxTree.rootId, hL0] at hfil
            have hnil : ((AuxTree.node lid lL lR).toList.filter fun u => (st.nodes u).val.isMarked) = [] :=
              List.eq_nil_of_length_eq_zero hfil.symm
            exact List.find?_eq_none.mpr fun u hu hm => (List.filter_eq_nil_iff.mp hnil u hu) hm
        cases hmk_id : (st.nodes id).val.isMarked with
        | true =>
          set r5 := Function.update r4 4 0
          have hev_mk : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 10)))).eval w ⟨mem, r4, lpos⟩ = some 1 := by
            simp [Expr.eval, r4, r3, r2, r1, BinOp.eval, hm_mk, hmk_id,
              (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w), (by omega : 10 < 2 ^ w), (by omega : nb + 17 * id + 10 < 2 ^ w)]
          have hst4 : Runs w p ω (.assign 4 (.const 0)) ⟨mem, r4, lpos⟩ .normal ⟨mem, r5, lpos⟩ 2 :=
            runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
          have hcond_mk := tour_runs_cond_true (s₂ := .assign 1 (.load (.bin .add (.reg 5) (.const 1)))) hev_mk (by omega) hst4
          have hcond7 := tour_runs_cond_false (e := .reg 7) (s₁ := .assign 1 (.reg 6))
            (by simp [Expr.eval, r4, hgoL0]) hcond_mk
          have hbody := tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hrunL hcond7)))
          have hexit : Runs w p ω (.loop (.reg 4) lbody) ⟨mem, r5, lpos⟩ .normal ⟨mem, r5, lpos⟩ 2 :=
            runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, r5], rfl, rfl, rfl⟩)
          have hfind_id : (AuxTree.node id L R).toList.find? (fun u => (st.nodes u).val.isMarked) = some id := by
            rw [AuxTree.toList, List.append_assoc, List.find?_append, hL_none]; simp [hmk_id]
          refine ⟨id, r5, lpos, _,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, ⟨mem, r5, lpos⟩, _, 2,
              by simp [Expr.eval, hr4], by omega, hbody, hexit, rfl⟩)),
            by simp [r5, r4, r3, r2, r1, hr1, AuxTree.rootId], by simp [AuxTree.toList], hfind_id, ?_⟩
          simp only [AuxTree.depthOf_root, Expr.size]; omega
        | false =>
          have htot := subtree_sum_markCnt hsub (by simp) hnr
          have hL_fil : (L.toList.filter fun u => (st.nodes u).val.isMarked) = [] := by
            refine List.filter_eq_nil_iff.mpr fun u hu hmu => ?_
            exact (List.find?_eq_none.mp hL_none u hu) hmu
          have hR_fil_pos : 0 < (R.toList.filter fun u => (st.nodes u).val.isMarked).length := by
            simp only [AuxTree.toList, List.filter_append, List.filter_cons, List.filter_nil, hL_fil, hmk_id,
              List.nil_append, Bool.false_eq_true, ↓reduceIte] at htot
            omega
          have hR_ne : R ≠ .leaf := by
            intro h; subst h; simp [AuxTree.toList] at hR_fil_pos
          have hR_mk : 0 < (st.nodes R.rootId).sum.markCnt := by
            rw [subtree_sum_markCnt hsub.2.2.2.2.2.2.2.2 hR_ne hR_nr]; exact hR_fil_pos
          set r5 := Function.update r4 1 R.rootId
          have hev_mk : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 10)))).eval w ⟨mem, r4, lpos⟩ = some 0 := by
            simp [Expr.eval, r4, r3, r2, r1, BinOp.eval, hm_mk, hmk_id,
              (by omega : 0 < 2 ^ w), (by omega : 10 < 2 ^ w), (by omega : nb + 17 * id + 10 < 2 ^ w)]
          have hst1 : Runs w p ω (.assign 1 (.load (.bin .add (.reg 5) (.const 1))))
              ⟨mem, r4, lpos⟩ .normal ⟨mem, r5, lpos⟩ 5 :=
            runs_assign_iff.mpr ⟨R.rootId, by
              simp [Expr.eval, r4, r3, r2, r1, BinOp.eval, hm_r,
                (by omega : 1 < 2 ^ w), (by omega : nb + 17 * id + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          have hcond_mk := tour_runs_cond_false (s₁ := .assign 4 (.const 0)) hev_mk hst1
          have hcond7 := tour_runs_cond_false (e := .reg 7) (s₁ := .assign 1 (.reg 6))
            (by simp [Expr.eval, r4, hgoL0]) hcond_mk
          have hbody := tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hrunL hcond7)))
          obtain ⟨y, regs', lpos', c', hrun', hy_r1, hy_R, hy_find, hc'⟩ :=
            ihR id r5 lpos hsub.2.2.2.2.2.2.2.2 hnd_nd.2.2.1 hR_ne hR_cap hR_nr hR_mk
              (by simp [r5, r4, r3, r2, r1, hr0]) (by simp [r5]) (by simp [r5, r4, r3, r2, r1, hr4])
          have hy_ne_id : y ≠ id := fun h => hnd_nd.2.2.2.1 (h ▸ hy_R)
          have hy_nL : y ∉ L.toList := fun h => hnd_nd.2.2.2.2 y h hy_R
          have hdep : (AuxTree.node id L R).depthOf y = 1 + R.depthOf y := by
            rw [AuxTree.depthOf.eq_2]; simp [hy_ne_id, hy_nL, hy_R]; omega
          have hfind_all : (AuxTree.node id L R).toList.find? (fun u => (st.nodes u).val.isMarked) = some y := by
            rw [AuxTree.toList, List.append_assoc, List.find?_append, hL_none]
            simpa [hmk_id] using hy_find
          refine ⟨y, regs', lpos', _,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, ⟨mem, r5, lpos⟩, _, c',
              by simp [Expr.eval, hr4], by omega, hbody, hrun', rfl⟩)),
            hy_r1, by simp [AuxTree.toList, hy_R], hfind_all, ?_⟩
          rw [hdep]; simp only [Expr.size]; omega
  unfold tourDescMark0Body; rw [startState]
  set r0 := fun i => [nb, t.rootId, fuel, heap].getD i 0
  set r1 := Function.update r0 4 1
  have ha0 : Runs w p ω (.assign 4 (.const 1)) ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
  obtain ⟨y, regs', lpos', c_lp, hrun_lp, hy_r1, hy_t, hy_find, hc_lp⟩ :=
    hloop t 0 r1 pos ht_inv.sub ht_inv.nodup ht_ne ht_cap ht_nr hmk (by simp [r1, r0]) (by simp [r1, r0]) (by simp [r1])
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem, regs', lpos'⟩) (r := 1) (v := y) hy_r1
  exact ⟨y, ⟨mem, regs', lpos'⟩, _, tour_runs_seq_normal ha0 (tour_runs_seq_normal hrun_lp hret),
    rfl, hy_t, hy_find, by omega⟩

/-! ## Zero-scratch `join`, `findFirstMark`, and `listMark` run theorems -/

theorem heapOk0_of_frame {nb cap heap : ℕ} {w : ℕ} {mem M : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap 0 mem)
    (hfr : TreeFrame tourLayout nb cap heap mem M) :
    HeapOk tourLayout w nb cap heap 0 M :=
  ⟨hheap.rec_le, hheap.room, hfr.1, hheap.wide⟩

/-- Zero-scratch `tourJoinBody` using `tourWalk0Body`, `splayLoopBody`, and `attachLeft`. -/
theorem tourJoin0Body_runs {w nb cap heap fuel pos walk0 : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (hw0 : p.procs[walk0]? = some tourWalk0Body)
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t₁? t₂? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t₁? ++ optTrees t₂? ++ rest))
    (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem) :
    ∃ t'? s' o st' c,
      Runs w p ω (tourJoinBody walk0 C.splay.loop C.attachLeft)
        (startState [nb, optRoot t₁?, optRoot t₂?, fuel, heap] mem pos) o st' c ∧
      o.value = optRoot t'? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t₁? ++ optList t₂? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t₁? ++ optList t₂?, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t₁? ++ optTrees t₂? ++ rest) +
          TOUR_JOIN_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  unfold tourJoinBody; rw [startState]
  cases t₁? with
  | none =>
    set st0 : State := ⟨mem, fun i => [nb, optRoot none, optRoot t₂?, fuel, heap].getD i 0, pos⟩
    have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 1 := by
      simp [Expr.eval, st0, optRoot, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    have hret : Runs w p ω (.ret (.reg 2)) st0 (.returned (optRoot t₂?)) st0 2 :=
      runs_ret_reg (by simp [st0])
    refine ⟨t₂?, st, .returned (optRoot t₂?), st0, _,
      tour_runs_cond_true hc0 (by omega) hret, rfl, hnodes,
      TreeFrame.refl hheap.zero, by simpa [optTrees] using hf, hvals, by simp [optList],
      fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    simp only [optTrees, Option.toList, List.nil_append, Expr.size, TOUR_JOIN_AMORT]; omega
  | some t₁ =>
    have ht₁_mem : t₁ ∈ optTrees (some t₁) ++ optTrees t₂? ++ rest := by simp [optTrees]
    have ht₁_ne : t₁ ≠ .leaf := hf.nonEmpty t₁ ht₁_mem
    have hr₁_nz : t₁.rootId ≠ 0 := by
      cases t₁ with | leaf => exact absurd rfl ht₁_ne | node _ _ _ => exact (hf.treesInv _ ht₁_mem).sub.1
    cases t₂? with
    | none =>
      set st0 : State := ⟨mem, fun i => [nb, optRoot (some t₁), optRoot none, fuel, heap].getD i 0, pos⟩
      have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 0 := by
        simp [Expr.eval, st0, optRoot, hr₁_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hc1 : (Expr.bin .eq (.reg 2) (.const 0)).eval w st0 = some 1 := by
        simp [Expr.eval, st0, optRoot, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      have hret : Runs w p ω (.ret (.reg 1)) st0 (.returned t₁.rootId) st0 2 :=
        runs_ret_reg (by simp [st0, optRoot])
      refine ⟨some t₁, st, .returned t₁.rootId, st0, _,
        tour_runs_cond_false hc0 (tour_runs_cond_true hc1 (by omega) hret), rfl, hnodes,
        TreeFrame.refl hheap.zero, by simpa [optTrees] using hf, hvals, by simp [optList],
        fun _ _ => rfl, fun _ _ => rfl, ?_⟩
      simp only [optTrees, Option.toList, List.append_nil, List.cons_append, List.nil_append,
        Expr.size, TOUR_JOIN_AMORT]; omega
    | some t₂ =>
      have ht₂_mem : t₂ ∈ optTrees (some t₁) ++ optTrees (some t₂) ++ rest := by simp [optTrees]
      have ht₂_ne : t₂ ≠ .leaf := hf.nonEmpty t₂ ht₂_mem
      have hr₂_nz : t₂.rootId ≠ 0 := by
        cases t₂ with | leaf => exact absurd rfl ht₂_ne | node _ _ _ => exact (hf.treesInv _ ht₂_mem).sub.1
      have hcnt₂ : t₂.countNodes < fuel := lt_of_le_of_lt (hf.countNodes_le ht₂_mem) hfuel
      have hf' : TourForestInv cap st ([t₁] ++ t₂ :: rest) := by simpa [optTrees] using hf
      obtain ⟨m, st₁, c₁, hrun₁, hmem₁, hm_mem, hm_head, hc₁⟩ :=
        tourWalk0Body_runs (fuel := fuel) (pos := pos) ω hnodes (hf'.treesInv t₂ (by simp)) ht₂_ne
          (fun u hu => hf'.mem_inCap (t := t₂) (by simp) hu) hheap
      have hdep_m : t₂.depthOf m < fuel := lt_trans (auxTree_depthOf_lt_countNodes hm_mem) hcnt₂
      obtain ⟨t₂', o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, hne₂', hroot₂', hlist₂', hout₂, hcost₂⟩ :=
        tourSplayLoop_runs_amort (pos := st₁.pos) C.toTourSplayCoreProcs ω (hmem₁ ▸ hnodes) hf' hvals
          hm_mem hdep_m hfuelW (hmem₁ ▸ hheap)
      set s₁ := SplayState.splay tourPayload st fuel m
      cases ht₂c : t₂' with
      | leaf => exact absurd ht₂c hne₂'
      | node mid l₂ R₂ =>
        have hmid : mid = m := by simpa [ht₂c, AuxTree.rootId] using hroot₂'
        rcases hmid with rfl
        rw [ht₂c] at hinv₂ hlist₂' hcost₂
        have hl₂_leaf : l₂ = .leaf := by
          cases l₂ with
          | leaf => rfl
          | node lid lL lR =>
            exfalso
            have hnd' := (hinv₂.treesInv (AuxTree.node mid (AuxTree.node lid lL lR) R₂) (by simp)).nodup
            have hm_nl : mid ∉ (AuxTree.node lid lL lR).toList := (AuxTree.nodup_node_unfold hnd').2.1
            have hl_ne : (AuxTree.node lid lL lR).toList ≠ [] :=
              List.ne_nil_of_mem (AuxTree.rootId_mem (by simp))
            have hhd : (AuxTree.node mid (AuxTree.node lid lL lR) R₂).toList.head? =
                (AuxTree.node lid lL lR).toList.head? := by
              rw [AuxTree.toList, List.append_assoc, List.head?_append_of_ne_nil _ hl_ne]
            rw [hlist₂', hm_head] at hhd
            exact hm_nl (List.mem_of_head? hhd.symm)
        subst hl₂_leaf
        have hinv₂' : TourForestInv cap s₁ (t₁ :: AuxTree.node mid .leaf R₂ :: rest) := by simpa using hinv₂
        have hm_cap : mid ≤ cap := (hinv₂'.mem_inCap (t := AuxTree.node mid .leaf R₂) (by simp) (by simp [AuxTree.toList])).2
        have hr₁_cap : t₁.rootId ≤ cap := (hinv₂'.mem_inCap (t := t₁) (by simp) (AuxTree.rootId_mem ht₁_ne)).2
        obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hn₃, hfr₃⟩, hc₃⟩ := tourAttachLeftBody_runs (pos := st₂.pos)
          C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hm_cap hr₁_cap
          (heapOk0_of_frame hheap (hmem₁ ▸ hfr₂)) (tourAttachLeft_sumOk hinv₂' hvals₂)
        obtain ⟨hinv₃, hout₃, hval₃, hphi₃⟩ := tourAttachLeft_preserves hinv₂'
        obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf' hm_mem hdep_m
        have hval_all : ∀ u ≤ cap, ((tourAttachLeft s₁ mid t₁.rootId).nodes u).val = (st.nodes u).val := by
          intro u hu; rw [hval₃ u hu]; exact hval_sp u hu
        have hvals₃ : TourValsOk w cap (tourAttachLeft s₁ mid t₁.rootId) :=
          ⟨hvals.1, fun u hu => by rw [hval_all u hu]; exact hvals.2 u hu⟩
        set s0 : State := ⟨mem, fun i => [nb, t₁.rootId, t₂.rootId, fuel, heap].getD i 0, pos⟩
        set s1_st : State := { st₁ with regs := Function.update s0.regs 5 mid }
        set s2_st : State := { st₂ with regs := Function.update s1_st.regs 6 o₂.value }
        set s3_st : State := { st₃ with regs := Function.update s2_st.regs 6 o₃.value }
        have hc_step1 := runs_call_regs4 5 0 2 3 4 (st := s0) hw0
          (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
        have hc_step2 := runs_call_regs4 6 0 5 3 4 (st := s1_st) C.splay.loop_body
          (by simp [s1_st, s0]) (by simp [s1_st]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
        have hc_step3 := runs_call_regs4 6 0 5 1 4 (st := s2_st) C.attachLeft_body
          (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) hrun₃
        have hret4 := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s3_st) (r := 5) (v := mid)
          (by simp [s3_st, s2_st, s1_st])
        have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w s0 = some 0 := by
          simp [Expr.eval, s0, hr₁_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hc1 : (Expr.bin .eq (.reg 2) (.const 0)).eval w s0 = some 0 := by
          simp [Expr.eval, s0, hr₂_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hfull := tour_runs_cond_false (s₁ := .ret (.reg 2)) hc0
          (tour_runs_cond_false (s₁ := .ret (.reg 1)) hc1
            (tour_runs_seq_normal hc_step1 (tour_runs_seq_normal hc_step2 (tour_runs_seq_normal hc_step3 hret4))))
        refine ⟨some (AuxTree.node mid t₁ R₂), tourAttachLeft s₁ mid t₁.rootId, .returned mid, s3_st, _,
          hfull, rfl, hn₃, (hmem₁ ▸ hfr₂).trans hfr₃, by simpa [optTrees] using hinv₃, hvals₃,
          by simp [optList, AuxTree.toList, ← hlist₂'], hval_all, ?_, ?_⟩
        · intro u hu
          have hu1 : u ∉ t₁.toList := fun hm => hu (by simp [optList, hm])
          have hu2 : u ∉ t₂.toList := fun hm => hu (by simp [optList, hm])
          have hu3 : u ∉ (AuxTree.node mid t₁ R₂).toList := fun hm => by
            simp only [AuxTree.toList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with (h1 | rfl) | h2
            · exact hu1 h1
            · exact hu2 hm_mem
            · exact hu2 (by rw [← hlist₂']; simp [AuxTree.toList, h2])
          exact (hout₃ u hu3).trans (hout₂ u hu2)
        · have hphi3' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
          have hc1_le : c₁ ≤ 50 * (t₂.depthOf mid / 2) + 70 := by omega
          simp only [optTrees, Option.toList, List.cons_append, List.nil_append, Expr.size,
            TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT] at hcost₂ hphi3' hc₃ hc1_le ⊢
          omega

/-- Zero-scratch `tourFindFirstBody` for marked nodes using `tourDescMark0Body` and `splayLoopBody`. -/
theorem tourFindFirstMark0Body_runs {w nb cap heap fuel pos dp0 : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (hdp0 : p.procs[dp0]? = some tourDescMark0Body)
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t? ++ rest)) (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem) :
    ∃ y t'? s' o st' c,
      Runs w p ω (tourFindFirstBody dp0 C.markTests.sumTest C.splay.loop)
        (startState [nb, optRoot t?, fuel, heap] mem pos) o st' c ∧
      o.value = y ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t?, s'.nodes u = st.nodes u) ∧
      (match (optList t?).find? (fun u => (st.nodes u).val.isMarked) with
        | none => y = 0 ∧ t'? = t? ∧ s' = st
        | some y₀ => y = y₀ ∧ ∃ t' L R, t'? = some t' ∧ t' = AuxTree.node y L R ∧
            (∀ u ∈ L.toList, (st.nodes u).val.isMarked = false) ∧ (st.nodes y).val.isMarked = true) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t? ++ rest) + TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide; have hroom := hheap.room
  unfold tourFindFirstBody; rw [startState]
  cases t? with
  | none =>
    set st0 : State := ⟨mem, fun i => [nb, 0, fuel, heap].getD i 0, pos⟩
    have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 1 := by
      simp [Expr.eval, st0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    have hret : Runs w p ω (.ret (.const 0)) st0 (.returned 0) st0 2 := runs_ret_const (by omega)
    refine ⟨0, none, st, .returned 0, st0, _,
      tour_runs_cond_true hc0 (by omega) hret, rfl, hnodes,
      TreeFrame.refl hheap.zero, hf, hvals, rfl, fun _ _ => rfl, fun _ _ => rfl,
      by simp [optList], by simp only [Expr.size, TOUR_FIND_AMORT]; omega⟩
  | some t =>
    have ht_mem : t ∈ optTrees (some t) ++ rest := by simp [optTrees]
    have ht_ne : t ≠ .leaf := hf.nonEmpty t ht_mem
    have hr_nz : t.rootId ≠ 0 := by
      cases t with | leaf => exact absurd rfl ht_ne | node _ _ _ => exact (hf.treesInv _ ht_mem).sub.1
    have hr_cap : t.rootId ≤ cap := (hf.mem_inCap ht_mem (AuxTree.rootId_mem ht_ne)).2
    have hAr : nb + 17 * t.rootId + 17 ≤ heap := by
      simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hr_cap
    have hsum_pre : (sumTestContract tourLayout tourMarkRs w C.markTests.cost).pre [nb + 17 * t.rootId] mem :=
      ⟨nb + 17 * t.rootId, (st.nodes t.rootId).val, (st.nodes t.rootId).sum, rfl,
        by rw [tourLayout_stride]; omega, (hnodes t.rootId hr_cap).2.2.2.2.2.2.1,
        (hnodes t.rootId hr_cap).2.2.2.2.2.2.2.1⟩
    obtain ⟨b_st, hb_st, o_st, st_st, c_st, hrun_st, ⟨hmem_st, hval_st⟩, hc_st⟩ :=
      C.markTests.sum_ok [nb + 17 * t.rootId] mem pos ω (by simp; omega) hsum_pre
    have hval_st' : o_st.value = if tourMarkRs (st.nodes t.rootId).sum then 1 else 0 :=
      hval_st (st.nodes t.rootId).sum (hnodes t.rootId hr_cap).2.2.2.2.2.2.2.1
    set r0 := fun i => [nb, t.rootId, fuel, heap].getD i 0
    set r1 := Function.update r0 4 (nb + 17 * t.rootId)
    have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w ⟨mem, r0, pos⟩ = some 0 := by
      simp [Expr.eval, r0, hr_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hass : Runs w p ω (.assign 4 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))
        ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ 6 :=
      runs_assign_iff.mpr ⟨nb + 17 * t.rootId, by
        simp [Expr.eval, r0, BinOp.eval, (by omega : 17 < 2 ^ w),
          (by omega : 17 * t.rootId < 2 ^ w), (by omega : nb + 17 * t.rootId < 2 ^ w)], rfl, rfl, rfl⟩
    have hcall_st := tour_runs_call_of (r := 5) (args := [.reg 4]) (st := ⟨mem, r1, pos⟩) hb_st
      (by simp [evalArgs, Expr.eval, r1]) hrun_st
    cases hrs : tourMarkRs (st.nodes t.rootId).sum with
    | false =>
      have hv0 : o_st.value = 0 := by simp [hval_st', hrs]
      have hmk0 : (st.nodes t.rootId).sum.markCnt = 0 := by
        simp [tourMarkRs] at hrs; exact hrs
      have hfil0 := hf.sum_markCnt ht_mem
      rw [hmk0] at hfil0
      have hnil : (t.toList.filter fun u => (st.nodes u).val.isMarked) = [] :=
        List.eq_nil_of_length_eq_zero hfil0.symm
      have hfind_none : t.toList.find? (fun u => (st.nodes u).val.isMarked) = none :=
        List.find?_eq_none.mpr fun u hu hm => (List.filter_eq_nil_iff.mp hnil u hu) hm
      have hret0 := runs_ret_const (w := w) (p := p) (ω := ω) (v := 0)
        (st := ⟨st_st.mem, Function.update r1 5 o_st.value, st_st.pos⟩) (by omega)
      have hcond5 := tour_runs_cond_true (e := .bin .eq (.reg 5) (.const 0)) (v := 1)
        (s₁ := .ret (.const 0))
        (s₂ := (.call 6 dp0 [.reg 0, .reg 1, .reg 2, .reg 3] ;;
                .call 7 C.splay.loop [.reg 0, .reg 6, .reg 2, .reg 3] ;; .ret (.reg 6)))
        (by simp [Expr.eval, Function.update_self, hv0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)])
        (by omega) hret0
      refine ⟨0, some t, st, .returned 0, _, _,
        tour_runs_cond_false hc0 (tour_runs_seq_normal hass (tour_runs_seq_normal hcall_st hcond5)),
        rfl, hmem_st ▸ hnodes, by dsimp only; rw [hmem_st]; exact TreeFrame.refl hheap.zero, hf, hvals, rfl,
        fun _ _ => rfl, fun _ _ => rfl, by simp [optList, hfind_none], ?_⟩
      rw [C.markTests_cost, TOUR_TEST_COST] at hc_st
      simp only [sumTestContract, argsSize, Expr.size, TOUR_FIND_AMORT] at hc_st ⊢; omega
    | true =>
      have hv1 : o_st.value = 1 := by simp [hval_st', hrs]
      have hmk_pos : 0 < (st.nodes t.rootId).sum.markCnt := by simpa [tourMarkRs] using hrs
      have hf' : TourForestInv cap st ([] ++ t :: rest) := by simpa [optTrees] using hf
      obtain ⟨y, st₁, c₁, hrun₁, hmem₁, hy_t, hy_find, hc₁⟩ :=
        tourDescMark0Body_runs (fuel := fuel) (pos := st_st.pos) ω (hmem_st ▸ hnodes)
          (hf'.treesInv t (by simp)) ht_ne (fun u hu => hf'.mem_inCap (t := t) (by simp) hu)
          (fun u hu => hf'.noRev u (hf'.mem_inCap (t := t) (by simp) hu).2) hmk_pos (hmem_st ▸ hheap)
      have hdep_y : t.depthOf y < fuel :=
        lt_trans (auxTree_depthOf_lt_countNodes hy_t) (lt_of_le_of_lt (hf'.countNodes_le (by simp)) hfuel)
      obtain ⟨t', o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, hne', hroot', hlist', hout', hcost₂⟩ :=
        tourSplayLoop_runs_amort (pos := st₁.pos) C.toTourSplayCoreProcs ω (hmem₁ ▸ hmem_st ▸ hnodes)
          hf' hvals hy_t hdep_y hfuelW (hmem₁ ▸ hmem_st ▸ hheap)
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf' hy_t hdep_y
      set s_st : State := { st_st with regs := Function.update r1 5 o_st.value }
      set s1_st : State := { st₁ with regs := Function.update s_st.regs 6 y }
      set s2_st : State := { st₂ with regs := Function.update s1_st.regs 7 o₂.value }
      have hcall1 := runs_call_regs4 6 0 1 2 3 (st := s_st) hdp0
        (by simp [s_st, r1, r0]) (by simp [s_st, r1, r0]) (by simp [s_st, r1, r0]) (by simp [s_st, r1, r0]) hrun₁
      have hcall2 := runs_call_regs4 7 0 6 2 3 (st := s1_st) C.splay.loop_body
        (by simp [s1_st, s_st, r1, r0]) (by simp [s1_st]) (by simp [s1_st, s_st, r1, r0]) (by simp [s1_st, s_st, r1, r0]) hrun₂
      have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s2_st) (r := 6) (v := y)
        (by simp [s2_st, s1_st])
      have hcond5 := tour_runs_cond_false (e := .bin .eq (.reg 5) (.const 0)) (st := s_st)
        (s₁ := .ret (.const 0))
        (by simp [Expr.eval, s_st, hv1, BinOp.eval, (by omega : 0 < 2 ^ w)])
        (tour_runs_seq_normal hcall1 (tour_runs_seq_normal hcall2 hret))
      refine ⟨y, some t', SplayState.splay tourPayload st fuel y, .returned y, s2_st, _,
        tour_runs_cond_false hc0 (tour_runs_seq_normal hass (tour_runs_seq_normal hcall_st hcond5)),
        rfl, hn₂, by dsimp only [s2_st]; rw [← hmem_st, ← hmem₁]; exact hfr₂, by simpa [optTrees] using hinv₂, hvals₂,
        by simpa [optList] using hlist', hval_sp, by simpa [optList] using hout', ?_, ?_⟩
      · dsimp only [optList, Option.elim]
        rw [hy_find]
        cases ht'c : t' with
        | leaf => exact absurd ht'c hne'
        | node yid L R =>
          have hyid : yid = y := by simpa [ht'c, AuxTree.rootId] using hroot'
          subst hyid
          refine ⟨rfl, AuxTree.node yid L R, L, R, rfl, rfl, ?_, ?_⟩
          · intro u hu
            have hfind' : (L.toList ++ yid :: R.toList).find? (fun z => (st.nodes z).val.isMarked) = some yid := by
              have hyf := hy_find; rw [← hlist', ht'c] at hyf; simpa [AuxTree.toList, List.append_assoc] using hyf
            cases hL : L.toList.find? (fun z => (st.nodes z).val.isMarked) with
            | none =>
              by_contra hnt
              have htr : (st.nodes u).val.isMarked = true := by cases (st.nodes u).val.isMarked <;> simp_all
              exact (List.find?_eq_none.mp hL u hu) htr
            | some w0 =>
              rw [List.find?_append, hL] at hfind'
              have hw0_eq : w0 = yid := by simpa using hfind'
              subst hw0_eq
              have hw0_L : w0 ∈ L.toList := List.mem_of_find?_eq_some hL
              have hnd' := (hinv₂.treesInv (AuxTree.node w0 L R) (by simp [ht'c])).nodup
              exact absurd hw0_L (AuxTree.nodup_node_unfold hnd').2.1
          · exact List.find?_some (p := fun u => (st.nodes u).val.isMarked) hy_find
      · rw [C.markTests_cost, TOUR_TEST_COST] at hc_st
        have hc1_le : c₁ ≤ 130 * (t.depthOf y / 2) + 150 := by omega
        simp only [optTrees, Option.toList, List.nil_append, List.cons_append, sumTestContract, argsSize, Expr.size,
          TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₂ hc_st hc1_le ⊢
        omega


end MinCostFlow.SparseCore.Program
