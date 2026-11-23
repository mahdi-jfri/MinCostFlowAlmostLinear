module

public import MinCostFlow.LinkCut.ForestExposeOps
import MinCostFlow.LinkCut.ForestReversals
import MinCostFlow.LinkCut.ForestCutLink

namespace MinCostFlow.LinkCut

@[expose] public section

variable {α : Type*} {σ : Type*} {τ : Type*}

/-! ### List, permutation, and reachability helper lemmas for `expose` -/

private theorem filter_length_lt_of_imp {β : Type*} [BEq β] [LawfulBEq β]
    {xs : List β} {q r : β → Bool} (_hnd : xs.Nodup)
    (himp : ∀ w ∈ xs, q w = true → r w = true)
    {p : β} (hp : p ∈ xs) (hrp : r p = true) (hqp : q p = false) :
    (xs.filter q).length + 1 ≤ (xs.filter r).length := by
  have hperm := List.perm_cons_erase hp
  rw [(hperm.filter q).length_eq, (hperm.filter r).length_eq]
  rw [List.filter_cons, List.filter_cons, hqp, hrp]
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
  have himp_er : ∀ w ∈ xs.erase p, q w = true → r w = true := fun w hw =>
    himp w (List.mem_of_mem_erase hw)
  have hle := filter_length_le_of_imp q r (xs.erase p) himp_er
  omega

private theorem active_perm_detachRight {ts : List AuxTree} {x : ℕ} {L R : AuxTree}
    (ht : AuxTree.node x L R ∈ ts) :
    let ts' := if R = AuxTree.leaf then ts else AuxTree.node x L AuxTree.leaf :: R :: ts.erase (AuxTree.node x L R)
    (ts'.flatMap AuxTree.toList).Perm (ts.flatMap AuxTree.toList) := by
  intro ts'
  by_cases hR : R = AuxTree.leaf
  · dsimp only [ts']; simp only [hR, ↓reduceIte]; exact List.Perm.rfl
  · dsimp only [ts']; simp only [eq_false hR, ↓reduceIte]
    have hperm := (List.perm_cons_erase ht).flatMap_right AuxTree.toList
    refine List.Perm.trans ?_ hperm.symm
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
    have hcat : (AuxTree.node x L AuxTree.leaf).toList ++
        (R.toList ++ (ts.erase (AuxTree.node x L R)).flatMap AuxTree.toList) =
        (AuxTree.node x L R).toList ++ (ts.erase (AuxTree.node x L R)).flatMap AuxTree.toList := by
      simp only [AuxTree.toList, List.append_nil, List.append_assoc]
    rw [hcat]

private theorem active_perm_attachRight {ts : List AuxTree} {u : ℕ} {Lu tx : AuxTree}
    (hu : AuxTree.node u Lu AuxTree.leaf ∈ ts) (htx : tx ∈ ts)
    (hne : AuxTree.node u Lu AuxTree.leaf ≠ tx) :
    let ts' := AuxTree.node u Lu tx :: (ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx
    (ts'.flatMap AuxTree.toList).Perm (ts.flatMap AuxTree.toList) := by
  intro ts'
  have htx_er : tx ∈ ts.erase (AuxTree.node u Lu AuxTree.leaf) :=
    (List.mem_erase_of_ne hne.symm).mpr htx
  have hperm := ((List.perm_cons_erase hu).trans (List.Perm.cons _ (List.perm_cons_erase htx_er))).flatMap_right
    AuxTree.toList
  refine List.Perm.trans ?_ hperm.symm
  dsimp only [ts']
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
  have hcat : (AuxTree.node u Lu tx).toList ++
      ((ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap AuxTree.toList =
      (AuxTree.node u Lu AuxTree.leaf).toList ++
        (tx.toList ++ ((ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap AuxTree.toList) := by
    simp only [AuxTree.toList, List.append_nil, List.append_assoc]
  rw [hcat]

private theorem repSize_congr_perm {active₁ active₂ : List ℕ} {par₁ par₂ : ℕ → ℕ}
    (hp : active₁.Perm active₂) (hpar : ∀ z, par₁ z = par₂ z) (u : ℕ) :
    repSize active₁ par₁ u = repSize active₂ par₂ u := by
  dsimp only [repSize]
  have hfilt : active₁.filter (fun w => reaches par₁ active₁.length u w) =
      active₁.filter (fun w => reaches par₂ active₂.length u w) :=
    List.filter_congr (fun w _ => by rw [hp.length_eq, reaches_congr hpar])
  rw [hfilt, (hp.filter _).length_eq]

private theorem vSize_congr_par {P : LctPayload α σ τ} {s : SplayState α σ τ} {active : List ℕ}
    {par₁ par₂ : ℕ → ℕ} {ts : List AuxTree} (hpar : ∀ z, par₁ z = par₂ z) :
    vSize P s active par₁ ts = vSize P s active par₂ ts := by
  funext u; simp only [vSize]; congr 1
  exact List.map_congr_left (fun c _ => repSize_congr_perm List.Perm.rfl hpar _)

private theorem tnode_par_closed_except_head {P : LctPayload α σ τ}
    {st : LctState α σ τ} {ts : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    {t : AuxTree} (W : LctInvWith P st ts freeList depth)
    (ht : t ∈ ts) (hpp : (st.splay.nodes t.rootId).ppar = 0) :
    let par := inducedSubPar P st.splay ts
    ∀ w ∈ t.toList, par w ≠ 0 → par w ∈ t.toList := by
  intro par w hw hpw
  have hmem := inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht hw
  have hpar_mem := chainPred_mem_or_prev (prev := (st.splay.nodes t.rootId).ppar)
    (xs := treeIds P st.splay t) ((mem_treeIds_iff P st.splay t w).mpr hw)
  rw [← hmem, hpp] at hpar_mem
  rcases hpar_mem with h | h
  · exact False.elim (hpw h)
  · exact (mem_treeIds_iff P st.splay t (par w)).mp h

private theorem tnode_reaches_iff {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {ts : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st ts freeList depth)
    {v : ℕ} {Lv : AuxTree} (ht : AuxTree.node v Lv AuxTree.leaf ∈ ts)
    (hpp : (st.splay.nodes v).ppar = 0)
    (hrev : (st.splay.nodes v).rev = false) (htag : (st.splay.nodes v).tag = P.idTag) :
    let active := ts.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay ts
    ∀ z, z ∈ (AuxTree.node v Lv AuxTree.leaf).toList ↔ reaches par active.length z v = true := by
  intro active par z
  let t := AuxTree.node v Lv AuxTree.leaf
  have hlast : listLast0 (treeIds P st.splay t) = v := listLast0_eq_root_of_right_leaf hL hrev htag
  have hv_mem : v ∈ t.toList := by simp [t, AuxTree.toList]
  constructor
  · intro hz
    have hids_nd : (treeIds P st.splay t).Nodup := treeIds_nodup (W.treesInv t ht)
    have hids_0 : 0 ∉ treeIds P st.splay t := fun h0 => by
      have hm := W.activeValid 0 (List.mem_flatMap.mpr ⟨t, ht, (mem_treeIds_iff P st.splay t 0).mp h0⟩)
      simp [isNode] at hm
    have hz_ids : z ∈ treeIds P st.splay t := (mem_treeIds_iff P st.splay t z).mpr hz
    have hrc := reaches_chainPred_last (treeIds P st.splay t) (st.splay.nodes t.rootId).ppar z hids_nd hids_0 hz_ids
    rw [hlast] at hrc
    have hag : ∀ y ∈ treeIds P st.splay t,
        chainPred (st.splay.nodes t.rootId).ppar (treeIds P st.splay t) y = par y := fun y hy =>
      (inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht
        ((mem_treeIds_iff P st.splay t y).mp hy)).symm
    have hout : ∀ y ∉ treeIds P st.splay t,
        chainPred (st.splay.nodes t.rootId).ppar (treeIds P st.splay t) y = 0 := fun y hy =>
      chainPred_eq_zero_of_not_mem hy
    have hrc' := reaches_agree_of_mem hag hout (treeIds P st.splay t).length z v hrc hz_ids
    have hlen : (treeIds P st.splay t).length ≤ active.length := by
      have heq_len : (treeIds P st.splay t).length = t.toList.length := by
        simp [treeIds, evalPairs_length]
      rw [heq_len]
      exact tree_length_le_active ht
    exact reaches_mono hlen hrc'
  · intro hr
    have hclosed := tnode_par_closed_except_head W ht hpp
    suffices ∀ k y, reaches par k z y = true → y ∈ t.toList → z ∈ t.toList by
      exact this active.length v hr hv_mem
    intro k
    induction k with
    | zero =>
        intro y hry hy
        simp only [reaches, beq_iff_eq] at hry
        rwa [← hry]
    | succ k ih =>
        intro y hry hy
        simp only [reaches] at hry
        by_cases hyz : y = z
        · rwa [← hyz]
        · simp only [beq_false_of_ne hyz, Bool.false_eq_true, ↓reduceIte] at hry
          by_cases hpy : par y = 0
          · simp [hpy] at hry
          · simp only [beq_false_of_ne hpy, Bool.false_eq_true, ↓reduceIte] at hry
            exact ih (par y) hry (hclosed y hy hpy)

/-! ### Phase 1 of `expose`: initial `splay v` and `detachRight v` -/

theorem lctExposeInit_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) :
    let d0 := splayDepth st.splay (2 * st.n + 1) v
    let s0 := SplayState.splay P st.splay (2 * st.n + 1) v
    let s1 := SplayState.detachRight P s0 v
    let st1 : LctState α σ τ := { n := st.n, splay := s1, freeHead := st.freeHead }
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∃ trees1 L1,
      let t1 := AuxTree.node v L1 AuxTree.leaf
      let active1 := trees1.flatMap AuxTree.toList
      let par1 := inducedSubPar P s1 trees1
      let v1 := vSize P s1 active1 par1 trees1
      t1 ∈ trees1 ∧
        v ∈ t1.toList ∧
        LctInvWith P st1 trees1 freeList depth ∧
        active1.Perm active ∧
        (∀ z, par1 z = par z) ∧
        (forestPairs P s1 trees1).Perm (forestPairs P st.splay trees) ∧
        listLast0 (treeIds P s1 t1) = v ∧
        (s1.nodes v).rev = false ∧
        (s1.nodes v).tag = P.idTag ∧
        1 ≤ t1.treeSize v1 ∧
        t1.treeSize v1 ≤ 2 * st.n ∧
        t1.rank v1 ≤ Nat.log 2 (2 * st.n + 1) ∧
        d0 / 2 + sumTreePhi P st1 ≤ sumTreePhi P st + 3 * t1.rank v1 ∧
        heavyCount P st1 ≤ heavyCount P st + 1 ∧
        ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
          c ∈ trees1 ∧ ∀ w ∈ c.toList, s1.nodes w = st.splay.nodes w := by
  intro d0 s0 s1 st1 active par
  rcases lctSplayTree_spec hL W htv hv with
    ⟨t0', ht0'_ne, ht0'_rt, ht0'_perm, hpp0, hrev0, htag0, hW0, hH0, hpairs0, hpar0, hout0, hev0, htsz0, hrank0, hpot0⟩
  cases ht0'_eq : t0' with
  | leaf => exact absurd ht0'_eq ht0'_ne
  | node vr L0 R0 =>
      have hvr : vr = v := by simpa [ht0'_eq, AuxTree.rootId] using ht0'_rt
      have ht0'_v : t0' = AuxTree.node v L0 R0 := by simpa [hvr] using ht0'_eq
      let trees0 := AuxTree.node v L0 R0 :: trees.erase tv
      have ht0'_mem : AuxTree.node v L0 R0 ∈ trees0 := by simp [trees0]
      have hW0' : LctInvWith P { n := st.n, splay := s0, freeHead := st.freeHead } trees0 freeList depth := by
        simpa [trees0, ht0'_v] using hW0
      have hdet := detachRight_spec hL hW0' ht0'_mem hrev0 htag0
      have hdet_p := SplayState.detachRight_preserves hL (hW0'.treesInv _ ht0'_mem) hrev0 htag0
      have hpairs_det := forestPairs_perm_detachRight hL ht0'_mem (hW0'.treesInv _ ht0'_mem)
        hrev0 htag0 hW0'.activeNodup
      rcases hdet with ⟨hW1, hPhi1, _, _, hH1_le, hpar1_eq⟩
      rcases hdet_p with ⟨_, hrev1, htag1, _, _, hev_L1, _, hout1⟩
      let t1 := AuxTree.node v L0 AuxTree.leaf
      let trees1 := if R0 = AuxTree.leaf then trees0 else t1 :: R0 :: trees0.erase (AuxTree.node v L0 R0)
      refine ⟨trees1, L0, ?_⟩
      have ht1_mem : t1 ∈ trees1 := by
        by_cases hR : R0 = AuxTree.leaf
        · subst hR; simp [trees1, t1, trees0]
        · simp [trees1, hR]
      have hv_mem1 : v ∈ t1.toList := by simp [t1, AuxTree.toList]
      have hact_perm0 : (trees0.flatMap AuxTree.toList).Perm active := by
        simpa [trees0, ht0'_v] using flatMap_perm_of_replace htv ht0'_perm
      have hact_perm1 : (trees1.flatMap AuxTree.toList).Perm active :=
        (active_perm_detachRight ht0'_mem).trans hact_perm0
      have hpar_all1 : ∀ z, inducedSubPar P s1 trees1 z = par z := fun z =>
        (hpar1_eq z).trans (by simpa [trees0, ht0'_v] using hpar0 z)
      have hpairs1 : (forestPairs P s1 trees1).Perm (forestPairs P st.splay trees) :=
        hpairs_det.trans (by simpa [trees0, ht0'_v] using hpairs0)
      have hlast1 : listLast0 (treeIds P s1 t1) = v := listLast0_eq_root_of_right_leaf hL hrev1 htag1
      let active1 := trees1.flatMap AuxTree.toList
      let par1 := inducedSubPar P s1 trees1
      let v1 := vSize P s1 active1 par1 trees1
      let active0 := trees0.flatMap AuxTree.toList
      let par0 := inducedSubPar P s0 trees0
      let v0 := vSize P s0 active0 par0 trees0
      let v_old := vSize P st.splay active par trees
      have hhead_eq : listHead0 (treeIds P s1 t1) = listHead0 (treeIds P s0 (AuxTree.node v L0 R0)) := by
        have hids1 : treeIds P s1 t1 = treeIds P s0 L0 ++ [v] := by
          dsimp only [treeIds, t1]
          rw [hev_L1]
          simp [List.map_append]
        have hids0 : treeIds P s0 (AuxTree.node v L0 R0) = treeIds P s0 L0 ++ [v] ++ treeIds P s0 R0 :=
          treeIds_of_rev_false hL hrev0 htag0
        have hne_l : treeIds P s0 L0 ++ [v] ≠ [] := by simp
        rw [hids1, hids0, listHead0_append_of_ne_nil hne_l]
      have hsz_t1_v0 : t1.treeSize v1 = (AuxTree.node v L0 R0).treeSize v0 := by
        rw [treeSize_vSize_eq_repSize hW1 ht1_mem, treeSize_vSize_eq_repSize hW0' ht0'_mem, hhead_eq]
        exact repSize_congr_perm (active_perm_detachRight ht0'_mem) hpar1_eq _
      have hsz_t0_old : (AuxTree.node v L0 R0).treeSize v0 = (AuxTree.node v L0 R0).treeSize v_old := by
        have htsz0' : (AuxTree.node v L0 R0).treeSize v_old = tv.treeSize v_old := by
          simpa [ht0'_v] using htsz0
        rw [treeSize_vSize_eq_repSize hW0' ht0'_mem, htsz0', treeSize_vSize_eq_repSize W htv]
        have hids_eq : treeIds P s0 (AuxTree.node v L0 R0) = treeIds P st.splay tv :=
          treeIds_eq_of_evalPairs (by simpa [ht0'_v] using hev0)
        rw [hids_eq]
        exact repSize_congr_perm hact_perm0 (fun z => by simpa [trees0, ht0'_v] using hpar0 z) _
      have hrank_eq : t1.rank v1 = (AuxTree.node v L0 R0).rank v_old := by
        simp only [AuxTree.rank, hsz_t1_v0, hsz_t0_old]
      have hsz_ge1 : 1 ≤ t1.treeSize v1 := by
        rw [treeSize_vSize_eq_repSize hW1 ht1_mem]
        exact repSize_pos_of_mem (List.mem_flatMap.mpr ⟨t1, ht1_mem, listHead0_mem_of_ne_nil (hW1.treesNonEmpty t1 ht1_mem)⟩)
      have hact1_v : ∀ x ∈ active1, isNode st.n x := hW1.activeValid
      have hact1_le : active1.length ≤ 2 * st.n :=
        active_length_le_two_mul hW1.activeNodup hact1_v
      have hsz_le2n : t1.treeSize v1 ≤ 2 * st.n := by
        rw [treeSize_vSize_eq_repSize hW1 ht1_mem]
        exact (repSize_le_active _).trans hact1_le
      have hrank_le : t1.rank v1 ≤ Nat.log 2 (2 * st.n + 1) :=
        Nat.log_mono_right (by omega)
      have hpot1 : d0 / 2 + sumTreePhi P st1 ≤ sumTreePhi P st + 3 * t1.rank v1 := by
        have h1 : d0 / 2 + sumTreePhi P { n := st.n, splay := s0, freeHead := st.freeHead } +
            3 * (tv.findSubtree v).rank v_old ≤
            sumTreePhi P st + 3 * (AuxTree.node v L0 R0).rank v_old := by
          simpa [ht0'_v] using hpot0
        have hPhi1' : sumTreePhi P st1 = sumTreePhi P { n := st.n, splay := s0, freeHead := st.freeHead } := hPhi1
        rw [hrank_eq]
        omega
      have hH_le : heavyCount P st1 ≤ heavyCount P st + 1 := by
        have hH1' : heavyCount P st1 ≤ heavyCount P { n := st.n, splay := s0, freeHead := st.freeHead } + 1 := hH1_le
        have hH0' : heavyCount P { n := st.n, splay := s0, freeHead := st.freeHead } = heavyCount P st := hH0
        omega
      have huntouched : ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
          c ∈ trees1 ∧ ∀ w ∈ c.toList, s1.nodes w = st.splay.nodes w := by
        intro c hc hno
        have hv_nc : v ∉ c.toList := fun hm => by
          have := hno v hm
          simp [reaches_self] at this
        have hctv : c ≠ tv := fun h => hv_nc (h ▸ hv)
        have hc_er : c ∈ trees.erase tv := (List.mem_erase_of_ne hctv).mpr hc
        have hc_t0 : c ∈ trees0 := List.mem_cons_of_mem _ hc_er
        have hct0 : c ≠ AuxTree.node v L0 R0 := fun h => hv_nc (h ▸ (by simp [AuxTree.toList]))
        have hc_t1 : c ∈ trees1 := by
          by_cases hR : R0 = AuxTree.leaf
          · simp [trees1, hR, hc_t0]
          · simp [trees1, hR, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hct0).mpr hc_t0)]
        have hag : ∀ w ∈ c.toList, s1.nodes w = st.splay.nodes w := by
          intro w hw
          have hw_ntv : w ∉ tv.toList := fun hm =>
            hctv (flatMap_mem_unique W.activeNodup hc htv hw hm)
          have hw_nt0 : w ∉ (AuxTree.node v L0 R0).toList := fun hm =>
            hw_ntv (ht0'_perm.mem_iff.mp (by simpa [ht0'_v] using hm))
          rw [hout1 w hw_nt0, hout0 w hw_ntv]
        exact ⟨hc_t1, hag⟩
      exact ⟨ht1_mem, hv_mem1, hW1, hact_perm1, hpar_all1, hpairs1, hlast1, hrev1, htag1,
        hsz_ge1, hsz_le2n, hrank_le, hpot1, hH_le, huntouched⟩

/-! ### Phase 2 of `expose`: single bottom-up splice iteration -/

theorem lctExposeStep_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {t_prev : AuxTree} {last v : ℕ}
    (ht_prev : t_prev ∈ trees) (ht_rt : t_prev.rootId = last) (hv_prev : v ∈ t_prev.toList)
    (hlast : listLast0 (treeIds P st.splay t_prev) = v)
    (hp_nz : (st.splay.nodes last).ppar ≠ 0)
    (par0 : ℕ → ℕ) (hpar_eq : ∀ z, inducedSubPar P st.splay trees z = par0 z)
    (active0 : List ℕ) (hact_perm0 : (trees.flatMap AuxTree.toList).Perm active0) :
    let r := lctExposeStep P st last
    let st' := r.1
    let p := r.2.1
    let h1 := r.2.2
    let active := trees.flatMap AuxTree.toList
    let v_old := vSize P st.splay active par0 trees
    ∃ trees' L_next,
      let t_next := AuxTree.node p L_next t_prev
      let active' := trees'.flatMap AuxTree.toList
      let v_new := vSize P st'.splay active' par0 trees'
      t_next ∈ trees' ∧
        v ∈ t_next.toList ∧
        LctInvWith P st' trees' freeList depth ∧
        active'.Perm active0 ∧
        (∀ z, inducedSubPar P st'.splay trees' z = par0 z) ∧
        (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) ∧
        listLast0 (treeIds P st'.splay t_next) = v ∧
        t_prev.treeSize v_old + 1 ≤ t_next.treeSize v_new ∧
        t_next.treeSize v_new ≤ 2 * st.n ∧
        t_next.rank v_new ≤ Nat.log 2 (2 * st.n + 1) ∧
        h1 + sumTreePhi P st' + 3 * t_prev.rank v_old ≤ sumTreePhi P st + 3 * t_next.rank v_new ∧
        1 + heavyCount P st' + 2 * (Nat.log 2 (2 * st.n + 1) - t_next.rank v_new) ≤
          heavyCount P st + 2 * (Nat.log 2 (2 * st.n + 1) - t_prev.rank v_old) ∧
        ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par0 active0.length w v = false) →
          c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
  intro r st' p h1 active v_old
  have hp_def : p = (st.splay.nodes last).ppar := rfl
  have hp_act : p ∈ active := by
    dsimp only [active]
    rw [hp_def, ← ht_rt]
    exact W.pparActive t_prev ht_prev (by rw [ht_rt, ← hp_def]; exact hp_nz)
  rcases List.mem_flatMap.mp hp_act with ⟨tp, htp, hp_tp⟩
  let h_prev := listHead0 (treeIds P st.splay t_prev)
  have hh_mem : h_prev ∈ t_prev.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty t_prev ht_prev)
  have hh_act : h_prev ∈ active := List.mem_flatMap.mpr ⟨t_prev, ht_prev, hh_mem⟩
  have hpar_h : par0 h_prev = p := by
    rw [← hpar_eq]
    rw [inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht_prev hh_mem]
    have hne : treeIds P st.splay t_prev ≠ [] := treeIds_ne_nil (W.treesNonEmpty t_prev ht_prev)
    cases hids : treeIds P st.splay t_prev with
    | nil => exact absurd hids hne
    | cons a rest => simp [h_prev, listHead0, hids, chainPred, ht_rt, hp_def]
  have htp_ne : tp ≠ t_prev := by
    intro heq
    have hp_prev : p ∈ t_prev.toList := heq ▸ hp_tp
    have hrc := tree_reaches_head W ht_prev hp_prev
    have hle := depth_le_of_reaches (fun _ hx hp => W.subPar_mem_active hx hp) W.acyclic
      active.length h_prev p hrc hp_act
    have hpar_h' : inducedSubPar P st.splay trees h_prev = p := by rwa [hpar_eq]
    have hlt := W.acyclic h_prev hh_act (by rw [hpar_h']; exact hp_nz)
    rw [hpar_h'] at hlt
    omega
  -- Splay `p` in `tp`
  rcases lctSplayTree_spec hL W htp hp_tp with
    ⟨tp', htp'_ne, htp'_rt, htp'_perm, hpp_tp', hrev_p, htag_p, hW1, hH1, hpairs1, hpar1, hout1, hev1, htsz1, hrank1, hpot1⟩
  cases htp'_eq : tp' with
  | leaf => exact absurd htp'_eq htp'_ne
  | node pr L R =>
      have hpr : pr = p := by simpa [htp'_eq, AuxTree.rootId] using htp'_rt
      have htp'_p : tp' = AuxTree.node p L R := by simpa [hpr] using htp'_eq
      let trees1 := AuxTree.node p L R :: trees.erase tp
      have htp'_mem : AuxTree.node p L R ∈ trees1 := List.mem_cons_self
      have ht_prev_er : t_prev ∈ trees.erase tp := (List.mem_erase_of_ne htp_ne.symm).mpr ht_prev
      have ht_prev_1 : t_prev ∈ trees1 := List.mem_cons_of_mem _ ht_prev_er
      have htp'_ne_prev : AuxTree.node p L R ≠ t_prev := fun h => by
        have hp_mem : p ∈ t_prev.toList := h ▸ (by simp [AuxTree.toList])
        exact htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hp_tp hp_mem)
      have hW1' : LctInvWith P { n := st.n, splay := SplayState.splay P st.splay (2 * st.n + 1) p, freeHead := st.freeHead }
          trees1 freeList depth := by simpa [trees1, htp'_p] using hW1
      have hdisj_tp_prev : ∀ w ∈ t_prev.toList, w ∉ tp.toList := fun w hw hm =>
        htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hm hw)
      have hag_prev1 : ∀ w ∈ t_prev.toList,
          (SplayState.splay P st.splay (2 * st.n + 1) p).nodes w = st.splay.nodes w :=
        fun w hw => hout1 w (hdisj_tp_prev w hw)
      have hpp_prev1 : ((SplayState.splay P st.splay (2 * st.n + 1) p).nodes t_prev.rootId).ppar = p := by
        rw [hag_prev1 t_prev.rootId (AuxTree.rootId_mem (W.treesNonEmpty t_prev ht_prev)), ht_rt]; exact hp_def.symm
      -- `exposeStep_heavy_light` applies `detachRight p; attachRight p last`
      have hexp := exposeStep_heavy_light hL hW1' htp'_mem ht_prev_1 htp'_ne_prev hrev_p htag_p hpp_prev1
      let s1 := SplayState.splay P st.splay (2 * st.n + 1) p
      let s2 := SplayState.detachRight P s1 p
      have hst_eq : st' = LctState.mk st.n (SplayState.attachRight P s2 p t_prev.rootId) st.freeHead := by
        dsimp only [st', r, lctExposeStep, s1, s2]
        have hp_eq : (st.splay.nodes last).ppar = p := hp_def.symm
        rw [hp_eq, ht_rt]
      have hs3_eq : SplayState.attachRight P s2 p t_prev.rootId = st'.splay := by
        rw [hst_eq]
      let trees_base := if R = AuxTree.leaf then trees1 else AuxTree.node p L AuxTree.leaf :: R :: trees1.erase (AuxTree.node p L R)
      let t_next := AuxTree.node p L t_prev
      let trees' := t_next :: (trees_base.erase (AuxTree.node p L AuxTree.leaf)).erase t_prev
      rcases hexp with ⟨hW2', hPhi2', hHeavy_t, hHeavy_f, hpar2'⟩
      have hW2 : LctInvWith P st' trees' freeList depth := by
        rw [hst_eq]
        simpa [trees_base, t_next, trees', s1, s2] using hW2'
      refine ⟨trees', L, ?_⟩
      have ht_next_mem : t_next ∈ trees' := List.mem_cons_self
      have hv_next : v ∈ t_next.toList := by simp [t_next, AuxTree.toList, hv_prev]
      -- Permutations of active and `forestPairs`, and equality of `par`
      have hact_perm1 : (trees1.flatMap AuxTree.toList).Perm active := by
        simpa [trees1, htp'_p] using flatMap_perm_of_replace htp htp'_perm
      have hdet_inv : SplayState.TreeInv P s2 (AuxTree.node p L AuxTree.leaf) :=
        (SplayState.detachRight_preserves hL (hW1'.treesInv _ htp'_mem) hrev_p htag_p).1
      have hdet_rev : (s2.nodes p).rev = false :=
        (SplayState.detachRight_preserves hL (hW1'.treesInv _ htp'_mem) hrev_p htag_p).2.1
      have hdet_tag : (s2.nodes p).tag = P.idTag :=
        (SplayState.detachRight_preserves hL (hW1'.treesInv _ htp'_mem) hrev_p htag_p).2.2.1
      have hev_L2 : SplayState.evalPairs P s2 (AuxTree.node p L AuxTree.leaf) false P.idTag =
          SplayState.evalPairs P s1 L false P.idTag ++ [(p, (s1.nodes p).val)] :=
        (SplayState.detachRight_preserves hL (hW1'.treesInv _ htp'_mem) hrev_p htag_p).2.2.2.2.2.1
      have hout_det : ∀ u ∉ (AuxTree.node p L R).toList, s2.nodes u = s1.nodes u :=
        (SplayState.detachRight_preserves hL (hW1'.treesInv _ htp'_mem) hrev_p htag_p).2.2.2.2.2.2.2
      have hp_mem_det : AuxTree.node p L AuxTree.leaf ∈ trees_base := by
        by_cases hR : R = AuxTree.leaf
        · subst hR; simp [trees_base, htp'_mem]
        · simp [trees_base, hR]
      have ht_prev_base : t_prev ∈ trees_base := by
        by_cases hR : R = AuxTree.leaf
        · simp [trees_base, hR, ht_prev_1]
        · simp [trees_base, hR, List.mem_cons_of_mem _ ((List.mem_erase_of_ne htp'_ne_prev.symm).mpr ht_prev_1)]
      have hdet_ne_prev : AuxTree.node p L AuxTree.leaf ≠ t_prev := fun h => by
        have hm : p ∈ t_prev.toList := h ▸ (by simp [AuxTree.toList])
        exact htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hp_tp hm)
      have hdet_spec := detachRight_spec hL hW1' htp'_mem hrev_p htag_p
      have hW_base : LctInvWith P { n := st.n, splay := s2, freeHead := st.freeHead } trees_base freeList depth := hdet_spec.1
      have hact_perm2 : (trees_base.flatMap AuxTree.toList).Perm (trees1.flatMap AuxTree.toList) :=
        active_perm_detachRight htp'_mem
      have hact_perm3 : (trees'.flatMap AuxTree.toList).Perm (trees_base.flatMap AuxTree.toList) :=
        active_perm_attachRight hp_mem_det ht_prev_base hdet_ne_prev
      have hact_perm_fin : (trees'.flatMap AuxTree.toList).Perm active0 :=
        hact_perm3.trans (hact_perm2.trans (hact_perm1.trans hact_perm0))
      have hpar_fin : ∀ z, inducedSubPar P st'.splay trees' z = par0 z := fun z => by
        have h1 : inducedSubPar P (SplayState.attachRight P s2 p t_prev.rootId) trees' z =
            inducedSubPar P s1 trees1 z := by simpa [trees_base, t_next, trees', s1, s2] using hpar2' z
        rw [← hs3_eq, h1]
        have h2 : inducedSubPar P s1 trees1 z = inducedSubPar P st.splay trees z := by
          simpa [trees1, htp'_p] using hpar1 z
        rw [h2, hpar_eq]
      have hpairs_det := forestPairs_perm_detachRight hL htp'_mem (hW1'.treesInv _ htp'_mem) hrev_p htag_p hW1'.activeNodup
      have hpairs_att := forestPairs_perm_attachRight hL hW_base.treesNonEmpty hp_mem_det ht_prev_base hdet_ne_prev
        hdet_inv hdet_rev hdet_tag (hW_base.treesInv _ ht_prev_base) (hW_base.treesNonEmpty _ ht_prev_base) hW_base.activeNodup
      have hpairs_fin : (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) := by
        have hperm_a : (forestPairs P st'.splay trees').Perm (forestPairs P s2 trees_base) := by
          rw [← hs3_eq]
          exact hpairs_att
        exact hperm_a.trans (hpairs_det.trans (by simpa [trees1, htp'_p] using hpairs1))
      -- `evalPairs` of `t_next` -> `listLast0` and `listHead0`
      have hdisj_det_prev : ∀ a ∈ (AuxTree.node p L AuxTree.leaf).toList, a ∉ t_prev.toList := fun a ha hm =>
        hdet_ne_prev (flatMap_mem_unique hW_base.activeNodup hp_mem_det ht_prev_base ha hm)
      have hatt_p := SplayState.attachRight_preserves hL hdet_inv hdet_rev hdet_tag
        (hW_base.treesInv _ ht_prev_base) (hW_base.treesNonEmpty _ ht_prev_base) rfl hdisj_det_prev
      rcases hatt_p with ⟨_, _, _, _, hev_next, _⟩
      have hev_L_eq : SplayState.evalPairs P s2 L false P.idTag = SplayState.evalPairs P s1 L false P.idTag := by
        have hev_lhs := evalPairs_of_rev_false hL hdet_rev hdet_tag (l := L) (r := AuxTree.leaf)
        simp only [SplayState.evalPairs.eq_1, List.append_nil] at hev_lhs
        rw [hev_lhs] at hev_L2
        exact (List.append_inj hev_L2 (by simp [evalPairs_length])).1
      have hev_prev_s2 : SplayState.evalPairs P s2 t_prev false P.idTag =
          SplayState.evalPairs P st.splay t_prev false P.idTag := by
        refine SplayState.evalPairs_agree P (fun w hw => ?_) false P.idTag
        have hw_nt0 : w ∉ (AuxTree.node p L R).toList := fun hm =>
          htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev (htp'_perm.mem_iff.mp (by simpa [htp'_p] using hm)) hw)
        rw [hout_det w hw_nt0, hag_prev1 w hw]
      have hev_next_fin : SplayState.evalPairs P st'.splay t_next false P.idTag =
          SplayState.evalPairs P s1 L false P.idTag ++ [(p, (s2.nodes p).val)] ++
            SplayState.evalPairs P st.splay t_prev false P.idTag := by
        rw [← hs3_eq]
        simpa [ht_rt, hev_L_eq, hev_prev_s2, List.append_assoc] using hev_next
      have hids_next : treeIds P st'.splay t_next =
          (treeIds P s1 L ++ [p]) ++ treeIds P st.splay t_prev := by
        dsimp only [treeIds]
        rw [hev_next_fin]
        simp [List.map_append]
      have hlast_next : listLast0 (treeIds P st'.splay t_next) = v := by
        rw [hids_next, listLast0_append_of_ne_nil (treeIds_ne_nil (W.treesNonEmpty t_prev ht_prev)), hlast]
      have hhead_next_eq : listHead0 (treeIds P st'.splay t_next) =
          listHead0 (treeIds P s1 (AuxTree.node p L R)) := by
        have hids_tp' : treeIds P s1 (AuxTree.node p L R) =
            (treeIds P s1 L ++ [p]) ++ treeIds P s1 R :=
          treeIds_of_rev_false hL hrev_p htag_p
        rw [hids_next, listHead0_append_of_ne_nil (by simp : treeIds P s1 L ++ [p] ≠ [])]
        rw [hids_tp']
        exact (listHead0_append_of_ne_nil (by simp : treeIds P s1 L ++ [p] ≠ [])).symm
      let active' := trees'.flatMap AuxTree.toList
      let v_new := vSize P st'.splay active' par0 trees'
      have hpar_eq_s1 : ∀ z, inducedSubPar P s1 trees1 z = par0 z := fun z => by
        have h2 : inducedSubPar P s1 trees1 z = inducedSubPar P st.splay trees z := by
          simpa [trees1, htp'_p] using hpar1 z
        rw [h2, hpar_eq]
      have hsz_next_tp' : t_next.treeSize v_new =
          (AuxTree.node p L R).treeSize (vSize P s1 (trees1.flatMap AuxTree.toList)
            (inducedSubPar P s1 trees1) trees1) := by
        have h1 : t_next.treeSize (vSize P st'.splay active' (inducedSubPar P st'.splay trees') trees') =
            repSize active' (inducedSubPar P st'.splay trees') (listHead0 (treeIds P st'.splay t_next)) :=
          treeSize_vSize_eq_repSize hW2 ht_next_mem
        have h2 : (AuxTree.node p L R).treeSize (vSize P s1 (trees1.flatMap AuxTree.toList)
              (inducedSubPar P s1 trees1) trees1) =
            repSize (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1)
              (listHead0 (treeIds P s1 (AuxTree.node p L R))) :=
          treeSize_vSize_eq_repSize hW1' htp'_mem
        have hcongr_vnew : vSize P st'.splay active' (inducedSubPar P st'.splay trees') trees' = v_new :=
          vSize_congr_par hpar_fin
        rw [hcongr_vnew] at h1
        rw [h1, h2, hhead_next_eq]
        exact repSize_congr_perm (hact_perm3.trans hact_perm2) (fun z => by rw [hpar_fin, hpar_eq_s1]) _
      have hcongr_vold : vSize P st.splay active (inducedSubPar P st.splay trees) trees = v_old :=
        vSize_congr_par hpar_eq
      have hsz_next_eq_tp : t_next.treeSize v_new = tp.treeSize v_old := by
        rw [hsz_next_tp']
        have h2 : (AuxTree.node p L R).treeSize (vSize P s1 (trees1.flatMap AuxTree.toList)
              (inducedSubPar P s1 trees1) trees1) =
            repSize (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1)
              (listHead0 (treeIds P s1 (AuxTree.node p L R))) :=
          treeSize_vSize_eq_repSize hW1' htp'_mem
        have h3 : tp.treeSize (vSize P st.splay active (inducedSubPar P st.splay trees) trees) =
            repSize active (inducedSubPar P st.splay trees) (listHead0 (treeIds P st.splay tp)) :=
          treeSize_vSize_eq_repSize W htp
        rw [hcongr_vold] at h3
        rw [h2, h3, treeIds_eq_of_evalPairs (by simpa [htp'_p] using hev1)]
        exact repSize_congr_perm hact_perm1 (fun z => by rw [hpar_eq_s1, hpar_eq]) _
      have hsz_prev_eq : t_prev.treeSize v_old = repSize active par0 h_prev := by
        have h3 : t_prev.treeSize (vSize P st.splay active (inducedSubPar P st.splay trees) trees) =
            repSize active (inducedSubPar P st.splay trees) h_prev :=
          treeSize_vSize_eq_repSize W ht_prev
        rw [hcongr_vold] at h3
        rw [h3]
        exact repSize_congr_perm List.Perm.rfl hpar_eq _
      have hsz_tp_eq : tp.treeSize v_old = repSize active par0 (listHead0 (treeIds P st.splay tp)) := by
        have h3 : tp.treeSize (vSize P st.splay active (inducedSubPar P st.splay trees) trees) =
            repSize active (inducedSubPar P st.splay trees) (listHead0 (treeIds P st.splay tp)) :=
          treeSize_vSize_eq_repSize W htp
        rw [hcongr_vold] at h3
        rw [h3]
        exact repSize_congr_perm List.Perm.rfl hpar_eq _
      have hmem_sub : ∀ x ∈ active, par0 x ≠ 0 → par0 x ∈ active := fun x hx hpx => by
        rw [← hpar_eq] at hpx ⊢; exact W.subPar_mem_active hx hpx
      have hdec_sub : ∀ x ∈ active, par0 x ≠ 0 → depth (par0 x) < depth x := fun x hx hpx => by
        rw [← hpar_eq] at hpx ⊢; exact W.acyclic x hx hpx
      have hr_p_h : reaches par0 active.length p h_prev = true :=
        (reaches_step_iff W.activeNodup hmem_sub hdec_sub hh_act).mpr
          (Or.inr ⟨by rw [hpar_h, hp_def]; exact hp_nz, by rw [hpar_h]; exact reaches_self par0 _ _⟩)
      have h_prev_le_p : repSize active par0 h_prev + 1 ≤ repSize active par0 p := by
        refine filter_length_lt_of_imp W.activeNodup (fun w hw hwh => ?_) hp_act (reaches_self par0 _ _) ?_
        · exact reaches_trans W.activeNodup hmem_sub hdec_sub hwh hr_p_h hw
        · by_contra hhp
          have hhp_true : reaches par0 active.length h_prev p = true := by
            cases hb : reaches par0 active.length h_prev p <;> simp_all
          have hle := depth_le_of_reaches hmem_sub hdec_sub active.length h_prev p hhp_true hp_act
          have hlt := hdec_sub h_prev hh_act (by rw [hpar_h]; exact hp_nz)
          rw [hpar_h] at hlt; omega
      have hp_le_tp : repSize active par0 p ≤ repSize active par0 (listHead0 (treeIds P st.splay tp)) := by
        dsimp only [repSize]
        refine filter_length_le_of_imp _ _ _ (fun w hw hwp => ?_)
        have hr_tp_p := tree_reaches_head W htp hp_tp
        have hr_tp_p' : reaches par0 active.length (listHead0 (treeIds P st.splay tp)) p = true := by
          rwa [reaches_congr hpar_eq] at hr_tp_p
        exact reaches_trans W.activeNodup hmem_sub hdec_sub hwp hr_tp_p' hw
      have hsz_strict : t_prev.treeSize v_old + 1 ≤ t_next.treeSize v_new := by
        rw [hsz_prev_eq, hsz_next_eq_tp, hsz_tp_eq]; omega
      have hact'_le : active'.length ≤ 2 * st.n :=
        active_length_le_two_mul hW2.activeNodup (fun x hx => (show st'.n = st.n from rfl) ▸ hW2.activeValid x hx)
      have hsz_le2n : t_next.treeSize v_new ≤ 2 * st.n := by
        rw [hsz_next_eq_tp, hsz_tp_eq]
        have hlen_act : active.length ≤ 2 * st.n := by
          rw [← hact_perm1.length_eq, ← hact_perm2.length_eq, ← hact_perm3.length_eq]
          exact hact'_le
        exact (repSize_le_active _).trans hlen_act
      have hrank_next_le : t_next.rank v_new ≤ Nat.log 2 (2 * st.n + 1) :=
        Nat.log_mono_right (by omega)
      have hrank_ppar := findSubtree_rank_ge_of_ppar W htp ht_prev hp_tp (by rw [ht_rt, hp_def])
      have hrank_sub_le : t_prev.rank v_old ≤ (tp.findSubtree p).rank v_old := by
        rw [← hcongr_vold]; exact hrank_ppar.2
      have hrank_next_eq_tp' : t_next.rank v_new = (AuxTree.node p L R).rank v_old := by
        have h_eq : (AuxTree.node p L R).treeSize (vSize P st.splay active (inducedSubPar P st.splay trees) trees) =
            tp.treeSize (vSize P st.splay active (inducedSubPar P st.splay trees) trees) := by
          simpa [htp'_p] using htsz1
        rw [hcongr_vold] at h_eq
        simp only [AuxTree.rank, hsz_next_eq_tp, h_eq]
      have hpot_splay : h1 + sumTreePhi P st' + 3 * t_prev.rank v_old ≤ sumTreePhi P st + 3 * t_next.rank v_new := by
        have h1_def : h1 = splayDepth st.splay (2 * st.n + 1) p / 2 := rfl
        have h1' : h1 + sumTreePhi P { n := st.n, splay := s1, freeHead := st.freeHead } +
            3 * (tp.findSubtree p).rank (vSize P st.splay active (inducedSubPar P st.splay trees) trees) ≤
            sumTreePhi P st +
              3 * (AuxTree.node p L R).rank (vSize P st.splay active (inducedSubPar P st.splay trees) trees) := by
          simpa [h1_def, htp'_p] using hpot1
        rw [hcongr_vold] at h1'
        have hPhi2_eq : sumTreePhi P st' = sumTreePhi P { n := st.n, splay := s1, freeHead := st.freeHead } := by
          rw [hst_eq]; exact hPhi2'
        rw [hPhi2_eq, hrank_next_eq_tp']
        omega
      have hHeavy_step : 1 + heavyCount P st' + 2 * (Nat.log 2 (2 * st.n + 1) - t_next.rank v_new) ≤
          heavyCount P st + 2 * (Nat.log 2 (2 * st.n + 1) - t_prev.rank v_old) := by
        have hH1_eq : heavyCount P { n := st.n, splay := s1, freeHead := st.freeHead } = heavyCount P st := hH1
        by_cases hhev : isHeavyEdge P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) t_prev = true
        · have ht_h' : heavyCount P st' + 1 = heavyCount P st := by
            rw [hst_eq, ← hH1_eq]; exact hHeavy_t hhev
          have hrank_mono : t_prev.rank v_old ≤ t_next.rank v_new :=
            Nat.log_mono_right (by omega)
          omega
        · have hhev_f : isHeavyEdge P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) t_prev = false := by
            cases hb : isHeavyEdge P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) t_prev <;> simp_all
          rcases hHeavy_f hhev_f with ⟨hHc_le, h2sz⟩
          have hHc_le' : heavyCount P st' ≤ heavyCount P st + 1 := by
            rw [hst_eq, ← hH1_eq]; exact hHc_le
          have h2_old : 2 * t_prev.treeSize v_old ≤ t_next.treeSize v_new := by
            have hids_prev1 : treeIds P s1 t_prev = treeIds P st.splay t_prev :=
              treeIds_eq_of_evalPairs (SplayState.evalPairs_agree P hag_prev1 false P.idTag)
            have hsz_prev1 : t_prev.treeSize (vSize P s1 (trees1.flatMap AuxTree.toList)
                (inducedSubPar P s1 trees1) trees1) = t_prev.treeSize v_old := by
              have h3 : t_prev.treeSize (vSize P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) trees1) =
                  repSize (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1)
                    (listHead0 (treeIds P s1 t_prev)) :=
                treeSize_vSize_eq_repSize hW1' ht_prev_1
              rw [h3, hids_prev1, hsz_prev_eq]
              exact repSize_congr_perm hact_perm1 hpar_eq_s1 _
            have hrep_p : repSize (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) p =
                repSize active par0 p :=
              repSize_congr_perm hact_perm1 hpar_eq_s1 p
            have h2sz' : 2 * t_prev.treeSize (vSize P s1 (trees1.flatMap AuxTree.toList)
                (inducedSubPar P s1 trees1) trees1) ≤
                repSize (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) p := h2sz
            rw [hsz_prev1, hrep_p] at h2sz'
            rw [hsz_next_eq_tp, hsz_tp_eq]
            omega
          have h1_old : 1 ≤ t_prev.treeSize v_old := by
            rw [hsz_prev_eq]; exact repSize_pos_of_mem hh_act
          have hlog_inc : t_prev.rank v_old + 1 ≤ t_next.rank v_new :=
            nat_log_succ_of_two_mul_le h1_old h2_old
          omega
      have hr_p_v : reaches par0 active0.length p v = true := by
        have hr_hv := tree_reaches_head W ht_prev hv_prev
        have hr_hv' : reaches par0 active.length h_prev v = true := by rwa [reaches_congr hpar_eq] at hr_hv
        have hr_pv := reaches_trans W.activeNodup hmem_sub hdec_sub hr_hv' hr_p_h
          (List.mem_flatMap.mpr ⟨t_prev, ht_prev, hv_prev⟩)
        rwa [← hact_perm0.length_eq]
      have huntouched : ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par0 active0.length w v = false) →
          c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
        intro c hc hno
        have hv_nc : v ∉ c.toList := fun hm => by
          have := hno v hm; simp [reaches_self] at this
        have hp_nc : p ∉ c.toList := fun hm => by
          have := hno p hm; simp [hr_p_v] at this
        have hc_tp : c ≠ tp := fun h => hp_nc (h ▸ hp_tp)
        have hc_prev : c ≠ t_prev := fun h => hv_nc (h ▸ hv_prev)
        have hc_1 : c ∈ trees1 := List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc_tp).mpr hc)
        have hc_tp' : c ≠ AuxTree.node p L R := fun h => hp_nc (h ▸ by simp [AuxTree.toList])
        have hc_det : c ≠ AuxTree.node p L AuxTree.leaf := fun h => hp_nc (h ▸ by simp [AuxTree.toList])
        have hc_base : c ∈ trees_base := by
          by_cases hR : R = AuxTree.leaf
          · simp [trees_base, hR, hc_1]
          · simp [trees_base, hR, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc_tp').mpr hc_1)]
        have hc_trees' : c ∈ trees' :=
          List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc_prev).mpr ((List.mem_erase_of_ne hc_det).mpr hc_base))
        rcases SplayState.attachRight_preserves hL hdet_inv hdet_rev hdet_tag
          (hW_base.treesInv _ ht_prev_base) (hW_base.treesNonEmpty _ ht_prev_base) rfl hdisj_det_prev with
          ⟨_, _, _, _, _, hout_att⟩
        have hag_c : ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
          intro w hw
          have hw_nt_next : w ∉ t_next.toList := fun hm => by
            simp only [t_next, AuxTree.toList, List.mem_append, List.mem_singleton] at hm
            rcases hm with (hl | rfl) | hpr_w
            · exact hc_tp' (flatMap_mem_unique hW1'.activeNodup htp'_mem hc_1
                (by simp [AuxTree.toList, hl]) hw).symm
            · exact hp_nc hw
            · exact hc_prev (flatMap_mem_unique W.activeNodup ht_prev hc hpr_w hw).symm
          have hw_nt0 : w ∉ (AuxTree.node p L R).toList := fun hm =>
            hc_tp (flatMap_mem_unique W.activeNodup hc htp hw (htp'_perm.mem_iff.mp (by simpa [htp'_p] using hm)))
          have hw_ntp : w ∉ tp.toList := fun hm => hc_tp (flatMap_mem_unique W.activeNodup hc htp hw hm)
          rw [← hs3_eq]
          rw [hout_att w hw_nt_next, hout_det w hw_nt0, hout1 w hw_ntp]
        exact ⟨hc_trees', hag_c⟩
      exact ⟨ht_next_mem, hv_next, hW2, hact_perm_fin, hpar_fin, hpairs_fin, hlast_next,
        hsz_strict, hsz_le2n, hrank_next_le, hpot_splay, hHeavy_step, huntouched⟩

/-! ### Phase 3 of `expose`: `lctExposeLoop_spec` and `lctExpose_spec` -/

theorem lctExposeLoop_spec {P : LctPayload α σ τ} (hL : P.Laws) :
    ∀ fuel {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
      {t_last : AuxTree} {last v : ℕ} {par0 : ℕ → ℕ} {active0 : List ℕ},
      LctInvWith P st trees freeList depth →
      t_last ∈ trees →
      t_last.rootId = last →
      v ∈ t_last.toList →
      listLast0 (treeIds P st.splay t_last) = v →
      (∀ z, inducedSubPar P st.splay trees z = par0 z) →
      (trees.flatMap AuxTree.toList).Perm active0 →
      2 * st.n - t_last.treeSize (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) < fuel →
      let r := lctExposeLoop P st fuel last
      let st' := r.1
      let last' := r.2.1
      let hLoop := r.2.2.1
      let iLoop := r.2.2.2
      let active := trees.flatMap AuxTree.toList
      let v_old := vSize P st.splay active par0 trees
      ∃ trees' t_fin,
        let active' := trees'.flatMap AuxTree.toList
        let v_fin := vSize P st'.splay active' par0 trees'
        t_fin ∈ trees' ∧
          t_fin.rootId = last' ∧
          v ∈ t_fin.toList ∧
          listLast0 (treeIds P st'.splay t_fin) = v ∧
          (st'.splay.nodes last').ppar = 0 ∧
          LctInvWith P st' trees' freeList depth ∧
          active'.Perm active0 ∧
          (∀ z, inducedSubPar P st'.splay trees' z = par0 z) ∧
          (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) ∧
          t_fin.treeSize v_fin ≤ 2 * st.n ∧
          t_fin.rank v_fin ≤ Nat.log 2 (2 * st.n + 1) ∧
          hLoop + sumTreePhi P st' + 3 * t_last.rank v_old ≤ sumTreePhi P st + 3 * t_fin.rank v_fin ∧
          iLoop + heavyCount P st' + 2 * (Nat.log 2 (2 * st.n + 1) - t_fin.rank v_fin) ≤
            heavyCount P st + 2 * (Nat.log 2 (2 * st.n + 1) - t_last.rank v_old) ∧
          ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par0 active0.length w v = false) →
            c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfuel
      omega
  | succ fuel ih =>
      intro st trees freeList depth t_last last v par0 active0 W ht_last ht_rt hv_last hlast hpar_eq hact_perm0 hfuel
      by_cases hp0 : (st.splay.nodes last).ppar = 0
      · refine ⟨trees, t_last, ?_⟩
        have hact_le := active_length_le_two_mul W.activeNodup W.activeValid
        have hcongr_v : vSize P st.splay (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) trees =
            vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees :=
          vSize_congr_par hpar_eq
        have hsz_le2n : t_last.treeSize (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) ≤ 2 * st.n := by
          rw [← hcongr_v, treeSize_vSize_eq_repSize W ht_last]
          exact (repSize_le_active _).trans hact_le
        have hrank_le : t_last.rank (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) ≤
            Nat.log 2 (2 * st.n + 1) := Nat.log_mono_right (by omega)
        simp only [lctExposeLoop, beq_iff_eq.mpr hp0, ↓reduceIte]
        refine ⟨ht_last, ht_rt, hv_last, hlast, hp0, W, hact_perm0, hpar_eq, List.Perm.rfl,
          hsz_le2n, hrank_le, ?_, ?_, fun c hc _ => ⟨hc, fun _ _ => trivial⟩⟩
        · omega
        · omega
      · rcases lctExposeStep_spec hL W ht_last ht_rt hv_last hlast hp0 par0 hpar_eq active0 hact_perm0 with
          ⟨trees1, L1, ht1_mem, hv1, hW1, hact_perm1, hpar1, hpairs1, hlast1, hsz_inc, hsz1_le2n,
            hrank1_le, hpot1, hH1, hunt1⟩
        let step := lctExposeStep P st last
        have hsz_inc' : t_last.treeSize (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) + 1 ≤
            (AuxTree.node (st.splay.nodes last).ppar L1 t_last).treeSize
              (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1) := hsz_inc
        have hsz1_le2n' : (AuxTree.node (st.splay.nodes last).ppar L1 t_last).treeSize
            (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1) ≤ 2 * st.n := hsz1_le2n
        have hfuel1 : 2 * step.1.n - (AuxTree.node (st.splay.nodes last).ppar L1 t_last).treeSize
            (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1) < fuel := by
          change 2 * st.n - _ < fuel
          omega
        have ht1_rt : (AuxTree.node (st.splay.nodes last).ppar L1 t_last).rootId = (st.splay.nodes last).ppar := rfl
        rcases ih hW1 ht1_mem ht1_rt hv1 hlast1 hpar1 hact_perm1 hfuel1 with
          ⟨trees', t_fin, ht_fin, ht_fin_rt, hv_fin, hlast_fin, hp_fin, hW_fin, hact_fin,
            hpar_fin, hpairs_fin, hsz_fin_le, hrank_fin_le, hpot_fin, hH_fin, hunt_fin⟩
        refine ⟨trees', t_fin, ?_⟩
        have hbeq0 : ((st.splay.nodes last).ppar == 0) = false := beq_false_of_ne hp0
        simp only [lctExposeLoop, hbeq0, Bool.false_eq_true, ↓reduceIte]
        let rLoop := lctExposeLoop P step.1 fuel step.2.1
        have hstep_n : (lctExposeStep P st last).1.n = st.n := rfl
        have hpot1' : step.2.2 + sumTreePhi P step.1 +
            3 * t_last.rank (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) ≤
            sumTreePhi P st + 3 * (AuxTree.node step.2.1 L1 t_last).rank
              (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1) := hpot1
        have hpot_fin' : rLoop.2.2.1 + sumTreePhi P rLoop.1 +
            3 * (AuxTree.node step.2.1 L1 t_last).rank
              (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1) ≤
            sumTreePhi P step.1 +
              3 * t_fin.rank (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees') := hpot_fin
        have hH1' : 1 + heavyCount P step.1 +
            2 * (Nat.log 2 (2 * st.n + 1) - (AuxTree.node step.2.1 L1 t_last).rank
              (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1)) ≤
            heavyCount P st + 2 * (Nat.log 2 (2 * st.n + 1) -
              t_last.rank (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees)) := hH1
        have hH_fin_tmp := hH_fin
        rw [hstep_n] at hH_fin_tmp
        have hH_fin' : rLoop.2.2.2 + heavyCount P rLoop.1 +
            2 * (Nat.log 2 (2 * st.n + 1) -
              t_fin.rank (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees')) ≤
            heavyCount P step.1 + 2 * (Nat.log 2 (2 * st.n + 1) -
              (AuxTree.node step.2.1 L1 t_last).rank
                (vSize P step.1.splay (trees1.flatMap AuxTree.toList) par0 trees1)) := hH_fin_tmp
        have hsz_fin_le' : t_fin.treeSize (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees') ≤ 2 * st.n :=
          hstep_n ▸ hsz_fin_le
        have hrank_fin_le' : t_fin.rank (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees') ≤
            Nat.log 2 (2 * st.n + 1) := hstep_n ▸ hrank_fin_le
        refine ⟨ht_fin, ht_fin_rt, hv_fin, hlast_fin, hp_fin, hW_fin, hact_fin, hpar_fin,
          hpairs_fin.trans hpairs1, hsz_fin_le', hrank_fin_le', ?_, ?_, fun c hc hno => ?_⟩
        · change (step.2.2 + rLoop.2.2.1) + sumTreePhi P rLoop.1 +
              3 * t_last.rank (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees) ≤
            sumTreePhi P st +
              3 * t_fin.rank (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees')
          omega
        · change (1 + rLoop.2.2.2) + heavyCount P rLoop.1 +
              2 * (Nat.log 2 (2 * st.n + 1) -
                t_fin.rank (vSize P rLoop.1.splay (trees'.flatMap AuxTree.toList) par0 trees')) ≤
            heavyCount P st + 2 * (Nat.log 2 (2 * st.n + 1) -
              t_last.rank (vSize P st.splay (trees.flatMap AuxTree.toList) par0 trees))
          omega
        · rcases hunt1 c hc hno with ⟨hc1, hag1⟩
          rcases hunt_fin c hc1 hno with ⟨hc', hag'⟩
          exact ⟨hc', fun w hw => (hag' w hw).trans (hag1 w hw)⟩

theorem lctExpose_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) :
    let res := lctExposeCost P st v
    let st' := res.1
    let halves := res.2.1
    let iters := res.2.2
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∃ trees' Lv,
      let t_exp := AuxTree.node v Lv AuxTree.leaf
      t_exp ∈ trees' ∧
        LctInvWith P st' trees' freeList depth ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        (∀ z, inducedSubPar P st'.splay trees' z = par z) ∧
        (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) ∧
        (st'.splay.nodes v).ppar = 0 ∧
        (st'.splay.nodes v).right = 0 ∧
        (st'.splay.nodes v).rev = false ∧
        (st'.splay.nodes v).tag = P.idTag ∧
        (∀ z, z ∈ t_exp.toList ↔ reaches par active.length z v = true) ∧
        (∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
          c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w) ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
  intro res st' halves iters active par
  rcases lctExposeInit_spec hL W htv hv with
    ⟨trees1, L1, ht1_mem, hv1, hW1, hact_perm1, hpar1, hpairs1, hlast1, _, _,
      hsz1_ge1, hsz1_le2n, hrank1_le, hpot1, hH1_le, hunt1⟩
  let s0 := SplayState.splay P st.splay (2 * st.n + 1) v
  let s1 := SplayState.detachRight P s0 v
  let st1 : LctState α σ τ := { n := st.n, splay := s1, freeHead := st.freeHead }
  have hfuel1 : 2 * st1.n - (AuxTree.node v L1 AuxTree.leaf).treeSize
      (vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1) < 2 * st.n + 1 := by
    have hcongr_v1 : vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1 =
        vSize P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) trees1 :=
      vSize_congr_par (fun z => (hpar1 z).symm)
    change 2 * st.n - _ < 2 * st.n + 1
    rw [hcongr_v1]
    omega
  rcases lctExposeLoop_spec hL (2 * st.n + 1) hW1 ht1_mem (last := v) rfl hv1 hlast1 hpar1 hact_perm1 hfuel1 with
    ⟨trees2, t_loop, ht2_mem, ht2_rt, hv2, hlast2, hpp2, hW2, hact_perm2, hpar2, hpairs2,
      hsz2_le, hrank2_le, hpot2, hH2, hunt2⟩
  let rLoop := lctExposeLoop P st1 (2 * st.n + 1) v
  have hrLoop_n : rLoop.1.n = st.n := lctExposeLoop_n P (2 * st.n + 1) st1 v
  have hrLoop_fh : rLoop.1.freeHead = st.freeHead := lctExposeLoop_freeHead P (2 * st.n + 1) st1 v
  rcases lctSplayTree_spec hL hW2 ht2_mem hv2 with
    ⟨t_fin, htf_ne, htf_rt, htf_perm, hpp_fin, hrev_fin, htag_fin, hW_fin, hH_fin,
      hpairs_fin, hpar_fin, hout_fin, hev_fin, htsz_fin, hrank_fin, hpot_fin⟩
  have hst_fin_eq : st' =
      LctState.mk rLoop.1.n (SplayState.splay P rLoop.1.splay (2 * rLoop.1.n + 1) v) rLoop.1.freeHead := by
    rw [hrLoop_n]
    rfl
  have hpp_v_fin : (st'.splay.nodes v).ppar = 0 := by
    rw [hst_fin_eq]
    have hpp2' : (rLoop.1.splay.nodes t_loop.rootId).ppar = 0 := by
      simpa [ht2_rt] using hpp2
    exact hpp_fin.trans hpp2'
  have hlast_fin : listLast0 (treeIds P st'.splay t_fin) = v := by
    rw [hst_fin_eq, treeIds_eq_of_evalPairs hev_fin]; exact hlast2
  cases htf_eq : t_fin with
  | leaf => exact absurd htf_eq htf_ne
  | node vr Lv Rf =>
      have hvr : vr = v := by simpa [htf_eq, AuxTree.rootId] using htf_rt
      have htf_v : t_fin = AuxTree.node v Lv Rf := by simpa [hvr] using htf_eq
      have hrev_fin' : (st'.splay.nodes v).rev = false := by rw [hst_fin_eq]; exact hrev_fin
      have htag_fin' : (st'.splay.nodes v).tag = P.idTag := by rw [hst_fin_eq]; exact htag_fin
      have hRf := right_eq_leaf_of_listLast0 hL
        (by rw [hst_fin_eq, ← htf_v]; exact hW_fin.treesInv t_fin (by simp)) hrev_fin' htag_fin'
        (by simpa [htf_v] using hlast_fin)
      rcases hRf with ⟨rfl, hright0⟩
      let trees' := AuxTree.node v Lv AuxTree.leaf :: trees2.erase t_loop
      refine ⟨trees', Lv, ?_⟩
      have htf_mem : AuxTree.node v Lv AuxTree.leaf ∈ trees' := List.mem_cons_self
      have hW' : LctInvWith P st' trees' freeList depth := by
        rw [hst_fin_eq]; simpa [trees', htf_v] using hW_fin
      have hact_perm' : (trees'.flatMap AuxTree.toList).Perm active := by
        have hp := flatMap_perm_of_replace ht2_mem htf_perm
        simpa [trees', htf_v] using hp.trans hact_perm2
      have hpar' : ∀ z, inducedSubPar P st'.splay trees' z = par z := fun z => by
        rw [hst_fin_eq]
        have h1' : inducedSubPar P (SplayState.splay P rLoop.1.splay (2 * rLoop.1.n + 1) v) trees' z =
            inducedSubPar P rLoop.1.splay trees2 z := by simpa [trees', htf_v] using hpar_fin z
        rw [h1', hpar2 z]
      have hpairs' : (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) := by
        rw [hst_fin_eq]
        have h1 : (forestPairs P (SplayState.splay P rLoop.1.splay (2 * rLoop.1.n + 1) v) trees').Perm
            (forestPairs P rLoop.1.splay trees2) := by
          simpa [trees', htf_v] using hpairs_fin
        exact h1.trans (hpairs2.trans hpairs1)
      have hreaches_iff : ∀ z, z ∈ (AuxTree.node v Lv AuxTree.leaf).toList ↔ reaches par active.length z v = true := by
        intro z
        have hr := tnode_reaches_iff hL hW' htf_mem hpp_v_fin hrev_fin' htag_fin' z
        rw [hact_perm'.length_eq, reaches_congr hpar'] at hr
        exact hr
      have huntouched : ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
          c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
        intro c hc hno
        rcases hunt1 c hc hno with ⟨hc1, hag1⟩
        rcases hunt2 c hc1 hno with ⟨hc2, hag2⟩
        have hv_nc : v ∉ c.toList := fun hm => by
          have := hno v hm; simp [reaches_self] at this
        have hc_nloop : c ≠ t_loop := fun h => hv_nc (h ▸ hv2)
        have hc' : c ∈ trees' := List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc_nloop).mpr hc2)
        have hag' : ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
          intro w hw
          have hw_nloop : w ∉ t_loop.toList := fun hm =>
            hc_nloop (flatMap_mem_unique hW2.activeNodup hc2 ht2_mem hw hm)
          rw [hst_fin_eq]
          dsimp only
          rw [hout_fin w hw_nloop, hag2 w hw, hag1 w hw]
        exact ⟨hc', hag'⟩
      have hcongr_v2 : vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList)
            (inducedSubPar P rLoop.1.splay trees2) trees2 =
          vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2 :=
        vSize_congr_par hpar2
      have htf_rank_eq : t_fin.rank (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList)
            (inducedSubPar P rLoop.1.splay trees2) trees2) =
          t_loop.rank (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2) := by
        simp only [AuxTree.rank]
        rw [htsz_fin, hcongr_v2]
      have hpot_fin' : halves + sumTreePhi P st' ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := by
        have hcongr_v1 : vSize P s1 (trees1.flatMap AuxTree.toList) (inducedSubPar P s1 trees1) trees1 =
            vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1 :=
          vSize_congr_par hpar1
        have hsd_fin_eq : splayDepth rLoop.1.splay (2 * st.n + 1) v =
            splayDepth rLoop.1.splay (2 * rLoop.1.n + 1) v := by rw [hrLoop_n]
        have hsum_fin_eq : sumTreePhi P st' =
            sumTreePhi P (LctState.mk rLoop.1.n (SplayState.splay P rLoop.1.splay (2 * rLoop.1.n + 1) v)
              rLoop.1.freeHead) := by rw [hst_fin_eq]
        have hpot3' : splayDepth rLoop.1.splay (2 * st.n + 1) v / 2 + sumTreePhi P st' ≤
            sumTreePhi P rLoop.1 + 3 * t_loop.rank
              (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2) := by
          have hp_fin' : splayDepth rLoop.1.splay (2 * rLoop.1.n + 1) v / 2 +
              sumTreePhi P (LctState.mk rLoop.1.n (SplayState.splay P rLoop.1.splay (2 * rLoop.1.n + 1) v)
                rLoop.1.freeHead) +
              3 * (t_loop.findSubtree v).rank (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList)
                (inducedSubPar P rLoop.1.splay trees2) trees2) ≤
              sumTreePhi P rLoop.1 + 3 * t_fin.rank (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList)
                (inducedSubPar P rLoop.1.splay trees2) trees2) := hpot_fin
          rw [htf_rank_eq, ← hsd_fin_eq, ← hsum_fin_eq] at hp_fin'
          omega
        have hpot2' : rLoop.2.2.1 + sumTreePhi P rLoop.1 +
            3 * (AuxTree.node v L1 AuxTree.leaf).rank
              (vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1) ≤
            sumTreePhi P st1 + 3 * t_loop.rank
              (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2) := hpot2
        have hpot1' : splayDepth st.splay (2 * st.n + 1) v / 2 + sumTreePhi P st1 ≤
            sumTreePhi P st + 3 * (AuxTree.node v L1 AuxTree.leaf).rank
              (vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1) := by
          rw [← hcongr_v1]; exact hpot1
        have hrank2_le' : t_loop.rank (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2) ≤
            Nat.log 2 (2 * st.n + 1) := hrank2_le
        change splayDepth st.splay (2 * st.n + 1) v / 2 + rLoop.2.2.1 +
            splayDepth rLoop.1.splay (2 * st.n + 1) v / 2 + sumTreePhi P st' ≤ _
        omega
      have hH_fin' : iters + heavyCount P st' ≤ heavyCount P st + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
        have hH_s : heavyCount P st' = heavyCount P rLoop.1 := by rw [hst_fin_eq]; exact hH_fin
        have hH1_le' : heavyCount P st1 ≤ heavyCount P st + 1 := hH1_le
        have hH2' : rLoop.2.2.2 + heavyCount P rLoop.1 +
            2 * (Nat.log 2 (2 * st.n + 1) - t_loop.rank
              (vSize P rLoop.1.splay (trees2.flatMap AuxTree.toList) par trees2)) ≤
            heavyCount P st1 + 2 * (Nat.log 2 (2 * st.n + 1) - (AuxTree.node v L1 AuxTree.leaf).rank
              (vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1)) := hH2
        have hsub_le : Nat.log 2 (2 * st.n + 1) - (AuxTree.node v L1 AuxTree.leaf).rank
            (vSize P st1.splay (trees1.flatMap AuxTree.toList) par trees1) ≤ Nat.log 2 (2 * st.n + 1) :=
          Nat.sub_le _ _
        change 1 + rLoop.2.2.2 + heavyCount P st' ≤ _
        rw [hH_s]
        omega
      refine ⟨htf_mem, hW', hact_perm', hpar', hpairs', hpp_v_fin, hright0, hrev_fin', htag_fin',
        hreaches_iff, huntouched, hpot_fin', hH_fin'⟩

end

end MinCostFlow.LinkCut