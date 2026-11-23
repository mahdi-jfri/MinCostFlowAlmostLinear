module

public import MinCostFlow.LinkCut.Prog.MathForestExpose

/-!
# Pure Helpers for `lctRerootBody` Verification

Auxiliary structural, parent-map (`lctAuxParent`), acyclicity (`iterParent`), connected-component
(`rootAbove`), and heavy-edge doubling lemmas used to prove `revNode_reroot_invs` and
`lctRerootBody_runs`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem mem_off_slot_eq {mem₁ mem₂ : ℕ → ℕ} {nb x : ℕ}
    (hout : ∀ addr, addr < nb + NODE_STRIDE * x ∨ nb + NODE_STRIDE * x + NODE_STRIDE ≤ addr →
      mem₂ addr = mem₁ addr)
    {u off : ℕ} (hne : u ≠ x) (hoff : off < NODE_STRIDE) :
    nodeField mem₂ nb u off = nodeField mem₁ nb u off := by
  apply hout
  by_cases hlt : u < x
  · left
    have hmul : NODE_STRIDE * u + NODE_STRIDE ≤ NODE_STRIDE * x := by
      have : u + 1 ≤ x := hlt
      calc
        NODE_STRIDE * u + NODE_STRIDE = NODE_STRIDE * (u + 1) := by ring
        _ ≤ NODE_STRIDE * x := Nat.mul_le_mul_left _ this
    omega
  · right
    have hgt : x + 1 ≤ u := by omega
    have hmul : NODE_STRIDE * x + NODE_STRIDE ≤ NODE_STRIDE * u := by
      calc
        NODE_STRIDE * x + NODE_STRIDE = NODE_STRIDE * (x + 1) := by ring
        _ ≤ NODE_STRIDE * u := Nat.mul_le_mul_left _ hgt
    omega

theorem freeSlotChain_agree' {mem₁ mem₂ : ℕ → ℕ} {nb : ℕ} {xs : List ℕ} {hd : ℕ}
    (heq : ∀ ed ∈ xs, nodeField mem₂ nb ed OFF_EU = nodeField mem₁ nb ed OFF_EU)
    (hfc : FreeSlotChain mem₁ nb hd xs) :
    FreeSlotChain mem₂ nb hd xs := by
  induction xs generalizing hd with
  | nil => exact hfc
  | cons ed rest ih =>
      rcases hfc with ⟨hhd, hrest⟩
      refine ⟨hhd, ?_⟩
      rw [heq ed (by simp)]
      exact ih (fun e he => heq e (by simp [he])) hrest

theorem listParentFrom_getElem (prev : ℕ) :
    ∀ (xs : List ℕ), xs.Nodup → ∀ i (hi : i < xs.length),
      listParentFrom prev xs xs[i] = if i = 0 then prev else xs[i - 1]!
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | y :: ys, hnd, i, hi => by
      cases i with
      | zero => simp [listParentFrom]
      | succ i' =>
          have hnd_cons := List.nodup_cons.1 hnd
          have hi' : i' < ys.length := by simpa using hi
          have hne : ys[i'] ≠ y := fun heq => hnd_cons.1 (heq ▸ List.getElem_mem hi')
          have ih := listParentFrom_getElem y ys hnd_cons.2 i' hi'
          cases i' with
          | zero =>
              simpa [listParentFrom, hne] using ih
          | succ j =>
              simpa [listParentFrom, hne] using ih

theorem lctAuxParent_zero_of_trees {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    (hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ cap) :
    lctAuxParent mem nb cap 0 = 0 := by
  rw [lctAuxParent_mem_iff_of_trees hok hpp_le 0]
  have hnone : trees.findSome? (fun s =>
      let seq := s.evalInorder (revFlag mem nb) false
      if 0 ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq 0) else none) = none := by
    apply List.findSome?_eq_none_iff.2
    intro s hs
    have h0_nin : 0 ∉ s.evalInorder (revFlag mem nb) false := by
      intro h0
      have h0_mem := (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 h0
      have hb := ((hok.2.2.2.2.2.2.2.2.2 s hs).2.2).nodup_perm_mem h0_mem
      omega
    simp [h0_nin]
  simp [hnone]

theorem lctAuxParent_le_cap_of_trees {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    (hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ cap) :
    ∀ u, lctAuxParent mem nb cap u ≤ cap := by
  intro u
  rw [lctAuxParent_mem_iff_of_trees hok hpp_le u]
  cases hfs : trees.findSome? (fun s =>
      let seq := s.evalInorder (revFlag mem nb) false
      if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) with
  | none => simp
  | some p =>
      simp only
      rcases List.exists_of_findSome?_eq_some hfs with ⟨s, hs, hsome⟩
      dsimp only at hsome
      split_ifs at hsome with hu_in
      · have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
          hok.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
        have hnd_s : (s.evalInorder (revFlag mem nb) false).Nodup :=
          (s.evalInorder_perm (revFlag mem nb) false).nodup_iff.2
            (list_nodup_of_flatMap_nodup hnd_all hs)
        rcases List.getElem_of_mem hu_in with ⟨i, hi, hu_eq⟩
        have hp_eq := Option.some.inj hsome
        rw [← hp_eq, ← hu_eq, listParentFrom_getElem _ _ hnd_s i hi]
        cases i with
        | zero => exact hpp_le s hs
        | succ i' =>
            have hmem_prev : (s.evalInorder (revFlag mem nb) false)[i'] ∈ s.toList :=
              (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 (List.getElem_mem (by omega))
            simpa [List.getElem!_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : i' < (s.evalInorder (revFlag mem nb) false).length)] using
              (((hok.2.2.2.2.2.2.2.2.2 s hs).2.2).nodup_perm_mem hmem_prev).2

theorem eq_rootId_of_parent_zero {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {t : AuxTree} {pp u : ℕ} (ht : TreeMemMatch w h L mem nb cap t 0 pp)
    (hu : u ∈ t.toList) (hpz : nodeField mem nb u OFF_PARENT = 0) :
    u = t.rootId := by
  have go : ∀ (s : AuxTree) (p pp' : ℕ), TreeMemMatch w h L mem nb cap s p pp' →
      1 ≤ p → ∀ z ∈ s.toList, nodeField mem nb z OFF_PARENT ≠ 0 := by
    intro s
    induction s with
    | leaf => intro _ _ _ _ z hz; simp [AuxTree.toList] at hz
    | node id l r ihl ihr =>
        intro p pp' hs hp1 z hz
        rcases hs with ⟨hid1, _, _, _, hp_eq, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
        rcases hz with (hzl | rfl) | hzr
        · exact ihl _ _ hl hid1 _ hzl
        · rw [hp_eq]; omega
        · exact ihr _ _ hr hid1 _ hzr
  cases t with
  | leaf => simp [AuxTree.toList] at hu
  | node x l r =>
      rcases ht with ⟨hx1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | rfl) | hur
      · exact absurd hpz (go l x 0 hl hx1 u hul)
      · rfl
      · exact absurd hpz (go r x 0 hr hx1 u hur)

theorem lctAuxParent_revRoot_summary {w h L b n x : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {t₁ t₂ : AuxTree} {rest : List AuxTree}
    (hsf₁ : SplayForestOk w h L mem₁ (lctNodesBase b) (lctCap n) (t₁ :: rest))
    (hsf₂ : SplayForestOk w h L mem₂ (lctNodesBase b) (lctCap n) (t₂ :: rest))
    (hpp₁_le : ∀ s ∈ t₁ :: rest, nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n)
    (hpp₂_le : ∀ s ∈ t₂ :: rest, nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n)
    (hpp_t1 : nodeField mem₁ (lctNodesBase b) t₁.rootId OFF_PPAR = 0)
    (hpp_t2 : nodeField mem₂ (lctNodesBase b) t₂.rootId OFF_PPAR = 0)
    (hev_rev : t₂.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
      (t₁.evalInorder (revFlag mem₁ (lctNodesBase b)) false).reverse)
    (hlast₁ : (t₁.evalInorder (revFlag mem₁ (lctNodesBase b)) false).getLast? = some x)
    (hrest_eq : ∀ s ∈ rest, nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false) :
    let seq := t₁.evalInorder (revFlag mem₁ (lctNodesBase b)) false
    let par₁ := lctAuxParent mem₁ (lctNodesBase b) (lctCap n)
    let par₂ := lctAuxParent mem₂ (lctNodesBase b) (lctCap n)
    seq.Nodup ∧
    seq ≠ [] ∧
    (∀ u, u ∉ seq → par₂ u = par₁ u) ∧
    par₁ 0 = 0 ∧
    par₂ 0 = 0 ∧
    (∀ hpos : seq.length > 0, par₁ (seq[0]'hpos) = 0) ∧
    (∀ i (hi : i + 1 < seq.length), par₁ seq[i + 1] = seq[i]) ∧
    (∀ i (hi : i + 1 < seq.length), par₂ seq[i] = seq[i + 1]) ∧
    par₂ x = 0 := by
  intro seq par₁ par₂
  have hne : seq ≠ [] := fun hn => by simp [seq, hn] at hlast₁
  have hnd_all₁ : ((t₁ :: rest).flatMap AuxTree.toList).Nodup :=
    hsf₁.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hnd_t1 : t₁.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all₁ (by simp)
  have hseq_nd : seq.Nodup := (t₁.evalInorder_perm (revFlag mem₁ (lctNodesBase b)) false).nodup_iff.2 hnd_t1
  have hseq'_nd : seq.reverse.Nodup := List.nodup_reverse.2 hseq_nd
  have hp0_1 : par₁ 0 = 0 := lctAuxParent_zero_of_trees hsf₁ hpp₁_le
  have hp0_2 : par₂ 0 = 0 := lctAuxParent_zero_of_trees hsf₂ hpp₂_le
  have hout : ∀ u, u ∉ seq → par₂ u = par₁ u := by
    intro u hu
    dsimp only [par₁, par₂]
    rw [lctAuxParent_mem_iff_of_trees hsf₂ hpp₂_le u, lctAuxParent_mem_iff_of_trees hsf₁ hpp₁_le u]
    have hu2 : u ∉ t₂.evalInorder (revFlag mem₂ (lctNodesBase b)) false := by
      rw [hev_rev, List.mem_reverse]; exact hu
    have hrest_find :
        rest.findSome? (fun s =>
          let sq := s.evalInorder (revFlag mem₂ (lctNodesBase b)) false
          if u ∈ sq then some (listParentFrom (nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR) sq u) else none) =
        rest.findSome? (fun s =>
          let sq := s.evalInorder (revFlag mem₁ (lctNodesBase b)) false
          if u ∈ sq then some (listParentFrom (nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR) sq u) else none) := by
      apply findSome?_congr_left
      intro s hs
      rcases hrest_eq s hs with ⟨hp_s, hev_s⟩
      simp only [hp_s, hev_s]
    simp only [List.findSome?_cons, hu2, ↓reduceIte, hrest_find]
    have hu1 : u ∉ t₁.evalInorder (revFlag mem₁ (lctNodesBase b)) false := hu
    simp [hu1]
  have hpar1_idx : ∀ i (hi : i < seq.length),
      par₁ seq[i] = if i = 0 then 0 else seq[i - 1]! := by
    intro i hi
    dsimp only [par₁]
    rw [lctAuxParent_mem_iff_of_trees hsf₁ hpp₁_le seq[i]]
    have hmem : seq[i] ∈ seq := List.getElem_mem hi
    simp only [List.findSome?_cons, seq, hmem, ↓reduceIte]
    rw [listParentFrom_getElem _ seq hseq_nd i hi, hpp_t1]
  have hpar2_idx : ∀ j (hj : j < seq.reverse.length),
      par₂ seq.reverse[j] = if j = 0 then 0 else seq.reverse[j - 1]! := by
    intro j hj
    dsimp only [par₂]
    rw [lctAuxParent_mem_iff_of_trees hsf₂ hpp₂_le seq.reverse[j]]
    have hmem : seq.reverse[j] ∈ t₂.evalInorder (revFlag mem₂ (lctNodesBase b)) false := by
      rw [hev_rev]; exact List.getElem_mem hj
    simp only [List.findSome?_cons, hmem, ↓reduceIte]
    rw [hev_rev, listParentFrom_getElem _ seq.reverse hseq'_nd j hj, hpp_t2]
  have hlen_pos : 0 < seq.length := List.length_pos_of_ne_nil hne
  refine ⟨hseq_nd, hne, hout, hp0_1, hp0_2, ?_, ?_, ?_, ?_⟩
  · intro _; simpa using hpar1_idx 0 hlen_pos
  · intro i hi
    have hi_succ : i + 1 < seq.length := hi
    simpa [Nat.succ_sub_one, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : i < seq.length)] using hpar1_idx (i + 1) hi_succ
  · intro i hi
    let j := seq.length - 1 - i
    have hj_lt : j < seq.reverse.length := by simp [j]; omega
    have hj_pos : j ≠ 0 := by omega
    have hrev_j : seq.reverse[j]'hj_lt = seq[i]'(by omega) := by
      rw [List.getElem_reverse]
      congr 1; omega
    have hrev_prev : seq.reverse[j - 1]! = seq[i + 1] := by
      have hj1_lt : j - 1 < seq.reverse.length := by simp [j]; omega
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj1_lt, List.getElem_reverse]
      simp only [Option.getD_some]
      congr 1; omega
    have hp := hpar2_idx j hj_lt
    simp only [hj_pos, ↓reduceIte, hrev_j, hrev_prev] at hp
    exact hp
  · have hlast_eq : seq[seq.length - 1]'(by omega) = x := by
      have hg : seq.getLast? = seq[seq.length - 1]? := List.getLast?_eq_getElem?
      rw [List.getElem?_eq_getElem (by omega : seq.length - 1 < seq.length), hlast₁] at hg
      exact Option.some.inj hg.symm
    have hj0_eq : seq.reverse[0]'(by simpa using hlen_pos) = x := by
      rw [List.getElem_reverse]
      simpa using hlast_eq
    simpa [hj0_eq] using hpar2_idx 0 (by simpa using hlen_pos)

theorem iterParent_eq_zero_of_exists {par : ℕ → ℕ} {cap u : ℕ}
    (hp0 : par 0 = 0) (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (_hu1 : 1 ≤ u) (hu2 : u ≤ cap) (hex : ∃ M, iterParent par M u = 0) :
    iterParent par cap u = 0 := by
  by_contra hne
  have hall_nz : ∀ k ≤ cap, iterParent par k u ≠ 0 := by
    intro k hk hkz
    have hzero : ∀ d, iterParent par (k + d) u = 0 := by
      intro d
      induction d with
      | zero => simpa using hkz
      | succ d ih => rw [← Nat.add_assoc, iterParent_succ_right, ih, hp0]
    exact hne (by simpa [show k + (cap - k) = cap by omega] using hzero (cap - k))
  have hall_maps : ∀ k ∈ Finset.range (cap + 1), iterParent par k u ∈ Finset.Icc 1 cap := by
    intro k hk
    have hk_le : k ≤ cap := by rw [Finset.mem_range] at hk; omega
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero (hall_nz k hk_le), iterParent_le_cap hp0 hle hu2 k⟩
  have hcard : (Finset.Icc 1 cap).card < (Finset.range (cap + 1)).card := by
    rw [Nat.card_Icc, Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hne_ab, heq_ab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hall_maps
  wlog hab : a < b generalizing a b
  · exact this b hb a ha hne_ab.symm heq_ab.symm (by omega)
  let d := b - a
  have hd_pos : 1 ≤ d := by omega
  have hcy : iterParent par d (iterParent par a u) = iterParent par a u := by
    rw [← iterParent_add, show a + d = b by omega, heq_ab]
  rcases hex with ⟨M, hM⟩
  have ha_le : a ≤ cap := by rw [Finset.mem_range] at ha; omega
  have hya_nz : iterParent par a u ≠ 0 := hall_nz a ha_le
  have hmul := iterParent_mul_cycle hcy (M + 1)
  have hbig : M ≤ a + (M + 1) * d := by
    have : M + 1 ≤ (M + 1) * d := Nat.le_mul_of_pos_right _ hd_pos
    omega
  have hzero_big : iterParent par (a + (M + 1) * d) u = 0 := by
    rw [show a + (M + 1) * d = M + (a + (M + 1) * d - M) by omega, iterParent_add, hM,
      iterParent_zero_fixed hp0]
  rw [iterParent_add, hmul] at hzero_big
  exact hya_nz hzero_big

theorem reroot_seq_zero_iff {par₁ par₂ : ℕ → ℕ} {seq : List ℕ} {x : ℕ}
    (hseq_ne : seq ≠ [])
    (hp0_1 : par₁ 0 = 0) (hp0_2 : par₂ 0 = 0)
    (hp_seq1_0 : ∀ hpos : seq.length > 0, par₁ (seq[0]'hpos) = 0)
    (hp_seq1_s : ∀ i (hi : i + 1 < seq.length), par₁ seq[i + 1] = seq[i])
    (hp_seq2_s : ∀ i (hi : i + 1 < seq.length), par₂ seq[i] = seq[i + 1])
    (hp_seq2_x : par₂ x = 0)
    (hx_last : seq[seq.length - 1]'(by have := List.length_pos_of_ne_nil hseq_ne; omega) = x) :
    (∀ u, u = 0 ∨ u ∈ seq → (par₁ u = 0 ∨ par₁ u ∈ seq) ∧ (par₂ u = 0 ∨ par₂ u ∈ seq)) ∧
    (∀ u ∈ seq, iterParent par₂ seq.length u = 0) := by
  have hclosed : ∀ u, u = 0 ∨ u ∈ seq → (par₁ u = 0 ∨ par₁ u ∈ seq) ∧ (par₂ u = 0 ∨ par₂ u ∈ seq) := by
    intro u hu
    rcases hu with rfl | hu
    · simp [hp0_1, hp0_2]
    · rcases List.getElem_of_mem hu with ⟨i, hi, rfl⟩
      constructor
      · cases i with
        | zero => left; exact hp_seq1_0 _
        | succ i' => right; rw [hp_seq1_s i' hi]; exact List.getElem_mem (by omega)
      · by_cases hil : i + 1 < seq.length
        · right; rw [hp_seq2_s i hil]; exact List.getElem_mem hil
        · have hi_last : i = seq.length - 1 := by omega
          subst hi_last; left; rw [hx_last]; exact hp_seq2_x
  have hreach_len : ∀ d i (hi : i < seq.length),
      seq.length - i ≤ d → iterParent par₂ d seq[i] = 0 := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
        intro i hi hd
        by_cases hil : i + 1 < seq.length
        · rw [iterParent, hp_seq2_s i hil]
          exact ih (i + 1) hil (by omega)
        · have hi_last : i = seq.length - 1 := by omega
          subst hi_last
          rw [iterParent, hx_last, hp_seq2_x, iterParent_zero_fixed hp0_2]
  refine ⟨hclosed, ?_⟩
  intro u hu
  rcases List.getElem_of_mem hu with ⟨i, hi, rfl⟩
  exact hreach_len seq.length i hi (Nat.sub_le _ _)

theorem reroot_repSize_eq_off_seq {par₁ par₂ : ℕ → ℕ} {seq : List ℕ}
    (hout : ∀ u, u ∉ seq → par₂ u = par₁ u)
    (hclosed : ∀ u, u = 0 ∨ u ∈ seq → (par₁ u = 0 ∨ par₁ u ∈ seq) ∧ (par₂ u = 0 ∨ par₂ u ∈ seq))
    {z : ℕ} (hz_nz : z ≠ 0) (hz_nin : z ∉ seq) :
    ∀ k u, iterParent par₂ k u = z ↔ iterParent par₁ k u = z := by
  have hstay1 : ∀ u, u = 0 ∨ u ∈ seq → ∀ k, iterParent par₁ k u = 0 ∨ iterParent par₁ k u ∈ seq := by
    intro u hu k
    induction k generalizing u with
    | zero => exact hu
    | succ k ih => rw [iterParent]; exact ih (par₁ u) (hclosed u hu).1
  have hstay2 : ∀ u, u = 0 ∨ u ∈ seq → ∀ k, iterParent par₂ k u = 0 ∨ iterParent par₂ k u ∈ seq := by
    intro u hu k
    induction k generalizing u with
    | zero => exact hu
    | succ k ih => rw [iterParent]; exact ih (par₂ u) (hclosed u hu).2
  intro k
  induction k with
  | zero => intro u; rfl
  | succ k ih =>
      intro u
      by_cases hu : u ∈ seq
      · have h1 : iterParent par₁ (k + 1) u ≠ z := by
          rcases hstay1 u (Or.inr hu) (k + 1) with h0 | hs
          · omega
          · intro heq; rw [heq] at hs; exact hz_nin hs
        have h2 : iterParent par₂ (k + 1) u ≠ z := by
          rcases hstay2 u (Or.inr hu) (k + 1) with h0 | hs
          · omega
          · intro heq; rw [heq] at hs; exact hz_nin hs
        simp [h1, h2]
      · rw [iterParent, iterParent, hout u hu]
        exact ih (par₁ u)

theorem reroot_rootAbove_congr_step {par₁ par₂ : ℕ → ℕ} {cap : ℕ}
    (hp0_1 : par₁ 0 = 0) (hp0_2 : par₂ 0 = 0)
    (hle₁ : ∀ x, 1 ≤ x → x ≤ cap → par₁ x ≤ cap)
    (hle₂ : ∀ x, 1 ≤ x → x ≤ cap → par₂ x ≤ cap)
    (hacyc₁ : ∀ u, 1 ≤ u → u ≤ cap → iterParent par₁ cap u = 0)
    (hacyc₂ : ∀ u, 1 ≤ u → u ≤ cap → iterParent par₂ cap u = 0)
    (hundir : ∀ a b, 1 ≤ a → a ≤ cap → 1 ≤ b → b ≤ cap →
      par₁ a = b → par₂ a = b ∨ par₂ b = a) :
    ∀ u, 1 ≤ u → u ≤ cap →
      rootAbove par₂ cap u = rootAbove par₂ cap (rootAbove par₁ cap u) := by
  have hk_step : ∀ k u, 1 ≤ u → u ≤ cap → iterParent par₁ k u ≠ 0 →
      rootAbove par₂ cap (iterParent par₁ k u) = rootAbove par₂ cap u := by
    intro k
    induction k with
    | zero => intro u _ _ _; rfl
    | succ k ih =>
        intro u hu1 hu2 hnz
        rw [iterParent_succ_right] at hnz ⊢
        have hx_le : iterParent par₁ k u ≤ cap := iterParent_le_cap hp0_1 hle₁ hu2 k
        have hx_nz : iterParent par₁ k u ≠ 0 := by
          intro hx0; rw [hx0, hp0_1] at hnz; exact hnz rfl
        have hx1 : 1 ≤ iterParent par₁ k u := Nat.pos_of_ne_zero hx_nz
        have hpy_nz : par₁ (iterParent par₁ k u) ≠ 0 := hnz
        have hpy_le : par₁ (iterParent par₁ k u) ≤ cap := hle₁ _ hx1 hx_le
        have hpy1 : 1 ≤ par₁ (iterParent par₁ k u) := Nat.pos_of_ne_zero hpy_nz
        have hstep_r : rootAbove par₂ cap (par₁ (iterParent par₁ k u)) =
            rootAbove par₂ cap (iterParent par₁ k u) := by
          rcases hundir (iterParent par₁ k u) (par₁ (iterParent par₁ k u)) hx1 hx_le hpy1 hpy_le rfl with
            h2a | h2b
          · rw [← h2a]
            exact rootAbove_step hp0_2 hle₂ hacyc₂ hx1 hx_le (by rw [h2a]; exact hpy_nz)
          · have hs := rootAbove_step hp0_2 hle₂ hacyc₂ hpy1 hpy_le (by rw [h2b]; exact hx_nz)
            rw [h2b] at hs
            exact hs.symm
        exact hstep_r.trans (ih u hu1 hu2 hx_nz)
  intro u hu1 hu2
  have hreach := rootAbove_reachesIn hle₁ hacyc₁ hu1 hu2
  simp only [reachesIn, hu1, hu2, and_self, decide_true, Bool.true_and, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at hreach
  rcases hreach with ⟨k, _, hk⟩
  have hrb := rootAbove_bounds hle₁ cap u hu1 hu2 (hacyc₁ u hu1 hu2)
  rw [← hk]
  exact (hk_step k u hu1 hu2 (by rw [hk]; omega)).symm

theorem list_filter_diff_length {α : Type*} (p q : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ (xs.filter q).length + (xs.filter (fun a => p a && !q a)).length := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      by_cases hp : p a = true <;> by_cases hq : q a = true <;>
        simp [hp, hq] <;> omega

theorem list_sum_ge_two_of_mem_ne {f : ℕ → ℕ} {xs : List ℕ} (hnd : xs.Nodup)
    {a b : ℕ} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    f a + f b ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at ha
  | cons y ys ih =>
      rcases List.nodup_cons.1 hnd with ⟨hny, hnd_ys⟩
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha_ys <;> rcases hb with rfl | hb_ys
      · exact absurd rfl hne
      · have hle : f b ≤ (ys.map f).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.2 ⟨b, hb_ys, rfl⟩)
        simp only [List.map_cons, List.sum_cons]
        omega
      · have hle : f a ≤ (ys.map f).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.2 ⟨a, ha_ys, rfl⟩)
        simp only [List.map_cons, List.sum_cons]
        omega
      · have ih' := ih hnd_ys ha_ys hb_ys
        simp only [List.map_cons, List.sum_cons]
        omega

theorem heavy_doubling_pow_bound (f : ℕ → ℕ) :
    ∀ K (S : List ℕ), S.Nodup →
      (∀ j ∈ S, j < K) →
      (∀ j ∈ S, 0 < j → 2 * f (j - 1) ≤ f j) →
      (∀ i, i + 1 < K → f i ≤ f (i + 1)) →
      0 < K → 1 ≤ f 0 →
      2 ^ (S.filter (fun x => x != 0)).length * f 0 ≤ f (K - 1) := by
  intro K
  induction K with
  | zero => intro _ _ _ _ _ hK _; omega
  | succ K' ih =>
      intro S hnd hlt hdbl hmono _ hf0
      cases K' with
      | zero =>
          have hnil : S.filter (fun x => x != 0) = [] := by
            rw [List.filter_eq_nil_iff]
            intro j hj
            have := hlt j hj
            simp only [bne_iff_ne, ne_eq, not_not]
            omega
          rw [hnil]
          simp
      | succ K'' =>
          let S' := S.filter (fun x => x != 0)
          have hS'_nd : S'.Nodup := hnd.filter _
          by_cases hmem : (K'' + 1) ∈ S'
          · let S'' := S'.erase (K'' + 1)
            have hS''_nd : S''.Nodup := hS'_nd.erase _
            have hlen : S'.length = S''.length + 1 := by
              have hc := List.length_erase_of_mem hmem
              have hpos : 0 < S'.length := List.length_pos_of_ne_nil (List.ne_nil_of_mem hmem)
              dsimp only [S''] at hc ⊢
              omega
            have hlt'' : ∀ j ∈ S'', j < K'' + 1 := by
              intro j hj
              have hmem' : j ∈ S' := List.mem_of_mem_erase hj
              have hne : j ≠ K'' + 1 := by
                intro heq
                subst heq
                exact hS'_nd.not_mem_erase hj
              have hj_s : j ∈ S := (List.mem_filter.1 hmem').1
              have hj_lt := hlt j hj_s
              omega
            have hdbl'' : ∀ j ∈ S'', 0 < j → 2 * f (j - 1) ≤ f j := by
              intro j hj hj0
              exact hdbl j (List.mem_filter.1 (List.mem_of_mem_erase hj)).1 hj0
            have hfilter'' : S''.filter (fun x => x != 0) = S'' := by
              rw [List.filter_eq_self]
              intro j hj
              have hj' : j ∈ S' := List.mem_of_mem_erase hj
              exact (List.mem_filter.1 hj').2
            have ih_k := ih S'' hS''_nd hlt'' hdbl'' (fun i hi => hmono i (by omega)) (by omega) hf0
            rw [hfilter''] at ih_k
            have hstep : 2 * f K'' ≤ f (K'' + 1) := by
              have hs := hdbl (K'' + 1) (List.mem_filter.1 hmem).1 (by omega)
              simpa using hs
            have hfin_eq : K'' + 1 + 1 - 1 = K'' + 1 := by omega
            change 2 ^ S'.length * f 0 ≤ f (K'' + 1 + 1 - 1)
            rw [hfin_eq, hlen, Nat.pow_succ]
            calc
              2 ^ S''.length * 2 * f 0 = 2 * (2 ^ S''.length * f 0) := by ring
              _ ≤ 2 * f K'' := Nat.mul_le_mul_left 2 ih_k
              _ ≤ f (K'' + 1) := hstep
          · have hlt' : ∀ j ∈ S', j < K'' + 1 := by
              intro j hj
              have hne : j ≠ K'' + 1 := fun heq => hmem (heq ▸ hj)
              have hj_lt := hlt j (List.mem_filter.1 hj).1
              omega
            have hdbl' : ∀ j ∈ S', 0 < j → 2 * f (j - 1) ≤ f j :=
              fun j hj hj0 => hdbl j (List.mem_filter.1 hj).1 hj0
            have hfilter' : S'.filter (fun x => x != 0) = S' := by
              rw [List.filter_eq_self]
              intro j hj
              exact (List.mem_filter.1 hj).2
            have ih_k := ih S' hS'_nd hlt' hdbl' (fun i hi => hmono i (by omega)) (by omega) hf0
            rw [hfilter'] at ih_k
            have hm : f K'' ≤ f (K'' + 1) := hmono K'' (by omega)
            simpa [S'] using le_trans ih_k hm

theorem reroot_heavy_length_bound (f : ℕ → ℕ) (K n : ℕ) (S : List ℕ)
    (hnd : S.Nodup) (hlt : ∀ j ∈ S, j < K)
    (hdbl : ∀ j ∈ S, 0 < j → 2 * f (j - 1) ≤ f j)
    (hmono : ∀ i, i + 1 < K → f i ≤ f (i + 1))
    (hf_bd : ∀ i < K, f i ≤ lctCap n)
    (hf0 : 1 ≤ f 0) :
    S.length ≤ Nat.log 2 (n + 2) + 2 := by
  by_cases hK : K = 0
  · subst hK
    have hnil : S = [] := List.eq_nil_iff_forall_not_mem.2 fun j hj => by
      have := hlt j hj; omega
    simp [hnil]
  have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
  have hpow := heavy_doubling_pow_bound f K S hnd hlt hdbl hmono hK_pos hf0
  have hcap_bd : f (K - 1) ≤ 2 * n := by
    simpa [lctCap] using hf_bd (K - 1) (by omega)
  have hpow_le : 2 ^ (S.filter (fun x => x != 0)).length ≤ 2 * n := by
    have : 2 ^ (S.filter (fun x => x != 0)).length ≤ 2 ^ (S.filter (fun x => x != 0)).length * f 0 :=
      Nat.le_mul_of_pos_right _ hf0
    omega
  have hlog_bd : (S.filter (fun x => x != 0)).length ≤ Nat.log 2 (n + 2) + 1 := by
    have hlt_pow : 2 ^ (S.filter (fun x => x != 0)).length < 2 ^ (Nat.log 2 (n + 2) + 2) := by
      have hlog_n := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)
      calc
        2 ^ (S.filter (fun x => x != 0)).length ≤ 2 * n := hpow_le
        _ < 2 * (n + 2) := by omega
        _ < 2 * 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.mul_lt_mul_of_pos_left hlog_n (by decide)
        _ = 2 ^ (Nat.log 2 (n + 2) + 2) := by rw [Nat.pow_succ]; ring
    have hlt_exp := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hlt_pow
    omega
  have hsplit_aux : ∀ xs : List ℕ,
      xs.length ≤ (xs.filter (fun x => x != 0)).length + (xs.filter (fun x => x == 0)).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons j js ih => by_cases hj0 : j = 0 <;> simp [hj0] <;> omega
  have hsplit := hsplit_aux S
  have hzero_le : (S.filter (fun x => x == 0)).length ≤ 1 := by
    by_cases h0 : 0 ∈ S
    · have hnd0 := hnd.filter (fun x => x == 0)
      have hmem0 : ∀ z ∈ S.filter (fun x => x == 0), z = 0 := fun z hz => by
        simpa [beq_iff_eq] using (List.mem_filter.1 hz).2
      cases hf : S.filter (fun x => x == 0) with
      | nil => simp
      | cons a tl =>
          have ha0 : a = 0 := hmem0 a (by rw [hf]; simp)
          subst ha0
          have htl_nil : tl = [] := List.eq_nil_iff_forall_not_mem.2 fun z hz => by
            have hz0 : z = 0 := hmem0 z (by rw [hf]; simp [hz])
            rw [hf] at hnd0
            exact (List.nodup_cons.1 hnd0).1 (hz0 ▸ hz)
          simp [htl_nil]
    · have hnil0 : S.filter (fun x => x == 0) = [] := List.filter_eq_nil_iff.2 fun z hz => by
        simp only [beq_iff_eq]
        intro heq; subst heq; exact h0 hz
      simp [hnil0]
  omega

end MinCostFlow.LinkCut.Prog
