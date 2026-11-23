module

public import MinCostFlow.LSF.Program.DecompGenLabel

/-!
# The boundary of the root pieces, from the batch numbers

A vertex is on the boundary when it lies in two different pieces. A non-root vertex `v` lies in
the piece named by its label, which also holds the parent of `v`, and in the batch pieces closed
at `v`. These are all the pieces that hold `v` (`mem_rootPieces_cases`), so `v` is on the
boundary exactly when at least one batch was closed at `v`. The root lies in the batch pieces
closed at the root and in the root bag, when the root bag is more than the root. So the root is
on the boundary when at least two batches were closed there, or one batch was closed and some
child of the root was merged into the root bag (`boundary_rootPieces`).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

variable {T : MGraph} {r : ℕ} {bidx nb : ℕ → ℕ}

/-- Every closed batch got some child. -/
lemma onlineRun_hit {α : Type*} (θ : ℝ) (f : α → ℝ) (bidx : α → ℕ) :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ f bidx nb cur xs nbF curF → ∀ j, nb ≤ j → j < nbF → ∃ x ∈ xs, bidx x = j := by
  intro xs
  induction xs with
  | nil =>
    intro nb cur nbF curF h j h1 h2
    obtain ⟨rfl, rfl⟩ := h
    omega
  | cons x xs ih =>
    intro nb cur nbF curF h j h1 h2
    obtain ⟨hx, h⟩ := h
    split_ifs at h with hc
    · by_cases hj : j = nb
      · exact ⟨x, List.mem_cons_self, hx.trans hj.symm⟩
      · obtain ⟨y, hy, hyj⟩ := ih _ _ _ _ h j (by omega) h2
        exact ⟨y, List.mem_cons_of_mem _ hy, hyj⟩
    · obtain ⟨y, hy, hyj⟩ := ih _ _ _ _ h j h1 h2
      exact ⟨y, List.mem_cons_of_mem _ hy, hyj⟩

lemma batch_nonempty {θ : ℝ} {ν s : ℕ → ℝ} {L : ℕ → List ℕ} (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u))
    {y : ℕ} (hy : y ∈ T.V) {b : ℕ} (hb : b < nb y) :
    ∃ c ∈ childSet T r y, bidx c = b := by
  obtain ⟨c, hc, hcb⟩ := onlineRun_hit θ s bidx _ _ _ _ _ (hrun y hy) b (Nat.zero_le _) hb
  exact ⟨c, ((hL y hy).2 c).mp hc, hcb⟩

lemma mem_bagSet_self (hT : IsRootedTree T r) {c : ℕ} (hc : c ∈ T.V) :
    c ∈ bagSet T r bidx nb c := by
  classical
  rw [bagSet, Finset.mem_filter]
  exact ⟨mem_subtree_iff.mpr ⟨hc, isAncestor_refl T r c⟩, merged_self hT bidx nb hc⟩

/-- A vertex lies in the part of one piece only. -/
lemma inPart_unique (hT : IsRootedTree T r) {yb yb' : ℕ × ℕ} {v : ℕ}
    (h : InPart T r bidx nb yb v) (h' : InPart T r bidx nb yb' v) : yb = yb' := by
  classical
  -- a closed child `c` above `v` cannot lie strictly inside a bag around `v`
  have hclosed : ∀ {a c y}, v ∈ bagSet T r bidx nb a → c ∈ childSet T r y →
      bidx c < nb y → IsAncestor T r a c → c ≠ a → IsAncestor T r c v → False := by
    intro a c y hva hc hlt hac hca hcv
    rw [bagSet, Finset.mem_filter] at hva
    have := hva.2 c hac hca hcv
    rw [(childSet_facts hT hc).2.2.1] at this
    omega
  obtain ⟨y, b⟩ := yb
  obtain ⟨y', b'⟩ := yb'
  rcases h with ⟨hlt, c, hc, hbc, hvc⟩ | ⟨hy, hbn, hvr, hvne⟩ <;>
    rcases h' with ⟨hlt', c', hc', hbc', hvc'⟩ | ⟨hy', hbn', hvr', hvne'⟩
  · dsimp only at hlt hc hbc hlt' hc' hbc'
    have hvV := (mem_subtree_iff.mp (bagSet_sub c hvc)).1
    have hcv := (mem_subtree_iff.mp (bagSet_sub c hvc)).2
    have hc'v := (mem_subtree_iff.mp (bagSet_sub c' hvc')).2
    have hcc : c = c' := by
      by_contra hne
      rcases isAncestor_total_on_ancestors hT hvV hcv hc'v with h1 | h1
      · exact hclosed hvc hc' (hbc' ▸ hlt') h1 (Ne.symm hne) hc'v
      · exact hclosed hvc' hc (hbc ▸ hlt) h1 hne hcv
    subst hcc
    rw [← (childSet_facts hT hc).2.2.1, ← (childSet_facts hT hc').2.2.1, ← hbc, ← hbc']
  · exfalso
    dsimp only at hlt hc hbc hy' hbn'
    have hcV := (childSet_facts hT hc).1
    exact hclosed hvr' hc (hbc ▸ hlt) (isAncestor_root hT hcV) (childSet_facts hT hc).2.1
      (mem_subtree_iff.mp (bagSet_sub c hvc)).2
  · exfalso
    dsimp only at hlt' hc' hbc' hy hbn
    have hcV := (childSet_facts hT hc').1
    exact hclosed hvr hc' (hbc' ▸ hlt') (isAncestor_root hT hcV) (childSet_facts hT hc').2.1
      (mem_subtree_iff.mp (bagSet_sub c' hvc')).2
  · dsimp only at hy hbn hy' hbn'
    rw [hy, hbn, hy', hbn']

lemma mem_rootPieces {𝒲r : Finset (Finset ℕ)} {Br P : Finset ℕ} :
    P ∈ rootPieces r 𝒲r Br ↔ P ∈ 𝒲r ∨ (P = Br ∧ Br ≠ {r}) := by
  classical
  unfold rootPieces
  split_ifs with h
  · exact ⟨Or.inl, fun h' => h'.elim id (fun h'' => absurd h h''.2)⟩
  · rw [Finset.mem_insert]
    exact ⟨fun h' => h'.elim (fun h'' => Or.inr ⟨h'', h⟩) Or.inl,
      fun h' => h'.elim Or.inr (fun h'' => Or.inl h''.1)⟩

/-- The root bag is more than the root exactly when some child of the root was merged. -/
lemma bagSet_root_ne (hT : IsRootedTree T r) :
    bagSet T r bidx nb r ≠ {r} ↔ ∃ c ∈ childSet T r r, bidx c = nb r := by
  classical
  constructor
  · intro hne
    have hr : r ∈ bagSet T r bidx nb r := mem_bagSet_self hT hT.2
    obtain ⟨x, hx, hxr⟩ : ∃ x ∈ bagSet T r bidx nb r, x ≠ r := by
      by_contra hno
      push_neg at hno
      exact hne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hr, hno⟩)
    rw [bagSet, Finset.mem_filter] at hx
    obtain ⟨c, ⟨hc, hxc⟩, _⟩ := mem_subtree_children_iff hT hT.2 hx.1 hxr
    exact ⟨c, mem_childSet.mpr hc,
      ((merged_child hT bidx nb hT.2 (mem_childSet.mpr hc) hxc).mp hx.2).1⟩
  · rintro ⟨c, hc, hbc⟩ h
    obtain ⟨hcV, hcr, -, -, -, -⟩ := childSet_facts hT hc
    have hcs : c ∈ subtree T r c := mem_subtree_iff.mpr ⟨hcV, isAncestor_refl T r c⟩
    have hcb : c ∈ bagSet T r bidx nb r := by
      rw [bagSet, Finset.mem_filter]
      refine ⟨Finset.sdiff_subset (subtree_child_subset hT (mem_childSet.mp hc) hcs), ?_⟩
      exact (merged_child hT bidx nb hT.2 hc hcs).mpr ⟨hbc, merged_self hT bidx nb hcV⟩
    rw [h, Finset.mem_singleton] at hcb
    exact hcr hcb

section root

variable {ν : ℕ → ℝ} {θ : ℝ} {L : ℕ → List ℕ} {s : ℕ → ℝ}

/-- The pieces at the root, from `progDecomp_char`. -/
lemma rootPieces_char (hT : IsRootedTree T r) (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u)) {P : Finset ℕ} :
    P ∈ rootPieces r (progDecomp ν θ L T.V.card r).1 (progDecomp ν θ L T.V.card r).2 ↔
      (∃ y ∈ T.V, ∃ b < nb y, P = batchPiece T r bidx nb y b) ∨
      (P = bagSet T r bidx nb r ∧ ∃ c ∈ childSet T r r, bidx c = nb r) := by
  have hroot_card : (subtree T r r).card ≤ T.V.card :=
    Finset.card_le_card (fun _ hx => (mem_subtree_iff.mp hx).1)
  obtain ⟨hD2, -, hD1⟩ := progDecomp_char hT ν θ hL s bidx nb hrun T.V.card r hT.2 hroot_card
  rw [mem_rootPieces, hD1, hD2, bagSet_root_ne hT]
  have hsub : ∀ y, y ∈ subtree T r r ↔ y ∈ T.V := fun y =>
    ⟨fun h => (mem_subtree_iff.mp h).1, fun h => mem_subtree_iff.mpr ⟨h, isAncestor_root hT h⟩⟩
  simp only [hsub]

/-- The piece named by the part of `x` is a root piece. -/
lemma inPart_mem_rootPieces (hT : IsRootedTree T r) (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u))
    {yb : ℕ × ℕ} {x : ℕ} (h : InPart T r bidx nb yb x) :
    pieceOfLab T r bidx nb yb ∈
      rootPieces r (progDecomp ν θ L T.V.card r).1 (progDecomp ν θ L T.V.card r).2 := by
  rw [rootPieces_char hT hL hrun]
  rcases h with ⟨hlt, c, hc, -, -⟩ | ⟨hy, hbn, hxb, hxne⟩
  · left
    refine ⟨yb.1, (childSet_facts hT hc).2.2.2.2.1, yb.2, hlt, ?_⟩
    rw [pieceOfLab, ite_eq_left hlt]
  · right
    have hnot : ¬ yb.2 < nb yb.1 := by rw [hy, hbn]; exact lt_irrefl _
    refine ⟨by rw [pieceOfLab, ite_eq_right hnot, hy], ?_⟩
    rw [← bagSet_root_ne hT]
    intro h
    rw [h, Finset.mem_singleton] at hxb
    exact hxne hxb

/-- The root pieces that hold a vertex `v`. -/
lemma mem_rootPieces_cases (hT : IsRootedTree T r) (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u))
    {P : Finset ℕ} {v : ℕ}
    (hP : P ∈ rootPieces r (progDecomp ν θ L T.V.card r).1 (progDecomp ν θ L T.V.card r).2)
    (hv : v ∈ P) :
    (∃ b < nb v, P = batchPiece T r bidx nb v b) ∨
      (∃ yb, InPart T r bidx nb yb v ∧ P = pieceOfLab T r bidx nb yb) ∨
      (v = r ∧ P = bagSet T r bidx nb r ∧ ∃ c ∈ childSet T r r, bidx c = nb r) := by
  classical
  rw [rootPieces_char hT hL hrun] at hP
  rcases hP with ⟨y, hyV, b, hb, rfl⟩ | ⟨rfl, hmc⟩
  · by_cases hvy : v = y
    · subst hvy; exact Or.inl ⟨b, hb, rfl⟩
    · right; left
      refine ⟨(y, b), ?_, by rw [pieceOfLab, ite_eq_left hb]⟩
      rw [batchPiece, Finset.mem_insert, Finset.mem_biUnion] at hv
      rcases hv with h | ⟨c, hc, hvc⟩
      · exact absurd h hvy
      · exact Or.inl ⟨hb, c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, hvc⟩
  · by_cases hvr : v = r
    · exact Or.inr (Or.inr ⟨hvr, rfl, hmc⟩)
    · right; left
      refine ⟨(r, nb r), Or.inr ⟨rfl, rfl, hv, hvr⟩, ?_⟩
      rw [pieceOfLab, ite_eq_right (lt_irrefl _)]

lemma bidx_le_of_run (hT : IsRootedTree T r) (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u)) :
    ∀ x ∈ T.V, x ≠ r → bidx x ≤ nb (parent T r x) := by
  intro x hxV hxr
  have hpV := parent_mem hT hxV
  have hxL : x ∈ L (parent T r x) := ((hL _ hpV).2 x).mpr (mem_childSet_parent hT hxV hxr)
  exact ((onlineRun_bounds θ s bidx _ _ _ _ _ (hrun _ hpV)).2 x hxL).2

lemma not_inPart_root (hT : IsRootedTree T r) (yb : ℕ × ℕ) : ¬ InPart T r bidx nb yb r := by
  rintro (⟨-, c, hc, -, hrc⟩ | ⟨-, -, -, hne⟩)
  · obtain ⟨hcV, hcr, -, -, -, -⟩ := childSet_facts hT hc
    exact hcr (isAncestor_antisymm hT hcV hT.2 (mem_subtree_iff.mp (bagSet_sub c hrc)).2
      (isAncestor_root hT hcV))
  · exact hne rfl

/-- The boundary of the root pieces, from the batch numbers. -/
theorem boundary_rootPieces (hT : IsRootedTree T r) (hL : IsChildLists T r L)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u))
    {lab : ℕ → ℕ × ℕ} (hlab : IsLabeling T r bidx nb lab) {v : ℕ} (hv : v ∈ T.V) :
    v ∈ boundary (rootPieces r (progDecomp ν θ L T.V.card r).1 (progDecomp ν θ L T.V.card r).2) ↔
      (v ≠ r ∧ 1 ≤ nb v) ∨
      (v = r ∧ (2 ≤ nb r ∨ (1 ≤ nb r ∧ ∃ c ∈ childSet T r r, bidx c = nb r))) := by
  classical
  have hle := bidx_le_of_run hT hL hrun
  have hbatch_mem : ∀ {y b}, y ∈ T.V → b < nb y → batchPiece T r bidx nb y b ∈
      rootPieces r (progDecomp ν θ L T.V.card r).1 (progDecomp ν θ L T.V.card r).2 :=
    fun hy hb => (rootPieces_char hT hL hrun).mpr (Or.inl ⟨_, hy, _, hb, rfl⟩)
  have hy_mem : ∀ y b, y ∈ batchPiece T r bidx nb y b := by
    intro y b; rw [batchPiece]; exact Finset.mem_insert_self _ _
  -- two batch pieces at `y` with different numbers differ
  have hbatch_ne : ∀ {y b b'}, y ∈ T.V → b < nb y → b' < nb y → b ≠ b' →
      batchPiece T r bidx nb y b ≠ batchPiece T r bidx nb y b' := by
    intro y b b' hy hb hb' hne heq
    obtain ⟨c, hc, hcb⟩ := batch_nonempty hL hrun hy hb
    obtain ⟨c', hc', hcb'⟩ := batch_nonempty hL hrun hy hb'
    have h1 : InPart T r bidx nb (y, b) c :=
      Or.inl ⟨hb, c, hc, hcb, mem_bagSet_self hT (childSet_facts hT hc).1⟩
    have h2 : InPart T r bidx nb (y, b') c' :=
      Or.inl ⟨hb', c', hc', hcb', mem_bagSet_self hT (childSet_facts hT hc').1⟩
    have := inPart_inj hT h1 h2 (by rw [pieceOfLab, pieceOfLab, ite_eq_left hb, ite_eq_left hb',
      heq])
    simp only [Prod.mk.injEq] at this
    exact hne this.2
  rw [mem_boundary_iff]
  constructor
  · rintro ⟨A, hA, B, hB, hne, hvA, hvB⟩
    have cA := mem_rootPieces_cases hT hL hrun hA hvA
    have cB := mem_rootPieces_cases hT hL hrun hB hvB
    by_cases hvr : v = r
    · subst hvr
      right
      refine ⟨rfl, ?_⟩
      rcases cA with ⟨b, hb, rfl⟩ | ⟨yb, hyb, -⟩ | ⟨-, rfl, hmc⟩
      · rcases cB with ⟨b', hb', rfl⟩ | ⟨yb, hyb, -⟩ | ⟨-, rfl, hmc⟩
        · left
          have : b ≠ b' := fun h => hne (by rw [h])
          omega
        · exact absurd hyb (not_inPart_root hT yb)
        · exact Or.inr ⟨by omega, hmc⟩
      · exact absurd hyb (not_inPart_root hT yb)
      · rcases cB with ⟨b', hb', rfl⟩ | ⟨yb, hyb, -⟩ | ⟨-, rfl, -⟩
        · exact Or.inr ⟨by omega, hmc⟩
        · exact absurd hyb (not_inPart_root hT yb)
        · exact absurd rfl hne
    · left
      refine ⟨hvr, ?_⟩
      by_contra h0
      have h0 : nb v = 0 := by omega
      rcases cA with ⟨b, hb, -⟩ | ⟨yb, hyb, rfl⟩ | ⟨h, -⟩
      · omega
      · rcases cB with ⟨b', hb', -⟩ | ⟨yb', hyb', rfl⟩ | ⟨h, -⟩
        · omega
        · exact hne (by rw [inPart_unique hT hyb hyb'])
        · exact hvr h
      · exact hvr h
  · rintro (⟨hvr, h1⟩ | ⟨rfl, h2 | ⟨h1, c, hc, hbc⟩⟩)
    · have hpart := inPart_lab hT hlab hle _ v rfl hv hvr
      obtain ⟨-, hvA, hpA⟩ := inPart_piece hT hpart
      refine ⟨_, inPart_mem_rootPieces hT hL hrun hpart, _, hbatch_mem hv (b := 0) (by omega),
        fun heq => ?_, hvA, hy_mem v 0⟩
      rw [heq] at hpA
      have hps := (mem_subtree_iff.mp (batchPiece_sub hT hv 0 hpA)).2
      exact parent_ne_self hT hv hvr (isAncestor_antisymm hT (parent_mem hT hv) hv
        (isAncestor_parent hT hv hvr) hps)
    · exact ⟨_, hbatch_mem hv (b := 0) (by omega), _, hbatch_mem hv (b := 1) (by omega),
        hbatch_ne hv (by omega) (by omega) (by omega), hy_mem v 0, hy_mem v 1⟩
    · obtain ⟨c0, hc0, hcb0⟩ := batch_nonempty hL hrun hv (b := 0) (by omega)
      have hcV := (childSet_facts hT hc).1
      have hcb : c ∈ bagSet T v bidx nb v := by
        classical
        have hcs : c ∈ subtree T v c := mem_subtree_iff.mpr ⟨hcV, isAncestor_refl T v c⟩
        rw [bagSet, Finset.mem_filter]
        refine ⟨Finset.sdiff_subset (subtree_child_subset hT (mem_childSet.mp hc) hcs), ?_⟩
        exact (merged_child hT bidx nb hT.2 hc hcs).mpr ⟨hbc, merged_self hT bidx nb hcV⟩
      refine ⟨_, hbatch_mem hv (b := 0) (by omega), bagSet T v bidx nb v,
        (rootPieces_char hT hL hrun).mpr (Or.inr ⟨rfl, c, hc, hbc⟩), fun heq => ?_,
        hy_mem v 0, mem_bagSet_self hT hv⟩
      have hA : InPart T v bidx nb (v, 0) c0 :=
        Or.inl ⟨show 0 < nb v by omega, c0, hc0, hcb0, mem_bagSet_self hT (childSet_facts hT hc0).1⟩
      have hB : InPart T v bidx nb (v, nb v) c :=
        Or.inr ⟨rfl, rfl, hcb, (childSet_facts hT hc).2.1⟩
      have := inPart_inj hT hA hB (by
        rw [pieceOfLab, pieceOfLab, ite_eq_left (show 0 < nb v by omega),
          ite_eq_right (lt_irrefl _), heq])
      simp only [Prod.mk.injEq] at this
      omega

end root

end MinCostFlow.LSF.Program.DecompGen
