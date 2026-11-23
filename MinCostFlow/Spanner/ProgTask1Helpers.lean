module

public import MinCostFlow.Spanner.ProgTask1

/-!
# Helper Lemmas and Invariants for `task1Module`

This module provides injectivity (`walkAt_inj`, `decomposeOutAt_inj`), congruence,
`PrepStaticState` / `CompsDoneUpTo` range preservation, `buildWitnessCoreCost` static upper
bounds, and the stage invariants used in `ProgTask1Steps` and `ProgTask1Proof`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. Injectivity, congruence, and preservation helpers -/

lemma walkAt_inj {mem : ℕ → ℕ} {a : ℕ} {P₁ P₂ : Walk}
    (h1 : WalkAt mem a P₁) (h2 : WalkAt mem a P₂) : P₁ = P₂ := by
  have hvlen : P₁.verts.length = P₂.verts.length := by
    have s1 := h1 0 (by simp [Walk.encode])
    have s2 := h2 0 (by simp [Walk.encode])
    simpa [Walk.encode] using s1.symm.trans s2
  have hv1 : ListAt mem (a + 1) P₁.verts := by
    intro i hi
    have hlt : i + 1 < P₁.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons]; omega
    have s := h1 (i + 1) hlt
    have g : P₁.encode[i + 1]'hlt = P₁.verts[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Walk.encode, List.getElem?_append_left hi])
    rw [g] at s
    rwa [show a + 1 + i = a + (i + 1) by omega]
  have hv2 : ListAt mem (a + 1) P₂.verts := by
    intro i hi
    have hlt : i + 1 < P₂.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons]; omega
    have s := h2 (i + 1) hlt
    have g : P₂.encode[i + 1]'hlt = P₂.verts[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Walk.encode, List.getElem?_append_left hi])
    rw [g] at s
    rwa [show a + 1 + i = a + (i + 1) by omega]
  have hv : P₁.verts = P₂.verts := listAt_inj hvlen hv1 hv2
  have helen : P₁.edges.length = P₂.edges.length := by
    have hlt1 : P₁.verts.length + 1 < P₁.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons, List.length_cons]; omega
    have hlt2 : P₁.verts.length + 1 < P₂.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons, List.length_cons, hvlen]; omega
    have s1 := h1 (P₁.verts.length + 1) hlt1
    have s2 := h2 (P₁.verts.length + 1) hlt2
    have g1 : P₁.encode[P₁.verts.length + 1]'hlt1 = P₁.edges.length := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt1]
      simp [Walk.encode])
    have g2 : P₂.encode[P₁.verts.length + 1]'hlt2 = P₂.edges.length := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt2]
      simp [Walk.encode, hvlen])
    rw [g1] at s1; rw [g2] at s2; exact s1.symm.trans s2
  have he1 : ListAt mem (a + 2 + P₁.verts.length) P₁.edges := by
    intro i hi
    have hlt : P₁.verts.length + i + 2 < P₁.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons, List.length_cons]; omega
    have s := h1 (P₁.verts.length + i + 2) hlt
    have g1 : P₁.encode[P₁.verts.length + i + 2]'hlt = P₁.edges[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Walk.encode, List.getElem?_append_right (by omega : P₁.verts.length ≤ P₁.verts.length + i + 1),
        show P₁.verts.length + i + 1 - P₁.verts.length = i + 1 by omega])
    rw [g1] at s
    rwa [show a + 2 + P₁.verts.length + i = a + (P₁.verts.length + i + 2) by omega]
  have he2 : ListAt mem (a + 2 + P₁.verts.length) P₂.edges := by
    intro i hi
    have hlt : P₁.verts.length + i + 2 < P₂.encode.length := by
      dsimp only [Walk.encode]; rw [List.length_append, List.length_cons, List.length_cons, hvlen]; omega
    have s := h2 (P₁.verts.length + i + 2) hlt
    have g2 : P₂.encode[P₁.verts.length + i + 2]'hlt = P₂.edges[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Walk.encode, hvlen, List.getElem?_append_right (by omega : P₂.verts.length ≤ P₂.verts.length + i + 1),
        show P₂.verts.length + i + 1 - P₂.verts.length = i + 1 by omega])
    rw [g2] at s
    rwa [show a + 2 + P₁.verts.length + i = a + (P₁.verts.length + i + 2) by omega]
  have he : P₁.edges = P₂.edges := listAt_inj helen he1 he2
  cases P₁; cases P₂; simp only at hv he; subst hv he; rfl

lemma decomposeOutAt_inj {mem : ℕ → ℕ} {a : ℕ}
    {ℓ₁ pn₁ pd₁ ℓ₂ pn₂ pd₂ : ℕ} {lvl₁ lvl₂ : List ℕ} {cs₁ cs₂ : List (ℕ × List ℕ)}
    (h1 : DecomposeOutAt mem a ℓ₁ pn₁ pd₁ lvl₁ cs₁)
    (h2 : DecomposeOutAt mem a ℓ₂ pn₂ pd₂ lvl₂ cs₂)
    (hll : lvl₁.length = lvl₂.length) :
    ℓ₁ = ℓ₂ ∧ pn₁ = pn₂ ∧ pd₁ = pd₂ ∧ lvl₁ = lvl₂ ∧ cs₁ = cs₂ := by
  have hℓ : ℓ₁ = ℓ₂ := by
    have s1 := h1 0 (by simp [Decompose.encode])
    have s2 := h2 0 (by simp [Decompose.encode])
    simpa [Decompose.encode] using s1.symm.trans s2
  have hpn : pn₁ = pn₂ := by
    have s1 := h1 1 (by simp [Decompose.encode])
    have s2 := h2 1 (by simp [Decompose.encode])
    simpa [Decompose.encode] using s1.symm.trans s2
  have hpd : pd₁ = pd₂ := by
    have s1 := h1 2 (by simp [Decompose.encode])
    have s2 := h2 2 (by simp [Decompose.encode])
    simpa [Decompose.encode] using s1.symm.trans s2
  have hlvl1 : ListAt mem (a + 3) lvl₁ := by
    intro i hi
    have hlt : i + 3 < (Decompose.encode ℓ₁ pn₁ pd₁ lvl₁ cs₁).length := by
      dsimp only [Decompose.encode]; simp; omega
    have s := h1 (i + 3) hlt
    have g : (Decompose.encode ℓ₁ pn₁ pd₁ lvl₁ cs₁)[i + 3]'hlt = lvl₁[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Decompose.encode, List.append_assoc, List.getElem?_append_left hi])
    rw [g] at s
    rwa [show a + 3 + i = a + (i + 3) by omega]
  have hlvl2 : ListAt mem (a + 3) lvl₂ := by
    intro i hi
    have hlt : i + 3 < (Decompose.encode ℓ₂ pn₂ pd₂ lvl₂ cs₂).length := by
      dsimp only [Decompose.encode]; simp; omega
    have s := h2 (i + 3) hlt
    have g : (Decompose.encode ℓ₂ pn₂ pd₂ lvl₂ cs₂)[i + 3]'hlt = lvl₂[i] := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hi]
      simp [Decompose.encode, List.append_assoc, List.getElem?_append_left hi])
    rw [g] at s
    rwa [show a + 3 + i = a + (i + 3) by omega]
  have hlvl : lvl₁ = lvl₂ := listAt_inj hll hlvl1 hlvl2
  have hclen : cs₁.length = cs₂.length := by
    have hlt1 : lvl₁.length + 3 < (Decompose.encode ℓ₁ pn₁ pd₁ lvl₁ cs₁).length := by
      simp [Decompose.encode]
    have hlt2 : lvl₁.length + 3 < (Decompose.encode ℓ₂ pn₂ pd₂ lvl₂ cs₂).length := by
      simp [Decompose.encode, hll]
    have s1 := h1 (lvl₁.length + 3) hlt1
    have s2 := h2 (lvl₁.length + 3) hlt2
    have g1 : (Decompose.encode ℓ₁ pn₁ pd₁ lvl₁ cs₁)[lvl₁.length + 3]'hlt1 = cs₁.length := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt1]
      simp [Decompose.encode, List.append_assoc])
    have g2 : (Decompose.encode ℓ₂ pn₂ pd₂ lvl₂ cs₂)[lvl₁.length + 3]'hlt2 = cs₂.length := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hlt2]
      simp [Decompose.encode, hll, List.append_assoc])
    rw [g1] at s1; rw [g2] at s2; exact s1.symm.trans s2
  have hf1 := listAt_decompose_flatMap h1 rfl
  have hf2 := listAt_decompose_flatMap h2 hll.symm
  have hcs := listAt_flatMap_compRecord_unique (a + 4 + lvl₁.length) cs₁ cs₂ hclen hf1 hf2
  exact ⟨hℓ, hpn, hpd, hlvl, hcs⟩

lemma length_congr_emb {J : Graph} {emb₁ emb₂ : ℕ → Walk}
    (h : ∀ e < J.m, emb₁ e = emb₂ e) : length J emb₁ = length J emb₂ := by
  unfold length
  exact Finset.fold_congr fun e he => by rw [h e (Finset.mem_range.mp he)]

lemma vcongNat_congr_emb {J H' : Graph} {emb₁ emb₂ : ℕ → Walk}
    (h : ∀ e < J.m, emb₁ e = emb₂ e) : vcongNat J H' emb₁ = vcongNat J H' emb₂ := by
  unfold vcongNat
  exact Finset.sup_congr rfl fun v _ => congrArg Finset.card
    (Finset.filter_congr fun e he => by simp [h e (Finset.mem_range.mp he)])

lemma prepStatic_and_comps_of_agree_range {p : PrepInput} {mem mem' : ℕ → ℕ} {w : ℕ}
    (hv : p.StaticValid mem w)
    (hs : PrepStaticState p mem mem) (hc : CompsDoneUpTo p mem p.rawComps.length)
    (hagree : ∀ x, p.h ≤ x → x < p.hEnd → mem' x = mem x) :
    PrepStaticState p mem' mem' ∧ CompsDoneUpTo p mem' p.rawComps.length := by
  have hsb := PrepInput.StaticValid.size_bounds hv
  have hblock_le : ∀ ci (hci : ci < p.rawComps.length),
      p.hBlocksStart ≤ p.cJSubPtr ci ∧
      p.cDegPtr ci + p.rawComps[ci].2.length ≤ p.hEnd := by
    intro ci hci
    set f : (ℕ × List ℕ) → ℕ := fun q => 2 + 3 * (p.cJSub q).m + q.2.length
    have hsplit : (List.map f (List.take ci p.rawComps)).sum + f p.rawComps[ci] ≤
        (List.map f p.rawComps).sum := by
      have htake1 : List.take (ci + 1) p.rawComps = List.take ci p.rawComps ++ [p.rawComps[ci]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hci]; rfl
      have hprefix : List.take (ci + 1) p.rawComps <+: p.rawComps := List.take_prefix _ _
      have hsum_eq : (List.map f (List.take (ci + 1) p.rawComps)).sum =
          (List.map f (List.take ci p.rawComps)).sum + f p.rawComps[ci] := by
        rw [htake1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      rw [← hsum_eq]
      exact (List.IsPrefix.map f hprefix).sublist.sum_le_sum (fun _ _ => Nat.zero_le _)
    have hcdeg_eq : p.cDegPtr ci + p.rawComps[ci].2.length =
        p.cJSubPtr ci + f p.rawComps[ci] := by
      unfold PrepInput.cDegPtr PrepInput.cJOrigPtr
      rw [List.getD_eq_getElem _ _ hci]
      dsimp only [f]; omega
    refine ⟨by unfold PrepInput.cJSubPtr; omega, ?_⟩
    rw [hcdeg_eq]
    unfold PrepInput.cJSubPtr PrepInput.hEnd
    change p.hBlocksStart + (List.map f (List.take ci p.rawComps)).sum + f p.rawComps[ci] ≤
      p.hBlocksStart + (List.map f p.rawComps).sum
    omega
  have haComps_lt : p.aComps + 7 * p.rawComps.length ≤ p.hBlocksStart := by
    unfold PrepInput.aComps PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead PrepInput.hBlocksStart
    omega
  have hBlocks_le_end : p.hBlocksStart ≤ p.hEnd := by unfold PrepInput.hEnd; omega
  have haNext_lt : p.aEdgeNext + p.J0_strip.m ≤ p.hBlocksStart := by
    unfold PrepInput.aEdgeNext PrepInput.aLvlHead PrepInput.hBlocksStart; omega
  have haJ0_lt : p.aJ0Out + p.j0Edges.length ≤ p.hBlocksStart := by
    unfold PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead PrepInput.hBlocksStart; omega
  have hp_lt_end : p.h + 7 < p.hEnd := by
    have : p.aLvlHead ≤ p.hEnd := by
      unfold PrepInput.aLvlHead PrepInput.hEnd PrepInput.hBlocksStart; omega
    unfold PrepInput.aLvlHead at this; omega
  rcases hs with ⟨_, hj0len, haJ0, hrlen, haComps, haLvl, haNext, haVC, haVL, hj0list, hchain⟩
  have hst' : PrepStaticState p mem' mem' := by
    refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hagree _ le_rfl (by omega)]; exact hj0len
    · rw [hagree _ (by omega) (by omega)]; exact haJ0
    · rw [hagree _ (by omega) (by omega)]; exact hrlen
    · rw [hagree _ (by omega) (by omega)]; exact haComps
    · rw [hagree _ (by omega) (by omega)]; exact haLvl
    · rw [hagree _ (by omega) (by omega)]; exact haNext
    · rw [hagree _ (by omega) (by omega)]; exact haVC
    · rw [hagree _ (by omega) (by omega)]; exact haVL
    · intro i hi
      have hp1 : p.h ≤ p.aJ0Out + i := by unfold PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead; omega
      rw [hagree _ hp1 (by omega)]; exact hj0list i hi
    · intro lvl hlvl
      have hhead_eq : mem' (p.aLvlHead + lvl) = mem (p.aLvlHead + lvl) := by
        have hp1 : p.h ≤ p.aLvlHead + lvl := by unfold PrepInput.aLvlHead; omega
        have hp2 : p.aLvlHead + lvl < p.aEdgeNext := by unfold PrepInput.aEdgeNext; omega
        exact hagree _ hp1 (by omega)
      rw [hhead_eq]
      refine chainAt_of_agree (hchain lvl hlvl) fun b hb => ?_
      unfold DecomposeOutput.edgesAt at hb
      have hb_lt := List.mem_range.mp (List.mem_filter.mp hb).1
      exact hagree _ (by unfold PrepInput.aEdgeNext PrepInput.aLvlHead; omega) (by omega)
  refine ⟨hst', fun k hk => ?_⟩
  have hck := hc k hk
  dsimp only at hck ⊢
  have ⟨hlo, hhi⟩ := hblock_le k hk
  have hp_c : p.h ≤ p.aComps := by unfold PrepInput.aComps PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead; omega
  have hget : p.rawComps[k]! = p.rawComps[k] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have hcj_props := comp_props_at hv.toValid_zeroTail hk
  rw [hget] at hcj_props
  rcases hck with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  refine ⟨by rw [hagree _ (by omega) (by omega)]; exact h0,
    by rw [hagree _ (by omega) (by omega)]; exact h1,
    by rw [hagree _ (by omega) (by omega)]; exact h2,
    by rw [hagree _ (by omega) (by omega)]; exact h3,
    by rw [hagree _ (by omega) (by omega)]; exact h4,
    by rw [hagree _ (by omega) (by omega)]; exact h5,
    by rw [hagree _ (by omega) (by omega)]; exact h6,
    ?_, ?_, ?_⟩
  · intro i hi
    have hlt_enc : (p.cJSub p.rawComps[k]!).encode.length = 2 + 2 * (p.cJSub p.rawComps[k]).m := by
      rw [hget]; simp [Graph.encode, Graph.m]; omega
    have hp1 : p.h ≤ p.cJSubPtr k + i := by
      have : p.h ≤ p.hBlocksStart := by unfold PrepInput.hBlocksStart; omega
      omega
    have hp2 : p.cJSubPtr k + i < p.hEnd := by
      have hlt_deg : p.cJSubPtr k + (2 + 2 * (p.cJSub p.rawComps[k]).m) ≤ p.cDegPtr k := by
        unfold PrepInput.cDegPtr PrepInput.cJOrigPtr
        rw [List.getD_eq_getElem _ _ hk]; omega
      omega
    rw [hagree _ hp1 hp2]; exact h7 i hi
  · intro i hi
    have hlt_o : (p.cJOrig p.rawComps[k]!).length = (p.cJSub p.rawComps[k]).m := by
      have h := (comp_edges_orig_spec hv.toValid_zeroTail hk).2.2.2
      simp only [hget] at h ⊢; exact h
    have hp1 : p.h ≤ p.cJOrigPtr k + i := by
      unfold PrepInput.cJOrigPtr
      have : p.h ≤ p.hBlocksStart := by unfold PrepInput.hBlocksStart; omega
      omega
    have hp2 : p.cJOrigPtr k + i < p.hEnd := by
      unfold PrepInput.cDegPtr at hhi; rw [List.getD_eq_getElem _ _ hk] at hhi; omega
    rw [hagree _ hp1 hp2]; exact h8 i hi
  · intro i hi
    have hlen_map : (List.map (p.cJSub p.rawComps[k]!).deg (List.range p.rawComps[k]!.2.length)).length =
        p.rawComps[k].2.length := by simp [hget]
    have hp1 : p.h ≤ p.cDegPtr k + i := by
      unfold PrepInput.cDegPtr PrepInput.cJOrigPtr
      have : p.h ≤ p.hBlocksStart := by unfold PrepInput.hBlocksStart; omega
      omega
    have hp2 : p.cDegPtr k + i < p.hEnd := by omega
    rw [hagree _ hp1 hp2]; exact h9 i hi

lemma prepStaticValid_of_agree_outside {p : PrepInput} {mem mem' : ℕ → ℕ} {w lo hi : ℕ}
    (hv : p.StaticValid mem w)
    (hlo_j0 : hi ≤ p.j0Addr) (hlo_nl : hi ≤ p.nlAddr) (hlo_dec : hi ≤ p.decAddr)
    (hagree : ∀ x, x < lo ∨ hi ≤ x → mem' x = mem x)
    (hjj_lo : p.jAddr + p.J.encode.length ≤ lo) :
    p.StaticValid mem' w := by
  rcases hv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _, h19, h20⟩
  refine ⟨h1, GraphAt.of_agree_below h2 hjj_lo (fun k hk => hagree k (Or.inl hk)), h3,
    fun i hi_j0 => by rw [hagree _ (Or.inr (by omega))]; exact h4 i hi_j0,
    h5,
    fun i hi_nl => by rw [hagree _ (Or.inr (by omega))]; exact h6 i hi_nl,
    fun i hi_dec => by rw [hagree _ (Or.inr (by omega))]; exact h7 i hi_dec,
    h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, trivial, h19, h20⟩

/-! ## 2. Cost helpers -/

private lemma rangeCost_congr' {f g : ℕ → ℕ} {n : ℕ}
    (hfg : ∀ i < n, f i = g i) : rangeCost f 0 n = rangeCost g 0 n := by
  induction n with
  | zero => simp [rangeCost]
  | succ k ih =>
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    have hpre : (List.map f (List.range k)).sum = (List.map g (List.range k)).sum := by
      simpa [rangeCost_zero_eq_range] using ih fun i hi => hfg i (Nat.lt_succ_of_lt hi)
    simp [hpre, hfg k (Nat.lt_succ_self k)]

private lemma rangeCost_add_le {f g h : ℕ → ℕ} {n : ℕ}
    (hle : ∀ i < n, f i ≤ g i + h i) :
    rangeCost f 0 n ≤ rangeCost g 0 n + rangeCost h 0 n := by
  induction n with
  | zero => simp [rangeCost]
  | succ k ih =>
    have ihk := ih fun i hi => hle i (Nat.lt_succ_of_lt hi)
    have hk := hle k (Nat.lt_succ_self k)
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    simp only [rangeCost_zero_eq_range] at ihk
    simp only [List.map_singleton, List.sum_singleton]
    omega

private lemma rangeCost_ceil_mul_le {n : ℕ} {K F : ℝ} {f : ℕ → ℝ}
    (hK : 0 ≤ K) (hf_nn : ∀ i < n, 0 ≤ f i) (hf_sum : (∑ i ∈ Finset.range n, f i) ≤ F) :
    rangeCost (fun i => Nat.ceil (K * f i)) 0 n ≤ n + Nat.ceil (K * F) := by
  have hreal : ∀ m, (∀ i < m, 0 ≤ f i) →
      (rangeCost (fun i => Nat.ceil (K * f i)) 0 m : ℝ) ≤
        (m : ℝ) + K * ∑ i ∈ Finset.range m, f i := by
    intro m hm_nn
    induction m with
    | zero => simp [rangeCost]
    | succ k ih =>
      have ihk := ih (fun i hi => hm_nn i (Nat.lt_succ_of_lt hi))
      rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton, Nat.cast_add]
      rw [← rangeCost_zero_eq_range, Finset.sum_range_succ, mul_add]
      have hfk : 0 ≤ K * f k := mul_nonneg hK (hm_nn k (Nat.lt_succ_self k))
      have hceil : (Nat.ceil (K * f k) : ℝ) ≤ K * f k + 1 := (Nat.ceil_lt_add_one hfk).le
      push_cast; linarith [ihk, hceil]
  have hceilF : K * (∑ i ∈ Finset.range n, f i) ≤ (Nat.ceil (K * F) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hf_sum hK) (Nat.le_ceil _)
  have htot : (rangeCost (fun i => Nat.ceil (K * f i)) 0 n : ℝ) ≤
      ((n + Nat.ceil (K * F) : ℕ) : ℝ) := by
    push_cast; linarith [hreal n hf_nn, hceilF]
  exact Nat.cast_le.mp htot

private lemma sum_range_cast_eq (g : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (g i : ℝ)) = (rangeCost g 0 n : ℝ) := by
  induction n with
  | zero => simp [rangeCost]
  | succ k ih =>
    rw [Finset.sum_range_succ, rangeCost_zero_eq_range, List.range_succ, List.map_append,
      List.sum_append, List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih,
      Nat.cast_add]

private lemma rangeCost_map_sum_eq {α : Type*} [Inhabited α] (l : List α) (f : α → ℕ) :
    rangeCost (fun i => f (l[i]!)) 0 l.length = (l.map f).sum := by
  induction l using List.reverseRecOn with
  | nil => simp [rangeCost]
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, rangeCost_zero_eq_range, List.range_succ,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← rangeCost_zero_eq_range]
    have hpre : rangeCost (fun i => f ((xs ++ [x])[i]!)) 0 xs.length =
        rangeCost (fun i => f (xs[i]!)) 0 xs.length := by
      refine rangeCost_congr' fun i hi => ?_
      have hi1 : i < (xs ++ [x]).length := by simp only [List.length_append]; omega
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some,
        List.getElem_append_left hi, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some]
    have hlast : (xs ++ [x])[xs.length]! = x := by
      have hi1 : xs.length < (xs ++ [x]).length := by simp
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some,
        List.getElem_append_right le_rfl]
      simp
    rw [hpre, ih, hlast]

lemma buildWitnessCoreCost_le_cap {inp : Task1Input} {impl : SpannerToolImpl}
    {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : wInp.prep.Valid mem w)
    (_hJ : wInp.prep.J = inp.J)
    (hJ0 : wInp.prep.J0_strip = stripLoops inp.J)
    (hdJ : wInp.dJInt ≤ Task1Input.dJCap impl inp.J)
    (hmw : wInp.mwInt impl.constructExpander ≤ Task1Input.mwCap impl inp.J)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    let m0 := (stripLoops inp.J).m
    let ce := impl.constructExpander
    let pds := impl.pathDS.params
    let dJ := Task1Input.dJCap impl inp.J
    let mw := Task1Input.mwCap impl inp.J
    let dW := WitnessCoreInput.dWInt ce
    let φ_min := impl.decompose.φ_lb m0
    buildWitnessCoreCost wInp ce pds ≤
      (350 + pds.K_bounds * (Nat.log 2 (dJ + m0 + 2) + 1) +
        pds.K_bounds * (Nat.log 2 (dW + mw + 2) + 1)) +
      (265 * m0 + 10 + (m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / φ_min)⌉₊)) +
      (307 * m0 + 119 * mw + 120) + 5 := by
  intro m0 ce pds dJ mw dW φ_min
  have hm0 : wInp.prep.J0_strip.m = m0 := congrArg Graph.m hJ0
  have hsb := PrepInput.size_bounds hv
  have hphase01 : phase01Cost wInp ce pds ≤
      350 + pds.K_bounds * (Nat.log 2 (dJ + m0 + 2) + 1) +
        pds.K_bounds * (Nat.log 2 (dW + mw + 2) + 1) := by
    unfold phase01Cost
    have h1 := Nat.log_mono_right (b := 2)
      (by omega : wInp.dJInt + wInp.prep.J0_strip.m + 2 ≤ dJ + m0 + 2)
    have h2 := Nat.log_mono_right (b := 2)
      (by have hmw' : wInp.mwInt ce ≤ mw := hmw; omega :
        WitnessCoreInput.dWInt ce + wInp.mwInt ce + 2 ≤ dW + mw + 2)
    have hm1 := Nat.mul_le_mul_left pds.K_bounds (Nat.add_le_add_right h1 1)
    have hm2 := Nat.mul_le_mul_left pds.K_bounds (Nat.add_le_add_right h2 1)
    omega
  have hphase3 : cePhase3Cost wInp ce ≤ 307 * m0 + 119 * mw + 120 := by
    unfold cePhase3Cost
    have hrc_le : wInp.prep.rawComps.length ≤ m0 := hm0 ▸ hsb.2.1
    have h109 : 109 * wInp.prep.rawComps.length ≤ 109 * m0 := Nat.mul_le_mul_left 109 hrc_le
    have h119 : 119 * wInp.mwInt ce ≤ 119 * mw := Nat.mul_le_mul_left 119 hmw
    rw [hm0]; omega
  have hloop : ceLoopCost wInp ce ≤
      265 * m0 + 10 + (m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / φ_min)⌉₊) := by
    unfold ceLoopCost
    set len := wInp.prep.rawComps.length
    have hlen_le : len ≤ m0 := hm0 ▸ hsb.2.1
    have hsplit : rangeCost (ceStepCost wInp ce) 0 len ≤
        rangeCost (fun ci => 34 * wInp.prep.rawComps[ci]!.2.length + 120) 0 len +
        rangeCost (fun ci => ⌈ce.K_ce *
          (↑wInp.prep.rawComps[ci]!.2.length + ↑(wInp.compWeights wInp.prep.rawComps[ci]!).sum)⌉₊)
          0 len := by
      refine rangeCost_add_le fun ci _ => ?_
      dsimp only [ceStepCost]; omega
    have hlin : rangeCost (fun ci => 34 * wInp.prep.rawComps[ci]!.2.length + 120) 0 len ≤
        256 * m0 := by
      have heq := rangeCost_map_sum_eq wInp.prep.rawComps (fun rc => 34 * rc.2.length + 120)
      have hmap : ∀ l : List (ℕ × List ℕ),
          (l.map fun rc => 34 * rc.2.length + 120).sum ≤
            34 * (l.map fun rc => 2 + rc.2.length).sum + 52 * l.length := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
      have hl4 := hsb.2.2.1
      have h52 := hmap wInp.prep.rawComps
      change rangeCost _ 0 wInp.prep.rawComps.length = _ at heq
      change rangeCost _ 0 wInp.prep.rawComps.length ≤ 256 * m0
      rw [heq]; omega
    have hceil : rangeCost (fun ci => ⌈ce.K_ce *
          (↑wInp.prep.rawComps[ci]!.2.length + ↑(wInp.compWeights wInp.prep.rawComps[ci]!).sum)⌉₊)
          0 len ≤
        m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / φ_min)⌉₊ := by
      let f : ℕ → ℝ := fun ci =>
        ↑wInp.prep.rawComps[ci]!.2.length + ↑(wInp.compWeights wInp.prep.rawComps[ci]!).sum
      have hf_nn : ∀ ci < len, 0 ≤ f ci := fun ci _ => by dsimp only [f]; positivity
      have hlen_sum_r : (∑ ci ∈ Finset.range len, (wInp.prep.rawComps[ci]!.2.length : ℝ)) ≤
          4 * (m0 : ℝ) := by
        have hnat : rangeCost (fun ci => wInp.prep.rawComps[ci]!.2.length) 0 len ≤ 4 * m0 := by
          change rangeCost (fun ci => wInp.prep.rawComps[ci]!.2.length) 0 wInp.prep.rawComps.length ≤ 4 * m0
          rw [rangeCost_map_sum_eq wInp.prep.rawComps (fun rc => rc.2.length)]
          have hle_2 : (wInp.prep.rawComps.map fun rc => rc.2.length).sum ≤
              (wInp.prep.rawComps.map fun rc => 2 + rc.2.length).sum := by
            induction wInp.prep.rawComps with
            | nil => simp
            | cons x xs ih => simp only [List.map_cons, List.sum_cons]; omega
          exact le_trans hle_2 (hm0 ▸ hsb.2.2.1)
        rw [sum_range_cast_eq]
        exact_mod_cast hnat
      have hcw_sum_r : (∑ ci ∈ Finset.range len, ((wInp.compWeights wInp.prep.rawComps[ci]!).sum : ℝ)) ≤
          2 * (m0 : ℝ) / φ_min := by
        have hnat := rangeCost_map_sum_eq wInp.prep.rawComps (fun rc => (wInp.compWeights rc).sum)
        rw [sum_range_cast_eq]
        change (rangeCost _ 0 wInp.prep.rawComps.length : ℝ) ≤ _
        rw [hnat]
        have hsc := sum_compWeights_le hv hφ_lb
        rwa [hm0] at hsc
      have hf_sum : (∑ ci ∈ Finset.range len, f ci) ≤ 4 * (m0 : ℝ) + 2 * (m0 : ℝ) / φ_min := by
        have hsep : (∑ ci ∈ Finset.range len, f ci) =
            (∑ ci ∈ Finset.range len, (wInp.prep.rawComps[ci]!.2.length : ℝ)) +
            (∑ ci ∈ Finset.range len, ((wInp.compWeights wInp.prep.rawComps[ci]!).sum : ℝ)) := by
          dsimp only [f]; exact Finset.sum_add_distrib
        rw [hsep]; exact add_le_add hlen_sum_r hcw_sum_r
      exact le_trans (rangeCost_ceil_mul_le ce.hK_ce hf_nn hf_sum) (by omega)
    omega
  unfold buildWitnessCoreCost
  omega

/-! ## 3. Shared stage invariants and word-width extraction -/

structure StatsInv (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) : Prop where
  hv : inp.Valid impl mem₀ w
  hr0 : st.regs 0 = inp.hAddr
  hr1 : st.regs 1 = inp.jAddr
  hr2 : st.regs 2 = inp.embJHAddr
  hr3 : st.regs 3 = inp.h
  hr4 : st.regs 4 = inp.H'.n
  hr5 : st.regs 5 = inp.h + 6
  hr6 : st.regs 6 = inp.j0Addr
  h_below : ∀ x < inp.h, st.mem x = mem₀ x
  h_hdr_zero : ∀ x, inp.h ≤ x → x < inp.h + 6 → st.mem x = 0
  h_zf : ZeroFrom st.mem inp.j0Addr
  hs0 : st.mem (inp.h + 6) = maxDeg inp.J
  hs1 : st.mem (inp.h + 6 + 1) = length inp.J inp.embJH
  hs2 : st.mem (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH

structure StripInv (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) : Prop where
  hv : inp.Valid impl mem₀ w
  hr0 : st.regs 0 = inp.hAddr
  hr1 : st.regs 1 = inp.jAddr
  hr2 : st.regs 2 = inp.embJHAddr
  hr3 : st.regs 3 = inp.h
  hr5 : st.regs 5 = inp.h + 6
  hr6 : st.regs 6 = inp.j0Addr
  hr8 : st.regs 8 = inp.nlAddr
  hr9 : st.regs 9 = (stripLoops inp.J).m
  h_below : ∀ x < inp.h, st.mem x = mem₀ x
  h_hdr_zero : ∀ x, inp.h ≤ x → x < inp.h + 6 → st.mem x = 0
  h_stats : st.mem (inp.h + 6) = maxDeg inp.J ∧
    st.mem (inp.h + 6 + 1) = length inp.J inp.embJH ∧
    st.mem (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH
  h_J0 : GraphAt st.mem inp.j0Addr (stripLoops inp.J)
  h_nl : ListAt st.mem inp.nlAddr (nonloopIndices inp.J)
  h_zf : ZeroFrom st.mem inp.decAddr

structure DecInvData (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) where
  hv : inp.Valid impl mem₀ w
  pInp : PrepInput
  hp_jAddr : pInp.jAddr = inp.jAddr
  hp_j0Addr : pInp.j0Addr = inp.j0Addr
  hp_nlAddr : pInp.nlAddr = inp.nlAddr
  hp_decAddr : pInp.decAddr = inp.decAddr
  hp_J : pInp.J = inp.J
  hp_cℓ : pInp.c_ℓ = impl.decompose.c_ℓ
  hp_valid : pInp.Valid st.mem w
  hp_h_ge : inp.decAddr ≤ pInp.h
  hp_h_le : pInp.h ≤ inp.prepHMax impl
  h_phi_lb : impl.decompose.φ_lb pInp.J0_strip.m ≤ (pInp.phiNum_dec : ℝ) / pInp.phiDen_dec
  h_phi_cap : pInp.phiDen_dec ≤ impl.decompose.maxPhiDen pInp.J0_strip.m
  hr1 : st.regs 1 = inp.jAddr
  hr3 : st.regs 3 = inp.h
  hr5 : st.regs 5 = inp.h + 6
  hr6 : st.regs 6 = inp.j0Addr
  hr8 : st.regs 8 = inp.nlAddr
  hr10 : st.regs 10 = inp.decAddr
  hr11 : st.regs 11 = pInp.h
  h_below : ∀ x < inp.h, st.mem x = mem₀ x
  h_hdr_zero : ∀ x, inp.h ≤ x → x < inp.h + 6 → st.mem x = 0
  h_stats : st.mem (inp.h + 6) = maxDeg inp.J ∧
    st.mem (inp.h + 6 + 1) = length inp.J inp.embJH ∧
    st.mem (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH

abbrev DecInv (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) : Prop :=
  Nonempty (DecInvData inp impl mem₀ w st)

structure PrepDoneInvData (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) where
  hv : inp.Valid impl mem₀ w
  wInp : WitnessCoreInput
  hw_H' : wInp.H' = inp.H'
  hw_emb : wInp.embJH = inp.embJH
  hw_stats : wInp.statsAddr = inp.h + 6
  hw_jAddr : wInp.prep.jAddr = inp.jAddr
  hw_j0Addr : wInp.prep.j0Addr = inp.j0Addr
  hw_nlAddr : wInp.prep.nlAddr = inp.nlAddr
  hw_decAddr : wInp.prep.decAddr = inp.decAddr
  hw_J : wInp.prep.J = inp.J
  hw_cℓ : wInp.prep.c_ℓ = impl.decompose.c_ℓ
  hw_valid : wInp.Valid impl.constructExpander impl.pathDS.params st.mem w
  hw_maxEnd : wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤ inp.maxHeapEnd impl
  h_static_state : PrepStaticState wInp.prep st.mem st.mem
  h_comps_done : CompsDoneUpTo wInp.prep st.mem wInp.prep.rawComps.length
  h_phi_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
    (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec
  h_phi_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m
  h_cost_le :
    let m0 := (stripLoops inp.J).m
    let ce := impl.constructExpander
    let pds := impl.pathDS.params
    buildWitnessCoreCost wInp ce pds ≤
      (350 + pds.K_bounds * (Nat.log 2 (Task1Input.dJCap impl inp.J + m0 + 2) + 1) +
        pds.K_bounds * (Nat.log 2 (WitnessCoreInput.dWInt ce + Task1Input.mwCap impl inp.J + 2) + 1)) +
      (265 * m0 + 10 + (m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0)⌉₊)) +
      (307 * m0 + 119 * Task1Input.mwCap impl inp.J + 120) + 5
  hr1 : st.regs 1 = inp.jAddr
  hr3 : st.regs 3 = inp.h
  hr5 : st.regs 5 = inp.h + 6
  hr6 : st.regs 6 = inp.j0Addr
  hr8 : st.regs 8 = inp.nlAddr
  hr10 : st.regs 10 = inp.decAddr
  hr11 : st.regs 11 = wInp.prep.h
  hr12 : st.regs 12 = wInp.h
  h_below : ∀ x < inp.h, st.mem x = mem₀ x
  h_hdr_zero : ∀ x, inp.h ≤ x → x < inp.h + 6 → st.mem x = 0

abbrev PrepDoneInv (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (st : State) : Prop :=
  Nonempty (PrepDoneInvData inp impl mem₀ w st)

lemma task1_word_bounds {inp : Task1Input} {impl : SpannerToolImpl}
    {mem₀ : ℕ → ℕ} {w : ℕ} (hv : inp.Valid impl mem₀ w) :
    1 < 2 ^ w ∧
    inp.hAddr < 2 ^ w ∧ inp.jAddr < 2 ^ w ∧ inp.embJHAddr < 2 ^ w ∧ inp.h < 2 ^ w ∧
    inp.H'.n < 2 ^ w ∧ inp.h + 6 < 2 ^ w ∧ inp.j0Addr < 2 ^ w ∧ inp.nlAddr < 2 ^ w ∧
    inp.nlAddr + inp.J.m < 2 ^ w ∧ inp.decAddr < 2 ^ w ∧
    inp.j0Addr + (stripLoops inp.J).encode.length ≤ inp.nlAddr ∧
    inp.h + 6 ≤ inp.j0Addr := by
  have hww := hv.2.2.2.2.2.2.2.2.2.2
  have hmw : inp.maxWordBound impl < 2 ^ w := hww.2.2.2.2.2.2
  have hmax_ge : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := le_max_left _ _
  have hc_ge : inp.coreHMax impl ≤ inp.maxHeapEnd impl := by
    dsimp only [Task1Input.maxHeapEnd]; omega
  have hp_ge : inp.prepHMax impl ≤ inp.coreHMax impl := by
    dsimp only [Task1Input.coreHMax]; omega
  have hd_ge : inp.decAddr ≤ inp.prepHMax impl := by
    dsimp only [Task1Input.prepHMax]; exact Nat.le_add_right _ _
  have hnl_dec : inp.nlAddr ≤ inp.decAddr := by
    unfold Task1Input.decAddr; exact Nat.le_add_right _ _
  have hnl_core : inp.nlAddr ≤ inp.coreHMax impl :=
    le_trans hnl_dec (le_trans hd_ge hp_ge)
  have hnl_max : inp.nlAddr + inp.J.m ≤ inp.maxHeapEnd impl := by
    dsimp only [Task1Input.maxHeapEnd]; omega
  have hj0_le : inp.j0Addr ≤ inp.nlAddr := by unfold Task1Input.nlAddr; omega
  have hj0_max : inp.j0Addr ≤ inp.maxHeapEnd impl :=
    le_trans (le_trans hj0_le hnl_core) hc_ge
  have hstats_le : inp.h + 6 ≤ inp.j0Addr := by unfold Task1Input.j0Addr; omega
  have hj_h := hv.2.2.2.2.2.2.2.2.1
  have hh_h := hv.2.2.2.2.2.2.2.1
  have hemb_h := hv.2.2.2.2.2.2.1.1
  have hH_n : inp.H'.n < 2 ^ w := by
    have := le_trans hj0_max (le_trans hmax_ge (Nat.le_of_lt hmw))
    unfold Task1Input.j0Addr at this; omega
  have hJ0_enc : (stripLoops inp.J).encode.length ≤ 2 + 2 * inp.J.m := by
    have hm := stripLoops_m_le inp.J
    simp [Graph.encode, Graph.m] at *
    omega
  have hj0_nl : inp.j0Addr + (stripLoops inp.J).encode.length ≤ inp.nlAddr := by
    unfold Task1Input.nlAddr; omega
  refine ⟨hww.1, ?_, ?_, ?_, ?_, hH_n, ?_, ?_, ?_, ?_, ?_, hj0_nl, hstats_le⟩ <;> omega

end MinCostFlow.Spanner
