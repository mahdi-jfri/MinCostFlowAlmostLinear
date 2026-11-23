module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

import MinCostFlow.DynSpanner.Correctness
import MinCostFlow.DynSpanner.Program.DynSpannerAmortInput
import MinCostFlow.DynSpanner.Program.DynSpannerInitCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-step heap-space bounds for the dynamic spanner (`DynSpannerSpaceStep`)

Bounds the per-step quantities of Algorithm 6 (`DynSpannerUpdateLoopDefs.lean`):
* edge and output counts per step (`runStep_G'_E_sub`, `runStep_D_card_le`,
  `runStep_reemb_card_le`, `runStep_UH_length_le`),
* the full-rebuild step space `dsStepZeroSpace_le_caps`, and
* the positive-level step space `dsStepPosSpaceAt_le_caps`.

All bounds are expressed in terms of `B = vCap + eCap + L + len + 2`,
`g = ⌈impl.γ_ℓ mMax⌉₊`, `W_len = ⌈lenBound (impl.γ_ℓ mMax) L⌉₊`, and `impl.cw`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

/-! ## Pure arithmetic and graph helpers -/

public section

lemma nat_le_ceil_of_cast_le {a : ℕ} {r : ℝ} (h : (a : ℝ) ≤ r) : a ≤ ⌈r⌉₊ := by
  exact_mod_cast h.trans (Nat.le_ceil r)

lemma one_le_ceil_gamma (impl : SparsifyImpl) (mMax : ℕ) :
    1 ≤ ⌈impl.γ_ℓ mMax⌉₊ :=
  nat_le_ceil_of_cast_le (by simpa using impl.hγ_ℓ mMax)

lemma one_le_ceil_lenBound (impl : SparsifyImpl) (mMax L : ℕ) :
    1 ≤ ⌈lenBound (impl.γ_ℓ mMax) L⌉₊ :=
  nat_le_ceil_of_cast_le (by simpa using one_le_lenBound (impl.hγ_ℓ mMax) L)

end

private lemma list_sum_map_le_mul {α : Type*} (l : List α) (f : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ l, f x ≤ K) : (l.map f).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    omega

private lemma two_pow_wordSize_succ_le_ds (c : ℕ) (input : List ℕ) :
    2 ^ (WordRAM.wordSize c input + 1) ≤
      2 * (2 * (input.length + input.foldr max 0 + 2)) ^ c := by
  unfold WordRAM.wordSize
  set X := input.length + input.foldr max 0 + 2
  have h1 : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  rw [pow_succ, mul_comm (2 ^ _) 2, mul_comm c, pow_mul]
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h1 c)

private lemma restrictUpdate_len_le_one (u : Update) (H : MGraph) (hds : isDelOrSplit u) :
    (restrictUpdate u H).length ≤ 1 := by
  cases u with
  | insert _ _ _ => cases hds
  | delete e => unfold restrictUpdate; dsimp only; split_ifs <;> simp
  | split v v' St Sh => simp [restrictUpdate]

private lemma restrictUpdate_E_sub (u : Update) (H : MGraph) (hds : isDelOrSplit u) :
    (H.applyBatch (restrictUpdate u H)).E ⊆ H.E := by
  cases u with
  | insert _ _ _ => cases hds
  | delete e =>
    unfold restrictUpdate; dsimp only
    split_ifs
    · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
      exact Finset.erase_subset e H.E
    · simp [MGraph.applyBatch]
  | split v v' St Sh =>
    simp [restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]

private lemma isWalk_of_subgraph {H₁ H₂ : MGraph} (hsub : H₂.IsSubgraph H₁)
    {u v : ℕ} {P : List (ℕ × Bool)} (hw : H₁.IsWalk u v P) : H₂.IsWalk u v P := by
  induction hw with
  | nil u => exact MGraph.IsWalk.nil u
  | @cons u v x P hx hsrc _ ih =>
    have hx₂ : x.1 ∈ H₂.E := hsub.2.1 hx
    have ⟨ht, hh⟩ := hsub.2.2 x.1 hx
    have hsrc' : H₂.src x = u := by
      cases x with
      | mk eid dir =>
        cases dir
        · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
          exact hh.symm.trans hsrc
        · simp only [MGraph.src, ↓reduceIte] at hsrc ⊢
          exact ht.symm.trans hsrc
    have hdst' : H₂.dst x = H₁.dst x := by
      cases x with
      | mk eid dir =>
        cases dir
        · simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte]; exact ht.symm
        · simp only [MGraph.dst, ↓reduceIte]; exact hh.symm
    exact MGraph.IsWalk.cons hx₂ hsrc' (hdst'.symm ▸ ih)

private lemma isEmbedding_of_subgraph {emb : Embedding} {J H₁ H₂ : MGraph}
    (hemb : emb.IsEmbedding J H₁) (hsub : H₂.IsSubgraph H₁) :
    emb.IsEmbedding J H₂ :=
  ⟨hemb.1.trans hsub.1, fun e he => isWalk_of_subgraph hsub (hemb.2 e he)⟩

private lemma length_le_comp_length_of_pos {emb₁ emb₂ : Embedding} {e : ℕ}
    (hpos : ∀ x ∈ emb₂ e, 1 ≤ (emb₁ x.1).length) :
    (emb₂ e).length ≤ (Embedding.comp emb₁ emb₂ e).length := by
  unfold Embedding.comp
  generalize emb₂ e = w at hpos ⊢
  induction w with
  | nil => simp
  | cons x rest ih =>
    rcases x with ⟨eid, dir⟩
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx : 1 ≤ (if dir = true then emb₁ eid else walkRev (emb₁ eid)).length := by
      cases dir
      · simp only [Bool.false_eq_true, ↓reduceIte, walkRev_length]
        exact hpos (eid, false) List.mem_cons_self
      · simp only [↓reduceIte]
        exact hpos (eid, true) List.mem_cons_self
    have hrest := ih fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    omega

private lemma walk_mem_E {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hw : G.IsWalk u v P) {x : ℕ × Bool} (hx : x ∈ P) : x.1 ∈ G.E := by
  induction hw with
  | nil _ => cases hx
  | cons he _ _ ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact he
    · exact ih hrest

private lemma mul_B2_gW_of_B {c B g W : ℕ} (hB2 : B ≤ B ^ 2) (hg : 1 ≤ g) (hW : 1 ≤ W) :
    c * B ≤ c * (B ^ 2 * g * W) := by
  have h1 : B ≤ B ^ 2 * g * W := by
    calc B ≤ B ^ 2 := hB2
      _ = B ^ 2 * 1 * 1 := by ring
      _ ≤ B ^ 2 * g * W := Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) hW
  exact Nat.mul_le_mul_left c h1

private lemma mul_B2_gW_of_B2 {c B g W : ℕ} (hg : 1 ≤ g) (hW : 1 ≤ W) :
    c * B ^ 2 ≤ c * (B ^ 2 * g * W) := by
  have h1 : B ^ 2 ≤ B ^ 2 * g * W := by
    calc B ^ 2 = B ^ 2 * 1 * 1 := by ring
      _ ≤ B ^ 2 * g * W := Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) hW
  exact Nat.mul_le_mul_left c h1

private lemma mul_B2_gW_of_BW {c B g W : ℕ} (hB2 : B ≤ B ^ 2) (hg : 1 ≤ g) :
    c * (B * W) ≤ c * (B ^ 2 * g * W) := by
  have h1 : B * W ≤ B ^ 2 * g * W := by
    calc B * W = B * 1 * W := by ring
      _ ≤ B ^ 2 * g * W := Nat.mul_le_mul_right W (Nat.mul_le_mul hB2 hg)
  exact Nat.mul_le_mul_left c h1

private lemma mul_B2_gW_of_Bg {c B g W : ℕ} (hB2 : B ≤ B ^ 2) (hW : 1 ≤ W) :
    c * B * g ≤ c * (B ^ 2 * g * W) := by
  calc c * B * g = c * (B * g * 1) := by ring
    _ ≤ c * (B ^ 2 * g * W) := Nat.mul_le_mul_left c
        (Nat.mul_le_mul (Nat.mul_le_mul_right g hB2) hW)

private lemma mul_B2_gW_of_BgW {c B g W : ℕ} (hB2 : B ≤ B ^ 2) :
    c * B * g * W ≤ c * (B ^ 2 * g * W) := by
  calc c * B * g * W = c * (B * g * W) := by ring
    _ ≤ c * (B ^ 2 * g * W) := Nat.mul_le_mul_left c
        (Nat.mul_le_mul_right W (Nat.mul_le_mul_right g hB2))

/-! ## Per-step output size bounds -/

public section

lemma runStep_G'_E_sub {G₀ : MGraph} {impl : SparsifyImpl} {mMax L q : ℕ}
    {us : List Update} {k : ℕ} {u : Update}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hk : us[k]? = some u) :
    ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).E ⊆ G₀.E := by
  have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
  have hInv := (runInv_all hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb impl mMax)
    hBV hds k (le_of_lt hklt)).1
  have hsub1 : (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.E ⊆ G₀.E := by
    rw [hInv.G_eq]
    exact (batch_delOrSplit_invariants (us.take k) G₀ hVG₀
      (batchIsValid_take us G₀ k hBV hds).1 (batchIsValid_take us G₀ k hBV hds).2.1).2.1
  have hu_ds : isDelOrSplit u := hds u (List.mem_of_getElem? hk)
  cases u with
  | insert _ _ _ => cases hu_ds
  | delete e => exact (Finset.erase_subset e _).trans hsub1
  | split _ _ _ _ => exact hsub1

lemma runStep_D_card_le {G₀ : MGraph} {impl : SparsifyImpl} {mMax L q : ℕ}
    {us : List Update} {k : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') :
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us k).D.card ≤ G₀.m := by
  unfold runStepOut
  cases hk : us[k]? with
  | none => simp
  | some u =>
    have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
    have hSpec := canonicalSparsify_spec_absorb impl mMax
    have hrec := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hklt).2 k (Nat.lt_succ_self k) u hk
    have hInv1 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hklt).1
    have hsubH : (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)).H.E ⊆ G₀.E :=
      hInv1.H_sub.2.1.trans (batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀
        (batchIsValid_take us G₀ (k + 1) hBV hds).1 (batchIsValid_take us G₀ (k + 1) hBV hds).2.1).2.1
    have hDsub := hrec.D_sub
    simp only [runStepOut, hk] at hDsub
    exact Finset.card_le_card (hDsub.trans hsubH)

lemma runStep_reemb_card_le {G₀ : MGraph} {impl : SparsifyImpl} {mMax L q : ℕ}
    {us : List Update} {k : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') :
    (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k).card ≤ G₀.m := by
  unfold runStepReembSet
  cases hk : us[k]? with
  | none => simp
  | some u =>
    have hG'sub := runStep_G'_E_sub (impl := impl) (mMax := mMax) (L := L) (q := q)
      hVG₀ hL hq hGm₀ hBV hds hk
    unfold stepReembSet
    dsimp only
    split_ifs
    · exact Finset.card_le_card hG'sub
    · exact Finset.card_le_card ((Finset.filter_subset _ _).trans hG'sub)

lemma runStep_UH_length_le {G₀ : MGraph} {impl : SparsifyImpl} {mMax L q : ℕ}
    {us : List Update} {k : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') :
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us k).UH.length ≤ 1 + 2 * G₀.m := by
  unfold runStepOut
  cases hk : us[k]? with
  | none => simp
  | some u =>
    have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
    have hSpec := canonicalSparsify_spec_absorb impl mMax
    have hInv0 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (le_of_lt hklt)).1
    have hInv1 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hklt).1
    have hu_ds : isDelOrSplit u := hds u (List.mem_of_getElem? hk)
    have hsub0 : (runState (L := L) G₀ q (canonicalSparsify impl) us k).H.E ⊆ G₀.E :=
      hInv0.H_sub.2.1.trans (batch_delOrSplit_invariants (us.take k) G₀ hVG₀
        (batchIsValid_take us G₀ k hBV hds).1 (batchIsValid_take us G₀ k hBV hds).2.1).2.1
    have hG'sub := runStep_G'_E_sub (impl := impl) (mMax := mMax) (L := L) (q := q)
      hVG₀ hL hq hGm₀ hBV hds hk
    have hpref := restrictUpdate_len_le_one u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H hu_ds
    have hmid_sub : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E ⊆ G₀.E :=
      (restrictUpdate_E_sub u _ hu_ds).trans hsub0
    have h1_eq : (step (runState (L := L) G₀ q (canonicalSparsify impl) us k) u
        (canonicalSparsify impl)).state =
        runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1) := by
      simp [runState, hk]
    have hHnew_sub : (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)).H.E ⊆ G₀.E :=
      hInv1.H_sub.2.1.trans (batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀
        (batchIsValid_take us G₀ (k + 1) hBV hds).1 (batchIsValid_take us G₀ (k + 1) hBV hds).2.1).2.1
    unfold step
    dsimp only
    by_cases hj0 : chooseLevel L (runState (L := L) G₀ q (canonicalSparsify impl) us k).q
        ((runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1) = 0
    · simp only [hj0, ↓reduceDIte, List.length_append, List.length_map, Finset.length_sort]
      have hdel : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
          (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E.card ≤ G₀.m :=
        Finset.card_le_card hmid_sub
      have hins_sub : (initAt ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u)
          L (runState (L := L) G₀ q (canonicalSparsify impl) us k).q
          ((runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1)
          (canonicalSparsify impl)).state.H.E ⊆ G₀.E := by
        have hV' : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).IsValid := by
          have htk := batchIsValid_take us G₀ (k + 1) hBV hds
          have htk_eq : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hk
          have hG'eq : (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u =
              G₀.applyBatch (us.take (k + 1)) := by
            rw [htk_eq, applyBatch_append, ← hInv0.G_eq]; rfl
          rw [hG'eq]
          exact (batch_delOrSplit_invariants _ G₀ hVG₀ htk.1 htk.2.1).1
        have hm' : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ≤ mMax :=
          (Finset.card_le_card hG'sub).trans hGm₀
        have hi := initAt_state_props (L := L) (q := (runState (L := L) G₀ q (canonicalSparsify impl) us k).q)
          (t := (runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1)
          hSpec hV' hm' (le_refl _)
        exact hi.2.2.2.2.2.2.1.2.1.trans hG'sub
      have hdel' : (((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
          (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E \
          (initAt ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u)
          L (runState (L := L) G₀ q (canonicalSparsify impl) us k).q
          ((runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1)
          (canonicalSparsify impl)).state.H.E).card ≤ G₀.m :=
        (Finset.card_le_card Finset.sdiff_subset).trans hdel
      have hins' : ((initAt ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u)
          L (runState (L := L) G₀ q (canonicalSparsify impl) us k).q
          ((runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1)
          (canonicalSparsify impl)).state.H.E \
          ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
          (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E).card ≤ G₀.m :=
        (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_le_card hins_sub)
      omega
    · simp only [hj0, ↓reduceDIte, List.length_append, List.length_map, Finset.length_sort]
      have hdel : ∀ S : Finset ℕ, (((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
          (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E \ S).card ≤ G₀.m :=
        fun _ => (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_le_card hmid_sub)
      have hHnew_eq : (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)).H.E =
          unionEdgesLt (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)).H_level (L + 1) :=
        hInv1.H_E
      have hHnew_lev : (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)).H_level =
          (step (runState (L := L) G₀ q (canonicalSparsify impl) us k) u (canonicalSparsify impl)).state.H_level := by
        rw [h1_eq]
      rw [hHnew_lev] at hHnew_eq
      unfold step at hHnew_eq
      simp only [hj0, ↓reduceDIte] at hHnew_eq
      refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add hpref (hdel _)) (?_ : _ ≤ G₀.m)) (by omega)
      refine (Finset.card_le_card Finset.sdiff_subset).trans ?_
      rw [← hHnew_eq]
      exact Finset.card_le_card hHnew_sub

/-! ## Step space bounds for `j = 0` and `0 < j` -/

lemma dsStepZeroSpace_le_caps {impl : SparsifyImpl} {mMax vCap eCap L len : ℕ}
    {G' H_old H_new : MGraph}
    (hGn : G'.n ≤ vCap) (hGm : G'.m ≤ eCap) (hHo : H_old.m ≤ eCap) (hHn : H_new.m ≤ eCap) :
    let B := vCap + eCap + L + len + 2
    let g := ⌈impl.γ_ℓ mMax⌉₊
    let W_len := ⌈lenBound (impl.γ_ℓ mMax) L⌉₊
    dsStepZeroSpace impl mMax vCap eCap G' H_old H_new len + 2 ≤
      2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len := by
  intro B g W_len
  have hB2 : 2 ≤ B := by omega
  have hg1 : 1 ≤ g := one_le_ceil_gamma impl mMax
  have hW1 : 1 ≤ W_len := one_le_ceil_lenBound impl mMax L
  have hB_B2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
  unfold dsStepZeroSpace dsInitCoreSpaceBound
  dsimp only
  set Gact := activeSubgraph G'
  set input := canonSparsifyInput Gact Gact idEmb
  have hact_n : Gact.n ≤ G'.n := activeSubgraph_n_le G'
  have hact_m : Gact.m = G'.m := rfl
  have hlen1 : idEmb.length Gact ≤ 1 := idEmb_length_le_one Gact
  have hX : input.length + input.foldr max 0 + 2 ≤ 18 * (vCap + 2 * eCap + 1) := by
    refine (canonSparsifyInput_size_le Gact Gact idEmb).trans (Nat.mul_le_mul_left 18 ?_)
    have : Gact.m * (idEmb.length Gact + 1) ≤ eCap * 2 := by
      rw [hact_m]; exact Nat.mul_le_mul hGm (by omega)
    omega
  have hpow : 2 ^ (WordRAM.wordSize impl.cw input + 1) ≤ 2 * (180 * B * W_len) ^ impl.cw := by
    refine (two_pow_wordSize_succ_le_ds impl.cw input).trans (Nat.mul_le_mul_left 2 ?_)
    apply Nat.pow_le_pow_left
    have h1 : 2 * (18 * (vCap + 2 * eCap + 1)) ≤ 180 * B := by omega
    have h2 : 180 * B ≤ 180 * B * W_len := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hgm1 : G'.m * (1 + 2 * g) + 9 * G'.m * (g + 1) ≤ 21 * B * g := by
    have h1 : G'.m * (1 + 2 * g) ≤ B * (3 * g) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 9 * G'.m * (g + 1) ≤ 9 * B * (2 * g) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 9 (by omega)) (by omega)
    linarith
  have h21 : 21 * B * g ≤ 21 * (B ^ 2 * g * W_len) := mul_B2_gW_of_Bg hB_B2 hW1
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hlin : 5 + 2 * len + 3 * H_old.m + 5 * H_new.m +
      (3 * G'.m + (8 + 3 * Gact.n + 11 * G'.m) + 2 + 3 * G'.m + dynGraphSize vCap eCap + eCap) + 2 ≤
      46 * B := by
    rw [hdg]; omega
  have h46 : 46 * B ≤ 46 * (B ^ 2 * g * W_len) := mul_B2_gW_of_B hB_B2 hg1 hW1
  have h400 : 400 * B ^ 2 * g * W_len = 400 * (B ^ 2 * g * W_len) := by ring
  linarith

end

/-- Pure arithmetic combination for `dsStepPosNonEmptyEnd`. -/
private lemma dsStepPosNonEmptyEnd_arith {B g W_len cw : ℕ}
    (hB2 : 2 ≤ B) (hB_B2 : B ≤ B ^ 2) (hg1 : 1 ≤ g) (hW1 : 1 ≤ W_len)
    {wpPtr lE mG nJ mJ vCap eCap mJt len lUH sumPi jmg sc reemb oldSum powT : ℕ}
    (hwpPtr : wpPtr ≤ 10 * B) (hlE : lE ≤ B) (hmG : mG ≤ B)
    (hnJ : nJ ≤ B) (hmJ : mJ ≤ B) (hv : vCap ≤ B) (he : eCap ≤ B) (hmJt : mJt ≤ B)
    (hlen : len ≤ B) (hlUH : lUH ≤ 3 * B) (hsumPi : sumPi ≤ B * W_len)
    (hjmg : jmg ≤ 3 * B * g) (hsc : sc ≤ 21 * B * g * W_len)
    (hreemb : reemb ≤ 43 * B * g * W_len) (hold : 2 * oldSum ≤ 4 * B ^ 2)
    (hpow : powT ≤ 2 * (180 * B * W_len) ^ cw) :
    wpPtr + lE + 14 * sumPi + 15 * lE + mG +
      8 + 3 * nJ + 11 * lE + 10 * sumPi +
      powT + 2 + 3 * mJ + (4 + 7 * vCap + 9 * eCap) + eCap + jmg +
      sc + eCap + 16 * lE + 14 * sumPi + 5 * reemb + 1 + 2 * oldSum +
      4 * mJt + 2 * sumPi + lE + len + 4 * lUH + 2 ≤
      2 * (180 * B * W_len) ^ cw + 400 * B ^ 2 * g * W_len := by
  have h96 : wpPtr + lE + 15 * lE + mG + 8 + 3 * nJ + 11 * lE + 2 + 3 * mJ +
      (4 + 7 * vCap + 9 * eCap) + eCap + eCap + 16 * lE + 1 + 4 * mJt + lE + len + 4 * lUH + 2 ≤
      96 * B + 17 := by
    linarith
  have h1 : 96 * B ≤ 96 * (B ^ 2 * g * W_len) := mul_B2_gW_of_B hB_B2 hg1 hW1
  have h17 : 17 ≤ 17 * (B ^ 2 * g * W_len) := by
    have hB1 : 1 ≤ B ^ 2 * g * W_len := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h2 : 40 * sumPi ≤ 40 * (B ^ 2 * g * W_len) :=
    (Nat.mul_le_mul_left 40 hsumPi).trans (mul_B2_gW_of_BW hB_B2 hg1)
  have h3 : jmg ≤ 3 * (B ^ 2 * g * W_len) := hjmg.trans (mul_B2_gW_of_Bg hB_B2 hW1)
  have h4 : sc ≤ 21 * (B ^ 2 * g * W_len) := hsc.trans (mul_B2_gW_of_BgW hB_B2)
  have h5 : 5 * reemb ≤ 215 * (B ^ 2 * g * W_len) := by
    have hr5 : 5 * reemb ≤ 215 * B * g * W_len := by
      calc 5 * reemb ≤ 5 * (43 * B * g * W_len) := Nat.mul_le_mul_left 5 hreemb
        _ = 215 * B * g * W_len := by ring
    exact hr5.trans (mul_B2_gW_of_BgW hB_B2)
  have h6 : 2 * oldSum ≤ 4 * (B ^ 2 * g * W_len) := hold.trans (mul_B2_gW_of_B2 hg1 hW1)
  have h400 : 400 * B ^ 2 * g * W_len = 400 * (B ^ 2 * g * W_len) := by ring
  linarith only [h96, h1, h17, h2, h3, h4, h5, h6, h400, hpow]

private lemma dsStepPosNonEmptyEnd_le_caps (m : StepPosModel) {mMax vCap eCap len : ℕ}
    (hSpec : SparsifySpec mMax (canonicalSparsifyParams m.impl mMax).absorbTime
      (canonicalSparsify m.impl))
    (hG'V : m.G'.IsValid) (hJV : m.J.IsValid)
    (hEmbG' : Embedding.IsEmbedding m.embJH m.J m.G')
    (hJn : m.J.n ≤ vCap) (hG'm_mMax : m.G'.m ≤ mMax)
    (hjle : m.j ≤ m.L) (hG'm : m.G'.m ≤ eCap)
    (hSprev_card : m.S_prev.card ≤ vCap) (holdSum : modelOldSum m ≤ (m.L + 1) * eCap)
    (hUH : m.res.UH.length ≤ 1 + 2 * eCap)
    (hpiLt_le : ∀ e ∈ m.G'.E, (m.piLt_mid e).length ≤ ⌈lenBound (m.impl.γ_ℓ mMax) m.L⌉₊)
    (hembJH_le : m.embJH.length m.J ≤ ⌈lenBound (m.impl.γ_ℓ mMax) m.L⌉₊ + 1) :
    let B := vCap + eCap + m.L + len + 2
    let g := ⌈m.impl.γ_ℓ mMax⌉₊
    let W_len := ⌈lenBound (m.impl.γ_ℓ mMax) m.L⌉₊
    dsStepPosNonEmptyEnd m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH m.E_aff.toList
      (5 + len + 4 * m.j + 2 + m.S_prev.card + m.G'.m + m.E_aff.card) m.G'.m (modelOldSum m) +
      len + 4 * m.res.UH.length + 2 ≤
      2 * (180 * B * W_len) ^ m.impl.cw + 400 * B ^ 2 * g * W_len := by
  intro B g W_len
  have hB2 : 2 ≤ B := by omega
  have hg1 : 1 ≤ g := one_le_ceil_gamma m.impl mMax
  have hW1 : 1 ≤ W_len := one_le_ceil_lenBound m.impl mMax m.L
  have hB_B2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
  have hEaff_card : m.E_aff.card ≤ eCap :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hG'm
  have hEaff_len : m.E_aff.toList.length ≤ eCap := by rw [Finset.length_toList]; exact hEaff_card
  have hJm : m.J.m ≤ eCap := hEaff_card
  have hJm_mMax : m.J.m ≤ mMax :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hG'm_mMax
  have hembJH_pos : ∀ e ∈ m.J.E, 1 ≤ (m.embJH e).length := fun e _ => by
    simp [StepPosModel.embJH, projWalk]; omega
  have hembJH_len_ge1 : m.J.E.Nonempty → 1 ≤ m.embJH.length m.J := fun ⟨e, he⟩ =>
    (hembJH_pos e he).trans (Finset.le_sup (f := fun x => (m.embJH x).length) he)
  have hSpOut := hSpec m.G' m.J m.embJH hG'V hJV hJm_mMax hembJH_len_ge1 hEmbG'
  set out := canonicalSparsify m.impl m.G' m.J m.embJH
  set outEmb : Embedding := fun e => shortcutWalk out.Jtilde (m.J.tail e) (out.emb e)
  have hJtilde_m : out.Jtilde.m ≤ eCap :=
    (Finset.card_le_card hSpOut.1.2.1).trans hJm
  have hcomp_le : ∀ e ∈ m.E_aff, (Embedding.comp m.embJH out.emb e).length ≤ g * (W_len + 1) :=
    fun e he => by
      have h1 : (Embedding.comp m.embJH out.emb e).length ≤
          (Embedding.comp m.embJH out.emb).length m.J :=
        Finset.le_sup (f := fun x => (Embedding.comp m.embJH out.emb x).length) he
      have h2 : ((Embedding.comp m.embJH out.emb e).length : ℝ) ≤
          m.impl.γ_ℓ mMax * (m.embJH.length m.J : ℝ) :=
        le_trans (Nat.cast_le.mpr h1) hSpOut.2.2.2.1
      have h3 : m.impl.γ_ℓ mMax * (m.embJH.length m.J : ℝ) ≤ (g : ℝ) * ((W_len + 1 : ℕ) : ℝ) :=
        mul_le_mul (Nat.le_ceil _) (by exact_mod_cast hembJH_le) (Nat.cast_nonneg _)
          (Nat.cast_nonneg _)
      have h4 : ((Embedding.comp m.embJH out.emb e).length : ℝ) ≤ ((g * (W_len + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul]; exact h2.trans h3
      exact_mod_cast h4
  have houtEmb_len : ∀ e ∈ m.E_aff, (out.emb e).length ≤ g * (W_len + 1) := fun e he => by
    have hwalk := hSpOut.2.1.2 e he
    have hpos : ∀ x ∈ out.emb e, 1 ≤ (m.embJH x.1).length := fun x hx =>
      hembJH_pos x.1 (hSpOut.1.2.1 (walk_mem_E hwalk hx))
    exact (length_le_comp_length_of_pos hpos).trans (hcomp_le e he)
  have hcompOut_le : ∀ e ∈ m.E_aff, (Embedding.comp m.embJH outEmb e).length ≤ g * (W_len + 1) :=
    fun e he =>
      (comp_sublist_of_sublist m.embJH outEmb out.emb
        (shortcutWalk_sublist out.Jtilde (out.emb e) (m.J.tail e))).length_le.trans (hcomp_le e he)
  have hlenSum : (m.E_aff.toList.map fun e => (m.piLt_mid e).length).sum ≤ B * W_len :=
    (list_sum_map_le_mul m.E_aff.toList _ W_len fun e he =>
      hpiLt_le e (Finset.filter_subset _ _ (Finset.mem_toList.mp he))).trans
      (Nat.mul_le_mul_right W_len (hEaff_len.trans (by omega)))
  have hpow : 2 ^ (WordRAM.wordSize m.impl.cw (canonSparsifyInput m.G' m.J m.embJH) + 1) ≤
      2 * (180 * B * W_len) ^ m.impl.cw := by
    refine (two_pow_wordSize_succ_le_ds m.impl.cw _).trans (Nat.mul_le_mul_left 2 ?_)
    apply Nat.pow_le_pow_left
    have hs := canonSparsifyInput_size_le m.G' m.J m.embJH
    have hJnB : m.J.n ≤ B := hJn.trans (by omega)
    have hm_emb : m.J.m * (m.embJH.length m.J + 1) ≤ B * (3 * W_len) :=
      Nat.mul_le_mul (hJm.trans (by omega)) (by omega)
    have hB_BW : B ≤ B * W_len := Nat.le_mul_of_pos_right B (by omega)
    have h1 : m.J.n + m.J.m * (m.embJH.length m.J + 1) + 1 ≤ 5 * B * W_len := by
      have e : 5 * B * W_len = B * W_len + B * (3 * W_len) + B * W_len := by ring
      omega
    have e2 : 2 * (18 * (5 * B * W_len)) = 180 * B * W_len := by ring
    omega
  have hsc : dsShortcutHeapSpace m.E_aff.toList out.emb ≤ 21 * B * g * W_len := by
    unfold dsShortcutHeapSpace
    have h1 : (m.E_aff.toList.map fun e => (out.emb e).length).sum ≤ B * (2 * g * W_len) := by
      refine (list_sum_map_le_mul m.E_aff.toList _ (2 * g * W_len) fun e he => ?_).trans
        (Nat.mul_le_mul_right _ (hEaff_len.trans (by omega)))
      have := houtEmb_len e (Finset.mem_toList.mp he)
      have hgW : g ≤ g * W_len := Nat.le_mul_of_pos_right g (by omega)
      nlinarith
    have hBe : m.E_aff.toList.length ≤ B * g * W_len :=
      (hEaff_len.trans (by omega : eCap ≤ B)).trans
        ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega)))
    linarith
  have hreemb : reembStageNeed m.piLt_mid m.embJH outEmb m.E_aff.toList ≤ 43 * B * g * W_len := by
    unfold reembStageNeed compHeapNeed compOutLen reembHeapNeed
    have hgW : g ≤ g * W_len := Nat.le_mul_of_pos_right g (by omega)
    have hWgW : W_len ≤ g * W_len := Nat.le_mul_of_pos_left W_len (by omega)
    have h1gW : 1 ≤ g * W_len := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hc1 : (m.E_aff.toList.map fun e => 2 * ((outEmb e).flatMap (compPiece m.embJH)).length + 1).sum ≤
        B * (5 * g * W_len) := by
      refine (list_sum_map_le_mul m.E_aff.toList _ (5 * g * W_len) fun e he => ?_).trans
        (Nat.mul_le_mul_right _ (hEaff_len.trans (by omega)))
      have hco := hcompOut_le e (Finset.mem_toList.mp he)
      change 2 * (Embedding.comp m.embJH outEmb e).length + 1 ≤ 5 * g * W_len
      nlinarith
    have hr1 : (m.E_aff.toList.map fun e =>
        14 * (m.piLt_mid e).length + 4 * (Embedding.comp m.embJH outEmb e).length + 15).sum ≤
        B * (37 * g * W_len) := by
      refine (list_sum_map_le_mul m.E_aff.toList _ (37 * g * W_len) fun e he => ?_).trans
        (Nat.mul_le_mul_right _ (hEaff_len.trans (by omega)))
      have hco := hcompOut_le e (Finset.mem_toList.mp he)
      have hpi := hpiLt_le e (Finset.filter_subset _ _ (Finset.mem_toList.mp he))
      nlinarith
    have hBe : m.E_aff.toList.length ≤ B * g * W_len :=
      (hEaff_len.trans (by omega : eCap ≤ B)).trans
        ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega)))
    linarith
  have hJm_g : m.J.m * (1 + 2 * g) ≤ 3 * B * g := by
    calc m.J.m * (1 + 2 * g) ≤ B * (3 * g) := Nat.mul_le_mul (hJm.trans (by omega)) (by omega)
      _ = 3 * B * g := by ring
  have holdB2 : 2 * modelOldSum m ≤ 4 * B ^ 2 := by
    have h1 : (m.L + 1) * eCap ≤ (2 * B) * B := Nat.mul_le_mul (by omega) (by omega)
    calc 2 * modelOldSum m ≤ 2 * ((m.L + 1) * eCap) := Nat.mul_le_mul_left 2 holdSum
      _ ≤ 2 * ((2 * B) * B) := Nat.mul_le_mul_left 2 h1
      _ = 4 * B ^ 2 := by ring
  unfold dsStepPosNonEmptyEnd spOutBound
  dsimp only
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  rw [hdg]
  exact dsStepPosNonEmptyEnd_arith hB2 hB_B2 hg1 hW1
    (by omega) (hEaff_len.trans (by omega))
    (hG'm.trans (by omega)) (hJn.trans (by omega)) (hJm.trans (by omega))
    (by omega) (by omega) (hJtilde_m.trans (by omega)) (by omega)
    (hUH.trans (by omega)) hlenSum hJm_g hsc hreemb holdB2 hpow

public section

lemma dsStepPosSpaceAt_le_caps {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax L q vCap eCap k len : ℕ} {us : List Update} {u : Update}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hGm_e : G₀.m ≤ eCap) (hGn_v : G₀.n + batchSplitCount us ≤ vCap)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hk : us[k]? = some u) (hjpos : 0 < chooseLevel L q (k + 1)) :
    let B := vCap + eCap + L + len + 2
    let g := ⌈impl.γ_ℓ mMax⌉₊
    let W_len := ⌈lenBound (impl.γ_ℓ mMax) L⌉₊
    dsStepPosSpaceAt ⟨G₀, impl, L, q, k, us, u⟩ mMax vCap eCap len ≤
      2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len := by
  intro B g W_len
  set m : StepPosModel := ⟨G₀, impl, L, q, k, us, u⟩
  have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
  have hSpec := canonicalSparsify_spec_absorb impl mMax
  have hInv0 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (le_of_lt hklt)).1
  have hRec := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hklt).2 k (Nat.lt_succ_self k) u hk
  have hRsz := hRec.rebuild_sizes hjpos
  have hjle : m.j ≤ L := chooseLevel_le L q (k + 1)
  have hB2 : 2 ≤ B := by omega
  have hg1 : 1 ≤ g := one_le_ceil_gamma impl mMax
  have hW1 : 1 ≤ W_len := one_le_ceil_lenBound impl mMax L
  have hB_B2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
  have hG'm_G₀ : m.G'.m ≤ G₀.m := hRsz.2.2.2.2.2.1
  have hG'm : m.G'.m ≤ eCap := hG'm_G₀.trans hGm_e
  have hG'eq : m.G' = G₀.applyBatch (us.take (k + 1)) := by
    have htk : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hk
    show m.st.G.applyUpdate u = _
    rw [htk, applyBatch_append, ← hInv0.G_eq]; rfl
  have hG'n : m.G'.n ≤ vCap := by
    have htk := batchIsValid_take us G₀ (k + 1) hBV hds
    rw [hG'eq, n_applyBatch_of_delOrSplit _ _ htk.1 htk.2.1]
    have hsc : batchSplitCount (us.take (k + 1)) ≤ batchSplitCount us := by
      have h1 : us = us.take (k + 1) ++ us.drop (k + 1) := (List.take_append_drop _ _).symm
      conv_rhs => rw [h1]
      simp only [batchSplitCount, List.countP_append]; omega
    omega
  have hSprev_sub : m.S_prev ⊆ m.G'.V := by
    have htk0 := batchIsValid_take us G₀ k hBV hds
    have htk1 := batchIsValid_take us G₀ (k + 1) hBV hds
    have hu_ds : isDelOrSplit u := hds u (List.mem_of_getElem? hk)
    have hSubV_step : m.st.G.V ⊆ m.G'.V := by
      cases u with
      | insert _ _ _ => cases hu_ds
      | delete _ => exact Finset.Subset.refl _
      | split _ _ _ _ => exact Finset.subset_insert _ _
    refine Finset.union_subset ?_ ?_
    · rw [hInv0.S_level_eq]
      set r := lastRebuild q L (m.j - 1) k
      have hr_le : r ≤ k := lastRebuild_le q L (m.j - 1) k
      have hsplit : us.take k = us.take r ++ (us.take k).drop r := by
        have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le]
        rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
      have hBVk := htk0.1
      rw [hsplit, batchIsValid_append] at hBVk
      have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
        htk0.2.1 x (by rw [hsplit]; exact List.mem_append_left _ hx)
      have hds_d : ∀ x ∈ (us.take k).drop r, isDelOrSplit x := fun x hx =>
        htk0.2.1 x (by rw [hsplit]; exact List.mem_append_right _ hx)
      have hVGr := (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBVk.1 hds_r).1
      have hAT := allTouched_subset_V ((us.take k).drop r) (G₀.applyBatch (us.take r)) hVGr hBVk.2 hds_d
      rw [← applyBatch_append, ← hsplit, ← hInv0.G_eq] at hAT
      exact hAT.trans hSubV_step
    · have hAT1 := allTouched_subset_V [u] m.st.G
        (by rw [hInv0.G_eq]; exact (batch_delOrSplit_invariants _ G₀ hVG₀ htk0.1 htk0.2.1).1)
        (by
          have h1 : G₀.BatchIsValid (us.take k ++ [u]) := by
            rw [← take_succ_of_getElem? hk]; exact htk1.1
          rw [batchIsValid_append] at h1
          have h2 := h1.2
          rwa [← hInv0.G_eq] at h2)
        (by simp [hu_ds])
      simpa [allTouched, MGraph.applyBatch] using hAT1
  have hSprev_card : m.S_prev.card ≤ vCap := (Finset.card_le_card hSprev_sub).trans hG'n
  have holdSum : modelOldSum m ≤ (L + 1) * eCap := by
    unfold modelOldSum
    calc (∑ i : Fin (L + 1), if m.j ≤ i.1 then (m.st.H_level i).m else 0)
        ≤ ∑ _i : Fin (L + 1), eCap := Finset.sum_le_sum fun i _ => by
          split_ifs
          · have hsub : (m.st.H_level i).E ⊆ G₀.E :=
              (hInv0.H_level_sub i).2.1.trans (batch_delOrSplit_invariants (us.take k) G₀ hVG₀
                (batchIsValid_take us G₀ k hBV hds).1 (batchIsValid_take us G₀ k hBV hds).2.1).2.1
            exact (Finset.card_le_card hsub).trans hGm_e
          · exact Nat.zero_le _
      _ = (L + 1) * eCap := by simp
  have hUH : m.res.UH.length ≤ 1 + 2 * eCap := by
    have h1 := runStep_UH_length_le (impl := impl) (mMax := mMax) (L := L) (q := q) (k := k)
      hVG₀ hL hq hGm₀ hBV hds
    simp only [runStepOut, hk] at h1
    exact h1.trans (by omega)
  have hpiLt_le : ∀ e ∈ m.G'.E, (m.piLt_mid e).length ≤ W_len := fun e he => by
    have h1 := hRsz.2.2.1 e he
    have h2 : lenBound (impl.γ_ℓ mMax) (m.j - 1) ≤ lenBound (impl.γ_ℓ mMax) L :=
      lenBound_mono (impl.hγ_ℓ mMax) (by omega)
    exact nat_le_ceil_of_cast_le (h1.trans h2)
  have hAff : dsStepPosAffDelta m vCap eCap len ≤ 400 * B ^ 2 * g * W_len := by
    unfold dsStepPosAffDelta dsStepPosFullAffEnd
    have hsum : (∑ e ∈ m.G'.E, (14 * (m.piLt_mid e).length + 15)) ≤ m.G'.m * (14 * W_len + 15) := by
      rw [← smul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun e he => by have := hpiLt_le e he; omega
    have hsum2 : m.G'.m * (14 * W_len + 15) ≤ 29 * (B * W_len) := by
      have : m.G'.m * (14 * W_len + 15) ≤ B * (29 * W_len) := Nat.mul_le_mul (by omega) (by omega)
      linarith
    have h29 : 29 * (B * W_len) ≤ 29 * (B ^ 2 * g * W_len) := mul_B2_gW_of_BW hB_B2 hg1
    have h9 : 9 * B ≤ 9 * (B ^ 2 * g * W_len) := mul_B2_gW_of_B hB_B2 hg1 hW1
    have hlin : 0 + 5 + len + 4 * m.j + 2 + vCap + 3 * eCap ≤ 9 * B := by omega
    have h400 : 400 * B ^ 2 * g * W_len = 400 * (B ^ 2 * g * W_len) := by ring
    linarith
  have hEnd : dsStepPosEndDelta m mMax vCap eCap len ≤
      2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len := by
    unfold dsStepPosEndDelta
    dsimp only
    split_ifs with hne
    · have hEaff_ne : m.E_aff.Nonempty := Finset.card_pos.mp hne
      have hembJH_le : m.embJH.length m.J ≤ W_len + 1 := by
        have h1 : ((m.embJH.length m.J : ℕ) : ℝ) ≤ lenBound (impl.γ_ℓ mMax) (m.j - 1) + 1 :=
          (hRsz.2.2.2.2.2.2.2.2.2.2.2 hEaff_ne).1
        have h2 : lenBound (impl.γ_ℓ mMax) (m.j - 1) ≤ lenBound (impl.γ_ℓ mMax) L :=
          lenBound_mono (impl.hγ_ℓ mMax) (by omega)
        have h3 : (m.embJH.length m.J : ℝ) ≤ (W_len : ℝ) + 1 := by
          have := Nat.le_ceil (lenBound (impl.γ_ℓ mMax) L); linarith
        exact_mod_cast h3
      exact dsStepPosNonEmptyEnd_le_caps m hSpec
        hRsz.2.2.2.2.2.2.1 hRsz.2.2.2.2.2.2.2.2.1
        (isEmbedding_of_subgraph hRsz.2.2.2.2.2.2.2.2.2.1 hRsz.2.2.2.2.2.2.2.2.2.2.1)
        (hRsz.2.2.2.2.1.trans hG'n) (hG'm_G₀.trans hGm₀)
        hjle hG'm hSprev_card holdSum hUH hpiLt_le hembJH_le
    · have holdB2 : 2 * modelOldSum m ≤ 4 * B ^ 2 := by
        have h1 : (L + 1) * eCap ≤ (2 * B) * B := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      have hlin : (5 + len + 4 * m.j + 2 + m.S_prev.card + m.G'.m) + m.G'.m + eCap + 1 + len +
          4 * m.res.UH.length + 2 ≤ 24 * B := by omega
      have h24 : 24 * B ≤ 24 * (B ^ 2 * g * W_len) := mul_B2_gW_of_B hB_B2 hg1 hW1
      have h4 : 4 * B ^ 2 ≤ 4 * (B ^ 2 * g * W_len) := mul_B2_gW_of_B2 hg1 hW1
      have h400 : 400 * B ^ 2 * g * W_len = 400 * (B ^ 2 * g * W_len) := by ring
      omega
  unfold dsStepPosSpaceAt
  exact max_le hEnd (hAff.trans (Nat.le_add_left _ _))

end

end MinCostFlow.DynSpanner.Program
