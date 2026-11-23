module

public import MinCostFlow.LinkCut.ForestExpose
import Mathlib.Tactic

/-!
# Invariant and Potential Lemma for `revNode` (`reroot`)

This file proves `revNode_spec`: reversing an exposed root auxiliary tree (`ppar = 0`, ending at
a vertex) preserves `LctInvWith` with an explicit shifted `depth` function, conserves `sumTreePhi`
exactly, and increases `heavyCount` by at most `Nat.log 2 (2 * st.n + 1) + 1`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Shared arithmetic, size, list-chain, and reachability helpers -/

theorem nat_log_succ_of_two_mul_le {a b : ℕ} (ha : 1 ≤ a) (hle : 2 * a ≤ b) :
    Nat.log 2 a + 1 ≤ Nat.log 2 b := by
  have := AuxTree.nat_log_add_le_of_add_le ha ha (by omega : a + a ≤ b)
  omega

private theorem nodup_length_le_of_subset_local {β : Type*} [DecidableEq β]
    {l₁ l₂ : List β} (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a as ih =>
      rcases List.nodup_cons.mp hnd with ⟨ha_n, has_nd⟩
      have ha2 : a ∈ l₂ := hsub a (by simp)
      have hlen_erase : (l₂.erase a).length + 1 = l₂.length :=
        (List.length_erase_of_mem ha2).symm ▸ Nat.sub_add_cancel (List.length_pos_of_mem ha2)
      have hsub' : ∀ x ∈ as, x ∈ l₂.erase a := fun x hx =>
        List.mem_erase_of_ne (fun (h : x = a) => ha_n (h ▸ hx)) |>.mpr (hsub x (by simp [hx]))
      have := ih has_nd hsub'
      simp only [List.length_cons]
      omega

theorem active_length_le_two_mul {n : ℕ} {active : List ℕ}
    (hnd : active.Nodup) (hval : ∀ x ∈ active, isNode n x) :
    active.length ≤ 2 * n := by
  have hsub : ∀ x ∈ active, x ∈ List.range' 1 (2 * n) := fun x hx => by
    have hv := hval x hx
    simp only [isNode] at hv
    exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  simpa [List.length_range'] using nodup_length_le_of_subset_local hnd hsub

theorem reaches_eq_of_not_mem_closed {par₁ par₂ : ℕ → ℕ} {S : List ℕ}
    (hag : ∀ w ∉ S, par₁ w = par₂ w)
    (hcl₁ : ∀ w ∈ S, par₁ w = 0 ∨ par₁ w ∈ S)
    (hcl₂ : ∀ w ∈ S, par₂ w = 0 ∨ par₂ w ∈ S)
    {u : ℕ} (hu : u ∉ S) :
    ∀ k w, reaches par₁ k u w = reaches par₂ k u w := by
  have hS₁ : ∀ k w, w ∈ S → reaches par₁ k u w = false := by
    intro k
    induction k with
    | zero =>
        intro w hw
        simp [reaches, show w ≠ u from fun h => hu (h ▸ hw)]
    | succ k ih =>
        intro w hw
        have hwu : w ≠ u := fun h => hu (h ▸ hw)
        rcases hcl₁ w hw with hp0 | hpS
        · simp [reaches, hwu, hp0]
        · simp only [reaches, hwu, beq_iff_eq, ↓reduceIte]
          by_cases hz : par₁ w = 0
          · simp [hz]
          · simp [hz, ih (par₁ w) hpS]
  have hS₂ : ∀ k w, w ∈ S → reaches par₂ k u w = false := by
    intro k
    induction k with
    | zero =>
        intro w hw
        simp [reaches, show w ≠ u from fun h => hu (h ▸ hw)]
    | succ k ih =>
        intro w hw
        have hwu : w ≠ u := fun h => hu (h ▸ hw)
        rcases hcl₂ w hw with hp0 | hpS
        · simp [reaches, hwu, hp0]
        · simp only [reaches, hwu, beq_iff_eq, ↓reduceIte]
          by_cases hz : par₂ w = 0
          · simp [hz]
          · simp [hz, ih (par₂ w) hpS]
  intro k
  induction k with
  | zero => intro w; simp [reaches]
  | succ k ih =>
      intro w
      by_cases hw : w ∈ S
      · rw [hS₁ (k + 1) w hw, hS₂ (k + 1) w hw]
      · simp only [reaches]
        by_cases hwu : w == u
        · simp [hwu]
        · simp only [hwu, ↓reduceIte, Bool.false_eq_true]
          rw [hag w hw]
          by_cases hz : par₂ w == 0
          · simp [hz]
          · simp [hz, ih (par₂ w)]

theorem repSize_eq_of_not_mem_closed {active : List ℕ} {par₁ par₂ : ℕ → ℕ} {S : List ℕ}
    (hag : ∀ w ∉ S, par₁ w = par₂ w)
    (hcl₁ : ∀ w ∈ S, par₁ w = 0 ∨ par₁ w ∈ S)
    (hcl₂ : ∀ w ∈ S, par₂ w = 0 ∨ par₂ w ∈ S)
    {u : ℕ} (hu : u ∉ S) :
    repSize active par₁ u = repSize active par₂ u := by
  dsimp only [repSize]
  exact congrArg List.length
    (List.filter_congr (fun w _ => reaches_eq_of_not_mem_closed hag hcl₁ hcl₂ hu active.length w))

theorem listHead0_mem_of_ne_nil {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {t : AuxTree} (ht : t ≠ .leaf) :
    listHead0 (treeIds P s t) ∈ t.toList := by
  cases hids : treeIds P s t with
  | nil => exact absurd hids (treeIds_ne_nil ht)
  | cons a rest => exact (mem_treeIds_iff P s t a).mp (by simp [hids])

theorem mem_treeIds_of_listLast0 {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {t : AuxTree} (ht : t ≠ .leaf) :
    listLast0 (treeIds P s t) ∈ treeIds P s t := by
  cases hids : (treeIds P s t).reverse with
  | nil =>
      have hnil : treeIds P s t = [] := by
        have := congrArg List.reverse hids
        simpa using this
      exact absurd hnil (treeIds_ne_nil ht)
  | cons b rest =>
      rw [← listHead0_reverse_eq_listLast0, hids]
      have hb : b ∈ (treeIds P s t).reverse := by simp [hids]
      exact List.mem_reverse.mp hb

theorem isVertex_of_par_zero {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {z : ℕ}
    (hz : z ∈ trees.flatMap AuxTree.toList)
    (hp0 : inducedSubPar P st.splay trees z = 0) :
    isVertex st.n z := by
  have hnd := W.activeValid z hz
  simp only [isNode] at hnd
  by_cases hv : z ≤ st.n
  · exact ⟨hnd.1, hv⟩
  · have hes : isEdgeSlot st.n z := ⟨by omega, hnd.2⟩
    exact absurd hp0 (W.edgeParVertex z hz hes).1

/-! ### Chain helpers for `revNode_spec` -/

private def revIdx : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, z => if z = x then xs.length else revIdx xs z

private theorem revIdx_lt_length {xs : List ℕ} {z : ℕ} (hz : z ∈ xs) :
    revIdx xs z < xs.length := by
  induction xs with
  | nil => simp at hz
  | cons a rest ih =>
      simp only [revIdx, List.length_cons]
      by_cases hza : z = a
      · simp [hza]
      · simp only [hza, ↓reduceIte]
        exact Nat.lt_trans (ih (by simpa [hza] using hz)) (Nat.lt_succ_self _)

private theorem revIdx_lt_of_chainPred :
    ∀ (xs : List ℕ) (p x y : ℕ),
      xs.Nodup → p ∉ xs → x ∈ xs → y ∈ xs →
      chainPred p xs y = x →
      revIdx xs y < revIdx xs x
  | [], _, _, _, _, _, hx, _, _ => by simp at hx
  | a :: rest, p, x, y, hnd, hp_nin, hx, hy, hc => by
      rcases List.nodup_cons.mp hnd with ⟨ha_nin, hrest_nd⟩
      by_cases hya : y = a
      · subst hya
        simp only [chainPred] at hc
        subst hc
        exact absurd hx hp_nin
      · have hyr : y ∈ rest := by simpa [hya] using hy
        simp only [chainPred, hya, ↓reduceIte] at hc
        by_cases hxa : x = a
        · subst hxa
          simp only [revIdx, ↓reduceIte, hya]
          exact revIdx_lt_length hyr
        · have hxr : x ∈ rest := by simpa [hxa] using hx
          simp only [revIdx, hya, ↓reduceIte, hxa]
          exact revIdx_lt_of_chainPred rest a x y hrest_nd ha_nin hxr hyr hc

theorem reaches_chain_head_of_acyclic {active : List ℕ} {par depth : ℕ → ℕ}
    (hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ (l : List ℕ) (prev u : ℕ),
      l.Nodup → (∀ w ∈ l, w ≠ 0) → prev ∉ l →
      (∀ w ∈ l, w ∈ active) →
      (∀ w ∈ l, chainPred prev l w = par w) →
      (u = listHead0 l ∨ (prev ≠ 0 ∧ reaches par active.length u prev = true)) →
      ∀ z ∈ l, reaches par active.length u z = true
  | [], _, _, _, _, _, _, _, _, z, hz => by simp at hz
  | a :: rest, prev, u, hcnd, hnz, hp_nin, hsub, hagree, hu, z, hz => by
      rcases List.nodup_cons.mp hcnd with ⟨ha_nin, hrest_nd⟩
      have ha_act : a ∈ active := hsub a (by simp)
      have ha_nz : a ≠ 0 := hnz a (by simp)
      have h_u_a : reaches par active.length u a = true := by
        rcases hu with hu_eq | ⟨hp_nz, hprev_reach⟩
        · rw [hu_eq]; exact reaches_self par _ a
        · have hpa : par a = prev := by simpa [chainPred] using (hagree a (by simp)).symm
          exact (reaches_step_iff hnd hmem hdec ha_act).mpr
            (Or.inr ⟨by rw [hpa]; exact hp_nz, by rw [hpa]; exact hprev_reach⟩)
      rcases List.mem_cons.mp hz with rfl | hzr
      · exact h_u_a
      · refine reaches_chain_head_of_acyclic hnd hmem hdec rest a u hrest_nd
          (fun w hw => hnz w (by simp [hw])) ha_nin (fun w hw => hsub w (by simp [hw]))
          (fun w hw => by
            have hwa : w ≠ a := fun h => ha_nin (h ▸ hw)
            simpa [chainPred, hwa] using hagree w (by simp [hw]))
          (Or.inr ⟨ha_nz, h_u_a⟩) z hzr

private theorem chainPred_rev_last0_eq_zero {xs : List ℕ} (hne : xs ≠ []) :
    chainPred 0 xs.reverse (listLast0 xs) = 0 := by
  rw [← listHead0_reverse_eq_listLast0]
  cases hr : xs.reverse with
  | nil => exact absurd (by simpa using congrArg List.reverse hr) hne
  | cons b rest => simp [listHead0, chainPred]

private theorem chainPred_rev_eq_zero_iff {xs : List ℕ} (hz : 0 ∉ xs)
    {x : ℕ} (hx : x ∈ xs) :
    chainPred 0 xs.reverse x = 0 ↔ x = listLast0 xs := by
  rw [← listHead0_reverse_eq_listLast0]
  cases hr : xs.reverse with
  | nil =>
      have : xs = [] := by
        have := congrArg List.reverse hr
        simpa using this
      subst this; simp at hx
  | cons b rest =>
      simp only [listHead0]
      constructor
      · intro hc
        by_contra hxb
        have hx_in_r : x ∈ b :: rest := by rw [← hr]; exact List.mem_reverse.mpr hx
        have hxr : x ∈ rest := by simpa [hxb] using hx_in_r
        rcases chainPred_mem_or_prev (prev := b) (xs := rest) hxr with h1 | h1
        · simp only [chainPred, hxb, ↓reduceIte] at hc
          rw [hc] at h1
          have hb_xs : b ∈ xs := List.mem_reverse.mp (by simp [hr])
          exact hz (h1 ▸ hb_xs)
        · simp only [chainPred, hxb, ↓reduceIte] at hc
          rw [hc] at h1
          have h0_xs : 0 ∈ xs := List.mem_reverse.mp (by rw [hr]; simp [h1])
          exact hz h0_xs
      · intro rfl
        simp [chainPred]

private def ChainRev (par' : ℕ → ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => par' a = b ∧ ChainRev par' (b :: rest)

private theorem chainPred_rev_chainRev :
    ∀ (xs : List ℕ),
      xs.Nodup → (∀ z ∈ xs, z ≠ 0) →
      ChainRev (fun z => chainPred 0 xs.reverse z) xs
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hnd, hnz => by
      rcases List.nodup_cons.mp hnd with ⟨ha_nin, hbr_nd⟩
      have ha_in : a ∈ a :: b :: rest := by simp
      have hb_in : b ∈ a :: b :: rest := by simp
      have hba : b ≠ a := fun h => ha_nin (h ▸ by simp)
      have hz0 : (0 : ℕ) ∉ a :: b :: rest := fun hm => hnz 0 hm rfl
      have hpab : chainPred 0 (a :: b :: rest).reverse a = b :=
        (chainPred_reverse_iff hnd hz0 ha_in hb_in).mpr (by simp [chainPred, hba])
      refine ⟨hpab, ?_⟩
      have hsub := chainPred_rev_chainRev (b :: rest) hbr_nd (fun z hz => hnz z (by simp [hz]))
      have hagree : ∀ l : List ℕ, (∀ z ∈ l, z ∈ b :: rest) →
          ChainRev (fun z => chainPred 0 (b :: rest).reverse z) l →
          ChainRev (fun z => chainPred 0 (a :: b :: rest).reverse z) l := by
        intro l hl hc
        induction l with
        | nil => trivial
        | cons u us ihl =>
            cases us with
            | nil => trivial
            | cons v vs =>
                rcases hc with ⟨huv, hrest⟩
                refine ⟨?_, ihl (fun w hw => hl w (by simp [hw])) hrest⟩
                dsimp only
                rw [List.reverse_cons, chainPred_mem_append_left
                  (List.mem_reverse.mpr (hl u (by simp)))]
                exact huv
      exact hagree (b :: rest) (fun _ hz => hz) hsub

theorem filter_length_le_one_of_nodup {β : Type*} (q : β → Bool) :
    ∀ (l : List β), l.Nodup →
      (∀ a₁ ∈ l, ∀ a₂ ∈ l, q a₁ = true → q a₂ = true → a₁ = a₂) →
      (l.filter q).length ≤ 1
  | [], _, _ => by simp
  | a :: rest, hnd, huniq => by
      rcases List.nodup_cons.mp hnd with ⟨ha_nin, hrest_nd⟩
      rw [List.filter_cons]
      cases hqa : q a with
      | false =>
          simpa using filter_length_le_one_of_nodup q rest hrest_nd
            (fun x hx y hy => huniq x (by simp [hx]) y (by simp [hy]))
      | true =>
          have hnil : rest.filter q = [] := by
            rw [List.filter_eq_nil_iff]
            intro b hb hqb
            have hab := huniq a (by simp) b (by simp [hb]) hqa (by simpa using hqb)
            exact ha_nin (hab ▸ hb)
          simp [hnil]

theorem nodup_of_flatMap_nodup :
    ∀ (ts : List AuxTree), (ts.flatMap AuxTree.toList).Nodup → (∀ a ∈ ts, a ≠ .leaf) → ts.Nodup
  | [], _, _ => List.nodup_nil
  | a :: rest, hnd, hne => by
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      refine List.nodup_cons.mpr ⟨?_, nodup_of_flatMap_nodup rest hnd.2.1 (fun b hb => hne b (by simp [hb]))⟩
      intro ha_rest
      have hrt := AuxTree.rootId_mem (hne a (by simp))
      exact hnd.2.2 a.rootId hrt _ (List.mem_flatMap.mpr ⟨a, ha_rest, hrt⟩) rfl

theorem filter_or_length_le {β : Type*} (b₁ b₂ : β → Bool) :
    ∀ l : List β,
      (l.filter (fun x => b₁ x || b₂ x)).length ≤ (l.filter b₁).length + (l.filter b₂).length
  | [] => by simp
  | a :: rest => by
      have ih := filter_or_length_le b₁ b₂ rest
      rw [List.filter_cons, List.filter_cons, List.filter_cons]
      cases b₁ a <;> cases b₂ a <;> simp <;> omega

theorem filter_length_le_of_imp {β : Type*} (p₁ p₂ : β → Bool) :
    ∀ l : List β, (∀ x ∈ l, p₁ x = true → p₂ x = true) →
      (l.filter p₁).length ≤ (l.filter p₂).length
  | [], _ => by simp
  | a :: rest, himp => by
      have ih := filter_length_le_of_imp p₁ p₂ rest (fun x hx => himp x (by simp [hx]))
      rw [List.filter_cons, List.filter_cons]
      cases h1 : p₁ a <;> cases h2 : p₂ a
      · simp; exact ih
      · simp; omega
      · exact absurd (himp a (by simp) h1) (by simp [h2])
      · simp; omega

private theorem er_filter_chain_le_hasHeavy (er : List AuxTree) (key : AuxTree → ℕ)
    (p : AuxTree → Bool) (hasHeavy : ℕ → Bool)
    (hh_iff : ∀ u, hasHeavy u = er.any (fun a => (key a == u) && p a)) :
    ∀ xs : List ℕ,
      (∀ u ∈ xs, (er.filter (fun a => (key a == u) && p a)).length ≤ 1) →
      (er.filter (fun a => decide (key a ∈ xs) && p a)).length ≤ (xs.filter hasHeavy).length
  | [], _ => by simp
  | u :: rest, huniq => by
      have hsub : er.filter (fun a => decide (key a ∈ u :: rest) && p a) =
          er.filter (fun a => ((key a == u) && p a) || (decide (key a ∈ rest) && p a)) := by
        refine List.filter_congr (fun a _ => ?_)
        cases pa : p a <;> by_cases hku : key a = u <;> simp [hku]
      have hsplit := hsub ▸ filter_or_length_le
        (fun a => (key a == u) && p a) (fun a => decide (key a ∈ rest) && p a) er
      have ih := er_filter_chain_le_hasHeavy er key p hasHeavy hh_iff rest
        (fun w hw => huniq w (by simp [hw]))
      rw [List.filter_cons]
      cases hhu : hasHeavy u with
      | true =>
          have hu1 := huniq u (by simp)
          simp only [↓reduceIte, List.length_cons]
          omega
      | false =>
          have hnil : er.filter (fun a => (key a == u) && p a) = [] := by
            rw [List.filter_eq_nil_iff]
            intro a ha hqa
            have hny := hh_iff u ▸ hhu
            simp only [List.any_eq_false] at hny
            exact hny a ha (by simpa using hqa)
          rw [hnil, List.length_nil, Nat.zero_add] at hsplit
          exact Nat.le_trans hsplit ih

private theorem chainRev_hasHeavy_log_bound (par' : ℕ → ℕ) (hasHeavy : ℕ → Bool) (rep : ℕ → ℕ) :
    ∀ (ys : List ℕ) (x : ℕ),
      ChainRev par' (x :: ys) →
      (∀ u ∈ x :: ys, 1 ≤ rep u) →
      (∀ a ∈ x :: ys, ∀ b ∈ x :: ys, par' a = b →
        rep a ≤ rep b ∧ (hasHeavy b = true → 2 * rep a ≤ rep b)) →
      (ys.filter hasHeavy).length + Nat.log 2 (rep x) ≤ Nat.log 2 (rep (listLast0 (x :: ys)))
  | [], x, _, _, _ => by simp [listLast0]
  | y :: rest, x, hcr, hpos, hstep => by
      rcases hcr with ⟨hpxy, hcr_tail⟩
      have ih := chainRev_hasHeavy_log_bound par' hasHeavy rep rest y hcr_tail
        (fun u hu => hpos u (by simp [hu]))
        (fun a ha b hb => hstep a (by simp [ha]) b (by simp [hb]))
      have hst := hstep x (by simp) y (by simp) hpxy
      have hx1 : 1 ≤ rep x := hpos x (by simp)
      have hlast : listLast0 (x :: y :: rest) = listLast0 (y :: rest) := rfl
      rw [hlast, List.filter_cons]
      cases hhy : hasHeavy y with
      | false =>
          have hlog : Nat.log 2 (rep x) ≤ Nat.log 2 (rep y) := Nat.log_mono_right hst.1
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
      | true =>
          have hlog : Nat.log 2 (rep x) + 1 ≤ Nat.log 2 (rep y) :=
            nat_log_succ_of_two_mul_le hx1 (hst.2 hhy)
          simp only [↓reduceIte, List.length_cons]
          omega

/-! ### `revNode_spec`: reversing an exposed root auxiliary tree -/

theorem isVertex_of_isNode_not_edge {n z : ℕ} (hn : isNode n z) (hne : ¬ isEdgeSlot n z) :
    isVertex n z := by
  simp only [isNode] at hn
  simp only [isEdgeSlot, not_and, not_lt] at hne
  exact ⟨hn.1, by omega⟩

theorem isEdgeSlot_of_isNode_not_vertex {n z : ℕ} (hn : isNode n z) (hnv : ¬ isVertex n z) :
    isEdgeSlot n z := by
  simp only [isNode] at hn
  simp only [isVertex, not_and, not_le] at hnv
  exact ⟨by omega, hn.2⟩

theorem revNode_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {x : ℕ} {L R : AuxTree}
    (ht : AuxTree.node x L R ∈ trees)
    (hpp0 : (st.splay.nodes x).ppar = 0)
    (hlast_v : isVertex st.n (listLast0 (treeIds P st.splay (.node x L R)))) :
    let s' := SplayState.revNode P st.splay x
    let st' : LctState α σ τ := { st with splay := s' }
    let t' := AuxTree.node x R L
    let trees' := t' :: trees.erase (.node x L R)
    ∃ depth' : ℕ → ℕ,
      LctInvWith P st' trees' freeList depth' ∧
      sumTreePhi P st' = sumTreePhi P st ∧
      heavyCount P st' ≤ heavyCount P st + Nat.log 2 (2 * st.n + 1) + 1 ∧
      treeIds P s' t' = (treeIds P st.splay (.node x L R)).reverse ∧
      ∀ z ∉ (AuxTree.node x L R).toList, s'.nodes z = st.splay.nodes z := by
  intro s' st' t' trees'
  let active := trees.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  let ids := treeIds P st.splay (.node x L R)
  have ht_inv := W.treesInv _ ht
  have hrev := SplayState.revNode_root_preserves hL ht_inv.nodup ht_inv.sub
  rcases hrev with ⟨hsub', hev', hpp_x, hout⟩
  have hperm_t : t'.toList.Perm (AuxTree.node x L R).toList := by
    simpa [t', AuxTree.revRoot] using SplayState.revRoot_toList_perm (.node x L R)
  have ht'_inv : SplayState.TreeInv P s' t' :=
    ⟨hperm_t.nodup_iff.mpr ht_inv.nodup, hsub'⟩
  have hev_rev : SplayState.evalPairs P s' t' false P.idTag =
      (SplayState.evalPairs P st.splay (.node x L R) false P.idTag).reverse.map
        (fun p => (p.1, P.revVal p.2)) := by
    rw [hev' false P.idTag, Bool.not_false, SplayState.evalPairs_true_idTag hL]
  have hids_rev : treeIds P s' t' = ids.reverse := by
    simp [treeIds, ids, hev_rev, List.map_reverse]
  have hact_perm : (trees'.flatMap AuxTree.toList).Perm active :=
    flatMap_perm_of_replace ht hperm_t
  have hact_nd : (trees'.flatMap AuxTree.toList).Nodup :=
    hact_perm.nodup_iff.mpr W.activeNodup
  have hdisj_er := erase_flatMap_disjoint_of_nodup ht W.activeNodup
  have hpp_t' : (s'.nodes t'.rootId).ppar = 0 := by
    change (s'.nodes x).ppar = 0
    exact hpp_x.trans hpp0
  have hids_nd : ids.Nodup := treeIds_nodup ht_inv
  have hids_ne : ids ≠ [] := treeIds_ne_nil (by simp)
  have hids_mem_act : ∀ z ∈ ids, z ∈ active := fun z hz =>
    List.mem_flatMap.mpr ⟨_, ht, (mem_treeIds_iff P st.splay (.node x L R) z).mp hz⟩
  have h0_nin_ids : (0 : ℕ) ∉ ids := fun h0 => by
    have hv := W.activeValid 0 (hids_mem_act 0 h0)
    simp [isNode] at hv
  let par' := inducedSubPar P s' trees'
  have hpar'_out : ∀ z ∉ ids, par' z = par z := by
    intro z hz_nin
    have hz_nt : z ∉ (AuxTree.node x L R).toList := fun hm =>
      hz_nin ((mem_treeIds_iff P st.splay (.node x L R) z).mpr hm)
    dsimp only [par', par]
    by_cases hz_act : z ∈ active
    · have hz_act' : z ∈ trees'.flatMap AuxTree.toList := hact_perm.mem_iff.mpr hz_act
      have hz_er : z ∈ (trees.erase (.node x L R)).flatMap AuxTree.toList := by
        rcases List.mem_flatMap.mp hz_act' with ⟨a, ha, hza⟩
        rcases List.mem_cons.mp ha with rfl | ha_er
        · exact absurd (hperm_t.mem_iff.mp hza) hz_nt
        · exact List.mem_flatMap.mpr ⟨a, ha_er, hza⟩
      obtain ⟨a, ha_er, hza⟩ := List.mem_flatMap.mp hz_er
      have ha_ts := List.mem_of_mem_erase ha_er
      rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees', ha_er]) hza,
        inducedSubPar_eq_of_mem W.activeNodup ha_ts hza]
      have hag_a : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
        hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
      rw [treeIds_agree hag_a, hag_a a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))]
    · have hz_nact' : z ∉ trees'.flatMap AuxTree.toList := fun hm => hz_act (hact_perm.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hz_nact', inducedSubPar_eq_zero_of_not_mem hz_act]
  have hpar_in : ∀ z ∈ ids, par z = chainPred 0 ids z := fun z hz => by
    have hz_t := (mem_treeIds_iff P st.splay (.node x L R) z).mp hz
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup ht hz_t]
    simp [ids, AuxTree.rootId, hpp0]
  have hpar'_in : ∀ z ∈ ids, par' z = chainPred 0 ids.reverse z := fun z hz => by
    have hz_t := hperm_t.mem_iff.mpr ((mem_treeIds_iff P st.splay (.node x L R) z).mp hz)
    dsimp only [par']
    rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees']) hz_t]
    rw [hids_rev, hpp_t']
  have hpar_cl : ∀ w ∈ ids, par w = 0 ∨ par w ∈ ids := fun w hw => by
    rw [hpar_in w hw]
    exact chainPred_mem_or_prev hw
  have hpar'_cl : ∀ w ∈ ids, par' w = 0 ∨ par' w ∈ ids := fun w hw => by
    rw [hpar'_in w hw]
    rcases chainPred_mem_or_prev (List.mem_reverse.mpr hw) with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_reverse.mp h)
  let hd := listHead0 ids
  have hreach_ids : ∀ z ∈ ids, reaches par active.length hd z = true := fun z hz =>
    reaches_chain_head_of_acyclic W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp)
      W.acyclic ids 0 hd hids_nd (fun w hw h0 => h0_nin_ids (h0 ▸ hw)) h0_nin_ids hids_mem_act
      (fun w hw => (hpar_in w hw).symm) (Or.inl rfl) z hz
  have hsubpar'_mem : ∀ z ∈ trees'.flatMap AuxTree.toList, par' z ≠ 0 →
      par' z ∈ trees'.flatMap AuxTree.toList := by
    intro z hz hpz
    rw [hact_perm.mem_iff] at hz ⊢
    by_cases hzi : z ∈ ids
    · rcases hpar'_cl z hzi with h0 | hi
      · exact absurd h0 hpz
      · exact hids_mem_act _ hi
    · rw [hpar'_out z hzi] at hpz ⊢
      exact W.subPar_mem_active hz hpz
  let depth' : ℕ → ℕ := fun z =>
    if z ∈ ids then revIdx ids z
    else if reaches par active.length hd z then ids.length + depth z
    else depth z
  have hacyc' : ∀ z ∈ trees'.flatMap AuxTree.toList, par' z ≠ 0 →
      depth' (par' z) < depth' z := by
    intro z hz hpz
    rw [hact_perm.mem_iff] at hz
    by_cases hzi : z ∈ ids
    · have hp_in_i : par' z ∈ ids := by
        rcases hpar'_cl z hzi with h0 | hi
        · exact absurd h0 hpz
        · exact hi
      have hrev_cp : chainPred 0 ids.reverse z = par' z := (hpar'_in z hzi).symm
      have hcp_par : chainPred 0 ids (par' z) = z :=
        (chainPred_reverse_iff hids_nd h0_nin_ids hzi hp_in_i).mp hrev_cp
      simp only [depth', hzi, hp_in_i, ↓reduceIte]
      exact revIdx_lt_of_chainPred ids 0 z (par' z) hids_nd h0_nin_ids hzi hp_in_i hcp_par
    · rw [hpar'_out z hzi] at hpz ⊢
      have hpnz : par z ≠ 0 := hpz
      have hhz_ne : z ≠ hd := by
        intro h
        subst h
        cases hids_c : ids with
        | nil => exact hids_ne hids_c
        | cons a rest => exact hzi (by simp [hd, hids_c, listHead0])
      have hstep := reaches_step_iff W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp)
        W.acyclic (u := hd) hz
      have hreach_eq : reaches par active.length hd z = reaches par active.length hd (par z) :=
        Bool.eq_iff_iff.mpr ⟨fun hr => (hstep.mp hr).elim (fun h => absurd h hhz_ne) And.right,
          fun hr => hstep.mpr (Or.inr ⟨hpnz, hr⟩)⟩
      by_cases hpi : par z ∈ ids
      · have hr_p : reaches par active.length hd (par z) = true := hreach_ids (par z) hpi
        have hr_z : reaches par active.length hd z = true := hreach_eq ▸ hr_p
        simp only [depth', hpi, hzi, hr_z, ↓reduceIte]
        have hlt := revIdx_lt_length hpi
        omega
      · have hd_lt : depth (par z) < depth z := W.acyclic z hz hpnz
        by_cases hrz : reaches par active.length hd z = true
        · have hrp : reaches par active.length hd (par z) = true := hreach_eq ▸ hrz
          simp only [depth', hpi, hzi, hrz, hrp, ↓reduceIte]
          omega
        · have hrp : reaches par active.length hd (par z) = false := by
            rw [← hreach_eq]; cases hc : reaches par active.length hd z <;> simp_all
          simp only [depth', hpi, hzi, hrz, hrp, ↓reduceIte, Bool.false_eq_true]
          exact hd_lt
  have hvpe' : ∀ u, isVertex st'.n u → par' u ≠ 0 → isEdgeSlot st'.n (par' u) := by
    intro u huv hpu
    by_cases hui : u ∈ ids
    · have hpi : par' u ∈ ids := by
        rcases hpar'_cl u hui with h0 | hi; exact absurd h0 hpu; exact hi
      have hpar_p : par (par' u) = u := by
        rw [hpar_in _ hpi]
        exact (chainPred_reverse_iff hids_nd h0_nin_ids hui hpi).mp (hpar'_in u hui).symm
      have hp_nd : isNode st.n (par' u) := W.activeValid _ (hids_mem_act _ hpi)
      by_contra hne
      have hp_v : isVertex st.n (par' u) := isVertex_of_isNode_not_edge hp_nd hne
      have he_u : isEdgeSlot st.n u := by
        have hp_nz : par (par' u) ≠ 0 := by rw [hpar_p]; exact fun h0 => h0_nin_ids (h0 ▸ hui)
        have hvpe_old : isEdgeSlot st.n (par (par' u)) := W.vertexParEdge (par' u) hp_v hp_nz
        rwa [hpar_p] at hvpe_old
      simp only [isVertex, isEdgeSlot, st'] at huv he_u
      omega
    · rw [hpar'_out u hui] at hpu ⊢
      exact W.vertexParEdge u huv hpu
  have hepv' : ∀ e ∈ trees'.flatMap AuxTree.toList, isEdgeSlot st'.n e →
      par' e ≠ 0 ∧ isVertex st'.n (par' e) := by
    intro e he hes
    rw [hact_perm.mem_iff] at he
    by_cases hei : e ∈ ids
    · have he_nlast : e ≠ listLast0 ids := by
        intro h
        subst h
        dsimp only [ids] at *
        simp only [isEdgeSlot, isVertex, st'] at hes hlast_v
        omega
      have hpe_nz : par' e ≠ 0 := by
        rw [hpar'_in e hei, ne_eq, chainPred_rev_eq_zero_iff h0_nin_ids hei]
        exact he_nlast
      have hpi : par' e ∈ ids := by
        rcases hpar'_cl e hei with h0 | hi; exact absurd h0 hpe_nz; exact hi
      have hpar_p : par (par' e) = e := by
        rw [hpar_in _ hpi]
        exact (chainPred_reverse_iff hids_nd h0_nin_ids hei hpi).mp (hpar'_in e hei).symm
      have hp_nd : isNode st.n (par' e) := W.activeValid _ (hids_mem_act _ hpi)
      refine ⟨hpe_nz, ?_⟩
      by_contra hnv
      have hp_e : isEdgeSlot st.n (par' e) := isEdgeSlot_of_isNode_not_vertex hp_nd hnv
      have hv_e : isVertex st.n e := by
        have hp_nz : par (par' e) ≠ 0 := by rw [hpar_p]; exact fun h0 => h0_nin_ids (h0 ▸ hei)
        have hep_old := W.edgeParVertex (par' e) (hids_mem_act _ hpi) hp_e
        change par (par' e) ≠ 0 ∧ isVertex st.n (par (par' e)) at hep_old
        have h2 := hep_old.2
        rwa [hpar_p] at h2
      simp only [isVertex, isEdgeSlot, st'] at hv_e hes
      omega
    · rw [hpar'_out e hei]
      exact W.edgeParVertex e he hes
  have heuc' : ∀ e ∈ trees'.flatMap AuxTree.toList, isEdgeSlot st'.n e →
      ∃! w, w ∈ trees'.flatMap AuxTree.toList ∧ par' w = e ∧
        isVertex st'.n w ∧ w ≠ par' e := by
    intro e he hes
    rw [hact_perm.mem_iff] at he
    have he_nz : e ≠ 0 := fun h0 => by simp [isEdgeSlot, h0] at hes
    by_cases hei : e ∈ ids
    · have hep_old := W.edgeParVertex e he hes
      let u_prev := par e
      have hu_in_i : u_prev ∈ ids := by
        dsimp only [u_prev]
        rcases hpar_cl e hei with h0 | hi
        · exact absurd h0 hep_old.1
        · exact hi
      have hpar'_u : par' u_prev = e := by
        rw [hpar'_in u_prev hu_in_i]
        exact (chainPred_reverse_iff hids_nd h0_nin_ids hu_in_i hei).mpr (hpar_in e hei).symm
      have hpe'_prop := hepv' e (hact_perm.symm.mem_iff.mp he) hes
      have hy_in_i : par' e ∈ ids := by
        rcases hpar'_cl e hei with h0 | hi; exact absurd h0 hpe'_prop.1; exact hi
      have hpar_y : par (par' e) = e := by
        rw [hpar_in _ hy_in_i]
        exact (chainPred_reverse_iff hids_nd h0_nin_ids hei hy_in_i).mp (hpar'_in e hei).symm
      have hune : u_prev ≠ par' e := by
        intro h
        have hd1 := W.acyclic e he hep_old.1
        have hd2 := W.acyclic (par' e) (hids_mem_act _ hy_in_i)
          (by change par (par' e) ≠ 0; rw [hpar_y]; exact he_nz)
        change depth (par (par' e)) < depth (par' e) at hd2
        rw [hpar_y] at hd2
        change depth u_prev < depth e at hd1
        rw [h] at hd1
        omega
      refine ⟨u_prev, ⟨hact_perm.symm.mem_iff.mp (hids_mem_act _ hu_in_i),
        hpar'_u, hep_old.2, hune⟩, ?_⟩
      intro y ⟨hy_act, hpy, hy_v, hy_ne⟩
      rw [hact_perm.mem_iff] at hy_act
      by_cases hyi : y ∈ ids
      · have : chainPred 0 ids e = y :=
          (chainPred_reverse_iff hids_nd h0_nin_ids hyi hei).mp (by rw [← hpar'_in y hyi]; exact hpy)
        exact ((hpar_in e hei).trans this).symm
      · rw [hpar'_out y hyi] at hpy
        rcases W.edgeUniqueChild e he hes with ⟨w₀, ⟨_, hw_p, hw_v, hw_ne⟩, huniq⟩
        have hy_ne_old : y ≠ par e := fun h => hyi (h ▸ hu_in_i)
        have hpe_ne_old : par' e ≠ par e := hune.symm
        have hy_w₀ : y = w₀ := huniq y ⟨hy_act, hpy, hy_v, hy_ne_old⟩
        have hpe_w₀ : par' e = w₀ := huniq (par' e)
          ⟨hids_mem_act _ hy_in_i, hpar_y, hpe'_prop.2, hpe_ne_old⟩
        exact absurd (hy_w₀.trans hpe_w₀.symm ▸ hy_in_i) hyi
    · rcases W.edgeUniqueChild e he hes with ⟨w₀, ⟨hw₀_act, hw₀_p, hw₀_v, hw₀_ne⟩, huniq⟩
      have hw₀_ni : w₀ ∉ ids := fun hm => by
        rcases hpar_cl w₀ hm with h0 | hi
        · change par w₀ = e at hw₀_p; rw [hw₀_p] at h0; exact he_nz h0
        · change par w₀ = e at hw₀_p; rw [hw₀_p] at hi; exact hei hi
      have hpar'_w₀ : par' w₀ = e := (hpar'_out w₀ hw₀_ni).trans hw₀_p
      have hpar'_e : par' e = par e := hpar'_out e hei
      refine ⟨w₀, ⟨hact_perm.symm.mem_iff.mp hw₀_act, hpar'_w₀, hw₀_v,
        by rw [hpar'_e]; exact hw₀_ne⟩, ?_⟩
      intro y ⟨hy_act, hpy, hy_v, hy_ne⟩
      rw [hact_perm.mem_iff] at hy_act
      by_cases hyi : y ∈ ids
      · rcases hpar'_cl y hyi with h0 | hi
        · rw [hpy] at h0; exact absurd h0 he_nz
        · rw [hpy] at hi; exact absurd hi hei
      · rw [hpar'_out y hyi] at hpy
        rw [hpar'_e] at hy_ne
        exact huniq y ⟨hy_act, hpy, hy_v, hy_ne⟩
  have hfl : FreeListInv s' st.freeHead freeList :=
    FreeListInv_agree W.freeListInv (fun e he => by
      have := hout e (fun hm => W.active_of_freeList_disjoint he
        (List.mem_flatMap.mpr ⟨.node x L R, ht, hm⟩))
      rw [this])
  have hW' : LctInvWith P st' trees' freeList depth' :=
    { treesNonEmpty := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha_er
        · simp [t']
        · exact W.treesNonEmpty a (List.mem_of_mem_erase ha_er)
      treesInv := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha_er
        · exact ht'_inv
        · have ha_ts := List.mem_of_mem_erase ha_er
          exact SplayState.TreeInv_agree (W.treesInv a ha_ts)
            (fun u hu => (hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))).symm)
      activeNodup := hact_nd
      activeValid := fun z hz => W.activeValid z (hact_perm.mem_iff.mp hz)
      verticesActive := fun v hv => hact_perm.symm.mem_iff.mp (W.verticesActive v hv)
      freeNodup := W.freeNodup
      freeValid := W.freeValid
      partitionSlots := fun e he => by rw [hact_perm.mem_iff]; exact W.partitionSlots e he
      freeListInv := hfl
      pparActive := fun a ha hp => by
        dsimp only [st'] at hp ⊢
        rw [hact_perm.mem_iff]
        rcases List.mem_cons.mp ha with rfl | ha_er
        · exact absurd hpp_t' hp
        · have ha_ts := List.mem_of_mem_erase ha_er
          have hrt_eq := hout a.rootId (hdisj_er a.rootId
            (List.mem_flatMap.mpr ⟨a, ha_er, AuxTree.rootId_mem (W.treesNonEmpty a ha_ts)⟩))
          rw [hrt_eq] at hp ⊢
          exact W.pparActive a ha_ts hp
      acyclic := fun z hz hp => hacyc' z hz hp
      vertexParEdge := hvpe'
      edgeParVertex := hepv'
      edgeUniqueChild := heuc' }
  rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
  rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
  let active' := trees'.flatMap AuxTree.toList
  let v := vSize P st.splay active par trees
  let v' := vSize P s' active' par' trees'
  have hrep_out : ∀ u, u ∉ ids → repSize active' par' u = repSize active par u := by
    intro u hu
    have hlen_eq : active'.length = active.length := hact_perm.length_eq
    have h1 : repSize active' par' u = repSize active par' u := by
      dsimp only [repSize, active']
      rw [hlen_eq]
      exact (hact_perm.filter _).length_eq
    rw [h1]
    exact repSize_eq_of_not_mem_closed hpar'_out hpar'_cl hpar_cl hu
  have h_er_agree : ∀ a ∈ trees.erase (.node x L R),
      (s'.nodes a.rootId).ppar = (st.splay.nodes a.rootId).ppar ∧
      treeIds P s' a = treeIds P st.splay a ∧
      listHead0 (treeIds P st.splay a) ∉ ids := by
    intro a ha_er
    have ha_ts := List.mem_of_mem_erase ha_er
    have hag : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
      hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
    have hhd_nin : listHead0 (treeIds P st.splay a) ∉ ids := fun hm =>
      hdisj_er _ (List.mem_flatMap.mpr ⟨a, ha_er, listHead0_mem_of_ne_nil (W.treesNonEmpty a ha_ts)⟩)
        ((mem_treeIds_iff P st.splay (.node x L R) _).mp hm)
    exact ⟨by rw [hag a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))],
      treeIds_agree hag, hhd_nin⟩
  have hv_eq : ∀ u, u ≠ 0 → v' u = v u := by
    intro u hu_nz
    dsimp only [v', v, vSize, trees']
    have hperm_t := List.perm_cons_erase ht
    rw [((hperm_t.filter _).map _).sum_eq, filter_cons_map_sum, filter_cons_map_sum]
    have hpp_old_u : ((st.splay.nodes (AuxTree.node x L R).rootId).ppar == u) = false := by
      simp [AuxTree.rootId, hpp0, beq_false_of_ne (Ne.symm hu_nz)]
    have hpp_new_u : ((s'.nodes t'.rootId).ppar == u) = false := by
      simp [hpp_t', beq_false_of_ne (Ne.symm hu_nz)]
    have hfilt_er : (trees.erase (.node x L R)).filter (fun a => (s'.nodes a.rootId).ppar == u) =
        (trees.erase (.node x L R)).filter (fun a => (st.splay.nodes a.rootId).ppar == u) :=
      List.filter_congr (fun a ha => by rw [(h_er_agree a ha).1])
    have hsum_er : (((trees.erase (.node x L R)).filter
          (fun a => (s'.nodes a.rootId).ppar == u)).map
        (fun a => repSize active' par' (listHead0 (treeIds P s' a)))).sum =
        (((trees.erase (.node x L R)).filter
          (fun a => (st.splay.nodes a.rootId).ppar == u)).map
        (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum := by
      rw [hfilt_er]
      congr 1
      refine List.map_congr_left (fun a ha => ?_)
      have ha' := h_er_agree a (List.mem_filter.mp ha).1
      rw [ha'.2.1, hrep_out _ ha'.2.2]
    rw [hpp_old_u, hpp_new_u, hsum_er]
    simp
  have hphi_eq : sumTreePhi P st' = sumTreePhi P st := by
    rw [hPhi_new, hPhi_old]
    have hperm_t := List.perm_cons_erase ht
    have hsum_old : sumTreePhiList v trees =
        (AuxTree.node x L R).treePhi v + sumTreePhiList v (trees.erase (.node x L R)) := by
      dsimp only [sumTreePhiList]
      rw [(hperm_t.map _).sum_eq, List.map_cons, List.sum_cons]
    have hsum_new : sumTreePhiList v' trees' =
        t'.treePhi v' + sumTreePhiList v' (trees.erase (.node x L R)) := by
      dsimp only [sumTreePhiList, trees']
      simp only [List.map_cons, List.sum_cons]
    have ht'_phi : t'.treePhi v' = (AuxTree.node x L R).treePhi v := by
      have hag_t : ∀ u ∈ t'.toList, v' u = v u := fun u hu => by
        have hnd := W.activeValid u (hact_perm.mem_iff.mp (List.mem_flatMap.mpr ⟨t', by simp [trees'], hu⟩))
        exact hv_eq u (by simp [isNode] at hnd; omega)
      rw [SplayState.treePhi_agree hag_t]
      simpa [t', AuxTree.revRoot] using SplayState.revRoot_treePhi v (.node x L R)
    have hsum_er : sumTreePhiList v' (trees.erase (.node x L R)) =
        sumTreePhiList v (trees.erase (.node x L R)) := by
      dsimp only [sumTreePhiList]
      congr 1
      refine List.map_congr_left (fun a ha => SplayState.treePhi_agree (fun u hu => ?_))
      have hnd := W.activeValid u (List.mem_flatMap.mpr ⟨a, List.mem_of_mem_erase ha, hu⟩)
      exact hv_eq u (by simp [isNode] at hnd; omega)
    rw [hsum_new, hsum_old, ht'_phi, hsum_er]
  have hheavy_le : heavyCount P st' ≤ heavyCount P st + Nat.log 2 (2 * st.n + 1) + 1 := by
    let er := trees.erase (.node x L R)
    have ht'_light : isHeavyEdge P s' active' par' t' = false := by
      simp [isHeavyEdge, hpp_t']
    have hsplit : ((er.filter (isHeavyEdge P s' active' par'))).length ≤
        (er.filter (fun a => decide ((s'.nodes a.rootId).ppar ∉ ids) &&
          isHeavyEdge P s' active' par' a)).length +
        (er.filter (fun a => decide ((s'.nodes a.rootId).ppar ∈ ids) &&
          isHeavyEdge P s' active' par' a)).length := by
      have hperm_f : er.filter (isHeavyEdge P s' active' par') =
          er.filter (fun a => (decide ((s'.nodes a.rootId).ppar ∉ ids) &&
            isHeavyEdge P s' active' par' a) ||
            (decide ((s'.nodes a.rootId).ppar ∈ ids) && isHeavyEdge P s' active' par' a)) := by
        refine List.filter_congr (fun a _ => ?_)
        by_cases h : (s'.nodes a.rootId).ppar ∈ ids <;>
          cases isHeavyEdge P s' active' par' a <;> simp [h]
      rw [hperm_f]
      exact filter_or_length_le _ _ er
    have hout_le : (er.filter (fun a => decide ((s'.nodes a.rootId).ppar ∉ ids) &&
        isHeavyEdge P s' active' par' a)).length ≤ heavyCount P st := by
      have hlen1 := filter_length_le_of_imp
        (fun a => decide ((s'.nodes a.rootId).ppar ∉ ids) && isHeavyEdge P s' active' par' a)
        (isHeavyEdge P st.splay active par) er (fun a ha h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          have ha' := h_er_agree a ha
          have hh_eq : isHeavyEdge P s' active' par' a = isHeavyEdge P st.splay active par a := by
            dsimp only [isHeavyEdge]
            rw [hrep_out _ h.1, ha'.1, ha'.2.1, hrep_out _ ha'.2.2]
          exact hh_eq ▸ h.2)
      have hperm_t := List.perm_cons_erase ht
      have hH_old_eq : heavyCount P st = (trees.filter (isHeavyEdge P st.splay active par)).length :=
        hH_old
      dsimp only [active, par] at hH_old_eq hlen1
      dsimp only [er] at hlen1 ⊢
      rw [hH_old_eq, (hperm_t.filter _).length_eq, filter_cons_length]
      omega
    have her_nd : er.Nodup :=
      (List.nodup_cons.mp ((List.perm_cons_erase ht).nodup_iff.mp
        (nodup_of_flatMap_nodup trees W.activeNodup W.treesNonEmpty))).2
    let key : AuxTree → ℕ := fun a => (s'.nodes a.rootId).ppar
    let p : AuxTree → Bool := isHeavyEdge P s' active' par'
    let hasHeavy : ℕ → Bool := fun u => er.any (fun a => (key a == u) && p a)
    have hpar_head_eq : ∀ {a : AuxTree} (ha : a ∈ er),
        par' (listHead0 (treeIds P s' a)) = (s'.nodes a.rootId).ppar := by
      intro a ha
      have ha_ts := List.mem_of_mem_erase ha
      have ha_ne := W.treesNonEmpty a ha_ts
      dsimp only [par']
      rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees', er, ha]) (listHead0_mem_of_ne_nil ha_ne)]
      cases hids_a : treeIds P s' a with
      | nil => exact absurd hids_a (treeIds_ne_nil ha_ne)
      | cons _ _ => simp [listHead0, chainPred_head]
    have huniq_u : ∀ u ∈ ids, (er.filter (fun a => (key a == u) && p a)).length ≤ 1 := by
      intro u hu
      refine filter_length_le_one_of_nodup _ er her_nd (fun a₁ ha₁ a₂ ha₂ hq₁ hq₂ => ?_)
      simp only [Bool.and_eq_true, beq_iff_eq, key] at hq₁ hq₂
      by_contra hne
      have ha₁_ts := List.mem_of_mem_erase ha₁
      have ha₂_ts := List.mem_of_mem_erase ha₂
      let c₁ := listHead0 (treeIds P s' a₁)
      let c₂ := listHead0 (treeIds P s' a₂)
      have hc₁_mem : c₁ ∈ active' :=
        List.mem_flatMap.mpr ⟨a₁, by simp [trees', er, ha₁], listHead0_mem_of_ne_nil (W.treesNonEmpty a₁ ha₁_ts)⟩
      have hc₂_mem : c₂ ∈ active' :=
        List.mem_flatMap.mpr ⟨a₂, by simp [trees', er, ha₂], listHead0_mem_of_ne_nil (W.treesNonEmpty a₂ ha₂_ts)⟩
      have hc₁_ne : c₁ ≠ c₂ := fun heq => by
        dsimp only [c₁, c₂] at heq
        exact hne (flatMap_mem_unique hact_nd
          (by simp [trees', er, ha₁]) (by simp [trees', er, ha₂])
          (listHead0_mem_of_ne_nil (W.treesNonEmpty a₁ ha₁_ts))
          (heq ▸ listHead0_mem_of_ne_nil (W.treesNonEmpty a₂ ha₂_ts)))
      have hu_act' : u ∈ active' := hact_perm.symm.mem_iff.mp (hids_mem_act u hu)
      have hu_nz : u ≠ 0 := fun h0 => h0_nin_ids (h0 ▸ hu)
      have htwo := repSize_ge_one_add_two_children hact_nd hsubpar'_mem hacyc' hu_act' hu_nz
        hc₁_mem hc₂_mem ((hpar_head_eq ha₁).trans hq₁.1) ((hpar_head_eq ha₂).trans hq₂.1) hc₁_ne
      dsimp only [c₁, c₂] at htwo
      have hp1 := hq₁.2
      have hp2 := hq₂.2
      dsimp only [p, isHeavyEdge] at hp1 hp2
      simp only [hq₁.1, hq₂.1, Bool.and_eq_true, decide_eq_true_eq] at hp1 hp2
      dsimp only [active'] at hp1 hp2
      omega
    have hin_le_hh : (er.filter (fun a => decide ((s'.nodes a.rootId).ppar ∈ ids) && p a)).length ≤
        (ids.filter hasHeavy).length :=
      er_filter_chain_le_hasHeavy er key p hasHeavy (fun u => rfl) ids huniq_u
    have hcr : ChainRev par' ids := by
      have hcr0 := chainPred_rev_chainRev ids hids_nd (fun z hz h0 => h0_nin_ids (h0 ▸ hz))
      have hagree_cr : ∀ l : List ℕ, (∀ z ∈ l, z ∈ ids) →
          ChainRev (fun z => chainPred 0 ids.reverse z) l → ChainRev par' l := by
        intro l hl hc
        induction l with
        | nil => trivial
        | cons u us ihl =>
            cases us with
            | nil => trivial
            | cons v vs =>
                rcases hc with ⟨huv, hrest⟩
                refine ⟨?_, ihl (fun w hw => hl w (by simp [hw])) hrest⟩
                rw [hpar'_in u (hl u (by simp))]
                exact huv
      exact hagree_cr ids (fun _ hz => hz) hcr0
    have hstep_cr : ∀ a ∈ ids, ∀ b ∈ ids, par' a = b →
        repSize active' par' a ≤ repSize active' par' b ∧
        (hasHeavy b = true → 2 * repSize active' par' a ≤ repSize active' par' b) := by
      intro a ha b hb hpab
      have ha_act' : a ∈ active' := hact_perm.symm.mem_iff.mp (hids_mem_act a ha)
      have hb_act' : b ∈ active' := hact_perm.symm.mem_iff.mp (hids_mem_act b hb)
      have hb_nz : b ≠ 0 := fun h0 => h0_nin_ids (h0 ▸ hb)
      have hsum_b := repSize_eq_one_add_sum_children hact_nd hsubpar'_mem hacyc' hb_act' hb_nz
      have ha_in_f : a ∈ active'.filter (fun c => par' c == b) :=
        List.mem_filter.mpr ⟨ha_act', by simp [hpab]⟩
      have ha_le_sum : repSize active' par' a ≤
          ((active'.filter (fun c => par' c == b)).map (repSize active' par')).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha_in_f, rfl⟩)
      dsimp only [active'] at ha_le_sum
      refine ⟨by dsimp only [active']; omega, fun hhb => ?_⟩
      dsimp only [hasHeavy] at hhb
      obtain ⟨c, hc_er, hqc⟩ := List.any_eq_true.mp hhb
      simp only [Bool.and_eq_true, beq_iff_eq, key] at hqc
      have hc_ts := List.mem_of_mem_erase hc_er
      let hd_c := listHead0 (treeIds P s' c)
      have hc_mem_t : hd_c ∈ c.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty c hc_ts)
      have hc_act' : hd_c ∈ active' :=
        List.mem_flatMap.mpr ⟨c, by simp [trees', er, hc_er], hc_mem_t⟩
      have hc_nin : hd_c ∉ ids := fun hm =>
        hdisj_er _ (List.mem_flatMap.mpr ⟨c, hc_er, hc_mem_t⟩)
          ((mem_treeIds_iff P st.splay (.node x L R) _).mp hm)
      have hc_ne_a : hd_c ≠ a := fun heq => hc_nin (heq ▸ ha)
      have htwo := repSize_ge_one_add_two_children hact_nd hsubpar'_mem hacyc' hb_act' hb_nz
        ha_act' hc_act' hpab ((hpar_head_eq hc_er).trans hqc.1) hc_ne_a.symm
      dsimp only [hd_c] at htwo
      have hpc := hqc.2
      dsimp only [p, isHeavyEdge] at hpc
      simp only [hqc.1, Bool.and_eq_true, decide_eq_true_eq] at hpc
      dsimp only [active'] at *
      omega
    have hlog_chain : (ids.filter hasHeavy).length ≤ 1 + Nat.log 2 (2 * st.n + 1) := by
      cases hids_c : ids with
      | nil => exact absurd hids_c hids_ne
      | cons z₀ rest =>
          have hpos : ∀ u ∈ z₀ :: rest, 1 ≤ repSize active' par' u := fun u hu =>
            repSize_pos_of_mem (hact_perm.symm.mem_iff.mp (hids_mem_act u (hids_c ▸ hu)))
          have hbound := chainRev_hasHeavy_log_bound par' hasHeavy (repSize active' par') rest z₀
            (hids_c ▸ hcr) hpos (fun a ha b hb => hstep_cr a (hids_c ▸ ha) b (hids_c ▸ hb))
          have hrep_le : repSize active' par' (listLast0 (z₀ :: rest)) ≤ 2 * st.n + 1 := by
            dsimp only [active']
            have h1 := repSize_le_active (active := trees'.flatMap AuxTree.toList)
              (par := par') (listLast0 (z₀ :: rest))
            have h2 := active_length_le_two_mul hact_nd
              (fun z hz => W.activeValid z (hact_perm.mem_iff.mp hz))
            omega
          have hlog_r : Nat.log 2 (repSize active' par' (listLast0 (z₀ :: rest))) ≤ Nat.log 2 (2 * st.n + 1) :=
            Nat.log_mono_right hrep_le
          rw [filter_cons_length]
          split_ifs <;> omega
    have hH_new' : heavyCount P st' = (er.filter (isHeavyEdge P s' active' par')).length := by
      rw [hH_new]
      dsimp only [heavyCountList]
      change ((t' :: er).filter (isHeavyEdge P s' active' par')).length =
        (er.filter (isHeavyEdge P s' active' par')).length
      rw [filter_cons_length, ht'_light]
      simp
    rw [hH_new']
    dsimp only [p] at hin_le_hh
    omega
  exact ⟨depth', hW', hphi_eq, hheavy_le, hids_rev, hout⟩

end MinCostFlow.LinkCut


